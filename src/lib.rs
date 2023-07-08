//! Ergonomic Rust bindings to the JavaScript standard built-in `RegExp` object
//!
//! ### Basic usage
//! ```
//! use js_regexp::{RegExp, RegExpFlags}
//!
//! let mut re = RegExp::new(
//!     r#"(?<greeting>\w+), (?<name>\w+)"#,
//!     RegExpFlags::new().has_indices(),
//! )
//! .unwrap();
//!
//! let result = re.exec("Hello, Alice!").unwrap();
//! let named_captures = result.captures.unwrap();
//! let named_captures = named_captures.get_named_captures_map();
//! assert_eq!("Hello, Alice", result.match_slice);
//! assert_eq!(0, result.match_index);
//! assert_eq!(12, result.match_length);
//! assert_eq!("Hello", named_captures.get("greeting").unwrap().slice);
//! assert_eq!(7, named_captures.get("name").unwrap().index)
//! ```
//! See [RegExp] for detailed information about the API.

use anyhow::Context;
use js_sys::{Function, JsString};
use std::{
    collections::HashMap,
    hash::{Hash, Hasher},
};
use thiserror::Error;
use wasm_bindgen::{JsCast, JsValue};

/// A wrapped JavaScript `RegExp`. The main type of this crate.
///
/// [MDN documentation](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/RegExp)
#[derive(Debug)]
pub struct RegExp<'p> {
    inner: js_sys::RegExp,
    pattern: PatternSource<'p>,
}
impl<'p> RegExp<'p> {
    /// Constructs a new regular expression, backed by a `RegExp` on the JavaScript heap. \
    /// Returns an error if JavaScript throws a SyntaxError exception. \
    /// You may pass a `&str` as the flags argument. \
    /// When constructed by this function, the returned value's lifetime becomes tied to the
    /// provided `&str` pattern. See [`new_with_ownership`](RegExp::new_with_ownership)
    /// for an alternative that takes ownership of a `String` pattern instead.
    pub fn new<F: Into<RegExpFlags>>(pattern: &'p str, flags: F) -> Result<Self, JsValue> {
        Ok(Self {
            inner: construct_regexp_panicking(pattern, flags.into().get())?,
            pattern: PatternSource::Ref(pattern),
        })
    }
    /// Constructs a new regular expression, backed by a `RegExp` on the JavaScript heap. \
    /// Returns an error if JavaScript throws a SyntaxError exception. \
    /// You may pass a `&str` as the flags argument. \
    /// Takes ownership of the provided `String` pattern. Use [`new`](RegExp::new) instead if you have a `&'static str`,
    /// or if it otherwise makes sense for the constructed value to store only a reference to your pattern.
    pub fn new_with_ownership<F: Into<RegExpFlags>>(
        pattern: String,
        flags: F,
    ) -> Result<Self, JsValue> {
        Ok(Self {
            inner: construct_regexp_panicking(&pattern, flags.into().get())?,
            pattern: PatternSource::Owned(pattern),
        })
    }
    /// Constructs a new regular expression, backed by a `RegExp` on the JavaScript heap. \
    /// Returns an error if JavaScript throws a SyntaxError exception. \
    /// You may pass a `&str` as the flags argument. \
    /// Unlike with [`new`](RegExp::new), the returned structure does not hold on to a reference to the provided
    /// `&str` pattern. This is achieved by copying any group names from the JavaScript heap every time the regular expression
    /// is used.
    pub fn new_with_copying<F: Into<RegExpFlags>>(
        pattern: &str,
        flags: F,
    ) -> Result<Self, JsValue> {
        Ok(Self {
            inner: construct_regexp_panicking(pattern, flags.into().get())?,
            pattern: PatternSource::Copy,
        })
    }

    /// Calls the underlying JavaScript `RegExp`'s `exec` method. \
    /// Returns `None` if the JavaScript call returns null.
    /// The returned [`ExecResult`]'s `captures` member is `None` if the underlying JavaScript call returns an object
    /// that does not have an `indices` property, which is only present when the [`d` flag](RegExpFlags::has_indices)
    /// is set for the expression.
    ///
    /// [MDN documentation](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/RegExp/exec)
    pub fn exec<'h>(&'p mut self, haystack: &'h str) -> Option<ExecResult<'h, 'p>> {
        match self.exec_internal(haystack) {
            Ok(v) => v,
            Err(v) => panic!("{:?}", v),
        }
    }
    fn exec_internal<'h>(
        &'p mut self,
        haystack: &'h str,
    ) -> Result<Option<ExecResult<'h, 'p>>, JsError> {
        let result = match self.inner.exec(haystack) {
            Some(v) => v,
            None => return Ok(None),
        };

        let utf16_match_index = get_value_property_str("index", &result)?
            .as_f64()
            .option_context()? as usize;
        let utf8_match_index =
            count_bytes_from_utf16_units(haystack, utf16_match_index).option_context()?;
        let matched = &haystack[utf8_match_index..];
        let string_match_js = result.iter().next().option_context()?;
        let string_match_js: &JsString = string_match_js.dyn_ref().option_context()?;
        let utf16_match_length = string_match_js.length() as usize;
        let utf8_match_length =
            count_bytes_from_utf16_units(matched, utf16_match_length).option_context()?;
        let matched = &matched[..utf8_match_length];
        let indices_array_js = get_value_property_str("indices", &result)?;

        let mut exec_result = ExecResult {
            match_slice: matched,
            match_index: utf8_match_index,
            match_length: utf16_match_length,
            captures: None,
        };
        if !indices_array_js.is_array() {
            return Ok(Some(exec_result));
        }

        let mut captures_vec = Vec::new();
        let js_array_iter = js_sys::try_iter(&indices_array_js)?.option_context()?;
        for indices_js in js_array_iter.skip(1) {
            let indices_js = indices_js?;
            let capture = slice_capture(haystack, &indices_js)?;
            captures_vec.push(capture);
        }
        let named_indices_js = get_value_property_str("groups", &indices_array_js)?;
        if !named_indices_js.is_object() {
            let _ = exec_result
                .captures
                .insert(CapturesList { vec: captures_vec });
            return Ok(Some(exec_result));
        }

        let group_names = js_sys::Reflect::own_keys(&named_indices_js)?;
        for group_name_js in group_names.iter() {
            let group_name_js: JsString = group_name_js.dyn_into()?;
            let indices_js = js_sys::Reflect::get(&named_indices_js, &group_name_js)?;
            let capture = slice_capture(haystack, &indices_js)?;
            let group_name = match self.pattern.get() {
                Some(pattern) => {
                    GroupName::Ref(find_js_string(pattern, &group_name_js).option_context()?)
                }
                None => GroupName::Owned(group_name_js.as_string().option_context()?),
            };
            let _ = captures_vec
                .iter_mut()
                .find(|v| v.index == capture.index && v.length == capture.length)
                .option_context()?
                .group_name
                .insert(group_name);
        }

        let _ = exec_result
            .captures
            .insert(CapturesList { vec: captures_vec });
        Ok(Some(exec_result))
    }
}

/// An error that occurs when something unexpected happens
/// while interacting with JavaScript.
#[derive(Debug, Error)]
enum JsError {
    #[error("JavaScript exception")]
    JavaScript(JsValue),
    #[error("Other error")]
    Other(#[from] anyhow::Error),
}
impl From<JsValue> for JsError {
    fn from(value: JsValue) -> Self {
        JsError::JavaScript(value)
    }
}

trait OptionContext<T, E> {
    fn option_context(self) -> Result<T, anyhow::Error>
    where
        Self: Context<T, E>;
}
impl<T, E> OptionContext<T, E> for Option<T> {
    fn option_context(self) -> Result<T, anyhow::Error>
    where
        Self: Context<T, E>,
    {
        self.context("Unexpectedly failed to unwrap an option while interacting with JavaScript")
    }
}

#[derive(Debug)]
enum PatternSource<'a> {
    Owned(String),
    Ref(&'a str),
    Copy,
}
impl<'a> PatternSource<'a> {
    fn get(&'a self) -> Option<&'a str> {
        match self {
            PatternSource::Owned(s) => Some(s),
            PatternSource::Ref(s) => Some(s),
            PatternSource::Copy => None,
        }
    }
}

macro_rules! flag_setters {
    (
        $(
            $(#[$doc:meta])*
            ($vis:vis $id:ident, $flag:literal)
        )*
    ) => {
        $(
            $(#[$doc])*
            $vis fn $id(mut self) -> Self {
                let find = self
                    .inner
                    .iter()
                    .enumerate()
                    .find(|(_, v)| **v == 0 || **v == $flag);
                let (i, flag) = match find {
                    Some(v) => v,
                    None => return self,
                };
                if *flag != 0 {
                    return self;
                }
                self.inner[i] = $flag;
                self
            }
        )*
    };
}
/// A constrained representation of JavaScript `RegExp` flags.
/// Not all flags allowed here are supported on all platforms; The `new*` functions on [`RegExp`] will
/// report a SyntaxError exception if you set unsupported flags.
#[derive(Debug)]
pub struct RegExpFlags {
    inner: [u8; 7],
}
impl RegExpFlags {
    pub fn new() -> Self {
        RegExpFlags { inner: [0; 7] }
    }
    fn get(&self) -> &str {
        let slice_end = self
            .inner
            .iter()
            .enumerate()
            .find(|(_, v)| **v == 0)
            .map(|v| v.0);
        let slice = std::str::from_utf8(match slice_end {
            Some(v) => &self.inner[..v],
            None => &self.inner,
        })
        .unwrap(); // Can never panic if RegExpFlags is only modified through the public API
        slice
    }
    fn is_set(&self, flag: u8) -> Option<usize> {
        self.inner
            .iter()
            .enumerate()
            .find(|(_, v)| **v == flag)
            .map(|(v, _)| v)
    }
    flag_setters!(
        /// Sets the `d` flag, which causes capture indices to be returned when matching. \
        /// [ExecResult]'s `captures` field is `None` when this flag is not set.
        ///
        /// [MDN documentation](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/RegExp/hasIndices#description)
        (pub has_indices, b'd')
        /// Sets the `i` flag, which enables case-insensitive matching.
        ///
        /// [MDN documentation](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/RegExp/ignoreCase#description)
        (pub ignore_case, b'i')
        /// Sets the `g` flag, which enables global matching.
        ///
        /// [MDN documentation](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/RegExp/global#description)
        (pub global, b'g')
        /// Sets the `s` flag, which causes the `.` special character to match additonal line terminators.
        ///
        /// [MDN documentation](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/RegExp/dotAll#description)
        (pub dot_all, b's')
        /// Sets the `m` flag, which enables multiline matching.
        ///
        /// [MDN documentation](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/RegExp/multiline#description)
        (pub multiline, b'm')
        /// Sets the `y` flag, which enables sticky matching.
        ///
        /// [MDN documentation](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/RegExp/sticky#description)
        (pub sticky, b'y')
        (unicode_internal, b'u')
        (unicode_sets_internal, b'v')
    );
    /// Sets the `u` flag, which enables some unicode-related features.
    /// Unsets the `v` (`unicode_sets`) flag.
    ///
    /// [MDN documentation](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/RegExp/unicode#description)
    pub fn unicode(mut self) -> Self {
        match self.is_set(b'v') {
            Some(idx) => self.inner[idx] = b'u',
            None => self = self.unicode_internal(),
        }
        self
    }
    /// Sets the `v` flag, which enables a superset of the features enabled by the `u` (`unicode`) flag.
    /// Unsets the `u` flag.
    ///
    /// [MDN documentation](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/RegExp/unicodeSets#description)
    pub fn unicode_sets(mut self) -> Self {
        match self.is_set(b'u') {
            Some(idx) => self.inner[idx] = b'v',
            None => self = self.unicode_sets_internal(),
        }
        self
    }
}
impl From<&str> for RegExpFlags {
    fn from(value: &str) -> Self {
        let mut flags = Self::new();
        for ch in value.chars() {
            match ch {
                'd' => flags = flags.has_indices(),
                'i' => flags = flags.ignore_case(),
                'g' => flags = flags.global(),
                's' => flags = flags.dot_all(),
                'm' => flags = flags.multiline(),
                'y' => flags = flags.sticky(),
                'u' => flags = flags.unicode(),
                'v' => flags = flags.unicode_sets(),
                _ => (),
            }
        }
        flags
    }
}

/// The result of a successful [`RegExp::exec`] call.
#[derive(Debug)]
pub struct ExecResult<'h, 'p> {
    pub match_slice: &'h str,
    pub match_index: usize,
    pub match_length: usize,
    pub captures: Option<CapturesList<'h, 'p>>,
}

/// A list of [`Capture`]s.
#[derive(Debug)]
pub struct CapturesList<'h, 'p> {
    pub vec: Vec<Capture<'h, 'p>>,
}
impl<'h, 'p> CapturesList<'h, 'p> {
    /// Maps group names to captures from the inner `Vec`
    pub fn get_named_captures_map(&self) -> HashMap<&str, &Capture<'h, 'p>> {
        let mut map = HashMap::new();
        for capture in self.vec.iter() {
            let key = match &capture.group_name {
                Some(GroupName::Owned(s)) => &s[..],
                Some(GroupName::Ref(s)) => s,
                None => continue,
            };
            map.insert(key, capture);
        }
        map
    }
}

/// An index, length, slice, and optional group name of a capture in a haystack.
#[derive(Debug)]
pub struct Capture<'h, 'p> {
    pub group_name: Option<GroupName<'p>>,
    pub index: usize,
    pub length: usize,
    pub slice: &'h str,
}

/// A name of a named capture group, backed either by a slice of a pattern or
/// an owned `String` copied from JavaScript.
#[derive(Debug)]
pub enum GroupName<'a> {
    Owned(String),
    Ref(&'a str),
}
impl PartialEq for GroupName<'_> {
    fn eq(&self, other: &Self) -> bool {
        let a = match self {
            GroupName::Owned(s) => &s[..],
            GroupName::Ref(s) => s,
        };
        let b = match other {
            GroupName::Owned(s) => &s[..],
            GroupName::Ref(s) => s,
        };
        a == b
    }
}
impl Eq for GroupName<'_> {}
impl Hash for GroupName<'_> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let s = match self {
            GroupName::Owned(s) => &s[..],
            GroupName::Ref(s) => s,
        };
        s.hash(state);
    }
}
impl<'a> From<&'a str> for GroupName<'a> {
    fn from(value: &'a str) -> Self {
        Self::Ref(value)
    }
}
impl From<String> for GroupName<'_> {
    fn from(value: String) -> Self {
        Self::Owned(value)
    }
}
impl<'a> Into<&'a str> for &'a GroupName<'a> {
    fn into(self) -> &'a str {
        match self {
            GroupName::Owned(s) => &s[..],
            GroupName::Ref(s) => s,
        }
    }
}

#[derive(Debug, Error)]
enum NewRegExpError {
    #[error("Syntax error")]
    SyntaxError(JsValue),
    #[error("Unexpected error")]
    JsError(#[from] JsError),
}
fn construct_regexp_panicking(pattern: &str, flags: &str) -> Result<js_sys::RegExp, JsValue> {
    construct_regexp(pattern, flags).map_err(|e| match e {
        NewRegExpError::SyntaxError(v) => v,
        NewRegExpError::JsError(e) => panic!("{:?}", e),
    })
}
fn construct_regexp(pattern: &str, flags: &str) -> Result<js_sys::RegExp, NewRegExpError> {
    let global = js_sys::global();
    let regexp_object = get_value_property_str("RegExp", &global).map_err(Into::<JsError>::into)?;
    let regexp_object: &Function = regexp_object
        .dyn_ref()
        .option_context()
        .map_err(Into::<JsError>::into)?;
    let args = js_sys::Array::new_with_length(2);
    args.set(0, JsValue::from_str(pattern));
    args.set(1, JsValue::from_str(flags));
    let regexp = js_sys::Reflect::construct(regexp_object, &args)
        .map_err(|e| NewRegExpError::SyntaxError(e))?;
    let regexp = regexp.dyn_into().map_err(Into::<JsError>::into)?;
    Ok(regexp)
}

fn get_value_property_usize(key: usize, target: &JsValue) -> Result<JsValue, JsValue> {
    let key = key as u32;
    js_sys::Reflect::get_u32(target, key)
}

fn get_value_property_str(key: &str, target: &JsValue) -> Result<JsValue, JsValue> {
    let key = JsValue::from_str(key);
    js_sys::Reflect::get(target, &key)
}

fn slice_capture<'h, 'p>(haystack: &'h str, indices: &JsValue) -> Result<Capture<'h, 'p>, JsError> {
    let utf16_index = get_value_property_usize(0, indices)?
        .as_f64()
        .option_context()? as usize;
    let utf16_end = get_value_property_usize(1, indices)?
        .as_f64()
        .option_context()? as usize;
    let utf16_length = utf16_end - utf16_index;
    let capture = haystack;
    let utf8_begin = count_bytes_from_utf16_units(capture, utf16_index).option_context()?;
    let capture = &capture[utf8_begin..];
    let utf8_length = count_bytes_from_utf16_units(capture, utf16_length).option_context()?;
    let capture = &capture[..utf8_length];
    Ok(Capture {
        group_name: None,
        index: utf8_begin,
        length: utf8_length,
        slice: capture,
    })
}

fn find_js_string<'a>(s: &'a str, js_str: &JsString) -> Option<&'a str> {
    let mut utf16_buf = [0u16, 2];
    let mut s = s;
    let end_index = 'lvl0: loop {
        let mut js_str_iter = js_str.iter();
        let mut s_iter = s.char_indices();
        'lvl1: loop {
            let (idx, ch) = match s_iter.next() {
                Some(v) => v,
                None => {
                    break 'lvl0 match js_str_iter.next() {
                        Some(_) => None,
                        None => Some(s.len()),
                    }
                }
            };
            let units = ch.encode_utf16(&mut utf16_buf);
            for unit in units.iter() {
                let should_match = match js_str_iter.next() {
                    Some(v) => v,
                    None => {
                        break 'lvl0 Some(idx);
                    }
                };
                if unit != &should_match {
                    break 'lvl1;
                }
            }
        }
        match s.char_indices().nth(1) {
            Some((v, _)) => s = &s[v..],
            None => break None,
        }
    };
    Some(&s[0..end_index?])
}

fn count_bytes_from_utf16_units(s: &str, n_units: usize) -> Option<usize> {
    let mut n_units = n_units as isize;
    let mut i = s.char_indices();
    while n_units > 0 {
        let (_, char) = i.next()?;
        n_units -= char.len_utf16() as isize;
    }
    let bytes_counted = i.next().map(|v| v.0).unwrap_or(s.len());
    Some(bytes_counted)
}
