//! Ergonomic Rust bindings to the JavaScript standard built-in `RegExp` object
//!
//! ### Basic usage
//! ```
//! use js_regexp::{flags, Flags, RegExp};
//!
//! let mut re = RegExp::new(r#"(?<greeting>\w+), (?<name>\w+)"#, flags!("d")).unwrap();
//! let result = re.exec("Hello, Alice!").unwrap();
//!
//! let mut iter = result.captures().unwrap().iter();
//! let named_captures = result.named_captures().unwrap();
//!
//! assert_eq!("Hello, Alice", result.match_slice);
//! assert_eq!(0, result.match_index);
//! assert_eq!(12, result.match_length);
//! assert_eq!("Hello", iter.next().unwrap().slice);
//! assert_eq!("Hello", named_captures.get("greeting").unwrap().slice);
//! assert_eq!(5, iter.next().unwrap().length);
//! assert_eq!(7, named_captures.get("name").unwrap().index);
//! ```

use anyhow::Context;
use js_sys::{Function, JsString};
use std::collections::HashMap;
use thiserror::Error;
use wasm_bindgen::{JsCast, JsValue};

pub use js_regexp_macros::flags;

/// A wrapped JavaScript `RegExp`. The main type of this crate.
///
/// [MDN documentation](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/RegExp)
#[derive(Debug)]
pub struct RegExp<'p> {
    inner: js_sys::RegExp,
    pattern: PatternSource<'p>,
    flags: Flags,
}
impl<'p> RegExp<'p> {
    /// Constructs a new regular expression, backed by a `RegExp` in JavaScript. \
    /// Returns an error if JavaScript throws a SyntaxError exception. \
    /// When constructed by this function, the returned value's lifetime becomes tied to the
    /// provided `&str` pattern. See [`new_with_owned_pattern`](RegExp::new_with_owned_pattern)
    /// for an alternative that takes ownership of a `String` pattern instead.
    pub fn new(pattern: &'p str, flags: Flags) -> Result<Self, JsValue> {
        Ok(Self {
            inner: construct_regexp_panicking(pattern, flags.build())?,
            pattern: PatternSource::Ref(pattern),
            flags,
        })
    }
    /// Constructs a new regular expression, backed by a `RegExp` in JavaScript. \
    /// Returns an error if JavaScript throws a SyntaxError exception. \
    /// Takes ownership of the provided `String` pattern. Use [`new`](RegExp::new) instead if you have a `&'static str`,
    /// or if it otherwise makes sense for the constructed value to store only a reference to your pattern.
    pub fn new_with_owned_pattern(pattern: String, flags: Flags) -> Result<Self, JsValue> {
        Ok(Self {
            inner: construct_regexp_panicking(&pattern, flags.build())?,
            pattern: PatternSource::Owned(pattern),
            flags,
        })
    }
    /// Constructs a new regular expression, backed by a `RegExp` in JavaScript. \
    /// Returns an error if JavaScript throws a SyntaxError exception. \
    /// Unlike with [`new`](RegExp::new), the returned structure does not hold on to a reference to the provided
    /// `&str` pattern. This is achieved by copying any group names from the JavaScript heap every time the regular expression
    /// is used.
    pub fn new_with_copied_names(pattern: &str, flags: Flags) -> Result<Self, JsValue> {
        Ok(Self {
            inner: construct_regexp_panicking(pattern, flags.build())?,
            pattern: PatternSource::Copy,
            flags,
        })
    }

    /// Calls the underlying JavaScript `RegExp`'s `exec` method. \
    /// Returns `None` if the JavaScript call returns null.
    ///
    /// [MDN documentation](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/RegExp/exec)
    pub fn exec<'h, 'a>(&'a mut self, haystack: &'h str) -> Option<ExecResult<'h, 'a>> {
        match self.exec_internal(haystack) {
            Ok(v) => v,
            Err(v) => panic!("{:?}", v),
        }
    }

    /// The flags set for this regular expression.
    pub fn flags(&self) -> &FlagSets {
        &self.flags.sets
    }

    /// Creates a [`RegExpStream`] for repeatedly matching in the same haystack
    pub fn stream<'s, 'h>(&'s mut self, haystack: &'h str) -> RegExpStream<'s, 'h, 'p> {
        RegExpStream {
            regex: self,
            haystack,
        }
    }

    /// The inner
    /// [`js_sys::RegExp`](https://docs.rs/js-sys/latest/js_sys/struct.RegExp.html).
    /// Useful for directly accessing the `lastIndex` property
    /// ([`MDN`](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/RegExp/lastIndex))
    /// and the `test` method
    /// ([`MDN`](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/RegExp/test)),
    /// which are not worth wrapping explicitly as they don't require fancy conversions.
    pub fn inner(&mut self) -> &mut js_sys::RegExp {
        &mut self.inner
    }

    fn exec_internal<'h>(
        &'p self,
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
            let _ = exec_result.captures.insert(captures_vec);
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

        let _ = exec_result.captures.insert(captures_vec);
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

/// Boolean fields representing regular expression flags.
#[derive(Debug)]
pub struct FlagSets {
    /// The `d` flag, which causes capture indices to be returned when matching.
    /// The [`ExecResult`] methods [`captures`](ExecResult::captures) and [`named_captures`](ExecResult::named_captures)
    /// return `None` when this flag is not set.
    /// ([MDN](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/RegExp/hasIndices#description))
    pub has_indices: bool,
    /// The `i` flag, which enables case-insensitive matching.
    /// ([MDN](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/RegExp/ignoreCase#description))
    pub ignore_case: bool,
    /// The `g` flag, which enables global matching.
    /// ([MDN](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/RegExp/global#description))
    pub global: bool,
    /// The `s` flag, which causes the `.` special character to match additonal line terminators.
    /// ([MDN](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/RegExp/dotAll#description))
    pub dot_all: bool,
    /// The `m` flag, which enables multiline matching.
    /// ([MDN](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/RegExp/multiline#description))
    pub multiline: bool,
    /// The `y` flag, which enables sticky matching.
    /// ([MDN](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/RegExp/sticky#description))
    pub sticky: bool,
    /// The `u` flag, which enables some unicode-related features.
    /// Can't be set at the same time as the `v` (`unicode_sets`) flag.
    /// ([MDN](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/RegExp/unicode#description))
    pub unicode: bool,
    /// The `v` flag, which enables a superset of the features enabled by the `u` (`unicode`) flag.
    /// Can't be set at the same time as the `u` flag.
    /// ([MDN](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/RegExp/unicodeSets#description))
    pub unicode_sets: bool,
}
impl FlagSets {
    fn new_empty_flagsets() -> FlagSets {
        FlagSets {
            has_indices: false,
            ignore_case: false,
            global: false,
            dot_all: false,
            multiline: false,
            sticky: false,
            unicode: false,
            unicode_sets: false,
        }
    }
}

/// A checked interface for setting regular expression flags.
///
/// Note that the `From<&str>` impl is just a shortcut for [`new_unchecked`](Flags::new_unchecked).
#[derive(Debug)]
pub struct Flags {
    sets: FlagSets,
}
impl Flags {
    /// Takes a source flags string using the same format as the JavaScript `RegExp` constructor,
    /// but returns `None` if invalid flags, or invalid combinations of flags, are used.
    pub fn new(source: &str) -> Option<Self> {
        let mut flags = FlagSets::new_empty_flagsets();
        for ch in source.chars() {
            match ch {
                'd' => (!flags.has_indices).then(|| flags.has_indices = true)?,
                'i' => (!flags.ignore_case).then(|| flags.ignore_case = true)?,
                'g' => (!flags.global).then(|| flags.global = true)?,
                's' => (!flags.dot_all).then(|| flags.dot_all = true)?,
                'm' => (!flags.multiline).then(|| flags.multiline = true)?,
                'y' => (!flags.sticky).then(|| flags.sticky = true)?,
                'u' => (!flags.unicode && !flags.unicode_sets).then(|| flags.unicode = true)?,
                'v' => {
                    (!flags.unicode && !flags.unicode_sets).then(|| flags.unicode_sets = true)?
                }
                _ => return None,
            };
        }
        Some(Self { sets: flags })
    }
    /// Same as [`new`](Flags::new), but doesn't care about invalid, duplicate, or bad combinations of flags.
    /// Will instead ignore invalid flags, and cause the [`RegExp`] constructors to report syntax errors
    /// from their JavaScript calls if invalid combinations are used.
    pub fn new_unchecked(source: &str) -> Self {
        let mut flags = FlagSets::new_empty_flagsets();
        for ch in source.chars() {
            match ch {
                'd' => flags.has_indices = true,
                'i' => flags.ignore_case = true,
                'g' => flags.global = true,
                's' => flags.dot_all = true,
                'm' => flags.multiline = true,
                'y' => flags.sticky = true,
                'u' => flags.unicode = true,
                'v' => flags.unicode_sets = true,
                _ => {}
            }
        }
        Self { sets: flags }
    }
    /// The inner [`FlagSets`]
    pub fn inspect(&self) -> &FlagSets {
        &self.sets
    }
    fn build(&self) -> JsValue {
        // Even though no valid flags string contains 8 flags,
        // we want to avoid panicking here when an invalid combination of
        // flags is set using new_unchecked
        let mut bytes_rep = [0u8; 8];
        let mut idx = 0;
        fn set_fn(bytes: &mut [u8; 8], idx: &mut usize, v: u8) {
            bytes[*idx] = v;
            *idx += 1;
        }
        let mut set = |v: u8| set_fn(&mut bytes_rep, &mut idx, v);
        self.sets.has_indices.then(|| set(b'd'));
        self.sets.ignore_case.then(|| set(b'i'));
        self.sets.global.then(|| set(b'g'));
        self.sets.dot_all.then(|| set(b's'));
        self.sets.multiline.then(|| set(b'm'));
        self.sets.sticky.then(|| set(b'y'));
        self.sets.unicode.then(|| set(b'u'));
        self.sets.unicode_sets.then(|| set(b'v'));
        JsValue::from_str(std::str::from_utf8(&bytes_rep[..idx]).unwrap())
    }
}
impl From<&str> for Flags {
    /// Shortcut for [`new_unchecked`](Flags::new_unchecked)
    fn from(value: &str) -> Self {
        Self::new_unchecked(value)
    }
}

/// The result of a successful [`RegExp::exec`] call.
#[derive(Debug)]
pub struct ExecResult<'h, 'p> {
    pub match_slice: &'h str,
    pub match_index: usize,
    pub match_length: usize,
    captures: Option<Vec<Capture<'h, 'p>>>,
}
impl ExecResult<'_, '_> {
    /// If the [`d` flag](FlagSets#structfield.has_indices) is set for this expression,
    /// a list of all capture groups' captures.
    pub fn captures(&self) -> Option<&Vec<Capture<'_, '_>>> {
        self.captures.as_ref()
    }
    /// If the [`d` flag](FlagSets#structfield.has_indices) is set for this expression,
    /// a map of all named capture groups' names to their captures.
    pub fn named_captures(&self) -> Option<HashMap<&str, &Capture<'_, '_>>> {
        let captures = self.captures.as_ref()?;
        let mut map = HashMap::new();
        for capture in captures.iter() {
            if let Some(v) = capture.name() {
                map.insert(v, capture);
            };
        }
        Some(map)
    }
}

/// An index, length, slice, and optional group name of a capture in a haystack.
#[derive(Debug)]
pub struct Capture<'h, 'p> {
    group_name: Option<GroupName<'p>>,
    pub index: usize,
    pub length: usize,
    pub slice: &'h str,
}
impl Capture<'_, '_> {
    pub fn name(&self) -> Option<&str> {
        Some(self.group_name.as_ref()?.into())
    }
}

#[derive(Debug)]
enum GroupName<'a> {
    Owned(String),
    Ref(&'a str),
}
impl<'a> Into<&'a str> for &'a GroupName<'a> {
    fn into(self) -> &'a str {
        match self {
            GroupName::Owned(s) => &s[..],
            GroupName::Ref(s) => s,
        }
    }
}

/// Repeatedly match in the same haystack using the same regular expression.
pub struct RegExpStream<'r, 'h, 'p> {
    regex: &'r mut RegExp<'p>,
    haystack: &'h str,
}
impl RegExpStream<'_, '_, '_> {
    /// Calls [`RegExp::exec`] with this stream's expression and haystack
    pub fn next<'s>(&'s mut self) -> Option<ExecResult<'s, 's>> {
        self.regex.exec(self.haystack)
    }
}

#[derive(Debug, Error)]
enum NewRegExpError {
    #[error("Syntax error")]
    SyntaxError(JsValue),
    #[error("Unexpected error")]
    JsError(#[from] JsError),
}
fn construct_regexp_panicking(pattern: &str, flags: JsValue) -> Result<js_sys::RegExp, JsValue> {
    construct_regexp(pattern, flags).map_err(|e| match e {
        NewRegExpError::SyntaxError(v) => v,
        NewRegExpError::JsError(e) => panic!("{:?}", e),
    })
}
fn construct_regexp(pattern: &str, flags: JsValue) -> Result<js_sys::RegExp, NewRegExpError> {
    let global = js_sys::global();
    let regexp_object = get_value_property_str("RegExp", &global).map_err(Into::<JsError>::into)?;
    let regexp_object: &Function = regexp_object
        .dyn_ref()
        .option_context()
        .map_err(Into::<JsError>::into)?;
    let args = js_sys::Array::new_with_length(2);
    args.set(0, JsValue::from_str(pattern));
    args.set(1, flags);
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

#[cfg(test)]
mod tests {
    use wasm_bindgen::{JsCast, JsValue};
    use wasm_bindgen_test::wasm_bindgen_test;

    use crate::{count_bytes_from_utf16_units, find_js_string, slice_capture};
    wasm_bindgen_test::wasm_bindgen_test_configure!(run_in_browser);

    #[wasm_bindgen_test]
    fn test_flags() {
        let flags = super::Flags::new("x");
        // Rejects invalid flag
        assert!(flags.is_none());
        let flags = super::Flags::new("uv");
        // Rejects invalid combination
        assert!(flags.is_none());
        let flags = super::Flags::new("digs").unwrap();
        let sets = flags.inspect();
        assert!(sets.has_indices);
        assert!(sets.ignore_case);
        assert!(sets.global);
        assert!(sets.dot_all);
        assert!(!sets.unicode);
        // Constructs the correct flags string
        assert_eq!(flags.build().as_string().unwrap(), "digs");
    }

    #[wasm_bindgen_test]
    fn test_count_bytes_from_utf16_units() {
        let s = "cool string with fun characters such as: üöä, 宿, 漢字, and even 💙 as well as 🏳‍⚧, which is a ZWJ sequence";
        let utf16_length = 105;
        let utf8_length = s.len();
        assert_eq!(utf8_length, 122);
        assert_eq!(count_bytes_from_utf16_units(s, 87).unwrap(), 104);
        assert_eq!(
            count_bytes_from_utf16_units(s, utf16_length).unwrap(),
            utf8_length
        );
        assert!(count_bytes_from_utf16_units(s, utf16_length + 1).is_none())
    }

    #[wasm_bindgen_test]
    fn test_slice_capture() {
        let haystack = "cool string with fun characters such as: üöä, 宿, 漢字, and even 💙 as well as 🏳‍⚧, which is a ZWJ sequence";
        let begin_index_utf16 = 57;
        let end_index_utf16 = 81;
        let js_array = js_sys::Array::new_with_length(2);
        js_array.set(0, JsValue::from_f64(begin_index_utf16 as f64));
        js_array.set(1, JsValue::from_f64(end_index_utf16 as f64));
        let capture = slice_capture(haystack, &js_array).unwrap();
        assert_eq!("even 💙 as well as 🏳‍⚧,", capture.slice)
    }

    #[wasm_bindgen_test]
    fn test_find_js_string() {
        let s = "cool string with fun characters such as: üöä, 宿, 漢字, and even 💙 as well as 🏳‍⚧, which is a ZWJ sequence";
        let slice = find_js_string(
            s,
            &JsValue::from_str("even 💙 as well as 🏳‍⚧,")
                .dyn_into()
                .unwrap(),
        )
        .unwrap();
        assert_eq!("even 💙 as well as 🏳‍⚧,", slice)
    }
}
