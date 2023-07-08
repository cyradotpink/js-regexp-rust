use js_sys::JsString;
use std::{
    collections::HashMap,
    hash::{Hash, Hasher},
};
use wasm_bindgen::{JsCast, JsValue};

/// A wrapped JavaScript `RegExp`. The main type of this crate.
#[derive(Debug)]
pub struct RegExp<'p> {
    inner: js_sys::RegExp,
    pattern: PatternSource<'p>,
}
impl<'p> RegExp<'p> {
    /// Constructs a new regular expression, backed by a `RegExp` on the JavaScript heap.
    /// When constructed by this function, the returned value's lifetime becomes tied to the
    /// provided `&str` pattern. This may not always be what you want; See `new_with_ownership`
    /// for an alternative that takes ownership of a `String` pattern instead.
    pub fn new(pattern: &'p str, flags: &str) -> Self {
        Self {
            inner: js_sys::RegExp::new(pattern, flags),
            pattern: PatternSource::Ref(pattern),
        }
    }
    /// Constructs a new regular expression, backed by a `RegExp` on the JavaScript heap.
    /// Takes ownership of the provided `String` pattern. Use `new` instead if you have a `&'static str`,
    /// or if it otherwise makes sense for the constructed value to store only a reference to your pattern.
    pub fn new_with_ownership(pattern: String, flags: &str) -> Self {
        Self {
            inner: js_sys::RegExp::new(&pattern, flags),
            pattern: PatternSource::Owned(pattern),
        }
    }
    /// Constructs a new regular expression, backed by a `RegExp` on the JavaScript heap.
    /// Unlike with `new`, the returned structure does not hold on to a reference to the provided
    /// `&str` pattern. This is achieved by copying any group names from the JavaScript heap every time the regular expression
    /// is used.
    pub fn new_with_copying(pattern: &str, flags: &str) -> Self {
        Self {
            inner: js_sys::RegExp::new(&pattern, flags),
            pattern: PatternSource::Copy,
        }
    }
    /// Calls the underlying JavaScript `RegExp`'s `exec` method. Returns `None` if the JavaScript call returns null.
    /// The returned `ExecResult`'s `captures` member is `None` if the underlying JavaScript call returns an object
    /// that does not have an `indices` property, which is only present when the `d` flag is set for the regular expression.
    /// Panics if the JavaScript call doesn't behave as expected.
    pub fn exec<'h>(&'p mut self, haystack: &'h str) -> Option<ExecResult<'h, 'p>> {
        let result = self.inner.exec(haystack)?;

        let utf16_match_index = get_value_property_str("index", &result).as_f64().unwrap() as usize;
        let utf8_match_index = count_bytes_from_utf16_units(haystack, utf16_match_index);
        let matched = &haystack[utf8_match_index..];
        let string_match_js = result.iter().next().unwrap();
        let string_match_js: &js_sys::JsString = string_match_js.unchecked_ref();
        let utf16_match_length = string_match_js.length() as usize;
        let utf8_match_length = count_bytes_from_utf16_units(matched, utf16_match_length);
        let matched = &matched[..utf8_match_length];
        let indices_array_js = get_value_property_str("indices", &result);

        let mut exec_result = ExecResult {
            match_slice: matched,
            match_index: utf8_match_index,
            match_length: utf16_match_length,
            captures: None,
        };
        if !indices_array_js.is_array() {
            return Some(exec_result);
        }

        let mut captures_vec = Vec::new();
        let js_array_iter = js_sys::try_iter(&indices_array_js).unwrap().unwrap();
        for indices_js in js_array_iter.skip(1) {
            let indices_js = indices_js.unwrap();
            let capture = slice_capture(haystack, &indices_js);
            captures_vec.push(capture);
        }
        let named_indices_js = get_value_property_str("groups", &indices_array_js);
        if !named_indices_js.is_object() {
            let _ = exec_result
                .captures
                .insert(CapturesList { vec: captures_vec });
            return Some(exec_result);
        }

        let group_names = js_sys::Reflect::own_keys(&named_indices_js).unwrap();
        for group_name_js in group_names.iter() {
            let group_name_js: js_sys::JsString = group_name_js.unchecked_into();
            let indices_js = js_sys::Reflect::get(&named_indices_js, &group_name_js).unwrap();
            let capture = slice_capture(haystack, &indices_js);
            let group_name = match self.pattern.get() {
                Some(pattern) => GroupName::Ref(find_js_string(pattern, &group_name_js).unwrap()),
                None => GroupName::Owned(group_name_js.as_string().unwrap()),
            };
            let _ = captures_vec
                .iter_mut()
                .find(|v| v.index == capture.index && v.length == capture.length)
                .unwrap()
                .group_name
                .insert(group_name);
        }

        let _ = exec_result
            .captures
            .insert(CapturesList { vec: captures_vec });
        Some(exec_result)
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

/// The result type of `RegExp::exec`.
#[derive(Debug)]
pub struct ExecResult<'h, 'p> {
    pub match_slice: &'h str,
    pub match_index: usize,
    pub match_length: usize,
    pub captures: Option<CapturesList<'h, 'p>>,
}

/// A list of captures.
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

/// An index, length, slice and optional group name of a capture in a haystack.
#[derive(Debug)]
pub struct Capture<'h, 'p> {
    pub group_name: Option<GroupName<'p>>,
    pub index: usize,
    pub length: usize,
    pub slice: &'h str,
}

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

fn get_value_property_usize(key: usize, target: &JsValue) -> JsValue {
    let key = key as u32;
    js_sys::Reflect::get_u32(target, key).unwrap()
}

fn get_value_property_str(key: &str, target: &JsValue) -> JsValue {
    let key = JsValue::from_str(key);
    js_sys::Reflect::get(target, &key).unwrap()
}

fn slice_capture<'h, 'p>(haystack: &'h str, indices: &JsValue) -> Capture<'h, 'p> {
    let utf16_index = get_value_property_usize(0, indices).as_f64().unwrap() as usize;
    let utf16_end = get_value_property_usize(1, indices).as_f64().unwrap() as usize;
    let utf16_length = utf16_end - utf16_index;
    let capture = haystack;
    let utf8_begin = count_bytes_from_utf16_units(capture, utf16_index);
    let capture = &capture[utf8_begin..];
    let utf8_length = count_bytes_from_utf16_units(capture, utf16_length);
    let capture = &capture[..utf8_length];
    Capture {
        group_name: None,
        index: utf8_begin,
        length: utf8_length,
        slice: capture,
    }
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

fn count_bytes_from_utf16_units(s: &str, n_units: usize) -> usize {
    let mut n_units = n_units as isize;
    let mut i = s.char_indices();
    while n_units > 0 {
        let (_, char) = i.next().unwrap();
        n_units -= char.len_utf16() as isize;
    }
    let bytes_counted = i.next().map(|v| v.0).unwrap_or(s.len());
    bytes_counted
}
