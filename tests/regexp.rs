use js_regexp::{flags, Flags, RegExp};
use wasm_bindgen_test::*;

wasm_bindgen_test_configure!(run_in_browser);

#[wasm_bindgen_test]
pub fn test_basic_expression() {
    let mut re = RegExp::new(r#"(?<greeting>\w+), (?<name>\w+)"#, flags!("d")).unwrap();
    let result = re.exec("Hello, Alice!").unwrap();

    let mut iter = result.captures().unwrap().iter();
    let named_captures = result.named_captures().unwrap();
    assert_eq!("Hello, Alice", result.match_slice);
    assert_eq!(0, result.match_index);
    assert_eq!(12, result.match_length);
    assert_eq!("Hello", iter.next().unwrap().slice);
    assert_eq!("Hello", named_captures.get("greeting").unwrap().slice);
    assert_eq!(5, iter.next().unwrap().length);
    assert_eq!(7, named_captures.get("name").unwrap().index);
}

#[wasm_bindgen_test]
pub fn test_unicode_expression() {
    let mut re = RegExp::new("üöä|宿|💙", Flags::new("g").unwrap()).unwrap();
    let haystack = "cool string with fun characters such as: üöä, 宿, 漢字, and even 💙 as well as 🏳‍⚧, which is a ZWJ sequence";

    let result = re.exec(haystack).unwrap();
    assert_eq!("üöä", result.match_slice);

    let result = re.exec(haystack).unwrap();
    assert_eq!("宿", result.match_slice);

    let result = re.exec(haystack).unwrap();
    assert_eq!("💙", result.match_slice);

    assert!(re.exec(haystack).is_none());
}

struct TestIter {}
impl Iterator for TestIter {
    type Item = ();
    fn next(&mut self) -> Option<Self::Item> {
        Some(())
    }
}

#[wasm_bindgen_test]
pub fn test_stream() {
    let mut re = RegExp::new(r#"(?<greeting>\w+), (?<name>\w+)"#, "dg".into()).unwrap();
    let haystack = "Hi, Alice! Hello, Bob! Sup, Claire?";
    assert!(re.exec(haystack).is_some());
    let mut stream = re.stream(haystack);
    assert_eq!(11, stream.next().unwrap().match_index);

    re.inner().set_last_index(0);

    let mut count = 0usize;
    let mut stream = re.stream(haystack);
    while let Some(v) = stream.next() {
        match count {
            0 => {}
            1 => {}
            2 => assert_eq!("Sup", v.captures().unwrap().iter().next().unwrap().slice),
            _ => panic!("Too many items in stream"),
        }
        count += 1;
    }
    assert_eq!(3, count);
}

#[wasm_bindgen_test]
pub fn test_flags_macro() {
    let flags = js_regexp::flags!("d");
    let inner = flags.inspect();
    assert!(inner.has_indices);
}
