use js_regexp::{Flags, RegExp};
use wasm_bindgen_test::*;

wasm_bindgen_test_configure!(run_in_browser);

#[wasm_bindgen_test]
pub fn test_basic_expression() {
    let re = RegExp::new(
        r#"(?<greeting>\w+), (?<name>\w+)"#,
        Flags::new("d").unwrap(),
    )
    .unwrap();
    let result = re.exec("Hello, Alice!").unwrap();
    let named_captures = result.captures.unwrap();
    let named_captures = named_captures.get_named_captures_map();
    assert_eq!("Hello, Alice", result.match_slice);
    assert_eq!(0, result.match_index);
    assert_eq!(12, result.match_length);
    assert_eq!("Hello", named_captures.get("greeting").unwrap().slice);
    assert_eq!(7, named_captures.get("name").unwrap().index);
}

#[wasm_bindgen_test]
pub fn test_unicode_expression() {
    let re = RegExp::new("üöä|宿|💙", Flags::new("g").unwrap()).unwrap();
    let haystack = "cool string with fun characters such as: üöä, 宿, 漢字, and even 💙 as well as 🏳‍⚧, which is a ZWJ sequence";
    let result = re.exec(haystack).unwrap();
    assert_eq!("üöä", result.match_slice);
    let result = re.exec(haystack).unwrap();
    assert_eq!("宿", result.match_slice);
    let result = re.exec(haystack).unwrap();
    assert_eq!("💙", result.match_slice);

    assert!(re.exec(haystack).is_none());
}
