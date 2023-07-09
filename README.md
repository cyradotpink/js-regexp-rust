js-regexp
=========

**Ergonomic Rust bindings to the JavaScript standard built-in `RegExp` object**

[![Latest Version](https://img.shields.io/crates/v/js-regexp?style=flat-square)](https://crates.io/crates/js-regexp)
[![Documentation](https://img.shields.io/docsrs/js-regexp/latest?style=flat-square)](https://docs.rs/js-regexp)

In WASM environments that are attached to a JavaScript runtime, depending on a crate like `regex`
for regular expression matching can seem silly (at least when package size is a concern) - There's a perfectly fine
regular expression engine right there, in JavaScript! And while `js-sys` does
_expose_ the standard built-in `RegExp` object, it does not aim to provide a convenient interface. \
This crate aims to bridge that gap.

## Usage
See [docs.rs](https://docs.rs/js-regexp/) for detailed usage information.
#### Basic example
```rust
use js_regexp::{RegExp, Flags}

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
```