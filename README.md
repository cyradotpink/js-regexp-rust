js-regexp
=========

**Ergonomic Rust bindings to the JavaScript standard built-in `RegExp` object**

[![Latest Version](https://img.shields.io/crates/v/js-regexp?style=flat-square)](https://crates.io/crates/js-regexp)
[![Documentation](https://img.shields.io/docsrs/js-regexp/latest?style=flat-square)](https://docs.rs/js-regexp)

In Wasm environments that are glued to a JavaScript runtime, depending on a crate like `regex`
for regular expression matching can seem silly (at least when package size is a concern) - There's a perfectly fine
regular expression engine right there, in JavaScript! This crate aims to provide a convenient interface using `js-sys`'s
raw bindings to JavaScript's `RegExp` built-in.

## Usage
See [docs.rs](https://docs.rs/js-regexp/) for detailed usage information.

#### Basic example
```rust
use js_regexp::{flags, RegExp};

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
```

## Stability
js-regexp is not tested extensively. \
The public interface may change across minor versions while
js-regexp is pre-1.0.0, but because of its simplicity and small scope I expect any required changes in consuming code to
be quick and easy.

Issues and pull requests are welcome!

## License
js-regexp is somewhat arbitrarily released under the MIT License. Worrying about copyright with small utility crates like this seems
not worth it - more restrictive licenses can never address all possible cases in just the right way anyway.
Copyright's ability to create justice is limited. So just don't be evil, please ❤️