js-regexp
=========

**Ergonomic Rust bindings to the JavaScript standard built-in `RegExp` object**

[![Latest Version](https://img.shields.io/crates/v/js-regexp?style=flat-square)](https://crates.io/crates/js-regexp)
[![Documentation](https://img.shields.io/docsrs/js-regexp/latest?style=flat-square)](https://docs.rs/js-regexp)

In Wasm environments that are glued to a JavaScript runtime, depending on a crate like `regex`
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

## Stability and future
js-regexp is not tested extensively, and I am not quite happy with the API yet. \
I will keep making changes as I use it in my own projects and get a better feel for where there are issues,
and where this crate could still be nicer to use. The public interface may change between minor versions while
js-regexp is 0.x.x, but because of its simplicity and small scope I expect any required changes in consuming code to
be quick and easy.
An easy and useful addition would be a wrapper around
[RegExp.test()](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/RegExp/test),
so I'll probably add that at some point.

Issues and pull requests are welcome!

## License
Starting with version 0.1.1, js-regexp is MIT-licensed. Worrying about copyright with small utility crates like this seems
not worth it - more restrictive licenses can never address all possible cases in just the right away. Turns out copyright,
as a system, isn't very good at creating justice. So just, like, don't be evil. Please!