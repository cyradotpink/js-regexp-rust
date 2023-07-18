use proc_macro::TokenStream;
use quote::quote;

struct FlagSets {
    d: bool,
    i: bool,
    g: bool,
    s: bool,
    m: bool,
    y: bool,
    u: bool,
    v: bool,
}
fn new_empty_flagsets() -> FlagSets {
    FlagSets {
        d: false,
        i: false,
        g: false,
        s: false,
        m: false,
        y: false,
        u: false,
        v: false,
    }
}
fn check_flags(source: &str) -> Result<(), char> {
    let mut flags = new_empty_flagsets();
    let mut inner = |ch: char| -> Option<()> {
        match ch {
            'd' => (!flags.d).then(|| flags.d = true)?,
            'i' => (!flags.i).then(|| flags.i = true)?,
            'g' => (!flags.g).then(|| flags.g = true)?,
            's' => (!flags.s).then(|| flags.s = true)?,
            'm' => (!flags.m).then(|| flags.m = true)?,
            'y' => (!flags.y).then(|| flags.y = true)?,
            'u' => (!flags.u && !flags.v).then(|| flags.u = true)?,
            'v' => (!flags.u && !flags.v).then(|| flags.v = true)?,
            _ => return None,
        };
        Some(())
    };
    for ch in source.chars() {
        if inner(ch).is_none() {
            return Err(ch);
        }
    }
    Ok(())
}

/// Checks validity of a flags string literal at compile time and inserts a therefore
/// safe runtime call to [`Flags::new_unchecked`](struct.Flags.html#method.new_unchecked).
#[proc_macro]
pub fn flags(item: TokenStream) -> TokenStream {
    let item = syn::parse_macro_input!(item as syn::Lit);
    let item = match item {
        syn::Lit::Str(v) => v,
        _ => panic!("Not a string literal"),
    };
    let value = item.value();
    if let Err(e) = check_flags(&value) {
        panic!("Invalid flags at char: '{}'", e);
    }
    quote!(::js_regexp::Flags::new_unchecked(#item)).into()
}
