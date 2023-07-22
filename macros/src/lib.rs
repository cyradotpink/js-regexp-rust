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

#[derive(Clone, Copy, Debug)]
enum Mode {
    Skip,
    Do,
}

#[proc_macro_derive(EnumConvert, attributes(enum_convert))]
pub fn derive(input: TokenStream) -> TokenStream {
    let input = syn::parse_macro_input!(input as syn::ItemEnum);
    let enum_ident = input.ident;
    let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();
    let mut output = proc_macro::TokenStream::new();

    let outer_attr = input
        .attrs
        .iter()
        .find(|v| v.path().is_ident("enum_convert"));
    let mut into_mode: Mode = Mode::Skip;
    let mut from_mode: Mode = Mode::Skip;
    if let Some(attr) = outer_attr {
        let _ = attr.parse_nested_meta(|meta| {
            if meta.path.is_ident("into") {
                into_mode = Mode::Do;
            } else if meta.path.is_ident("from") {
                from_mode = Mode::Do;
            }
            Ok(())
        });
    }

    for variant in input.variants {
        let variant_ident = variant.ident;
        let type_path = match variant.fields {
            syn::Fields::Unnamed(v) => match v.unnamed.first() {
                Some(v) => match &v.ty {
                    syn::Type::Path(v) => v.to_owned(),
                    _ => continue,
                },
                None => continue,
            },
            _ => continue,
        };

        let mut into_override = into_mode;
        let mut from_override = from_mode;
        let inner_attr = variant
            .attrs
            .iter()
            .find(|v| v.path().is_ident("enum_convert"));
        if let Some(attr) = inner_attr {
            into_override = Mode::Skip;
            from_override = Mode::Skip;
            attr.parse_nested_meta(|meta| {
                if meta.path.is_ident("skip") {
                } else if meta.path.is_ident("from") {
                    from_override = Mode::Do;
                } else if meta.path.is_ident("into") {
                    into_override = Mode::Do;
                } else {
                    return Err(meta.error("Invalid mode override"));
                }
                Ok(())
            })
            .unwrap()
        }

        if let Mode::Do = from_override {
            output.extend(Into::<proc_macro::TokenStream>::into(quote! {
                impl #impl_generics From<#type_path> for #enum_ident #ty_generics #where_clause {
                    fn from(value: #type_path) -> Self {
                        Self::#variant_ident(value)
                    }
                }
            }))
        }
        if let Mode::Do = into_override {
            output.extend(Into::<proc_macro::TokenStream>::into(quote! {
                impl #impl_generics TryInto<#type_path> for #enum_ident #ty_generics #where_clause {
                    type Error = &'static str;
                    fn try_into(self) -> Result<#type_path, Self::Error> {
                        match self {
                            Self::#variant_ident(value) => Ok(value),
                            _ => Err("Incorrect Variant"),
                        }
                    }
                }
            }));
        }
    }
    output.into()
}
