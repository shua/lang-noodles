extern crate proc_macro;
use proc_macro::TokenStream;

#[proc_macro_derive(SubstAny, attributes(subst_skip, subst_bind))]
pub fn derive_subst_any(item: TokenStream) -> TokenStream {
    inner::derive_subst_any(item.into()).into()
}

mod inner {
    use proc_macro2::TokenStream;
    use quote::quote;
    use syn::{
        punctuated::{Pair, Punctuated},
        Token,
    };

    pub fn derive_subst_any(item: TokenStream) -> TokenStream {
        let Ok(expr) = syn::parse2::<syn::DeriveInput>(item) else {
            return quote!(compiler_error!(
                "SubstAny derive only works on enums and structs"
            ));
        };
        match expr.data {
            syn::Data::Struct(s) => for_struct(expr.ident, expr.generics, s),
            syn::Data::Enum(e) => for_enum(expr.ident, expr.generics, e),
            syn::Data::Union(_) => quote!(compiler_error!(
                "SubstAny derive only works on enums and structs"
            )),
        }
    }

    struct VarFieldsPat<'a>(&'a Punctuated<syn::Field, Token![,]>);
    struct VarFieldsSubst<'a>(&'a Punctuated<syn::Field, Token![,]>);
    struct Variants<'a>(&'a syn::Ident, &'a syn::Variant);
    impl quote::ToTokens for Variants<'_> {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            let Variants(enum_id, variant) = self;
            let v_id = &variant.ident;
            tokens.extend(std::iter::once(quote!(#enum_id :: #v_id)));
            let field_subst = match &self.1.fields {
                syn::Fields::Named(n) => {
                    n.brace_token
                        .surround(tokens, |tokens| VarFieldsPat(&n.named).to_tokens(tokens));
                    VarFieldsSubst(&n.named)
                }
                syn::Fields::Unnamed(u) => {
                    u.paren_token
                        .surround(tokens, |tokens| VarFieldsPat(&u.unnamed).to_tokens(tokens));
                    VarFieldsSubst(&u.unnamed)
                }
                syn::Fields::Unit => {
                    tokens.extend(std::iter::once(quote!(=> {})));
                    return;
                }
            };

            quote!(=> { #field_subst }).to_tokens(tokens);
        }
    }
    fn field_pairs(
        f: &Punctuated<syn::Field, Token![,]>,
    ) -> impl Iterator<Item = (&syn::Field, Option<&Token![,]>, bool, syn::Ident)> {
        f.pairs().enumerate().map(move |(i, p)| {
            let id = quote::format_ident!("_{i}");
            match p {
                Pair::Punctuated(f, p) => (f, Some(p), f.attrs.contains(&subst_skip_attr()), id),
                Pair::End(f) => (f, None, f.attrs.contains(&subst_skip_attr()), id),
            }
        })
    }
    impl quote::ToTokens for VarFieldsPat<'_> {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            let &VarFieldsPat(fs) = self;
            if fs.is_empty() {
                return;
            }

            for (f, p, skip_attr, id) in field_pairs(fs) {
                let named_ident = f.ident.as_ref().map(|f| quote!(#f : ));
                let cap_ident = if skip_attr {
                    quote!(_).into_token_stream()
                } else {
                    id.into_token_stream()
                };
                tokens.extend([
                    named_ident.into_token_stream(),
                    cap_ident,
                    p.into_token_stream(),
                ])
            }
        }
    }
    impl quote::ToTokens for VarFieldsSubst<'_> {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            let &VarFieldsSubst(fs) = self;
            if fs.is_empty() {
                return;
            }
            let mut last = None;
            let inc_x = quote!(+1);
            for (f, _, skip_attr, id) in field_pairs(fs) {
                if skip_attr {
                    continue;
                }
                tokens.extend(
                    last.map(|(id, inc)| quote!(#id.subst(x #inc, v.clone());))
                        .into_iter(),
                );
                let bind = f.attrs.contains(&subst_bind_attr());
                last = Some((id, bind.then_some(&inc_x)));
            }
            tokens.extend(
                last.map(|(id, inc)| quote!(#id.subst(x #inc, v);))
                    .into_iter(),
            );
        }
    }

    fn subst_skip_attr() -> syn::Attribute {
        syn::parse_quote!(#[subst_skip])
    }
    fn subst_bind_attr() -> syn::Attribute {
        syn::parse_quote!(#[subst_bind])
    }

    fn subst_constraints<'a>(
        fs: &'a syn::Fields,
        t_gen: &'a syn::TypeParam,
        count: &'a mut usize,
    ) -> impl Iterator<Item = syn::WherePredicate> + 'a {
        fs.iter()
            .filter(|f| !f.attrs.contains(&subst_skip_attr()))
            .map(move |f| {
                *count += 1;
                let ty = &f.ty;
                syn::parse_quote!(#ty : subst::Subst<#t_gen>)
            })
    }

    fn for_enum(name: syn::Ident, mut gen: syn::Generics, d: syn::DataEnum) -> TokenStream {
        let t_gen: syn::TypeParam = syn::parse_quote!(T);
        let mut where_clause = gen.where_clause.take().unwrap_or_else(|| syn::WhereClause {
            where_token: syn::token::Where::default(),
            predicates: syn::punctuated::Punctuated::default(),
        });
        if true {
            let mut subst_count = 0;
            let mut must_clone = false;
            for variant in &d.variants {
                where_clause.predicates.extend(subst_constraints(
                    &variant.fields,
                    &t_gen,
                    &mut subst_count,
                ));
                must_clone |= subst_count > 1;
            }
            if must_clone {
                where_clause
                    .predicates
                    .push(syn::parse_quote!(#t_gen: Clone));
            }
        }
        if !where_clause.predicates.is_empty() {
            gen.where_clause = Some(where_clause);
        }
        let (_, ty_gen, where_clause) = gen.split_for_impl();
        let mut impl_gen = gen.clone();
        let gen_ty_start = (0..gen.params.len()).find(|i| {
            matches!(
                gen.params[*i],
                syn::GenericParam::Type(_) | syn::GenericParam::Const(_)
            )
        });
        if let Some(i) = gen_ty_start {
            impl_gen.params.insert(i, t_gen.clone().into());
        } else {
            impl_gen.params.push(t_gen.clone().into());
        }
        let (impl_gen, _, _) = impl_gen.split_for_impl();
        let t_gen = &t_gen;

        let variants = d.variants.iter().map(|v| Variants(&name, v));
        quote! {
            impl #impl_gen subst::SubstAny<#t_gen> for #name #ty_gen #where_clause {
                fn subst_any(&mut self, x: usize, v: #t_gen) {
                    use subst::Subst as _;
                    match self {
                        #(#variants)*
                    }
                }
            }
        }
    }

    struct StructSubst<'a>(&'a syn::Ident, &'a syn::Fields);
    impl quote::ToTokens for StructSubst<'_> {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            let &StructSubst(name, fs) = self;
            if fs.is_empty() || matches!(fs, syn::Fields::Unit) {
                return;
            }

            tokens.extend(std::iter::once(quote!(let #name)));
            let field_subst = match fs {
                syn::Fields::Named(n) => {
                    n.brace_token
                        .surround(tokens, |tokens| VarFieldsPat(&n.named).to_tokens(tokens));
                    VarFieldsSubst(&n.named)
                }
                syn::Fields::Unnamed(u) => {
                    u.paren_token
                        .surround(tokens, |tokens| VarFieldsPat(&u.unnamed).to_tokens(tokens));
                    VarFieldsSubst(&u.unnamed)
                }
                syn::Fields::Unit => unreachable!(),
            };
            tokens.extend(std::iter::once(quote! {= self;
                #field_subst
            }));
        }
    }

    fn for_struct(name: syn::Ident, mut gen: syn::Generics, d: syn::DataStruct) -> TokenStream {
        let t_gen: syn::TypeParam = syn::parse_quote!(T);
        let mut where_clause = gen.where_clause.take().unwrap_or_else(|| syn::WhereClause {
            where_token: syn::token::Where::default(),
            predicates: syn::punctuated::Punctuated::default(),
        });
        if true {
            let mut subst_count = 0;
            where_clause
                .predicates
                .extend(subst_constraints(&d.fields, &t_gen, &mut subst_count));
            if subst_count > 1 {
                where_clause.predicates.push(syn::parse_quote!(T: Clone));
            }
        }
        if !where_clause.predicates.is_empty() {
            gen.where_clause = Some(where_clause);
        }
        let (_, ty_gen, where_clause) = gen.split_for_impl();
        let mut impl_gen = gen.clone();
        let gen_ty_start = (0..gen.params.len()).find(|i| {
            matches!(
                gen.params[*i],
                syn::GenericParam::Type(_) | syn::GenericParam::Const(_)
            )
        });
        if let Some(i) = gen_ty_start {
            impl_gen.params.insert(i, t_gen.clone().into());
        } else {
            impl_gen.params.push(t_gen.clone().into());
        }
        let (impl_gen, _, _) = impl_gen.split_for_impl();
        let subst_struct = StructSubst(&name, &d.fields);
        let t_gen = &t_gen;
        quote! {
            impl #impl_gen subst::SubstAny<#t_gen> for #name #ty_gen #where_clause {
                fn subst_any(&mut self, x: usize, v: #t_gen) {
                    use subst::Subst as _;
                    #subst_struct
                }
            }
        }
    }
}
