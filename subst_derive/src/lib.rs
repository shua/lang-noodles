extern crate proc_macro;
use proc_macro::TokenStream;

#[proc_macro_derive(SubstAny, attributes(subst_any, subst_bind))]
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
            syn::Data::Struct(s) => for_struct(expr.ident, expr.generics, expr.attrs, s),
            syn::Data::Enum(e) => for_enum(expr.ident, expr.generics, expr.attrs, e),
            syn::Data::Union(_) => quote!(compiler_error!(
                "SubstAny derive only works on enums and structs"
            )),
        }
    }

    struct VarFieldsPat<'a>(&'a Punctuated<syn::Field, Token![,]>, &'a [syn::Type]);
    struct VarFieldsSubst<'a>(&'a Punctuated<syn::Field, Token![,]>, &'a [syn::Type]);
    struct Variants<'a>(&'a syn::Ident, &'a syn::Variant, &'a [syn::Type]);
    impl quote::ToTokens for Variants<'_> {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            let Variants(enum_id, variant, subst_ty) = self;
            let v_id = &variant.ident;
            tokens.extend(std::iter::once(quote!(#enum_id :: #v_id)));
            let field_subst = match &self.1.fields {
                syn::Fields::Named(n) => {
                    n.brace_token.surround(tokens, |tokens| {
                        VarFieldsPat(&n.named, subst_ty).to_tokens(tokens)
                    });
                    VarFieldsSubst(&n.named, subst_ty)
                }
                syn::Fields::Unnamed(u) => {
                    u.paren_token.surround(tokens, |tokens| {
                        VarFieldsPat(&u.unnamed, subst_ty).to_tokens(tokens)
                    });
                    VarFieldsSubst(&u.unnamed, subst_ty)
                }
                syn::Fields::Unit => {
                    tokens.extend(std::iter::once(quote!(=> {})));
                    return;
                }
            };

            quote!(=> { #field_subst }).to_tokens(tokens);
        }
    }
    fn field_pairs<'a>(
        f: &'a Punctuated<syn::Field, Token![,]>,
        subst_ty: &'a [syn::Type],
    ) -> impl Iterator<Item = (&'a syn::Field, Option<&'a Token![,]>, bool, syn::Ident)> + 'a {
        f.pairs().enumerate().map(move |(i, p)| {
            let id = quote::format_ident!("_{i}");
            match p {
                Pair::Punctuated(f, p) => (f, Some(p), subst_ty.contains(&&f.ty), id),
                Pair::End(f) => (f, None, subst_ty.contains(&&f.ty), id),
            }
        })
    }
    impl quote::ToTokens for VarFieldsPat<'_> {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            let &VarFieldsPat(fs, subst_ty) = self;
            if fs.is_empty() {
                return;
            }

            for (f, p, subst_ty, id) in field_pairs(fs, subst_ty) {
                let named_ident = f.ident.as_ref().map(|f| quote!(#f : ));
                let cap_ident = if subst_ty {
                    id.into_token_stream()
                } else {
                    quote!(_).into_token_stream()
                };
                tokens.extend([
                    named_ident.into_token_stream(),
                    cap_ident,
                    p.into_token_stream(),
                ])
            }
        }
    }
    fn subst_bind_attr() -> syn::Attribute {
        syn::parse_quote!(#[subst_bind])
    }
    impl quote::ToTokens for VarFieldsSubst<'_> {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            let &VarFieldsSubst(fs, subst_ty) = self;
            if fs.is_empty() {
                return;
            }
            let mut last = None;
            let inc_x = quote!(+1);
            for (f, _, subst_ty, id) in field_pairs(fs, subst_ty) {
                if !subst_ty {
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

    fn subst_constraints<'a>(
        fs: &'a syn::Fields,
        t_gen: &'a syn::TypeParam,
        count: &'a mut usize,
        subst_ty: &'a [syn::Type],
    ) -> impl Iterator<Item = syn::WherePredicate> + 'a {
        fs.iter()
            .filter(|f| subst_ty.contains(&f.ty))
            .map(move |f| {
                *count += 1;
                let ty = &f.ty;
                syn::parse_quote!(#ty : ::subst::Subst<#t_gen>)
            })
    }

    fn for_enum(
        name: syn::Ident,
        mut gen: syn::Generics,
        attrs: Vec<syn::Attribute>,
        d: syn::DataEnum,
    ) -> TokenStream {
        let t_gen: syn::TypeParam = syn::parse_quote!(T);
        let mut subst_ty = vec![];
        if let Some(attr) = attrs
            .iter()
            .find(|a| a.path() == &syn::parse_quote!(subst_any))
        {
            let res = attr.parse_args_with(<Punctuated<syn::Type, Token![,]>>::parse_terminated);
            match res {
                Ok(tys) => subst_ty.extend(tys),
                Err(err) => return err.into_compile_error(),
            }
        }
        let mut where_clause = gen.where_clause.take().unwrap_or_else(|| syn::WhereClause {
            where_token: syn::token::Where::default(),
            predicates: syn::punctuated::Punctuated::default(),
        });
        if true {
            let mut subst_count = 0;
            let mut must_clone = false;
            for variant in &d.variants {
                subst_constraints(&variant.fields, &t_gen, &mut subst_count, &subst_ty).count();
                must_clone |= subst_count > 1;
            }
            let t_gen = &t_gen;
            for ty in &subst_ty {
                where_clause
                    .predicates
                    .push(syn::parse_quote!(#ty : ::subst::Subst<#t_gen>));
            }
            if must_clone {
                where_clause
                    .predicates
                    .push(syn::parse_quote!(#t_gen: ::core::clone::Clone));
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

        let variants = d.variants.iter().map(|v| Variants(&name, v, &subst_ty));
        quote! {
            impl #impl_gen ::subst::SubstAny<#t_gen> for #name #ty_gen #where_clause {
                fn subst_any(&mut self, x: usize, v: #t_gen) {
                    use ::subst::Subst as _;
                    match self {
                        #(#variants)*
                    }
                }
            }
        }
    }

    struct StructSubst<'a>(&'a syn::Ident, &'a syn::Fields, &'a [syn::Type]);
    impl quote::ToTokens for StructSubst<'_> {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            let &StructSubst(name, fs, subst_ty) = self;
            if fs.is_empty() || matches!(fs, syn::Fields::Unit) {
                return;
            }

            tokens.extend(std::iter::once(quote!(let #name)));
            let field_subst = match fs {
                syn::Fields::Named(n) => {
                    n.brace_token.surround(tokens, |tokens| {
                        VarFieldsPat(&n.named, subst_ty).to_tokens(tokens)
                    });
                    VarFieldsSubst(&n.named, subst_ty)
                }
                syn::Fields::Unnamed(u) => {
                    u.paren_token.surround(tokens, |tokens| {
                        VarFieldsPat(&u.unnamed, subst_ty).to_tokens(tokens)
                    });
                    VarFieldsSubst(&u.unnamed, subst_ty)
                }
                syn::Fields::Unit => unreachable!(),
            };
            tokens.extend(std::iter::once(quote! {= self;
                #field_subst
            }));
        }
    }

    fn for_struct(
        name: syn::Ident,
        mut gen: syn::Generics,
        attrs: Vec<syn::Attribute>,
        d: syn::DataStruct,
    ) -> TokenStream {
        let t_gen: syn::TypeParam = syn::parse_quote!(T);
        let mut subst_ty = vec![];
        if let Some(attr) = attrs
            .iter()
            .find(|a| a.path() == &syn::parse_quote!(subst_any))
        {
            let res = attr.parse_args_with(<Punctuated<syn::Type, Token![,]>>::parse_terminated);
            match res {
                Ok(tys) => subst_ty.extend(tys),
                Err(err) => return err.into_compile_error(),
            }
        }
        let mut where_clause = gen.where_clause.take().unwrap_or_else(|| syn::WhereClause {
            where_token: syn::token::Where::default(),
            predicates: syn::punctuated::Punctuated::default(),
        });
        if true {
            let mut subst_count = 0;
            where_clause.predicates.extend(subst_constraints(
                &d.fields,
                &t_gen,
                &mut subst_count,
                &subst_ty,
            ));
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
        let subst_struct = StructSubst(&name, &d.fields, &subst_ty);
        let t_gen = &t_gen;
        quote! {
            impl #impl_gen ::subst::SubstAny<#t_gen> for #name #ty_gen #where_clause {
                fn subst_any(&mut self, x: usize, v: #t_gen) {
                    use ::subst::Subst as _;
                    #subst_struct
                }
            }
        }
    }
}
