//! `T: Tr with { fn m(&self, x: X) -> (r: R) requires P ensures Q allocates e; fn drop allocates 0; }`
//! on a function's type parameter: a specification of the bound's methods. Inside the function,
//! a call `t.m(x)` gets it; a caller must show that the type it instantiates `T` with meets it.
//!
//! syn_verus carries the block as the attribute `#[verus_bound_spec{..}]` on the type parameter;
//! here it becomes `requires` clauses of the function, through `call_requires`, `call_ensures`
//! and `call_allocates` (and, for `drop`, `bound_drop_alloc_free::<T>()`, which Verus checks
//! against the instantiation's drop glue):
//! - `requires P`:   `forall|args| P ==> call_requires(T::m, (args,))`
//! - `ensures Q`:    `forall|args, r: R| call_ensures(T::m, (args,), r) ==> Q`
//! - `allocates e`:  `forall|args| call_allocates(T::m, (args,)) <= e`
//! (`self` is the first argument; `Self` is `T`)

use proc_macro2::{Group, TokenStream, TokenTree};
use quote::{quote, quote_spanned};
use verus_syn::parse::{Parse, ParseStream};
use verus_syn::spanned::Spanned;
use verus_syn::{
    Expr, FnArgKind, GenericParam, Ident, Meta, Pat, ReturnType, Signature, Token, Type,
};

enum BoundFn {
    Method(Signature),
    Drop(Expr),
}

struct BoundFns(Vec<BoundFn>);

impl Parse for BoundFns {
    fn parse(input: ParseStream) -> verus_syn::Result<Self> {
        let mut fns = Vec::new();
        while !input.is_empty() {
            if input.peek(Token![fn])
                && input.peek2(Ident)
                && !input.peek3(verus_syn::token::Paren)
                && !input.peek3(Token![<])
            {
                let _: Token![fn] = input.parse()?;
                let name: Ident = input.parse()?;
                if name != "drop" {
                    return Err(verus_syn::Error::new(
                        name.span(),
                        "expected a method signature, or `fn drop allocates 0;`",
                    ));
                }
                let _: Token![allocates] = input.parse()?;
                let e: Expr = input.parse()?;
                let _: Token![;] = input.parse()?;
                fns.push(BoundFn::Drop(e));
            } else {
                let sig: Signature = input.parse()?;
                let _: Token![;] = input.parse()?;
                fns.push(BoundFn::Method(sig));
            }
        }
        Ok(BoundFns(fns))
    }
}

fn replace_idents(ts: TokenStream, from: &str, to: &TokenStream) -> TokenStream {
    ts.into_iter()
        .flat_map(|tt| -> Vec<TokenTree> {
            match tt {
                TokenTree::Ident(i) if i == from => to.clone().into_iter().collect(),
                TokenTree::Group(g) => {
                    let mut ng = Group::new(g.delimiter(), replace_idents(g.stream(), from, to));
                    ng.set_span(g.span());
                    vec![TokenTree::Group(ng)]
                }
                other => vec![other],
            }
        })
        .collect()
}

/// Take the `#[verus_bound_spec{..}]` attributes off `generics`' type parameters, and return the
/// `requires` expressions they stand for
pub(crate) fn take_bound_specs(
    generics: &mut verus_syn::Generics,
    builtin: &TokenStream,
    vstd_alloc_check: &TokenStream,
) -> verus_syn::Result<Vec<Expr>> {
    let mut reqs: Vec<TokenStream> = Vec::new();
    for param in generics.params.iter_mut() {
        let GenericParam::Type(tp) = param else { continue };
        let t = tp.ident.clone();
        let t_toks = quote! { #t };
        let mut specs = Vec::new();
        tp.attrs.retain(|a| {
            if a.path().is_ident("verus_bound_spec") {
                specs.push(a.clone());
                false
            } else {
                true
            }
        });
        for a in specs {
            let Meta::List(list) = &a.meta else { continue };
            let fns: BoundFns = verus_syn::parse2(list.tokens.clone())?;
            for f in fns.0 {
                match f {
                    BoundFn::Drop(e) => {
                        let span = e.span();
                        reqs.push(quote_spanned! { span =>
                            (#e == 0int && #vstd_alloc_check::bound_drop_alloc_free::<#t>())
                        });
                    }
                    BoundFn::Method(sig) => {
                        reqs.extend(method_reqs(&sig, &t_toks, builtin)?);
                    }
                }
            }
        }
    }
    reqs.into_iter().map(|r| verus_syn::parse2::<Expr>(r)).collect()
}

fn method_reqs(
    sig: &Signature,
    t: &TokenStream,
    builtin: &TokenStream,
) -> verus_syn::Result<Vec<TokenStream>> {
    let span = sig.ident.span();
    let m = &sig.ident;
    let self_ident = quote_spanned! { span => verus_bound_self };
    let mut binders: Vec<TokenStream> = Vec::new();
    let mut args: Vec<TokenStream> = Vec::new();
    for arg in sig.inputs.iter() {
        match &arg.kind {
            FnArgKind::Receiver(r) => {
                if r.mutability.is_some() && r.reference.is_some() {
                    return Err(verus_syn::Error::new(
                        r.span(),
                        "a bound specification of a `&mut self` method is not supported yet",
                    ));
                }
                let ty = if r.reference.is_some() {
                    quote! { &#t }
                } else {
                    t.clone()
                };
                binders.push(quote! { #self_ident: #ty });
                args.push(self_ident.clone());
            }
            FnArgKind::Typed(pt) => {
                let Pat::Ident(pi) = &*pt.pat else {
                    return Err(verus_syn::Error::new(pt.pat.span(), "expected an argument name"));
                };
                let x = &pi.ident;
                let ty = replace_idents(ty_tokens(&pt.ty), "Self", t);
                binders.push(quote! { #x: #ty });
                args.push(quote! { #x });
            }
        }
    }
    let callee = quote_spanned! { span => #t::#m };
    let tuple = quote! { (#(#args,)*) };
    let fix = |e: &Expr| -> TokenStream { replace_idents(quote! { #e }, "self", &self_ident) };
    let mut out = Vec::new();
    let spec = &sig.spec;
    if let Some(req) = &spec.requires {
        let ps: Vec<TokenStream> = req.exprs.exprs.iter().map(fix).collect();
        let p = conj(&ps);
        out.push(quote_spanned! { span =>
            forall|#(#binders),*| !(#p) || #[trigger] #builtin::call_requires(#callee, #tuple)
        });
    }
    if let Some(ens) = &spec.ensures {
        let (rname, rty) = match &sig.output {
            ReturnType::Type(_, _, Some(p), ty) => {
                let Pat::Ident(pi) = &p.1 else {
                    return Err(verus_syn::Error::new(
                        p.1.span(),
                        "expected a name for the result",
                    ));
                };
                (quote! { #pi }, replace_idents(ty_tokens(ty), "Self", t))
            }
            ReturnType::Type(_, _, None, ty) => {
                (quote! { verus_bound_ret }, replace_idents(ty_tokens(ty), "Self", t))
            }
            ReturnType::Default => (quote! { verus_bound_ret }, quote! { () }),
        };
        let qs: Vec<TokenStream> = ens.exprs.exprs.iter().map(fix).collect();
        let q = conj(&qs);
        out.push(quote_spanned! { span =>
            forall|#(#binders,)* #rname: #rty| !(#[trigger] #builtin::call_ensures(#callee, #tuple, #rname)) || (#q)
        });
    }
    if let Some(alloc) = &spec.allocates {
        let Some(e) = alloc.exprs.exprs.first() else {
            return Err(verus_syn::Error::new(span, "expected an `allocates` bound"));
        };
        let e = fix(e);
        out.push(quote_spanned! { span =>
            forall|#(#binders),*| #[trigger] #builtin::call_allocates(#callee, #tuple) <= #e
        });
    }
    if spec.recommends.is_some()
        || spec.decreases.is_some()
        || spec.invariants.is_some()
        || spec.unwind.is_some()
        || spec.returns.is_some()
    {
        return Err(verus_syn::Error::new(
            span,
            "a bound specification may only have `requires`, `ensures` and `allocates`",
        ));
    }
    Ok(out)
}

fn conj(es: &[TokenStream]) -> TokenStream {
    let mut out = TokenStream::new();
    for (i, e) in es.iter().enumerate() {
        if i > 0 {
            out.extend(quote! { && });
        }
        out.extend(quote! { (#e) });
    }
    out
}

fn ty_tokens(ty: &Type) -> TokenStream {
    quote! { #ty }
}
