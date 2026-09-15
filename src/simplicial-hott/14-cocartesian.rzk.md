# Cocartesian families

These formalizations capture cocartesian families as treated in
[Buchholtz and Weinberger (2023), Higher Structures 7](https://doi.org/10.21136/HS.2023.04).

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Prerequisites

- `hott/*` - We require various prerequisites from homotopy type theory, for
  instance the axiom of function extensionality.
- `02-simplicial-type-theory.rzk.md`
- `03-extension-types.rzk.md`
- `13-inner.rzk.md` - We use (iso)inner families.

## Cocartesian arrows

Here we define the proposition that a dependent arrow in a family is
cocartesian. This is an alternative version using unpacked extension types, as
this is preferred for usage.

```rzk title="BW23, Definition 5.1.1"

#def is-cocartesian-arrow-over
  ( B : U)
  ( b b' b'' : B)
  ( u : hom B b b')
  ( v : hom B b' b'')
  ( w : hom B b b'')
  ( sigma : hom2 B b b' b'' u v w)
  ( P : B → U)
  ( e : P b)
  ( e' : P b')
  ( e'' : P b'')
  ( f : dhom B b b' u P e e')
  : U
  :=
  ( h : dhom B b b'' w P e e'')
  → is-contr
    ( Σ ( g : dhom B b' b'' v P e' e'')
    , ( dhom2 B b b' b'' u v w sigma P e e' e'' f g h))

#def is-cocartesian-arrow
  ( B : U)
  ( b b' : B)
  ( u : hom B b b')
  ( P : B → U)
  ( e : P b)
  ( e' : P b')
  ( f : dhom B b b' u P e e')
  : U
  :=
    ( b'' : B) → (v : hom B b' b'') → (w : hom B b b'')
    → ( sigma : hom2 B b b' b'' u v w) → (e'' : P b'')
    → is-cocartesian-arrow-over B b b' b'' u v w sigma P e e' e'' f
```

### An arrow is cocartesian if and only if post-composition is an equivalence

```rzk

#def is-cocartesian-arrow-over-is-equiv-comp-over-is-inner
  ( B : U)
  ( P : B → U)
  ( is-inner-P : is-inner-family B P)
  ( b b' b'' : B)
  ( u : hom B b b')
  ( v : hom B b' b'')
  ( w : hom B b b'')
  ( sigma : hom2 B b b' b'' u v w)
  ( e : P b)
  ( e' : P b')
  ( e'' : P b'')
  ( f : dhom B b b' u P e e')
  : is-equiv
      ( dhom B b' b'' v P e' e'')
      ( dhom B b b'' w P e e'')
      ( comp-over-is-inner-family B P is-inner-P b b' b'' u v w sigma e e' e'' f)
  → is-cocartesian-arrow-over B b b' b'' u v w sigma P e e' e'' f
  :=
  \ is-equiv-comp h →
    is-contr-equiv-is-contr
      ( fib
        ( dhom B b' b'' v P e' e'')
        ( dhom B b b'' w P e e'')
        ( comp-over-is-inner-family B P is-inner-P b b' b'' u v w sigma e e' e'' f)
        h)
      ( Σ ( g : dhom B b' b'' v P e' e'')
        , ( dhom2 B b b' b'' u v w sigma P e e' e'' f g h))
      ( equiv-fib-comp-tot-dhom2 B P is-inner-P b b' b'' u v w sigma e e' e'' f h)
      ( is-contr-map-is-equiv
        ( dhom B b' b'' v P e' e'')
        ( dhom B b b'' w P e e'')
        ( comp-over-is-inner-family B P is-inner-P b b' b'' u v w sigma e e' e'' f)
        ( is-equiv-comp)
        ( h))


#def is-cocartesian-arrow-is-equiv-comp-over-is-inner
  ( B : U)
  ( P : B → U)
  ( is-inner-P : is-inner-family B P)
  ( b b' : B)
  ( u : hom B b b')
  ( e : P b)
  ( e' : P b')
  ( f : dhom B b b' u P e e')
  : ( ( b'' : B) → (v : hom B b' b'') → (w : hom B b b'')
    → ( sigma : hom2 B b b' b'' u v w) → (e'' : P b'')
    → is-equiv
      ( dhom B b' b'' v P e' e'')
      ( dhom B b b'' w P e e'')
      ( comp-over-is-inner-family B P is-inner-P b b' b'' u v w sigma e e' e'' f))
  → is-cocartesian-arrow  B b b' u P e e' f
  :=
  \ is-equiv-comp b'' v w sigma e'' →
    is-cocartesian-arrow-over-is-equiv-comp-over-is-inner
      B P is-inner-P b b' b'' u v w sigma e e' e'' f
      ( is-equiv-comp b'' v w sigma e'')

#def is-equiv-comp-over-is-inner-is-cocartesian-arrow-over
  ( B : U)
  ( P : B → U)
  ( is-inner-P : is-inner-family B P)
  ( b b' b'' : B)
  ( u : hom B b b')
  ( v : hom B b' b'')
  ( w : hom B b b'')
  ( sigma : hom2 B b b' b'' u v w)
  ( e : P b)
  ( e' : P b')
  ( e'' : P b'')
  ( f : dhom B b b' u P e e')
  ( is-cocart-f : is-cocartesian-arrow-over B b b' b'' u v w sigma P e e' e'' f)
  : is-equiv
    ( dhom B b' b'' v P e' e'')
    ( dhom B b b'' w P e e'')
    ( comp-over-is-inner-family B P is-inner-P b b' b'' u v w sigma e e' e'' f)
  :=
  is-equiv-is-contr-map
    ( dhom B b' b'' v P e' e'')
    ( dhom B b b'' w P e e'')
    ( comp-over-is-inner-family B P is-inner-P b b' b'' u v w sigma e e' e'' f)
    ( \ h →
      is-contr-equiv-is-contr'
        ( fib
          ( dhom B b' b'' v P e' e'')
          ( dhom B b b'' w P e e'')
          ( comp-over-is-inner-family B P is-inner-P b b' b'' u v w
            sigma e e' e'' f)
          ( h))
        ( Σ ( g : dhom B b' b'' v P e' e'')
        , ( dhom2 B b b' b'' u v w sigma P e e' e'' f g h))
        ( equiv-fib-comp-tot-dhom2 B P is-inner-P b b' b'' u v w
          sigma e e' e'' f h)
        ( is-cocart-f h))

#def is-equiv-comp-over-is-inner-is-cocartesian-arrow
  ( B : U)
  ( P : B → U)
  ( is-inner-P : is-inner-family B P)
  ( b b' : B)
  ( u : hom B b b')
  ( e : P b)
  ( e' : P b')
  ( f : dhom B b b' u P e e')
  ( is-cocart-f : is-cocartesian-arrow  B b b' u P e e' f)
  ( b'' : B)
  ( v : hom B b' b'')
  ( w : hom B b b'')
  ( sigma : hom2 B b b' b'' u v w)
  ( e'' : P b'')
  : is-equiv
    ( dhom B b' b'' v P e' e'')
    ( dhom B b b'' w P e e'')
    ( comp-over-is-inner-family B P is-inner-P b b' b'' u v w sigma e e' e'' f)
  :=
  is-equiv-comp-over-is-inner-is-cocartesian-arrow-over
    B P is-inner-P b b' b'' u v w sigma e e' e'' f
    ( is-cocart-f b'' v w sigma e'')

```


## Cocartesian lifts

The following is the type of cocartesian lifts of a fixed arrow in the base with
a given starting point in the fiber.

```rzk title="BW23, Definition 5.1.2"
#def cocartesian-lift
  ( B : U)
  ( b b' : B)
  ( u : hom B b b')
  ( P : B → U)
  ( e : P b)
  : U
  :=
    Σ ( e' : P b')
    , Σ ( f : dhom B b b' u P e e') , is-cocartesian-arrow B b b' u P e e' f
```

## Cocartesian family

A family is cocartesian if it is isoinner and any arrow in the has a cocartesian
lift, given a point in the fiber over the domain.

```rzk title="BW23, Definition 5.2.1"
#def has-cocartesian-lifts
  ( B : U)
  ( P : B → U)
  : U
  :=
    ( b : B) → (b' : B) → (u : hom B b b')
    → ( e : P b) → (Σ (e' : P b')
      , ( Σ ( f : dhom B b b' u P e e') , is-cocartesian-arrow B b b' u
          P e e' f))
```

```rzk title="BW23, Definition 5.2.2"
#def is-cocartesian-family
  ( B : U)
  ( P : B → U)
  : U
  := product (is-isoinner-family B P) (has-cocartesian-lifts B P)
```
