# 12. Sets

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Sets

A type is a set when its identity types are propositions.

```rzk
#def is-set
  ( A : U)
  : U
  := (x : A) → (y : A) → (p : x = y) → (q : x = y) → p = q
```

## Hedberg's theorem

```rzk
#def path-to-relation
  ( A : U)
  ( R : A → A → U)
  ( rho : (z : A) → R z z)
  ( x y : A)
  ( p : x = y)
  : R x y
  := transport
    A
    ( \ z → R x z)
    x
    y
    p
    ( rho x)

#def transport-eq-in-prop
  ( A : U)
  ( B : A → U)
  ( x y : A)
  ( p : x = y)
  ( u : B x)
  ( v : B y)
  ( is-prop-By : is-prop (B y))
  : ( transport A B x y p u) = v
  :=
    let t : B y := transport A B x y p u in
    let h := is-prop-By t v in
      first h

#def is-contr-total-prop-in-id
  ( A : U)
  ( R : A → A → U)
  ( is-prop-R : (x : A) → (y : A) → is-prop (R x y))
  ( rho : (x : A) → R x x)
  ( d : (x : A) → (y : A) → R x y → (x = y))
  ( x : A)
  : is-contr (total-type A (R x))
  :=
    ( ( x , rho x)
    , \ (a , b) →
      let p : x = a := d x a b in
      let q : transport A (R x) x a p (rho x) = b :=
        transport-eq-in-prop
          A (R x)
          x a p
          ( rho x) b
          ( is-prop-R x a)
      in
        path-of-pairs-pair-of-paths
          A (R x)
          x a p
          ( rho x) b q
    )
```

A reflexive, prop-valued relation
that implies equality
is equivalent to identity type.

```rzk
#def equiv-paths-prop-in-id
  ( A : U)
  ( R : A → A → U)
  ( is-prop-R : (x : A) → (y : A) → is-prop (R x y))
  ( rho : (x : A) → R x x)
  ( d : (x : A) → (y : A) → R x y → (x = y))
  ( x y : A)
  : Equiv (x = y) (R x y)
  :=
    let H :=
      is-contr-total-prop-in-id A R
        is-prop-R
        rho d x in
    ( path-to-relation A R
        rho x y
    , are-equiv-from-paths-is-contr-total A x
        ( R x)
        ( path-to-relation A R rho x)
        H
        y
    )
```

A type is a set if it admits a reflexive
prop-valued relation that implies equality.

```rzk
#def is-set-prop-in-id
  ( A : U)
  ( R : A → A → U)
  ( is-prop-R : (x : A) → (y : A) → is-prop (R x y))
  ( rho : (x : A) → R x x)
  ( d : (x : A) → (y : A) → R x y → (x = y))
  : is-set A
  :=
    \ x y p q →
      let equiv := equiv-paths-prop-in-id A R
        is-prop-R
        rho d x y in
      let eq-is-prop : is-prop (x = y) :=
        is-prop-Equiv-is-prop
          ( x = y)
          ( R x y)
          equiv
          ( is-prop-R x y) in
        first (eq-is-prop p q)
```

TODO:
Corollary. If equality in `A` is double negation stable,
then `A` is a set

TODO:
Corollary. If equality in `A` is decidable,
then `A` is a set.
