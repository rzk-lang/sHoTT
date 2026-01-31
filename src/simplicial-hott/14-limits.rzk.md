# 13. Limits and colimits

These formalisations correspond in part to Section 3 of the BM22 paper.

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

Some definitions make use of function extentionality and extension
extensionality.

```rzk
#assume funext : FunExt
#assume extext : ExtExt
```

## Definition limits and colimits

Given a function `#!rzk f : A → B` and `#!rzk b:B` we define the type of cones
over `#!rzk f`.

```rzk
#def cone
  ( A B : U)
  ( f : A → B)
  : U
  := Σ (b : B) , hom (A → B) (constant A B b) f
```

Given a function `#!rzk f : A → B` and `#!rzk b:B` we define the type of cocones
under `#!rzk f`.

```rzk
#def cocone
  ( A B : U)
  ( f : A → B)
  : U
  := Σ (b : B) , hom (A → B) f (constant A B b)
```

We define a colimit for `#!rzk f : A → B` as an initial cocone under `#!rzk f`.

```rzk
#def colimit
  ( A B : U)
  ( f : A → B)
  : U
  := Σ (x : cocone A B f) , is-initial (cocone A B f) x
```

We define a limit of `#!rzk f : A → B` as a final cone over `#!rzk f`.

```rzk
#def limit
  ( A B : U)
  ( f : A → B)
  : U
  := Σ (x : cone A B f) , is-final (cone A B f) x
```

We give a second definition of limits, we eventually want to prove both
definitions coincide. Define cone as a family.

```rzk
#def family-cone
  ( A B : U)
  : ( A → B) → (B) → U
  := \ f → \ b → (hom (A → B) (constant A B b) f)

#def constant-nat-trans
  ( A B : U)
  ( x y : B)
  ( k : hom B x y)
  : hom (A → B) (constant A B x) (constant A B y)
  := \ t a → (constant A (hom B x y) k) a t

#def cone-precomposition
  ( A B : U)
  ( is-segal-B : is-segal B)
  ( f : A → B)
  ( b x : B)
  ( k : hom B b x)
  : ( family-cone A B f x) → (family-cone A B f b)
  :=
  \ α →
  vertical-comp-nat-trans
    ( A)
    ( \ _ → B)
    ( \ _ → is-segal-B)
    ( constant A B b)
    ( constant A B x)
    ( f)
    ( constant-nat-trans A B b x k)
    ( α)
```

Another definition of limit.

```rzk
#def limit2
  ( A B : U)
  ( is-segal-B : is-segal B)
  ( f : A → B)
  : U
  := Σ (b : B)
  , Σ ( c : family-cone A B f b)
    , ( x : B) → (k : hom B b x)
      → is-equiv
        ( family-cone A B f x)
        ( family-cone A B f b)
        ( cone-precomposition A B is-segal-B f b x k)
```

We give a second definition of colimits, we eventually want to prove both
definitions coincide. Define cocone as a family.

```rzk
#def family-cocone
  ( A B : U)
  : ( A → B) → (B) → U
  := \ f → \ b → (hom (A → B) f (constant A B b))

#def cocone-postcomposition
  ( A B : U)
  ( is-segal-B : is-segal B)
  ( f : A → B)
  ( x b : B)
  ( k : hom B x b)
  : ( family-cocone A B f x) → (family-cocone A B f b)
  :=
  \ α →
  vertical-comp-nat-trans
    ( A)
    ( \ _ → B)
    ( \ _ → is-segal-B)
    ( f)
    ( constant A B x)
    ( constant A B b)
    ( α)
    ( constant-nat-trans A B x b k)
```

Another definition of colimit.

```rzk
#def colimit2
  ( A B : U)
  ( is-segal-B : is-segal B)
  ( f : A → B)
  : U
  := Σ (b : B)
  , Σ ( c : family-cocone A B f b)
    , ( x : B) → (k : hom B x b)
    → is-equiv
      ( family-cocone A B f x)
      ( family-cocone A B f b)
      ( cocone-postcomposition A B is-segal-B f x b k)
```

The following alternative definition does not require a Segalness condition.
When `#!rzk is-segal B` then definitions 1 and 3 coincide.

```rzk
#def limit3
  ( A B : U)
  ( f : A → B)
  : U
  := Σ (b : B) , (x : B) → Equiv (hom B b x) (family-cone A B f x)

#def colimit3
  ( A B : U)
  ( f : A → B)
  : U
  := Σ (b : B) , (x : B) → Equiv (hom B x b) (family-cocone A B f x)
```

## Uniqueness of initial and final objects.

In a Segal type, initial objects are isomorphic.

```rzk
#def iso-initial
  ( A : U)
  ( is-segal-A : is-segal A)
  ( a b : A)
  ( is-initial-a : is-initial A a)
  ( is-initial-b : is-initial A b)
  : Iso A is-segal-A a b
  :=
    ( first (is-initial-a b)
    , ( ( first (is-initial-b a)
        , all-elements-equal-is-contr
            ( hom A a a)
            ( is-initial-a a)
            ( comp-is-segal A is-segal-A a b a
              ( first (is-initial-a b))
              ( first (is-initial-b a)))
            ( id-hom A a))
      , ( first (is-initial-b a)
        , all-elements-equal-is-contr
            ( hom A b b)
            ( is-initial-b b)
            ( comp-is-segal A is-segal-A b a b
              ( first (is-initial-b a))
              ( first (is-initial-a b)))
            ( id-hom A b))))
```

In a Segal type, final objects are isomorphic.

```rzk
#def iso-final
  ( A : U)
  ( is-segal-A : is-segal A)
  ( a b : A)
  ( is-final-a : is-final A a)
  ( is-final-b : is-final A b)
  : Iso A is-segal-A a b
  :=
    ( first (is-final-b a)
    , ( ( first (is-final-a b)
        , all-elements-equal-is-contr
            ( hom A a a)
            ( is-final-a a)
            ( comp-is-segal A is-segal-A a b a
              ( first (is-final-b a))
              ( first (is-final-a b)))
            ( id-hom A a))
      , ( first (is-final-a b)
        , all-elements-equal-is-contr
            ( hom A b b)
            ( is-final-b b)
            ( comp-is-segal A is-segal-A b a b
              ( first (is-final-a b))
              ( first (is-final-b a)))
            ( id-hom A b))))
```

## Uniqueness up to isomophism of (co)limits.

The type of cocones of a function with codomain a Segal type is a Segal type.

```rzk title="BM22, Remark 4 (i)"
#def is-covariant-family-cone-is-segal
  ( A B : U)
  ( is-segal-B : is-segal B)
  ( f : A → B)
  : is-covariant B (\ b → family-cocone A B f b)
  :=
    is-covariant-substitution-is-covariant
    ( A → B)
    ( B)
    ( hom (A → B) f)
    ( is-covariant-representable-is-segal
        ( A → B)
        ( is-segal-function-type
          ( funext)
          ( A)
          ( \ _ → B)
          ( \ _ → is-segal-B))
        ( f))
    ( \ b → constant A B b)

#def is-segal-cocone-is-segal uses (funext extext)
  ( A B : U)
  ( is-segal-B : is-segal B)
  ( f : A → B)
  : is-segal (cocone A B f)
  :=
    is-segal-total-type-covariant-family-is-segal-base
    ( extext)
    ( B)
    ( family-cocone A B f)
    ( is-covariant-family-cone-is-segal
      ( A)
      ( B)
      ( is-segal-B)
      ( f))
    ( is-segal-B)
```

Colimits are unique up to isomorphism.

```rzk title="BM, Corollary 1 (i)"
#def iso-colimit-is-segal uses (extext funext)
  ( A B : U)
  ( is-segal-B : is-segal B)
  ( f : A → B)
  ( x y : colimit A B f)
  : Iso
    ( cocone A B f)
    ( is-segal-cocone-is-segal A B is-segal-B f)
    ( first x)
    ( first y)
  :=
    iso-initial
    ( cocone A B f)
    ( is-segal-cocone-is-segal A B is-segal-B f)
    ( first x)
    ( first y)
    ( second x)
    ( second y)
```
