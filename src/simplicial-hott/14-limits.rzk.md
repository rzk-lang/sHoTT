# Limits and colimits

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

## Prerequisites

- `hott/*` - We require various prerequisites from homotopy type theory, for
  instance the notion of equivalence (`#!rzk is-equiv`).
- `02-simplicial-type-theory.rzk.md` — We rely on definitions of simplices and
  their subshapes.
- `03-extension-types.rzk.md` — We use extension extensionality.
- `05-segal-types.rzk.md` - We use Segal types (`#!rzk hom`, `#!rzk is-segal`,
  `#!rzk constant`).
- `06-2cat-of-segal-types.rzk.md` - We use natural transformations
  (`#!rzk vertical-comp-nat-trans`).
- `09-yoneda.rzk.md` - We use initial and final objects (`#!rzk is-initial`,
  `#!rzk is-final`).

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

In a Segal type, an object isomorphic to an initial object is also initial.

```rzk
#def is-initial-iso-is-initial uses (extext)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( a b : A)
  ( is-initial-a : is-initial A a)
  ( is-iso-a-b : Iso A is-segal-A a b)
  : is-initial A b
  :=
  \ x →
    is-contr-equiv-is-contr'
    ( hom A b x)
    ( hom A a x)
    ( precomp-is-segal A is-segal-A a b
      ( first is-iso-a-b)
      ( x)
    , is-equiv-precomp-is-iso extext A is-segal-A a b
      ( first is-iso-a-b)
      ( first (first (second is-iso-a-b)))
      ( second (first (second is-iso-a-b)))
      ( first (second (second is-iso-a-b)))
      ( second (second (second is-iso-a-b)))
      ( x))
    ( is-initial-a x)

#def is-final-iso-is-final uses (extext)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( a b : A)
  ( is-final-a : is-final A a)
  ( is-iso-a-b : Iso A is-segal-A a b)
  : is-final A b
  :=
  \ x →
    is-contr-equiv-is-contr
    ( hom A x a)
    ( hom A x b)
    ( postcomp-is-segal A is-segal-A a b
      ( first is-iso-a-b)
      ( x)
    , is-equiv-postcomp-is-iso extext A is-segal-A a b
      ( first is-iso-a-b)
      ( first (first (second is-iso-a-b)))
      ( second (first (second is-iso-a-b)))
      ( first (second (second is-iso-a-b)))
      ( second (second (second is-iso-a-b)))
      ( x))
    ( is-final-a x)
```

## Uniqueness up to isomophism of (co)limits.

The type of (co)cones of a function with codomain a Segal type is a Segal type.

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

#def is-contravariant-family-cone-is-segal
  ( A B : U)
  ( is-segal-B : is-segal B)
  ( f : A → B)
  : is-contravariant B (\ b → family-cone A B f b)
  :=
    is-contravariant-substitution-is-contravariant
    ( A → B)
    ( B)
    ( \ g → hom (A → B) g f)
    ( is-contravariant-representable-is-segal
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

#def is-segal-cone-is-segal uses (funext extext)
  ( A B : U)
  ( is-segal-B : is-segal B)
  ( f : A → B)
  : is-segal (cone A B f)
  :=
    is-segal-total-type-contravariant-family-is-segal-base
    ( extext)
    ( B)
    ( family-cone A B f)
    ( is-contravariant-family-cone-is-segal
      ( A)
      ( B)
      ( is-segal-B)
      ( f))
    ( is-segal-B)
```

The same also holds for Rezk-ness, (co)cones over(/under) a Rezk type also form
a Rezk type.

```rzk
#def concat3
  ( A : U)
  ( x y z w : A)
  ( p : x = y)
  ( q : y = z)
  ( r : z = w)
  : x = w
  :=
  concat A x z w
    ( concat A x y z p q)
    r
#def ap-iso uses (extext)
  ( A B : U)
  ( is-segal-A : is-segal A)
  ( is-segal-B : is-segal B)
  ( F : A → B)
  ( x y : A)
  : ( Iso A is-segal-A x y) → (Iso B is-segal-B (F x) (F y))
  := \ φ →
      let f : hom A x y :=
        first φ in
      let F∘f : hom B (F x) (F y) :=
        ap-hom A B F x y f in
    ( F∘f
    , (
        let g : hom A y x :=
          first (first (second φ)) in
        let F∘g : hom B (F y) (F x) :=
          ap-hom A B F y x g in
        ( F∘g
      , let base-eq :=
        ap
          ( hom A x x)
          ( hom B (F x) (F x))
          ( comp-is-segal A is-segal-A x y x f g)
          ( id-hom A x)
          ( ap-hom A B F x x)
          ( second (first (second φ))) in
        concat3
          ( hom B (F x) (F x))
          ( comp-is-segal
            B
            is-segal-B
            ( F x)
            ( F y)
            ( F x)
            F∘f
            F∘g)
          ( ap-hom A B F x x
            ( comp-is-segal
              A
              is-segal-A
              x
              y
              x
              f
              g))
          ( ap-hom A B F x x
            ( id-hom A x))
          ( id-hom B (F x))
          ( functors-pres-comp A B
            is-segal-A
            is-segal-B
            F
            x
            y
            x
            f
            g)
          base-eq
          ( functors-pres-id
            extext
            A
            B
            F
            x))
      , let h : hom A y x :=
          first (second (second φ)) in
        let F∘h : hom B (F y) (F x) :=
          ap-hom A B F y x h in
        ( F∘h
      , let base-eq :=
        ap
          ( hom A y y)
          ( hom B (F y) (F y))
          ( comp-is-segal A is-segal-A y x y h f)
          ( id-hom A y)
          ( ap-hom A B F y y)
          ( second (second (second φ))) in
        concat3
          ( hom B (F y) (F y))
          ( comp-is-segal
            B
            is-segal-B
            ( F y)
            ( F x)
            ( F y)
            F∘h
            F∘f)
          ( ap-hom A B F y y
            ( comp-is-segal
              A
              is-segal-A
              y
              x
              y
              h
              f))
          ( ap-hom A B F y y
            ( id-hom A y))
          ( id-hom B (F y))
          ( functors-pres-comp A B
            is-segal-A
            is-segal-B
            F
            y
            x
            y
            h
            f)
          base-eq
          ( functors-pres-id
            extext
            A
            B
            F
            y))))
#def is-rezk-total-type-covariant-family-is-rezk-base uses (funext extext)
  ( A : U)
  ( C : A → U)
  ( is-covariant-C : is-covariant A C)
  : is-rezk A → is-rezk (total-type A C)
  := \ is-rezk-A →
    let is-segal-A : is-segal A := (
      is-segal-is-rezk A is-rezk-A
    ) in
    let is-segal-total-type : is-segal (Σ (a : A) , C a) :=
      ( is-segal-total-type-covariant-family-is-segal-base
        ( extext)
        A
        C
        is-covariant-C
        is-segal-A) in
    ( is-segal-total-type
      , \ x → \ y →
        let eq-iso : (Iso (total-type A C) is-segal-total-type x y) → (x = y) :=
          \ f →
          eq-pair A C x y
            ( eq-iso-is-rezk
                A
                is-rezk-A
                ( first x)
                ( first y)
                ( ap-iso
                  ( total-type A C)
                  A
                  is-segal-total-type
                  is-segal-A
                  ( \ p → first p)
                  x
                  y
                  f)
            , ?) in
        is-equiv-has-inverse
          ( x = y)
          ( Iso (total-type A C) is-segal-total-type x y)
          ( iso-eq (total-type A C) is-segal-total-type x y)
          ( eq-iso
          , ( ?
            , ?)))

#def is-rezk-cocone-is-rezk uses (funext extext)
  ( A B : U)
  ( is-rezk-B : is-rezk B)
  ( f : A → B)
  : is-rezk (cocone A B f)
  :=
  is-rezk-total-type-covariant-family-is-rezk-base
    B
    ( family-cocone A B f)
    ( is-covariant-family-cone-is-segal
      ( A)
      ( B)
      ( is-segal-is-rezk B is-rezk-B)
      ( f))
    ( is-rezk-B)
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

```rzk
#def iso-limit-is-segal uses (extext funext)
  ( A B : U)
  ( is-segal-B : is-segal B)
  ( f : A → B)
  ( x y : limit A B f)
  : Iso
    ( cone A B f)
    ( is-segal-cone-is-segal A B is-segal-B f)
    ( first x)
    ( first y)
  :=
    iso-final
    ( cone A B f)
    ( is-segal-cone-is-segal A B is-segal-B f)
    ( first x)
    ( first y)
    ( second x)
    ( second y)
```

(Co)limits in Rezk types are unique up to equality.
