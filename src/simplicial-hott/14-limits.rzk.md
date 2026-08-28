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
  := Σ (b : B) , (x : B) → Equiv (hom B x b) (family-cone A B f x)

#def colimit3
  ( A B : U)
  ( f : A → B)
  : U
  := Σ (b : B) , (x : B) → Equiv (hom B b x) (family-cocone A B f x)
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

Co-/limits are unique up to isomorphism.

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

The universal property of limits and colimits.

```rzk title="Bar22, Proposition 3.7"
#def colimit3-colimit uses (funext)
  ( J B : U)
  ( is-segal-B : is-segal B)
  ( g : J → B)
  ( colim-g : colimit J B g)
  : colimit3 J B g
  :=
    is-representable-family-has-initial-tot
      B
      is-segal-B
      ( family-cocone J B g)
      ( is-covariant-family-cone-is-segal J B is-segal-B g)
      colim-g

#def colimit-colimit3 uses (extext)
  ( J B : U)
  ( is-segal-B : is-segal B)
  ( g : J → B)
  ( colim3-g : colimit3 J B g)
  : colimit J B g
  :=
    has-initial-tot-is-representable-family
      extext
      B
      is-segal-B
      ( family-cocone J B g)
      colim3-g

#def limit3-limit uses (funext)
  ( J B : U)
  ( is-segal-B : is-segal B)
  ( g : J → B)
  ( lim-g : limit J B g)
  : limit3 J B g
  :=
    is-contravariant-representable-family-has-final-tot
      B
      is-segal-B
      ( family-cone J B g)
      ( is-contravariant-family-cone-is-segal J B is-segal-B g)
      lim-g

#def limit-limit3 uses (extext)
  ( J B : U)
  ( is-segal-B : is-segal B)
  ( g : J → B)
  ( lim3-g : limit3 J B g)
  : limit J B g
  :=
    has-final-tot-is-contravariant-representable-family
      extext
      B
      is-segal-B
      ( family-cone J B g)
      lim3-g
```

```rzk
#def equiv-transpose-cocone uses (funext)
  ( A B J : U)
  ( g : J → A)
  ( f : A → B)
  ( u : B → A)
  ( adj : is-transposing-adj A B f u)
  ( z : B)
  : Equiv
      ( family-cocone J B (comp J A B f g) z)
      ( family-cocone J A g (u z))
  :=
    equiv-triple-comp
      ( family-cocone J B (comp J A B f g) z)
      ( ( j : J) → hom B (f (g j)) z)
      ( ( j : J) → hom A (g j) (u z))
      ( family-cocone J A g (u z))
      ( equiv-components-nat-trans
        J
        ( \ _ → B)
        ( comp J A B f g)
        ( constant J B z))
      ( equiv-function-equiv-family
        funext
        J
        ( \ j → hom B (f (g j)) z)
        ( \ j → hom A (g j) (u z))
        ( \ j → adj (g j) z))
      ( inv-equiv
        ( family-cocone J A g (u z))
        ( ( j : J) → hom A (g j) (u z))
        ( equiv-components-nat-trans
          J
          ( \ _ → A)
          g
          ( constant J A (u z))))

#def equiv-transpose-cone uses (funext)
  ( A B J : U)
  ( g : J → B)
  ( f : A → B)
  ( u : B → A)
  ( adj : is-transposing-adj A B f u)
  ( y : A)
  : Equiv
      ( family-cone J B g (f y))
      ( family-cone J A (comp J B A u g) y)
  :=
    equiv-triple-comp
      ( family-cone J B g (f y))
      ( ( j : J) → hom B (f y) (g j))
      ( ( j : J) → hom A y (u (g j)))
      ( family-cone J A (comp J B A u g) y)
      ( equiv-components-nat-trans
        J
        ( \ _ → B)
        ( constant J B (f y))
        g)
      ( equiv-function-equiv-family
        funext
        J
        ( \ j → hom B (f y) (g j))
        ( \ j → hom A y (u (g j)))
        ( \ j → adj y (g j)))
      ( inv-equiv
        ( family-cone J A (comp J B A u g) y)
        ( ( j : J) → hom A y (u (g j)))
        ( equiv-components-nat-trans
          J
          ( \ _ → A)
          ( constant J A y)
          ( comp J B A u g)))

#def left-adjoint-preserves-colimit3 uses (funext)
  ( A B J : U)
  ( g : J → A)
  ( f : A → B)
  ( u : B → A)
  ( adj : is-transposing-adj A B f u)
  ( ( a , is-represented-cocone-g) : colimit3 J A g)
  : colimit3 J B (comp J A B f g)
  :=
    ( f a
    , \ z →
      equiv-triple-comp
        ( hom B (f a) z)
        ( hom A a (u z))
        ( family-cocone J A g (u z))
        ( family-cocone J B (comp J A B f g) z)
        ( adj a z)
        ( is-represented-cocone-g (u z))
        ( inv-equiv
          ( family-cocone J B (comp J A B f g) z)
          ( family-cocone J A g (u z))
          ( equiv-transpose-cocone A B J g f u adj z)))

#def right-adjoint-preserves-limit3 uses (funext)
  ( A B J : U)
  ( g : J → B)
  ( f : A → B)
  ( u : B → A)
  ( adj : is-transposing-adj A B f u)
  ( ( b , is-represented-cone-g) : limit3 J B g)
  : limit3 J A (comp J B A u g)
  :=
    ( u b
    , \ y →
      equiv-triple-comp
        ( hom A y (u b))
        ( hom B (f y) b)
        ( family-cone J B g (f y))
        ( family-cone J A (comp J B A u g) y)
        ( inv-equiv
          ( hom B (f y) b)
          ( hom A y (u b))
          ( adj y b))
        ( is-represented-cone-g (f y))
        ( equiv-transpose-cone A B J g f u adj y))
```

Left/right adjoints preserve co/limits.

```rzk title="BM22, Theorem 3.8, 3.9"
#def left-adjoint-preserves-colimit uses (funext extext)
  ( A B J : U)
  ( is-segal-A : is-segal A)
  ( is-segal-B : is-segal B)
  ( g : J → A)
  ( f : A → B)
  ( u : B → A)
  ( colim-g : colimit J A g)
  ( adj : is-transposing-adj A B f u)
  : colimit J B (comp J A B f g)
  :=
    colimit-is-colimit3 J B is-segal-B (comp J A B f g)
      ( left-adjoint-preserves-colimit3 A B J g f u adj
        ( colimit3-is-colimit J A is-segal-A g colim-g))

#def right-adjoint-preserves-limit uses (funext extext)
  ( A B J : U)
  ( is-segal-A : is-segal A)
  ( is-segal-B : is-segal B)
  ( g : J → B)
  ( f : A → B)
  ( u : B → A)
  ( lim-g : limit J B g)
  ( adj : is-transposing-adj A B f u)
  : limit J A (comp J B A u g)
  :=
    limit-is-limit3 J A is-segal-A (comp J B A u g)
      ( right-adjoint-preserves-limit3 A B J g f u adj
        ( limit3-is-limit J B is-segal-B g lim-g))
```
