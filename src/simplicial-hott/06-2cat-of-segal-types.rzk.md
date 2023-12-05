# The 2-category of Segal types

These formalisations correspond to Section 6 of the RS17 paper.

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Prerequisites

- `02-simplicial-type-theory.rzk.md` — We rely on definitions of simplicies and
  their subshapes.
- `03-extension-types.rzk.md` — We use extension extensionality.
- `05-segal-types.rzk.md` - We use the notion of hom types.

Some of the definitions in this file rely on function extensionality and
extension extensionality:

```rzk
#assume funext : FunExt
#assume extext : ExtExt
```

## Functors

Functions between types induce an action on hom types, preserving sources and
targets. The action is called `#!rzk ap-hom` to avoid conflicting with
`#!rzk ap`.

```rzk title="RS17, Section 6.1"
#def ap-hom
  ( A B : U)
  ( F : A → B)
  ( x y : A)
  ( f : hom A x y)
  : hom B (F x) (F y)
  := \ t → F (f t)

#def ap-hom2
  ( A B : U)
  ( F : A → B)
  ( x y z : A)
  ( f : hom A x y)
  ( g : hom A y z)
  ( h : hom A x z)
  ( α : hom2 A x y z f g h)
  : hom2 B (F x) (F y) (F z)
    ( ap-hom A B F x y f) (ap-hom A B F y z g) (ap-hom A B F x z h)
  := \ t → F (α t)
```

Functions between types automatically preserve identity arrows. Preservation of
identities follows from extension extensionality because these arrows are
pointwise equal.

```rzk title="RS17, Proposition 6.1.a"
#def functors-pres-id uses (extext)
  ( A B : U)
  ( F : A → B)
  ( x : A)
  : ( ap-hom A B F x x (id-hom A x)) = (id-hom B (F x))
  :=
    naiveextext-extext
      ( extext)
      ( 2)
      ( Δ¹)
      ( ∂Δ¹)
      ( \ t → B)
      ( \ t → recOR (t ≡ 0₂ ↦ F x , t ≡ 1₂ ↦ F x))
      ( ap-hom A B F x x (id-hom A x))
      ( id-hom B (F x))
      ( \ t → refl)
```

Preservation of composition requires the Segal hypothesis.

```rzk title="RS17, Proposition 6.1.b"
#def functors-pres-comp
  ( A B : U)
  ( is-segal-A : is-segal A)
  ( is-segal-B : is-segal B)
  ( F : A → B)
  ( x y z : A)
  ( f : hom A x y)
  ( g : hom A y z)
  :
    ( comp-is-segal B is-segal-B
      ( F x) (F y) (F z)
      ( ap-hom A B F x y f)
      ( ap-hom A B F y z g))

  = ( ap-hom A B F x z (comp-is-segal A is-segal-A x y z f g))
  :=
    uniqueness-comp-is-segal B is-segal-B
      ( F x) (F y) (F z)
      ( ap-hom A B F x y f)
      ( ap-hom A B F y z g)
      ( ap-hom A B F x z (comp-is-segal A is-segal-A x y z f g))
      ( ap-hom2 A B F x y z f g
        ( comp-is-segal A is-segal-A x y z f g)
        ( witness-comp-is-segal A is-segal-A x y z f g))

#def rev-functors-pres-comp
  ( A B : U)
  ( is-segal-A : is-segal A)
  ( is-segal-B : is-segal B)
  ( F : A → B)
  ( x y z : A)
  ( f : hom A x y)
  ( g : hom A y z)
  :
    ( ap-hom A B F x z (comp-is-segal A is-segal-A x y z f g))

  = ( comp-is-segal B is-segal-B
      ( F x) (F y) (F z)
      ( ap-hom A B F x y f)
      ( ap-hom A B F y z g))
  :=
    rev (hom B (F x) (F z))
    ( comp-is-segal B is-segal-B
      ( F x) (F y) (F z)
      ( ap-hom A B F x y f)
      ( ap-hom A B F y z g))
    ( ap-hom A B F x z (comp-is-segal A is-segal-A x y z f g))
    ( functors-pres-comp A B is-segal-A is-segal-B F x y z f g)
```

The action on morphisms commutes with transport.

```rzk
#def ap-hom-naturality
  ( A B C : U)
  ( f g : A → B)
  ( h k : B → C)
  ( p : f = g)
  ( q : h = k)
  ( x y : A)
  : comp
    ( hom B (f x) (f y))
    ( hom B (g x) (g y))
    ( hom C (k (g x)) (k (g y)))
    ( ap-hom B C k (g x) (g y))
    ( transport (A → B) (\ f' → hom B (f' x) (f' y)) f g p)

  = comp
    ( hom B (f x) (f y)) (hom C (h (f x)) (h (f y))) (hom C (k (g x)) (k (g y)))
    ( transport (A → C) (\ f' → hom C (f' x) (f' y))
      ( comp A B C h f)
      ( comp A B C k g)
      ( comp-homotopic-maps A B C f g h k p q))
    ( ap-hom B C h (f x) (f y))
  :=
  ind-path (A → B) f
  ( \ g' p' →
    comp (hom B (f x) (f y)) (hom B (g' x) (g' y)) (hom C (k (g' x)) (k (g' y)))
    ( ap-hom B C k (g' x) (g' y))
    ( transport (A → B) (\ f' → hom B (f' x) (f' y)) f g' p')

  = comp
    ( hom B (f x) (f y))(hom C (h (f x)) (h (f y)))(hom C (k (g' x)) (k (g' y)))
    ( transport (A → C) (\ f' → hom C (f' x) (f' y))
      ( comp A B C h f)
      ( comp A B C k g')
      ( comp-homotopic-maps A B C f g' h k p' q))
    ( ap-hom B C h (f x) (f y)))
  ( ind-path (B → C) h
    ( \ k' q' →
      comp (hom B (f x) (f y)) (hom B (f x) (f y)) (hom C (k' (f x)) (k' (f y)))
      ( ap-hom B C k' (f x) (f y))
      ( transport (A → B) (\ f' → hom B (f' x) (f' y)) f f refl)

    = comp
      ( hom B (f x) (f y))
      ( hom C (h (f x)) (h (f y)))
      ( hom C (k' (f x)) (k' (f y)))
      ( transport (A → C) (\ f' → hom C (f' x) (f' y))
        ( comp A B C h f)
        ( comp A B C k' f)
        ( comp-homotopic-maps A B C f f h k' refl q'))
      ( ap-hom B C h (f x) (f y)))
    ( refl)
    ( k)
    ( q))
  ( g)
  ( p)
```

## Natural transformations

Given two simplicial maps `#!rzk f g : (x : A) → B x` , a **natural
transformation** from `#!rzk f` to `#!rzk g` is an arrow
`#!rzk η : hom ((x : A) → B x) f g` between them.

```rzk title="RS17, Definition 6.2"
#def nat-trans
  ( A : U)
  ( B : A → U)
  ( f g : (x : A) → (B x))
  : U
  := hom ((x : A) → (B x)) f g
```

Equivalently , natural transformations can be determined by their **components**
, i.e. as a family of arrows `#!rzk (x : A) → hom (B x) (f x) (g x)`.

```rzk
#def nat-trans-components
  ( A : U)
  ( B : A → U)
  ( f g : (x : A) → (B x))
  : U
  := (x : A) → hom (B x) (f x) (g x)
```

```rzk
#def ev-components-nat-trans
  ( A : U)
  ( B : A → U)
  ( f g : (x : A) → (B x))
  ( η : nat-trans A B f g)
  : nat-trans-components A B f g
  := \ x t → η t x

#def nat-trans-nat-trans-components
  ( A : U)
  ( B : A → U)
  ( f g : (x : A) → (B x))
  ( η : nat-trans-components A B f g)
  : nat-trans A B f g
  := \ t x → η x t
```

### Natural transformation extensionality

```rzk title="RS17, Proposition 6.3"
#def is-equiv-ev-components-nat-trans
  ( A : U)
  ( B : A → U)
  ( f g : (x : A) → (B x))
  : is-equiv
      ( nat-trans A B f g)
      ( nat-trans-components A B f g)
      ( ev-components-nat-trans A B f g)
  :=
    ( ( \ η t x → η x t , \ _ → refl)
    , ( \ η t x → η x t , \ _ → refl))

#def equiv-components-nat-trans
  ( A : U)
  ( B : A → U)
  ( f g : (x : A) → (B x))
  : Equiv (nat-trans A B f g) (nat-trans-components A B f g)
  :=
    ( ev-components-nat-trans A B f g
    , is-equiv-ev-components-nat-trans A B f g)
```

### Naturality square

Natural transformations are automatically natural when the codomain is a Segal
type.

```rzk title="RS17, Proposition 6.6"
#section comp-eq-square-is-segal

#variable A : U
#variable is-segal-A : is-segal A
#variable α : (Δ¹×Δ¹) → A

#def α00
  : A
  := α (0₂ , 0₂)
#def α01
  : A
  := α (0₂ , 1₂)
#def α10
  : A
  := α (1₂ , 0₂)
#def α11
  : A
  := α (1₂ , 1₂)

#def α0*
  : Δ¹ → A
  := \ t → α (0₂ , t)
#def α1*
  : Δ¹ → A
  := \ t → α (1₂ , t)
#def α*0
  : Δ¹ → A
  := \ s → α (s , 0₂)
#def α*1
  : Δ¹ → A
  := \ s → α (s , 1₂)
#def α-diag
  : Δ¹ → A
  := \ s → α (s , s)

#def lhs uses (α)
  : Δ¹ → A
  := comp-is-segal A is-segal-A α00 α01 α11 α0* α*1
#def rhs uses (α)
  : Δ¹ → A
  := comp-is-segal A is-segal-A α00 α10 α11 α*0 α1*

#def lower-triangle-square
  : hom2 A α00 α01 α11 α0* α*1 α-diag
  := \ (s , t) → α (t , s)

#def upper-triangle-square
  : hom2 A α00 α10 α11 α*0 α1* α-diag
  := \ (s , t) → α (s , t)

#def comp-eq-square-is-segal uses (α)
  : comp-is-segal A is-segal-A α00 α01 α11 α0* α*1
  = comp-is-segal A is-segal-A α00 α10 α11 α*0 α1*
  :=
    zig-zag-concat (hom A α00 α11) lhs α-diag rhs
    ( uniqueness-comp-is-segal A is-segal-A α00 α01 α11 α0* α*1 α-diag
      ( lower-triangle-square))
    ( uniqueness-comp-is-segal A is-segal-A α00 α10 α11 α*0 α1* α-diag
      ( upper-triangle-square))


#end comp-eq-square-is-segal
```

We now extract a naturality square from a natural transformation whose codomain
is a Segal type.

```rzk title="RS17, Proposition 6.6"
#def naturality-nat-trans-is-segal
  ( A B : U)
  ( is-segal-B : is-segal B)
  ( f g : A → B)
  ( α : nat-trans A (\ _ → B) f g)
  ( x y : A)
  ( k : hom A x y)
  : comp-is-segal B is-segal-B (f x) (f y) (g y)
    ( ap-hom A B f x y k)
    ( \ s → α s y)
  = comp-is-segal B is-segal-B (f x) (g x) (g y)
    ( \ s → α s x)
    ( ap-hom A B g x y k)
  := comp-eq-square-is-segal B is-segal-B (\ (s , t) → α s (k t))
```

### Vertical composition

We can define vertical composition for natural transformations in families of
Segal types.

```rzk
#def vertical-comp-nat-trans-components
  ( A : U)
  ( B : A → U)
  ( is-segal-B : (x : A) → is-segal (B x))
  ( f g h : (x : A) → (B x))
  ( η : nat-trans-components A B f g)
  ( η' : nat-trans-components A B g h)
  : nat-trans-components A B f h
  := \ x → comp-is-segal (B x) (is-segal-B x) (f x) (g x) (h x) (η x) (η' x)

#def vertical-comp-nat-trans
  ( A : U)
  ( B : A → U)
  ( is-segal-B : (x : A) → is-segal (B x))
  ( f g h : (x : A) → (B x))
  ( η : nat-trans A B f g)
  ( η' : nat-trans A B g h)
  : nat-trans A B f h
  :=
    \ t x →
    vertical-comp-nat-trans-components A B is-segal-B f g h
      ( \ x' t' → η t' x')
      ( \ x' t' → η' t' x')
      ( x)
      ( t)
```

### Functoriality of evaluation at components

The components of the identity natural transformation are identity arrows.

```rzk title="RS17, Proposition 6.5(ii)"
#def id-arr-components-id-nat-trans
  ( A : U)
  ( B : A → U)
  ( f : (x : A) → (B x))
  ( a : A)
  : ( ev-components-nat-trans A B f f (id-hom ((x : A) → B x) f)) a
  = id-hom (B a) (f a)
  := refl
```

When the fibers of a family of types `#!rzk B : A → U` are Segal types, the
components of the natural transformation defined by composing in the Segal type
`#!rzk (x : A) → B x` agree with the components defined by vertical composition.

```rzk title="RS17, Proposition 6.5(i)"
#def comp-components-comp-nat-trans-is-segal uses (funext)
  ( A : U)
  ( B : A → U)
  ( is-segal-B : (x : A) → is-segal (B x))
  ( f g h : (x : A) → (B x))
  ( α : nat-trans A B f g)
  ( β : nat-trans A B g h)
  ( a : A)
  : ( comp-is-segal (B a) (is-segal-B a) (f a) (g a) (h a)
      ( ev-components-nat-trans A B f g α a)
      ( ev-components-nat-trans A B g h β a))
  = ( ev-components-nat-trans A B f h
      ( comp-is-segal
        ( ( x : A) → B x) (is-segal-function-type (funext) (A) (B) (is-segal-B))
        ( f) (g) (h) (α) (β))) a
  :=
    functors-pres-comp
    ( ( x : A) → (B x)) (B a)
    ( is-segal-function-type (funext) (A) (B) (is-segal-B)) (is-segal-B a)
    ( \ s → s a) (f) (g) (h) (α) (β)
```

### Horizontal composition

Horizontal composition of natural transformations makes sense over any type. In
particular , contrary to what is written in [RS17] we do not need `#!rzk C` to
be Segal.

```rzk
#def horizontal-comp-nat-trans
  ( A B C : U)
  ( f g : A → B)
  ( f' g' : B → C)
  ( η : nat-trans A (\ _ → B) f g)
  ( η' : nat-trans B (\ _ → C) f' g')
  : nat-trans A (\ _ → C) (\ x → f' (f x)) (\ x → g' (g x))
  := \ t x → η' t (η t x)

#def horizontal-comp-nat-trans-components
  ( A B C : U)
  ( f g : A → B)
  ( f' g' : B → C)
  ( η : nat-trans-components A (\ _ → B) f g)
  ( η' : nat-trans-components B (\ _ → C) f' g')
  : nat-trans-components A (\ _ → C) (\ x → f' (f x)) (\ x → g' (g x))
  := \ x t → η' (η x t) t
```

### Whiskering

Whiskering is a special case of horizontal composition when one of the natural
transformations is the identity.

```rzk
#def postwhisker-nat-trans
  ( B C D : U)
  ( f g : B → C)
  ( h : C → D)
  ( η : nat-trans B (\ _ → C) f g)
  : nat-trans B (\ _ → D) (comp B C D h f) (comp B C D h g)
  := horizontal-comp-nat-trans B C D f g h h η (id-hom (C → D) h)

#def prewhisker-nat-trans
  ( A B C : U)
  ( k : A → B)
  ( f g : B → C)
  ( η : nat-trans B (\ _ → C) f g)
  : nat-trans A (\ _ → C) (comp A B C f k) (comp A B C g k)
  := horizontal-comp-nat-trans A B C k k f g (id-hom (A → B) k) η

#def whisker-nat-trans
  ( A B C D : U)
  ( k : A → B)
  ( f g : B → C)
  ( h : C → D)
  ( η : nat-trans B (\ _ → C) f g)
  : nat-trans A (\ _ → D)
    ( triple-comp A B C D h f k)
    ( triple-comp A B C D h g k)
  :=
    postwhisker-nat-trans A C D (comp A B C f k) (comp A B C g k) h
    ( prewhisker-nat-trans A B C k f g η)

```

## Gray interchanger

The horizontal composition operation also defines coherence data in the form of
the "Gray interchanger" built from two commutative triangles.

```rzk
#def gray-interchanger-horizontal-comp-nat-trans
  ( A B C : U)
  ( f g : A → B)
  ( f' g' : B → C)
  ( η : nat-trans A (\ _ → B) f g)
  ( η' : nat-trans B (\ _ → C) f' g')
  : Δ¹×Δ¹ → (A → C)
  := \ (t , s) a → η' s (η t a)

#def left-gray-interchanger-horizontal-comp-nat-trans
  ( A B C : U)
  ( f g : A → B)
  ( f' g' : B → C)
  ( η : nat-trans A (\ _ → B) f g)
  ( η' : nat-trans B (\ _ → C) f' g')
  : hom2 (A → C) (comp A B C f' f) (comp A B C f' g) (comp A B C g' g)
    ( postwhisker-nat-trans A B C f g f' η)
    ( prewhisker-nat-trans A B C g f' g' η')
    ( horizontal-comp-nat-trans A B C f g f' g' η η')
  := \ (t , s) a → η' s (η t a)

#def right-gray-interchanger-horizontal-comp-nat-trans
  ( A B C : U)
  ( f g : A → B)
  ( f' g' : B → C)
  ( η : nat-trans A (\ _ → B) f g)
  ( η' : nat-trans B (\ _ → C) f' g')
  : hom2 (A → C) (comp A B C f' f) (comp A B C g' f) (comp A B C g' g)
    ( prewhisker-nat-trans A B C f f' g' η')
    ( postwhisker-nat-trans A B C f g g' η)
    ( horizontal-comp-nat-trans A B C f g f' g' η η')
  := \ (t , s) a → η' t (η s a)
```

## Equivalences are fully faithful

Since `#!rzk hom` is defined as an extension type, `#!rzk ap-hom` correspond to
postcomposition. Hence, we can use `#!rzk is-equiv-extensions-is-equiv` to show
that `#!rzk ap-hom` is an equivalence when f is an equivalence.

```rzk
#def is-equiv-ap-hom-is-equiv uses (extext)
  ( A B : U)
  ( f : A → B)
  ( is-equiv-f : is-equiv A B f)
  ( x y : A)
  : is-equiv (hom A x y) (hom B (f x) (f y)) (ap-hom A B f x y)
  :=
    is-equiv-extensions-is-equiv extext 2 Δ¹ ∂Δ¹
    ( \ _ → A) (\ _ → B)
    ( \ _ → f)
    ( \ t → recOR (t ≡ 0₂ ↦ x , t ≡ 1₂ ↦ y))
    ( \ _ → is-equiv-f)
```

More precicely:

```rzk
#def fiber-ap-hom
  ( A B : U)
  ( x y : A)
  ( f : A → B)
  ( β : hom B (f x) (f y))
  : U
  :=
    fib (hom A x y) (hom B (f x) (f y)) (ap-hom A B f x y) (β)

#def is-contr-fiber-ap-hom-is-equiv uses (extext)
  ( A B : U)
  ( f : A → B)
  ( is-equiv-f : is-equiv A B f)
  ( x y : A)
  ( β : hom B (f x) (f y))
  : is-contr (fiber-ap-hom A B x y f β)
  :=
    is-contr-fiber-postcomp-Π-ext-is-equiv-fam extext 2 Δ¹ ∂Δ¹
    ( \ _ → A) (\ _ → B)
    ( \ _ → f)
    ( \ t → recOR (t ≡ 0₂ ↦ x , t ≡ 1₂ ↦ y))
    ( β)
    ( \ _ → is-equiv-f)
```

We can also define a retraction of `#!rzk ap-hom` directly.

```rzk
#def has-retraction-ap-hom-retraction uses (extext)
  ( A B : U)
  ( f : A → B)
  ( has-retraction-f : has-retraction A B f)
  ( x y : A)
  : has-retraction (hom A x y) (hom B (f x) (f y)) (ap-hom A B f x y)
  :=
    has-retraction-extensions-has-retraction extext 2 Δ¹ ∂Δ¹
    ( \ _ → A) (\ _ → B)
    ( \ _ → f)
    ( \ _ → has-retraction-f)
    ( \ t → recOR (t ≡ 0₂ ↦ x , t ≡ 1₂ ↦ y))
```
