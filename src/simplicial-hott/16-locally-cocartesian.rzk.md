# Coherently locally cocartesian families

This is a formalization of part of the theory of coherenttly locally cocartesian
families as developed in Chapter 5 of [Rob Schellingerhout (2026), Master's thesis, §4](https://studenttheses.uu.nl/items/6b387401-50f1-4463-836a-9ee8c138fec6).

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

```rzk
#assume funext : FunExt
#assume extext : ExtExt
```

## Prerequisites

- `hott/*` - We require various prerequisites from homotopy type theory, for
  instance the axiom of function extensionality.
- `02-simplicial-type-theory.rzk.md`
- `03-extension-types.rzk.md`
- `13-inner.rzk.md` - We use (iso)inner families.
- `14-cocartesian.rzk.md`
- `15-coherent-actions.rzk.md`

## Locally cocartesian arrows

```rzk title="S26, Definition 5.1.7"
#def is-locally-cocartesian-arrow
  ( B : U)
  ( b b' : B)
  ( u : hom B b b')
  ( P : B → U)
  ( e : P b)
  ( e' : P b')
  ( f : dhom B b b' u P e e')
  : U
  :=
  ( e'' : P b')
  → is-cocartesian-arrow-over
    B b b' b' u (id-hom B b') u (comp-id-witness B b b' u)
    P e e' e'' f
```

### An arrow is locally cocartesian if and only if post-composition is an equivalence

```rzk

#def is-locally-cocartesian-arrow-is-equiv-comp-over-is-inner-is-inner
  ( B : U)
  ( P : B → U)
  ( is-inner-P : is-inner-family B P)
  ( b b' : B)
  ( u : hom B b b')
  ( e : P b)
  ( e' : P b')
  ( f : dhom B b b' u P e e')
  : ( ( e'' : P b')
  → is-equiv
      ( hom (P b') e' e'')
      ( dhom B b b' u P e e'')
      ( comp-over-is-inner-family B P is-inner-P
        b b' b' u (id-hom B b') u (comp-id-witness B b b' u) e e' e'' f))
  → is-locally-cocartesian-arrow B b b' u P e e' f
  :=
  \ is-equiv-comp e'' →
    is-cocartesian-arrow-over-is-equiv-comp-over-is-inner B P is-inner-P
      b b' b' u (id-hom B b') u (comp-id-witness B b b' u) e e' e'' f
      ( is-equiv-comp e'')

#def is-equiv-comp-over-is-inner-locally-cocartesian-arrow-is-inner
  ( B : U)
  ( P : B → U)
  ( is-inner-P : is-inner-family B P)
  ( b b' : B)
  ( u : hom B b b')
  ( e : P b)
  ( e' : P b')
  ( f : dhom B b b' u P e e')
  : is-locally-cocartesian-arrow B b b' u P e e' f
  → ( e'' : P b') → is-equiv
    ( hom (P b') e' e'')
    ( dhom B b b' u P e e'')
    ( comp-over-is-inner-family B P is-inner-P
      b b' b' u (id-hom B b') u (comp-id-witness B b b' u) e e' e'' f)
  :=
  \ is-locally-cocart-f e'' →
    is-equiv-comp-over-is-inner-is-cocartesian-arrow-over B P is-inner-P
      b b' b' u (id-hom B b') u (comp-id-witness B b b' u) e e' e'' f
      ( is-locally-cocart-f e'')

#def equiv-hom-dhom-is-locally-cocartesian-arrow-is-inner
  ( B : U)
  ( P : B → U)
  ( is-inner-P : is-inner-family B P)
  ( b b' : B)
  ( u : hom B b b')
  ( e : P b)
  ( e' : P b')
  ( f : dhom B b b' u P e e')
  ( is-locally-cocart-f : is-locally-cocartesian-arrow B b b' u P e e' f)
  : ( e'' : P b')
  → Equiv (hom (P b') e' e'') (dhom B b b' u P e e'')
  :=
  \ e'' →
    ( comp-over-is-inner-family B P is-inner-P
      b b' b' u (id-hom B b') u (comp-id-witness B b b' u) e e' e'' f
    , is-equiv-comp-over-is-inner-locally-cocartesian-arrow-is-inner
      B P is-inner-P
      b b' u e e' f is-locally-cocart-f
      e'')

```

## Coherently locally cocartesian family

A family is coherently locally cocartesian if it is isoinner and any arrow in
the base has a locally cocartesian lift, given a point in the fiber over
the domain. The reason for the prefix 'coherently' here is that these lifts are
required to exist functorialy in the base, which is not the case for the
classical notion of locally cocartesian fibrations.

```rzk
#def has-locally-cocartesian-lifts
  ( B : U)
  ( P : B → U)
  : U
  :=
    ( b : B) → (b' : B) → (u : hom B b b')
    → ( e : P b) → (Σ (e' : P b')
      , ( Σ ( f : dhom B b b' u P e e') , is-locally-cocartesian-arrow B b b' u
          P e e' f))
```

```rzk title="S26, Definition 5.1.8"
#def is-coherently-locally-cocartesian-family
  ( B : U)
  ( P : B → U)
  : U
  := product (is-isoinner-family B P) (has-locally-cocartesian-lifts B P)
```

## Coherently locally cocartesian families have a coherent action

```rzk

#section coherent-action-locally-cocartesian

#variable B : U
#variable E : B → U
#variable is-coherently-locally-cocartesian-family-E :
  is-coherently-locally-cocartesian-family B E
```

### The action

The action induced by being a coherently locally cocartesian family.

```rzk title="S26, Lemma 5.1.9"
#def action-coherently-locally-cocartesian
  ( x y : B)
  ( f : hom B x y)
  : E x → E y
  :=
  \ e → first (second
    ( is-coherently-locally-cocartesian-family-E)
    ( x) (y) (f) (e))
```

### The chosen locally cocartesian lifts

```rzk
#def lift-coherently-locally-cocartesian
  ( x y : B)
  ( f : hom B x y)
  ( e : E x)
  : dhom B x y f E e (action-coherently-locally-cocartesian x y f e)
  :=
  first (second (second
    ( is-coherently-locally-cocartesian-family-E)
    ( x) (y) (f) (e)))

#def is-locally-cocartesian-lift-coherently-locally-cocartesian
  ( x y : B)
  ( f : hom B x y)
  ( e : E x)
  : is-locally-cocartesian-arrow B x y f E
    e
    ( action-coherently-locally-cocartesian x y f e)
    ( lift-coherently-locally-cocartesian x y f e)
  :=
  second (second (second
    ( is-coherently-locally-cocartesian-family-E)
    ( x) (y) (f) (e)))

```

### The vertical morphism induced by a dependent morphism
```rzk

#def hom-dhom-coherently-locally-cocartesian
  uses (is-coherently-locally-cocartesian-family-E)
  ( x y : B)
  ( f : hom B x y)
  ( x' : E x)
  ( y' : E y)
  : dhom B x y f E x' y'
  → hom (E y) (action-coherently-locally-cocartesian x y f x') y'
  :=
  \ f' →
    first (first (is-locally-cocartesian-lift-coherently-locally-cocartesian
      x y f x' y' f'))

#def fill-dhom-coherently-locally-cocartesian
  uses (is-coherently-locally-cocartesian-family-E)
  ( x y : B)
  ( f : hom B x y)
  ( x' : E x)
  ( y' : E y)
  ( h' : dhom B x y f E x' y')
  : dhom2 B x y y f (id-hom B y) f (comp-id-witness B x y f) E
    ( x')
    ( action-coherently-locally-cocartesian x y f x')
    ( y')
    ( lift-coherently-locally-cocartesian x y f x')
    ( hom-dhom-coherently-locally-cocartesian x y f x' y' h')
    ( h')
  :=
  second (first (is-locally-cocartesian-lift-coherently-locally-cocartesian
    x y f x' y' h'))


```

Any triangle with, bottom edge being the locally cocartesian lift induces an
equality between the vertical morphism and the induced one.

```rzk

#def eq-hom-dhom2-coherently-locally-cocartesian
  uses (is-coherently-locally-cocartesian-family-E)
  ( x y : B)
  ( f : hom B x y)
  ( x' : E x)
  ( y' : E y)
  ( h' : dhom B x y f E x' y')
  ( g' : hom (E y) (action-coherently-locally-cocartesian x y f x') y')
  : dhom2 B x y y f (id-hom B y) f (comp-id-witness B x y f) E
    ( x')
    ( action-coherently-locally-cocartesian x y f x')
    ( y')
    ( lift-coherently-locally-cocartesian x y f x')
    ( g')
    ( h')
  → hom-dhom-coherently-locally-cocartesian x y f x' y' h' = g'
  :=
  \ σ' →
    ap
      ( Σ ( g' : hom (E y) (action-coherently-locally-cocartesian x y f x') y')
      , dhom2 B x y y f (id-hom B y) f (comp-id-witness B x y f) E
        ( x')
        ( action-coherently-locally-cocartesian x y f x')
        ( y')
        ( lift-coherently-locally-cocartesian x y f x')
        ( g')
        ( h'))
      ( hom (E y) (action-coherently-locally-cocartesian x y f x') y')
      ( hom-dhom-coherently-locally-cocartesian x y f x' y' h'
      , fill-dhom-coherently-locally-cocartesian x y f x' y' h')
      ( g' , σ')
      ( \ (g' , σ') → g')
      ( homotopy-contraction
        ( Σ ( g' : hom (E y) (action-coherently-locally-cocartesian x y f x') y')
        , dhom2 B x y y f (id-hom B y) f (comp-id-witness B x y f) E
          ( x')
          ( action-coherently-locally-cocartesian x y f x')
          ( y')
          ( lift-coherently-locally-cocartesian x y f x')
          ( g')
          ( h'))
        ( is-locally-cocartesian-lift-coherently-locally-cocartesian
          x y f x' y' h')
        ( g' , σ'))

```

### Unitality

This action is unital.

```rzk title="S26, Lemma 5.1.9"

#def unit-iso-action-coherently-locally-cocartesian
  ( x : B)
  ( e : E x)
  : Iso (E x)
    ( is-segal-fiber-is-isoinner-family B E
      ( first is-coherently-locally-cocartesian-family-E) x)
    ( action-coherently-locally-cocartesian x x (id-hom B x) e)
    ( e)
  :=
  rev-iso extext
    ( E x)
    ( is-segal-fiber-is-isoinner-family B E
      ( first is-coherently-locally-cocartesian-family-E) x)
    ( e)
    ( action-coherently-locally-cocartesian x x (id-hom B x) e)
    ( arr-map-representable-equiv (E x)
      ( action-coherently-locally-cocartesian x x (id-hom B x) e)
      ( e)
      ( equiv-hom-dhom-is-locally-cocartesian-arrow-is-inner B E
        ( is-inner-family-is-iso-inner-family B E
          ( first is-coherently-locally-cocartesian-family-E))
        x x (id-hom B x)
        ( e)
        ( action-coherently-locally-cocartesian x x (id-hom B x) e)
        ( lift-coherently-locally-cocartesian x x (id-hom B x) e)
        ( is-locally-cocartesian-lift-coherently-locally-cocartesian
          x x (id-hom B x) e))
    , representable-isomorphism funext extext (E x)
      ( is-segal-fiber-is-isoinner-family B E
        ( first is-coherently-locally-cocartesian-family-E) x)
      ( action-coherently-locally-cocartesian x x (id-hom B x) e)
      ( e)
      ( equiv-hom-dhom-is-locally-cocartesian-arrow-is-inner B E
        ( is-inner-family-is-iso-inner-family B E
          ( first is-coherently-locally-cocartesian-family-E))
        x x (id-hom B x)
        ( e)
        ( action-coherently-locally-cocartesian x x (id-hom B x) e)
        ( lift-coherently-locally-cocartesian x x (id-hom B x) e)
        ( is-locally-cocartesian-lift-coherently-locally-cocartesian
          x x (id-hom B x) e)))

#def is-unital-action-coherently-locally-cocartesian uses (extext funext)
  ( x : B)
  ( e : E x)
  : action-coherently-locally-cocartesian x x (id-hom B x) e = e
  :=
  eq-iso-is-rezk
    ( E x)
    ( is-rezk-fiber-is-isoinner-family B E
      ( first is-coherently-locally-cocartesian-family-E) x)
    ( action-coherently-locally-cocartesian x x (id-hom B x) e)
    ( e)
    ( unit-iso-action-coherently-locally-cocartesian x e)

```

### The lift induced by the action is locally cocartesian

```rzk title="S26, Lemma 5.1.10"

#def lift-action-coherently-locally-cocartesian
  uses (is-coherently-locally-cocartesian-family-E)
  ( x y : B)
  ( f : hom B x y)
  ( e : E x)
  : dhom B x y f E
    ( action-coherently-locally-cocartesian x x (id-hom B x) e)
    ( action-coherently-locally-cocartesian x y f e)
  :=
  lift-action B E action-coherently-locally-cocartesian x y f e

```

There is a comparison morphism from the lift induced from the action to the
chosen locally cocartesian lift.

```rzk

#def comparison-lifts-coherently-locally-cocartesian
  uses (is-coherently-locally-cocartesian-family-E)
  ( x y : B)
  ( f : hom B x y)
  ( e : E x)
  : ( t : Δ¹)
  → hom (E (f t))
      ( lift-action-coherently-locally-cocartesian x y f e t)
      ( lift-coherently-locally-cocartesian x y f e t)
  :=
  \ t →
    hom-dhom-coherently-locally-cocartesian
      ( x) (f t) (clamp-above B f t)
      ( e)
      ( lift-coherently-locally-cocartesian x y f e t)
      ( dclamp-above B E f (lift-coherently-locally-cocartesian x y f e) t)

```

This comparison square is an isomorphism in the endpoints.

```rzk

#def is-iso-comparison-lifts-0-coherently-locally-cocartesian
  uses (extext funext)
  ( x y : B)
  ( f : hom B x y)
  ( e : E x)
  : is-iso-arrow (E x)
    ( is-segal-fiber-is-isoinner-family B E
      ( first is-coherently-locally-cocartesian-family-E) x)
    ( action-coherently-locally-cocartesian x x (id-hom B x) e)
    ( e)
    ( comparison-lifts-coherently-locally-cocartesian x y f e 0₂)
  :=
  second (unit-iso-action-coherently-locally-cocartesian x e)


#def is-iso-comparison-lifts-1-coherently-locally-cocartesian
  ( x y : B)
  ( f : hom B x y)
  ( e : E x)
  : is-iso-arrow (E y)
    ( is-segal-fiber-is-isoinner-family B E
      ( first is-coherently-locally-cocartesian-family-E) y)
    ( action-coherently-locally-cocartesian x y f e)
    ( action-coherently-locally-cocartesian x y f e)
    ( comparison-lifts-coherently-locally-cocartesian x y f e 1₂)
  :=
  transport
    ( hom (E y)
      ( action-coherently-locally-cocartesian x y f e)
      ( action-coherently-locally-cocartesian x y f e))
    ( is-iso-arrow (E y)
      ( is-segal-fiber-is-isoinner-family B E
        ( first is-coherently-locally-cocartesian-family-E) y)
      ( action-coherently-locally-cocartesian x y f e)
      ( action-coherently-locally-cocartesian x y f e))
    ( id-hom (E y) (action-coherently-locally-cocartesian x y f e))
    ( comparison-lifts-coherently-locally-cocartesian x y f e 1₂)
    ( rev
      ( hom (E y)
        ( action-coherently-locally-cocartesian x y f e)
        ( action-coherently-locally-cocartesian x y f e))
      ( comparison-lifts-coherently-locally-cocartesian x y f e 1₂)
      ( id-hom (E y) (action-coherently-locally-cocartesian x y f e))
      ( eq-hom-dhom2-coherently-locally-cocartesian x y f
        ( e)
        ( action-coherently-locally-cocartesian x y f e)
        ( lift-coherently-locally-cocartesian x y f e)
        ( id-hom (E y) (action-coherently-locally-cocartesian x y f e))
        ( \ (s , t) → lift-coherently-locally-cocartesian x y f e s)))
    ( is-iso-arrow-id-hom
      ( E y)
      ( is-segal-fiber-is-isoinner-family B E
        ( first is-coherently-locally-cocartesian-family-E) y)
      ( action-coherently-locally-cocartesian x y f e))

```

This square shows that the two types of lifts agree.

```rzk

#def eq-lift-action-lift-coherently-locally-cocartesian-family
  uses (extext funext)
  ( x y : B)
  ( f : hom B x y)
  ( e : E x)
  : ( lift-action-coherently-locally-cocartesian x y f e)
  =_{darr B f E}
  ( lift-coherently-locally-cocartesian x y f e)
  :=
  eq-darr-square-is-isoinner-family B E
    ( first is-coherently-locally-cocartesian-family-E)
    ( x) (y) (f)
    ( lift-action-coherently-locally-cocartesian x y f e)
    ( lift-coherently-locally-cocartesian x y f e)
    ( comparison-lifts-coherently-locally-cocartesian x y f e)
    ( is-iso-comparison-lifts-0-coherently-locally-cocartesian x y f e)
    ( is-iso-comparison-lifts-1-coherently-locally-cocartesian x y f e)

```

It follows that the lift induced by the action is also locally cocartesian.

```rzk

#def is-locally-cocartesian-lift-action-coherently-locally-cocartesian
  uses (extext funext is-coherently-locally-cocartesian-family-E)
  ( x y : B)
  ( f : hom B x y)
  ( e : E x)
  : is-locally-cocartesian-arrow B x y f E
    ( action-coherently-locally-cocartesian x x (id-hom B x) e)
    ( action-coherently-locally-cocartesian x y f e)
    ( lift-action-coherently-locally-cocartesian x y f e)
  :=
  transport-rev
    ( darr B f E)
    ( \ f' → is-locally-cocartesian-arrow B x y f E (f' 0₂) (f' 1₂) (f'))
    ( lift-action-coherently-locally-cocartesian x y f e)
    ( lift-coherently-locally-cocartesian x y f e)
    ( eq-lift-action-lift-coherently-locally-cocartesian-family x y f e)
    ( is-locally-cocartesian-lift-coherently-locally-cocartesian x y f e)

```

### The action is coherent

We will show that the coherence morphism is degenerate by constructing two
triangles involving these morphisms, with bottom edge locally cocartesian.

We'll define some useful shorthands.

```rzk

#def action2-coherently-locally-cocartesian
  uses (is-coherently-locally-cocartesian-family-E)
  ( x y z : B)
  ( f : hom B x y)
  ( g : hom B y z)
  : E x → E z
  :=
  \ e →
    action-coherently-locally-cocartesian y z g
      ( action-coherently-locally-cocartesian x y f e)

#def action-id-dhom-coherently-locally-cocartesian
  uses (is-coherently-locally-cocartesian-family-E)
  ( x y : B)
  ( f : hom B x y)
  ( x' : E x)
  ( y' : E y)
  ( f' : dhom B x y f E x' y')
  : dhom B x y f E
    ( action-coherently-locally-cocartesian x x (id-hom B x) x')
    ( action-coherently-locally-cocartesian y y (id-hom B y) y')
  :=
  \ t →
    action-coherently-locally-cocartesian (f t) (f t) (id-hom B (f t)) (f' t)

```

The triangle involving the coherence morphism.

```rzk

#def coherence-morphism-coherently-locally-cocartesian
  uses (is-coherently-locally-cocartesian-family-E)
  ( x y : B)
  ( f : hom B x y)
  ( e : E x)
  : hom (E y)
    ( action2-coherently-locally-cocartesian x x y (id-hom B x) f e)
    ( action2-coherently-locally-cocartesian x y y f (id-hom B y) e)
  :=
  coherence-morphism-action B E action-coherently-locally-cocartesian x y f e

#def dhom2-coherence-morphism-coherently-locally-cocartesian
  uses (is-coherently-locally-cocartesian-family-E)
  ( x y : B)
  ( f : hom B x y)
  ( e : E x)
  : dhom2 B x y y f (id-hom B y) f (comp-id-witness B x y f) E
    ( action2-coherently-locally-cocartesian x x x (id-hom B x) (id-hom B x) e)
    ( action2-coherently-locally-cocartesian x x y (id-hom B x) f e)
    ( action2-coherently-locally-cocartesian x y y f (id-hom B y) e)
    ( lift-action-coherently-locally-cocartesian x y f
      ( action-coherently-locally-cocartesian x x (id-hom B x) e))
    ( coherence-morphism-coherently-locally-cocartesian x y f e)
    ( action-id-dhom-coherently-locally-cocartesian x y f
      ( action-coherently-locally-cocartesian x x (id-hom B x) e)
      ( action-coherently-locally-cocartesian x y f e)
      ( lift-action-coherently-locally-cocartesian x y f e))
  :=
  \ (s , t) →
    action2-coherently-locally-cocartesian
      ( x) (f t) (f s)
      ( clamp-above B f t)
      ( clamp B f (s , t))
      ( e)

```

The triangle involving the zig-zag morphism.

```rzk

#def zig-zag-morphism-coherently-locally-cocartesian
  uses (extext funext is-coherently-locally-cocartesian-family-E)
  ( x y : B)
  ( f : hom B x y)
  ( e : E x)
  : hom (E y)
    ( action2-coherently-locally-cocartesian x x y (id-hom B x) f e)
    ( action2-coherently-locally-cocartesian x y y f (id-hom B y) e)
  :=
  zig-zag-morphism-unital-action B E
    action-coherently-locally-cocartesian
    is-unital-action-coherently-locally-cocartesian
    x y f e

#def square-zig-zag-morphism-coherently-locally-cocartesian
  uses (funext extext is-coherently-locally-cocartesian-family-E)
  ( x y : B)
  ( f : hom B x y)
  ( e : E x)
  : ( ( s , t) : 2 × 2) → E (f s)
  :=
  \ (s , t) →
    zig-zag-morphism-coherently-locally-cocartesian
      x (f s) (clamp-above B f s) e t

#def diagonal-square-zig-zag-morphism-coherently-locally-cocartesian
  uses (funext extext is-coherently-locally-cocartesian-family-E)
  ( x y : B)
  ( f : hom B x y)
  ( e : E x)
  : dhom B x y f E
    ( action2-coherently-locally-cocartesian x x x (id-hom B x) (id-hom B x) e)
    ( action2-coherently-locally-cocartesian x y y f (id-hom B y) e)
  :=
  \ t → square-zig-zag-morphism-coherently-locally-cocartesian x y f e (t , t)

#def dhom2-zig-zag-morphism-coherently-locally-cocartesian
  uses (extext is-coherently-locally-cocartesian-family-E)
  ( x y : B)
  ( f : hom B x y)
  ( e : E x)
  : dhom2 B x y y f (id-hom B y) f (comp-id-witness B x y f) E
    ( action2-coherently-locally-cocartesian x x x (id-hom B x) (id-hom B x) e)
    ( action2-coherently-locally-cocartesian x x y (id-hom B x) f e)
    ( action2-coherently-locally-cocartesian x y y f (id-hom B y) e)
    ( lift-action-coherently-locally-cocartesian x y f
      ( action-coherently-locally-cocartesian x x (id-hom B x) e))
    ( zig-zag-morphism-coherently-locally-cocartesian x y f e)
    ( action-id-dhom-coherently-locally-cocartesian x y f
      ( action-coherently-locally-cocartesian x x (id-hom B x) e)
      ( action-coherently-locally-cocartesian x y f e)
      ( lift-action-coherently-locally-cocartesian x y f e))
  :=
  transport
    ( dhom B x y f E
      ( action2-coherently-locally-cocartesian x x x (id-hom B x) (id-hom B x) e)
      ( action2-coherently-locally-cocartesian x y y f (id-hom B y) e))
    ( \ h' →
      dhom2 B x y y f (id-hom B y) f (comp-id-witness B x y f) E
      ( action2-coherently-locally-cocartesian x x x (id-hom B x) (id-hom B x) e)
      ( action2-coherently-locally-cocartesian x x y (id-hom B x) f e)
      ( action2-coherently-locally-cocartesian x y y f (id-hom B y) e)
      ( lift-action-coherently-locally-cocartesian x y f
        ( action-coherently-locally-cocartesian x x (id-hom B x) e))
      ( zig-zag-morphism-coherently-locally-cocartesian x y f e)
      ( h')
    )
    ( diagonal-square-zig-zag-morphism-coherently-locally-cocartesian x y f e)
    ( action-id-dhom-coherently-locally-cocartesian x y f
      ( action-coherently-locally-cocartesian x x (id-hom B x) e)
      ( action-coherently-locally-cocartesian x y f e)
      ( lift-action-coherently-locally-cocartesian x y f e))
    ( eq-dhom2-id-hom-inner-family B E
      ( is-inner-family-is-iso-inner-family B E
        ( first is-coherently-locally-cocartesian-family-E))
      x y f
      ( action2-coherently-locally-cocartesian x x x (id-hom B x) (id-hom B x) e)
      ( action2-coherently-locally-cocartesian x y y f (id-hom B y) e)
      ( diagonal-square-zig-zag-morphism-coherently-locally-cocartesian x y f e)
      ( action-id-dhom-coherently-locally-cocartesian x y f
        ( action-coherently-locally-cocartesian x x (id-hom B x) e)
        ( action-coherently-locally-cocartesian x y f e)
        ( lift-action-coherently-locally-cocartesian x y f e))
      ( transport
        ( hom (E x)
          ( action2-coherently-locally-cocartesian x x x
            ( id-hom B x) (id-hom B x) e)
          ( action2-coherently-locally-cocartesian x x x
            ( id-hom B x) (id-hom B x) e))
        ( \ f' →
          dhom2 B x x y (id-hom B x) f f (id-comp-witness B x y f) E
            ( action2-coherently-locally-cocartesian x x x
              ( id-hom B x) (id-hom B x) e)
            ( action2-coherently-locally-cocartesian x x x
              ( id-hom B x) (id-hom B x) e)
            ( action2-coherently-locally-cocartesian x y y f (id-hom B y) e)
            f'
            ( action-id-dhom-coherently-locally-cocartesian x y f
              ( action-coherently-locally-cocartesian x x (id-hom B x) e)
              ( action-coherently-locally-cocartesian x y f e)
              ( lift-action-coherently-locally-cocartesian x y f e))
            ( diagonal-square-zig-zag-morphism-coherently-locally-cocartesian
              x y f e))
        ( zig-zag-morphism-coherently-locally-cocartesian x x (id-hom B x) e)
        ( id-hom (E x)
          ( action2-coherently-locally-cocartesian x x x
            ( id-hom B x) (id-hom B x) e))
        ( eq-zig-zag-morphism-id-id-unital-action funext B E
          action-coherently-locally-cocartesian
          is-unital-action-coherently-locally-cocartesian
          x
          e)
        ( \ (s , t) →
          square-zig-zag-morphism-coherently-locally-cocartesian x y f e
            ( t , s))))
    ( square-zig-zag-morphism-coherently-locally-cocartesian x y f e)

```

We use locally cocartesianness to show that these triangles are equal and
consequently, that coherence morphism is the zig-zag morphism.

```rzk title="S26, Lemma 5.1.11"

#def is-coherent-action-coherently-locally-cocartesian
  uses (funext extext is-coherently-locally-cocartesian-family-E)
  : is-coherent-unital-action' B E
    action-coherently-locally-cocartesian
    is-unital-action-coherently-locally-cocartesian
  :=
  \ x y f e →
    ap
      ( Σ ( g' : hom (E y)
        ( action2-coherently-locally-cocartesian x x y (id-hom B x) f e)
        ( action2-coherently-locally-cocartesian x y y f (id-hom B y) e))
      , dhom2 B x y y f (id-hom B y) f (comp-id-witness B x y f) E
          ( action2-coherently-locally-cocartesian x x x
            ( id-hom B x) (id-hom B x) e)
          ( action2-coherently-locally-cocartesian x x y (id-hom B x) f e)
          ( action2-coherently-locally-cocartesian x y y f (id-hom B y) e)
          ( lift-action-coherently-locally-cocartesian x y f
            ( action-coherently-locally-cocartesian x x (id-hom B x) e))
          ( g')
          ( action-id-dhom-coherently-locally-cocartesian x y f
            ( action-coherently-locally-cocartesian x x (id-hom B x) e)
            ( action-coherently-locally-cocartesian x y f e)
            ( lift-action-coherently-locally-cocartesian x y f e)))
      ( hom (E y)
        ( action2-coherently-locally-cocartesian x x y (id-hom B x) f e)
        ( action2-coherently-locally-cocartesian x y y f (id-hom B y) e))
      ( coherence-morphism-coherently-locally-cocartesian x y f e
      , dhom2-coherence-morphism-coherently-locally-cocartesian x y f e)
      ( zig-zag-morphism-coherently-locally-cocartesian x y f e
      , dhom2-zig-zag-morphism-coherently-locally-cocartesian x y f e)
      ( \ p → first p)
      ( all-elements-equal-is-contr
        ( Σ ( g' : hom (E y)
          ( action2-coherently-locally-cocartesian x x y (id-hom B x) f e)
          ( action2-coherently-locally-cocartesian x y y f (id-hom B y) e))
        , dhom2 B x y y f (id-hom B y) f (comp-id-witness B x y f) E
            ( action2-coherently-locally-cocartesian x x x
              ( id-hom B x) (id-hom B x) e)
            ( action2-coherently-locally-cocartesian x x y (id-hom B x) f e)
            ( action2-coherently-locally-cocartesian x y y f (id-hom B y) e)
            ( lift-action-coherently-locally-cocartesian x y f
              ( action-coherently-locally-cocartesian x x (id-hom B x) e))
            ( g')
            ( action-id-dhom-coherently-locally-cocartesian x y f
              ( action-coherently-locally-cocartesian x x (id-hom B x) e)
              ( action-coherently-locally-cocartesian x y f e)
              ( lift-action-coherently-locally-cocartesian x y f e)))
        ( is-locally-cocartesian-lift-action-coherently-locally-cocartesian
          x y f (action-coherently-locally-cocartesian x x (id-hom B x) e)
          ( action2-coherently-locally-cocartesian x y y f (id-hom B y) e)
          ( action-id-dhom-coherently-locally-cocartesian x y f
            ( action-coherently-locally-cocartesian x x (id-hom B x) e)
            ( action-coherently-locally-cocartesian x y f e)
            ( lift-action-coherently-locally-cocartesian x y f e)))
        ( coherence-morphism-coherently-locally-cocartesian x y f e
        , dhom2-coherence-morphism-coherently-locally-cocartesian x y f e)
        ( zig-zag-morphism-coherently-locally-cocartesian x y f e
        , dhom2-zig-zag-morphism-coherently-locally-cocartesian x y f e))

```


```rzk
#end coherent-action-locally-cocartesian
```



## Coherently locally cocartesian families are cocartesian

```rzk title="S26, Corollary 5.1.11.1"

#def is-cocartesian-coherently-locally-cocartesian uses (funext)
  ( B : U)
  ( E : B → U)
  ( is-coherently-locally-cocartesian-E :
    is-coherently-locally-cocartesian-family B E)
  : is-cocartesian-family B E
  :=
  is-cocartesian-coherent-action' extext B E
    ( first is-coherently-locally-cocartesian-E)
    ( action-coherently-locally-cocartesian B E
      is-coherently-locally-cocartesian-E)
    ( is-unital-action-coherently-locally-cocartesian B E
      is-coherently-locally-cocartesian-E)
    ( is-coherent-action-coherently-locally-cocartesian B E
      is-coherently-locally-cocartesian-E)

```
