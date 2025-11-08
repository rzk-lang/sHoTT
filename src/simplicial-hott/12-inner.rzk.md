# Inner families

This is a formalization of important feature of (iso-)inner families. In
particular, we provide an interface for dependent composition, crucially needed
for cocartesian families.

We build on [BW23, §4].

NB: We do not define them as orthogonal maps here but it would be desirable to
provide this characterization in the future.

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Prerequisites

- `hott/*` - We require various prerequisites from homotopy type theory, for
  instance the axiom of function extensionality.
- `03-simplicial-type-theory.rzk.md` — We rely on definitions of simplices and
  their subshapes.
- `04-extension-types.rzk.md` — We use the Fubini theorem and extension
  extensionality.
- `05-segal-types.rzk.md` - We make heavy use of the notion of Segal types
- `10-rezk-types.rzk.md`- We use Rezk types.

## (Iso-)Inner familiess

Inner families are (currently) defined as families where the base, the total type,
and the fibers are required to be Segal. This will induce a dependent composition operation
where we can fill (2,1)-horns in the total type over a given 2-simplex in the base.

Isoinner families are inner families where the base, total type, and the fibers are Rezk-complete.

```rzk
#def is-inner-family
  ( B : U)
  ( P : B → U)
  : U
  :=
    product
    ( product (is-segal B) (is-segal (Σ (b : B) , P b)))
    ( ( b : B) → (is-segal (P b)))

#def is-isoinner-family
  ( B : U)
  ( P : B → U)
  : U
  :=
    product
    ( product (is-rezk B) (is-rezk (Σ (b : B) , P b)))
    ( ( b : B) → (is-rezk (P b)))
```

Some easy but useful facts about (iso)inner families regarding their bases:

The base of an inner family is Segal.

```rzk
#def is-segal-base-is-inner
 ( B : U)
 ( P : B → U)
 ( is-inner-family-P : is-inner-family B P)
  : is-segal B
  := (first (first is-inner-family-P))
```

The base of an isoinner family is Rezk.

```rzk
#def is-rezk-base-is-isoinner
 ( B : U)
 ( P : B → U)
 ( is-isoinner-family-P : is-isoinner-family B P)
  : is-rezk B
  := (first (first is-isoinner-family-P))
```

The base of an isoinner family is isoinner.

```rzk
#def is-segal-base-is-isoinner
 ( B : U)
 ( P : B → U)
 ( is-isoinner-family-P : is-isoinner-family B P)
  : is-segal B
  := (is-segal-is-rezk B (first (first is-isoinner-family-P)))
```

The total type of an inner family is Segal.

```rzk
#def is-segal-total-type-is-inner
    ( B : U)
    ( P : B → U)
    ( is-inner-family-P : is-inner-family B P)
  : is-segal (total-type B P)
  := (second (first (is-inner-family-P)))
```

The total type of an isoinner family is Rezk.

```rzk
#def is-rezk-total-type-is-isoinner
    ( B : U)
    ( P : B → U)
    ( is-isoinner-family-P : is-isoinner-family B P)
  : is-rezk (total-type B P)
  := (second (first is-isoinner-family-P))
```

The total type of an isoinner family is iosinner.

```rzk
#def is-segal-total-type-is-isoinner
    ( B : U)
    ( P : B → U)
    ( is-isoinner-family-P : is-isoinner-family B P)
  : is-segal (total-type B P)
  := (is-segal-is-rezk (total-type B P) (is-rezk-total-type-is-isoinner B P is-isoinner-family-P))
```

An isoinner family is isoinner.

```rzk
#def is-inner-is-isoinner
 ( B : U)
 ( P : B → U)
 ( is-isoinner-P : is-isoinner-family B P)
  : is-inner-family B P
  := (
      ( is-segal-is-rezk B (first (first is-isoinner-P))
      , ( is-segal-is-rezk (total-type B P) (second (first is-isoinner-P))))
     , ( \ b → (is-segal-is-rezk (P b) ((second is-isoinner-P) b))))
```


## Dependent composition

In an inner family, we can dependently compose arrows. To make this precise,
some coherence seems to be needed going through the axiom of choice for
extension types.

We first record instances of the axiom of choice for dependent 1- and
2-dimensional hom types.

The axiom of choice and its inverse map for dependent homs:

```rzk
#def axiom-choice-dhom
  ( B : U)
  ( a b : B)
  ( P : B → U)
  ( x : P a)
  ( y : P b)
  : Equiv
    ( hom (total-type B P) (a , x) (b , y))
    ( Σ ( u' : hom B a b)
      , ( dhom B a b u' P x y))
  :=
  ( axiom-choice
    2
    Δ¹
    ∂Δ¹
    ( \ t → B)
    ( \ t → \ c → (P c))
    ( \ t → recOR(t ≡ 0₂ ↦ a , t ≡ 1₂ ↦ b))
    ( \ t → recOR(t ≡ 0₂ ↦ x , t ≡ 1₂ ↦ y)))

#def inv-axiom-choice-dhom
  ( B : U)
  ( a b : B)
  ( P : B → U)
  ( x : P a)
  ( y : P b)
  : Equiv
    ( Σ ( u' : hom B a b)
      , ( dhom B a b u' P x y)
    )
    ( hom (total-type B P) (a , x) (b , y))
  :=
  ( inv-equiv
    ( hom (total-type B P) (a , x) (b , y))
    ( Σ ( u' : hom B a b)
      , ( dhom B a b u' P x y))
    ( axiom-choice-dhom B a b P x y))

```

The axiom of choice for dependent 2-simplices:

```rzk

#def axiom-choice-hom2
  ( B : U)
  ( a b c : B)
  ( u : hom B a b)
  ( v : hom B b c)
  ( w : hom B a c)
  ( P : B → U)
  ( x : P a)
  ( y : P b)
  ( z : P c)
  ( f : dhom B a b u P x y)
  ( g : dhom B b c v P y z)
  ( h : dhom B a c w P x z)
  : Equiv
    ( hom2 (total-type B P)
      ( a , x) (b , y) (c , z)
      ( \ t → (u t , f t))
      ( \ t → (v t , g t))
      ( \ t → (w t , h t)))
    ( Σ ( α : hom2 B a b c u v w)
      , ( dhom2 B a b c u v w α P x y z f g h))
  :=
  ( axiom-choice
    ( 2 × 2)
    Δ²
    ∂Δ²
    ( \ (t , s) → B)
    ( \ (t , s) → \ k → (P k))
    ( \ (t , s) → recOR(s ≡ 0₂ ↦ u t , t ≡ 1₂ ↦ v s , s ≡ t ↦ w s))
    ( \ (t , s) → recOR(s ≡ 0₂ ↦ f t , t ≡ 1₂ ↦ g s , s ≡ t ↦ h s)))
```

We now capture composition of morphisms in the total type of an inner family:

```rzk
#def comp-total-type-is-inner
  ( B : U)
  ( a b c : B)
  ( u : hom B a b)
  ( v : hom B b c)
  ( P : B → U)
  ( is-segal-B : is-segal B)
  ( is-segal-total-P : is-segal (total-type B P))
  ( x : P a)
  ( y : P b)
  ( z : P c)
  ( f : dhom B a b u P x y)
  ( g : dhom B b c v P y z)
  : hom (total-type B P) (a , x) (c , z)
  := ((first (inv-axiom-choice-dhom B a c P x z))
      (
       ( first (axiom-choice-dhom B a c P x z))
       ( comp-is-segal
          ( total-type B P)
          is-segal-total-P (a , x) (b , y) (c , z)
          ( ( first (inv-axiom-choice-dhom B a b P x y))
            ( ( \ t → u t , \ t → f t)))
          ( ( first (inv-axiom-choice-dhom B b c P y z))
            ( ( \ t → v t , \ t → g t))))))
```

For dependent composition, we prove coherence first for the arrows in the base,
then for dependent arrows.

The following functions will be helpful along the way:

```rzk
#def proj-base-dhom
  ( B : U)
  ( a b : B)
  ( u : hom B a b)
  ( P : B → U)
  ( x : P a)
  ( y : P b)
  ( f : dhom B a b u P x y)
  : ( hom B a b)
  := (first
        ( ( first (axiom-choice-dhom B a b P x y))
        ( ( \ t → (u t , f t)))))

#def comp2-total-type-is-inner
  ( B : U)
  ( a b c : B)
  ( u : hom B a b)
  ( v : hom B b c)
  ( P : B → U)
  ( is-segal-B : is-segal B)
  ( is-segal-total-P : is-segal (total-type B P))
  ( x : P a)
  ( y : P b)
  ( z : P c)
  ( f : dhom B a b u P x y)
  ( g : dhom B b c v P y z)
  : hom2 (total-type B P) (a , x) (b , y) (c , z)
    ( ( first (inv-axiom-choice-dhom B a b P x y))((\ t → u t , \ t → f t)))
    ( ( first (inv-axiom-choice-dhom B b c P y z))((\ t → v t , \ t → g t)))
    ( comp-total-type-is-inner B a b c u v P is-segal-B is-segal-total-P x y z f g)
  := (witness-comp-is-segal (total-type B P) is-segal-total-P  (a , x) (b , y) (c , z)
      ( ( first (inv-axiom-choice-dhom B a b P x y))((\ t → u t , \ t → f t)))
      ( ( first (inv-axiom-choice-dhom B b c P y z))((\ t → v t , \ t → g t))))

#def hom2-base-hom2-total-is-inner
  ( B : U)
  ( a b c : B)
  ( u : hom B a b)
  ( v : hom B b c)
  ( P : B → U)
  ( is-segal-B : is-segal B)
  ( is-segal-total-P : is-segal (total-type B P))
  ( x : P a)
  ( y : P b)
  ( z : P c)
  ( f : dhom B a b u P x y)
  ( g : dhom B b c v P y z)
  : hom2 B a b c u v
    ( first ((first (axiom-choice-dhom B a c P x z))
    ( comp-total-type-is-inner B a b c u v P is-segal-B is-segal-total-P x y z f g)))
  :=
    ( ap-hom2
    ( total-type B P)
    B
    ( projection-total-type B P)
    ( a , x) (b , y) (c , z)
    ( ( first (inv-axiom-choice-dhom B a b P x y))((\ t → u t , \ t → f t)))
    ( ( first (inv-axiom-choice-dhom B b c P y z))((\ t → v t , \ t → g t)))
    ( comp-total-type-is-inner B a b c u v P is-segal-B is-segal-total-P x y z f g)
    ( comp2-total-type-is-inner B a b c u v P is-segal-B is-segal-total-P x y z f g)
    )
```

Now we give the coherence proof that the two possible candidates for dependent
composition are identified:

```rzk
#def coherence-comp-is-inner
  ( B : U)
  ( a b c : B)
  ( u : hom B a b)
  ( v : hom B b c)
  ( P : B → U)
  ( is-segal-B : is-segal B)
  ( is-segal-total-P : is-segal (total-type B P))
  ( x : P a)
  ( y : P b)
  ( z : P c)
  ( f : dhom B a b u P x y)
  ( g : dhom B b c v P y z)
  : ( comp-is-segal B is-segal-B a b c u v)
    = ( first ((first (axiom-choice-dhom B a c P x z))
    ( comp-total-type-is-inner B a b c u v P is-segal-B is-segal-total-P x y z f g)
  )
  )
  :=
    ( uniqueness-comp-is-segal B is-segal-B a b c u v
     ( first ((first (axiom-choice-dhom B a c P x z))
      ( comp-total-type-is-inner B a b c u v P is-segal-B is-segal-total-P x y z f g)
      )
    )
    ( hom2-base-hom2-total-is-inner B a b c u v P is-segal-B is-segal-total-P x y z f g)
    )
```

This now gives rise to a dependent composition operation:

```rzk
#def proj2-comp-total-type-is-inner
  ( B : U)
  ( a b c : B)
  ( u : hom B a b)
  ( v : hom B b c)
  ( P : B → U)
  ( is-segal-B : is-segal B)
  ( is-segal-total-P : is-segal (total-type B P))
  ( x : P a)
  ( y : P b)
  ( z : P c)
  ( f : dhom B a b u P x y)
  ( g : dhom B b c v P y z)
  : dhom B a c (first ((first (axiom-choice-dhom B a c P x z))
    ( comp-total-type-is-inner B a b c u v P is-segal-B is-segal-total-P x y z f g)))
  P x z
  :=
  ( second ((first (axiom-choice-dhom B a c P x z))
    ( comp-total-type-is-inner B a b c u v P is-segal-B is-segal-total-P x y z f g)))
```

```rzk
#def dep-comp-is-inner
  ( B : U)
  ( a b c : B)
  ( u : hom B a b)
  ( v : hom B b c)
  ( P : B → U)
  ( is-segal-B : is-segal B)
  ( is-segal-total-P : is-segal (total-type B P))
  ( x : P a)
  ( y : P b)
  ( z : P c)
  ( f : dhom B a b u P x y)
  ( g : dhom B b c v P y z)
  : dhom B a c (comp-is-segal B is-segal-B a b c u v) P x z
  := (transport (hom B a c) (\ w → dhom B a c w P x z)
     ( first ((first (axiom-choice-dhom B a c P x z))
     ( comp-total-type-is-inner B a b c u v P is-segal-B is-segal-total-P x y z f g)))
     ( comp-is-segal B is-segal-B a b c u v)
      ( rev (hom B a c)
        ( comp-is-segal B is-segal-B a b c u v)
        ( first ((first (axiom-choice-dhom B a c P x z))
        ( comp-total-type-is-inner B a b c u v P is-segal-B is-segal-total-P x y z f g)))
        ( coherence-comp-is-inner B a b c u v P is-segal-B is-segal-total-P x y z f g)
      )
     ( proj2-comp-total-type-is-inner B a b c u v P is-segal-B is-segal-total-P
       x y z f g)
    )
```

## Vertical morphisms

```rzk
#def vert-dhom
    ( B : U)
    ( b b' : B)
    ( P : B → U)
    ( is-inner-family-P : is-inner-family B P)
    ( e : P b)
    ( e' : P b')
  : U
  := Σ (u : Iso B (is-segal-base-is-inner B P is-inner-family-P) b b') , (dhom B b b' (first u) P e e')
```




```rzk
#def vert-Iso
    ( B : U)
    ( b b' : B)
    ( P : B → U)
    ( is-inner-family-P : is-inner-family B P)
    ( e : P b)
    ( e' : P b')
  : U
  := Σ (u : Iso B (is-segal-base-is-inner B P is-inner-family-P) b b') , (dhom B b b' (first u) P e e')
```
