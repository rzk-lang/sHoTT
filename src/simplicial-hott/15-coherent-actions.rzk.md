# Cocartesian families

This is a formalization of part of the theory of coherent actions on inner
families as developed in [Rob Schellingerhout (2026), Master's thesis, §5](https://studenttheses.uu.nl/items/6b387401-50f1-4463-836a-9ee8c138fec6).

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


## Clamping morphisms

```rzk title="S26, Definition 5.1.2"
#section clamping

#variable B : U


#def clamp (f : Δ¹ → B) ((u , l) : Δ²)
  : hom B (f l) (f u)
  :=
  \ t →
    recOR (t ≤ l ↦ f l , l ≤ t ↦
      recOR (u ≤ t ↦ f u , t ≤ u ↦ f t))

#def clamp-above
  ( f : Δ¹ → B)
  ( t : Δ¹)
  : hom B (f 0₂) (f t)
  := clamp f (t , 0₂)

#def clamp-below
  ( f : Δ¹ → B)
  ( t : Δ¹)
  : hom B (f t) (f 1₂)
  := clamp f (1₂ , t)

#def clamp-commutes
  ( f : Δ¹ → B)
  ( t : Δ¹)
  : hom2 B (f 0₂) (f t) (f 1₂) (clamp-above f t) (clamp-below f t) f
  := \ (x , y) → clamp f (x , y) t

#variable E : B → U

#def dclamp
  ( f : Δ¹ → B)
  ( g : (t : Δ¹) → E (f t))
  ( ( u , l) : Δ²)
  : dhom B (f l) (f u) (clamp f (u , l)) E (g l) (g u)
  :=
  \ t →
    recOR (t ≤ l ↦ g l , l ≤ t ↦
      recOR (u ≤ t ↦ g u , t ≤ u ↦ g t))

#def dclamp-above
  ( f : Δ¹ → B)
  ( g : (t : Δ¹) → E (f t))
  ( t : Δ¹)
  : dhom B (f 0₂) (f t) (clamp-above f t) E (g 0₂) (g t)
  := dclamp f g (t , 0₂)

#def dclamp-below
  ( f : Δ¹ → B)
  ( g : (t : Δ¹) → E (f t))
  ( t : Δ¹)
  : dhom B (f t) (f 1₂) (clamp-below f t) E (g t) (g 1₂)
  := dclamp f g (1₂ , t)

#end clamping
```

## Horizontal morphisms in a triangle
```rzk

#def hor-hom-hom2
  ( B : U)
  ( x y z : B)
  ( f : hom B x y)
  ( g : hom B y z)
  ( h : hom B x z)
  ( σ : hom2 B x y z f g h)
  ( t : Δ¹)
  : hom B (h t) (g t)
  :=
  \ s →
    recOR (
      s ≤ t ↦ h t
      , t ≤ s ↦ σ (s , t)
    )

```



## Lifts from transport

```rzk

#section lift-action

#variable B : U
#variable E : B → U
#variable action : (x y : B) → hom B x y → E x → E y
```

### Lifts of edges

Given a morphism $f : x \to y$ in the base and a start point $e : E(x)$ we can
construct a morphism $id_* e \to f_* e$ laying over it.

```rzk title="S26, Remark 5.1.2"

#def lift-action
  ( x y : B)
  ( f : hom B x y)
  ( e : E x)
  : dhom B x y f E (action x x (id-hom B x) e) (action x y f e)
  := \ t → action x (f t) (clamp-above B f t) e

```

### Lifts of triangles

Given a triangle `hom2 B x y z f g h` in the base and a morphism over `h`,
we construct a morphism over `g` that will be the inverse to postcomposition
with the lift over `f`.

```rzk
#def inv-comp-lift-action uses (action)
  ( x y z : B)
  ( f : hom B x y)
  ( g : hom B y z)
  ( h : hom B x z)
  ( σ : hom2 B x y z f g h)
  ( x' : E x)
  ( z' : E z)
  ( h' : dhom B x z h E x' z')
  : dhom B y z g E
    ( action x y f x')
    ( action z z (id-hom B z) z')
  := \ t → action (h t) (g t) (hor-hom-hom2 B x y z f g h σ t) (h' t)
```

We can lift the entire triangle to a dependent triangle, which will witness
the right inverse law.

```rzk

#def action-id-dhom
  ( x y : B)
  ( f : hom B x y)
  ( x' : E x)
  ( y' : E y)
  ( f' : dhom B x y f E x' y')
  : dhom B x y f E
    ( action x x (id-hom B x) x')
    ( action y y (id-hom B y) y')
  := \ t → action (f t) (f t) (id-hom B (f t)) (f' t)

#def lift-2-action uses (action)
  ( x y z : B)
  ( f : hom B x y)
  ( g : hom B y z)
  ( h : hom B x z)
  ( σ : hom2 B x y z f g h)
  ( x' : E x)
  ( z' : E z)
  ( h' : dhom B x z h E x' z')
  : dhom2 B x y z f g h σ E
    ( action x x (id-hom B x) x')
    ( action x y f x')
    ( action z z (id-hom B z) z')
    ( lift-action x y f x')
    ( inv-comp-lift-action x y z f g h σ x' z' h')
    ( action-id-dhom x z h x' z' h')
  :=
  \ (s , t) →
    lift-action
      ( h t) (g t) (hor-hom-hom2 B x y z f g h σ t)
      ( h' t) s

```

### The coherence morphism

There is always a dependent morphism `f_* id_* e -> id_* f_* e` in the fiber
over the codomain of `f`, which we call the coherence morphism.

```rzk

#def coherence-morphism-action
  ( x y : B)
  ( f : hom B x y)
  ( e : E x)
  : hom (E y)
    ( action x y f (action x x (id-hom B x) e))
    ( action y y (id-hom B y) (action x y f e))
  :=
  \ t →
    ( action (f t) y (clamp-below B f t) (action x (f t) (clamp-above B f t) e))

```

### Pushforward of dependent triangles

Any dependent triangle, with bottom edge being the lift induced by the action,
can be pushed forward to a triangle involving, the inverse to composition with
the lift and the coherence morphism.

```rzk

#def action-dhom2-action
  ( x y z : B)
  ( f : hom B x y)
  ( g : hom B y z)
  ( h : hom B x z)
  ( σ : hom2 B x y z f g h)
  ( x' : E x)
  ( z' : E z)
  ( g' : dhom B y z g E (action x y f x') z')
  ( h' : dhom B x z h E (action x x (id-hom B x) x') z')
  ( σ' : dhom2 B x y z f g h σ E
    ( action x x (id-hom B x) x')
    ( action x y f x')
    z'
    ( lift-action x y f x')
    g'
    h')
  : dhom2 B y y z (id-hom B y) g g (id-comp-witness B y z g) E
    ( action x y f (action x x (id-hom B x) x'))
    ( action y y (id-hom B y) (action x y f x'))
    ( action z z (id-hom B z) z')
    ( coherence-morphism-action x y f x')
    ( action-id-dhom y z g (action x y f x') z' g')
    ( inv-comp-lift-action x y z f g h σ (action x x (id-hom B x) x') z' h')
  :=
  \ (t , s) →
    action (σ (t , s)) (g s)
      ( clamp-below B (hor-hom-hom2 B x y z f g h σ s) t)
      ( σ' (t , s))

```

## Composing with lifts

Now we will assume that our family is inner.

```rzk

#variable is-inner-E
  : is-inner-family B E

```

If `E` is inner we can compose with the lift. We would like to show that this
map is an equivalence.

```rzk

#def comp-lift-action
  ( x y z : B)
  ( f : hom B x y)
  ( g : hom B y z)
  ( h : hom B x z)
  ( σ : hom2 B x y z f g h)
  ( x' : E x)
  ( z' : E z)
  : dhom B y z g E (action x y f x') z'
  → dhom B x z h E (action x x (id-hom B x) x') z'
  :=
  \ g' → comp-over-is-inner-family B E is-inner-E
    x y z f g h σ
    ( action x x (id-hom B x) x')
    ( action x y f x') z'
    ( lift-action x y f x')
    ( g')

#def fill-lift-action
  ( x y z : B)
  ( f : hom B x y)
  ( g : hom B y z)
  ( h : hom B x z)
  ( σ : hom2 B x y z f g h)
  ( x' : E x)
  ( z' : E z)
  ( g' : dhom B y z g E (action x y f x') z')
  : dhom2 B x y z f g h σ E (action x x (id-hom B x) x') (action x y f x') z'
    ( lift-action x y f x')
    ( g')
    ( comp-lift-action x y z f g h σ x' z' g')
  :=
  fill-over-is-inner-family' B E is-inner-E
    x y z f g h σ
    ( action x x (id-hom B x) x')
    ( action x y f x') z'
    ( lift-action x y f x')
    ( g')

```

We will do this by considering the map on total types.

```rzk

#def tot-comp-lift-action uses (is-inner-E)
  ( x y z : B)
  ( f : hom B x y)
  ( g : hom B y z)
  ( h : hom B x z)
  ( σ : hom2 B x y z f g h)
  :
  ( Σ ( x' : E x) , darr-from B g E (action x y f x'))
  → ( ( t : Δ¹) → E (h t))
  :=
  \ (x' , g') → comp-lift-action x y z f g h σ x' (g' 1₂) (\ t → g' t)


#def inv-tot-comp-lift-action
  ( x y z : B)
  ( f : hom B x y)
  ( g : hom B y z)
  ( h : hom B x z)
  ( σ : hom2 B x y z f g h)
  :
  ( ( t : Δ¹) → E (h t))
  → ( Σ ( x' : E x) , darr-from B g E (action x y f x'))
  :=
  \ h' → (h' 0₂ , inv-comp-lift-action x y z f g h σ (h' 0₂) (h' 1₂) h')

```

The lift over our triangle almost witnesses the right inverse law.

```rzk

#def comp-lift-action-inv-lift-action-is-action-id-dhom-action
  ( x y z : B)
  ( f : hom B x y)
  ( g : hom B y z)
  ( h : hom B x z)
  ( σ : hom2 B x y z f g h)
  ( x' : E x)
  ( z' : E z)
  ( h' : dhom B x z h E x' z')
  : comp-lift-action x y z f g h σ x' (action z z (id-hom B z) z')
    ( inv-comp-lift-action x y z f g h σ x' z' h')
    = action-id-dhom x z h x' z' h'
  :=
  unqiue-comp-over-is-inner-family B E is-inner-E
    x y z f g h σ
    ( action x x (id-hom B x) x')
    ( action x y f x')
    ( action z z (id-hom B z) z')
    ( lift-action x y f x')
    ( inv-comp-lift-action x y z f g h σ x' z' h')
    ( action-id-dhom x z h x' z' h')
    ( lift-2-action x y z f g h σ x' z' h')

```

## Unital actions

For the next part of the argument we need to assume that the action is unital.

```rzk
#variable is-unital-action :
  ( x : B)
  → ( e : E x)
  → action x x (id-hom B x) e = e
```

### The right inverse law

Now we can show that our total map has a right inverse.

```rzk

#def is-retraction-tot-comp-lift-action uses (is-inner-E action)
  ( x y z : B)
  ( f : hom B x y)
  ( g : hom B y z)
  ( h : hom B x z)
  ( σ : hom2 B x y z f g h)
  ( x' : E x)
  ( z' : E z)
  ( h' : dhom B x z h E x' z')
  : tot-comp-lift-action x y z f g h σ
    ( inv-tot-comp-lift-action x y z f g h σ h')
    = h'
  :=
  concat ((t : Δ¹) → E (h t))
    ( tot-comp-lift-action x y z f g h σ
      ( inv-tot-comp-lift-action x y z f g h σ h'))
    ( action-id-dhom x z h x' z' (h'))
    h'
    ( ap
      ( dhom B x z h E (action x x (id-hom B x) x') (action z z (id-hom B z) z'))
      ( ( t : Δ¹) → E (h t))
      ( comp-lift-action x y z f g h σ x' (action z z (id-hom B z) z')
        ( inv-comp-lift-action x y z f g h σ x' z' h'))
      ( action-id-dhom x z h x' z' h')
      ( \ h' → \ t → h' t)
      ( comp-lift-action-inv-lift-action-is-action-id-dhom-action
        x y z f g h σ x' z' h'))
    ( naiveextext-extext extext
      2
      Δ¹
      ( \ _ → BOT)
      ( \ t → E (h t))
      ( \ _ → recBOT)
      ( action-id-dhom x z h x' z' (h'))
      h'
      ( \ t → is-unital-action (h t) (h' t)))

```

## Coherent actions

For the left inverse we will need to assume that our action is coherent in a
suitable sense. More specifically, we need to assume that the action preserves
the composites of `clamp-below f t` and `clamp-above f t`. In addition we need
some coherences, relating these compositors to the unitors.

```rzk title="S26, Remark 5.1.4"

#def local-composition-law-action
  ( x y : B)
  ( f : hom B x y)
  ( e : E x)
  : U
  :=
  ( t : Δ¹)
  → action (f t) y (clamp-below B f t) (action x (f t) (clamp-above B f t) e)
    = action x y f e

#def left-coherence-local-composition-law-unital-action
  ( x y : B)
  ( f : hom B x y)
  ( e : E x)
  ( compositor : local-composition-law-action x y f e)
  : U
  :=
  ( compositor 0₂)
    = ( ap (E x) (E y)
      ( action x x (id-hom B x) e)
      ( e)
      ( action x y f)
      ( is-unital-action x e))

#def right-coherence-local-composition-law-unital-action
  ( x y : B)
  ( f : hom B x y)
  ( e : E x)
  ( compositor : local-composition-law-action x y f e)
  : U
  := (compositor 1₂) = is-unital-action y (action x y f e)


#def is-coherent-over-hom-unital-action uses (E action is-unital-action)
  ( x y : B)
  ( f : hom B x y)
  ( e : E x)
  : U
  :=
  Σ ( compositor : local-composition-law-action x y f e)
  , product
    ( left-coherence-local-composition-law-unital-action x y f e compositor)
    ( right-coherence-local-composition-law-unital-action x y f e compositor)

#def is-coherent-unital-action uses (E action is-unital-action)
  : U
  :=
  ( x y : B) → (f : hom B x y) → (e : E x)
  → is-coherent-over-hom-unital-action x y f e

```

### Alternative characterization of coherent actions

There is an alternative characterization of the coherence data in terms of the
coherence morphism.

```rzk

#def zig-zag-morphism-unital-action
  ( x y : B)
  ( f : hom B x y)
  ( e : E x)
  : hom (E y)
    ( action x y f (action x x (id-hom B x) e))
    ( action y y (id-hom B y) (action x y f e))
  :=
  hom-eq (E y)
    ( action x y f (action x x (id-hom B x) e))
    ( action y y (id-hom B y) (action x y f e))
    ( zig-zag-concat (E y)
      ( action x y f (action x x (id-hom B x) e))
      ( action x y f e)
      ( action y y (id-hom B y) (action x y f e))
      ( ap
        ( E x)
        ( E y)
        ( action x x (id-hom B x) e)
        ( e)
        ( action x y f)
        ( is-unital-action x e))
      ( is-unital-action y (action x y f e)))

```

The zig-zag morphism applied to the identity is the identity.

```rzk

#def eq-zig-zag-morphism-id-id-unital-action uses (is-unital-action)
  ( x : B)
  ( e : E x)
  : zig-zag-morphism-unital-action x x (id-hom B x) e
    = id-hom (E x) (action x x (id-hom B x) (action x x (id-hom B x) e))
  :=
  ap
    ( ( action x x (id-hom B x) (action x x (id-hom B x) e))
      = ( action x x (id-hom B x) (action x x (id-hom B x) e)))
    ( hom (E x)
      ( action x x (id-hom B x) (action x x (id-hom B x) e))
      ( action x x (id-hom B x) (action x x (id-hom B x) e)))
    ( zig-zag-concat (E x)
      ( action x x (id-hom B x) (action x x (id-hom B x) e))
      ( action x x (id-hom B x) e)
      ( action x x (id-hom B x) (action x x (id-hom B x) e))
      ( ap
        ( E x)
        ( E x)
        ( action x x (id-hom B x) e)
        ( e)
        ( action x x (id-hom B x))
        ( is-unital-action x e))
      ( is-unital-action x (action x x (id-hom B x) e)))
    ( refl)
    ( hom-eq (E x)
      ( action x x (id-hom B x) (action x x (id-hom B x) e))
      ( action x x (id-hom B x) (action x x (id-hom B x) e)))
    ( eq-zig-zag-homotopy-id-refl funext
      ( E x)
      ( action x x (id-hom B x))
      ( is-unital-action x)
      ( e))
```

```rzk title="S26, Definition 5.1.5"

#def is-coherent-over-hom-unital-action' uses (is-unital-action)
  ( x y : B)
  ( f : hom B x y)
  ( e : E x)
  : U
  :=
  ( coherence-morphism-action x y f e) = (zig-zag-morphism-unital-action x y f e)

#def is-coherent-unital-action' uses (action is-unital-action)
  : U
  :=
  ( x y : B) → (f : hom B x y) → (e : E x)
  → is-coherent-over-hom-unital-action' x y f e

```

These characterizations are equivalent.

```rzk title="S26, Remark 5.1.4"

#def extension-type-is-coherent-over-hom-unital-action
  ( x y : B)
  ( f : hom B x y)
  ( e : E x)
  : U
  :=
  extension-type
      2
      Δ¹
      ∂Δ¹
      ( \ t → coherence-morphism-action x y f e t =_{E y} action x y f e)
      ( \ t → recOR (
        t ≡ 0₂ ↦
          ap (E x) (E y)
            ( action x x (id-hom B x) e)
            ( e)
            ( action x y f)
            ( is-unital-action x e)
      , t ≡ 1₂ ↦ is-unital-action y (action x y f e)))

#def pointwise-homotopy-extension-type-is-coherent-over-hom-unital-action
  ( x y : B)
  ( f : hom B x y)
  ( e : E x)
  : U
  :=
  pointwise-homotopy-extension-type
      2
      Δ¹
      ∂Δ¹
      ( \ t → coherence-morphism-action x y f e t =_{E y} action x y f e)
      ( \ t → recOR (
        t ≡ 0₂ ↦
          ap (E x) (E y)
            ( action x x (id-hom B x) e)
            ( e)
            ( action x y f)
            ( is-unital-action x e)
      , t ≡ 1₂ ↦ is-unital-action y (action x y f e)))

#def equiv-is-coherent-unital-action-over-is-coherent-unital-action-over'
  ( x y : B)
  ( f : hom B x y)
  ( e : E x)
  : Equiv
    ( is-coherent-over-hom-unital-action x y f e)
    ( is-coherent-over-hom-unital-action' x y f e)
  :=
  equiv-triple-comp
    ( is-coherent-over-hom-unital-action x y f e)
    ( pointwise-homotopy-extension-type-is-coherent-over-hom-unital-action
      x y f e)
    ( extension-type-is-coherent-over-hom-unital-action x y f e)
    ( is-coherent-over-hom-unital-action' x y f e)
    ( equiv-has-inverse
      ( is-coherent-over-hom-unital-action x y f e)
      ( pointwise-homotopy-extension-type-is-coherent-over-hom-unital-action
        x y f e)
      ( \ (compositor , (left-coh , right-coh)) →
        ( compositor
        , \ t → recOR (
          t ≡ 0₂ ↦ left-coh
        , t ≡ 1₂ ↦ right-coh
        )))
      ( \ (compositor , coh) → (compositor , (coh 0₂ , coh 1₂)))
      ( \ _ → refl)
      ( \ _ → refl))
    ( inv-equiv
      ( extension-type-is-coherent-over-hom-unital-action x y f e)
      ( pointwise-homotopy-extension-type-is-coherent-over-hom-unital-action
        x y f e)
      ( extension-type-pointwise-weakening extext
        2
        Δ¹
        ∂Δ¹
        ( \ t → coherence-morphism-action x y f e t =_{E y} action x y f e)
        ( \ t → recOR (
          t ≡ 0₂ ↦
            ap (E x) (E y)
              ( action x x (id-hom B x) e)
              ( e)
              ( action x y f)
              ( is-unital-action x e)
        , t ≡ 1₂ ↦ is-unital-action y (action x y f e)))))
    ( inv-equiv
      ( is-coherent-over-hom-unital-action' x y f e)
      ( extension-type-is-coherent-over-hom-unital-action x y f e)
      ( equiv-eq-hom-eq-zig-zag-concat extext
        ( E y)
        ( action x y f (action x x (id-hom B x) e))
        ( action x y f e)
        ( action y y (id-hom B y) (action x y f e))
        ( ap (E x) (E y)
          ( action x x (id-hom B x) e)
          ( e)
          ( action x y f)
          ( is-unital-action x e))
        ( is-unital-action y (action x y f e))
        ( coherence-morphism-action x y f e)))


#def equiv-is-coherent-unital-action-is-coherent-unital-action'
  uses (extext action is-unital-action)
  : Equiv is-coherent-unital-action is-coherent-unital-action'
  :=
  equiv-function-equiv-family funext
    B
    ( \ x → (y : B) → (f : hom B x y) → (e : E x)
    → is-coherent-over-hom-unital-action x y f e)
    ( \ x → (y : B) → (f : hom B x y) → (e : E x)
    → is-coherent-over-hom-unital-action' x y f e)
    ( \ x →
      equiv-function-equiv-family funext
        B
        ( \ y → (f : hom B x y) → (e : E x)
        → is-coherent-over-hom-unital-action x y f e)
        ( \ y → (f : hom B x y) → (e : E x)
        → is-coherent-over-hom-unital-action' x y f e)
        ( \ y →
          equiv-function-equiv-family funext
            ( hom B x y)
            ( \ f → (e : E x)
            → is-coherent-over-hom-unital-action x y f e)
            ( \ f → (e : E x)
            → is-coherent-over-hom-unital-action' x y f e)
            ( \ f →
              equiv-function-equiv-family funext
              ( E x)
              ( is-coherent-over-hom-unital-action x y f)
              ( is-coherent-over-hom-unital-action' x y f)
              ( \ e →
                equiv-is-coherent-unital-action-over-is-coherent-unital-action-over'
                  x y f e))))

#def is-coherent'-is-coherent-unital-action
  uses (funext extext B E action is-unital-action)
  : is-coherent-unital-action → is-coherent-unital-action'
  :=
  first equiv-is-coherent-unital-action-is-coherent-unital-action'

#def is-coherent-is-coherent'-unital-action
  uses (funext extext B E action is-unital-action)
  : is-coherent-unital-action' → is-coherent-unital-action
  :=
  first (inv-equiv
    is-coherent-unital-action
    is-coherent-unital-action'
    equiv-is-coherent-unital-action-is-coherent-unital-action')

```

From now on we will assume that the action is coherent.

```rzk

#assume is-coherent-unital-action-action : is-coherent-unital-action'

```

We can use this to change the bottom edge of our pushed forward triangle
`action-dhom2-action`.


```rzk

#def degen-edge-action-dhom2-action uses (is-unital-action)
  ( x y z : B)
  ( f : hom B x y)
  ( g : hom B y z)
  ( h : hom B x z)
  ( σ : hom2 B x y z f g h)
  ( x' : E x)
  ( z' : E z)
  ( g' : dhom B y z g E (action x y f x') z')
  ( h' : dhom B x z h E (action x x (id-hom B x) x') z')
  ( σ' : dhom2 B x y z f g h σ E
    ( action x x (id-hom B x) x')
    ( action x y f x')
    z'
    ( lift-action x y f x')
    g'
    h')
  : dhom2 B y y z (id-hom B y) g g (id-comp-witness B y z g) E
    ( action x y f (action x x (id-hom B x) x'))
    ( action y y (id-hom B y) (action x y f x'))
    ( action z z (id-hom B z) z')
    ( zig-zag-morphism-unital-action x y f x')
    ( action-id-dhom y z g (action x y f x') z' g')
    ( inv-comp-lift-action x y z f g h σ (action x x (id-hom B x) x') z' h')
  :=
  transport
    ( hom (E y)
      ( action x y f (action x x (id-hom B x) x'))
      ( action y y (id-hom B y) (action x y f x')))
    ( \ c →
      dhom2 B y y z (id-hom B y) g g (id-comp-witness B y z g) E
        ( action x y f (action x x (id-hom B x) x'))
        ( action y y (id-hom B y) (action x y f x'))
        ( action z z (id-hom B z) z')
        ( c)
        ( action-id-dhom y z g (action x y f x') z' g')
        ( inv-comp-lift-action x y z f g h σ (action x x (id-hom B x) x') z' h'))
    ( coherence-morphism-action x y f x')
    ( zig-zag-morphism-unital-action x y f x')
    ( is-coherent-unital-action-action x y f x')
    ( action-dhom2-action x y z f g h σ x' z' g' h' σ')

```

### Left inverse law

This triangle witnesses the left inverse law for our total map
`tot-comp-lift-action`.

```rzk

#def is-section-tot-comp-lift-action
  uses (is-inner-E is-coherent-unital-action-action)
  ( x y z : B)
  ( f : hom B x y)
  ( g : hom B y z)
  ( h : hom B x z)
  ( σ : hom2 B x y z f g h)
  : ( g' : Σ (x' : E x) , darr-from B g E (action x y f x'))
  → ( inv-tot-comp-lift-action x y z f g h σ
    ( tot-comp-lift-action x y z f g h σ g'))
    = g'
  :=
  \ (x' , g') →
    eq-pullback-dom-projection-dhom2-ext-homotopy-inner-family
      extext B E is-inner-E
      x y z g
      ( action x x (id-hom B x) x')
      ( x')
      ( g' 1₂)
      ( is-unital-action x x')
      ( action x y f)
      ( action-id-dhom y z g (action x y f x') (g' 1₂) (\ t → g' t))
      ( \ t → g' t)
      ( \ t → is-unital-action (g t) (g' t))
      ( inv-comp-lift-action x y z f g h σ
        ( action x x (id-hom B x) x')
        ( g' 1₂)
        ( comp-lift-action x y z f g h σ x' (g' 1₂) (\ t → g' t)))
      ( degen-edge-action-dhom2-action x y z f g h σ x' (g' 1₂)
        ( \ t → g' t)
        ( comp-lift-action x y z f g h σ x' (g' 1₂) (\ t → g' t))
        ( fill-lift-action x y z f g h σ x' (g' 1₂) (\ t → g' t)))

#def is-equiv-tot-comp-lift-action
  uses (extext is-inner-E is-unital-action is-coherent-unital-action-action)
  ( x y z : B)
  ( f : hom B x y)
  ( g : hom B y z)
  ( h : hom B x z)
  ( σ : hom2 B x y z f g h)
  : is-equiv
    ( Σ ( x' : E x) , darr-from B g E (action x y f x'))
    ( ( t : Δ¹) → E (h t))
    ( tot-comp-lift-action x y z f g h σ)
  :=
  is-equiv-has-inverse
    ( Σ ( x' : E x) , darr-from B g E (action x y f x'))
    ( ( t : Δ¹) → E (h t))
    ( tot-comp-lift-action x y z f g h σ)
    ( inv-tot-comp-lift-action x y z f g h σ
    , ( is-section-tot-comp-lift-action x y z f g h σ
    , ( \ h' →
      is-retraction-tot-comp-lift-action x y z f g h σ (h' 0₂) (h' 1₂) h')))

```

### Cocartesianness

We know now that our total map is an equivalence. Now it remains to prove the
equivalence on fibers and conclude that our family is cocartesian. We will do
this in two steps.

First we show that we obtain an equivalence when one endpoint is fixed.

```rzk

#def comp-lift-darr-from-action uses (is-inner-E)
  ( x y z : B)
  ( f : hom B x y)
  ( g : hom B y z)
  ( h : hom B x z)
  ( σ : hom2 B x y z f g h)
  ( x' : E x)
  : darr-from B g E (action x y f x')
  → darr-from B h E (action x x (id-hom B x) x')
  :=
  \ g' → comp-lift-action x y z f g h σ x' (g' 1₂) (\ t → g' t)


#def is-equiv-action-id
  ( x : B)
  : is-equiv
    ( E x)
    ( E x)
    ( action x x (id-hom B x))
  :=
  is-equiv-has-inverse
    ( E x)
    ( E x)
    ( action x x (id-hom B x))
    ( identity (E x)
    , ( is-unital-action x , is-unital-action x))

#def is-equiv-comp-lift-darr-from-action
  uses (extext is-inner-E is-unital-action is-coherent-unital-action-action)
  ( x y z : B)
  ( f : hom B x y)
  ( g : hom B y z)
  ( h : hom B x z)
  ( σ : hom2 B x y z f g h)
  ( x' : E x)
  : is-equiv
    ( darr-from B g E (action x y f x'))
    ( darr-from B h E (action x x (id-hom B x) x'))
    ( comp-lift-darr-from-action x y z f g h σ x')
  :=
  is-equiv-fiberwise-is-equiv-total
    ( E x)
    ( \ x' → darr-from B g E (action x y f x'))
    ( \ x' → darr-from B h E (action x x (id-hom B x) x'))
    ( \ x' → comp-lift-darr-from-action x y z f g h σ x')
    ( is-equiv-right-factor
      ( Σ ( x' : E x) , darr-from B g E (action x y f x'))
      ( Σ ( x' : E x) , darr-from B h E (action x x (id-hom B x) x'))
      ( ( t : Δ¹) → E (h t))
      ( \ (x' , g') → (x' , comp-lift-darr-from-action x y z f g h σ x' g'))
      ( \ (x' , g') → g')
      ( is-equiv-comp
        ( Σ ( x' : E x) , darr-from B h E (action x x (id-hom B x) x'))
        ( Σ ( x' : E x) , darr-from B h E x')
        ( ( t : Δ¹) → E (h t))
        ( \ (x' , g') → (action x x (id-hom B x) x' , g'))
        ( second (equiv-total-pullback-is-equiv
          ( E x)
          ( E x)
          ( action x x (id-hom B x))
          ( is-equiv-action-id x)
          ( darr-from B h E)))
        ( \ (x' , g') → g')
        ( is-equiv-map-sigma-darr-from-darr B h E))
      ( is-equiv-tot-comp-lift-action x y z f g h σ))
    x'

```

Finally, we show that the other endpoint can also be fixed.

```rzk

#def is-equiv-comp-lift-action
  uses (extext is-inner-E is-unital-action is-coherent-unital-action-action)
  ( x y z : B)
  ( f : hom B x y)
  ( g : hom B y z)
  ( h : hom B x z)
  ( σ : hom2 B x y z f g h)
  ( x' : E x)
  ( z' : E z)
  : is-equiv
    ( dhom B y z g E (action x y f x') z')
    ( dhom B x z h E (action x x (id-hom B x) x') z')
    ( comp-lift-action x y z f g h σ x' z')
  :=
  is-equiv-fiberwise-is-equiv-total
    ( E z)
    ( dhom B y z g E (action x y f x'))
    ( dhom B x z h E (action x x (id-hom B x) x'))
    ( comp-lift-action x y z f g h σ x')
    ( is-equiv-left-factor
      ( darr-from B g E (action x y f x'))
      ( Σ ( z' : E z) , dhom B y z g E (action x y f x') z')
      ( Σ ( z' : E z) , dhom B x z h E (action x x (id-hom B x) x') z')
      ( \ g' → (g' 1₂ , \ t → g' t))
      ( is-equiv-has-inverse
        ( darr-from B g E (action x y f x'))
        ( Σ ( z' : E z) , dhom B y z g E (action x y f x') z')
        ( \ g' → (g' 1₂ , \ t → g' t))
        ( \ (z' , g') → g' , (\ g' → refl , \ g' → refl)))
      ( \ (z' , g') → (z' , comp-lift-action x y z f g h σ x' z' g'))
      ( is-equiv-right-factor
        ( darr-from B g E (action x y f x'))
        ( Σ ( z' : E z) , dhom B x z h E (action x x (id-hom B x) x') z')
        ( darr-from B h E (action x x (id-hom B x) x'))
        ( \ g' → (g' 1₂ , comp-lift-action x y z f g h σ x' (g' 1₂) (\ t → g' t)))
        ( \ (z' , g') → g')
        ( is-equiv-has-inverse
          ( Σ ( z' : E z) , dhom B x z h E (action x x (id-hom B x) x') z')
          ( darr-from B h E (action x x (id-hom B x) x'))
          ( \ (z' , g') → g')
          ( \ g' → (g' 1₂ , \ t → g' t) , (\ g' → refl , \ g' → refl)))
        ( is-equiv-comp-lift-darr-from-action x y z f g h σ x')))
    z'

```

It follows that our lift is indeed a cocartesian morphism.

```rzk

#def is-cocartesian-arrow-lift-action
  uses (extext is-inner-E is-unital-action is-coherent-unital-action-action)
  ( x y : B)
  ( f : hom B x y)
  ( x' : E x)
  : is-cocartesian-arrow B x y f E
    ( action x x (id-hom B x) x')
    ( action x y f x')
    ( lift-action x y f x')
  :=
  is-cocartesian-arrow-is-equiv-comp-over-is-inner B E is-inner-E x y f
    ( action x x (id-hom B x) x')
    ( action x y f x')
    ( lift-action x y f x')
    ( \ z g h σ z' → is-equiv-comp-lift-action x y z f g h σ x' z')

```

```rzk
#end lift-action
```

It follows that all morpshisms have cocartesian lifts.

```rzk title="S26, Theorem 5.1.6"

#def has-cocartesian-lifts-coherent-action' uses (extext)
  ( B : U)
  ( E : B → U)
  ( is-inner-E : is-inner-family B E)
  ( action : (x y : B) → hom B x y → E x → E y)
  ( is-unital-action : (x : B) → (e : E x) → action x x (id-hom B x) e = e)
  ( is-coherent-unital-action-action :
    is-coherent-unital-action' B E action is-unital-action)
  : has-cocartesian-lifts B E
  :=
  \ x y f x' →
    transport
      ( E x)
      ( \ x' →
        Σ ( y' : E y)
      , Σ ( f' : dhom B x y f E x' y')
      , is-cocartesian-arrow B x y f E x' y' f')
      ( action x x (id-hom B x) x')
      x'
      ( is-unital-action x x')
      ( action x y f x'
      , ( lift-action B E action x y f x'
        , is-cocartesian-arrow-lift-action B E
          action
          is-inner-E
          is-unital-action
          is-coherent-unital-action-action
          x y f x'))

#def has-cocartesian-lifts-coherent-action uses (funext extext)
  ( B : U)
  ( E : B → U)
  ( is-inner-E : is-inner-family B E)
  ( action : (x y : B) → hom B x y → E x → E y)
  ( is-unital-action : (x : B) → (e : E x) → action x x (id-hom B x) e = e)
  ( is-coherent-unital-action-action :
    is-coherent-unital-action B E action is-unital-action)
  : has-cocartesian-lifts B E
  :=
  has-cocartesian-lifts-coherent-action'
    B
    E
    is-inner-E
    action
    is-unital-action
    ( is-coherent'-is-coherent-unital-action B E action is-unital-action
      is-coherent-unital-action-action)

#def is-cocartesian-coherent-action' uses (extext)
  ( B : U)
  ( E : B → U)
  ( is-iso-inner-E : is-isoinner-family B E)
  ( action : (x y : B) → hom B x y → E x → E y)
  ( is-unital-action : (x : B) → (e : E x) → action x x (id-hom B x) e = e)
  ( is-coherent-unital-action-action :
    is-coherent-unital-action' B E action is-unital-action)
  : is-cocartesian-family B E
  :=
  ( is-iso-inner-E
  , has-cocartesian-lifts-coherent-action' B E
    ( first (is-iso-inner-E))
    action
    is-unital-action
    is-coherent-unital-action-action)

#def is-cocartesian-coherent-action uses (funext extext)
  ( B : U)
  ( E : B → U)
  ( is-iso-inner-E : is-isoinner-family B E)
  ( action : (x y : B) → hom B x y → E x → E y)
  ( is-unital-action : (x : B) → (e : E x) → action x x (id-hom B x) e = e)
  ( is-coherent-unital-action-action :
    is-coherent-unital-action B E action is-unital-action)
  : is-cocartesian-family B E
  :=
  ( is-iso-inner-E
  , has-cocartesian-lifts-coherent-action B E
    ( first (is-iso-inner-E))
    action
    is-unital-action
    is-coherent-unital-action-action)

```
