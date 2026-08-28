# Orthogonal families

This is a formalization of orthogonal families. A specific instance of
orthogonal families are inner families. These enable dependent composition
needed for cocartesian families.

The previously defined [orthogonal maps](./04-right-orthogonal.rzk.md) are
equivalent to this notion which we also show in this section. The family version
of the term is more useful in light of strict sections and cocartesian families.

We build on
[Buchholtz and Weinberger (2023), Higher Structures 7, §3 & §4](https://doi.org/10.21136/HS.2023.04).

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Prerequisites

- `hott/*` - We require various prerequisites from homotopy type theory, for
  instance the axiom of function extensionality.
- `02-simplicial-type-theory.rzk.md` — We rely on definitions of simplices and
  their subshapes.
- `03-extension-types.rzk.md` — We use the Fubini theorem and extension
  extensionality.
- `05-segal-types.rzk.md` - We make heavy use of the notion of Segal types

```rzk
#assume funext : FunExt
#assume extext : ExtExt
```

## Definition of orthogonal families

We use the defining property given in BW Corollary 3.1.2 for orthogonal
families:

```rzk
#def is-right-orthogonal-family
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( φ : ψ → TOPE)
  ( A : U)
  ( C : A → U)
  : U
  :=
    ( a : ψ → A)
  → ( f : (t : φ) → C (a t))
  → is-contr ((t : ψ) → C (a t) [φ t ↦ f t])
```

```rzk
#def is-right-orthogonal-family-is-prop
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( φ : ψ → TOPE)
  ( A : U)
  ( C : A → U)
  : is-prop (is-right-orthogonal-family I ψ φ A C)
  :=
  is-prop-fiberwise-prop2 funext
  ( ψ → A)
  ( \ a → (t : φ) → C (a t))
  ( \ a f → is-contr ((t : ψ) → C (a t) [φ t ↦ f t]))
  ( \ a f → is-prop-is-contr-itself
    ( weakfunext-funext funext)
    ( ( t : ψ) → C (a t) [φ t ↦ f t]))
```

## Equivalence to `is-right-orthogonal-to-shape`

This notion of orthogonal family is equivalent to the notion of orthogonal map.
We simply need to repackage the data.

The proofs in this section have no grand idea behind them. Writing down the
types, unfolding them it becomes apparent that they are equivalent and only the
equivalence needs to be spelled out.

```rzk
#section has-contr-relative-extension-types-iff-is-right-orthogonal-family

#variable I : CUBE
#variable ψ : I → TOPE
#variable ϕ : ψ → TOPE
#variable A : U
#variable C : A → U

#def has-contr-relative-extension-types-is-right-orthogonal-family
  ( is-right-orthogonal-family-C : is-right-orthogonal-family I ψ ϕ A C)
  : has-contr-relative-extension-types I ψ ϕ
    ( \ _ → total-type A C)
    ( \ _ → A)
    ( \ _ → projection-total-type A C)
  :=
  \ a τ →
  is-contr-equiv-is-contr'
  ( relative-extension-type I ψ ϕ
    ( \ _ → total-type A C)
    ( \ _ → A)
    ( \ _ → projection-total-type A C)
    ( a) (τ))
  ( ( t : ψ) → C (τ t) [ϕ t ↦ second (a t)])
  ( equiv-relative-extension-type-direct-extension extext I ψ ϕ
    ( \ _ → A) (\ _ → C) (a) (τ))
  ( is-right-orthogonal-family-C τ (\ t → second (a t)))

#def is-right-orthogonal-family-has-contr-relative-extension-types
  ( has-contr-rel-ext
    : has-contr-relative-extension-types I ψ ϕ
    ( \ _ → total-type A C)
    ( \ _ → A)
    ( \ _ → projection-total-type A C))
  : is-right-orthogonal-family I ψ ϕ A C
  :=
  \ a f →
  is-contr-equiv-is-contr
  ( relative-extension-type I ψ ϕ
    ( \ _ → total-type A C)
    ( \ _ → A)
    ( \ _ → projection-total-type A C)
    ( \ t → (a t , f t)) (a))
  ( ( t : ψ) → C (a t) [ϕ t ↦ f t])
  ( equiv-relative-extension-type-direct-extension extext I ψ ϕ
    ( \ _ → A) (\ _ → C) (\ t → (a t , f t)) (a))
  ( has-contr-rel-ext (\ t → (a t , f t)) a)

#end has-contr-relative-extension-types-iff-is-right-orthogonal-family
```

```rzk
#section is-right-orthogonal-family-iff-is-right-orthogonal-to-shape

#variable I : CUBE
#variable ψ : I → TOPE
#variable ϕ : ψ → TOPE
#variable A : U
#variable C : A → U

#def is-right-orthogonal-to-shape-is-right-orthogonal-family
  ( is-right-orthogonal-family-C : is-right-orthogonal-family I ψ ϕ A C)
  : is-right-orthogonal-to-shape I ψ ϕ
    ( total-type A C)
    ( A)
    ( projection-total-type A C)
  :=
  is-right-orthogonal-to-shape-has-contr-relative-extension-types extext I ψ ϕ
  ( total-type A C)
  ( A)
  ( projection-total-type A C)
  ( has-contr-relative-extension-types-is-right-orthogonal-family I ψ ϕ A C
    ( is-right-orthogonal-family-C))

#def is-right-orthogonal-family-is-right-orthogonal-to-shape
  ( is-right-orth-C : is-right-orthogonal-to-shape I ψ ϕ
    ( total-type A C)
    ( A)
    ( projection-total-type A C))
  : is-right-orthogonal-family I ψ ϕ A C
  :=
  is-right-orthogonal-family-has-contr-relative-extension-types I ψ ϕ A C
  ( has-contr-relative-extension-types-is-right-orthogonal-to-shape
    ( extext) I ψ ϕ
    ( total-type A C)
    ( A)
    ( projection-total-type A C)
    ( is-right-orth-C))

#end is-right-orthogonal-family-iff-is-right-orthogonal-to-shape
```

## Leibniz cotensor map

Buchholtz and Weinberger use the definition of the Leibniz-cotensor map to
define orthogonal families. We also show that this is a definition equivalent to
our initial definition. Again the proofs are just simple repackaging of data.

```rzk
#def leibniz-cotensor-codomain
  ( I : CUBE)
  ( X : I → TOPE)
  ( Y : X → TOPE)
  ( E B : U)
  ( p : E → B)
  : U
  :=
  Σ ( f : Y → E)
  , Σ ( g : X → B)
    , ( \ (y : Y) → p (f y)) =_{ Y → B } (\ (y : Y) → g y)

#def leibniz-cotensor
  ( I : CUBE)
  ( X : I → TOPE)
  ( Y : X → TOPE)
  ( E B : U)
  ( p : E → B)
  ( f : X → E)
  : leibniz-cotensor-codomain I X Y E B p
  := (\ (y : Y) → f y , (\ (x : X) → p (f x) , refl))
```

```rzk
#def is-equiv-leibniz-cotensor-is-right-orthogonal-to-shape
  ( I : CUBE)
  ( X : I → TOPE)
  ( Y : X → TOPE)
  ( E B : U)
  ( p : E → B)
  ( is-right-orthogonal-to-shape-p : is-right-orthogonal-to-shape I X Y E B p)
  : is-equiv
    ( X → E)
    ( leibniz-cotensor-codomain I X Y E B p)
    ( leibniz-cotensor I X Y E B p)
  :=
  second
  ( equiv-triple-comp
    ( X → E)
    ( Σ ( f : Y → E) , (x : X) → E [Y x ↦ f x])
    ( Σ ( f : Y → E) , (x : X) → B [Y x ↦ p (f x)])
    ( leibniz-cotensor-codomain I X Y E B p)
    ( equiv-extension-subshape I X Y (\ _ → E))
    ( total-equiv-family-of-equiv
      ( Y → E)
      ( \ f → (x : X) → E [Y x ↦ f x])
      ( \ f → (x : X) → B [Y x ↦ p (f x)])
      ( \ f → (\ F x → p (F x) , is-right-orthogonal-to-shape-p f)))
    ( total-equiv-family-of-equiv
      ( Y → E)
      ( \ f → (x : X) → B [Y x ↦ p (f x)])
      ( \ f → Σ (g : X → B) , (\ y → p (f y)) =_{Y → B} (\ y → g y))
      ( \ f → inv-equiv
        ( Σ ( g : X → B) , (\ y → p (f y)) =_{Y → B} (\ y → g y))
        ( ( x : X) → B [Y x ↦ p (f x)])
        ( equiv-extension-homotopy-constraint I X Y (\ _ → B) (\ y → p (f y))))))
```

```rzk
#def is-equiv-leibniz-cotensor-is-right-orthogonal-family uses (extext)
  ( I : CUBE)
  ( X : I → TOPE)
  ( Y : X → TOPE)
  ( B : U)
  ( P : B → U)
  ( is-right-orthogonal-family-P : is-right-orthogonal-family I X Y B P)
  : is-equiv
  ( X → total-type B P)
  ( leibniz-cotensor-codomain I X Y (total-type B P) B
    ( projection-total-type B P))
  ( leibniz-cotensor I X Y (total-type B P) B
    ( projection-total-type B P))
  :=
  is-equiv-leibniz-cotensor-is-right-orthogonal-to-shape I X Y
  ( total-type B P) (B)
  ( projection-total-type B P)
  ( is-right-orthogonal-to-shape-is-right-orthogonal-family I X Y B P
    ( is-right-orthogonal-family-P))
```

## Inner families

Inner families are a special case of orthogonal families. Any triangle below can
be lifted to a unique triangle above when specifying the inner horn above. This
corresponds to a "dependent Segal condition" and is often referred to as
composing dependent morphisms.

```rzk
#def is-inner-family
  ( A : U)
  ( B : A → U)
  : U
  := is-right-orthogonal-family (2 × 2) Δ² Λ²₁ A B

#def is-inner-family-is-prop uses (funext)
  ( A : U)
  ( B : A → U)
  : is-prop (is-inner-family A B)
  := is-right-orthogonal-family-is-prop (2 × 2) Δ² Λ²₁ A B
```

Each fiber of an inner family is Segal, since being inner is a stronger notion.

```rzk
#def is-segal-fiber-is-inner-family
  ( B : U)
  ( P : B → U)
  ( is-inner-family-P : is-inner-family B P)
  ( b : B)
  : is-segal (P b)
  :=
  \ x y z f g → is-contr-equiv-is-contr
  ( ( ( t , s) : Δ²) → P b [s ≡ 0₂ ↦ f t , t ≡ 1₂ ↦ g s])
  ( Σ ( h : hom (P b) x z) , (hom2 (P b) x y z f g h))
  ( \ τ → (\ t → τ (t , t) , (\ ts → τ ts))
  , ( ( \ (_ , τ) ts → τ ts , \ _ → refl)
    , ( \ (_ , τ) ts → τ ts , \ _ → refl)))
  ( is-inner-family-P
    ( \ _ → b)
    ( \ (t , s) → recOR(s ≡ 0₂ ↦ f t , t ≡ 1₂ ↦ g s)))
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
      , dhom B a b u' P x y)
  :=
  axiom-choice
  ( 2)
  ( Δ¹)
  ( ∂Δ¹)
  ( \ t → B)
  ( \ t → \ c → (P c))
  ( \ t → recOR(t ≡ 0₂ ↦ a , t ≡ 1₂ ↦ b))
  ( \ t → recOR(t ≡ 0₂ ↦ x , t ≡ 1₂ ↦ y))

#def inv-axiom-choice-dhom
  ( B : U)
  ( a b : B)
  ( P : B → U)
  ( x : P a)
  ( y : P b)
  : Equiv
    ( Σ ( u' : hom B a b)
      , dhom B a b u' P x y)
    ( hom (total-type B P) (a , x) (b , y))
  :=
  inv-equiv
  ( hom (total-type B P) (a , x) (b , y))
  ( Σ ( u' : hom B a b)
    , dhom B a b u' P x y)
  ( axiom-choice-dhom B a b P x y)
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
      , dhom2 B a b c u v w α P x y z f g h)
  :=
  axiom-choice
  ( 2 × 2)
  ( Δ²)
  ( ∂Δ²)
  ( \ _ → B)
  ( \ _ → P)
  ( \ (t , s) → recOR(s ≡ 0₂ ↦ u t , t ≡ 1₂ ↦ v s , s ≡ t ↦ w s))
  ( \ (t , s) → recOR(s ≡ 0₂ ↦ f t , t ≡ 1₂ ↦ g s , s ≡ t ↦ h s))
```

## Homotopies in inner families

Exactly analogously to Segal types, inner families give us an equivalence
between paths and triangles where one side is the identity morphism. In fact the
proof follows exactly the same structure.

```rzk
#def dhom-htpy
  ( A : U)
  ( x y : A)
  ( f : hom A x y)
  ( B : A → U)
  ( X : B x)
  ( Y : B y)
  ( F G : dhom A x y f B X Y)
  : U
  :=
  dhom2
    A x x y (id-hom A x) f f (id-comp-witness A x y f)
    B X X Y (id-dhom A x B X) F G
```

```rzk
#def id-dcomp-witness
  ( A : U)
  ( x y : A)
  ( f : hom A x y)
  ( B : A → U)
  ( X : B x)
  ( Y : B y)
  ( F : dhom A x y f B X Y)
  : dhom-htpy A x y f B X Y F F
  := \ (t₁ , t₂) → F t₂
```

```rzk
#def map-dhom2-homotopy
  ( A : U)
  ( x y : A)
  ( f : hom A x y)
  ( B : A → U)
  ( X : B x)
  ( Y : B y)
  ( F G : dhom A x y f B X Y)
  : ( F = G) → (dhom-htpy A x y f B X Y F G)
  :=
  ind-path
    ( dhom A x y f B X Y)
    ( F)
    ( \ G' p → (dhom-htpy A x y f B X Y F G'))
    ( id-dcomp-witness A x y f B X Y F)
    ( G)
```

```rzk
#def map-total-dhom2-homotopy
  ( A : U)
  ( x y : A)
  ( f : hom A x y)
  ( B : A → U)
  ( X : B x)
  ( Y : B y)
  ( F : dhom A x y f B X Y)
  : ( Σ ( G : dhom A x y f B X Y) , F = G)
  → ( Σ ( G : dhom A x y f B X Y) , dhom-htpy A x y f B X Y F G)
  := \ (G , p) → (G , map-dhom2-homotopy A x y f B X Y F G p)
```

```rzk
#def is-equiv-map-total-dhom2-homotopy-is-inner-family
  ( B : U)
  ( x y : B)
  ( u : hom B x y)
  ( P : B → U)
  ( is-inner-family-P : is-inner-family B P)
  ( X : P x)
  ( Y : P y)
  ( F : dhom B x y u P X Y)
  : is-equiv
    ( Σ ( G : dhom B x y u P X Y) , F = G)
    ( Σ ( G : dhom B x y u P X Y) , dhom-htpy B x y u P X Y F G)
    ( map-total-dhom2-homotopy B x y u P X Y F)
  :=
  is-equiv-are-contr
  ( Σ ( G : dhom B x y u P X Y) , F = G)
  ( Σ ( G : dhom B x y u P X Y) , dhom-htpy B x y u P X Y F G)
  ( is-contr-based-paths (dhom B x y u P X Y) F)
  ( is-contr-equiv-is-contr'
    ( Σ ( G : dhom B x y u P X Y) , dhom-htpy B x y u P X Y F G)
    ( ( ( t , s) : Δ²) → P (u s) [s ≡ 0₂ ↦ X , t ≡ 1₂ ↦ F s])
    ( equiv-has-inverse
      ( Σ ( G : dhom B x y u P X Y) , dhom-htpy B x y u P X Y F G)
      ( ( ( t , s) : Δ²) → P (u s) [s ≡ 0₂ ↦ X , t ≡ 1₂ ↦ F s])
      ( \ (_ , τ) ts → τ ts)
      ( \ τ → (\ t → τ (t , t) , \ ts → τ ts))
      ( \ _ → refl)
      ( \ _ → refl))
    ( is-inner-family-P
      ( \ (_ , s) → u s)
      ( \ (t , s) → recOR(s ≡ 0₂ ↦ X , t ≡ 1₂ ↦ F s))))
  ( map-total-dhom2-homotopy B x y u P X Y F)

#def equiv-homotopy-dhom2-is-inner-family
  ( B : U)
  ( x y : B)
  ( u : hom B x y)
  ( P : B → U)
  ( is-inner-family-P : is-inner-family B P)
  ( X : P x)
  ( Y : P y)
  ( F G : dhom B x y u P X Y)
  : Equiv
    ( F = G)
    ( dhom2 B x x y
      ( id-hom B x) u u
      ( \ (_ , s) → u s)
      ( P) X X Y
      ( id-dhom B x P X) F G)
  :=
  ( map-dhom2-homotopy B x y u P X Y F G
  , is-equiv-fiberwise-is-equiv-total
    ( dhom B x y u P X Y)
    ( \ K → F = K)
    ( dhom2 B x x y
      ( id-hom B x) u u
      ( \ (_ , s) → u s)
      ( P) X X Y
      ( id-dhom B x P X) F)
    ( map-dhom2-homotopy B x y u P X Y F)
    ( is-equiv-map-total-dhom2-homotopy-is-inner-family
      B x y u P is-inner-family-P X Y F)
    ( G))
```

TODO: formulate these in terms of true innerness!

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
  :=
  ( first (inv-axiom-choice-dhom B a c P x z))
  ( ( first (axiom-choice-dhom B a c P x z))
    ( comp-is-segal
      ( total-type B P)
      ( is-segal-total-P)
      ( a , x) (b , y) (c , z)
      ( ( first (inv-axiom-choice-dhom B a b P x y))
        ( \ t → u t , \ t → f t))
      ( ( first (inv-axiom-choice-dhom B b c P y z))
        ( \ t → v t , \ t → g t))))
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
  : hom B a b
  :=
  first
  ( ( first (axiom-choice-dhom B a b P x y))
    ( \ t → (u t , f t)))

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
    ( ( first (inv-axiom-choice-dhom B a b P x y))
      ( \ t → u t , \ t → f t))
    ( ( first (inv-axiom-choice-dhom B b c P y z))
      ( \ t → v t , \ t → g t))
    ( comp-total-type-is-inner
     B a b c u v P is-segal-B is-segal-total-P x y z f g)
  :=
  witness-comp-is-segal (total-type B P) is-segal-total-P
  ( a , x) (b , y) (c , z)
  ( ( first (inv-axiom-choice-dhom B a b P x y))
    ( \ t → u t , \ t → f t))
  ( ( first (inv-axiom-choice-dhom B b c P y z))
    ( \ t → v t , \ t → g t))

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
    ( first
      ( ( first (axiom-choice-dhom B a c P x z))
        ( comp-total-type-is-inner B a b c u v P is-segal-B
          is-segal-total-P x y z f g)))
  :=
  ap-hom2
  ( total-type B P)
  ( B)
  ( projection-total-type B P)
  ( a , x) (b , y) (c , z)
  ( ( first (inv-axiom-choice-dhom B a b P x y))
    ( \ t → u t , \ t → f t))
  ( ( first (inv-axiom-choice-dhom B b c P y z))
    ( \ t → v t , \ t → g t))
  ( comp-total-type-is-inner B a b c u v P is-segal-B
    is-segal-total-P x y z f g)
  ( comp2-total-type-is-inner B a b c u v P is-segal-B
    is-segal-total-P x y z f g)
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
    = ( first
        ( ( first (axiom-choice-dhom B a c P x z))
          ( comp-total-type-is-inner B a b c u v P is-segal-B
            is-segal-total-P x y z f g)))
  :=
  uniqueness-comp-is-segal B is-segal-B a b c u v
  ( first
    ( ( first (axiom-choice-dhom B a c P x z))
      ( comp-total-type-is-inner B a b c u v P is-segal-B
        is-segal-total-P x y z f g)))
  ( hom2-base-hom2-total-is-inner B a b c u v P is-segal-B
    is-segal-total-P x y z f g)
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
  : dhom B a c
    ( first
      ( ( first (axiom-choice-dhom B a c P x z))
        ( comp-total-type-is-inner B a b c u v P
          is-segal-B is-segal-total-P x y z f g)))
  P x z
  :=
  second
  ( ( first (axiom-choice-dhom B a c P x z))
    ( comp-total-type-is-inner B a b c u v P
      is-segal-B is-segal-total-P x y z f g))
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
  :=
  transport (hom B a c) (\ w → dhom B a c w P x z)
  ( first
    ( ( first (axiom-choice-dhom B a c P x z))
      ( comp-total-type-is-inner B a b c u v P
        is-segal-B is-segal-total-P x y z f g)))
  ( comp-is-segal B is-segal-B a b c u v)
  ( rev (hom B a c)
    ( comp-is-segal B is-segal-B a b c u v)
    ( first
      ( ( first (axiom-choice-dhom B a c P x z))
        ( comp-total-type-is-inner B a b c u v P is-segal-B
          is-segal-total-P x y z f g)))
    ( coherence-comp-is-inner B a b c u v P is-segal-B
      is-segal-total-P x y z f g))
  ( proj2-comp-total-type-is-inner B a b c u v P is-segal-B
    is-segal-total-P x y z f g)
```

For isoinner families, we can define dependent composition using the inner
family structure:

## Isoinner families

Lastly we need to define isoinner families for cocartesian families.

```rzk
#def Iso-arr
  ( A : U)
  ( is-segal-A : is-segal A)
  : U
  := Σ (f : arr A) , is-iso-arrow A is-segal-A (f 0₂) (f 1₂) f

#def iso-arr-eq
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  ( p : x = y)
  : Iso-arr A is-segal-A
  := (hom-eq A x y p , is-iso-arrow-hom-eq A is-segal-A x y p)
```

```rzk
#def is-isoinner-family
  ( B : U)
  ( P : B → U)
  : U
  :=
  Σ ( is-inner-family-P : is-inner-family B P)
  , ( ( b : B)
    → ( f : Iso-arr (P b)
           ( is-segal-fiber-is-inner-family B P is-inner-family-P b))
    → is-contr (Σ (e : P b)
      , f = iso-arr-eq (P b)
            ( is-segal-fiber-is-inner-family B P is-inner-family-P b)
            ( e) (e) (refl)))
```

## Vertical morphisms

Vertical morphisms are dependent morphisms over an identity.

```rzk
#def vert-dhom
  ( B : U)
  ( is-segal-B : is-segal B)
  ( b b' : B)
  ( P : B → U)
  ( e : P b)
  ( e' : P b')
  : U
  :=
  Σ ( u : Iso B is-segal-B b b')
  , dhom B b b' (first u) P e e'
```

```rzk
#def vert-Iso
  ( B : U)
  ( is-segal-B : is-segal B)
  ( b b' : B)
  ( P : B → U)
  ( e : P b)
  ( e' : P b')
  : U
  :=
  Σ ( u : Iso B is-segal-B b b')
  , dhom B b b' (first u) P e e'
```
