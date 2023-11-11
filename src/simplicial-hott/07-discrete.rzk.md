# Discrete types

These formalisations correspond to Section 7 of the RS17 paper.

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Prerequisites

- `hott/01-paths.rzk.md` - We require basic path algebra.
- `hott/04-equivalences.rzk.md` - We require the notion of equivalence between
  types.
- `03-simplicial-type-theory.rzk.md` — We rely on definitions of simplicies and
  their subshapes.
- `04-extension-types.rzk.md` — We use extension extensionality.
- `05-segal-types.rzk.md` - We use the notion of hom types.

Some of the definitions in this file rely on function extensionality and
extension extensionality:

```rzk
#assume funext : FunExt
#assume extext : ExtExt
```

## The definition

Discrete types are types in which the hom-types are canonically equivalent to
identity types.

```rzk title="RS17, Definition 7.1"
#def hom-eq
  ( A : U)
  ( x y : A)
  ( p : x = y)
  : hom A x y
  := ind-path (A) (x) (\ y' p' → hom A x y') ((id-hom A x)) (y) (p)

#def is-discrete
  ( A : U)
  : U
  := (x : A) → (y : A) → is-equiv (x = y) (hom A x y) (hom-eq A x y)
```

## Alternative definitions

One can characterize discrete types in various other equivalent:

```rzk
#section discrete-types-alternative

#variable A : U

#def is-Δ¹-local
  : U
  := is-equiv A (Δ¹ → A) (\ a _ → a)
```

```rzk
#def is-left-local
  : U
  := is-local-type 2 Δ¹ (\ t → t ≡ 0₂) A

#def is-right-local
  : U
  := is-local-type 2 Δ¹ (\ t → t ≡ 1₂) A
```

### Alternative definitions : proofs

First ot all, note that we have two section-retraction pairs

```rzk
#def is-section-retraction-0-Δ¹-0
  : is-section-retraction-pair
    ( A) ( Δ¹ → A) ( (t : 2 | Δ¹ t ∧ t ≡ 0₂) → A)
    ( \ a _ → a) (\ τ t → τ t)
  :=
    ( ( \ σ → σ 0₂ , \ _ → refl)
    , ( \ σ → σ 0₂ , \ _ → refl))

#def is-section-retraction-1-Δ¹-1
  : is-section-retraction-pair
    ( A) ( Δ¹ → A) ( (t : 2 | Δ¹ t ∧ t ≡ 1₂) → A)
    ( \ a _ → a) (\ τ t → τ t)
  :=
    ( ( \ σ → σ 1₂ , \ _ → refl)
    , ( \ σ → σ 1₂ , \ _ → refl))
```

From this it follows that the three alternative definitions are all equivalent
to each other.

```rzk
#def is-left-local-is-Δ¹-local
  : is-Δ¹-local → is-left-local
  :=
    is-equiv-retraction-is-equiv-section-is-section-retraction-pair
      ( A) ( Δ¹ → A) ( (t : 2 | Δ¹ t ∧ t ≡ 0₂) → A)
      ( \ a _ → a) (\ τ t → τ t)
    ( is-section-retraction-0-Δ¹-0)

#def is-Δ¹-local-is-left-local
  : is-left-local → is-Δ¹-local
  :=
    is-equiv-section-is-equiv-retraction-is-section-retraction-pair
      ( A) ( Δ¹ → A) ( (t : 2 | Δ¹ t ∧ t ≡ 0₂) → A)
      ( \ a _ → a) (\ τ t → τ t)
    ( is-section-retraction-0-Δ¹-0)

#def is-right-local-is-Δ¹-local
  : is-Δ¹-local → is-right-local
  :=
    is-equiv-retraction-is-equiv-section-is-section-retraction-pair
      ( A) ( Δ¹ → A) ( (t : 2 | Δ¹ t ∧ t ≡ 1₂) → A)
      ( \ a _ → a) (\ τ t → τ t)
    ( is-section-retraction-1-Δ¹-1)

#def is-Δ¹-local-is-right-local
  : is-right-local → is-Δ¹-local
  :=
    is-equiv-section-is-equiv-retraction-is-section-retraction-pair
      ( A) ( Δ¹ → A) ( (t : 2 | Δ¹ t ∧ t ≡ 1₂) → A)
      ( \ a _ → a) (\ τ t → τ t)
    ( is-section-retraction-1-Δ¹-1)
```

Next, we aim to compare the original `is-discrete` with `is-Δ¹-local`.

To do this, we note that we have an equivalence of maps between `A → (Δ¹ → A)`
and the total map of the family `\ (a, b) → hom-eq a b : a = b → hom A a b` .

```rzk
#def equiv-of-maps-total-map-hom-eq-const-Δ¹
  : Equiv-of-maps
    ( A) ( Δ¹ → A)
    ( \ a _ → a)
    ( free-paths A) ( fibered-arr' A)
    ( \ ((a,b), p) → ((a,b), hom-eq A a b p))
  :=
  ( ( ( constant-free-path A
      , fibered-arr-free-arr' A)
    , \ _ → refl)
  , ( is-equiv-constant-free-path A
    , is-equiv-fibered-arr-free-arr' A))
```

The rest is just logical bookkeeping using that equivalences are preserved under
equivalences of maps and when passing to/from total types.

```rzk
#def is-Δ¹-local-is-discrete
  ( is-discrete-A : is-discrete A)
  : is-Δ¹-local
  :=
    is-equiv-Equiv-is-equiv ( A) ( Δ¹ → A) ( \ a _ → a)
      ( free-paths A) ( fibered-arr' A)
      ( \ ((a,b), p) → ((a,b), hom-eq A a b p))
    ( equiv-of-maps-total-map-hom-eq-const-Δ¹)
    ( is-equiv-total-is-equiv-fiberwise
        ( product A A) ( \ (a,b) → a = b) ( \ (a,b) → hom A a b)
      ( \ (a,b) → hom-eq A a b)
      ( \ (a,b) → is-discrete-A a b))

#def is-discrete-is-Δ¹-local
  ( is-Δ¹-local-A : is-Δ¹-local)
  : is-discrete A
  :=
  \ a b →
    ( is-equiv-fiberwise-is-equiv-total ( product A A) ( \ (a,b) → a = b)
        ( \ (a,b) → hom A a b)
      ( \ (a,b) → hom-eq A a b)
      ( is-equiv-Equiv-is-equiv' ( A) ( Δ¹ → A) ( \ a _ → a)
          ( free-paths A) ( fibered-arr' A)
          ( \ ((a,b), p) → ((a,b), hom-eq A a b p))
        ( equiv-of-maps-total-map-hom-eq-const-Δ¹)
        (is-Δ¹-local-A)))
    ( a, b)

#end discrete-types-alternative
```

## Families of discrete types

By function extensionality, the dependent function type associated to a family
of discrete types is discrete.

```rzk
#def equiv-hom-eq-function-type-is-discrete uses (funext)
  ( X : U)
  ( A : X → U)
  ( is-discrete-A : (x : X) → is-discrete (A x))
  ( f g : (x : X) → A x)
  : Equiv (f = g) (hom ((x : X) → A x) f g)
  :=
    equiv-triple-comp
      ( f = g)
      ( (x : X) → f x = g x)
      ( (x : X) → hom (A x) (f x) (g x))
      ( hom ((x : X) → A x) f g)
      ( equiv-FunExt funext X A f g)
      ( equiv-function-equiv-family funext X
        ( \ x → (f x = g x))
        ( \ x → hom (A x) (f x) (g x))
        ( \ x → (hom-eq (A x) (f x) (g x) , (is-discrete-A x (f x) (g x)))))
      ( flip-ext-fun-inv
        ( 2)
        ( Δ¹)
        ( ∂Δ¹)
        ( X)
        ( \ t x → A x)
        ( \ t x → recOR (t ≡ 0₂ ↦ f x , t ≡ 1₂ ↦ g x)))

#def compute-hom-eq-function-type-is-discrete uses (funext)
  ( X : U)
  ( A : X → U)
  ( is-discrete-A : (x : X) → is-discrete (A x))
  ( f g : (x : X) → A x)
  ( h : f = g)
  : ( hom-eq ((x : X) → A x) f g h) =
    ( first (equiv-hom-eq-function-type-is-discrete X A is-discrete-A f g)) h
  :=
    ind-path
      ( (x : X) → A x)
      ( f)
      ( \ g' h' →
        hom-eq ((x : X) → A x) f g' h' =
        (first (equiv-hom-eq-function-type-is-discrete X A is-discrete-A f g')) h')
      ( refl)
      ( g)
      ( h)
```

```rzk title="RS17, Proposition 7.2"
#def is-discrete-function-type uses (funext)
  ( X : U)
  ( A : X → U)
  ( is-discrete-A : (x : X) → is-discrete (A x))
  : is-discrete ((x : X) → A x)
  :=
    \ f g →
    is-equiv-homotopy
      ( f = g)
      ( hom ((x : X) → A x) f g)
      ( hom-eq ((x : X) → A x) f g)
      ( first (equiv-hom-eq-function-type-is-discrete X A is-discrete-A f g))
      ( compute-hom-eq-function-type-is-discrete X A is-discrete-A f g)
      ( second (equiv-hom-eq-function-type-is-discrete X A is-discrete-A f g))
```

By extension extensionality, an extension type into a family of discrete types
is discrete. Since `#!rzk equiv-extensions-BOT-equiv` considers total extension
types only, extending from `#!rzk BOT`, that's all we prove here for now.

```rzk
#def equiv-hom-eq-extension-type-is-discrete uses (extext)
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( A : ψ → U)
  ( is-discrete-A : (t : ψ) → is-discrete (A t))
  ( f g : (t : ψ) → A t)
  : Equiv (f = g) (hom ((t : ψ) → A t) f g)
  :=
    equiv-triple-comp
      ( f = g)
      ( (t : ψ) → f t = g t)
      ( (t : ψ) → hom (A t) (f t) (g t))
      ( hom ((t : ψ) → A t) f g)
      ( equiv-ExtExt extext I ψ (\ _ → BOT) A (\ _ → recBOT) f g)
      ( equiv-extensions-BOT-equiv
        ( extext)
        ( I)
        ( ψ)
        ( \ t → f t = g t)
        ( \ t → hom (A t) (f t) (g t))
        ( \ t → (hom-eq (A t) (f t) (g t) , (is-discrete-A t (f t) (g t)))))
      ( fubini
        ( I)
        ( 2)
        ( ψ)
        ( \ t → BOT)
        ( Δ¹)
        ( ∂Δ¹)
        ( \ t s → A t)
        ( \ (t , s) → recOR (s ≡ 0₂ ↦ f t , s ≡ 1₂ ↦ g t)))

#def compute-hom-eq-extension-type-is-discrete uses (extext)
  ( I : CUBE)
  ( ψ : (t : I) → TOPE)
  ( A : ψ → U)
  ( is-discrete-A : (t : ψ) → is-discrete (A t))
  ( f g : (t : ψ) → A t)
  ( h : f = g)
  : ( hom-eq ((t : ψ) → A t) f g h) =
    ( first (equiv-hom-eq-extension-type-is-discrete I ψ A is-discrete-A f g)) h
  :=
    ind-path
      ( (t : ψ) → A t)
      ( f)
      ( \ g' h' →
        ( hom-eq ((t : ψ) → A t) f g' h') =
        ( first (equiv-hom-eq-extension-type-is-discrete I ψ A is-discrete-A f g') h'))
      ( refl)
      ( g)
      ( h)
```

```rzk title="RS17, Proposition 7.2, for extension types"
#def is-discrete-extension-type uses (extext)
  ( I : CUBE)
  ( ψ : (t : I) → TOPE)
  ( A : ψ → U)
  ( is-discrete-A : (t : ψ) → is-discrete (A t))
  : is-discrete ((t : ψ) → A t)
  :=
    \ f g →
    is-equiv-homotopy
      ( f = g)
      ( hom ((t : ψ) → A t) f g)
      ( hom-eq ((t : ψ) → A t) f g)
      ( first (equiv-hom-eq-extension-type-is-discrete I ψ A is-discrete-A f g))
      ( compute-hom-eq-extension-type-is-discrete I ψ A is-discrete-A f g)
      ( second (equiv-hom-eq-extension-type-is-discrete I ψ A is-discrete-A f g))
```

For instance, the arrow type of a discrete type is discrete.

```rzk
#def is-discrete-arr uses (extext)
  ( A : U)
  ( is-discrete-A : is-discrete A)
  : is-discrete (arr A)
  := is-discrete-extension-type 2 Δ¹ (\ _ → A) (\ _ → is-discrete-A)
```

## Contractible types are discrete

Every contractible type is automatically discrete.

```rzk
#def is-discrete-is-contr uses (extext)
  ( A : U)
  : is-contr A → is-discrete A
  :=
  \ is-contr-A →
    ( is-discrete-is-Δ¹-local A
      ( is-Δ¹-local-is-left-local A
        ( is-local-type-is-contr extext 2 Δ¹ (\ t → t ≡ 0₂) A
          is-contr-A)))

#def is-discrete-Unit uses (extext)
  : is-discrete Unit
  := is-discrete-is-contr Unit (is-contr-Unit)
```

## Discrete types are Segal types

Recall that we can characterize discrete type either as those local for
`{0} ⊂ Δ¹` _or_, equivalently, as those that are local for `{1} ⊂ Δ¹`. This
suggests two different relative notions of discreteness and corresponding
notions of anodyne shape inclusions.

Note that while the absolute notions of locality for `{0} ⊂ Δ¹` and `{1} ⊂ Δ¹`
agree, the relative notions _do not_. We will explore this discrepancy more when
we introduce covariant and contravariant type families.

```rzk
#def is-left-fibration
  ( A' A : U)
  ( α : A' → A)
  : U
  := is-right-orthogonal-to-shape 2 Δ¹ ( \ s → s ≡ 0₂) A' A α

#def is-right-fibration
  ( A' A : U)
  ( α : A' → A)
  : U
  := is-right-orthogonal-to-shape 2 Δ¹ ( \ s → s ≡ 1₂) A' A α
```

### Left and right anodyne shape inclusions

```rzk
#def is-left-anodyne
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  : U
  := is-anodyne-for-shape 2 Δ¹ ( \ s → s ≡ 0₂) I ψ ϕ

#def is-right-anodyne
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  : U
  := is-anodyne-for-shape 2 Δ¹ ( \ s → s ≡ 1₂) I ψ ϕ
```

### Left fibrations are inner fibrations

We aim to show that every left fibration is an inner fibration, i.e. that the
inner horn inclusion `Λ ⊂ Δ²` is left anodyne.

The first step is to identify the pair `{0} ⊂ Δ¹` with the pair of subshapes
`{1} ⊂ right-leg-of-Λ` of `Λ`.

```rzk
#def is-left-anodyne-1-right-leg-of-Λ
  : is-left-anodyne ( 2 × 2)
    (\ ts → right-leg-of-Λ ts) ( \ (_,s) → s ≡ 0₂)
  :=
  \ A' A α →
  is-right-orthogonal-to-shape-isomorphism A' A α
  ( 2 × 2) (\ ts → right-leg-of-Λ ts) (\ (t , s) → t ≡ 1₂ ∧ s ≡ 0₂)
  ( 2) (Δ¹) (\ t → t ≡ 0₂)
  ( functorial-isomorphism-0-Δ¹-1-right-leg-of-Λ)
```

Next we use that `Λ` is the pushout of its left leg and its right leg to deduce
that the pair `left-leg-of-Λ ⊂ Λ` is left anodyne.

```rzk
#def left-leg-of-Λ : Λ → TOPE
  := \ (t, s) → s ≡ 0₂

#def is-left-anodyne-left-leg-of-Λ-Λ
  : is-left-anodyne ( 2 × 2)
    ( \ ts → Λ ts) ( \ ts → left-leg-of-Λ ts)
  :=
  \ A' A α is-left-fib-α →
    is-right-orthogonal-to-shape-pushout A' A α
    ( 2 × 2) ( \ ts → right-leg-of-Λ ts) (\ ts → left-leg-of-Λ ts)
    ( is-left-anodyne-1-right-leg-of-Λ A' A α is-left-fib-α)
```

Furthermore, we observe that the pair `left-leg-of-Δ ⊂ Δ¹×Δ¹` is the product of
`Δ¹` with the left anodyne pair `{0} ⊂ Δ¹`, hence left anodyne itself.

```rzk
#def is-left-anodyne-left-leg-of-Λ-Δ¹×Δ¹ uses (extext)
  : is-left-anodyne ( 2 × 2)
    ( \ ts → Δ¹×Δ¹ ts) ( \ ts → left-leg-of-Λ ts)
  :=
  \ A' A α →
    is-right-orthogonal-to-shape-product extext A' A α
      2 Δ¹ 2 Δ¹ ( \ s → s ≡ 0₂)
```

Next, we use the left cancellation of left anodyne shape inclusions to deduce
that `Λ ⊂ Δ¹×Δ¹` is left anodyne.

```rzk
#def is-left-anodyne-Λ-Δ¹×Δ¹ uses (extext)
  : is-left-anodyne ( 2 × 2)
    ( \ ts → Δ¹×Δ¹ ts) ( \ ts → Λ ts)
  :=
  is-anodyne-left-cancel-for-shape 2 Δ¹ (\ t → t ≡ 0₂)
  ( 2 × 2) ( \ ts → Δ¹×Δ¹ ts) ( \ ts → Λ ts) ( \ ts → left-leg-of-Λ ts)
  ( is-left-anodyne-left-leg-of-Λ-Λ)
  ( is-left-anodyne-left-leg-of-Λ-Δ¹×Δ¹)
```

Finally, we right cancel the functorial retract `Δ² ⊂ Δ¹×Δ¹` to obtain the
desired left anodyne shape inclusion `Λ ⊂ Δ²`.

```rzk
#def is-left-anodyne-Λ-Δ² uses (extext)
  : is-left-anodyne (2 × 2)
    Δ² (\ t → Λ t)
  :=
  is-anodyne-right-cancel-retract-for-shape 2 Δ¹ (\ t → t ≡ 0₂)
  ( 2 × 2) ( \ ts → Δ¹×Δ¹ ts) ( \ ts → Δ² ts) ( \ ts → Λ ts)
  ( is-functorial-retract-Δ²-Δ¹×Δ¹)
  ( is-left-anodyne-Λ-Δ¹×Δ¹)
```

which we can unpack to get the desired implication

```rzk
#def is-inner-fibration-is-left-fibration uses (extext)
  ( A' A : U)
  ( α : A' → A)
  : is-left-fibration A' A α → is-inner-fibration A' A α
  := is-left-anodyne-Λ-Δ² A' A α
```

### Left fibrations and Segal types

Since the Segal types are precisely the local types with respect to `Λ ⊂ Δ²`, we
immediately deduce that in any left fibration `α : A' → A`, if `A` is a Segal
type, then so is `A'`.

```rzk title="RS 17, Theorem 8.8, categorical version"
#def is-segal-domain-left-fibration-is-segal-codomain uses (extext)
  ( A' A : U)
  ( α : A' → A)
  ( is-left-fib-α : is-left-fibration A' A α)
  ( is-segal-A : is-segal A)
  : is-segal A'
  :=
    is-segal-is-local-horn-inclusion A'
      ( is-local-type-right-orthogonal-is-local-type
        ( 2 × 2) Δ² ( \ ts → Λ ts) A' A α
        ( is-inner-fibration-is-left-fibration A' A α is-left-fib-α)
        ( is-local-horn-inclusion-is-segal A is-segal-A))
```

### Discrete types are Segal types

Another immediate corollary is that every discrete type is Segal.

```rzk
#def is-segal-is-discrete uses (extext)
  ( A : U)
  : is-discrete A → is-segal A
  :=
  \ is-discrete-A →
  ( is-segal-has-unique-inner-extensions A
    ( is-weak-anodyne-is-anodyne-for-shape extext
      ( 2) (Δ¹) (\ t → t ≡ 0₂) ( 2 × 2) (Δ²) (\ t → Λ t)
      ( is-left-anodyne-Λ-Δ²)
      ( A)
      ( has-unique-extensions-is-local-type 2 Δ¹ (\ t → t ≡ 0₂) A
        ( is-left-local-is-Δ¹-local A
          ( is-Δ¹-local-is-discrete A is-discrete-A)))))
```

## Discrete types are Segal types (original proof of RS17)

This chapter contains the original proof of RS17 that discrete types are
automatically Segal types. We retain it since some intermediate calculations
might still be of use.

```rzk
#section discrete-arr-equivalences

#variable A : U
#variable is-discrete-A : is-discrete A
#variables x y z w : A
#variable f : hom A x y
#variable g : hom A z w

#def is-equiv-hom-eq-discrete uses (extext x y z w)
  : is-equiv (f =_{arr A} g) (hom (arr A) f g) (hom-eq (arr A) f g)
  := (is-discrete-arr A is-discrete-A) f g

#def equiv-hom-eq-discrete uses (extext x y z w)
  : Equiv (f =_{arr A} g) (hom (arr A) f g)
  := (hom-eq (arr A) f g , (is-discrete-arr A is-discrete-A) f g)

#def equiv-square-hom-arr
  : Equiv
      ( hom (arr A) f g)
      ( Σ ( h : hom A x z) ,
          ( Σ ( k : hom A y w) ,
              ( ( (t , s) : Δ¹×Δ¹) →
                A [ t ≡ 0₂ ∧ Δ¹ s ↦ f s ,
                    t ≡ 1₂ ∧ Δ¹ s ↦ g s ,
                    Δ¹ t ∧ s ≡ 0₂ ↦ h t ,
                    Δ¹ t ∧ s ≡ 1₂ ↦ k t])))
  :=
    ( \ α →
      ( ( \ t → α t 0₂) ,
        ( ( \ t → α t 1₂) , (\ (t , s) → α t s))) ,
      ( ( ( \ σ t s → (second (second σ)) (t , s)) , (\ α → refl)) ,
        ( ( \ σ t s → (second (second σ)) (t , s)) , (\ σ → refl))))
```

```rzk
#def is-equiv-ap-fibered-arr-free-arr uses (w x y z)
  : is-equiv
      ( f =_{Δ¹ → A} g)
      ( fibered-arr-free-arr A f = fibered-arr-free-arr A g)
      ( ap
        ( arr A)
        ( Σ (u : A) , (Σ (v : A) , (hom A u v)))
        ( f)
        ( g)
        ( fibered-arr-free-arr A))
  :=
    is-emb-is-equiv
      ( arr A)
      ( Σ (u : A) , (Σ (v : A) , (hom A u v)))
      ( fibered-arr-free-arr A)
      ( is-equiv-fibered-arr-free-arr A)
      ( f)
      ( g)

#def equiv-eq-fibered-arr-eq-free-arr uses (w x y z)
  : Equiv (f =_{Δ¹ → A} g) (fibered-arr-free-arr A f = fibered-arr-free-arr A g)
  :=
    equiv-ap-is-equiv
      ( arr A)
      ( Σ (u : A) , (Σ (v : A) , (hom A u v)))
      ( fibered-arr-free-arr A)
      ( is-equiv-fibered-arr-free-arr A)
      ( f)
      ( g)

#def equiv-sigma-over-product-hom-eq
  : Equiv
      ( fibered-arr-free-arr A f = fibered-arr-free-arr A g)
      ( Σ ( p : x = z) ,
          ( Σ ( q : y = w) ,
              ( product-transport A A (hom A) x z y w p q f = g)))
  :=
    extensionality-Σ-over-product
      ( A) (A)
      ( hom A)
      ( fibered-arr-free-arr A f)
      ( fibered-arr-free-arr A g)

#def equiv-square-sigma-over-product uses (extext is-discrete-A)
  : Equiv
    ( Σ ( p : x = z) ,
        ( Σ (q : y = w) ,
            ( product-transport A A (hom A) x z y w p q f = g)))
    ( Σ ( h : hom A x z) ,
        ( Σ ( k : hom A y w) ,
            ( ((t , s) : Δ¹×Δ¹) →
              A [ (t ≡ 0₂) ∧ (Δ¹ s) ↦ f s ,
                  (t ≡ 1₂) ∧ (Δ¹ s) ↦ g s ,
                  (Δ¹ t) ∧ (s ≡ 0₂) ↦ h t ,
                  (Δ¹ t) ∧ (s ≡ 1₂) ↦ k t])))
  :=
    equiv-left-cancel
      ( f =_{Δ¹ → A} g)
      ( Σ ( p : x = z) ,
          ( Σ ( q : y = w) ,
              ( product-transport A A (hom A) x z y w p q f = g)))
      ( Σ ( h : hom A x z) ,
          ( Σ ( k : hom A y w) ,
              ( ((t , s) : Δ¹×Δ¹) →
                A [ (t ≡ 0₂) ∧ (Δ¹ s) ↦ f s ,
                    (t ≡ 1₂) ∧ (Δ¹ s) ↦ g s ,
                    (Δ¹ t) ∧ (s ≡ 0₂) ↦ h t ,
                    (Δ¹ t) ∧ (s ≡ 1₂) ↦ k t])))
      ( equiv-comp
        ( f =_{Δ¹ → A} g)
        ( fibered-arr-free-arr A f = fibered-arr-free-arr A g)
        ( Σ ( p : x = z) ,
            ( Σ ( q : y = w) ,
                ( product-transport A A (hom A) x z y w p q f = g)))
        equiv-eq-fibered-arr-eq-free-arr
        equiv-sigma-over-product-hom-eq)
      ( equiv-comp
        ( f =_{Δ¹ → A} g)
        ( hom (arr A) f g)
        ( Σ ( h : hom A x z) ,
            ( Σ ( k : hom A y w) ,
                ( ( (t , s) : Δ¹×Δ¹) →
                  A [ (t ≡ 0₂) ∧ (Δ¹ s) ↦ f s ,
                      (t ≡ 1₂) ∧ (Δ¹ s) ↦ g s ,
                      (Δ¹ t) ∧ (s ≡ 0₂) ↦ h t ,
                      (Δ¹ t) ∧ (s ≡ 1₂) ↦ k t])))
        ( equiv-hom-eq-discrete)
        ( equiv-square-hom-arr))
```

We close the section so we can use path induction.

```rzk
#end discrete-arr-equivalences
```

```rzk
#def fibered-map-square-sigma-over-product
  ( A : U)
  ( x y z w : A)
  ( f : hom A x y)
  ( p : x = z)
  ( q : y = w)
  : ( g : hom A z w) →
    ( product-transport A A (hom A) x z y w p q f = g) →
    ( ( (t , s) : Δ¹×Δ¹) →
      A [ (t ≡ 0₂) ∧ (Δ¹ s) ↦ f s ,
          (t ≡ 1₂) ∧ (Δ¹ s) ↦ g s ,
          (Δ¹ t) ∧ (s ≡ 0₂) ↦ (hom-eq A x z p) t ,
          (Δ¹ t) ∧ (s ≡ 1₂) ↦ (hom-eq A y w q) t])
  :=
    ind-path
      ( A)
      ( x)
      ( \ z' p' →
        ( g : hom A z' w) →
        ( product-transport A A (hom A) x z' y w p' q f = g) →
        ( ( (t , s) : Δ¹×Δ¹) →
          A [ (t ≡ 0₂) ∧ (Δ¹ s) ↦ f s ,
              (t ≡ 1₂) ∧ (Δ¹ s) ↦ g s ,
              (Δ¹ t) ∧ (s ≡ 0₂) ↦ (hom-eq A x z' p') t ,
              (Δ¹ t) ∧ (s ≡ 1₂) ↦ (hom-eq A y w q) t]))
      ( ind-path
        ( A)
        ( y)
        ( \ w' q' →
          ( g : hom A x w') →
          ( product-transport A A (hom A) x x y w' refl q' f = g) →
          ( ( (t , s) : Δ¹×Δ¹) →
            A [ (t ≡ 0₂) ∧ (Δ¹ s) ↦ f s ,
                (t ≡ 1₂) ∧ (Δ¹ s) ↦ g s ,
                (Δ¹ t) ∧ (s ≡ 0₂) ↦ x ,
                (Δ¹ t) ∧ (s ≡ 1₂) ↦ (hom-eq A y w' q') t]))
        ( ind-path
          ( hom A x y)
          ( f)
          ( \ g' τ' →
            ( ( (t , s) : Δ¹×Δ¹) →
              A [ (t ≡ 0₂) ∧ (Δ¹ s) ↦ f s ,
                  (t ≡ 1₂) ∧ (Δ¹ s) ↦ g' s ,
                  (Δ¹ t) ∧ (s ≡ 0₂) ↦ x ,
                  (Δ¹ t) ∧ (s ≡ 1₂) ↦ y]))
          ( \ (t , s) → f s))
        ( w)
        ( q))
      ( z)
      ( p)

#def square-sigma-over-product
  ( A : U)
  ( x y z w : A)
  ( f : hom A x y)
  ( g : hom A z w)
  ( ( p , (q , τ)) :
    ( Σ ( p : x = z) ,
        ( Σ ( q : y = w) ,
            ( product-transport A A (hom A) x z y w p q f = g))))
  : Σ ( h : hom A x z) ,
      ( Σ ( k : hom A y w) ,
          ( ( (t , s) : Δ¹×Δ¹) →
            A [ (t ≡ 0₂) ∧ (Δ¹ s) ↦ f s ,
                (t ≡ 1₂) ∧ (Δ¹ s) ↦ g s ,
                (Δ¹ t) ∧ (s ≡ 0₂) ↦ h t ,
                (Δ¹ t) ∧ (s ≡ 1₂) ↦ k t]))
  :=
    ( ( hom-eq A x z p) ,
      ( ( hom-eq A y w q) ,
        ( fibered-map-square-sigma-over-product
          ( A)
          ( x) (y) (z) (w)
          ( f) (p) (q) (g)
          ( τ))))

#def refl-refl-map-equiv-square-sigma-over-product uses (extext)
  ( A : U)
  ( is-discrete-A : is-discrete A)
  ( x y : A)
  ( f g : hom A x y)
  ( τ : product-transport A A (hom A) x x y y refl refl f = g)
  : ( first
      ( equiv-square-sigma-over-product A is-discrete-A x y x y f g)
      (refl , (refl , τ))) =
    ( square-sigma-over-product
      ( A)
      ( x) (y) (x) (y)
      ( f) (g)
      ( refl , (refl , τ)))
  :=
    ind-path
      ( hom A x y)
      ( f)
      ( \ g' τ' →
        ( first
          ( equiv-square-sigma-over-product A is-discrete-A x y x y f g')
          ( refl , (refl , τ'))) =
        ( square-sigma-over-product
          ( A)
          ( x) (y) (x) (y)
          ( f) (g')
          ( refl , (refl , τ'))))
      ( refl)
      ( g)
      ( τ)

#def map-equiv-square-sigma-over-product uses (extext)
  ( A : U)
  ( is-discrete-A : is-discrete A)
  ( x y z w : A)
  ( f : hom A x y)
  ( p : x = z)
  ( q : y = w)
  : ( g : hom A z w) →
    ( τ : product-transport A A (hom A) x z y w p q f = g) →
    ( first
      ( equiv-square-sigma-over-product A is-discrete-A x y z w f g)
      ( p , (q , τ))) =
    ( square-sigma-over-product
        A x y z w f g (p , (q , τ)))
  :=
    ind-path
      ( A)
      ( y)
      ( \ w' q' →
        ( g : hom A z w') →
        ( τ : product-transport A A (hom A) x z y w' p q' f = g) →
        ( first
          ( equiv-square-sigma-over-product
              A is-discrete-A x y z w' f g))
          ( p , (q' , τ)) =
        ( square-sigma-over-product A x y z w' f g)
          ( p , (q' , τ)))
      ( ind-path
        ( A)
        ( x)
        ( \ z' p' →
          ( g : hom A z' y) →
          ( τ : product-transport A A (hom A) x z' y y p' refl f = g) →
          ( first
            ( equiv-square-sigma-over-product A is-discrete-A x y z' y f g)
            ( p' , (refl , τ))) =
          ( square-sigma-over-product A x y z' y f g (p' , (refl , τ))))
        ( refl-refl-map-equiv-square-sigma-over-product
            ( A) (is-discrete-A) (x) (y) (f))
        ( z)
        ( p))
      ( w)
      ( q)

#def is-equiv-square-sigma-over-product uses (extext)
  ( A : U)
  ( is-discrete-A : is-discrete A)
  ( x y z w : A)
  ( f : hom A x y)
  ( g : hom A z w)
  : is-equiv
    ( Σ ( p : x = z) ,
        ( Σ ( q : y = w) ,
            ( product-transport A A (hom A) x z y w p q f = g)))
    ( Σ ( h : hom A x z) ,
        ( Σ ( k : hom A y w) ,
            ( ( (t , s) : Δ¹×Δ¹) →
              A [ (t ≡ 0₂) ∧ (Δ¹ s) ↦ f s ,
                  (t ≡ 1₂) ∧ (Δ¹ s) ↦ g s ,
                  (Δ¹ t) ∧ (s ≡ 0₂) ↦ h t ,
                  (Δ¹ t) ∧ (s ≡ 1₂) ↦ k t])))
    ( square-sigma-over-product A x y z w f g)
  :=
    is-equiv-rev-homotopy
    ( Σ ( p : x = z) ,
        ( Σ ( q : y = w) ,
            ( product-transport A A (hom A) x z y w p q f = g)))
    ( Σ ( h : hom A x z) ,
        ( Σ ( k : hom A y w) ,
            ( ( (t , s) : Δ¹×Δ¹) →
              A [ (t ≡ 0₂) ∧ (Δ¹ s) ↦ f s ,
                  (t ≡ 1₂) ∧ (Δ¹ s) ↦ g s ,
                  (Δ¹ t) ∧ (s ≡ 0₂) ↦ h t ,
                  (Δ¹ t) ∧ (s ≡ 1₂) ↦ k t])))
    ( first (equiv-square-sigma-over-product A is-discrete-A x y z w f g))
    ( square-sigma-over-product A x y z w f g)
    ( \ (p , (q , τ)) →
      map-equiv-square-sigma-over-product A is-discrete-A x y z w f p q g τ)
    ( second (equiv-square-sigma-over-product A is-discrete-A x y z w f g))

#def is-equiv-fibered-map-square-sigma-over-product uses (extext)
  ( A : U)
  ( is-discrete-A : is-discrete A)
  ( x y z w : A)
  ( f : hom A x y)
  ( g : hom A z w)
  ( p : x = z)
  ( q : y = w)
  : is-equiv
    ( product-transport A A (hom A) x z y w p q f = g)
    ( ( (t , s) : Δ¹×Δ¹) →
      A [ (t ≡ 0₂) ∧ (Δ¹ s) ↦ f s ,
          (t ≡ 1₂) ∧ (Δ¹ s) ↦ g s ,
          (Δ¹ t) ∧ (s ≡ 0₂) ↦ (hom-eq A x z p) t ,
          (Δ¹ t) ∧ (s ≡ 1₂) ↦ (hom-eq A y w q) t])
    ( fibered-map-square-sigma-over-product A x y z w f p q g)
  :=
    fibered-map-is-equiv-bases-are-equiv-total-map-is-equiv
      ( x = z)
      ( hom A x z)
      ( y = w)
      ( hom A y w)
      ( \ p' q' → (product-transport A A (hom A) x z y w p' q' f) = g)
      ( \ h' k' →
        ( ( (t , s) : Δ¹×Δ¹) →
          A [ (t ≡ 0₂) ∧ (Δ¹ s) ↦ f s ,
              (t ≡ 1₂) ∧ (Δ¹ s) ↦ g s ,
              (Δ¹ t) ∧ (s ≡ 0₂) ↦ h' t ,
              (Δ¹ t) ∧ (s ≡ 1₂) ↦ k' t]))
      ( hom-eq A x z)
      ( hom-eq A y w)
      ( \ p' q' →
        fibered-map-square-sigma-over-product
          ( A)
          ( x) (y) (z) (w)
          ( f)
          ( p')
          ( q')
          ( g))
      ( is-equiv-square-sigma-over-product A is-discrete-A x y z w f g)
      ( is-discrete-A x z)
      ( is-discrete-A y w)
      ( p)
      ( q)

#def is-equiv-fibered-map-square-sigma-over-product-refl-refl uses (extext)
  ( A : U)
  ( is-discrete-A : is-discrete A)
  ( x y : A)
  ( f : hom A x y)
  ( g : hom A x y)
  : is-equiv
    (f = g)
    ( ( (t , s) : Δ¹×Δ¹) →
      A [ (t ≡ 0₂) ∧ (Δ¹ s) ↦ f s ,
          (t ≡ 1₂) ∧ (Δ¹ s) ↦ g s ,
          (Δ¹ t) ∧ (s ≡ 0₂) ↦ x ,
          (Δ¹ t) ∧ (s ≡ 1₂) ↦ y])
    ( fibered-map-square-sigma-over-product
      A x y x y f refl refl g)
  :=
    is-equiv-fibered-map-square-sigma-over-product
      A is-discrete-A x y x y f g refl refl
```

The previous calculations allow us to establish a family of equivalences:

```rzk
#def is-equiv-sum-fibered-map-square-sigma-over-product-refl-refl uses (extext)
  ( A : U)
  ( is-discrete-A : is-discrete A)
  ( x y : A)
  ( f : hom A x y)
  : is-equiv
    ( Σ ( g : hom A x y) , f = g)
    ( Σ ( g : hom A x y) ,
        ( ( (t , s) : Δ¹×Δ¹) →
          A [ (t ≡ 0₂) ∧ (Δ¹ s) ↦ f s ,
              (t ≡ 1₂) ∧ (Δ¹ s) ↦ g s ,
              (Δ¹ t) ∧ (s ≡ 0₂) ↦ x ,
              (Δ¹ t) ∧ (s ≡ 1₂) ↦ y]))
    ( total-map
      ( hom A x y)
      ( \ g → f = g)
      ( \ g →
        ( (t , s) : Δ¹×Δ¹) →
        A [ (t ≡ 0₂) ∧ (Δ¹ s) ↦ f s ,
            (t ≡ 1₂) ∧ (Δ¹ s) ↦ g s ,
            (Δ¹ t) ∧ (s ≡ 0₂) ↦ x ,
            (Δ¹ t) ∧ (s ≡ 1₂) ↦ y])
      ( fibered-map-square-sigma-over-product
          A x y x y f refl refl))
  :=
    is-equiv-total-is-equiv-fiberwise
      ( hom A x y)
      ( \ g → f = g)
      ( \ g →
        ( (t , s) : Δ¹×Δ¹) →
        A [ (t ≡ 0₂) ∧ (Δ¹ s) ↦ f s ,
            (t ≡ 1₂) ∧ (Δ¹ s) ↦ g s ,
            (Δ¹ t) ∧ (s ≡ 0₂) ↦ x ,
            (Δ¹ t) ∧ (s ≡ 1₂) ↦ y])
      ( fibered-map-square-sigma-over-product
          A x y x y f refl refl)
      ( \ g →
        is-equiv-fibered-map-square-sigma-over-product-refl-refl
          ( A) (is-discrete-A)
          ( x) (y)
          ( f) (g))

#def equiv-sum-fibered-map-square-sigma-over-product-refl-refl uses (extext)
  ( A : U)
  ( is-discrete-A : is-discrete A)
  ( x y : A)
  ( f : hom A x y)
  : Equiv
      ( Σ (g : hom A x y) , f = g)
      ( Σ (g : hom A x y) ,
          ( ( (t , s) : Δ¹×Δ¹) →
            A [ (t ≡ 0₂) ∧ (Δ¹ s) ↦ f s ,
                (t ≡ 1₂) ∧ (Δ¹ s) ↦ g s ,
                (Δ¹ t) ∧ (s ≡ 0₂) ↦ x ,
                (Δ¹ t) ∧ (s ≡ 1₂) ↦ y]))
  :=
    ( ( total-map
        ( hom A x y)
        ( \ g → f = g)
        ( \ g →
          ( (t , s) : Δ¹×Δ¹) →
          A [ (t ≡ 0₂) ∧ (Δ¹ s) ↦ f s ,
              (t ≡ 1₂) ∧ (Δ¹ s) ↦ g s ,
              (Δ¹ t) ∧ (s ≡ 0₂) ↦ x ,
              (Δ¹ t) ∧ (s ≡ 1₂) ↦ y])
        ( fibered-map-square-sigma-over-product
            A x y x y f refl refl)) ,
    is-equiv-sum-fibered-map-square-sigma-over-product-refl-refl
      A is-discrete-A x y f)
```

Now using the equivalence on total spaces and the contractibility of based path
spaces, we conclude that the codomain extension type is contractible.

```rzk
#def is-contr-horn-refl-refl-extension-type uses (extext)
  ( A : U)
  ( is-discrete-A : is-discrete A)
  ( x y : A)
  ( f : hom A x y)
  : is-contr
    ( Σ ( g : hom A x y) ,
        ( ( (t , s) : Δ¹×Δ¹) →
          A [ (t ≡ 0₂) ∧ (Δ¹ s) ↦ f s ,
              (t ≡ 1₂) ∧ (Δ¹ s) ↦ g s ,
              (Δ¹ t) ∧ (s ≡ 0₂) ↦ x ,
              (Δ¹ t) ∧ (s ≡ 1₂) ↦ y]))
  :=
    is-contr-equiv-is-contr
      ( Σ ( g : hom A x y) , f = g)
      ( Σ ( g : hom A x y) ,
          ( ( (t , s) : Δ¹×Δ¹) →
            A [ (t ≡ 0₂) ∧ (Δ¹ s) ↦ f s ,
                (t ≡ 1₂) ∧ (Δ¹ s) ↦ g s ,
                (Δ¹ t) ∧ (s ≡ 0₂) ↦ x ,
                (Δ¹ t) ∧ (s ≡ 1₂) ↦ y]))
      ( equiv-sum-fibered-map-square-sigma-over-product-refl-refl
          A is-discrete-A x y f)
      ( is-contr-based-paths (hom A x y) f)
```

The extension types that appear in the Segal condition are retracts of this type
--- at least when the second arrow in the composable pair is an identity.

```rzk
#def triangle-to-square-section
  ( A : U)
  ( x y : A)
  ( f g : hom A x y)
  ( α : hom2 A x y y f (id-hom A y) g)
  : ( (t , s) : Δ¹×Δ¹) →
    A [ (t ≡ 0₂) ∧ (Δ¹ s) ↦ f s ,
        (t ≡ 1₂) ∧ (Δ¹ s) ↦ g s ,
        (Δ¹ t) ∧ (s ≡ 0₂) ↦ x ,
        (Δ¹ t) ∧ (s ≡ 1₂) ↦ y]
  := \ (t , s) → recOR (t ≤ s ↦ α (s , t) , s ≤ t ↦ g s)

#def sigma-triangle-to-sigma-square-section
  ( A : U)
  ( x y : A)
  ( f : hom A x y)
  ( (d , α) : Σ (d : hom A x y) , hom2 A x y y f (id-hom A y) d)
  : Σ ( g : hom A x y) ,
      ( ( (t , s) : Δ¹×Δ¹) →
        A [ (t ≡ 0₂) ∧ (Δ¹ s) ↦ f s ,
            (t ≡ 1₂) ∧ (Δ¹ s) ↦ g s ,
            (Δ¹ t) ∧ (s ≡ 0₂) ↦ x ,
            (Δ¹ t) ∧ (s ≡ 1₂) ↦ y])
  := ( d , triangle-to-square-section A x y f d α)

#def sigma-square-to-sigma-triangle-retraction
  ( A : U)
  ( x y : A)
  ( f : hom A x y)
  ( (g , σ) :
    Σ ( g : hom A x y) ,
      ( ( (t , s) : Δ¹×Δ¹) →
        A [ (t ≡ 0₂) ∧ (Δ¹ s) ↦ f s ,
            (t ≡ 1₂) ∧ (Δ¹ s) ↦ g s ,
            (Δ¹ t) ∧ (s ≡ 0₂) ↦ x ,
            (Δ¹ t) ∧ (s ≡ 1₂) ↦ y]))
  : Σ (d : hom A x y) , (hom2 A x y y f (id-hom A y) d)
  := ( (\ t → σ (t , t)) , (\ (t , s) → σ (s , t)))

#def sigma-triangle-to-sigma-square-retract
  ( A : U)
  ( x y : A)
  ( f : hom A x y)
  : is-retract-of
      ( Σ (d : hom A x y) , (hom2 A x y y f (id-hom A y) d))
      ( Σ ( g : hom A x y) ,
          ( ( (t , s) : Δ¹×Δ¹) →
            A [ (t ≡ 0₂) ∧ (Δ¹ s) ↦ f s ,
                (t ≡ 1₂) ∧ (Δ¹ s) ↦ g s ,
                (Δ¹ t) ∧ (s ≡ 0₂) ↦ x ,
                (Δ¹ t) ∧ (s ≡ 1₂) ↦ y]))
  :=
    ( ( sigma-triangle-to-sigma-square-section A x y f) ,
      ( ( sigma-square-to-sigma-triangle-retraction A x y f) ,
        ( \ dα → refl)))
```

We can now verify the Segal condition in the case of composable pairs in which
the second arrow is an identity.

```rzk
#def is-contr-hom2-with-id-is-discrete uses (extext)
  ( A : U)
  ( is-discrete-A : is-discrete A)
  ( x y : A)
  ( f : hom A x y)
  : is-contr ( Σ (d : hom A x y) , (hom2 A x y y f (id-hom A y) d))
  :=
    is-contr-is-retract-of-is-contr
      ( Σ ( d : hom A x y) , (hom2 A x y y f (id-hom A y) d))
      ( Σ ( g : hom A x y) ,
          ( ( (t , s) : Δ¹×Δ¹) →
            A [ (t ≡ 0₂) ∧ (Δ¹ s) ↦ f s ,
                (t ≡ 1₂) ∧ (Δ¹ s) ↦ g s ,
                (Δ¹ t) ∧ (s ≡ 0₂) ↦ x ,
                (Δ¹ t) ∧ (s ≡ 1₂) ↦ y]))
      ( sigma-triangle-to-sigma-square-retract A x y f)
      ( is-contr-horn-refl-refl-extension-type A is-discrete-A x y f)
```

But since `#!rzk A` is discrete, its hom type family is equivalent to its
identity type family, and we can use "path induction" over arrows to reduce the
general case to the one just proven:

```rzk
#def is-contr-hom2-is-discrete uses (extext)
  ( A : U)
  ( is-discrete-A : is-discrete A)
  ( x y z : A)
  ( f : hom A x y)
  ( g : hom A y z)
  : is-contr (Σ (h : hom A x z) , hom2 A x y z f g h)
  :=
    ind-based-path
      ( A)
      ( y)
      ( \ w → hom A y w)
      ( \ w → hom-eq A y w)
      ( is-discrete-A y)
      ( \ w d → is-contr ( Σ (h : hom A x w) , hom2 A x y w f d h))
      ( is-contr-hom2-with-id-is-discrete A is-discrete-A x y f)
      ( z)
      ( g)
```

Finally, we conclude:

```rzk title="RS17, Proposition 7.3"
#def is-segal-is-discrete' uses (extext)
  ( A : U)
  ( is-discrete-A : is-discrete A)
  : is-segal A
  := is-contr-hom2-is-discrete A is-discrete-A
```
