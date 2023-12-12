# 4. Equivalences involving extension types

These formalisations correspond to Section 3 of the RS17 paper.

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Prerequisites

- `hott/03-equivalences.rzk.md` — contains the definitions of `#!rzk Equiv` and
  `#!rzk comp-equiv`

## Extension up to homotopy

For a shape inclusion `ϕ ⊂ ψ` and any type `A`, we have the inbuilt extension
types `(t : ψ) → A [ϕ t ↦ σ t]` (for every `σ : ϕ → A`).

We show that these extension types are equivalent to the fibers of the canonical
restriction map `(ψ → A) → (ϕ → A)`, which we can view as the types of
"extension up to homotopy".

```rzk
#section extensions-up-to-homotopy
#variable I : CUBE
#variable ψ : I → TOPE
#variable ϕ : ψ → TOPE
#variable A : (t : ψ) → U

#def extension-type
  ( σ : (t : ϕ) → A t)
  : U
  := (t : ψ) → A t [ϕ t ↦ σ t]

#def homotopy-extension-type
  ( σ : (t : ϕ) → A t)
  : U
  := fib ((t : ψ) → A t) ((t : ϕ) → A t) (\ τ t → τ t) (σ)

#def extension-type-weakening-map
  ( σ : (t : ϕ) → A t)
  : extension-type σ → homotopy-extension-type σ
  := \ τ → (τ , refl)

#def section-extension-type-weakening'
  : ( σ : (t : ϕ) → A t)
  → ( th : homotopy-extension-type σ)
  → Σ ( τ : extension-type σ) , ((τ , refl) =_{homotopy-extension-type σ} th)
  :=
    ind-fib ((t : ψ) → A t) ((t : ϕ) → A t) (\ τ t → τ t)
      ( \ σ th →
          Σ ( τ : extension-type σ)
          , ( τ , refl) =_{homotopy-extension-type σ} th)
      ( \ (τ : (t : ψ) → A t) → (τ , refl))

#def extension-strictification
  ( σ : (t : ϕ) → A t)
  : ( homotopy-extension-type σ) → (extension-type σ)
  :=
    \ th → first (section-extension-type-weakening' σ th)

#def has-section-extension-type-weakening
  ( σ : (t : ϕ) → A t)
  : has-section (extension-type σ) (homotopy-extension-type σ)
      ( extension-type-weakening-map σ)
  :=
    ( extension-strictification σ
    , \ th → (second (section-extension-type-weakening' σ th)))


#def is-equiv-extension-type-weakening
  ( σ : (t : ϕ) → A t)
  : is-equiv (extension-type σ) (homotopy-extension-type σ)
      ( extension-type-weakening-map σ)
  :=
    ( ( extension-strictification σ , \ _ → refl)
    , has-section-extension-type-weakening σ)

#def extension-type-weakening
  ( σ : (t : ϕ) → A t)
  : Equiv (extension-type σ) (homotopy-extension-type σ)
  := (extension-type-weakening-map σ , is-equiv-extension-type-weakening σ)

#end extensions-up-to-homotopy
```

This equivalence is functorial in the following sense:

```rzk
#def extension-type-weakening-functorial
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( A' A : (t : ψ) → U)
  ( α : (t : ψ) → A' t → A t)
  ( σ' : (t : ϕ) → A' t)
  : Equiv-of-maps
    ( extension-type I ψ ϕ A' σ')
    ( extension-type I ψ ϕ A (\ t → α t (σ' t)))
    ( \ τ' t → α t (τ' t))
    ( homotopy-extension-type I ψ ϕ A' σ')
    ( homotopy-extension-type I ψ ϕ A (\ t → α t (σ' t)))
    ( \ (τ' , p) →
      ( \ t → α t (τ' t)
      , ap
        ( ( t : ϕ) → A' t)
        ( ( t : ϕ) → A t)
        ( \ (t : ϕ) → τ' t)
        ( \ (t : ϕ) → σ' t)
        ( \ σ'' t → α t (σ'' t))
        ( p)))
  :=
    ( ( ( extension-type-weakening-map I ψ ϕ A' σ'
        , extension-type-weakening-map I ψ ϕ A (\ t → α t (σ' t)))
      , ( \ _ → refl))
    , ( is-equiv-extension-type-weakening I ψ ϕ A' σ'
      , is-equiv-extension-type-weakening I ψ ϕ A (\ t → α t (σ' t))))
```

## Commutation of arguments and currying

```rzk title="RS17, Theorem 4.1"
#def flip-ext-fun
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( X : U)
  ( Y : ψ → X → U)
  ( f : (t : ϕ) → (x : X) → Y t x)
  : Equiv
      ( ( t : ψ) → ((x : X) → Y t x) [ϕ t ↦ f t])
      ( ( x : X) → (t : ψ) → Y t x [ϕ t ↦ f t x])
  :=
    ( ( \ g x t → g t x)
    , ( ( \ h t x → (h x) t , \ g → refl)
      , ( \ h t x → (h x) t , \ h → refl)))

#def flip-ext-fun-inv
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( X : U)
  ( Y : ψ → X → U)
  ( f : (t : ϕ) → (x : X) → Y t x)
  : Equiv
    ( ( x : X) → (t : ψ) → Y t x [ϕ t ↦ f t x])
    ( ( t : ψ) → ((x : X) → Y t x) [ϕ t ↦ f t])
  :=
    ( ( \ h t x → (h x) t)
    , ( ( \ g x t → g t x , \ h → refl)
      , ( \ g x t → g t x , \ g → refl)))
```

```rzk title="RS17, Theorem 4.2"
#def curry-uncurry
  ( I J : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( ζ : J → TOPE)
  ( χ : ζ → TOPE)
  ( X : ψ → ζ → U)
  ( f : ((t , s) : I × J | (ϕ t ∧ ζ s) ∨ (ψ t ∧ χ s)) → X t s)
  : Equiv
    ( ( t : ψ)
    → ( ( s : ζ) → X t s [χ s ↦ f (t , s)])
      [ ϕ t ↦ \ s → f (t , s)])
    ( ( ( t , s) : I × J | ψ t ∧ ζ s)
    → ( X t s [(ϕ t ∧ ζ s) ∨ (ψ t ∧ χ s) ↦ f (t , s)]))
  :=
    ( ( \ g (t , s) → (g t) s)
    , ( ( \ h t s → h (t , s) , \ g → refl)
      , ( \ h t s → h (t , s) , \ h → refl)))

#def uncurry-opcurry
  ( I J : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( ζ : J → TOPE)
  ( χ : ζ → TOPE)
  ( X : ψ → ζ → U)
  ( f : ((t , s) : I × J | (ϕ t ∧ ζ s) ∨ (ψ t ∧ χ s)) → X t s)
  : Equiv
    ( ( ( t , s) : I × J | ψ t ∧ ζ s)
    → ( X t s [(ϕ t ∧ ζ s) ∨ (ψ t ∧ χ s) ↦ f (t , s)]))
    ( ( s : ζ)
    → ( ( t : ψ) → X t s [ϕ t ↦ f (t , s)])
      [ χ s ↦ \ t → f (t , s)])
  :=
    ( ( \ h s t → h (t , s))
    , ( ( \ g (t , s) → (g s) t , \ h → refl)
      , ( \ g (t , s) → (g s) t , \ g → refl)))

#def fubini
  ( I J : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( ζ : J → TOPE)
  ( χ : ζ → TOPE)
  ( X : ψ → ζ → U)
  ( f : ((t , s) : I × J | (ϕ t ∧ ζ s) ∨ (ψ t ∧ χ s)) → X t s)
  : Equiv
    ( ( t : ψ)
    → ( ( s : ζ) → X t s [χ s ↦ f (t , s)]) [ϕ t ↦ \ s → f (t , s)])
    ( ( s : ζ)
    → ( ( t : ψ) → X t s [ϕ t ↦ f (t , s)]) [χ s ↦ \ t → f (t , s)])
  :=
    equiv-comp
      ( ( t : ψ)
      → ( ( s : ζ) → X t s [χ s ↦ f (t , s)]) [ϕ t ↦ \ s → f (t , s)])
      ( ( ( t , s) : I × J | ψ t ∧ ζ s)
      → X t s [(ϕ t ∧ ζ s) ∨ (ψ t ∧ χ s) ↦ f (t , s)])
      ( ( s : ζ)
      → ( ( t : ψ) → X t s [ϕ t ↦ f (t , s)]) [χ s ↦ \ t → f (t , s)])
      ( curry-uncurry I J ψ ϕ ζ χ X f)
      ( uncurry-opcurry I J ψ ϕ ζ χ X f)
```

### Functorial instances

For each of these we provide a corresponding functorial instance

```rzk
#def flip-ext-fun-functorial
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( X : U)
  ( A' A : ψ → X → U)
  ( α : (t : ψ) → (x : X) → A' t x → A t x)
  ( σ' : (t : ϕ) → (x : X) → A' t x)
  : Equiv-of-maps
    ( ( t : ψ) → ((x : X) → A' t x) [ϕ t ↦ σ' t])
    ( ( t : ψ) → ((x : X) → A t x) [ϕ t ↦ \ x → α t x (σ' t x)])
    ( \ τ t x → α t x (τ t x))
    ( ( x : X) → (t : ψ) → A' t x [ϕ t ↦ σ' t x])
    ( ( x : X) → (t : ψ) → A t x [ϕ t ↦ α t x (σ' t x)])
    ( \ τ x t → α t x (τ x t))
  :=
    ( ( ( first (flip-ext-fun I ψ ϕ X A' σ')
        , first (flip-ext-fun I ψ ϕ X A (\ t x → α t x (σ' t x))))
      , ( \ _ → refl))
    , ( second (flip-ext-fun I ψ ϕ X A' σ')
      , second (flip-ext-fun I ψ ϕ X A (\ t x → α t x (σ' t x)))))


#def curry-uncurry-functorial
  ( I J : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( ζ : J → TOPE)
  ( χ : ζ → TOPE)
  ( A' A : ψ → ζ → U)
  ( α : (t : ψ) → (s : ζ) → A' t s → A t s)
  ( σ' : ((t , s) : I × J | (ϕ t ∧ ζ s) ∨ (ψ t ∧ χ s)) → A' t s)
  : Equiv-of-maps
    ( ( t : ψ)
    → ( ( s : ζ) → A' t s [χ s ↦ σ' (t , s)])
      [ ϕ t ↦ \ s → σ' (t , s)])
    ( ( t : ψ)
    → ( ( s : ζ) → A t s [χ s ↦ α t s (σ' (t , s))])
      [ ϕ t ↦ \ s → α t s (σ' (t , s))])
    ( \ τ' t s → α t s (τ' t s))
    ( ( ( t , s) : I × J | ψ t ∧ ζ s)
    → ( A' t s) [ (ϕ t ∧ ζ s) ∨ (ψ t ∧ χ s) ↦ σ' (t , s)])
    ( ( ( t , s) : I × J | ψ t ∧ ζ s)
    → ( A t s) [ (ϕ t ∧ ζ s) ∨ (ψ t ∧ χ s) ↦ α t s (σ' (t , s))])
    ( \ uτ' (t , s) → α t s (uτ' (t , s)))
  :=
  ( ( ( first (curry-uncurry I J ψ ϕ ζ χ A' σ')
      , first (curry-uncurry I J ψ ϕ ζ χ A (\ (t , s) → α t s (σ' (t , s)))))
    , ( \ _ → refl))
  , ( second (curry-uncurry I J ψ ϕ ζ χ A' σ')
    , second (curry-uncurry I J ψ ϕ ζ χ A (\ (t , s) → α t s (σ' (t , s))))))

#def uncurry-opcurry-functorial
  ( I J : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( ζ : J → TOPE)
  ( χ : ζ → TOPE)
  ( A' A : ψ → ζ → U)
  ( α : (t : ψ) → (s : ζ) → A' t s → A t s)
  ( σ' : ((t , s) : I × J | (ϕ t ∧ ζ s) ∨ (ψ t ∧ χ s)) → A' t s)
  : Equiv-of-maps
    ( ( ( t , s) : I × J | ψ t ∧ ζ s)
    → ( A' t s) [ (ϕ t ∧ ζ s) ∨ (ψ t ∧ χ s) ↦ σ' (t , s)])
    ( ( ( t , s) : I × J | ψ t ∧ ζ s)
    → ( A t s) [ (ϕ t ∧ ζ s) ∨ (ψ t ∧ χ s) ↦ α t s (σ' (t , s))])
    ( \ uτ' (t , s) → α t s (uτ' (t , s)))
    ( ( s : ζ)
    → ( ( t : ψ) → A' t s [ϕ t ↦ σ' (t , s)])
      [ χ s ↦ \ t → σ' (t , s)])
    ( ( s : ζ)
    → ( ( t : ψ) → A t s [ϕ t ↦ α t s (σ' (t , s))])
      [ χ s ↦ \ t → α t s (σ' (t , s))])
    ( \ τ' s t → α t s (τ' s t))
  :=
  ( ( ( first (uncurry-opcurry I J ψ ϕ ζ χ A' σ')
      , first (uncurry-opcurry I J ψ ϕ ζ χ A (\ (t , s) → α t s (σ' (t , s)))))
    , ( \ _ → refl))
  , ( second (uncurry-opcurry I J ψ ϕ ζ χ A' σ')
    , second (uncurry-opcurry I J ψ ϕ ζ χ A (\ (t , s) → α t s (σ' (t , s))))))

#def fubini-functorial
  ( I J : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( ζ : J → TOPE)
  ( χ : ζ → TOPE)
  ( A' A : ψ → ζ → U)
  ( α : (t : ψ) → (s : ζ) → A' t s → A t s)
  ( σ' : ((t , s) : I × J | (ϕ t ∧ ζ s) ∨ (ψ t ∧ χ s)) → A' t s)
  : Equiv-of-maps
    ( ( t : ψ)
    → ( ( s : ζ) → A' t s [χ s ↦ σ' (t , s)])
      [ ϕ t ↦ \ s → σ' (t , s)])
    ( ( t : ψ)
    → ( ( s : ζ) → A t s [χ s ↦ α t s (σ' (t , s))])
      [ ϕ t ↦ \ s → α t s (σ' (t , s))])
    ( \ τ' t s → α t s (τ' t s))
    ( ( s : ζ)
    → ( ( t : ψ) → A' t s [ϕ t ↦ σ' (t , s)])
      [ χ s ↦ \ t → σ' (t , s)])
    ( ( s : ζ)
    → ( ( t : ψ) → A t s [ϕ t ↦ α t s(σ' (t , s))])
      [ χ s ↦ \ t → α t s (σ' (t , s))])
    ( \ τ' s t → α t s (τ' s t))
  :=
  ( ( ( first (fubini I J ψ ϕ ζ χ A' σ')
      , first (fubini I J ψ ϕ ζ χ A (\ (t , s) → α t s (σ' (t , s)))))
    , ( \ _ → refl))
  , ( second (fubini I J ψ ϕ ζ χ A' σ')
    , second (fubini I J ψ ϕ ζ χ A (\ (t , s) → α t s (σ' (t , s))))))
```

## Extending into Σ-types (the non-axiom of choice)

```rzk title="RS17, Theorem 4.3"
#def axiom-choice
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( X : ψ → U)
  ( Y : (t : ψ) → (x : X t) → U)
  ( a : (t : ϕ) → X t)
  ( b : (t : ϕ) → Y t (a t))
  : Equiv
    ( ( t : ψ) → (Σ (x : X t) , Y t x) [ϕ t ↦ (a t , b t)])
    ( Σ ( f : ((t : ψ) → X t [ϕ t ↦ a t]))
      , ( ( t : ψ) → Y t (f t) [ϕ t ↦ b t]))
  :=
      ( ( \ g → (\ t → (first (g t)) , \ t → second (g t)))
      , ( ( \ (f , h) t → (f t , h t) , \ _ → refl)
        , ( \ (f , h) t → (f t , h t) , \ _ → refl)))

#def inv-equiv-axiom-choice
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( X : ψ → U)
  ( Y : (t : ψ) → (x : X t) → U)
  ( a : (t : ϕ) → X t)
  ( b : (t : ϕ) → Y t (a t))
  : Equiv
    ( Σ ( f : ((t : ψ) → X t [ϕ t ↦ a t]))
      , ( ( t : ψ) → Y t (f t) [ϕ t ↦ b t]))
    ( ( t : ψ) → (Σ (x : X t) , Y t x) [ϕ t ↦ (a t , b t)])
  :=
    inv-equiv
    ( ( t : ψ) → (Σ (x : X t) , Y t x) [ϕ t ↦ (a t , b t)])
    ( Σ ( f : ((t : ψ) → X t [ϕ t ↦ a t]))
      , ( ( t : ψ) → Y t (f t) [ϕ t ↦ b t]))
    ( axiom-choice I ψ ϕ X Y a b)
```

## Composites and unions of cofibrations

The original form.

```rzk title="RS17, Theorem 4.4"
#def cofibration-composition
  ( I : CUBE)
  ( χ : I → TOPE)
  ( ψ : χ → TOPE)
  ( ϕ : ψ → TOPE)
  ( X : χ → U)
  ( a : (t : ϕ) → X t)
  : Equiv
    ( ( t : χ) → X t [ϕ t ↦ a t])
    ( Σ ( f : (t : ψ) → X t [ϕ t ↦ a t])
      , ( ( t : χ) → X t [ψ t ↦ f t]))
  :=
    ( ( \ h → (\ t → h t , \ t → h t))
    , ( ( \ (_ , g) t → g t , \ _ → refl)
      , ( ( \ (_ , g) t → g t , \ _ → refl))))
```

A reformulated version via tope disjunction instead of inclusion (see
<https://github.com/rzk-lang/rzk/issues/8>).

```rzk title="RS17, Theorem 4.4"
#def cofibration-composition'
  ( I : CUBE)
  ( χ ψ ϕ : I → TOPE)
  ( X : χ → U)
  ( a : (t : I | χ t ∧ ψ t ∧ ϕ t) → X t)
  : Equiv
      ( ( t : χ) → X t [χ t ∧ ψ t ∧ ϕ t ↦ a t])
      ( Σ ( f : (t : I | χ t ∧ ψ t) → X t [χ t ∧ ψ t ∧ ϕ t ↦ a t])
        , ( ( t : χ) → X t [χ t ∧ ψ t ↦ f t]))
  :=
    ( ( \ h → (\ t → h t , \ t → h t))
    , ( ( \ (_ , g) t → g t , \ _ → refl)
      , ( \ (_ , g) t → g t , \ _ → refl)))
```

Another variant is the following:

```rzk
#def cofibration-composition''
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ χ : ψ → TOPE)
  ( A : ψ → U)
  ( a : (t : I | ϕ t) → A t)
  : Equiv
    ( ( t : ψ) → A t [ϕ t ↦ a t])
    ( Σ ( b : (t : I | χ t) → A t [χ t ∧ ϕ t ↦ a t])
      , ( t : ψ) → A t [χ t ↦ b t , ϕ t ↦ a t])
  :=
  ( \ c → (\ t → c t , \ t → c t)
  , ( ( \ (_ , c) t → c t
      , \ _ → refl)
    , ( \ (_ , c) t → c t
      , \ _ → refl)))
```

```rzk title="RS17, Theorem 4.5"
#def cofibration-union
  ( I : CUBE)
  ( ϕ ψ : I → TOPE)
  ( X : (t : I | ϕ t ∨ ψ t) → U)
  ( a : (t : ψ) → X t)
  : Equiv
      ( ( t : I | ϕ t ∨ ψ t) → X t [ψ t ↦ a t])
      ( ( t : ϕ) → X t [ϕ t ∧ ψ t ↦ a t])
  :=
    ( \ h t → h t
    , ( ( \ g t → recOR (ϕ t ↦ g t , ψ t ↦ a t) , \ _ → refl)
      , ( \ g t → recOR (ϕ t ↦ g t , ψ t ↦ a t) , \ _ → refl)))
```

### Functorial instances

```rzk
#def cofibration-composition-functorial
  ( I : CUBE)
  ( χ : I → TOPE)
  ( ψ : χ → TOPE)
  ( ϕ : ψ → TOPE)
  ( A' A : χ → U)
  ( α : (t : χ) → A' t → A t)
  ( σ' : (t : ϕ) → A' t)
  : Equiv-of-maps
    ( ( t : χ) → A' t [ϕ t ↦ σ' t])
    ( ( t : χ) → A t [ϕ t ↦ α t (σ' t)])
    ( \ τ' t → α t (τ' t))
    ( Σ ( τ' : (t : ψ) → A' t [ϕ t ↦ σ' t])
      , ( ( t : χ) → A' t [ψ t ↦ τ' t]))
    ( Σ ( τ : (t : ψ) → A t [ϕ t ↦ α t (σ' t)])
      , ( ( t : χ) → A t [ψ t ↦ τ t]))
    ( \ (τ' , υ') → (\ t → α t (τ' t) , \ t → α t (υ' t)))
  :=
    ( ( ( \ h → (\ t → h t , \ t → h t) , \ h → (\ t → h t , \ t → h t))
      , ( \ _ → refl))
    , ( ( ( \ (_f , g) t → g t , \ h → refl)
        , ( ( \ (_f , g) t → g t , \ h → refl)))
      , ( ( \ (_f , g) t → g t , \ h → refl)
        , ( ( \ (_f , g) t → g t , \ h → refl)))))

#def cofibration-composition-functorial''
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ χ : ψ → TOPE)
  ( A' A : (t : I | ϕ t ∨ ψ t) → U)
  ( α : (t : I | ϕ t ∨ ψ t) → A' t → A t)
  ( a' : (t : I | ϕ t) → A' t)
  : Equiv-of-maps
    ( ( t : ψ) → A' t [ϕ t ↦ a' t])
    ( ( t : ψ) → A t [ϕ t ↦ α t (a' t)])
    ( \ c t → α t (c t))
    ( Σ ( b' : (t : I | χ t) → A' t [χ t ∧ ϕ t ↦ a' t])
      , ( t : ψ) → A' t [χ t ↦ b' t , ϕ t ↦ a' t])
    ( Σ ( b : (t : I | χ t) → A t [χ t ∧ ϕ t ↦ α t (a' t)])
      , ( t : ψ) → A t [χ t ↦ b t , ϕ t ↦ α t (a' t)])
    ( \ (b , c) → (\ t → α t (b t) , \ t → α t (c t)))
  :=
  ( ( ( first (cofibration-composition'' I ψ ϕ χ A' a')
      , first (cofibration-composition'' I ψ ϕ χ A (\ t → α t (a' t))))
    , \ _ → refl)
  , ( second (cofibration-composition'' I ψ ϕ χ A' a')
    , second (cofibration-composition'' I ψ ϕ χ A (\ t → α t (a' t)))))

#def cofibration-union-functorial
  ( I : CUBE)
  ( ϕ ψ : I → TOPE)
  ( A' A : (t : I | ϕ t ∨ ψ t) → U)
  ( α : (t : I | ϕ t ∨ ψ t) → A' t → A t)
  ( τ' : (t : ψ) → A' t)
  : Equiv-of-maps
      ( ( t : I | ϕ t ∨ ψ t) → A' t [ψ t ↦ τ' t])
      ( ( t : I | ϕ t ∨ ψ t) → A t [ψ t ↦ α t (τ' t)])
      ( \ υ' t → α t (υ' t))
      ( ( t : ϕ) → A' t [ϕ t ∧ ψ t ↦ τ' t])
      ( ( t : ϕ) → A t [ϕ t ∧ ψ t ↦ α t (τ' t)])
      ( \ ν' t → α t (ν' t))
  :=
     ( ( ( \ υ' t → υ' t , \ υ t → υ t)
       , ( \ _ → refl))
     , ( ( second (cofibration-union I ϕ ψ A' τ'))
       , ( second (cofibration-union I ϕ ψ A (\ t → α t (τ' t))))))
```

## Extension extensionality

There are various equivalent forms of the relative function extensionality axiom
for extension types. One form corresponds to the standard weak function
extensionality. As suggested by footnote 8, we refer to this as a "weak
extension extensionality" axiom.

```rzk title="RS17, Axiom 4.6, Weak extension extensionality"
#define WeakExtExt
  : U
  := (I : CUBE) → (ψ : I → TOPE) → (ϕ : ψ → TOPE) → (A : ψ → U)
   → ( is-locally-contr-A : (t : ψ) → is-contr (A t))
   → ( a : (t : ϕ) → A t) → is-contr ((t : ψ) → A t [ϕ t ↦ a t])
```

We refer to another form as an "extension extensionality" axiom.

```rzk
#def ext-htpy-eq
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( A : ψ → U)
  ( a : (t : ϕ) → A t)
  ( f g : (t : ψ) → A t [ϕ t ↦ a t])
  ( p : f = g)
  : ( t : ψ) → (f t = g t) [ϕ t ↦ refl]
  :=
    ind-path
      ( ( t : ψ) → A t [ϕ t ↦ a t])
      ( f)
      ( \ g' p' → (t : ψ) → (f t = g' t) [ϕ t ↦ refl])
      ( \ _ → refl)
      ( g)
      ( p)
```

```rzk title="RS17, Proposition 4.8(ii)"
#def ExtExt
  : U
  :=
    ( ( I : CUBE)
    → ( ψ : I → TOPE)
    → ( ϕ : ψ → TOPE)
    → ( A : ψ → U)
    → ( a : (t : ϕ) → A t)
    → ( f : (t : ψ) → A t [ϕ t ↦ a t])
    → ( g : (t : ψ) → A t [ϕ t ↦ a t])
    → is-equiv
      ( f = g)
      ( ( t : ψ) → (f t = g t) [ϕ t ↦ refl])
      ( ext-htpy-eq I ψ ϕ A a f g))
```

```rzk title="The equivalence provided by extension extensionality"
#def equiv-ExtExt
  ( extext : ExtExt)
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( A : ψ → U)
  ( a : (t : ϕ) → A t)
  ( f g : (t : ψ) → A t [ϕ t ↦ a t])
  : Equiv (f = g) ((t : ψ) → (f t = g t) [ϕ t ↦ refl])
  := (ext-htpy-eq I ψ ϕ A a f g , extext I ψ ϕ A a f g)
```

### Naive extension extensionality

For readability of code, it is useful to the function that supplies an equality
between terms of an extension type from a pointwise equality extending refl. In
fact, sometimes only this weaker form of the axiom is needed.

```rzk
#def NaiveExtExt
  : U
  :=
  ( ( I : CUBE)
  → ( ψ : I → TOPE)
  → ( ϕ : ψ → TOPE)
  → ( A : ψ → U)
  → ( a : (t : ϕ) → A t)
  → ( f : (t : ψ) → A t [ϕ t ↦ a t])
  → ( g : (t : ψ) → A t [ϕ t ↦ a t])
  → ( ( t : ψ) → (f t = g t) [ϕ t ↦ refl])
  → ( f = g))

#def naiveextext-extext
  ( extext : ExtExt)
  : NaiveExtExt
  := \ I ψ ϕ A a f g → (first (first (extext I ψ ϕ A a f g)))
```

We show that naive extension extensionality implies weak extension
extensionality. On the way, we obtain another useful version of extension
extensionality, stating that all extension types in a proposition are
propositions.

```rzk
#section weakextext-naiveextext
#variable naiveextext : NaiveExtExt

#def is-prop-shape-type-is-locally-prop uses (naiveextext)
  ( I : CUBE)
  ( ϕ : I → TOPE)
  ( A : ϕ → U)
  ( is-locally-prop-A : (t : ϕ) → is-prop (A t))
  : is-prop ((t : ϕ) → A t)
  :=
    is-prop-all-elements-equal ((t : ϕ) → A t)
    ( \ a a' →
      naiveextext I (\ t → ϕ t) (\ _ → ⊥) (\ t → A t) (\ _ → recBOT) a a'
      ( \ t → first (is-locally-prop-A t (a t) (a' t))))

#def is-prop-extension-type-is-locally-prop uses (naiveextext)
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( A : ψ → U)
  ( is-locally-prop-A : (t : ψ) → is-prop (A t))
  : ( a : (t : ϕ) → A t) → is-prop ((t : ψ) → A t [ϕ t ↦ a t])
  :=
    is-fiberwise-prop-is-prop-total-type-is-prop-base
    ( ( t : ϕ) → A t)
    ( is-prop-shape-type-is-locally-prop I (\ t → ϕ t) (\ t → A t)
      ( \ t → is-locally-prop-A t))
    ( \ a → (t : ψ) → A t [ϕ t ↦ a t])
    ( is-prop-Equiv-is-prop'
      ( ( t : ψ) → A t)
      ( Σ ( a : (t : ϕ) → A t) , (t : ψ) → A t [ϕ t ↦ a t])
      ( cofibration-composition I ψ ϕ (\ _ → BOT) (\ t → A t) (\ _ → recBOT))
      ( is-prop-shape-type-is-locally-prop I ψ A is-locally-prop-A))
```

Still using `naiveextext`, in a fiberwise contractible family, every extension
type is always inhabited.

```rzk
#def is-inhabited-extension-type-is-locally-contr uses (naiveextext)
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( A : ψ → U)
  ( is-locally-contr-A : (t : ψ) → is-contr (A t))
  ( a : (t : ϕ) → A t)
  : ( t : ψ) → A t [ϕ t ↦ a t]
  :=
    extension-strictification I ψ ϕ A a
    ( \ (t : ψ) → first (is-locally-contr-A t)
    , naiveextext I (\ t → ϕ t) (\ _ → BOT) (\ t → A t) (\ _ → recBOT)
      ( \ (t : ϕ) → first (is-locally-contr-A t))
      ( \ (t : ϕ) → a t)
      ( \ (t : ϕ) → second (is-locally-contr-A t) (a t)))

#end weakextext-naiveextext
```

We conclude that naive extension extensionality implies weak extension
extensionality.

```rzk
#def weakextext-naiveextext
  : NaiveExtExt → WeakExtExt
  :=
    \ naiveextext I ψ ϕ A is-locally-contr-A a →
    ( is-contr-is-inhabited-is-prop
      ( ( t : ψ) → A t [ϕ t ↦ a t])
      ( is-prop-extension-type-is-locally-prop naiveextext
        ( I) (ψ) (ϕ) (A)
        ( \ t → is-prop-is-contr (A t) (is-locally-contr-A t))
        ( a))
      ( is-inhabited-extension-type-is-locally-contr naiveextext I ψ ϕ A
        ( is-locally-contr-A) (a)))
```

For convenience we also provide the composite implication from extension
extensionality to weak extension extensionality:

```rzk
#def weakextext-extext
  : ExtExt → WeakExtExt
  :=
    comp ExtExt NaiveExtExt WeakExtExt
    ( weakextext-naiveextext) (naiveextext-extext)
```

### Weak extension extensionality implies extension extensionality

Weak extension extensionality implies extension extensionality; this is the
context of RS17 Proposition 4.8 (i). We prove this in a series of lemmas. The
`ext-projection-temp` function is a (hopefully temporary) helper that explicitly
cases an extension type to a function type.

```rzk
#section rs-4-8

#variable  weakextext : WeakExtExt
#variable  I : CUBE
#variable  ψ : I → TOPE
#variable  ϕ : ψ → TOPE
#variable  A : ψ → U
#variable  a : (t : ϕ) → A t
#variable  f : (t : ψ) → A t [ϕ t ↦ a t]

#define ext-projection-temp uses (I ψ ϕ A a f)
  : ( ( t : ψ) → A t)
  := f

#define is-contr-ext-based-paths uses (weakextext f)
  : is-contr
    ( ( t : ψ)
    → ( Σ ( y : A t) , ((ext-projection-temp) t = y))
      [ ϕ t ↦ (a t , refl)])
  :=
    weakextext I ψ ϕ
    ( \ t → (Σ (y : A t) , ((ext-projection-temp) t = y)))
    ( \ t → is-contr-based-paths (A t) ((ext-projection-temp) t))
    ( \ t → (a t , refl))

#define is-contr-ext-endpoint-based-paths uses (weakextext f)
  : is-contr
    ( ( t : ψ)
    → ( Σ ( y : A t) , (y = ext-projection-temp t))
      [ ϕ t ↦ (a t , refl)])
  :=
    weakextext I ψ ϕ
    ( \ t → (Σ (y : A t) , y = ext-projection-temp t))
    ( \ t → is-contr-endpoint-based-paths (A t) (ext-projection-temp t))
    ( \ t → (a t , refl))

#define is-contr-based-paths-ext uses (weakextext)
  : is-contr
    ( Σ ( g : (t : ψ) → A t [ϕ t ↦ a t])
      , ( ( t : ψ) → (f t = g t) [ϕ t ↦ refl]))
  :=
    is-contr-equiv-is-contr
    ( ( t : ψ) → (Σ (y : A t)
                   , ( ( ext-projection-temp) t = y)) [ϕ t ↦ (a t , refl)])
    ( Σ ( g : (t : ψ) → A t [ϕ t ↦ a t])
              , ( t : ψ) → (f t = g t) [ϕ t ↦ refl])
    ( axiom-choice I ψ ϕ A
      ( \ t y → (ext-projection-temp) t = y)
      ( a)
      ( \ t → refl))
    ( is-contr-ext-based-paths)

#end rs-4-8
```

The map that defines extension extensionality

```rzk title="RS17 4.7"
#define extext-weakextext-map
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( A : ψ → U)
  ( a : (t : ϕ) → A t)
  ( f : (t : ψ) → A t [ϕ t ↦ a t])
  : ( ( Σ ( g : (t : ψ) → A t [ϕ t ↦ a t]) , (f = g))
    → ( Σ ( g : (t : ψ) → A t [ϕ t ↦ a t])
      , ( ( t : ψ) → (f t = g t) [ϕ t ↦ refl])))
  :=
    total-map
    ( ( t : ψ) → A t [ϕ t ↦ a t])
    ( \ g → (f = g))
    ( \ g → (t : ψ) → (f t = g t) [ϕ t ↦ refl])
    ( ext-htpy-eq I ψ ϕ A a f)
```

The total bundle version of extension extensionality

```rzk
#define extext-weakextext-bundle-version
  ( weakextext : WeakExtExt)
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( A : ψ → U)
  ( a : (t : ϕ) → A t)
  ( f : (t : ψ) → A t [ϕ t ↦ a t])
  : is-equiv
    ( ( Σ ( g : (t : ψ) → A t [ϕ t ↦ a t]) , (f = g)))
    ( Σ ( g : (t : ψ) → A t [ϕ t ↦ a t])
      , ( ( t : ψ) → (f t = g t) [ϕ t ↦ refl]))
    ( extext-weakextext-map I ψ ϕ A a f)
  :=
    is-equiv-are-contr
    ( Σ ( g : (t : ψ) → A t [ϕ t ↦ a t]) , (f = g))
    ( Σ ( g : (t : ψ) → A t [ϕ t ↦ a t])
    , ( ( t : ψ) → (f t = g t) [ϕ t ↦ refl]))
    ( is-contr-based-paths ((t : ψ) → A t [ϕ t ↦ a t]) (f))
    ( is-contr-based-paths-ext weakextext I ψ ϕ A a f)
    ( extext-weakextext-map I ψ ϕ A a f)
```

Finally, using equivalences between families of equivalences and bundles of
equivalences we have that weak extension extensionality implies extension
extensionality. The following is statement the as proved in RS17.

```rzk title="RS17 Prop 4.8(i) as proved"
#define extext-weakextext'
  ( weakextext : WeakExtExt)
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( A : ψ → U)
  ( a : (t : ϕ) → A t)
  ( f : (t : ψ) → A t [ϕ t ↦ a t])
  : ( ( g : (t : ψ) → A t [ϕ t ↦ a t])
    → is-equiv
        ( f = g)
        ( ( t : ψ) → (f t = g t) [ϕ t ↦ refl])
        ( ext-htpy-eq I ψ ϕ A a f g))
  := is-equiv-fiberwise-is-equiv-total
      ( ( t : ψ) → A t [ϕ t ↦ a t])
      ( \ g → (f = g))
      ( \ g → (t : ψ) → (f t = g t) [ϕ t ↦ refl])
      ( ext-htpy-eq I ψ ϕ A a f)
      ( extext-weakextext-bundle-version weakextext I ψ ϕ A a f)
```

The following is the literal statement of weak extension extensionality implying
extension extensionality that we get by extracting the fiberwise equivalence.

```rzk title="RS17 Proposition 4.8(i)"
#define extext-weakextext
  : WeakExtExt → ExtExt
  := extext-weakextext'
```

## Homotopy extension property

The homotopy extension property has the following signature. We state this
separately since below we will will show that this follows from extension
extensionality.

```rzk
#def instance-HtpyExtProperty
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( A : ψ → U)
  ( b : (t : ψ) → A t)
  ( a : (t : ϕ) → A t)
  ( e : (t : ϕ) → a t = b t)
  : U
  :=
    Σ ( a' : (t : ψ) → A t [ϕ t ↦ a t])
    , ( ( t : ψ) → (a' t =_{ A t} b t) [ϕ t ↦ e t])

#def HtpyExtProperty
  : U
  :=
    ( ( I : CUBE)
    → ( ψ : I → TOPE)
    → ( ϕ : ψ → TOPE)
    → ( A : ψ → U)
    → ( b : (t : ψ) → A t)
    → ( a : (t : ϕ) → A t)
    → ( e : (t : ϕ) → a t = b t)
    → ( instance-HtpyExtProperty I ψ ϕ A b a e))
```

If we assume weak extension extensionality, then then homotopy extension
property follows from a straightforward application of the axiom of choice to
the point of contraction for weak extension extensionality.

```rzk title="RS17 Proposition 4.10"
#define htpy-ext-prop-weakextext
  ( weakextext : WeakExtExt)
  : HtpyExtProperty
  :=
  \ I ψ ϕ A b a e →
    first
    ( axiom-choice I ψ ϕ A
      ( \ t y → y = b t)
      ( a)
      ( e))
    ( first
      ( weakextext I ψ ϕ
        ( \ t → (Σ (y : A t) , y = b t))
        ( \ t → is-contr-endpoint-based-paths (A t) (b t))
        ( \ t → (a t , e t))))
```

For completeness, we give a short direct proof that extension extensionality
also implies the homotopy extension property without passing through weak
extension extensionality.

```rzk
#def htpy-ext-prop-extext
  ( extext : ExtExt)
  : HtpyExtProperty
  :=
  \ I ψ ϕ A b a →
  ind-has-section-equiv (a = (\ (t : ϕ) → b t)) ((t : ϕ) → a t = b t)
  ( equiv-ExtExt extext I (\ t → ϕ t) (\ _ → BOT) (\ t → A t) (\ _ → recBOT)
    ( a) (\ (t : ϕ) → b t))
  ( instance-HtpyExtProperty I ψ ϕ A b a)
  ( \ e' →
    ind-rev-fib
    ( ( t : ψ) → A t) ((t : ϕ) → A t) (\ b' t → b' t)
    ( \ a' (b' , p) →
      instance-HtpyExtProperty I ψ ϕ A b' a'
      ( ext-htpy-eq I (\ t → ϕ t) (\ _ → BOT) (\ t → A t) (\ _ → recBOT)
        ( a') (\ (t : ϕ) → b' t) (p)))
    ( \ b' → (b' , \ _ → refl))
    ( a) (b , e'))
```

### Homotopy extension property and NaiveExtExt imply WeakExtExt

This section contains the original proof of RS17, Proposition 4.11 stating that
NaiveExtExt and HptyExtProperty jointly imply WeakExtExt. In light of
`weakextext-naiveextext`, this is now redundant. We keep it around since some
intermediate statements might still be useful.

In an extension type of a dependent type that is pointwise contractible, then we
have an inhabitant of the extension type witnessing the contraction, at every
inhabitant of the base, of each point in the fiber to the center of the fiber.
Both directions of this statement will be needed.

```rzk
#def eq-ext-is-contr
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( A : ψ → U)
  ( a : (t : ϕ) → A t)
  ( is-contr-fiberwise-A : (t : ψ) → is-contr (A t))
  : ( t : ϕ) → ((first (is-contr-fiberwise-A t)) = a t)
  := \ t → (second (is-contr-fiberwise-A t) (a t))

#def codomain-eq-ext-is-contr
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( A : ψ → U)
  ( a : (t : ϕ) → A t)
  ( is-contr-fiberwise-A : (t : ψ) → is-contr (A t))
  : ( t : ϕ) → (a t = first (is-contr-fiberwise-A t))
  :=
    \ t →
      rev
      ( A t)
      ( first (is-contr-fiberwise-A t))
      ( a t)
      ( second (is-contr-fiberwise-A t) (a t))
```

The below gives us the inhabitant
$(a', e')
: \sum_{\left\langle\prod_{t : I|\psi} A (t) \biggr|^\phi_a\right\rangle}
\left\langle \prod_{t: I |\psi} a'(t) = b(t)\biggr|^\phi_e \right\rangle$
from the first part of the proof of RS Prop 4.11. It amounts to the fact that
parameterized contractibility, i.e. `#!rzk A : ψ → U` such that each `A t` is
contractible, implies the hypotheses of the homotopy extension property are
satisfied, and so assuming homotopy extension property, we are entitled to the
conclusion.

```rzk
#define htpy-ext-prop-is-fiberwise-contr
  ( htpy-ext-property : HtpyExtProperty)
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( A : ψ → U)
  ( a : (t : ϕ) → A t)
  ( is-contr-fiberwise-A : (t : ψ) → is-contr (A t))
  : Σ ( a' : (t : ψ) → A t [ϕ t ↦ a t])
    , ( ( t : ψ)
      → ( ( a' t) =_{ A t} first (is-contr-fiberwise-A t))
        [ ϕ t ↦ codomain-eq-ext-is-contr I ψ ϕ A a is-contr-fiberwise-A t])
  :=
    htpy-ext-property I ψ ϕ A
    ( \ t → first (is-contr-fiberwise-A t))
    ( a)
    ( codomain-eq-ext-is-contr I ψ ϕ A a is-contr-fiberwise-A)
```

The expression below give us the inhabitant `#!rzk c : (t : ψ) → f t = a' t`
used in the proof of RS Proposition 4.11. It follows from a more general
statement about the contractibility of identity types, but it is unclear if that
generality is needed.

```rzk
#define RS-4-11-c
  ( htpy-ext-prop : HtpyExtProperty)
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( A : ψ → U)
  ( a : (t : ϕ) → A t)
  ( f : (t : ψ) → A t [ϕ t ↦ a t])
  ( is-contr-fiberwise-A : (t : ψ) → is-contr (A t))
  : ( t : ψ)
  → ( f t
    = first
      ( htpy-ext-prop-is-fiberwise-contr
        htpy-ext-prop
        I ψ ϕ A a
        is-contr-fiberwise-A)
      ( t))
  :=
    \ t →
    all-elements-equal-is-contr
    ( A t)
    ( is-contr-fiberwise-A t)
    ( f t)
    ( ( first
        ( htpy-ext-prop-is-fiberwise-contr
          htpy-ext-prop
          I ψ ϕ A a
          is-contr-fiberwise-A))
      ( t))
```

And below proves that `#!rzk c(t) = refl`. Again, this is a consequence of a
slightly more general statement.

```rzk
#define RS-4-11-c-is-refl
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( A : ψ → U)
  ( is-fiberwise-contr : (t : ψ) → is-contr (A t))
  ( a : (t : ϕ) → A t)
  ( f : (t : ψ) → A t [ϕ t ↦ a t])
  ( a' : (t : ψ) → A t [ϕ t ↦ a t])
  ( c : (t : ψ) → (f t = a' t))
  : ( t : ϕ) → (refl =_{f t = a' t} c t)
  := \ t →
    all-paths-equal-is-contr
    ( A t) (is-fiberwise-contr t)
    ( f t) (a' t) (refl) (c t)
```

Given the `#!rzk a'` produced above, the following gives an inhabitant of
$\left \langle_{t : I |\psi}
f(t) = a'(t) \biggr|^\phi_{\lambda t.refl} \right\rangle$

```rzk
#define is-fiberwise-contr-ext-is-fiberwise-contr
  ( htpy-ext-prop : HtpyExtProperty)
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( A : ψ → U)
  ( is-contr-fiberwise-A : (t : ψ) → is-contr (A t))
  ( a : (t : ϕ) → A t)
  ( f : (t : ψ) → A t [ϕ t ↦ a t])
  : ( t : ψ)
    → ( f t = (first
              ( htpy-ext-prop-is-fiberwise-contr
                htpy-ext-prop I ψ ϕ A a is-contr-fiberwise-A)) t)[ϕ t ↦ refl]
  :=
  first(
    htpy-ext-prop I ψ ϕ
    ( \ t →
      ( ( f t)
      = first
        ( htpy-ext-prop-is-fiberwise-contr
          htpy-ext-prop
          I ψ ϕ A a
          is-contr-fiberwise-A)
        ( t)))
    ( RS-4-11-c
      htpy-ext-prop I ψ ϕ A a f is-contr-fiberwise-A)
    ( \ t → refl)
    ( RS-4-11-c-is-refl I ψ ϕ A
      ( is-contr-fiberwise-A)
      ( a)
      ( f)
      ( first
        ( htpy-ext-prop-is-fiberwise-contr
          htpy-ext-prop
          I ψ ϕ A a
          is-contr-fiberwise-A))
      ( RS-4-11-c
        ( htpy-ext-prop)
        ( I) (ψ) (ϕ) (A) (a) (f)
        ( is-contr-fiberwise-A))))
```

```rzk title="RS17, Proposition 4.11"
#define weak-extext-naiveextext-htpy-ext-property
 ( naiveextext : NaiveExtExt)
 ( htpy-ext-prop : HtpyExtProperty)
  : WeakExtExt
  := \ I ψ ϕ A is-contr-fiberwise-A a →
    ( first (htpy-ext-prop-is-fiberwise-contr htpy-ext-prop I ψ ϕ A a is-contr-fiberwise-A)
   , \ f →
      rev
      ( ( t : ψ) → A t [ϕ t ↦ a t])
      ( f)
      ( first (htpy-ext-prop-is-fiberwise-contr
                htpy-ext-prop I ψ ϕ A a is-contr-fiberwise-A))
      ( naiveextext I ψ ϕ A a f
      ( first (htpy-ext-prop-is-fiberwise-contr
                htpy-ext-prop I ψ ϕ A a is-contr-fiberwise-A))
      ( is-fiberwise-contr-ext-is-fiberwise-contr
        ( htpy-ext-prop)
        ( I) (ψ) (ϕ) (A)
        ( is-contr-fiberwise-A)
        ( a)
        ( f))))
```

## Applications of extension extensionality

We now assume extension extensionality and derive a few consequences.

```rzk
#assume extext : ExtExt
```

### Pointwise homotopy extension types

Using `ExtExt` we can write the homotopy in the homotopy extension type
pointwise.

```rzk
#section pointwise-homotopy-extension-type

#variable I : CUBE
#variable ψ : I → TOPE
#variable ϕ : ψ → TOPE
#variable A : ψ → U

#def pointwise-homotopy-extension-type
  ( σ : (t : ϕ) → A t)
  : U
  :=
    Σ ( τ : (t : ψ) → A t)
    , ( ( t : ϕ) → (τ t =_{ A t} σ t))

#def equiv-pointwise-homotopy-extension-type uses (extext)
  ( σ : (t : ϕ) → A t)
  : Equiv
    ( homotopy-extension-type I ψ ϕ A σ)
    ( pointwise-homotopy-extension-type σ)
  :=
    total-equiv-family-of-equiv
    ( ( t : ψ) → A t)
    ( \ τ → (\ t → τ t) =_{ (t : ϕ) → A t} σ)
    ( \ τ → (t : ϕ) → (τ t = σ t))
    ( \ τ →
      equiv-ExtExt extext
      ( I) (\ t → ϕ t) (\ _ → BOT) (\ t → A t)
      ( \ _ → recBOT) (\ t → τ t) σ)

#def extension-type-pointwise-weakening uses (extext)
  ( σ : (t : ϕ) → A t)
  : Equiv
    ( extension-type I ψ ϕ A σ)
    ( pointwise-homotopy-extension-type σ)
  := equiv-comp
    ( extension-type I ψ ϕ A σ)
    ( homotopy-extension-type I ψ ϕ A σ)
    ( pointwise-homotopy-extension-type σ)
    ( extension-type-weakening I ψ ϕ A σ)
    ( equiv-pointwise-homotopy-extension-type σ)


#end pointwise-homotopy-extension-type
```

## Relative extension types

Given a map `α : A' → A`, there is also a notion of relative extension types.

```rzk
#section relative-extension-types

#variable I : CUBE
#variable ψ : I → TOPE
#variable ϕ : ψ → TOPE
#variables A B : ψ → U
#variable f : (t : ψ) → A t → B t
#variable a : (t : ϕ) → A t
#variable τ : (t : ψ) → B t [ϕ t ↦ f t (a t)]

#def relative-extension-type
  : U
  :=
    Σ ( τ' : (t : ψ) → A t [ϕ t ↦ a t])
    , ( ( t : ψ) → (f t (τ' t) = τ t) [ϕ t ↦ refl])
```

This is equivalently expressed as the fibers of postcomposition by $f$.

```rzk
#def postcomp-Π-ext
  : ( ( t : ψ) → A t [ϕ t ↦ a t])
  → ( ( t : ψ) → B t [ϕ t ↦ f t (a t)])
  := (\ τ' t → f t (τ' t))

#def fiber-postcomp-Π-ext
  : U
  :=
    fib
    ( ( t : ψ) → A t [ϕ t ↦ a t])
    ( ( t : ψ) → B t [ϕ t ↦ f t (a t)])
    ( postcomp-Π-ext)
    ( τ)

#def equiv-relative-extension-type-fib uses (extext)
  : Equiv
    ( fiber-postcomp-Π-ext)
    ( relative-extension-type)
  :=
    total-equiv-family-of-equiv
    ( ( t : ψ) → A t [ϕ t ↦ a t])
    ( \ τ' → (\ t → f t (τ' t)) =_{ (t : ψ) → B t [ϕ t ↦ f t (a t)]} τ)
    ( \ τ' → (t : ψ) → (f t (τ' t) = τ t) [ϕ t ↦ refl])
    ( \ τ' →
      equiv-ExtExt extext I ψ ϕ B
      ( \ t → f t (a t))
      ( \ t → f t (τ' t)) (τ))
```

The fiber of postcomposition by a map $f: \prod_{t : I|\psi} A (t) \to B (t)$ is
equivalent to the family of fibers of $f\_t$.

```rzk
#def fiber-family-ext
  : U
  := (t : ψ) → fib (A t) (B t) (f t) (τ t) [ϕ t ↦ (a t , refl)]

#def equiv-fiber-postcomp-Π-ext-fiber-family-ext uses (extext)
  : Equiv
    ( fiber-postcomp-Π-ext)
    ( fiber-family-ext)
  :=
    equiv-comp
    ( fiber-postcomp-Π-ext)
    ( relative-extension-type)
    ( fiber-family-ext)
    ( equiv-relative-extension-type-fib)
    ( inv-equiv-axiom-choice I ψ ϕ A (\ t x → f t x = τ t) a (\ t → refl))

#end relative-extension-types
```

### Generalized relative extension types

We will also need to allow more general relative extension types, where we start
with a `τ : ψ → A` that does not strictly restrict to `\ t → α (σ' t)`.

```rzk
#section general-extension-types

#variable I : CUBE
#variable ψ : I → TOPE
#variable ϕ : ψ → TOPE
#variables A' A : ψ → U
#variable α : (t : ψ) → A' t → A t

#def general-relative-extension-type
  ( σ' : (t : ϕ) → A' t)
  ( τ : (t : ψ) → A t)
  ( h : (t : ϕ) → α t (σ' t) = τ t)
  : U
  :=
    Σ ( τ' : (t : ψ) → A' t [ϕ t ↦ σ' t])
    , ( t : ψ) → (α t (τ' t) = τ t) [ϕ t ↦ h t]
```

If all ordinary relative extension types are contractible, then all generalized
extension types are also contractible.

```rzk
#def has-contr-relative-extension-types
  : U
  :=
    ( ( σ' : (t : ϕ) → A' t)
    → ( τ : (t : ψ) → A t [ϕ t ↦ α t (σ' t)])
    → ( is-contr (relative-extension-type I ψ ϕ A' A α σ' τ)))

#def has-contr-general-relative-extension-types
  : U
  :=
    ( ( σ' : (t : ϕ) → A' t)
    → ( τ : (t : ψ) → A t)
    → ( h : (t : ϕ) → α t (σ' t) = τ t)
    → ( is-contr (general-relative-extension-type σ' τ h)))

#def has-contr-relative-extension-types-generalize' uses (extext)
  ( has-contr-relext-α : has-contr-relative-extension-types)
  ( σ' : (t : ϕ) → A' t)
  ( τ : (t : ψ) → A t)
  ( h : (t : ϕ) → α t (σ' t) = τ t)
  : is-contr
    ( general-relative-extension-type σ' τ
      ( \ t →
        rev (A t) (τ t) (α t (σ' t)) (rev (A t) (α t (σ' t)) (τ t) (h t))))
  :=
    ind-has-section-equiv
    ( extension-type I ψ ϕ A (\ t → α t (σ' t)))
    ( pointwise-homotopy-extension-type I ψ ϕ A (\ t → α t (σ' t)))
    ( extension-type-pointwise-weakening I ψ ϕ A (\ t → α t (σ' t)))
    ( \ (τ̂ , ĥ) →
      is-contr
      ( general-relative-extension-type σ' τ̂
        ( \ t → rev (A t) (τ̂ t) (α t (σ' t)) (ĥ t))))
    ( \ τ → has-contr-relext-α σ' τ)
    ( τ , \ t → (rev (A t) (α t (σ' t)) (τ t) (h t)))

#def has-contr-relative-extension-types-generalize uses (extext)
  ( has-contr-relext-α : has-contr-relative-extension-types)
  : has-contr-general-relative-extension-types
  :=
  \ σ' τ h →
    transport
    ( ( t : ϕ) → α t (σ' t) = τ t)
    ( \ ĥ → is-contr (general-relative-extension-type σ' τ ĥ))
    ( \ t → rev (A t) (τ t) (α t (σ' t)) (rev (A t) (α t (σ' t)) (τ t) (h t)))
    ( h)
    ( naiveextext-extext extext
      ( I) (\ t → ϕ t) (\ _ → BOT) (\ t → α t (σ' t) = τ t) (\ _ → recBOT)
      ( \ t → rev (A t) (τ t) (α t (σ' t)) (rev (A t) (α t (σ' t)) (τ t) (h t)))
      ( h)
      ( \ t → rev-rev (A t) (α t (σ' t)) (τ t) (h t)))
    ( has-contr-relative-extension-types-generalize'
         has-contr-relext-α σ' τ h)
```

The converse is of course trivial.

```rzk
#def has-contr-relative-extension-types-specialize
  ( has-contr-gen-relext-α : has-contr-general-relative-extension-types)
  : has-contr-relative-extension-types
  := \ σ' τ → has-contr-gen-relext-α σ' τ (\ _ → refl)

#end general-extension-types
```

## Functoriality of extension types

We aim to show that special properties of a map of types `f : A → B`, such as
being an equivalence or having a retraction carry over to the induced map on
extension types.

For each map `f : A → B` and each shape inclusion `ϕ ⊂ ψ`, we have a commutative
square.

```
(ψ → A') → (ψ → A)

   ↓          ↓

(ϕ → A') → (ϕ → A)
```

We can view it as a map of maps either vertically or horizontally.

```rzk
#def map-of-restriction-maps
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( A B : ψ → U)
  ( f : (t : ψ) → A t → B t)
  : map-of-maps
    ( ( t : ψ) → A t) ((t : ϕ) → A t)  (\ a t → a t)
    ( ( t : ψ) → B t) ((t : ϕ) → B t)  (\ b t → b t)
  :=
    ( ( ( \ a t → f t (a t)) , (\ a t → f t (a t))) , \ _ → refl)

#def map-of-map-extension-type
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( A B : ψ → U)
  ( f : (t : ψ) → A t → B t)
  : map-of-maps
    ( ( t : ψ) → A t) ((t : ψ) → B t) (\ a t → f t (a t))
    ( ( t : ϕ) → A t) ((t : ϕ) → B t) (\ a t → f t (a t))
  :=
    ( ( ( \ a t → a t) , (\ b t → b t)) , \ _ → refl)
```

### Equivalences induce equivalences of extension types

If $f: \prod_{t : I|\psi} A (t) \to B (t)$ is a family of equivalence then the
fibers of postcomposition by $f$ are contractible.

```rzk

#def is-contr-fiber-family-ext-contr-fib
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( A B : ψ → U)
  ( f : (t : ψ) → A t → B t)
  ( a : (t : ϕ) → A t)
  ( τ : (t : ψ) → B t [ϕ t ↦ f t (a t)])
  ( family-equiv-f : (t : ψ) → is-equiv (A t) (B t) (f t))
  : is-contr (fiber-family-ext I ψ ϕ A B f a τ)
  :=
    ( weakextext-extext extext) I ψ ϕ
    ( \ t → fib (A t) (B t) (f t) (τ t))
    ( \ t → is-contr-map-is-equiv (A t) (B t) (f t) (family-equiv-f t) (τ t))
    ( \ t → (a t , refl))

#def is-contr-fiber-postcomp-Π-ext-is-equiv-fam uses (extext)
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( A B : ψ → U)
  ( f : (t : ψ) → A t → B t)
  ( a : (t : ϕ) → A t)
  ( τ : (t : ψ) → B t [ϕ t ↦ f t (a t)])
  ( family-equiv-f : (t : ψ) → is-equiv (A t) (B t) (f t))
  : is-contr (fiber-postcomp-Π-ext I ψ ϕ A B f a τ)
  :=
    is-contr-equiv-is-contr'
    ( fiber-postcomp-Π-ext I ψ ϕ A B f a τ)
    ( fiber-family-ext I ψ ϕ A B f a τ)
    ( equiv-fiber-postcomp-Π-ext-fiber-family-ext I ψ ϕ A B f a τ)
    ( is-contr-fiber-family-ext-contr-fib I ψ ϕ A B f a τ family-equiv-f)
```

Hence, postcomposing with an equivalence induces an equivalence of extension
types.

```rzk
#def is-equiv-extensions-is-equiv uses (extext)
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( A B : ψ → U)
  ( f : (t : ψ) → A t → B t)
  ( a : (t : ϕ) → A t)
  ( family-equiv-f : (t : ψ) → is-equiv (A t) (B t) (f t))
  : is-equiv
    ( ( t : ψ) → A t [ϕ t ↦ a t])
    ( ( t : ψ) → B t [ϕ t ↦ f t (a t)])
    ( postcomp-Π-ext I ψ ϕ A B f a)
  :=
    is-equiv-is-contr-map
    ( ( t : ψ) → A t [ϕ t ↦ a t])
    ( ( t : ψ) → B t [ϕ t ↦ f t (a t)])
    ( postcomp-Π-ext I ψ ϕ A B f a)
    ( \ τ →
      is-contr-fiber-postcomp-Π-ext-is-equiv-fam I ψ ϕ A B f a τ family-equiv-f)

#def equiv-extensions-equiv uses (extext)
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( A B : ψ → U)
  ( equivs-A-B : (t : ψ) → Equiv (A t) (B t))
  ( a : (t : ϕ) → A t)
  : Equiv
    ( ( t : ψ) → A t [ϕ t ↦ a t])
    ( ( t : ψ) → B t [ϕ t ↦ first (equivs-A-B t) (a t)])
  :=
    ( postcomp-Π-ext I ψ ϕ A B (\ t → (first (equivs-A-B t))) a
    , is-equiv-extensions-is-equiv I ψ ϕ A B
      ( \ t → first (equivs-A-B t))
      ( a)
      ( \ t → second (equivs-A-B t)))

#def equiv-of-restriction-maps-equiv uses (extext)
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( A B : ψ → U)
  ( famequiv : (t : ψ) → (Equiv (A t) (B t)))
  : Equiv-of-maps
    ( ( t : ψ) → A t) ((t : ϕ) → A t)  (\ a t → a t)
    ( ( t : ψ) → B t) ((t : ϕ) → B t)  (\ b t → b t)
  :=
    ( map-of-restriction-maps I ψ ϕ A B (\ t → first (famequiv t))
    , ( second (equiv-extensions-equiv I ψ (\ _ → BOT)
      ( A) (B)
      ( famequiv)
      ( \ _ → recBOT))
      , second (equiv-extensions-equiv I (\ t → ϕ t) (\ _ → BOT)
        ( \ t → A t) (\ t → B t)
        ( \ t → famequiv t)
        ( \ _ → recBOT))))
```

### Retracts induce retracts of extension types

We show that if `f : A → B` has a retraction, then the same is true for the
induced map on extension types. We reduce this to the case of equivalences by
working with external retractions.

```rzk
#section section-retraction-extensions

#variable I : CUBE
#variable ψ : I → TOPE
#variable ϕ : ψ → TOPE
#variables A B : ψ → U

#variable s : (t : ψ) → A t → B t
#variable r : (t : ψ) → B t → A t
#variable η : (t : ψ) → (a : A t) → r t (s t a) = a

#def is-sec-rec-extensions-sec-rec uses (extext)
  ( a : (t : ϕ) → A t)
  : is-section-retraction-pair
    ( ( t : ψ) → A t [ϕ t ↦ a t])
    ( ( t : ψ) → B t [ϕ t ↦ s t (a t)])
    ( ( t : ψ) → A t [ϕ t ↦ r t(s t(a t))])
    ( \ a' t → s t (a' t))
    ( \ b' t → r t (b' t))
  :=
    is-equiv-extensions-is-equiv I ψ ϕ A A
    ( \ t a₀ → r t (s t (a₀)))
    ( a)
    ( \ t → is-equiv-retraction-section (A t) (B t) (s t) (r t) (η t))


#def has-retraction-extensions-has-retraction' uses (extext η)
  ( a : (t : ϕ) → A t)
  : has-retraction
    ( ( t : ψ) → A t [ϕ t ↦ a t])
    ( ( t : ψ) → B t [ϕ t ↦ s t (a t)])
    ( \ a' t → s t (a' t))
  :=
    has-retraction-internalize
    ( ( t : ψ) → A t [ϕ t ↦ a t])
    ( ( t : ψ) → B t [ϕ t ↦ s t (a t)])
    ( \ a' t → s t (a' t))
    ( ( ( t : ψ) → A t [ϕ t ↦ r t (s t (a t))]
      , \ b' t → r t (b' t))
    , is-sec-rec-extensions-sec-rec a)

#def has-section-extensions-has-section' uses (extext η)
  ( a : (t : ϕ) → A t)
  : has-section
    ( ( t : ψ) → B t [ϕ t ↦ s t (a t)])
    ( ( t : ψ) → A t [ϕ t ↦ r t (s t (a t))])
    ( \ b t → r t (b t))
  :=
    has-section-internalize
    ( ( t : ψ) → B t [ϕ t ↦ s t (a t)])
    ( ( t : ψ) → A t [ϕ t ↦ r t (s t (a t))])
    ( \ b' t → r t (b' t))
    ( ( ( ( t : ψ) → A t [ϕ t ↦ a t])
      , ( \ a' t → s t (a' t)))
    , is-sec-rec-extensions-sec-rec a)

#end section-retraction-extensions
```

It is convenient to have uncurried versions.

```rzk
#def has-retraction-extensions-has-retraction uses (extext)
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( A B : ψ → U)
  ( s : (t : ψ) → A t → B t)
  ( has-retraction-s : (t : ψ) → has-retraction (A t) (B t) (s t))
  ( a : (t : ϕ) → A t)
  : has-retraction
    ( ( t : ψ) → A t [ϕ t ↦ a t])
    ( ( t : ψ) → B t [ϕ t ↦ s t (a t)])
    ( \ a' t → s t (a' t))
  :=
    has-retraction-extensions-has-retraction' I ψ ϕ A B s
    ( \ t → first (has-retraction-s t))
    ( \ t → second (has-retraction-s t))
    ( a)

#def has-section-extensions-has-section uses (extext)
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( B A : ψ → U)
  ( r : (t : ψ) → B t → A t)
  ( has-section-r : (t : ψ) → has-section (B t) (A t) (r t))
  ( a : (t : ϕ) → A t)
  : has-section
    ( ( t : ψ) → B t [ϕ t ↦ (first (has-section-r t)) (a t)])
    ( ( t : ψ) → A t [ϕ t ↦ r t (first (has-section-r t) (a t))])
    ( \ b t → r t (b t))
  :=
    has-section-extensions-has-section' I ψ ϕ A B
    ( \ t → first (has-section-r t))
    ( r)
    ( \ t → second (has-section-r t))
    ( a)
```

We summarize by saying that retracts of types induce retracts of extension
types.

```rzk
#def is-retract-of-extensions-are-retract-of uses (extext)
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( A B : ψ → U)
  ( are-retract-A-of-B : (t : ψ) → is-retract-of (A t) (B t))
  ( a : (t : ϕ) → A t)
  : is-retract-of
    ( ( t : ψ) → A t [ϕ t ↦ a t])
    ( ( t : ψ) → B t [ϕ t ↦ first (are-retract-A-of-B t) (a t)])
  :=
  ( ( \ a' t → first (are-retract-A-of-B t) (a' t))
  , ( has-retraction-extensions-has-retraction I ψ ϕ A B
      ( \ t → first (are-retract-A-of-B t))
      ( \ t → second (are-retract-A-of-B t))
      ( a)))
```

The following special case of extensions from `BOT` is also useful.

```rzk
#def has-section-extensions-BOT-has-section uses (extext)
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( A B : ψ → U)
  ( f : (t : ψ) → A t → B t)
  ( has-section-f : (t : ψ) → has-section (A t) (B t) (f t))
  : has-section ((t : ψ) → A t) ((t : ψ) → B t) (\ a t → f t (a t))
  :=
    ( ( \ b t → first (has-section-f t) (b t))
    , \ b →
      ( naiveextext-extext extext I ψ (\ _ → BOT) B (\ _ → recBOT)
        ( \ t → f t (first (has-section-f t) (b t)))
        ( \ t → b t)
        ( \ t → second (has-section-f t) (b t))))
```
