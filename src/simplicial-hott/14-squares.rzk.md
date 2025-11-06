# Squares

```rzk
#lang rzk-1
```

## Prerequisites

- `05-segal-types.rzk.md` - We make use of statements true in Segal types.

## Definition squares

```rzk
#def square
  ( A : U)
  ( x y z w : A)
  ( f₁ : hom A x y)
  ( g₁ : hom A x z)
  ( f₂ : hom A z w)
  ( g₂ : hom A y w)
  : U
  :=
  ( ( t , s) : 2 × 2) → A
  [ t ≡ 0₂ ↦ g₁ s
  , t ≡ 1₂ ↦ g₂ s
  , s ≡ 0₂ ↦ f₁ t
  , s ≡ 1₂ ↦ f₂ t]
```

```rzk
#def curried-square
  ( A : U)
  ( x y z w : A)
  ( f₁ : hom A x y)
  ( g₁ : hom A x z)
  ( f₂ : hom A z w)
  ( g₂ : hom A y w)
  : U
  :=
  ( t : Δ¹) → (s : Δ¹) → A
  [ s ≡ 0₂ ↦ f₁ t
  , s ≡ 1₂ ↦ f₂ t
  , t ≡ 0₂ ↦ g₁ s
  , t ≡ 1₂ ↦ g₂ s]
```

These two notions are trivially equivalent:

```rzk
#def equiv-square-curried-square
  ( A : U)
  ( x y z w : A)
  ( f₁ : hom A x y)
  ( g₁ : hom A x z)
  ( f₂ : hom A z w)
  ( g₂ : hom A y w)
  : Equiv
    ( square A x y z w f₁ g₁ f₂ g₂)
    ( curried-square A x y z w f₁ g₁ f₂ g₂)
  :=
  equiv-inverse
  ( square A x y z w f₁ g₁ f₂ g₂)
  ( curried-square A x y z w f₁ g₁ f₂ g₂)
  ( \ σ t s → σ (t , s))
  ( \ σ (t , s) → σ t s)
  ( \ _ → refl)
  ( \ _ → refl)
```

Additionally we have another expected result that a square is just made up of
two triangles that agree on the diagonal.

```rzk
#def equiv-square-glued-triangles
  ( A : U)
  ( x y z w : A)
  ( f₁ : hom A x y)
  ( g₁ : hom A x z)
  ( f₂ : hom A z w)
  ( g₂ : hom A y w)
  : Equiv
    ( square A x y z w f₁ g₁ f₂ g₂)
    ( Σ ( d : hom A x w)
      , product
        ( hom2 A x y w f₁ g₂ d)
        ( hom2 A x z w g₁ f₂ d))
  :=
  equiv-inverse
  ( square A x y z w f₁ g₁ f₂ g₂)
  ( Σ ( d : hom A x w)
    , product
      ( hom2 A x y w f₁ g₂ d)
      ( hom2 A x z w g₁ f₂ d))
  ( \ σ →
    ( \ t → σ (t , t)
    , ( \ tt → σ tt , \ (t , s) → σ (s , t))))
  ( \ (_ , (τ₁ , τ₂)) (t , s) → recOR
    ( s ≤ t ↦ τ₁ (t , s)
    , t ≤ s ↦ τ₂ (s , t)))
  ( \ _ → refl)
  ( \ _ → refl)
```

Since triangles with one side being the identity are equivalent to paths (in
Segal types), we can combine the above equivalence with this fact and obtain
that squares with one side being the identity are equivalent to triangles.

```rzk
#def equiv-square-left-id-triangle-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y w : A)
  ( f₁ : hom A x y)
  ( f₂ : hom A x w)
  ( g₂ : hom A y w)
  : Equiv
    ( square A x y x w f₁ (id-hom A x) f₂ g₂)
    ( hom2 A x y w f₁ g₂ f₂)
  :=
  equiv-quadruple-comp
  ( square A x y x w f₁ (id-hom A x) f₂ g₂)
  ( Σ ( d : hom A x w)
    , product
      ( hom2 A x y w f₁ g₂ d)
      ( hom2 A x x w (id-hom A x) f₂ d))
  ( Σ ( d : hom A x w)
    , product
      ( hom2 A x y w f₁ g₂ d)
      ( f₂ = d))
  ( Σ ( d : hom A x w)
    , product
      ( f₂ = d)
      ( hom2 A x y w f₁ g₂ d))
  ( hom2 A x y w f₁ g₂ f₂)
  ( equiv-square-glued-triangles A x y x w f₁ (id-hom A x) f₂ g₂)
  ( total-equiv-family-of-equiv
    ( hom A x w)
    ( \ d →
      product
      ( hom2 A x y w f₁ g₂ d)
      ( hom2 A x x w (id-hom A x) f₂ d))
    ( \ d →
      product
      ( hom2 A x y w f₁ g₂ d)
      ( f₂ = d))
    ( \ d →
      equiv-product-equivs
      ( hom2 A x y w f₁ g₂ d)
      ( hom2 A x y w f₁ g₂ d)
      ( identity (hom2 A x y w f₁ g₂ d)
      , is-equiv-identity (hom2 A x y w f₁ g₂ d))
      ( hom2 A x x w (id-hom A x) f₂ d)
      ( f₂ = d)
      ( inv-equiv
        ( f₂ = d)
        ( hom2 A x x w (id-hom A x) f₂ d)
        ( equiv-homotopy-hom2-is-segal A is-segal-A x w f₂ d))))
  ( equiv-inverse
    ( Σ ( d : hom A x w)
      , product
        ( hom2 A x y w f₁ g₂ d)
        ( f₂ = d))
    ( Σ ( d : hom A x w)
      , product
        ( f₂ = d)
        ( hom2 A x y w f₁ g₂ d))
    ( \ (d , (τ , p)) → (d , (p , τ)))
    ( \ (d , (p , τ)) → (d , (τ , p)))
    ( \ _ → refl)
    ( \ _ → refl))
  ( equiv-based-paths-family (hom A x w) (\ d → hom2 A x y w f₁ g₂ d) f₂)
```

If we have a square with two sides being identity, we can thus conclude that it
is equivalent to a path of the two other sides:

```rzk
#def equiv-square-sides-id-eq-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  ( f : hom A x y)
  ( g : hom A x y)
  : Equiv
    ( square A x y x y f (id-hom A x) g (id-hom A y))
    ( f = g)
  :=
  equiv-comp
  ( square A x y x y f (id-hom A x) g (id-hom A y))
  ( hom2 A x y y f (id-hom A y) g)
  ( f = g)
  ( equiv-square-left-id-triangle-is-segal A is-segal-A x y y f g (id-hom A y))
  ( inv-equiv
    ( f = g)
    ( hom2 A x y y f (id-hom A y) g)
    ( equiv-homotopy-hom2'-is-segal A is-segal-A x y f g))

#def square-id-hom-eq-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  ( f : hom A x y)
  ( g : hom A x y)
  ( p : f = g)
  : square A x y x y f (id-hom A x) g (id-hom A y)
  :=
  first
  ( inv-equiv
    ( square A x y x y f (id-hom A x) g (id-hom A y))
    ( f = g)
    ( equiv-square-sides-id-eq-is-segal A is-segal-A x y f g))
  ( p)

#def eq-square-id-hom-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  ( f : hom A x y)
  ( g : hom A x y)
  ( σ : square A x y x y f (id-hom A x) g (id-hom A y))
  : f = g
  :=
  first
  ( equiv-square-sides-id-eq-is-segal A is-segal-A x y f g)
  ( σ)
```

Finally, we obtain the main result of this subsection, by showing that squares
with two constant opposing sides have the same induction scheme as identity
types.

```rzk
#def ind-square-sides-id-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  ( f : hom A x y)
  ( C : (g : hom A x y) → (square A x y x y f (id-hom A x) g (id-hom A y)) → U)
  ( d : C f (\ (t , s) → f t))
  ( g : hom A x y)
  ( σ : square A x y x y f (id-hom A x) g (id-hom A y))
  : C g σ
  :=
  transport
  ( square A x y x y f (id-hom A x) g (id-hom A y))
  ( C g)
  ( square-id-hom-eq-is-segal A is-segal-A x y f g
    ( eq-square-id-hom-is-segal A is-segal-A x y f g σ))
  ( σ)
  ( inv-equiv-cancel
    ( square A x y x y f (id-hom A x) g (id-hom A y))
    ( f = g)
    ( equiv-square-sides-id-eq-is-segal A is-segal-A x y f g)
    ( σ))
  ( ind-path (hom A x y) f
    ( \ g' p → C g' (square-id-hom-eq-is-segal A is-segal-A x y f g' p))
    ( d)
    ( g)
    ( eq-square-id-hom-is-segal A is-segal-A x y f g σ))

#def ind-curried-square-sides-id-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  ( f : hom A x y)
  ( C : (g : hom A x y)
      → ( curried-square A x y x y f (id-hom A x) g (id-hom A y))
      → U)
  ( d : C f (\ t _ → f t))
  ( g : hom A x y)
  ( σ : curried-square A x y x y f (id-hom A x) g (id-hom A y))
  : C g σ
  :=
  ind-square-sides-id-is-segal A is-segal-A x y f
  ( \ g σ → C g (\ t s → σ (t , s)))
  ( d)
  ( g)
  ( \ (t , s) → σ t s)
```
