# Squares

```rzk
#lang rzk-1
```

## Prerequisites

- `05-segal-types.rzk.md` - We make use of statements true in Segal types.

## Definition squares

A square is a map `#!rzk Δ¹ × Δ¹ → A` where we fix the boundary:

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

We can alternatively curry the argument to define it as: `#!rzk Δ¹ → Δ¹ → A`
again with the boundary fixed:

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

These two notions are trivially equivalent by just currying the extension types:

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
  equiv-has-inverse
  ( square A x y z w f₁ g₁ f₂ g₂)
  ( curried-square A x y z w f₁ g₁ f₂ g₂)
  ( \ σ t s → σ (t , s))
  ( \ σ (t , s) → σ t s)
  ( \ _ → refl)
  ( \ _ → refl)
```

A square can be decomposed into two triangles that agree on the diagonal:

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
  equiv-has-inverse
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

## Collapsing squares with identities

In Segal types, triangles in which one side is the identity morphism are
equivalent to paths. Together with the decomposition of squares, this allows us
to collapse a square with an identity to a square.

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
  ( equiv-has-inverse
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

```rzk
#def square-hom2
  ( A : U)
  ( x y w : A)
  ( f₁ : hom A x y)
  ( f₂ : hom A x w)
  ( g₂ : hom A y w)
  ( τ : hom2 A x y w f₁ g₂ f₂)
  : square A x y x w f₁ (id-hom A x) f₂ g₂
  :=
  \ (t , s) → recOR(s ≤ t ↦ τ (t , s) , t ≤ s ↦ f₂ t)
```

If we have a square with two opposite sides being identity, we can thus conclude
that it is equivalent to a path of the two other sides:

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

Through this equivalence of squares to paths given identities on opposite sides,
we can transfer the induction principle to squares.

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
    ( \ g p → C g (square-id-hom-eq-is-segal A is-segal-A x y f g p))
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

## Dependent squares

```rzk
#def dependent-square
  ( B : U)
  ( x y z w : B)
  ( f₁ : hom B x y)
  ( g₁ : hom B x z)
  ( f₂ : hom B z w)
  ( g₂ : hom B y w)
  ( σ : square B x y z w f₁ g₁ f₂ g₂)
  ( P : B → U)
  ( X : P x)
  ( Y : P y)
  ( Z : P z)
  ( W : P w)
  ( F₁ : dhom B x y f₁ P X Y)
  ( G₁ : dhom B x z g₁ P X Z)
  ( F₂ : dhom B z w f₂ P Z W)
  ( G₂ : dhom B y w g₂ P Y W)
  : U
  :=
  ( ( t , s) : 2 × 2) → P (σ (t , s))
  [ t ≡ 0₂ ↦ G₁ s
  , t ≡ 1₂ ↦ G₂ s
  , s ≡ 0₂ ↦ F₁ t
  , s ≡ 1₂ ↦ F₂ t]
```

```rzk
#def equiv-dependent-square-glued-dhom2
  ( B : U)
  ( x y z w : B)
  ( f₁ : hom B x y)
  ( g₁ : hom B x z)
  ( f₂ : hom B z w)
  ( g₂ : hom B y w)
  ( σ : square B x y z w f₁ g₁ f₂ g₂)
  ( P : B → U)
  ( X : P x)
  ( Y : P y)
  ( Z : P z)
  ( W : P w)
  ( F₁ : dhom B x y f₁ P X Y)
  ( G₁ : dhom B x z g₁ P X Z)
  ( F₂ : dhom B z w f₂ P Z W)
  ( G₂ : dhom B y w g₂ P Y W)
  : Equiv
    ( dependent-square B x y z w f₁ g₁ f₂ g₂ σ P X Y Z W F₁ G₁ F₂ G₂)
    ( Σ ( D : dhom B x w (\ t → σ (t , t)) P X W)
      , product
        ( dhom2 B x y w
          ( f₁) (g₂) (\ t → σ (t , t))
          ( \ ts → σ ts)
          ( P) (X) (Y) (W)
          ( F₁) (G₂) (D))
        ( dhom2 B x z w
          ( g₁) (f₂) (\ t → σ (t , t))
          ( \ (t , s) → σ (s , t))
          ( P) (X) (Z) (W)
          ( G₁) (F₂) (D)))
  :=
  equiv-has-inverse
  ( dependent-square B x y z w f₁ g₁ f₂ g₂ σ P X Y Z W F₁ G₁ F₂ G₂)
  ( Σ ( D : dhom B x w (\ t → σ (t , t)) P X W)
    , product
      ( dhom2 B x y w
        ( f₁) (g₂) (\ t → σ (t , t))
        ( \ ts → σ ts)
        ( P) (X) (Y) (W)
        ( F₁) (G₂) (D))
      ( dhom2 B x z w
        ( g₁) (f₂) (\ t → σ (t , t))
        ( \ (t , s) → σ (s , t))
        ( P) (X) (Z) (W)
        ( G₁) (F₂) (D)))
  ( \ S → (\ t → S (t , t) , (\ ts → S ts , \ (t , s) → S (s , t))))
  ( \ (_ , (τ₁ , τ₂)) (t , s) → recOR
    ( s ≤ t ↦ τ₁ (t , s)
    , t ≤ s ↦ τ₂ (s , t)))
  ( \ _ → refl)
  ( \ _ → refl)
```

```rzk
#def equiv-dependent-square-left-id-dhom2-is-inner-family
  ( B : U)
  ( x y w : B)
  ( f₁ : hom B x y)
  ( f₂ : hom B x w)
  ( g₂ : hom B y w)
  ( τ : hom2 B x y w f₁ g₂ f₂)
  ( P : B → U)
  ( is-inner-family-P : is-inner-family B P)
  ( X : P x)
  ( Y : P y)
  ( W : P w)
  ( F₁ : dhom B x y f₁ P X Y)
  ( F₂ : dhom B x w f₂ P X W)
  ( G₂ : dhom B y w g₂ P Y W)
  : Equiv
    ( dependent-square B x y x w f₁ (id-hom B x) f₂ g₂
      ( square-hom2 B x y w f₁ f₂ g₂ τ)
      ( P) X Y X W F₁ (id-dhom B x P X) F₂ G₂)
    ( dhom2 B x y w f₁ g₂ f₂ τ P X Y W F₁ G₂ F₂)
  :=
  equiv-quadruple-comp
  ( dependent-square B x y x w f₁ (id-hom B x) f₂ g₂
    ( square-hom2 B x y w f₁ f₂ g₂ τ)
    ( P) X Y X W F₁ (id-dhom B x P X) F₂ G₂)
  ( Σ ( D : dhom B x w f₂ P X W)
    , product
      ( dhom2 B x y w
        ( f₁) (g₂) (f₂)
        ( τ)
        ( P) (X) (Y) (W)
        ( F₁) (G₂) (D))
      ( dhom2 B x x w
        ( id-hom B x) (f₂) (f₂)
        ( \ (_ , s) → f₂ s)
        ( P) (X) (X) (W)
        ( id-dhom B x P X) (F₂) (D)))
  ( Σ ( D : dhom B x w f₂ P X W)
    , product
      ( dhom2 B x y w
        ( f₁) (g₂) (f₂)
        ( τ)
        ( P) (X) (Y) (W)
        ( F₁) (G₂) (D))
      ( F₂ = D))
  ( Σ ( D : dhom B x w f₂ P X W)
    , product
      ( F₂ = D)
      ( dhom2 B x y w
        ( f₁) (g₂) (f₂)
        ( τ)
        ( P) (X) (Y) (W)
        ( F₁) (G₂) (D)))
  ( dhom2 B x y w f₁ g₂ f₂ τ P X Y W F₁ G₂ F₂)
  ( equiv-dependent-square-glued-dhom2 B x y x w f₁ (id-hom B x) f₂ g₂
    ( square-hom2 B x y w f₁ f₂ g₂ τ) P X Y X W F₁ (id-dhom B x P X) F₂ G₂)
  ( total-equiv-family-of-equiv
    ( dhom B x w f₂ P X W)
    ( \ D → product
      ( dhom2 B x y w
        ( f₁) (g₂) (f₂)
        ( τ)
        ( P) (X) (Y) (W)
        ( F₁) (G₂) (D))
      ( dhom2 B x x w
        ( id-hom B x) (f₂) (f₂)
        ( \ (_ , s) → f₂ s)
        ( P) (X) (X) (W)
        ( id-dhom B x P X) (F₂) (D)))
    ( \ D → product
      ( dhom2 B x y w
        ( f₁) (g₂) (f₂)
        ( τ)
        ( P) (X) (Y) (W)
        ( F₁) (G₂) (D))
      ( F₂ = D))
    ( \ D → equiv-product-equivs
      ( dhom2 B x y w
        ( f₁) (g₂) (f₂)
        ( τ)
        ( P) (X) (Y) (W)
        ( F₁) (G₂) (D))
      ( dhom2 B x y w
        ( f₁) (g₂) (f₂)
        ( τ)
        ( P) (X) (Y) (W)
        ( F₁) (G₂) (D))
      ( equiv-identity
        ( dhom2 B x y w
          ( f₁) (g₂) (f₂)
          ( τ)
          ( P) (X) (Y) (W)
          ( F₁) (G₂) (D)))
      ( dhom2 B x x w
        ( id-hom B x) (f₂) (f₂)
        ( \ (_ , s) → f₂ s)
        ( P) (X) (X) (W)
        ( id-dhom B x P X) (F₂) (D))
      ( F₂ = D)
      ( inv-equiv
        ( F₂ = D)
        ( dhom2 B x x w
          ( id-hom B x) (f₂) (f₂)
          ( \ (_ , s) → f₂ s)
          ( P) (X) (X) (W)
          ( id-dhom B x P X) (F₂) (D))
        ( equiv-homotopy-dhom2-is-inner-family B x w f₂
          ( P) is-inner-family-P X W F₂ D))))
  ( equiv-has-inverse
    ( Σ ( D : dhom B x w f₂ P X W)
      , product
        ( dhom2 B x y w
          ( f₁) (g₂) (f₂)
          ( τ)
          ( P) (X) (Y) (W)
          ( F₁) (G₂) (D))
        ( F₂ = D))
    ( Σ ( D : dhom B x w f₂ P X W)
      , product
        ( F₂ = D)
        ( dhom2 B x y w
          ( f₁) (g₂) (f₂)
          ( τ)
          ( P) (X) (Y) (W)
          ( F₁) (G₂) (D)))
    ( \ (D , (τ' , p)) → (D , (p , τ')))
    ( \ (D , (p , τ')) → (D , (τ' , p)))
    ( \ _ → refl)
    ( \ _ → refl))
  ( equiv-based-paths-family (dhom B x w f₂ P X W)
    ( \ D → dhom2 B x y w
        ( f₁) (g₂) (f₂)
        ( τ)
        ( P) (X) (Y) (W)
        ( F₁) (G₂) (D))
    ( F₂))
```

