# LARI Families

```rzk
#lang rzk-1
```

```rzk
#assume funext : FunExt
#assume extext : ExtExt
```

## Definition


```rzk
#section LARI-families

#variable I : CUBE
#variable X : I → TOPE
#variable Y : X → TOPE

#def LARI-family-domain
  ( B : U)
  ( P : B → U)
  : U
  := Σ (g : X → B) , (y : Y) → P (g y)

#def LARI-family-codomain
  ( B : U)
  ( P : B → U)
  ( ( g , f₀) : LARI-family-domain B P)
  : U
  := (x : X) → P (g x) [Y x ↦ f₀ x]

#def is-LARI-family
  ( B : U)
  ( P : B → U)
  : U
  :=
  ( g : X → B)
  → ( f₀ : (y : Y) → P (g y))
  → has-dependent-initial
    ( LARI-family-domain B P)
    ( LARI-family-codomain B P)
    ( g , f₀)

#def section-is-LARI-family uses (I X Y)
  ( B : U)
  ( P : B → U)
  ( is-LARI-family-P : is-LARI-family B P)
  : ( ( g , f₀) : LARI-family-domain B P) → (LARI-family-codomain B P (g , f₀))
  :=
  \ (g , f₀) → first (is-LARI-family-P g f₀)

#def is-dependent-initial-section-is-LARI-family uses (I X Y)
  ( B : U)
  ( P : B → U)
  ( is-LARI-family-P : is-LARI-family B P)
  : is-dependent-initial-section
    ( LARI-family-domain B P)
    ( LARI-family-codomain B P)
    ( section-is-LARI-family B P is-LARI-family-P)
  :=
  \ (g , f₀) → second (is-LARI-family-P g f₀)

#def is-LARI-family-is-dependent-initial-section uses (I X Y)
  ( B : U)
  ( P : B → U)
  ( s : ((g , f₀) : LARI-family-domain B P) → LARI-family-codomain B P (g , f₀))
  ( is-dependent-initial-section-s
 : is-dependent-initial-section
      ( LARI-family-domain B P)
      ( LARI-family-codomain B P)
      ( s))
  : is-LARI-family B P
  := \ g f₀ → (s (g , f₀) , is-dependent-initial-section-s (g , f₀))
```

## Closure Properties

```rzk
#def equiv-LARI-dhom-product-help
  ( J : U)
  ( B : J → U)
  ( P : (j : J) → (b : B j) → U)
  ( is-LARI-family-P : (j : J) → is-LARI-family (B j) (P j))
  ( ( g , f₀) : LARI-family-domain ((j : J) → B j) (\ b → (j : J) → P j (b j)))
  ( ( g' , f₀') : LARI-family-domain ((j : J) → B j) (\ b → (j : J) → P j (b j)))
  ( m
 : hom (LARI-family-domain ((j : J) → B j) (\ b → (j : J) → P j (b j)))
      ( g , f₀) (g' , f₀'))
  ( b' : LARI-family-codomain ((j : J) → B j) (\ b → (j : J) → P j (b j)) (g' , f₀'))
  : Equiv
    ( dhom
      ( LARI-family-domain ((j : J) → B j) (\ b → (j : J) → P j (b j)))
      ( g , f₀)
      ( g' , f₀')
      ( m)
      ( LARI-family-codomain ((j : J) → B j) (\ (b : (j : J) → B j) → (j : J) → P j (b j)))
      ( \ x j →
        section-is-LARI-family (B j) (P j) (is-LARI-family-P j)
        ( \ x → g x j , \ y → f₀ y j)
        ( x))
      ( b'))
    ( dhom
      ( ( j : J) → LARI-family-domain (B j) (P j))
      ( \ j → (\ x → g x j , \ y → f₀ y j))
      ( \ j → (\ x → g' x j , \ y → f₀' y j))
      ( \ t j → (\ x → first (m t) x j , \ y → second (m t) y j))
      ( \ d → (j : J) → LARI-family-codomain (B j) (P j) (d j))
      ( \ j →
        section-is-LARI-family (B j) (P j) (is-LARI-family-P j)
        ( \ x → g x j , \ y → f₀ y j))
      ( \ j x → b' x j))
  :=
  equiv-has-inverse
  ( dhom
    ( LARI-family-domain ((j : J) → B j) (\ b → (j : J) → P j (b j)))
    ( g , f₀)
    ( g' , f₀')
    ( m)
    ( LARI-family-codomain ((j : J) → B j) (\ (b : (j : J) → B j) → (j : J) → P j (b j)))
    ( \ x j →
      section-is-LARI-family (B j) (P j) (is-LARI-family-P j)
      ( \ x → g x j , \ y → f₀ y j)
      ( x))
    ( b'))
  ( dhom
    ( ( j : J) → LARI-family-domain (B j) (P j))
    ( \ j → (\ x → g x j , \ y → f₀ y j))
    ( \ j → (\ x → g' x j , \ y → f₀' y j))
    ( \ t j → (\ x → first (m t) x j , \ y → second (m t) y j))
    ( \ d → (j : J) → LARI-family-codomain (B j) (P j) (d j))
    ( \ j →
      section-is-LARI-family (B j) (P j) (is-LARI-family-P j)
      ( \ x → g x j , \ y → f₀ y j))
    ( \ j x → b' x j))
  ( \ M t j x → M t x j)
  ( \ M t x j → M t j x)
  ( \ _ → refl)
  ( \ _ → refl)

#def is-LARI-family-product-is-LARI-family uses (I X Y)
  ( J : U)
  ( B : J → U)
  ( P : (j : J) → (b : B j) → U)
  ( is-LARI-family-P : (j : J) → is-LARI-family (B j) (P j))
  : is-LARI-family ((j : J) → B j) (\ (b : (j : J) → B j) → ((j : J) → P j (b j)))
  :=
  is-LARI-family-is-dependent-initial-section
  ( ( j : J) → B j) (\ (b : (j : J) → B j) → ((j : J) → P j (b j)))
  ( \ (g , f₀) →
    \ x j → section-is-LARI-family (B j) (P j) (is-LARI-family-P j) (\ x → g x j , \ y → f₀ y j) x)
  ( \ (g , f₀) (g' , f₀') F m →
    is-contr-equiv-is-contr'
    ( dhom
      ( LARI-family-domain ((j : J) → B j) (\ b → (j : J) → P j (b j)))
      ( g , f₀)
      ( g' , f₀')
      ( m)
      ( LARI-family-codomain ((j : J) → B j) (\ (b : (j : J) → B j) → (j : J) → P j (b j)))
      ( \ x j →
        section-is-LARI-family (B j) (P j) (is-LARI-family-P j)
        ( \ x → g x j , \ y → f₀ y j)
        ( x))
      ( F))
    ( dhom
      ( ( j : J) → LARI-family-domain (B j) (P j))
      ( \ j → (\ x → g x j , \ y → f₀ y j))
      ( \ j → (\ x → g' x j , \ y → f₀' y j))
      ( \ t j → (\ x → first (m t) x j , \ y → second (m t) y j))
      ( \ d → (j : J) → LARI-family-codomain (B j) (P j) (d j))
      ( \ j →
        section-is-LARI-family (B j) (P j) (is-LARI-family-P j)
        ( \ x → g x j , \ y → f₀ y j))
      ( \ j x → F x j))
    ( equiv-LARI-dhom-product-help J B P is-LARI-family-P (g , f₀) (g' , f₀') m F)
    ( is-dependent-initial-section-product-is-dependent-initial-section funext J
      ( \ j → LARI-family-domain (B j) (P j))
      ( \ j → LARI-family-codomain (B j) (P j))
      ( \ j → section-is-LARI-family (B j) (P j) (is-LARI-family-P j))
      ( \ j →
        is-dependent-initial-section-is-LARI-family (B j) (P j) (is-LARI-family-P j))
      ( \ j → (\ x → g x j , \ y → f₀ y j))
      ( \ j → (\ x → g' x j , \ y → f₀' y j))
      ( \ j x → F x j)
      ( \ t j → (\ x → first (m t) x j , \ y → second (m t) y j))))
```

```rzk
#def is-LARI-family-pullback-is-LARI-family uses (I X Y)
  ( A B : U)
  ( P : B → U)
  ( k : A → B)
  ( is-LARI-family-P : is-LARI-family B P)
  : is-LARI-family A (\ a → P (k a))
  :=
  is-LARI-family-is-dependent-initial-section A (\ a → P (k a))
  ( \ (g , f₀) → section-is-LARI-family B P is-LARI-family-P (\ x → k (g x) , f₀))
  ( is-dependent-initial-section-pullback-is-dependent-initial-section
    ( LARI-family-domain B P)
    ( LARI-family-codomain B P)
    ( section-is-LARI-family B P is-LARI-family-P)
    ( is-dependent-initial-section-is-LARI-family B P is-LARI-family-P)
    ( LARI-family-domain A (\ a → P (k a)))
    ( \ (g , f₀) → (\ x → k (g x) , f₀)))
```


```rzk
#def helper2
  ( B : U)
  ( P : B → U)
  ( is-LARI-family-P : is-LARI-family B P)
  ( R : (total-type B P) → U)
  ( is-LARI-family-R : is-LARI-family (total-type B P) R)
  ( ( g , f₀) : LARI-family-domain B (\ b → Σ (p : P b) , R (b , p)))
  : Equiv
    ( Σ ( F : LARI-family-codomain B P (g , \ y → first (f₀ y)))
      , LARI-family-codomain (total-type B P) R
        ( \ x → (g x , F x) , \ y → second (f₀ y)))
    ( LARI-family-codomain B (\ b → Σ (p : P b) , R (b , p)) (g , f₀))
  :=
  equiv-has-inverse
  ( Σ ( F : LARI-family-codomain B P (g , \ y → first (f₀ y)))
    , LARI-family-codomain (total-type B P) R
      ( \ x → (g x , F x) , \ y → second (f₀ y)))
  ( LARI-family-codomain B (\ b → Σ (p : P b) , R (b , p)) (g , f₀))
  ( \ F x → (first F x , second F x))
  ( \ F → (\ x → first (F x) , \ x → second (F x)))
  ( \ _ → refl)
  ( \ _ → refl)

#def helper
  ( B : U)
  ( P : B → U)
  ( is-LARI-family-P : is-LARI-family B P)
  ( R : (total-type B P) → U)
  ( is-LARI-family-R : is-LARI-family (total-type B P) R)
  : is-dependent-initial-section
    ( LARI-family-domain B (\ b → Σ (p : P b) , R (b , p)))
    ( \ (g , f₀) →
      Σ ( F : LARI-family-codomain B P (g , \ y → first (f₀ y)))
      , LARI-family-codomain (total-type B P) R
        ( \ x → (g x , F x) , \ y → second (f₀ y)))
    ( \ (g , f₀) →
      ( \ x → section-is-LARI-family B P is-LARI-family-P (g , \ x → first (f₀ x)) x
      , \ x → section-is-LARI-family (total-type B P) R is-LARI-family-R
        ( \ x →
          ( g x
          , section-is-LARI-family B P is-LARI-family-P (g , \ x → first (f₀ x)) x)
        , \ x → second (f₀ x))
        ( x)))
  :=
  ( is-dependent-initial-section-comp-is-dependent-initial-section
    ( LARI-family-domain B (\ b → Σ (p : P b) , R (b , p)))
    ( \ (g , f₀) → LARI-family-codomain B P (g , \ y → first (f₀ y)))
    ( \ (g , f₀) →
      section-is-LARI-family B P is-LARI-family-P (g , \ y → first (f₀ y)))
    ( is-dependent-initial-section-pullback-is-dependent-initial-section
      ( LARI-family-domain B P)
      ( LARI-family-codomain B P)
      ( section-is-LARI-family B P is-LARI-family-P)
      ( is-dependent-initial-section-is-LARI-family B P is-LARI-family-P)
      ( LARI-family-domain B (\ b → Σ (p : P b) , R (b , p)))
      ( \ (g , f₀) → (g , \ y → first (f₀ y))))
    ( \ ((g , f₀) , F) →
      LARI-family-codomain (total-type B P) R
      ( \ x → (g x , F x) , \ y → second (f₀ y)))
    ( \ ((g , f₀) , F) →
      section-is-LARI-family (total-type B P) R is-LARI-family-R
      ( \ x → (g x , F x) , \ y → second (f₀ y)))
    ( is-dependent-initial-section-pullback-is-dependent-initial-section
      ( LARI-family-domain (total-type B P) R)
      ( LARI-family-codomain (total-type B P) R)
      ( section-is-LARI-family (total-type B P) R is-LARI-family-R)
      ( is-dependent-initial-section-is-LARI-family
        ( total-type B P) (R) (is-LARI-family-R))
      ( total-type
        ( LARI-family-domain B (\ b → Σ (p : P b) , R (b , p)))
        ( \ (g , f₀) → LARI-family-codomain B P (g , \ y → first (f₀ y))))
      ( \ ((g , f₀) , F) → (\ x → (g x , F x) , \ y → second (f₀ y)))))

#def is-LARI-family-comp-is-LARI-family uses (I X Y)
  ( B : U)
  ( P : B → U)
  ( is-LARI-family-P : is-LARI-family B P)
  ( R : (total-type B P) → U)
  ( is-LARI-family-R : is-LARI-family (total-type B P) R)
  : is-LARI-family B (\ b → Σ (p : P b) , R (b , p))
  :=
  is-LARI-family-is-dependent-initial-section B (\ b → Σ (p : P b) , R (b , p))
  ( \ (g , f₀) x →
    ( section-is-LARI-family B P is-LARI-family-P (g , \ x → first (f₀ x)) x
    , section-is-LARI-family (total-type B P) R is-LARI-family-R
      ( \ x →
        ( g x
        , section-is-LARI-family B P is-LARI-family-P (g , \ x → first (f₀ x)) x)
      , \ x → second (f₀ x))
      ( x)))
  ( is-dependent-initial-section-equiv-help extext
    ( LARI-family-domain B (\ b → Σ (p : P b) , R (b , p)))
    ( \ (g , f₀) →
      Σ ( F : LARI-family-codomain B P (g , \ y → first (f₀ y)))
      , LARI-family-codomain (total-type B P) R
        ( \ x → (g x , F x) , \ y → second (f₀ y)))
    ( \ (g , f₀) →
      ( \ x → section-is-LARI-family B P is-LARI-family-P (g , \ x → first (f₀ x)) x
      , \ x → section-is-LARI-family (total-type B P) R is-LARI-family-R
        ( \ x →
          ( g x
          , section-is-LARI-family B P is-LARI-family-P (g , \ x → first (f₀ x)) x)
        , \ x → second (f₀ x))
        ( x)))
    ( helper B P is-LARI-family-P R is-LARI-family-R)
    ( LARI-family-codomain B (\ b → Σ (p : P b) , R (b , p)))
    ( helper2 B P is-LARI-family-P R is-LARI-family-R))




#end LARI-families
```
