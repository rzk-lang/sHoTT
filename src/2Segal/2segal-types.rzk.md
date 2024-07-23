# 2-Segal spaces

Experimental formalization project on 2-Segal spaces.

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

### The 3 dimensional 2-Segal horns

```rzkx
#def Λ³₍₀₂₎
  : Δ³ → TOPE
  :=
    \ ((t1 , t2) , t3) → t3 ≡ 0₂ ∨ t1 ≡ t2 -- This could be t3==t2.

#def Λ³₍₁₃₎
  : Δ³ → TOPE
  :=
    \ ((t1 , t2) , t3) → t2 ≡ t3 ∨ t1 ≡ 1₂ -- This could be t1==t2.
```

### 2-Segal types

We use the conventions from the definition of `#!rzk hom3` from
`11-adjunctions.rzk`.

```rzk
#def is-2-segal₍₀₂₎
  ( A : U)
  : U
  :=
    ( w : A) → (x : A) → (y : A) → (z : A)
  → ( f : hom A w x) → (gf : hom A w y) → (hgf : hom A w z)
  → ( g : hom A x y) → (h : hom A y z)
  → ( α₃ : hom2 A w x y f g gf) → (α₁ : hom2 A w y z gf h hgf)
  → is-contr
      ( Σ ( hg : hom A x z)
      , ( Σ ( α₂ : hom2 A w x z f hg hgf)
        , ( Σ ( α₀ : hom2 A x y z g h hg)
            , hom3 A w x y z f gf hgf g hg h α₃ α₂ α₁ α₀)))

#def is-2-segal₍₁₃₎
  ( A : U)
  : U
  :=
    ( w : A) → (x : A) → (y : A) → (z : A)
  → ( f : hom A w x) → (hgf : hom A w z)
  → ( g : hom A x y) → (hg : hom A x z) → (h : hom A y z)
  → ( α₂ : hom2 A w x z f hg hgf) → (α₀ : hom2 A x y z g h hg)
  → is-contr
      ( Σ ( gf : hom A w y)
      , ( Σ ( α₃ : hom2 A w x y f g gf)
        , ( Σ ( α₁ : hom2 A w y z gf h hgf)
            , hom3 A w x y z f gf hgf g hg h α₃ α₂ α₁ α₀)))

#def is-2-segal
  ( A : U)
  : U
  :=
    product (is-2-segal₍₀₂₎ A) (is-2-segal₍₁₃₎ A)
```

```rzk
#def 3horn₍₀₂₎
  ( A : U)
  ( w x y z : A)
  ( f : hom A w x)
  ( gf : hom A w y)
  ( hgf : hom A w z)
  ( g : hom A x y)
  ( h : hom A y z)
  ( α₃ : hom2 A w x y f g gf)
  ( α₁ : hom2 A w y z gf h hgf)
  : Λ³₍₀₂₎ → A
  :=
    \ ((t₁ , t₂) , t₃) →
      recOR
        ( t₃ ≡ 0₂ ↦ α₃ (t₁ , t₂)
        , t₁ ≡ t₂ ↦ α₁ (t₁ , t₃)) -- This could be t3==t2.

#def 3horn₍₁₃₎
  ( A : U)
  ( w x y z : A)
  ( f : hom A w x)
  ( hgf : hom A w z)
  ( g : hom A x y)
  ( hg : hom A x z)
  ( h : hom A y z)
  ( α₂ : hom2 A w x z f hg hgf)
  ( α₀ : hom2 A x y z g h hg)
  : Λ³₍₁₃₎ → A
  :=
  \ ((t₁ , t₂) , t₃) →
    recOR
      ( t₂ ≡ t₃ ↦ α₂ (t₁ , t₃) -- This could be t1==t2.
      , t₁ ≡ 1₂ ↦ α₀ (t₂ , t₃))

#def associators-are-3horn-fillings₍₀₂₎
  ( A : U)
  ( w x y z : A)
  ( f : hom A w x)
  ( gf : hom A w y)
  ( hgf : hom A w z)
  ( g : hom A x y)
  ( h : hom A y z)
  ( α₃ : hom2 A w x y f g gf)
  ( α₁ : hom2 A w y z gf h hgf)
  : Equiv
      ( Σ ( hg : hom A x z)
      , ( Σ ( α₂ : hom2 A w x z f hg hgf)
        , ( Σ ( α₀ : hom2 A x y z g h hg)
            , hom3 A w x y z f gf hgf g hg h α₃ α₂ α₁ α₀)))
      ( ( t : Δ³) → A [Λ³₍₀₂₎ t ↦ 3horn₍₀₂₎ A w x y z f gf hgf g h α₃ α₁ t])
  :=
    ( \ H t → second (second (second H)) t
      , ( ( \ k → (\ t → k ((t , t) , t)
          , ( \ (t , s) → k ((t , s) , s)
            , ( \ (t , s) → k ((1₂ , t) , s)
              , \ ((t1 , t2) , t3) → k ((t1 , t2) , t3))))
        , \ H → refl)
          , ( U , U)
      )
    )
```

A type is 2-Segal if it is local with respect to 2-Segal horn inclusions.

```rzk
#def is-local-2-segal-horn-inclusion
  ( A : U)
  : U
  :=
    product
     ( is-local-type (2 × 2 × 2) Δ³ Λ³₍₀₂₎ A)
     ( is-local-type (2 × 2 × 2) Δ³ Λ³₍₁₃₎ A)
```
