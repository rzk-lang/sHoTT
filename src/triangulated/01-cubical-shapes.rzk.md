# 1. Cubical shapes

This file is cubical analog of simplicial type theory, for proofing basic results about cubical shapes based on `II`.

```rzk
#lang rzk-1
```
## Basic cubical shapes

```rzk

#def □¹
  : 𝕀 → TOPE
  := \ i → TOP

```

## Simplicial predicate

Simpliciality predicate

```rzk

#def is-simplicial (A : U)
  : U
  := Equiv (𝕀 → A) (2 → A)

#def op-hom-to-hom
  ( B :ᵒᵖ U)
  ( x :ᵒᵖ B )
  ( y :ᵒᵖ B )
  ( h :ᵒᵖ (t : 2) → B [ t ≡ 0₂ ↦ x , t ≡ 1₂ ↦ y ])
  : ( ( t : 2) → ᵒᵖ B [ t ≡ 0₂ ↦ mod ᵒᵖ y , t ≡ 1₂ ↦ mod ᵒᵖ x ])
  := \ t → let mod ᵒᵖ s := flipᵒᵖ t in mod ᵒᵖ (h s)

-- Inverse of op-hom-to-hom (I ≃ ᵒᵖ I via unflip/flip; forget extension to unpack ᵒᵖ B)
#def forget-op-hom
  ( B :ᵒᵖ U)
  ( y :ᵒᵖ B)
  ( x :ᵒᵖ B)
  ( k : (t : 2) → ᵒᵖ B [ t ≡ 0₂ ↦ mod ᵒᵖ y , t ≡ 1₂ ↦ mod ᵒᵖ x ])
  ( t : 2)
  : ᵒᵖ B
  := k t

#def hom-to-op-hom
  ( B :ᵒᵖ U)
  ( x :ᵒᵖ B )
  ( y :ᵒᵖ B )
  ( k : ( ( t : 2) → ᵒᵖ B [ t ≡ 0₂ ↦ mod ᵒᵖ y , t ≡ 1₂ ↦ mod ᵒᵖ x ]))
  : ᵒᵖ ((t : 2) → B [ t ≡ 0₂ ↦ x , t ≡ 1₂ ↦ y ])
  :=
    mod ᵒᵖ (\ (t : 2) →
      let ᵒᵖ mod ᵒᵖ b := forget-op-hom B y x k (unflipᵒᵖ (mod ᵒᵖ t)) in
        b)

-- Same for extension types over I (endpoints swap under flip)
#def op-ext-I-to-ext
  ( B :ᵒᵖ U)
  ( x :ᵒᵖ B )
  ( y :ᵒᵖ B )
  ( h :ᵒᵖ (t : 𝕀) → B [ t ≡ 0₂ ↦ x , t ≡ 1₂ ↦ y ])
  : ( ( t : 𝕀) → ᵒᵖ B [ t ≡ 0₂ ↦ mod ᵒᵖ y , t ≡ 1₂ ↦ mod ᵒᵖ x ])
  := \ t → let mod ᵒᵖ s := flipᵒᵖ t in mod ᵒᵖ (h s)

#def forget-op-ext-I
  ( B :ᵒᵖ U)
  ( y :ᵒᵖ B)
  ( x :ᵒᵖ B)
  ( k : (t : 𝕀) → ᵒᵖ B [ t ≡ 0₂ ↦ mod ᵒᵖ y , t ≡ 1₂ ↦ mod ᵒᵖ x ])
  ( t : 𝕀)
  : ᵒᵖ B
  := k t

#def ext-I-to-op-ext
  ( B :ᵒᵖ U)
  ( x :ᵒᵖ B )
  ( y :ᵒᵖ B )
  ( k : ( ( t : 𝕀) → ᵒᵖ B [ t ≡ 0₂ ↦ mod ᵒᵖ y , t ≡ 1₂ ↦ mod ᵒᵖ x ]))
  : ᵒᵖ ((t : 𝕀) → B [ t ≡ 0₂ ↦ x , t ≡ 1₂ ↦ y ])
  :=
    mod ᵒᵖ (\ (t : 𝕀) →
      let ᵒᵖ mod ᵒᵖ b := forget-op-ext-I B y x k (unflipᵒᵖ (mod ᵒᵖ t)) in
        b)
```

## Cube function equivalences

```rzk

#def equiv-fun-curry
  ( I J : U)
  ( A : I → J → U)
  : Equiv
      ( ( i : I) → (j : J) → A i j)
      ( ( p : product I J) → A (first p) (second p))
  :=
    equiv-has-inverse
      ( ( i : I) → (j : J) → A i j)
      ( ( p : product I J) → A (first p) (second p))
      ( \ f p → f (first p) (second p))
      ( \ g i j → g (i , j))
      ( \ _ → refl)
      ( \ _ → refl)

#def choice-sigma3
  ( I : U)
  ( A : U)
  ( B : A → U)
  ( C : (a : A) → B a → U)
  ( D : (a : A) → (b : B a) → C a b → U)
  : Equiv
    ( ( v : I) → (Σ (a : A) , Σ (b : B a) , Σ (c : C a b) , D a b c))
    ( Σ (fa : (v : I) → A)
    , Σ (fb : (v : I) → B (fa v))
    , Σ (fc : (v : I) → C (fa v) (fb v))
    , ( ( v : I) → D (fa v) (fb v) (fc v)))
  :=
    equiv-has-inverse
      ( ( v : I) → (Σ (a : A) , Σ (b : B a) , Σ (c : C a b) , D a b c))
      ( Σ (fa : (v : I) → A)
      , Σ (fb : (v : I) → B (fa v))
      , Σ (fc : (v : I) → C (fa v) (fb v))
      , ( ( v : I) → D (fa v) (fb v) (fc v)))
      ( \ g →
        ( \ v → first (g v)
        , ( \ v → first (second (g v))
          , ( \ v → first (second (second (g v)))
            , \ v → second (second (second (g v)))))))
      ( \ (fa , (fb , (fc , fd))) → \ v → (fa v , (fb v , (fc v , fd v))))
      ( \ _ → refl)
      ( \ _ → refl)

#def equiv-fun-cube-shape-TOP
  ( I : CUBE)
  ( A : I → U)
  : Equiv
      ( ( x : I) → A x)
      ( ( t : shape (_ : I | TOP)) → A (unform t))
  :=
    equiv-has-inverse
      ( ( x : I) → A x)
      ( ( t : shape (_ : I | TOP)) → A (unform t))
      ( \ f t → f (unform t))
      ( \ g x → g (form x))
      ( \ _ → refl)
      ( \ _ → refl)

```

Simplicial monad

```rzk

#postulate simp-monad (A : U) : U

#postulate is-simplicial-simp-monad (A : U) : is-simplicial (simp-monad A)

#postulate simp-monad-pure (A : U) (a : A) : simp-monad A

-- #postulate simp-monad-elim (A : U) (B : simp-monad A -> U) (f : (a : A) -> is-simplicial (P a)) : is-simplicial (B (f pure ))

```
