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
```

Simplicial monad

```rzk

#postulate simp-monad (A : U) : U

#postulate is-simplicial-simp-monad (A : U) : is-simplicial (simp-monad A)

#postulate simp-monad-pure (A : U) (a : A) : simp-monad A

-- #postulate simp-monad-elim (A : U) (B : simp-monad A -> U) (f : (a : A) -> is-simplicial (P a)) : is-simplicial (B (f pure ))

```
