# 6. Simpliciality

```rzk
#lang rzk-1

#def is-simplicial (A : U)
  : U
  := Equiv (𝕀 → A) (2 → A)

#postulate simp-monad (A : U) : U

#postulate is-simplicial-simp-monad (A : U) : is-simplicial (simp-monad A)

#postulate simp-monad-pure (A : U) (a : A) : simp-monad A

-- #postulate simp-monad-elim (A : U) (B : simp-monad A -> U) (f : (a : A) -> is-simplicial (P a)) : is-simplicial (B (f pure ))

```
