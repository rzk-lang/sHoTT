# 2-Segal spaces

Experimental formalization project on 2-Segal spaces.

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

```rzk
-- #def is-2segal-local
--   ( A : U)
--   : U
--   :=
--     product
--      ( is-local-type (2 × 2 × 2) Δ³ (2segalhorn1) A)
--      ( is-local-type (2 × 2 × 2) Δ³ (2segalhorn2) A)
```

```rzk
-- #def 3hornfill1
--   ( A : U)
--   : U
--   :=
--     ( x : A) → (y : A) → (z : A) → (w : A)
--   → ( f : hom A x y) → (g : hom A y z) → (h : hom A x z)
--   → ( b : hom A x w) → (d : hom A y w) → (e : hom A z w)
--   → ( α : hom2 A x y z f g h) → (β : hom2 A x y w f d b)
--   → ( γ : hom2 A x z w h d e)
```
