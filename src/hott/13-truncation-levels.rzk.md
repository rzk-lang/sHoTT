# 13. Higher Truncation Levels

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Indexing type for truncation levels

```rzk
#data 𝕋
  := neg-two-𝕋
  |  succ-𝕋 (k : 𝕋)
```

## Definition of truncatedness

```rzk
#def is-trunc
  ( k : 𝕋)
  : U → U
  :=
  match k
    ( neg-two-𝕋 ⇒ \ A → is-contr A
    | succ-𝕋 _ ih ⇒ \ A → (x y : A) → ih (x = y))
```

## k-truncated types are (k+1)-trunctated

```rzk
#def is-trunc-is-trunc-succ
  ( k : 𝕋)
  : ( A : U) → is-trunc k A → is-trunc (succ-𝕋 k) A
  :=
  match k
    ( neg-two-𝕋 ⇒
      \ A is-contr-A →
        is-prop-is-contr A is-contr-A
    | succ-𝕋 _ ih ⇒
      \ A H x y →
        ih (x = y) (H x y))
```

## Propositions are (-1)-truncated types

```rzk
#def eq-is-prop-is-neg-one-trunc
  ( A : U)
  : is-prop A = is-trunc (succ-𝕋 neg-two-𝕋) A
  := refl
```

## The unit type is (-2)-trunctated

```rzk
#def is-neg-two-trunc-Unit
  : is-trunc neg-two-𝕋 Unit
  := is-contr-Unit
```
## Closure Properties of Truncation Levels

## k-truncated types are stabel under equivalences

```rzk
#def is-trunc-Equiv-is-trunc
  ( k : 𝕋)
  : ( A B : U)
  → Equiv A B
  → is-trunc k B
  → is-trunc k A
  :=
  match k
    ( neg-two-𝕋 ⇒
      \ A B e is-contr-B →
        is-contr-equiv-is-contr' A B e is-contr-B
    | succ-𝕋 _ ih ⇒
      \ A B e is-trunc-B x y →
        ih
          ( x = y)
          ( first e x = first e y)
          ( equiv-ap-is-equiv
            A B (first e) (second e) x y)
          ( is-trunc-B (first e x) (first e y)))
```
## (k+1)-trunctated types are stable under embeddings

As a corollary we show that that f:A→B is an embedding and B is (k+1)-trunctated then so is A

```rzk
#def is-trunc-embed-is-trunc
  ( k : 𝕋)
  : ( A B : U)
  → Emb A B
  → is-trunc (succ-𝕋 k) B
  → is-trunc (succ-𝕋 k) A
  :=
  \ A B i is-trunc-B x y →
    is-trunc-Equiv-is-trunc
      k
      ( x = y)
      ( first i x = first i y)
      ( ap A B x y (first i) , second i x y)
      ( is-trunc-B (first i x) (first i y))
```

## k-truncated type are close under Π-types

```rzk
#assume funext : FunExt
```

```rzk
#def is-contr-Π-is-contr-fiber uses (funext)
  ( A : U)
  ( B : A → U)
  : ( ( x : A) → is-contr (B x))
  → is-contr ((x : A) → B x)
  :=
  \ h →
    ( ( \ x → first (h x))
    , ( \ g →
        eq-htpy funext
          A
          B
          ( \ x → first (h x))
          g
          ( \ x → second (h x) (g x))))
```

```rzk
#def is-Π-trunc-is-trunc-fiber uses (funext)
  ( k : 𝕋)
  : ( A : U)
  → ( B : A → U)
  → ( ( x : A) → is-trunc k (B x))
  → is-trunc k ((x : A) → B x)
  :=
  match k
    ( neg-two-𝕋 ⇒
      \ A B H →
        weakfunext-funext funext A B H
    | succ-𝕋 j ih ⇒
      \ A B H f g →
        is-trunc-Equiv-is-trunc
          j
          ( f = g)
          ( ( x : A) → f x = g x)
          ( equiv-FunExt funext A B f g)
          ( ih
            A
            ( \ x → f x = g x)
            ( \ x → H x (f x) (g x))))
```
## k-truncated types are closed under function types

```rzk
#def is-f-trunc-is-trunc uses (funext)
  ( k : 𝕋)
  : ( A B : U)
  → ( is-trunc k B)
  → ( is-trunc k (A → B))
  :=
  \ A B is-trunc-B →
  is-Π-trunc-is-trunc-fiber
  k
  A
  ( \ _ → B)
  ( \ _ → is-trunc-B)
```
