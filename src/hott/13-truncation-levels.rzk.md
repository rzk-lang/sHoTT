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
