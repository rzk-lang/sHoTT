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
#def is-trunc-succ-is-trunc
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

## Closure properties of truncation levels

### k-truncated types are stable under equivalences

```rzk
#def is-trunc-equiv-is-trunc
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
        ( equiv-ap-is-equiv A B (first e) (second e) x y)
        ( is-trunc-B (first e x) (first e y)))
```

### (k+1)-trunctated types are stable under embeddings

As a corollary we show that that if `f:A→B` is an embedding and `B` is
`(k+1)`-trunctated, then so is `A`.

```rzk
#def is-trunc-emb-is-trunc
  ( k : 𝕋)
  ( A B : U)
  ( i : Emb A B)
  : is-trunc (succ-𝕋 k) B
  → is-trunc (succ-𝕋 k) A
  :=
  \ is-trunc-B x y →
    is-trunc-equiv-is-trunc
    ( k)
    ( x = y)
    ( first i x = first i y)
    ( ap A B x y (first i) , second i x y)
    ( is-trunc-B (first i x) (first i y))
```

### k-truncated types are closed under Π-types

```rzk
#assume funext
  : FunExt
```

```rzk
#def is-trunc-function-type-fiberwise-is-trunc uses (funext)
  ( k : 𝕋)
  ( A : U)
  : ( B : A → U)
  → ( ( x : A) → is-trunc k (B x))
  → is-trunc k ((x : A) → B x)
  :=
  match k
    ( neg-two-𝕋 ⇒
      \ B H →
        weakfunext-funext funext A B H
    | succ-𝕋 j ih ⇒
      \ B H f g →
        is-trunc-equiv-is-trunc
        ( j)
        ( f = g)
        ( ( x : A) → f x = g x)
        ( equiv-FunExt funext A B f g)
        ( ih
          ( \ x → f x = g x)
          ( \ x → H x (f x) (g x))))
```

As a corollary, non-dependent function types with `k`-truncated codomain are
`k`-truncated.

```rzk
#def is-trunc-function-type-is-trunc-codomain uses (funext)
  ( k : 𝕋)
  ( A B : U)
  : ( is-trunc k B)
  → ( is-trunc k (A → B))
  :=
  \ is-trunc-B →
    is-trunc-function-type-fiberwise-is-trunc
    ( k)
    ( A)
    ( \ _ → B)
    ( \ _ → is-trunc-B)
```

### Σ-types of k-truncated types are k-truncated

```rzk
#def is-contr-total-type-fiberwise-is-contr-is-contr-base
  ( A : U)
  ( B : A → U)
  ( is-contr-A : is-contr A)
  ( is-contr-fam : (x : A) → is-contr (B x))
  : is-contr (Σ (x : A) , B x)
  :=
  is-contr-equiv-is-contr'
    ( Σ ( x : A) , B x)
    ( B (first is-contr-A))
    ( equiv-center-fiber-total-type-is-contr-base A is-contr-A B)
    ( is-contr-fam (first is-contr-A))
```

```rzk
#def is-trunc-total-type-fiberwise-is-trunc-is-trunc-base
  ( k : 𝕋)
  : ( A : U)
  → ( B : A → U)
  → ( is-trunc k A)
  → ( ( x : A) → (is-trunc k (B x)))
  → ( is-trunc k (Σ (x : A) , B x))
  :=
  match k
    ( neg-two-𝕋 ⇒
      \ A B is-contr-A is-contr-fam →
        is-contr-total-type-fiberwise-is-contr-is-contr-base
        A B is-contr-A is-contr-fam
    | succ-𝕋 k' ih ⇒
      \ A B is-trunc-A is-trunc-fam s t →
        is-trunc-equiv-is-trunc
          ( k')
          ( s = t)
          ( Eq-Σ A B s t)
          ( extensionality-Σ A B s t)
          ( ih
            ( first s = first t)
            ( \ p → transport A B (first s) (first t) p (second s) = second t)
            ( is-trunc-A (first s) (first t))
            ( \ p →
                is-trunc-fam
                ( first t)
                ( transport A B (first s) (first t) p (second s))
                ( second t))))
```
### k-truncated types are closed under retracts

```rzk
#def is-contr-retract-is-retract-of-contr
  ( A B : U)
  : ( is-retract-of A B)
  → ( is-contr B)
  → ( is-contr A)
  := \ is-retract-of-B is-contr-B →
  ( first (second is-retract-of-B) (first is-contr-B)
  , \ (x : A) → concat
      ( A)
      ( first (second is-retract-of-B) (first is-contr-B))
      ( comp A B A (first (second is-retract-of-B)) (first is-retract-of-B) x)
      ( x)
      ( ap
        ( B)
        ( A)
        ( first is-contr-B)
        ( first is-retract-of-B x)
        ( first (second is-retract-of-B))
        ( second is-contr-B (first is-retract-of-B x)))
      ( second (second is-retract-of-B) x))

#def is-retract-of-path-types-is-retract-of
  ( A B : U)
  ( ( s , (r , η)) : is-retract-of A B)
  ( x y : A)
  : is-retract-of (x = y) (s x = s y)
  :=
    ( ap A B x y s
    , ( \ q →
          triple-concat A x (r (s x)) (r (s y)) y
            ( rev A (r (s x)) x (η x))
            ( ap B A (s x) (s y) r q)
            ( η y)
      , \ p →
          ind-path
            ( A)
            ( x)
            ( \ y' p' →
                triple-concat A x (r (s x)) (r (s y')) y'
                  ( rev A (r (s x)) x (η x))
                  ( ap B A (s x) (s y') r (ap A B x y' s p'))
                  ( η y')
                = p')
            ( rev-refl-id-triple-concat A (r (s x)) x (η x))
            ( y)
            ( p)))

#def is-trunc-retract-is-retract-of-trunc
  ( k : 𝕋)
  : ( A B : U)
  → ( is-retract-of A B)
  → ( is-trunc k B)
  → ( is-trunc k A)
  :=
  match k
    ( neg-two-𝕋 ⇒
      \ A B H is-contr-B →
       is-contr-retract-is-retract-of-contr A B H is-contr-B
    | succ-𝕋 _ ih ⇒
       \ A B H is-trunc-B x y →
         ih
        ( x = y)
        ( first H x = first H y)
        ( is-retract-of-path-types-is-retract-of A B H x y)
        ( is-trunc-B (first H x) (first H y)))
```

### Being a k-truncated type is a property

```rzk
#assume weakfunext : WeakFunExt
```

```rzk
#def is-property-is-trunc
  uses (weakfunext funext)
  ( k : 𝕋)
  : ( A : U)
  → is-prop (is-trunc k A)
  :=
  match k
    ( neg-two-𝕋 ⇒
      \ A → is-prop-is-contr-itself weakfunext A
    | succ-𝕋 k' ih ⇒
      \ A →
      is-prop-fiberwise-prop2
        ( funext)
        ( A)
        ( \ _ → A)
        ( \ x y → is-trunc k' (x = y))
        ( \ x y → ih (x = y)))
```
