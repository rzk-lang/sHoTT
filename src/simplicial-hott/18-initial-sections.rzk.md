# Initial sections

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Prerequisites

- `hott/*` -
-

## Definition of initial sections

```rzk
#def is-initial-section
  ( A : U)
  ( B : A → U)
  ( s : (a : A) → B a)
  : U
  := (a : A) → is-initial (B a) (s a)
```

## Dependent initial sections

```rzk
#def is-dependent-initial
  ( A : U)
  ( B : A → U)
  ( a : A)
  ( b : B a)
  : U
  :=
    ( a' : A)
  → ( b' : B a')
  → ( f : hom A a a')
  → is-contr (dhom A a a' f B b b')
```

```rzk
#def has-dependent-initial
  ( A : U)
  ( B : A → U)
  ( a : A)
  : U
  := Σ (b : B a) , is-dependent-initial A B a b
```

```rzk
#def is-dependent-initial-section
  ( A : U)
  ( B : A → U)
  ( s : (a : A) → B a)
  : U
  := (a : A) → is-dependent-initial A B a (s a)
```

```rzk
#def is-initial-section-is-dependent-initial-section
  ( A : U)
  ( B : A → U)
  ( s : (a : A) → B a)
  ( is-dependent-initial-section-s : is-dependent-initial-section A B s)
  : is-initial-section A B s
  := \ a b → is-dependent-initial-section-s a a b (id-hom A a)
```

## Initial sections are dependent initial sections

```rzk
#section is-dependent-initial-section-is-initial-section-is-inner-family

#variable A : U
#variable B : A → U
#variable is-inner-family-B : is-inner-family A B
#variable s : (a : A) → B a
#variable is-initial-section-s : is-initial-section A B s
```

```rzk
#def temp-1i4p-ctr
  ( a' : A)
  ( b' : B a')
  : hom (B a') (s a') (b')
  :=
  center-contraction
    ( hom (B a') (s a') b')
    ( is-initial-section-s a' b')
```

```rzk
#def temp-1i4p-horn uses (is-initial-section-s)
  ( a a' : A)
  ( b' : B a')
  ( f : hom A a a')
  : ( ( t₁ , t₂) : Λ²₁) → B (f t₁)
  := \ (t₁ , t₂) → recOR(t₂ ≡ 0₂ ↦ s (f t₁) , t₁ ≡ 1₂ ↦ temp-1i4p-ctr a' b' t₂)
```

```rzk
#def temp-1i4p-trig uses (s is-initial-section-s)
  ( a a' : A)
  ( b' : B a')
  ( f : hom A a a')
  : ( t : Δ²) → B (f (first t)) [Λ²₁ t ↦ temp-1i4p-horn a a' b' f t]
  :=
  center-contraction
  ( ( t : Δ²) → B (f (first t)) [Λ²₁ t ↦ temp-1i4p-horn a a' b' f t])
  ( is-inner-family-B
    ( \ t → f (first t))
    ( temp-1i4p-horn a a' b' f))
```

```rzk
#def temp-1i4p-lift uses (is-initial-section-s is-inner-family-B)
  ( a a' : A)
  ( b' : B a')
  ( f : hom A a a')
  : dhom A a a' f B (s a) b'
  := \ t → temp-1i4p-trig a a' b' f (t , t)
```

```rzk
#def temp-1i4p-dependent-square
  ( a a' : A)
  ( b' : B a')
  ( f : hom A a a')
  ( F : dhom A a a' f B (s a) b')
  : dependent-square A a a' a a'
    ( f) (id-hom A a) (f) (id-hom A a')
    ( \ t → f (first t))
    ( B) (s a) (s a') (s a) (b')
    ( \ t → s (f t)) (temp-1i4p-ctr a (s a)) (F) (temp-1i4p-ctr a' b')
  :=
  \ (t₁ , t₂) →
  center-contraction
  ( hom (B (f t₁)) (s (f t₁)) (F t₁))
  ( is-initial-section-s (f t₁) (F t₁))
  ( t₂)

#def temp-1i4p-dependent-square'
  ( a a' : A)
  ( b' : B a')
  ( f : hom A a a')
  ( F : dhom A a a' f B (s a) b')
  : dependent-square A a a' a a'
    ( f) (id-hom A a) (f) (id-hom A a')
    ( \ t → f (first t))
    ( B) (s a) (s a') (s a) (b')
    ( \ t → s (f t)) (id-hom (B a) (s a)) (F) (temp-1i4p-ctr a' b')
  :=
  transport
  ( hom (B a) (s a) (s a))
  ( \ g →
    dependent-square A a a' a a'
    ( f) (id-hom A a) (f) (id-hom A a')
    ( \ t → f (first t))
    ( B) (s a) (s a') (s a) (b')
    ( \ t → s (f t)) g (F) (temp-1i4p-ctr a' b'))
  ( temp-1i4p-ctr a (s a))
  ( id-hom (B a) (s a))
  ( homotopy-contraction
    ( hom (B a) (s a) (s a))
    ( is-initial-section-s a (s a))
    ( id-hom (B a) (s a)))
  ( temp-1i4p-dependent-square a a' b' f F)
```

```rzk
#def temp-1i4p-dependent-trig uses (is-initial-section-s)
  ( a a' : A)
  ( b' : B a')
  ( f : hom A a a')
  ( F : dhom A a a' f B (s a) b')
  : dhom2 A a a' a' f (id-hom A a') f (\ t → f (first t))
    ( B) (s a) (s a') b' (\ t → s (f t)) (temp-1i4p-ctr a' b') F
  :=
  first
  ( equiv-dependent-square-left-id-dhom2-is-inner-family
    ( A) a a' a' f f (id-hom A a') (\ t → f (first t))
    ( B) is-inner-family-B (s a) (s a') b'
    ( \ t → s (f t))
    ( F)
    ( temp-1i4p-ctr a' b'))
  ( temp-1i4p-dependent-square' a a' b' f F)
```

```rzk
#def temp-1i4p-is-unique-lift uses (is-initial-section-s)
  ( a a' : A)
  ( b' : B a')
  ( f : hom A a a')
  ( F : dhom A a a' f B (s a) b')
  : temp-1i4p-lift a a' b' f = F
  :=
  ap
  ( ( t : Δ²) → B (f (first t)) [Λ²₁ t ↦ temp-1i4p-horn a a' b' f t])
  ( dhom A a a' f B (s a) b')
  ( temp-1i4p-trig a a' b' f)
  ( temp-1i4p-dependent-trig a a' b' f F)
  ( \ τ t → τ (t , t))
  ( homotopy-contraction
    ( ( t' : Δ²) → B (f (first t')) [Λ²₁ t' ↦ temp-1i4p-horn a a' b' f t'])
    ( is-inner-family-B
      ( \ t' → f (first t'))
      ( temp-1i4p-horn a a' b' f))
    ( temp-1i4p-dependent-trig a a' b' f F))
```

```rzk
#def is-dependent-initial-section-is-initial-section-is-inner-family
  uses (is-initial-section-s is-inner-family-B)
  : is-dependent-initial-section A B s
  :=
  \ a a' b' f → (temp-1i4p-lift a a' b' f , temp-1i4p-is-unique-lift a a' b' f)
```

```rzk
#end is-dependent-initial-section-is-initial-section-is-inner-family
```
