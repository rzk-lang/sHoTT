# Initial sections

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Prerequisites

- `hott/*` -
-

```rzk
#assume funext : FunExt
```

## Definition of initial sections

```rzk
#def is-initial-section
  ( A : U)
  ( B : A → U)
  ( s : (a : A) → B a)
  : U
  := (a : A) → is-initial (B a) (s a)
```

```rzk
#def has-initial
  ( A : U)
  : U
  := Σ (a : A) , is-initial A a
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

## Closure properties

```rzk
#def is-initial-section-product-is-initial-section
  ( I : U)
  ( A : I → U)
  ( B : (i : I) → A i → U)
  ( s : (i : I) → (a : A i) → B i a)
  ( is-initial-section-s : (i : I) → is-initial-section (A i) (B i) (s i))
  : is-initial-section
    ( ( i : I) → A i)
    ( \ a → (i : I) → B i (a i))
    ( \ a i → s i (a i))
  :=
  \ (a : (i : I) → A i) (x : (i : I) → B i (a i))
  → is-contr-equiv-is-contr'
  ( hom ((i : I) → B i (a i)) (\ i → s i (a i)) x)
  ( ( i : I) → hom (B i (a i)) (s i (a i)) (x i))
  ( flip-ext-fun 2 Δ¹ ∂Δ¹ I
    ( \ _ i → B i (a i))
    ( \ t i → recOR(t ≡ 0₂ ↦ s i (a i) , t ≡ 1₂ ↦ x i)))
  ( weakfunext-funext funext I (\ i → hom (B i (a i)) (s i (a i)) (x i))
    ( \ i → is-initial-section-s i (a i) (x i)))
```

```rzk
#def is-dependent-initial-section-product-is-dependent-initial-section
  ( I : U)
  ( A : I → U)
  ( B : (i : I) → A i → U)
  ( s : (i : I) → (a : A i) → B i a)
  ( is-dependent-initial-section-s
    : ( i : I) → is-dependent-initial-section (A i) (B i) (s i))
  : is-dependent-initial-section
    ( ( i : I) → A i)
    ( \ a → (i : I) → B i (a i))
    ( \ a i → s i (a i))
  :=
  \ (x : (i : I) → A i)
    ( y : (i : I) → A i)
    ( Y : (i : I) → B i (y i))
    ( f : hom ((i : I) → A i) x y)
  → is-contr-equiv-is-contr'
  ( dhom ((i : I) → A i) x y f (\ a → (i : I) → B i (a i)) (\ i → s i (x i)) Y)
  ( ( i : I)
    → dhom (A i) (x i) (y i) (\ t → f t i) (B i) (s i (x i)) (Y i))
  ( flip-ext-fun 2 Δ¹ ∂Δ¹ I
    ( \ t i → B i ((f t) i))
    ( \ t i → recOR(t ≡ 0₂ ↦ s i (x i) , t ≡ 1₂ ↦ Y i)))
  ( weakfunext-funext funext I
    ( \ i → dhom (A i) (x i) (y i) (\ t → f t i) (B i) (s i (x i)) (Y i))
    ( \ i → is-dependent-initial-section-s i (x i) (y i) (Y i) (\ t → f t i)))
```

```rzk
#def is-initial-section-pullback-is-initial-section
  ( A : U)
  ( B : A → U)
  ( s : (a : A) → B a)
  ( is-initial-section-s : is-initial-section A B s)
  ( A' : U)
  ( k : A' → A)
  : is-initial-section A' (\ a' → B (k a')) (\ a' → s (k a'))
  := \ a' → is-initial-section-s (k a')
```

```rzk
#def is-dependent-initial-section-pullback-is-dependent-initial-section
  ( A : U)
  ( B : A → U)
  ( s : (a : A) → B a)
  ( is-dependent-initial-section-s : is-dependent-initial-section A B s)
  ( A' : U)
  ( k : A' → A)
  : is-dependent-initial-section A' (\ a' → B (k a')) (\ a' → s (k a'))
  :=
  \ x y Y f → is-dependent-initial-section-s (k x) (k y) Y (ap-hom A' A k x y f)
```

```rzk
#def is-initial-total-type-base-is-initial-fiber-is-dependent-initial
  ( B : U)
  ( P : B → U)
  ( b : B)
  ( is-initial-B : is-initial B b)
  ( p : P b)
  ( is-dependent-initial-p : is-dependent-initial B P b p)
  : is-initial (total-type B P) (b , p)
  :=
  \ (b' , p') →
  is-contr-equiv-is-contr'
  ( hom (total-type B P) (b , p) (b' , p'))
  ( hom B b b')
  ( equiv-comp
    ( hom (total-type B P) (b , p) (b' , p'))
    ( Σ ( h : hom B b b') , dhom B b b' h P p p')
    ( hom B b b')
    ( axiom-choice-dhom B b b' P p p')
    ( equiv-total-type-is-contr-fiber
      ( hom B b b')
      ( \ h → dhom B b b' h P p p')
      ( is-dependent-initial-p b' p')))
  ( is-initial-B b')
```

```rzk
#def bad
  ( A : U)
  ( a : A)
  : Δ¹ → U
  := \ t → (t' : Δ¹) → A [t ≡ 0₂ ↦ a]
```

```rzk
#def is-initial-section-comp-is-initial-section-is-dependent-initial-section
  ( A : U)
  ( B : A → U)
  ( s : (a : A) → B a)
  ( is-initial-section-s : is-initial-section A B s)
  ( C : total-type A B → U)
  ( s' : (x : total-type A B) → C x)
  ( is-dependent-initial-section-s'
    : is-dependent-initial-section (total-type A B) C s')
  : is-initial-section A (\ a → Σ (b : B a) , C (a , b))
    ( \ a → (s a , s' (a , s a)))
  :=
  \ a →
  is-initial-total-type-base-is-initial-fiber-is-dependent-initial
  ( B a)
  ( \ b → C (a , b))
  ( s a)
  ( is-initial-section-s a)
  ( s' (a , s a))
  ( \ b' c' f →
    is-dependent-initial-section-s' (a , s a) (a , b') c' (\ t → (a , f t)))
```

```rzk
#def is-dependent-initial-section-comp-is-dependent-initial-section
  ( A : U)
  ( B : A → U)
  ( s : (a : A) → B a)
  ( is-dependent-initial-section-s : is-dependent-initial-section A B s)
  ( C : total-type A B → U)
  ( s' : (x : total-type A B) → C x)
  ( is-dependent-initial-section-s'
    : is-dependent-initial-section (total-type A B) C s')
  : is-dependent-initial-section A (\ a → Σ (b : B a) , C (a , b))
    ( \ a → (s a , s' (a , s a)))
  :=
  \ x y (b' , c') f →
  is-contr-equiv-is-contr'
  ( dhom A x y f (\ a → Σ (b : B a) , C (a , b)) (s x , s' (x , s x)) (b' , c'))
  ( dhom A x y f B (s x) b')
  ( equiv-comp
    ( dhom A x y f (\ a → Σ (b : B a) , C (a , b)) (s x , s' (x , s x)) (b' , c'))
    ( Σ ( F : dhom A x y f B (s x) b')
      , dhom (total-type A B) (x , s x) (y , b') (\ t → (f t , F t))
        ( C) (s' (x , s x)) c')
    ( dhom A x y f B (s x) b')
    ( equiv-has-inverse
      ( dhom A x y f (\ a → Σ (b : B a) , C (a , b)) (s x , s' (x , s x)) (b' , c'))
      ( Σ ( F : dhom A x y f B (s x) b')
        , dhom (total-type A B) (x , s x) (y , b') (\ t → (f t , F t))
          ( C) (s' (x , s x)) c')
      ( \ ff → (\ t → first (ff t) , \ t → second (ff t)))
      ( \ (F , ff) t → (F t , ff t))
      ( \ _ → refl)
      ( \ _ → refl))
    ( equiv-total-type-is-contr-fiber
      ( dhom A x y f B (s x) b')
      ( \ F →
        dhom (total-type A B) (x , s x) (y , b') (\ t → (f t , F t))
        ( C) (s' (x , s x)) c')
      ( \ F →
        is-dependent-initial-section-s' (x , s x) (y , b') c'
        ( \ t → (f t , F t)))))
  ( is-dependent-initial-section-s x y b' f)
```

```rzkk
#def is-dependent-initial-section-comp-is-dependent-initial-section
  ( A : U)
  ( B : A → U)
  ( s : (a : A) → B a)
  ( C : total-type A B → U)
  ( s' : (x : total-type A B) → C x)
  ( is-dependent-initial-section-s'
  : is-dependent-initial-section (total-type A B) C s')
  : is-dependent-initial-section A (\ a → Σ (b : B a) , C (a, b))
    ( \ a → (s a, s' (a, s a)))
  :=
  \ x y (Y : C (y, (s y))) f →
  is-dependent-initial-section-s' (x, s x) (y, s y) Y (\ t → (f t, s (f t)))
```
