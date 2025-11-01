# Cocartesian Fibrations

These formalizations capture cocartesian families as treated in
[Buchholtz and Weinberger (2023), Higher Structures 7](https://doi.org/10.21136/HS.2023.04).

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Prerequisites

- `hott/*` - We require various prerequisites from homotopy type theory, for
  instance the axiom of function extensionality.
- `03-simplicial-type-theory.rzk.md` — We rely on definitions of simplicies and
  their subshapes.
- `04-extension-types.rzk.md` — We use extension extensionality.
- `12-orthogonal-families.rzk.md` - We make use of inner families.
- `./20-lari-families.rzk.md` - We make use of LARI families.

```rzk
#assume funext : FunExt
#assume extext : ExtExt
```

## Naive Cocartesian Families

### Cocartesian arrows

Here we define the proposition that a dependent arrow in a family is
cocartesian. This is an alternative version using unpacked extension types, as
this is preferred for usage.

```rzk title="BW23, Definition 5.1.1"
#def is-cocartesian-arrow
  ( B : U)
  ( b b' : B)
  ( u : hom B b b')
  ( P : B → U)
  ( e : P b)
  ( e' : P b')
  ( f : dhom B b b' u P e e')
  : U
  :=
    ( b'' : B) → (v : hom B b' b'') → (w : hom B b b'')
    → ( sigma : hom2 B b b' b'' u v w) → (e'' : P b'')
    → ( h : dhom B b b'' w P e e'')
    → is-contr
        ( Σ ( g : dhom B b' b'' v P e' e'')
        , ( dhom2 B b b' b'' u v w sigma P e e' e'' f g h))

#def is-prop-is-cocartesian-arrow
  ( B : U)
  ( b b' : B)
  ( u : hom B b b')
  ( P : B → U)
  ( e : P b)
  ( e' : P b')
  ( f : dhom B b b' u P e e')
  : is-prop (is-cocartesian-arrow B b b' u P e e' f)
  :=
  is-prop-fiberwise-prop6 funext
  ( B)
  ( \ b'' → hom B b' b'')
  ( \ b'' v → hom B b b'')
  ( \ b'' v w → hom2 B b b' b'' u v w)
  ( \ b'' v w sigma → P b'')
  ( \ b'' v w sigma e'' → dhom B b b'' w P e e'')
  ( \ b'' v w sigma e'' h →
    is-contr
    ( Σ ( g : dhom B b' b'' v P e' e'')
      , ( dhom2 B b b' b'' u v w sigma P e e' e'' f g h)))
  ( \ b'' v w sigma e'' h →
    is-prop-is-contr-itself (weakfunext-funext funext)
    ( Σ ( g : dhom B b' b'' v P e' e'')
    , ( dhom2 B b b' b'' u v w sigma P e e' e'' f g h)))
```

### Cocartesian lifts

The following is the type of cocartesian lifts of a fixed arrow in the base with
a given starting point in the fiber.

```rzk title="BW23, Definition 5.1.2"
#def cocartesian-lift
  ( B : U)
  ( b b' : B)
  ( u : hom B b b')
  ( P : B → U)
  ( e : P b)
  : U
  :=
    Σ ( e' : P b')
    , Σ ( f : dhom B b b' u P e e') , is-cocartesian-arrow B b b' u P e e' f
```

### Cocartesian family

A family over cocartesian if it is isoinner and any arrow in the has a
cocartesian lift, given a point in the fiber over the domain.

```rzk title="BW23, Definition 5.2.1"
#def has-cocartesian-lifts
  ( B : U)
  ( P : B → U)
  : U
  :=
    ( b : B) → (b' : B) → (u : hom B b b')
    → ( e : P b) → (Σ (e' : P b')
      , ( Σ ( f : dhom B b b' u P e e') , is-cocartesian-arrow B b b' u P e e' f))
```

```rzk title="BW23, Definition 5.2.2"
#def is-naive-cocartesian-family
  ( B : U)
  ( P : B → U)
  : U
  := product (is-inner-family B P) (has-cocartesian-lifts B P)
```

## Definition via LARI Families

```rzk
#def is-cocartesian-family
  ( B : U)
  ( P : B → U)
  : U
  := is-LARI-family 2 Δ¹ (\ t → t ≡ 0₂) B P
```

## Cocartesian Families are LARI Families

```rzk
#section is-cocartesian-arrow-equiv-is-dependent-initial

#variable B : U
#variable P : B → U
#variable is-inner-family-P : is-inner-family B P

#def temp-96cf-G
  : U
  := Σ (f : Δ¹ → B) , P (f 0₂)

#def temp-96cf-Q uses (B)
  ( ( f , e) : temp-96cf-G)
  : U
  := (t : Δ¹) → P (f t) [t ≡ 0₂ ↦ e]

#variable f : Δ¹ → B
#variable e : P (f 0₂)
#variable F : temp-96cf-Q (f , e)

#def temp-96cf-A
  : U
  :=
  ( Σ ( b'' : B)
    , Σ ( g : hom B (f 1₂) b'')
      , Σ ( h : hom B (f 0₂) b'')
        , Σ ( τ : hom2 B (f 0₂) (f 1₂) b'' f g h)
          , Σ ( e'' : P b'')
            , dhom B (f 0₂) b'' (\ t → τ (t , t)) P e e'')

#def temp-96cf-A'
  : U
  :=
  ( Σ ( f' : Δ¹ → B)
    , Σ ( e' : P(f' 0₂))
      , Σ ( m : hom temp-96cf-G (f , e) (f' , e'))
        , ( t : Δ¹) → P (f' t) [t ≡ 0₂ ↦ e'])

#def temp-96cf-R
  ( ( b'' , (g , (h , (τ , (e'' , F'))))) : temp-96cf-A)
  : U
  :=
  ( Σ ( G : dhom B (f 1₂) b'' g P (F 1₂) e'')
    , dhom2 B (f 0₂) (f 1₂) b'' f g h τ P e (F 1₂) e'' (\ t → F t) G F')

#def temp-96cf-R' uses (P B)
  ( ( f' , (e' , (m , F'))) : temp-96cf-A')
  : U
  := dhom temp-96cf-G (f , e) (f' , e') m (temp-96cf-Q) F F'

#def temp-96cf-alpha₁ uses (f P B)
  ( ( b'' , (g , (h , (τ , (e'' , F'))))) : temp-96cf-A)
  : temp-96cf-A'
  :=
  ( \ t → τ (t , t)
    , ( e
      , ( \ s → (\ t → recOR(Δ² (t , s) ↦ τ (t , s) , t ≤ s ↦ h t) , e)
        , F')))

#def temp-96cf-A'-inner-filler uses (e f B)
  ( ( f' , (e' , (m , F'))) : temp-96cf-A')
  : ( ( t , s) : Δ²) → P (first (m t) s) [t ≡ 1₂ ↦ F' s , s ≡ 0₂ ↦ second (m t)]
  :=
  center-contraction
  ( ( ( t , s) : Δ²) → P (first (m t) s) [t ≡ 1₂ ↦ F' s , s ≡ 0₂ ↦ second (m t)])
  ( is-inner-family-P
    ( \ (t , s) → first (m t) s)
    ( \ (t , s) → recOR(t ≡ 1₂ ↦ F' s , s ≡ 0₂ ↦ second (m t))))

#def temp-96cf-A'-diag uses (is-inner-family-P)
  ( ( f' , (e' , (m , F'))) : temp-96cf-A')
  : dhom B (f 0₂) (f' 1₂) (\ t → first (m t) t) P e (F' 1₂)
  :=
  \ t → temp-96cf-A'-inner-filler (f' , (e' , (m , F'))) (t , t)

#def temp-96cf-alpha₂ uses (e f is-inner-family-P P B)
  ( ( f' , (e' , (m , F'))) : temp-96cf-A')
  : temp-96cf-A
  :=
  ( f' 1₂
  , ( \ t → first (m t) 1₂
    , ( \ t → first (m t) t
      , ( \ (t , s) → first (m s) t
        , ( F' 1₂
          , temp-96cf-A'-diag (f' , (e' , (m , F'))))))))

#def temp-96cf-equiv-cocartesian-arrow
  : Equiv
    ( is-cocartesian-arrow B (f 0₂) (f 1₂) f P e (F 1₂) (\ t → F t))
    ( ( a : temp-96cf-A) → is-contr (temp-96cf-R a))
  :=
  equiv-has-inverse
  ( is-cocartesian-arrow B (f 0₂) (f 1₂) f P e (F 1₂) (\ t → F t))
  ( ( a : temp-96cf-A) → is-contr (temp-96cf-R a))
  ( \ is-cocartesian-arrow-F (b'' , (g , (h , (τ , (e'' , F'))))) →
    is-cocartesian-arrow-F b'' g h τ e'' (\ t → F' t))
  ( \ a-is-contr-R-a b'' v w sigma e'' h → a-is-contr-R-a (b'' , (v , (w , (sigma , (e'' , h))))))
  ( \ _ → refl)
  ( \ _ → refl)

#def temp-96cf-equiv-dependent-initial uses (P B)
  : Equiv
    ( ( a' : temp-96cf-A') → is-contr (temp-96cf-R' a'))
    ( is-dependent-initial temp-96cf-G temp-96cf-Q (f , e) F)
  :=
  equiv-has-inverse
  ( ( a' : temp-96cf-A') → is-contr (temp-96cf-R' a'))
  ( is-dependent-initial temp-96cf-G temp-96cf-Q (f , e) F)
  ( \ a'-is-contr-R'-a' (f' , e') F' m → a'-is-contr-R'-a' (f' , (e' , (m , F'))))
  ( \ is-dependent-initial-F (f' , (e' , (m , F'))) →
    is-dependent-initial-F (f' , e') F' m)
  ( \ _ → refl)
  ( \ _ → refl)

#def temp-96cf-is-contr-R-a-is-contr-R'-alpha₁-a
  ( ( b'' , (g , (h , (τ , (e'' , F'))))) : temp-96cf-A)
  : is-contr (temp-96cf-R' (temp-96cf-alpha₁ (b'' , (g , (h , (τ , (e'' , F')))))))
    → is-contr (temp-96cf-R (b'' , (g , (h , (τ , (e'' , F'))))))
  :=
  is-contr-equiv-is-contr
  ( temp-96cf-R' (temp-96cf-alpha₁ (b'' , (g , (h , (τ , (e'' , F')))))))
  ( temp-96cf-R (b'' , (g , (h , (τ , (e'' , F'))))))
  ( equiv-comp
    ( temp-96cf-R' (temp-96cf-alpha₁ (b'' , (g , (h , (τ , (e'' , F')))))))
    ( Σ ( G : dhom B (f 1₂) b'' g P (F 1₂) e'')
      , dependent-square B (f 0₂) (f 1₂) (f 0₂) b''
        ( f) (id-hom B (f 0₂)) h g
        ( \ (t , s) → recOR(Δ² (t , s) ↦ τ (t , s) , t ≤ s ↦ h t))
        ( P) e (F 1₂) e e''
        ( \ t → F t) (id-dhom B (f 0₂) P e) F' G)
    ( temp-96cf-R (b'' , (g , (h , (τ , (e'' , F'))))))
    ( equiv-has-inverse
      ( temp-96cf-R' (temp-96cf-alpha₁ (b'' , (g , (h , (τ , (e'' , F')))))))
      ( Σ ( G : dhom B (f 1₂) b'' g P (F 1₂) e'')
        , dependent-square B (f 0₂) (f 1₂) (f 0₂) b''
          ( f) (id-hom B (f 0₂)) h g
          ( \ (t , s) → recOR(Δ² (t , s) ↦ τ (t , s) , t ≤ s ↦ h t))
          ( P) e (F 1₂) e e''
          ( \ t → F t) (id-dhom B (f 0₂) P e) F' G)
      ( \ M → (\ t → M t 1₂ , \ (t , s) → M s t))
      ( \ (G , σ) t s → σ (s , t))
      ( \ _ → refl)
      ( \ _ → refl))
    ( total-equiv-family-of-equiv
      ( dhom B (f 1₂) b'' g P (F 1₂) e'')
      ( \ G →
        dependent-square B (f 0₂) (f 1₂) (f 0₂) b''
        ( f) (id-hom B (f 0₂)) h g
        ( \ (t , s) → recOR(Δ² (t , s) ↦ τ (t , s) , t ≤ s ↦ h t))
        ( P) e (F 1₂) e e''
        ( \ t → F t) (id-dhom B (f 0₂) P e) F' G)
      ( \ G → dhom2 B (f 0₂) (f 1₂) b'' f g h τ P e (F 1₂) e'' (\ t → F t) G F')
      ( equiv-dependent-square-left-id-dhom2-is-inner-family B
        ( f 0₂) (f 1₂) b''
        ( f) h g
        ( τ)
        ( P) is-inner-family-P
        ( e) (F 1₂) e''
        ( \ t → F t) F')))

#def temp-96cf-is-contr-R'-a'-is-contr-R-alpha₂-a'
  ( ( f' , (e' , (m , F'))) : temp-96cf-A')
  : is-contr (temp-96cf-R (temp-96cf-alpha₂ (f' , (e' , (m , F')))))
    → is-contr (temp-96cf-R' (f' , (e' , (m , F'))))
  :=
  is-contr-equiv-is-contr'
  ( temp-96cf-R' (f' , (e' , (m , F'))))
  ( temp-96cf-R (temp-96cf-alpha₂ (f' , (e' , (m , F')))))
  ( equiv-quadruple-comp
    ( temp-96cf-R' (f' , (e' , (m , F'))))
    ( Σ ( G : dhom B (f 1₂) (f' 1₂) (\ t → first (m t) 1₂) P (F 1₂) (F' 1₂))
      , dependent-square B (f 0₂) (f 1₂) (f' 0₂) (f' 1₂)
        ( f) (\ t → first (m t) 0₂) f' (\ t → first (m t) 1₂)
        ( \ (t , s) → first (m s) t)
        ( P) e (F 1₂) e' (F' 1₂)
        ( \ t → F t) (\ t → second (m t)) (\ t → F' t) G)
    ( Σ ( G : dhom B (f 1₂) (f' 1₂) (\ t → first (m t) 1₂) P (F 1₂) (F' 1₂))
      , Σ ( D : dhom B (f 0₂) (f' 1₂) (\ t → first (m t) t) P e (F' 1₂))
        , product
          ( dhom2 B (f 0₂) (f 1₂) (f' 1₂)
            ( f) (\ t → first (m t) 1₂) (\ t → first (m t) t)
            ( \ (t , s) → first (m s) t)
            ( P) e (F 1₂) (F' 1₂)
            ( \ t → F t) G D)
          ( dhom2 B (f 0₂) (f' 0₂) (f' 1₂)
            ( \ t → first (m t) 0₂) (f') (\ t → first (m t) t)
            ( \ (t , s) → first (m t) s)
            ( P) e (F' 0₂) (F' 1₂)
            ( \ t → second (m t)) (\ t → F' t) D))
    ( Σ ( G : dhom B (f 1₂) (f' 1₂) (\ t → first (m t) 1₂) P (F 1₂) (F' 1₂))
      , Σ ( Dτ : Σ (D : dhom B (f 0₂) (f' 1₂) (\ t → first (m t) t) P e (F' 1₂))
                , dhom2 B (f 0₂) (f' 0₂) (f' 1₂)
                  ( \ t → first (m t) 0₂) (f') (\ t → first (m t) t)
                  ( \ (t , s) → first (m t) s)
                  ( P) e (F' 0₂) (F' 1₂)
                  ( \ t → second (m t)) (\ t → F' t) D)
        , dhom2 B (f 0₂) (f 1₂) (f' 1₂)
          ( f) (\ t → first (m t) 1₂) (\ t → first (m t) t)
          ( \ (t , s) → first (m s) t)
          ( P) e (F 1₂) (F' 1₂)
          ( \ t → F t) G (first Dτ))
    ( temp-96cf-R (temp-96cf-alpha₂ (f' , (e' , (m , F')))))
    ( equiv-has-inverse
      ( temp-96cf-R' (f' , (e' , (m , F'))))
      ( Σ ( G : dhom B (f 1₂) (f' 1₂) (\ t → first (m t) 1₂) P (F 1₂) (F' 1₂))
        , dependent-square B (f 0₂) (f 1₂) (f' 0₂) (f' 1₂)
          ( f) (\ t → first (m t) 0₂) f' (\ t → first (m t) 1₂)
          ( \ (t , s) → first (m s) t)
          ( P) e (F 1₂) e' (F' 1₂)
          ( \ t → F t) (\ t → second (m t)) (\ t → F' t) G)
      ( \ M → (\ t → M t 1₂ , \ (t , s) → M s t))
      ( \ (G , σ) t s → σ (s , t))
      ( \ _ → refl)
      ( \ _ → refl))
    ( total-equiv-family-of-equiv
      ( dhom B (f 1₂) (f' 1₂) (\ t → first (m t) 1₂) P (F 1₂) (F' 1₂))
      ( \ G →
        dependent-square B (f 0₂) (f 1₂) (f' 0₂) (f' 1₂)
        ( f) (\ t → first (m t) 0₂) f' (\ t → first (m t) 1₂)
        ( \ (t , s) → first (m s) t)
        ( P) e (F 1₂) e' (F' 1₂)
        ( \ t → F t) (\ t → second (m t)) (\ t → F' t) G)
      ( \ G →
        Σ ( D : dhom B (f 0₂) (f' 1₂) (\ t → first (m t) t) P e (F' 1₂))
        , product
          ( dhom2 B (f 0₂) (f 1₂) (f' 1₂)
            ( f) (\ t → first (m t) 1₂) (\ t → first (m t) t)
            ( \ (t , s) → first (m s) t)
            ( P) e (F 1₂) (F' 1₂)
            ( \ t → F t) G D)
          ( dhom2 B (f 0₂) (f' 0₂) (f' 1₂)
            ( \ t → first (m t) 0₂) (f') (\ t → first (m t) t)
            ( \ (t , s) → first (m t) s)
            ( P) e (F' 0₂) (F' 1₂)
            ( \ t → second (m t)) (\ t → F' t) D))
      ( equiv-dependent-square-glued-dhom2 B (f 0₂) (f 1₂) (f' 0₂) (f' 1₂)
        ( f) (\ t → first (m t) 0₂) f' (\ t → first (m t) 1₂)
        ( \ (t , s) → first (m s) t)
        ( P) e (F 1₂) e' (F' 1₂)
        ( \ t → F t) (\ t → second (m t)) (\ t → F' t)))
    ( equiv-has-inverse
      ( Σ ( G : dhom B (f 1₂) (f' 1₂) (\ t → first (m t) 1₂) P (F 1₂) (F' 1₂))
        , Σ ( D : dhom B (f 0₂) (f' 1₂) (\ t → first (m t) t) P e (F' 1₂))
          , product
            ( dhom2 B (f 0₂) (f 1₂) (f' 1₂)
              ( f) (\ t → first (m t) 1₂) (\ t → first (m t) t)
              ( \ (t , s) → first (m s) t)
              ( P) e (F 1₂) (F' 1₂)
              ( \ t → F t) G D)
            ( dhom2 B (f 0₂) (f' 0₂) (f' 1₂)
              ( \ t → first (m t) 0₂) (f') (\ t → first (m t) t)
              ( \ (t , s) → first (m t) s)
              ( P) e (F' 0₂) (F' 1₂)
              ( \ t → second (m t)) (\ t → F' t) D))
      ( Σ ( G : dhom B (f 1₂) (f' 1₂) (\ t → first (m t) 1₂) P (F 1₂) (F' 1₂))
        , Σ ( Dτ : Σ (D : dhom B (f 0₂) (f' 1₂) (\ t → first (m t) t) P e (F' 1₂))
                  , dhom2 B (f 0₂) (f' 0₂) (f' 1₂)
                    ( \ t → first (m t) 0₂) (f') (\ t → first (m t) t)
                    ( \ (t , s) → first (m t) s)
                    ( P) e (F' 0₂) (F' 1₂)
                    ( \ t → second (m t)) (\ t → F' t) D)
          , dhom2 B (f 0₂) (f 1₂) (f' 1₂)
            ( f) (\ t → first (m t) 1₂) (\ t → first (m t) t)
            ( \ (t , s) → first (m s) t)
            ( P) e (F 1₂) (F' 1₂)
            ( \ t → F t) G (first Dτ))
      ( \ (G , (D , (τ' , τ))) → (G , ((D , τ) , τ')))
      ( \ (G , ((D , τ) , τ')) → (G , (D , (τ' , τ))))
      ( \ _ → refl)
      ( \ _ → refl))
    ( total-equiv-family-of-equiv
      ( dhom B (f 1₂) (f' 1₂) (\ t → first (m t) 1₂) P (F 1₂) (F' 1₂))
      ( \ G →
        Σ ( Dτ : Σ (D : dhom B (f 0₂) (f' 1₂) (\ t → first (m t) t) P e (F' 1₂))
                , dhom2 B (f 0₂) (f' 0₂) (f' 1₂)
                  ( \ t → first (m t) 0₂) (f') (\ t → first (m t) t)
                  ( \ (t , s) → first (m t) s)
                  ( P) e (F' 0₂) (F' 1₂)
                  ( \ t → second (m t)) (\ t → F' t) D)
        , dhom2 B (f 0₂) (f 1₂) (f' 1₂)
          ( f) (\ t → first (m t) 1₂) (\ t → first (m t) t)
          ( \ (t , s) → first (m s) t)
          ( P) e (F 1₂) (F' 1₂)
          ( \ t → F t) G (first Dτ))
      ( \ G →
        dhom2 B (f 0₂) (f 1₂) (f' 1₂)
        ( f) (\ t → first (m t) 1₂) (\ t → first (m t) t)
        ( \ (t , s) → first (m s) t)
        ( P) e (F 1₂) (F' 1₂)
        ( \ t → F t) G (temp-96cf-A'-diag (f' , (e' , (m , F')))))
      ( \ G →
        transport-equiv-center-fiber-total-type-is-contr-base
        ( Σ ( D : dhom B (f 0₂) (f' 1₂) (\ t → first (m t) t) P e (F' 1₂))
          , dhom2 B (f 0₂) (f' 0₂) (f' 1₂)
            ( \ t → first (m t) 0₂) (f') (\ t → first (m t) t)
            ( \ (t , s) → first (m t) s)
            ( P) e (F' 0₂) (F' 1₂)
            ( \ t → second (m t)) (\ t → F' t) D)
        ( is-contr-equiv-is-contr'
          ( Σ ( D : dhom B (f 0₂) (f' 1₂) (\ t → first (m t) t) P e (F' 1₂))
            , dhom2 B (f 0₂) (f' 0₂) (f' 1₂)
              ( \ t → first (m t) 0₂) (f') (\ t → first (m t) t)
              ( \ (t , s) → first (m t) s)
              ( P) e (F' 0₂) (F' 1₂)
              ( \ t → second (m t)) (\ t → F' t) D)
          ( ( ( t , s) : Δ²) → P (first (m t) s) [s ≡ 0₂ ↦ second (m t) , t ≡ 1₂ ↦ F' s])
          ( equiv-has-inverse
            ( Σ ( D : dhom B (f 0₂) (f' 1₂) (\ t → first (m t) t) P e (F' 1₂))
              , dhom2 B (f 0₂) (f' 0₂) (f' 1₂)
                ( \ t → first (m t) 0₂) (f') (\ t → first (m t) t)
                ( \ (t , s) → first (m t) s)
                ( P) e (F' 0₂) (F' 1₂)
                ( \ t → second (m t)) (\ t → F' t) D)
            ( ( ( t , s) : Δ²) → P (first (m t) s) [s ≡ 0₂ ↦ second (m t) , t ≡ 1₂ ↦ F' s])
            ( \ (D , τ) (t , s) → τ (t , s))
            ( \ τ → (\ t → τ (t , t) , \ (t , s) → τ (t , s)))
            ( \ _ → refl)
            ( \ _ → refl))
          ( is-inner-family-P
            ( \ (t , s) → first (m t) s)
            ( \ (t , s) → recOR(s ≡ 0₂ ↦ second (m t) , t ≡ 1₂ ↦ F' s))))
        ( \ Dτ →
          dhom2 B (f 0₂) (f 1₂) (f' 1₂)
          ( f) (\ t → first (m t) 1₂) (\ t → first (m t) t)
          ( \ (t , s) → first (m s) t)
          ( P) e (F 1₂) (F' 1₂)
          ( \ t → F t) G (first Dτ))
        ( temp-96cf-A'-diag (f' , (e' , (m , F')))
        , \ (t , s) → temp-96cf-A'-inner-filler (f' , (e' , (m , F'))) (t , s)))))

#def is-cocartesian-arrow-equiv-is-dependent-initial uses (is-inner-family-P)
  : Equiv
    ( is-cocartesian-arrow B (f 0₂) (f 1₂) f P e (F 1₂) (\ t → F t))
    ( is-dependent-initial temp-96cf-G temp-96cf-Q (f , e) F)
  :=
  equiv-triple-comp
  ( is-cocartesian-arrow B (f 0₂) (f 1₂) f P e (F 1₂) (\ t → F t))
  ( ( a : temp-96cf-A) → is-contr (temp-96cf-R a))
  ( ( a' : temp-96cf-A') → is-contr (temp-96cf-R' a'))
  ( is-dependent-initial temp-96cf-G temp-96cf-Q (f , e) F)
  ( temp-96cf-equiv-cocartesian-arrow)
  ( equiv-family-of-props funext
    ( temp-96cf-A)
    ( temp-96cf-A')
    ( \ a → is-contr (temp-96cf-R a))
    ( \ a → is-prop-is-contr-itself (weakfunext-funext funext) (temp-96cf-R a))
    ( \ a' → is-contr (temp-96cf-R' a'))
    ( \ a' → is-prop-is-contr-itself (weakfunext-funext funext) (temp-96cf-R' a'))
    ( temp-96cf-alpha₁)
    ( temp-96cf-is-contr-R-a-is-contr-R'-alpha₁-a)
    ( temp-96cf-alpha₂)
    ( temp-96cf-is-contr-R'-a'-is-contr-R-alpha₂-a'))
  ( temp-96cf-equiv-dependent-initial)

#def is-cocartesian-arrow-is-dependent-initial uses (is-inner-family-P funext)
  : is-cocartesian-arrow B (f 0₂) (f 1₂) f P e (F 1₂) (\ t → F t)
    → is-dependent-initial temp-96cf-G temp-96cf-Q (f , e) F
  := first is-cocartesian-arrow-equiv-is-dependent-initial

#def is-dependent-initial-is-cocartesian-arrow uses (is-inner-family-P funext)
  : is-dependent-initial temp-96cf-G temp-96cf-Q (f , e) F
    → is-cocartesian-arrow B (f 0₂) (f 1₂) f P e (F 1₂) (\ t → F t)
  :=
  first
  ( inv-equiv
    ( is-cocartesian-arrow B (f 0₂) (f 1₂) f P e (F 1₂) (\ t → F t))
    ( is-dependent-initial temp-96cf-G temp-96cf-Q (f , e) F)
    ( is-cocartesian-arrow-equiv-is-dependent-initial))

#end is-cocartesian-arrow-equiv-is-dependent-initial
```

```rzk
#def is-cocartesian-family-equiv-has-cocartesian-lifts
  ( B : U)
  ( P : B → U)
  ( is-inner-family-P : is-inner-family B P)
  : Equiv (is-cocartesian-family B P) (has-cocartesian-lifts B P)
  :=
  equiv-triple-comp
  ( is-cocartesian-family B P)
  ( ( ( g , f₀) : temp-96cf-G B P)
    → Σ ( f : LARI-family-codomain 2 Δ¹ (\ t → t ≡ 0₂) B P (g , \ t → f₀))
      , is-dependent-initial
        ( LARI-family-domain 2 Δ¹ (\ t → t ≡ 0₂) B P)
        ( LARI-family-codomain 2 Δ¹ (\ t → t ≡ 0₂) B P)
        ( g , \ t → f₀)
        ( f))
  ( ( ( f , e) : temp-96cf-G B P)
    → Σ ( e' : P (f 1₂))
      , Σ ( F : dhom B (f 0₂) (f 1₂) f P e e')
        , is-cocartesian-arrow B (f 0₂) (f 1₂) (\ t → f t) P e e' F)
  ( has-cocartesian-lifts B P)
  ( equiv-has-inverse
    ( is-cocartesian-family B P)
    ( ( ( g , f₀) : temp-96cf-G B P)
      → Σ ( f : LARI-family-codomain 2 Δ¹ (\ t → t ≡ 0₂) B P (g , \ t → f₀))
        , is-dependent-initial
          ( LARI-family-domain 2 Δ¹ (\ t → t ≡ 0₂) B P)
          ( LARI-family-codomain 2 Δ¹ (\ t → t ≡ 0₂) B P)
          ( g , \ t → f₀)
          ( f))
    ( \ is-cocartesian-family-P (g , f₀) → is-cocartesian-family-P g (\ t → f₀))
    ( \ is-cocartesian-family-P' g f₀ → is-cocartesian-family-P' (g , f₀ 0₂))
    ( \ _ → refl)
    ( \ _ → refl))
  ( equiv-function-equiv-family funext
    ( temp-96cf-G B P)
    ( \ (g , f₀) →
      Σ ( f : LARI-family-codomain 2 Δ¹ (\ t → t ≡ 0₂) B P (g , \ t → f₀))
      , is-dependent-initial
        ( LARI-family-domain 2 Δ¹ (\ t → t ≡ 0₂) B P)
        ( LARI-family-codomain 2 Δ¹ (\ t → t ≡ 0₂) B P)
        ( g , \ t → f₀)
        ( f))
    ( \ (f , e) →
      Σ ( e' : P (f 1₂))
      , Σ ( F : dhom B (f 0₂) (f 1₂) f P e e')
        , is-cocartesian-arrow B (f 0₂) (f 1₂) (\ t → f t) P e e' F)
    ( \ (f , e) →
      equiv-comp
      ( Σ ( F : LARI-family-codomain 2 Δ¹ (\ t → t ≡ 0₂) B P (f , \ t → e))
        , is-dependent-initial
          ( LARI-family-domain 2 Δ¹ (\ t → t ≡ 0₂) B P)
          ( LARI-family-codomain 2 Δ¹ (\ t → t ≡ 0₂) B P)
          ( f , \ t → e)
          ( F))
      ( Σ ( F : LARI-family-codomain 2 Δ¹ (\ t → t ≡ 0₂) B P (f , \ t → e))
        , is-cocartesian-arrow B (f 0₂) (f 1₂) (\ t → f t) P e (F 1₂) (\ t → F t))
      ( Σ ( e' : P (f 1₂))
        , Σ ( F : dhom B (f 0₂) (f 1₂) f P e e')
          , is-cocartesian-arrow B (f 0₂) (f 1₂) (\ t → f t) P e e' F)
      ( total-equiv-family-of-equiv
        ( LARI-family-codomain 2 Δ¹ (\ t → t ≡ 0₂) B P (f , \ t → e))
        ( is-dependent-initial
          ( LARI-family-domain 2 Δ¹ (\ t → t ≡ 0₂) B P)
          ( LARI-family-codomain 2 Δ¹ (\ t → t ≡ 0₂) B P)
          ( f , \ t → e))
        ( \ F → is-cocartesian-arrow B (f 0₂) (f 1₂) (\ t → f t) P e (F 1₂) (\ t → F t))
        ( \ F →
          equiv-comp
          ( is-dependent-initial
            ( LARI-family-domain 2 Δ¹ (\ t → t ≡ 0₂) B P)
            ( LARI-family-codomain 2 Δ¹ (\ t → t ≡ 0₂) B P)
            ( f , \ t → e)
            ( F))
          ( is-dependent-initial (temp-96cf-G B P) (temp-96cf-Q B P) (f , e) F)
          ( is-cocartesian-arrow B (f 0₂) (f 1₂) (\ t → f t) P e (F 1₂) (\ t → F t))
          ( equiv-has-inverse
            ( is-dependent-initial
              ( LARI-family-domain 2 Δ¹ (\ t → t ≡ 0₂) B P)
              ( LARI-family-codomain 2 Δ¹ (\ t → t ≡ 0₂) B P)
              ( f , \ t → e)
              ( F))
            ( is-dependent-initial (temp-96cf-G B P) (temp-96cf-Q B P) (f , e) F)
            ( \ is-dependent-initial-F (f' , e') F' m →
              is-dependent-initial-F (f' , \ _ → e') F'
              ( \ t → (first (m t) , \ _ → second (m t))))
            ( \ is-dependent-initial-F (f' , e') F' m →
              is-dependent-initial-F (f' , e' 0₂) F'
              ( \ t → (first (m t) , second (m t) 0₂)))
            ( \ _ → refl)
            ( \ _ → refl))
          ( inv-equiv
            ( is-cocartesian-arrow B (f 0₂) (f 1₂) (\ t → f t) P e (F 1₂) (\ t → F t))
            ( is-dependent-initial (temp-96cf-G B P) (temp-96cf-Q B P) (f , e) F)
            ( is-cocartesian-arrow-equiv-is-dependent-initial B P is-inner-family-P f e F))))
      ( equiv-has-inverse
        ( Σ ( F : LARI-family-codomain 2 Δ¹ (\ t → t ≡ 0₂) B P (f , \ t → e))
          , is-cocartesian-arrow B (f 0₂) (f 1₂) (\ t → f t) P e (F 1₂) (\ t → F t))
        ( Σ ( e' : P (f 1₂))
          , Σ ( F : dhom B (f 0₂) (f 1₂) (\ t → f t) P e e')
            , is-cocartesian-arrow B (f 0₂) (f 1₂) (\ t → f t) P e e' F)
        ( \ (F , prf) → (F 1₂ , (\ t → F t , prf)))
        ( \ (e' , (f , prf)) → (\ t → f t , prf))
        ( \ _ → refl)
        ( \ _ → refl))))
  ( equiv-has-inverse
    ( ( ( f , e) : temp-96cf-G B P)
      → Σ ( e' : P (f 1₂))
        , Σ ( F : dhom B (f 0₂) (f 1₂) (\ t → f t) P e e')
          , is-cocartesian-arrow B (f 0₂) (f 1₂) (\ t → f t) P e e' F)
    ( has-cocartesian-lifts B P)
    ( \ has-cocartesian-lifts-P' b b' u e → has-cocartesian-lifts-P' (u , e))
    ( \ has-cocartesian-lifts-P (f , e) →
      has-cocartesian-lifts-P (f 0₂) (f 1₂) (\ t → f t) e)
    ( \ _ → refl)
    ( \ _ → refl))

{-
#def is-cocartesian-family-equiv-is-naive-cocartesian-family
  ( B : U)
  ( P : B → U)
  ( is-inner-family-P : is-inner-family B P)
  : Equiv (is-cocartesian-family B P) (is-naive-cocartesian-family B P)
  :=
  equiv-has-inverse
  ( is-cocartesian-family B P)
  ( is-naive-cocartesian-family B P)
  ( \ is-cocartesian-family-P → (is-inner-family-P, )
-}
```

## Closure Properties

```rzk
#def is-cocartesian-family-product-is-cocartesian-family
  ( I : U)
  ( B : I → U)
  ( P : (i : I) → (b : B i) → U)
  ( is-cocartesian-family-P : (i : I) → is-cocartesian-family (B i) (P i))
  : is-cocartesian-family ((i : I) → B i) (\ (b : (i : I) → B i) → ((i : I) → P i (b i)))
  :=
  is-LARI-family-product-is-LARI-family funext 2 Δ¹ (\ t → t ≡ 0₂) I B P
  ( is-cocartesian-family-P)

#def is-cocartesian-family-pullback-is-cocartesian-family
  ( A B : U)
  ( P : B → U)
  ( k : A → B)
  ( is-cocartesian-family-P : is-cocartesian-family B P)
  : is-cocartesian-family A (\ a → P (k a))
  :=
  is-LARI-family-pullback-is-LARI-family 2 Δ¹ (\ t → t ≡ 0₂) A B P k
  ( is-cocartesian-family-P)

#def is-cocartesian-family-comp-is-cocartesian-family
  ( B : U)
  ( P : B → U)
  ( is-cocartesian-family-P : is-cocartesian-family B P)
  ( R : (total-type B P) → U)
  ( is-cocartesian-family-R : is-cocartesian-family (total-type B P) R)
  : is-cocartesian-family B (\ b → Σ (p : P b) , R (b , p))
  :=
  is-LARI-family-comp-is-LARI-family extext 2 Δ¹ (\ t → t ≡ 0₂) B
  ( P) is-cocartesian-family-P
  ( R) is-cocartesian-family-R
```
