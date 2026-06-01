# 3. Directed univalence

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Prerequisites

- `hott/01-paths.rzk.md` — `ap`, `rev`, `concat`, `transport`.
- `hott/03-equivalences.rzk.md` — `Equiv`, `is-equiv`, `FunExt`, `eq-htpy`, `htpy-eq`, `equiv-comp`, `inv-ap-is-emb`.
- `hott/04-half-adjoint-equivalences.rzk.md` — `is-emb-is-equiv`.
- `hott/05-sigma.rzk.md` — `eq-pair`, `total-type`.
- `hott/06-contractible.rzk.md` — `is-contr`, `WeakFunExt`, `equiv-total-type-is-contr-fiber`.
- `hott/07-fibers.rzk.md` — `fib`.
- `hott/08-families-of-maps.rzk.md` — `total-equiv-family-of-equiv`.
- `hott/09-propositions.rzk.md` — `is-prop-Unit`, `is-prop-is-prop`.
- `hott/10-trivial-fibrations.rzk.md` — `is-equiv-domain-sum-of-fibers`.
- `simplicial-hott/03-extension-types.rzk.md` — `ExtExt`, `naiveextext-extext`.
- `01-modalities.rzk.md` — Modality operations and type aliases.
- `02-axioms.rzk.md` — Right adjoint and transpose adjunction.


## Covariant families

```rzk

#def dhom'
  ( A : 2 → U)
  ( x : A 0₂)
  ( y : A 1₂)
  : U
  :=
    ( t : 2)
  → ( A t) [ t ≡ 0₂ ↦ x
          , t ≡ 1₂ ↦ y]

#def is-cov-i (A : 2 → U)
  : U
  := (a_0 : A 0₂) → is-contr (Σ (a_1 : A (1₂)) , dhom' (\ i → A i) a_0 a_1)

#def coe-i (A : 2 → U) (phi : is-cov-i A)
  : A 0₂ → A 1₂
  :=
  \ a0 → first (first (phi a0))

#postulate is-prop-is-cov-i
  : ( A : 2 → U) → is-prop (is-cov-i A)

#def is-cov-i-Prop (A : 2 → U)
  : Prop
  := (is-cov-i A , is-prop-is-cov-i A)
```

## Amazing covariance

```rzk

#def is-a-cov (X : U)
  : U
  := amazing-predicate (mod _b is-cov-i-Prop) X

#def S
  : U
  := Σ (A : U) , is-a-cov A

#def S-b
  : <| ♭ | U |>
  := mod ♭ S

```

## S is covariant

```rzk
#def s-is-cov-i
  (f : 2 → S)
  : is-cov-i (\ b → first (f b))
  :=
    b-extract
      (mod _b (( f : 2 → S) → is-cov-i (\ b → first (f b))))
      (amazing-transpose
        (mod _b is-cov-i-Prop)
        (S-b)
        (mod _b (\s -> first s))
        (mod _b (\s -> second s)))
    f

#def is-a-cov-transpose
  ( A : _b U)
  ( h : _b A → U)
  ( f : _b (a : A) → is-a-cov (h a))
  : <| _b | (g : 2 → A) → is-cov-i (\ b → h (g b)) |>
  := amazing-transpose (mod _b is-cov-i-Prop) (mod _b A) (mod _b h) (mod _b f)

#def is-a-cov-untranspose
  ( A : _b U)
  ( h : _b A → U)
  ( f : _b (g : 2 → A) → is-cov-i (\ b → h (g b)))
  : <| _b | (a : A) → is-a-cov (h a) |>
  := amazing-untranspose (mod _b is-cov-i-Prop) (mod _b A) (mod _b h) (mod _b f)

#def is-a-cov-transposition-equiv
  ( A : _b U)
  ( h : _b A → U)
  : Equiv
    <| _b | (a : A) → is-a-cov (h a) |>
    <| _b | (g : 2 → A) → is-cov-i (\ b → h (g b)) |>
  := amazing-transpose-untranspose-equiv (mod _b is-cov-i-Prop) (mod _b A) (mod _b h)
```

## mor2fun

```rzk
#def mor2fun (f : 2 → S)
  : Σ ( A : S) , (Σ (B : S) , (first A) → (first B))
  :=
  ( f 0₂ , (f 1₂ , coe-i (\ x → first (f x)) (s-is-cov-i f)))
```

## dirglue

```rzk
#postulate is-a-cov-sigma-closed
    ( A : U) (B : A → U)
    ( is-a-cov-A : is-a-cov A)
    ( is-a-cov-B : (a : A) → is-a-cov (B a))
  : is-a-cov (Σ (a : A) , B a)

#postulate is-a-cov-id (A : U) (is-a-cov-A : is-a-cov A) (x y : A)
  : is-a-cov (x = y)

#def is-a-cov-fib (A B : U) (is-a-cov-A : is-a-cov A) (is-a-cov-B : is-a-cov B) (f : A → B) (b : B)
  : is-a-cov (fib A B f b)
  :=
    is-a-cov-sigma-closed
      A
      ( \ a → (f a) = b)
      is-a-cov-A
      ( \ a → is-a-cov-id B is-a-cov-B (f a) b)

#postulate is-monotone (I : CUBE) (phi : I → TOPE) : U

#postulate i===0-is-monotone-op-1 (i : 2)
  : is-monotone 1 (\ s → i ≡ 1₂)

#postulate is-a-cov-contr-ext
    ( phi : <| _op | TOPE |>)
    ( monotone : let mod _op phi_op := phi in <| _op | is-monotone 1 (\s -> phi_op) |>)
    ( A : U)
  : is-a-cov ((t : 1 | uninv_op phi) → A)

#def dirglue-is-acov (A B : S) (f : (first A) → (first B)) (i : 2)
  : is-a-cov (
    Σ ( b : (first B))
  , ( (t : 1 | i ≡ 0₂) → fib (first A) (first B) f b)
  )
  :=
    is-a-cov-sigma-closed
      ( first B)
      ( \ b → (t : 1 | i ≡ 0₂) → fib (first A) (first B) f b)
      ( second B)
      ( \ b →
        let mod _op flip_i := flip_op i in
        is-a-cov-contr-ext
          (inv_op (i ≡ 0₂))
          ((mod _op (i===0-is-monotone-op-1 flip_i)))
          (fib (first A) (first B) f b))

#def dirglue (A B : S) (f : (first A) → (first B))
  : 2 → S
  :=
    \ i →
      ( Σ ( b : (first B))
      , ( (t : 1 | i ≡ 0₂) → fib (first A) (first B) f b)
    , dirglue-is-acov A B f i)
```

First part of equivalence mor2fun (dirglue f) is f.

```rzk
#postulate is-prop-is-a-cov (A : U)
  : is-prop (is-a-cov A)

#def equiv-extent-0 (X : U)
  : Equiv ((t : 1 | 0₂ ≡ 0₂) → X) X
  :=
    ( ( \ h → h *_1)
    , ( ( ( \ x _ → x , \ _ → refl)
        , ( \ x _ → x , \ _ → refl))))

#def is-contr-extent-1 (X : U)
  : is-contr ((t : 1 | 1₂ ≡ 0₂) → X)
  :=
    ( ( \ t → recBOT)
    , \ f →
        naiveextext-extext extext
          1 (\ t → 1₂ ≡ 0₂) (\ _ → BOT) (\ _ → X) (\ _ → recBOT)
          ( \ t → recBOT) f
          ( \ t → recBOT))

#def dirglue_0=A (A B : S) (f : (first A) → (first B))
  : dirglue A B f 0₂ = A
  :=
    let equiv-0
      : Equiv (first (dirglue A B f 0₂)) (first A)
      := equiv-comp
           ( first (dirglue A B f 0₂))
           ( total-type (first B) (fib (first A) (first B) f))
           ( first A)
           ( total-equiv-family-of-equiv
               ( first B)
               ( \ b → (t : 1 | 0₂ ≡ 0₂) → fib (first A) (first B) f b)
               ( fib (first A) (first B) f)
               ( \ b → equiv-extent-0 (fib (first A) (first B) f b)))
           ( ( \ (_ , (a , _)) → a)
           , is-equiv-domain-sum-of-fibers (first A) (first B) f)
    in
    let path-types
      : first (dirglue A B f 0₂) = first A
      := first (ua (first (dirglue A B f 0₂)) (first A)) equiv-0
    in
    eq-pair U is-a-cov
      ( dirglue A B f 0₂) A
      ( path-types
      , first
          ( is-prop-is-a-cov (first A)
            ( transport U is-a-cov
                ( first (dirglue A B f 0₂)) (first A)
                path-types
                ( second (dirglue A B f 0₂)))
            ( second A)))

#def dirglue_1=B (A B : S) (f : (first A) → (first B))
  : dirglue A B f 1₂ = B
  :=
    let equiv-1
      : Equiv (first (dirglue A B f 1₂)) (first B)
      := equiv-total-type-is-contr-fiber
           ( first B)
           ( \ b → (t : 1 | 1₂ ≡ 0₂) → fib (first A) (first B) f b)
           ( \ b → is-contr-extent-1 (fib (first A) (first B) f b))
    in
    let path-types
      : first (dirglue A B f 1₂) = first B
      := first (ua (first (dirglue A B f 1₂)) (first B)) equiv-1
    in
    eq-pair U is-a-cov
      ( dirglue A B f 1₂) B
      ( path-types
      , first
          ( is-prop-is-a-cov (first B)
            ( transport U is-a-cov
                ( first (dirglue A B f 1₂)) (first B)
                path-types
                ( second (dirglue A B f 1₂)))
            ( second B)))

#postulate mor2fun-dirglue=f (A B : S) (f : (first A) → (first B))
  : mor2fun (dirglue A B f) = (A , (B , f))

#postulate nat-transform-is-eq (f g : 2 → S) (a : (i : 2) → first (f i) → first (g i))
  : iff
    ( ( i : 2) → (is-equiv (first (f i)) (first (g i)) (a i)))
    ( product (is-equiv (first (f 0₂)) (first (g 0₂)) (a 0₂)) (is-equiv (first (f 1₂)) (first (g 1₂)) (a 1₂)))
```
