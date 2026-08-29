# 5. Directed univalence

This is a literate `rzk` file:

```rzk
#lang rzk-1

#assume funext : FunExt
#assume weakfunext : WeakFunExt
#assume extext : ExtExt
```

## Prerequisites

- `hott/**` — `ap`, `rev`, `concat`, `transport`, `Equiv`, `is-equiv`, `eq-pair`, `total-map`, etc.
- `simplicial-hott/**` — extension types, right-orthogonality, discreteness.
- `hott/04-modalities.rzk.md` — modalities, `Prop-b`, `univ-family-Prop-b`.
- `triangulated/01`–`02` — tiny interval, internal universe.
- `triangulated/04-amazing-covariant.rzk.md` — `is-covariant-arrow-II`, `is-covariant-arrow-II-Prop`, `amazing-covariant-uniqueness-line-II`, `is-a-cov`, `is-a-cov-sigma-closed`, `is-a-cov-fib`, `is-a-cov-ext`, `is-a-cov-i===0`, `is-prop-is-a-cov`.

## Cubes separate

```rzk
#postulate cubes-separate (A B :♭ U) (f :♭ A → B)
  : iff (is-equiv A B f) ((n :_b nat) → is-equiv (♭ (I^n n → A)) (♭ (I^n n → B)) (b-map (I^n n → A) (I^n n → B) (\ p t → f (p t))))
```

## S and its morphisms

`S` is the type of amazingly-covariant types; a map `𝕀 → S` is a morphism.

```rzk

#def S uses (funext weakfunext)
  : U
  := Σ (A : U) , (is-a-cov funext weakfunext) A

#def S-b uses (funext weakfunext)
  : ( ♭ U)
  := mod ♭ S

#def s-is-covariant-arrow-II uses (funext weakfunext)
  ( f : 𝕀 → S)
  : is-covariant-arrow-II (\ (t : 𝕀 | TOP) → first (f t))
  :=
    b-extract
      ( ( f : 𝕀 → S) → is-covariant-arrow-II (\ (t : 𝕀 | TOP) → first (f t)))
      ( amazing-transpose funext weakfunext
        ( is-covariant-arrow-II-Prop funext weakfunext)
        ( S)
        ( ( \ s → first s))
        ( ( \ s → second s)))
    f

#def mor2fun uses (funext weakfunext) (f : 𝕀 → S)
  : Σ ( A : S) , (Σ (B : S) , (first A) → (first B))
  :=
  ( f 0₂ , (f 1₂ , covariant-transport-line-II
      ( \ (t : 𝕀 | TOP) → first (f t))
      ( s-is-covariant-arrow-II f)
      (\ k → form k)))
```

## dirglue

```rzk

#def dirglue-is-acov uses (funext weakfunext extext) (A B : S) (f : (first A) → (first B)) (i : 𝕀)
  : (is-a-cov funext weakfunext) (
    Σ ( b : (first B))
  , ( ( t : 1 | i ≡ 0₂) → fib (first A) (first B) f b)
  )
  :=
    is-a-cov-sigma-closed funext weakfunext
      ( first B)
      ( \ b → (t : 1 | i ≡ 0₂) → fib (first A) (first B) f b)
      ( second B)
      ( \ b →
          let mod ᵒᵖ flip_i := flipᵒᵖ i in
            is-a-cov-ext funext weakfunext extext
              ( mod ᵒᵖ (flip_i ≡ 1₂))
              ( mod ᵒᵖ (is-a-cov-i===0 funext weakfunext extext flip_i))
              ( fib (first A) (first B) f b)
              ( is-a-cov-fib funext weakfunext
                  ( first A) ( first B)
                  ( second A) ( second B)
                  ( f) ( b)))

#def dirglue uses (funext weakfunext extext) (A B : S) (f : (first A) → (first B))
  : 𝕀 → S
  :=
    \ i →
      ( Σ ( b : (first B))
      , ( ( t : 1 | i ≡ 0₂) → fib (first A) (first B) f b)
    , dirglue-is-acov A B f i)
```

First part of equivalence mor2fun (dirglue f) is f.

```rzk
#def equiv-extent-0 (X : U)
  : Equiv ((t : 1 | 0₂ ≡ 0₂) → X) X
  :=
    ( ( \ h → h *₁)
    , ( ( ( \ x _ → x , \ _ → refl)
        , ( \ x _ → x , \ _ → refl))))

#def is-contr-extent-1 uses (extext) (X : U)
  : is-contr ((t : 1 | 1₂ ≡ 0₂) → X)
  :=
    ( ( \ t → recBOT)
    , \ f →
        naiveextext-extext extext
          1 (\ t → 1₂ ≡ 0₂) (\ _ → BOT) (\ _ → X) (\ _ → recBOT)
          ( \ t → recBOT) f
          ( \ t → recBOT))

#def dirglue-equiv-0 uses (funext weakfunext extext) (A B : S) (f : (first A) → (first B))
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

#def dirglue-0=A-EqΣ uses (funext weakfunext extext) (A B : S) (f : (first A) → (first B))
  : Eq-Σ U (is-a-cov funext weakfunext) (dirglue A B f 0₂) A
  := (first (ua (first (dirglue A B f 0₂)) (first A)) (dirglue-equiv-0 A B f)
     , first
         ( is-prop-is-a-cov funext weakfunext (first A)
           ( transport U (is-a-cov funext weakfunext)
               ( first (dirglue A B f 0₂)) (first A)
               ( first (ua (first (dirglue A B f 0₂)) (first A)) (dirglue-equiv-0 A B f))
               ( second (dirglue A B f 0₂)))
           ( second A)))

#def dirglue_0=A uses (funext weakfunext extext) (A B : S) (f : (first A) → (first B))
  : dirglue A B f 0₂ = A
  := eq-pair U (is-a-cov funext weakfunext) (dirglue A B f 0₂) A (dirglue-0=A-EqΣ A B f)

#def dirglue-equiv-1 uses (funext weakfunext extext) (A B : S) (f : (first A) → (first B))
  : Equiv (first (dirglue A B f 1₂)) (first B)
  := equiv-total-type-is-contr-fiber
       ( first B)
       ( \ b → (t : 1 | 1₂ ≡ 0₂) → fib (first A) (first B) f b)
       ( \ b → is-contr-extent-1 (fib (first A) (first B) f b))

#def dirglue-1=B-EqΣ uses (funext weakfunext extext) (A B : S) (f : (first A) → (first B))
  : Eq-Σ U (is-a-cov funext weakfunext) (dirglue A B f 1₂) B
  := (first (ua (first (dirglue A B f 1₂)) (first B)) (dirglue-equiv-1 A B f)
     , first
         ( is-prop-is-a-cov funext weakfunext (first B)
           ( transport U (is-a-cov funext weakfunext)
               ( first (dirglue A B f 1₂)) (first B)
               ( first (ua (first (dirglue A B f 1₂)) (first B)) (dirglue-equiv-1 A B f))
               ( second (dirglue A B f 1₂)))
           ( second B)))

#def dirglue_1=B uses (funext weakfunext extext) (A B : S) (f : (first A) → (first B))
  : dirglue A B f 1₂ = B
  := eq-pair U (is-a-cov funext weakfunext) (dirglue A B f 1₂) B (dirglue-1=B-EqΣ A B f)

#def coe-dirglue-is-f-pointwise uses (funext weakfunext extext)
  ( A B : S) (f : (first A) → (first B))
  ( a : first A)
  : transport S (\ s → first s) (dirglue A B f 1₂) B (dirglue_1=B A B f)
      ( covariant-transport-line-II (\ (t : 𝕀 | TOP) → first (dirglue A B f t)) (s-is-covariant-arrow-II (dirglue A B f)) (\ k → form k)
          ( transport-rev S (\ s → first s) (dirglue A B f 0₂) A (dirglue_0=A A B f) a))
    = f a
  :=
    let coe-dirglue : first (dirglue A B f 0₂) → first (dirglue A B f 1₂)
      := covariant-transport-line-II (\ (t : 𝕀 | TOP) → first (dirglue A B f t)) (s-is-covariant-arrow-II (dirglue A B f)) (\ k → form k) in
    let a-in-dirglue-0 : first (dirglue A B f 0₂)
      := transport-rev S (\ s → first s) (dirglue A B f 0₂) A (dirglue_0=A A B f) a in
    let base-is-f-a : first a-in-dirglue-0 = f a
      := concat (first B)
           ( first a-in-dirglue-0)
           ( f (first (dirglue-equiv-0 A B f) a-in-dirglue-0))
           ( f a)
           -- first a-in-dirglue-0 = f (dirglue-equiv-0 a-in-dirglue-0)
           ( rev (first B) (f (first (dirglue-equiv-0 A B f) a-in-dirglue-0)) (first a-in-dirglue-0)
               ( second ((second a-in-dirglue-0) *₁)))
           -- f (dirglue-equiv-0 a-in-dirglue-0) = f a
           ( ap (first A) (first B) (first (dirglue-equiv-0 A B f) a-in-dirglue-0) a f
               ( concat (first A)
                   ( first (dirglue-equiv-0 A B f) a-in-dirglue-0)
                   ( transport S (\ s → first s) (dirglue A B f 0₂) A (dirglue_0=A A B f) a-in-dirglue-0)
                   ( a)
                   -- dirglue-equiv-0 a-in-dirglue-0 = transport (dirglue_0=A) a-in-dirglue-0
                   ( rev (first A)
                       ( transport S (\ s → first s) (dirglue A B f 0₂) A (dirglue_0=A A B f) a-in-dirglue-0)
                       ( first (dirglue-equiv-0 A B f) a-in-dirglue-0)
                       ( concat (first A)
                           ( transport S (\ s → first s) (dirglue A B f 0₂) A (dirglue_0=A A B f) a-in-dirglue-0)
                           ( transport U (\ Z → Z) (first (dirglue A B f 0₂)) (first A)
                               ( first (dirglue-0=A-EqΣ A B f)) a-in-dirglue-0)
                           ( first (dirglue-equiv-0 A B f) a-in-dirglue-0)
                           ( transport-first-eq-pair (is-a-cov funext weakfunext) (dirglue A B f 0₂) A (dirglue-0=A-EqΣ A B f) a-in-dirglue-0)
                           ( transport-ua (first (dirglue A B f 0₂)) (first A) (dirglue-equiv-0 A B f) a-in-dirglue-0)))
                   -- transport (dirglue_0=A) a-in-dirglue-0 = a
                   ( transport-transport-rev S (\ s → first s)
                       ( dirglue A B f 0₂) A (dirglue_0=A A B f) a))) in
    concat (first B)
      ( transport S (\ s → first s) (dirglue A B f 1₂) B (dirglue_1=B A B f) (coe-dirglue a-in-dirglue-0))
      ( first a-in-dirglue-0)
      ( f a)
      -- transport (dirglue_1=B) (coe-dirglue a-in-dirglue-0) = first a-in-dirglue-0
      ( concat (first B)
          ( transport S (\ s → first s) (dirglue A B f 1₂) B (dirglue_1=B A B f) (coe-dirglue a-in-dirglue-0))
          ( first (coe-dirglue a-in-dirglue-0))
          ( first a-in-dirglue-0)
          -- transport (dirglue_1=B) (coe-dirglue a-in-dirglue-0) = first (coe-dirglue a-in-dirglue-0)
          ( concat (first B)
              ( transport S (\ s → first s) (dirglue A B f 1₂) B (dirglue_1=B A B f) (coe-dirglue a-in-dirglue-0))
              ( transport U (\ Z → Z) (first (dirglue A B f 1₂)) (first B)
                  ( first (dirglue-1=B-EqΣ A B f)) (coe-dirglue a-in-dirglue-0))
              ( first (coe-dirglue a-in-dirglue-0))
              ( transport-first-eq-pair (is-a-cov funext weakfunext) (dirglue A B f 1₂) B (dirglue-1=B-EqΣ A B f) (coe-dirglue a-in-dirglue-0))
              ( transport-ua (first (dirglue A B f 1₂)) (first B) (dirglue-equiv-1 A B f) (coe-dirglue a-in-dirglue-0)))
          -- first (coe-dirglue a-in-dirglue-0) = first a-in-dirglue-0
          ( ap (first (dirglue A B f 1₂)) (first B) (coe-dirglue a-in-dirglue-0) (first a-in-dirglue-0 , second a-in-dirglue-0)
              ( \ z → first z)
              ( amazing-covariant-uniqueness-line-II (\ (t : 𝕀 | TOP) → first (dirglue A B f t)) (s-is-covariant-arrow-II (dirglue A B f))
                  ( a-in-dirglue-0) (first a-in-dirglue-0 , second a-in-dirglue-0) (\ (t : 𝕀) → (first a-in-dirglue-0 , second a-in-dirglue-0)))))
      ( base-is-f-a)

#def coe-dirglue-is-f uses (funext weakfunext extext)
  ( A B : S) (f : (first A) → (first B))
  : product-transport S S (\ X Y → (first X) → (first Y))
      ( dirglue A B f 0₂) A
      ( dirglue A B f 1₂) B
      ( dirglue_0=A A B f) (dirglue_1=B A B f)
      ( covariant-transport-line-II (\ (t : 𝕀 | TOP) → first (dirglue A B f t)) (s-is-covariant-arrow-II (dirglue A B f)) (\ k → form k))
    = f
  :=
    let coe-dirglue : first (dirglue A B f 0₂) → first (dirglue A B f 1₂)
      := covariant-transport-line-II (\ (t : 𝕀 | TOP) → first (dirglue A B f t)) (s-is-covariant-arrow-II (dirglue A B f)) (\ k → form k) in
    let coe-dirglue-transported : (first A) → (first B)
      := \ (a : first A) →
         transport S (\ s → first s) (dirglue A B f 1₂) B (dirglue_1=B A B f)
           ( coe-dirglue (transport-rev S (\ s → first s) (dirglue A B f 0₂) A (dirglue_0=A A B f) a)) in
    concat ((first A) → (first B))
      ( product-transport S S (\ X Y → (first X) → (first Y))
          ( dirglue A B f 0₂) A (dirglue A B f 1₂) B
          ( dirglue_0=A A B f) (dirglue_1=B A B f) coe-dirglue)
      ( coe-dirglue-transported)
      ( f)
      -- product-transport (dirglue_0=A) (dirglue_1=B) coe-dirglue = coe-dirglue-transported
      ( product-transport-fun S (\ s → first s)
          ( dirglue A B f 0₂) A (dirglue A B f 1₂) B
          ( dirglue_0=A A B f) (dirglue_1=B A B f) coe-dirglue)
      -- coe-dirglue-transported = f
      ( eq-htpy funext (first A) (\ _ → first B)
          coe-dirglue-transported f (coe-dirglue-is-f-pointwise A B f))


#def mor2fun-dirglue=f uses (funext weakfunext extext) (A B : S) (f : (first A) → (first B))
  : mor2fun (dirglue A B f) = (A , (B , f))
  :=
    eq-triple S S (\ X Y → (first X) → (first Y))
      ( mor2fun (dirglue A B f))
      ( A , (B , f))
      ( dirglue_0=A A B f , (dirglue_1=B A B f , (coe-dirglue-is-f A B f)))

#def orthogonality-pullback-fiber uses (funext weakfunext)
  ( n m : nat)
  ( F0 : product (I^n n) (shape (_ : 𝕀 | TOP)) → S)
  : U
  :=
    Σ ( c : I^n m → product (I^n n) (shape (_ : 𝕀 | TOP)))
    , first (F0 (c (zero-vec-I^n m)))

#def orthogonality-pullback-fwd uses (funext weakfunext)
  ( n m : nat)
  ( F0 : product (I^n n) (shape (_ : 𝕀 | TOP)) → S)
  : ( I^n m
      → Σ ( t : product (I^n n) (shape (_ : 𝕀 | TOP)))
        , first (F0 t))
    → orthogonality-pullback-fiber n m F0
  :=
    \ f →
      ( \ t → first (f t)
      , second (f (zero-vec-I^n m)))

#def orthogonality-pullback uses (funext weakfunext)
  ( n m : nat)
  ( F0 : product (I^n n) (shape (_ : 𝕀 | TOP)) → S)
  : Equiv
      ( I^n m
        → Σ ( t : product (I^n n) (shape (_ : 𝕀 | TOP)))
          , first (F0 t))
      ( orthogonality-pullback-fiber n m F0)
  :=
    ( orthogonality-pullback-fwd n m F0
    , ?orthogonality-pullback)

#def orthogonality-pullback-split uses (funext weakfunext)
  ( n m : nat)
  ( F0 : product (I^n n) (shape (_ : 𝕀 | TOP)) → S)
  : U
  :=
    Σ ( v : I^n m → I^n n)
    , Σ ( theta : I^n m → shape (_ : 𝕀 | TOP))
    , first
        ( F0
            ( v (zero-vec-I^n m)
            , theta (zero-vec-I^n m)))

#def equiv-orthogonality-pullback-split uses (funext weakfunext)
  ( n m : nat)
  ( F0 : product (I^n n) (shape (_ : 𝕀 | TOP)) → S)
  : Equiv (orthogonality-pullback-fiber n m F0) (orthogonality-pullback-split n m F0)
  :=
    -- Both sides are Σ over `I^n m → product (I^n n) 𝕀-shape`; splitting the
    -- pair pointwise is a definitional isomorphism (Σ-η).
    equiv-has-inverse
      ( orthogonality-pullback-fiber n m F0)
      ( orthogonality-pullback-split n m F0)
      ( \ (c , p) →
          ( \ t → first (c t)
          , ( \ t → second (c t)
            , p)))
      ( \ (v , (theta , p)) →
          ( \ t → (v t , theta t)
          , p))
      ( \ _ → refl)
      ( \ _ → refl)

#def orthogonality-pullback-flat-commute uses (funext weakfunext)
  ( n m :♭ nat)
  ( F0 :♭ product (I^n n) (shape (_ : 𝕀 | TOP)) → S)
  : Equiv
      ( ♭ ( orthogonality-pullback-split n m F0))
      ( Σ ( v : ♭ (I^n m → I^n n))
      , ( let mod ♭ v' := v in
          Σ ( theta : ♭ (I^n m → shape (_ : 𝕀 | TOP)))
          , ( let mod ♭ theta' := theta in
              ♭
                ( first
                    ( F0
                        ( v' (zero-vec-I^n m)
                        , theta' (zero-vec-I^n m)))))))
  :=
    b-sigma2-commute-equiv
      ( I^n m → I^n n)
      ( I^n m → shape (_ : 𝕀 | TOP))
      ( \ v theta →
          first
            ( F0
                ( v (zero-vec-I^n m)
                , theta (zero-vec-I^n m))))

#def equiv-orthogonality-to-flat uses (funext weakfunext)
  ( n m :♭ nat)
  ( F0 :♭ product (I^n n) (shape (_ : 𝕀 | TOP)) → S)
  : Equiv
      ( ♭
          ( I^n m
            → Σ ( t : product (I^n n) (shape (_ : 𝕀 | TOP)))
              , first (F0 t)))
      ( ♭ ( orthogonality-pullback-split n m F0))
  :=
    let mod ♭ F-uncurried :=
      mod ♭ (orthogonality-pullback-fiber n m F0) in
    let mod ♭ curry-F :=
      mod ♭ (equiv-orthogonality-pullback-split n m F0) in
    b-equiv
      ( I^n m
        → Σ ( t : product (I^n n) (shape (_ : 𝕀 | TOP)))
          , first (F0 t))
      ( orthogonality-pullback-split n m F0)
      ( equiv-comp
          ( I^n m
            → Σ ( t : product (I^n n) (shape (_ : 𝕀 | TOP)))
              , first (F0 t))
          ( F-uncurried)
          ( orthogonality-pullback-split n m F0)
          ( orthogonality-pullback n m F0)
          ( curry-F))

#def split-lemma uses (funext weakfunext extext) (f g : 𝕀 → S) (a : (i : 𝕀) → first (f i) → first (g i))
  : ( is-equiv (first (f 0₂)) (first (g 0₂)) (a 0₂)) → (is-equiv (first (f 1₂)) (first (g 1₂)) (a 1₂))
    → ( ( i : 𝕀) → (is-equiv (first (f i)) (first (g i)) (a i)))
  :=
    let mod ♭ X := mod ♭ (Σ (F : 𝕀 → S) , Σ (G : 𝕀 → S) , Σ (alpha : (theta : 𝕀) → first (F theta) → first (G theta)) , Σ (equiv-0 : is-equiv (first (F 0₂)) (first (G 0₂)) (alpha 0₂)) , (is-equiv (first (F 1₂)) (first (G 1₂)) (alpha 1₂))) in
    let mod ♭ Y := mod ♭ (Σ (F : 𝕀 → S) , Σ (G : 𝕀 → S) , Σ (alpha : (theta : 𝕀) → first (F theta) → first (G theta)) , (theta : 𝕀) → is-equiv (first (F theta)) (first (G theta)) (alpha theta)) in
    let mod ♭ Y-to-X : Y → X := mod ♭ (\ (F , (G , (alpha , pequiv))) → (F , (G , (alpha , (pequiv 0₂ , pequiv 1₂))))) in
    let Y-to-X-is-equiv : is-equiv Y X Y-to-X :=
      second (cubes-separate Y X Y-to-X) (\ n →
        let mod ♭ Gamma := mod ♭ ((I^n n)) in
        let mod ♭ Gamma' := mod ♭ (product (I^n n) (shape (_ : 𝕀 | TOP))) in
        let mod ♭ Hom-in-S := mod ♭ (\ (F : Gamma' → S) → \ (G : Gamma' → S) → (((v , i) : Gamma') → first (F (v , i)) → first (G (v , i)))) in
        let mod ♭ E-X := mod ♭ (\ (F : Gamma' → S) → \ (G : Gamma' → S) → \ (alpha : Hom-in-S F G) →
          ( ( v : I^n n) → product
              ( is-equiv (first (F (v , form 0₂))) (first (G (v , form 0₂))) (alpha (v , form 0₂)))
              ( is-equiv (first (F (v , form 1₂))) (first (G (v , form 1₂))) (alpha (v , form 1₂))))) in
        let mod ♭ E-Y := mod ♭ (\ (F : Gamma' → S) → \ (G : Gamma' → S) → \ (alpha : Hom-in-S F G) →
          ( ( ( v , i) : product (I^n n) (shape (_ : 𝕀 | TOP))) → is-equiv (first (F (v , i))) (first (G (v , i))) (alpha (v , i)))) in
        let mod ♭ X-cube :=
          mod ♭ (Σ (F : Gamma' → S) , Σ (G : Gamma' → S) , Σ (alpha : Hom-in-S F G) , E-X F G alpha) in
        let mod ♭ Y-cube :=
          mod ♭ (Σ (F : Gamma' → S) , Σ (G : Gamma' → S) , Σ (alpha : Hom-in-S F G) , E-Y F G alpha) in
        let mod ♭ X-split :=
          mod ♭ (Σ (F : ♭ (Gamma' → S))
          , ( let mod ♭ F0 := F in
              Σ ( G : ♭ (Gamma' → S))
              , ( let mod ♭ G0 := G in
                  Σ ( alpha : ♭ (Hom-in-S F0 G0))
                  , ( let mod ♭ a0 := alpha in ♭ (E-X F0 G0 a0))))) in
        let mod ♭ Y-split :=
          mod ♭ (Σ (F : ♭ (Gamma' → S))
          , ( let mod ♭ F0 := F in
              Σ ( G : ♭ (Gamma' → S))
              , ( let mod ♭ G0 := G in
                  Σ ( alpha : ♭ (Hom-in-S F0 G0))
                  , ( let mod ♭ a0 := alpha in ♭ (E-Y F0 G0 a0))))) in
        let mod ♭ E-Y-is-prop
 : ( F : Gamma' → S) → (G : Gamma' → S) → (alpha : Hom-in-S F G) → is-prop (E-Y F G alpha)
          :=
            mod ♭ (\ F G alpha →
              is-prop-fiberwise-prop funext Gamma'
                ( \ (v , i) → is-equiv (first (F (v , i))) (first (G (v , i))) (alpha (v , i)))
                ( \ (v , i) → is-prop-is-equiv funext (first (F (v , i))) (first (G (v , i))) (alpha (v , i)))) in
        let mod ♭ E-X-is-prop
 : ( F : Gamma' → S) → (G : Gamma' → S) → (alpha : Hom-in-S F G) → is-prop (E-X F G alpha)
          :=
            mod ♭ (\ F G alpha →
              is-prop-fiberwise-prop funext (I^n n)
                ( \ v → product
                    ( is-equiv (first (F (v , form 0₂))) (first (G (v , form 0₂))) (alpha (v , form 0₂)))
                    ( is-equiv (first (F (v , form 1₂))) (first (G (v , form 1₂))) (alpha (v , form 1₂))))
                ( \ v → is-prop-total-type-is-fiberwise-prop-is-prop-base
                    ( is-equiv (first (F (v , form 0₂))) (first (G (v , form 0₂))) (alpha (v , form 0₂)))
                    ( is-prop-is-equiv funext (first (F (v , form 0₂))) (first (G (v , form 0₂))) (alpha (v , form 0₂)))
                    ( \ _ → is-equiv (first (F (v , form 1₂))) (first (G (v , form 1₂))) (alpha (v , form 1₂)))
                    ( \ _ → is-prop-is-equiv funext (first (F (v , form 1₂))) (first (G (v , form 1₂))) (alpha (v , form 1₂))))) in
        let to-X-split : Equiv (♭ (I^n n → X)) X-split :=
          let mod ♭ X-uncurried :=
            mod ♭ (Σ (fa : (v : I^n n) → 𝕀 → S)
            , Σ ( fb : (v : I^n n) → 𝕀 → S)
            , Σ ( fc : (v : I^n n) → ((i : 𝕀) → first (fa v i) → first (fb v i)))
            , ( ( v : I^n n) → product
                  ( is-equiv (first (fa v 0₂)) (first (fb v 0₂)) (fc v 0₂))
                  ( is-equiv (first (fa v 1₂)) (first (fb v 1₂)) (fc v 1₂)))) in
          let mod ♭ curry-X :=
            mod ♭ (equiv-has-inverse
              ( X-uncurried) (X-cube)
              ( \ (fa , (fb , (fc , last))) →
                ( \ (v , t) → fa v (unform t)
                , ( \ (v , t) → fb v (unform t)
                  , ( \ (v , t) → fc v (unform t)
                    , last))))
              ( \ (F , (G , (alpha , e))) →
                ( \ v j → F (v , form j)
                , ( \ v j → G (v , form j)
                  , ( \ v j → alpha (v , form j)
                    , e))))
              ( \ _ → refl) (\ _ → refl)) in
          equiv-comp (♭ (I^n n → X)) (♭ X-cube) X-split
            ( b-equiv (I^n n → X) X-cube
                ( equiv-comp (I^n n → X) X-uncurried X-cube
                    ( equiv-choice3 (I^n n) (\ _ → 𝕀 → S) (\ _ _ → 𝕀 → S)
                        ( \ _ F G → (i : 𝕀) → first (F i) → first (G i))
                        ( \ _ F G alpha → product
                            ( is-equiv (first (F 0₂)) (first (G 0₂)) (alpha 0₂))
                            ( is-equiv (first (F 1₂)) (first (G 1₂)) (alpha 1₂))))
                    ( curry-X)))
            ( b-sigma3-commute-equiv (Gamma' → S) (\ _ → Gamma' → S) Hom-in-S E-X) in
        let to-Y-split : Equiv (♭ (I^n n → Y)) Y-split :=
          let mod ♭ Y-uncurried :=
            mod ♭ (Σ (fa : (v : I^n n) → 𝕀 → S)
            , Σ ( fb : (v : I^n n) → 𝕀 → S)
            , Σ ( fc : (v : I^n n) → ((i : 𝕀) → first (fa v i) → first (fb v i)))
            , ( ( v : I^n n) → (i : 𝕀) → is-equiv (first (fa v i)) (first (fb v i)) (fc v i))) in
          let mod ♭ curry-Y :=
            mod ♭ (equiv-has-inverse
              ( Y-uncurried) (Y-cube)
              ( \ (fa , (fb , (fc , nlast))) →
                ( \ (v , t) → fa v (unform t)
                , ( \ (v , t) → fb v (unform t)
                  , ( \ (v , t) → fc v (unform t)
                    , \ (v , i) → nlast v (unform i)))))
              ( \ (F , (G , (alpha , e))) →
                ( \ v j → F (v , form j)
                , ( \ v j → G (v , form j)
                  , ( \ v j → alpha (v , form j)
                    , \ v j → e (v , form j)))))
              ( \ _ → refl) (\ _ → refl)) in
          equiv-comp (♭ (I^n n → Y)) (♭ Y-cube) Y-split
            ( b-equiv (I^n n → Y) Y-cube
                ( equiv-comp (I^n n → Y) Y-uncurried Y-cube
                    ( equiv-choice3 (I^n n) (\ _ → 𝕀 → S) (\ _ _ → 𝕀 → S)
                        ( \ _ F G → (i : 𝕀) → first (F i) → first (G i))
                        ( \ _ F G alpha → (theta : 𝕀) → is-equiv (first (F theta)) (first (G theta)) (alpha theta)))
                    ( curry-Y)))
            ( b-sigma3-commute-equiv (Gamma' → S) (\ _ → Gamma' → S) Hom-in-S E-Y) in
        let Y-to-X-split : Equiv Y-split X-split :=
          total-b-equiv-family3
            ( Gamma' → S)
            ( \ _ → Gamma' → S)
            ( Hom-in-S)
            ( \ (F0 :♭ Gamma' → S) → \ (G0 :♭ Gamma' → S) → \ (a0 :♭ Hom-in-S F0 G0) → ♭ (E-Y F0 G0 a0))
            ( \ (F0 :♭ Gamma' → S) → \ (G0 :♭ Gamma' → S) → \ (a0 :♭ Hom-in-S F0 G0) → ♭ (E-X F0 G0 a0))
            ( \ (F0 :♭ Gamma' → S) → \ (G0 :♭ Gamma' → S) → \ (a0 :♭ Hom-in-S F0 G0) →
                equiv-iff-is-prop-is-prop
                  ( ♭ ( E-Y F0 G0 a0))
                  ( ♭ ( E-X F0 G0 a0))
                  ( is-prop-flat (E-Y F0 G0 a0) (mod ♭ (E-Y-is-prop F0 G0 a0)))
                  ( is-prop-flat (E-X F0 G0 a0) (mod ♭ (E-X-is-prop F0 G0 a0)))
                  ( ( b-map (E-Y F0 G0 a0) (E-X F0 G0 a0)
                        ( \ e v → (e (v , form 0₂) , e (v , form 1₂))))
                  , ( \ e →
                        let mod ♭ e0 := e in
                        let mod ♭ F̃ :=
                          mod ♭ (Σ (t : Gamma') , first (F0 t)) in
                        let mod ♭ G̃ :=
                          mod ♭ (Σ (t : Gamma') , first (G0 t)) in
                        let mod ♭ ã : F̃ → G̃ :=
                          mod ♭ (total-map
                            ( Gamma')
                            ( \ t → first (F0 t))
                            ( \ t → first (G0 t))
                            ( \ t → a0 t)) in
                        let mod ♭ fiberwise-is-equiv :=
                          mod ♭ ((t : Gamma')
                          → is-equiv (first (F0 t)) (first (G0 t)) (a0 t)) in
                        let mod ♭ fiberwise-is-equiv-is-prop
 : is-prop fiberwise-is-equiv
                          :=
                            mod ♭ (is-prop-fiberwise-prop funext
                              ( Gamma')
                              ( \ t → is-equiv (first (F0 t))
                                  ( first (G0 t)) (a0 t))
                              ( \ t → is-prop-is-equiv funext
                                  ( first (F0 t))
                                  ( first (G0 t))
                                  ( a0 t))) in
                        let mod ♭ total-is-equiv-is-prop
 : is-prop (is-equiv F̃ G̃ ã)
                          :=
                            mod ♭ (is-prop-is-equiv funext F̃ G̃ ã) in
                        let mod ♭ to-E-Y : is-equiv F̃ G̃ ã → E-Y F0 G0 a0 :=
                          mod ♭ (first (inv-equiv
                            ( E-Y F0 G0 a0)
                            ( is-equiv F̃ G̃ ã)
                            ( equiv-comp
                                ( E-Y F0 G0 a0)
                                ( fiberwise-is-equiv)
                                ( is-equiv F̃ G̃ ã)
                                ( equiv-identity (E-Y F0 G0 a0))
                                ( equiv-iff-is-prop-is-prop
                                    ( fiberwise-is-equiv)
                                    ( is-equiv F̃ G̃ ã)
                                    ( fiberwise-is-equiv-is-prop)
                                    ( total-is-equiv-is-prop)
                                    ( is-equiv-total-iff-is-equiv-fiberwise
                                        ( Gamma')
                                        ( \ t → first (F0 t))
                                        ( \ t → first (G0 t))
                                        ( \ t → a0 t)))))) in
                        b-map (is-equiv F̃ G̃ ã) (E-Y F0 G0 a0) to-E-Y
                          ( mod ♭ (second (cubes-separate F̃ G̃ ã)
                              ( \ (m :♭ nat) →
                                let fixed-F
 : ( v : ♭ (I^n m → I^n n)) → U
                                  :=
                                    \ v →
                                      let mod ♭ v' := v in
                                      Σ ( theta : ♭ (I^n m → shape (_ : 𝕀 | TOP)))
                                      , ( let mod ♭ theta' := theta in
                                          let mod ♭ vc :=
                                            mod ♭ (v' (zero-vec-I^n m)) in
                                          let mod ♭ i :=
                                            mod ♭ (unform (theta' (zero-vec-I^n m))) in
                                          ♭ ( first (F0 (vc , form i)))) in
                                let fixed-G
 : ( v : ♭ (I^n m → I^n n)) → U
                                  :=
                                    \ v →
                                      let mod ♭ v' := v in
                                      Σ ( theta : ♭ (I^n m → shape (_ : 𝕀 | TOP)))
                                      , ( let mod ♭ theta' := theta in
                                          let mod ♭ vc :=
                                            mod ♭ (v' (zero-vec-I^n m)) in
                                          let mod ♭ i :=
                                            mod ♭ (unform (theta' (zero-vec-I^n m))) in
                                          ♭ ( first (G0 (vc , form i)))) in
                                let to-F-split
 : Equiv
                                      ( ♭ ( I^n m → Σ (t : product (I^n n) (shape (_ : 𝕀 | TOP))) , first (F0 t)))
                                      ( Σ ( v : ♭ (I^n m → I^n n)) , fixed-F v)
                                  :=
                                    let mod ♭ F-uncurried :=
                                      mod ♭ (orthogonality-pullback-fiber n m F0) in
                                    let mod ♭ curry-F :=
                                      mod ♭ (equiv-orthogonality-pullback-split n m F0) in
                                    equiv-comp
                                      ( ♭ ( I^n m → Σ (t : product (I^n n) (shape (_ : 𝕀 | TOP))) , first (F0 t)))
                                      ( ♭ ( orthogonality-pullback-split n m F0))
                                      ( Σ ( v : ♭ (I^n m → I^n n)) , fixed-F v)
                                      ( b-equiv
                                          ( I^n m → Σ (t : product (I^n n) (shape (_ : 𝕀 | TOP))) , first (F0 t))
                                          ( orthogonality-pullback-split n m F0)
                                          ( equiv-comp
                                              ( I^n m → Σ (t : product (I^n n) (shape (_ : 𝕀 | TOP))) , first (F0 t))
                                              ( F-uncurried)
                                              ( orthogonality-pullback-split n m F0)
                                              ( orthogonality-pullback n m F0)
                                              ( curry-F)))
                                      ( orthogonality-pullback-flat-commute n m F0) in
                                let to-G-split
 : Equiv
                                      ( ♭ ( I^n m → Σ (t : product (I^n n) (shape (_ : 𝕀 | TOP))) , first (G0 t)))
                                      ( Σ ( v : ♭ (I^n m → I^n n)) , fixed-G v)
                                  :=
                                    let mod ♭ G-uncurried :=
                                      mod ♭ (orthogonality-pullback-fiber n m G0) in
                                    let mod ♭ curry-G :=
                                      mod ♭ (equiv-orthogonality-pullback-split n m G0) in
                                    equiv-comp
                                      ( ♭ ( I^n m → Σ (t : product (I^n n) (shape (_ : 𝕀 | TOP))) , first (G0 t)))
                                      ( ♭ ( orthogonality-pullback-split n m G0))
                                      ( Σ ( v : ♭ (I^n m → I^n n)) , fixed-G v)
                                      ( b-equiv
                                          ( I^n m → Σ (t : product (I^n n) (shape (_ : 𝕀 | TOP))) , first (G0 t))
                                          ( orthogonality-pullback-split n m G0)
                                          ( equiv-comp
                                              ( I^n m → Σ (t : product (I^n n) (shape (_ : 𝕀 | TOP))) , first (G0 t))
                                              ( G-uncurried)
                                              ( orthogonality-pullback-split n m G0)
                                              ( orthogonality-pullback n m G0)
                                              ( curry-G)))
                                      ( orthogonality-pullback-flat-commute n m G0) in
                                let fixed-equiv
 : Equiv
                                      ( Σ ( v : ♭ (I^n m → I^n n)) , fixed-F v)
                                      ( Σ ( v : ♭ (I^n m → I^n n)) , fixed-G v)
                                  :=
                                    total-b-equiv-family2
                                      ( I^n m → I^n n)
                                      ( \ _ → I^n m → shape (_ : 𝕀 | TOP))
                                      ( \ (v' :♭ (I^n m → I^n n))
                                        → \ (theta' :♭ (I^n m → shape (_ : 𝕀 | TOP)))
                                          → let mod ♭ vc :=
                                              mod ♭ (v' (zero-vec-I^n m)) in
                                            let mod ♭ i :=
                                              mod ♭ (unform (theta' (zero-vec-I^n m))) in
                                            ♭ ( first (F0 (vc , form i))))
                                      ( \ (v' :♭ (I^n m → I^n n))
                                        → \ (theta' :♭ (I^n m → shape (_ : 𝕀 | TOP)))
                                          → let mod ♭ vc :=
                                              mod ♭ (v' (zero-vec-I^n m)) in
                                            let mod ♭ i :=
                                              mod ♭ (unform (theta' (zero-vec-I^n m))) in
                                            ♭ ( first (G0 (vc , form i))))
                                      ( \ (v' :♭ (I^n m → I^n n))
                                        → \ (theta' :♭ (I^n m → shape (_ : 𝕀 | TOP)))
                                          → let mod ♭ vc :=
                                              mod ♭ (v' (zero-vec-I^n m)) in
                                            let mod ♭ i :=
                                              mod ♭ (unform (theta' (zero-vec-I^n m))) in
                                            b-equiv
                                              ( first (F0 (vc , form i)))
                                              ( first (G0 (vc , form i)))
                                              ( a0 (vc , form i)
                                              , is-equiv-discrete-interval-elim i
                                                  ( \ j → first (F0 (vc , form j)))
                                                  ( \ j → first (G0 (vc , form j)))
                                                  ( \ j → a0 (vc , form j))
                                                  ( first (e0 vc))
                                                  ( second (e0 vc)))) in
                                is-equiv-b-map-via-splits
                                  ( I^n m → F̃) (I^n m → G̃)
                                  ( \ p t → ã (p t))
                                  ( Σ ( v : ♭ (I^n m → I^n n)) , fixed-F v)
                                  ( Σ ( v : ♭ (I^n m → I^n n)) , fixed-G v)
                                  ( to-F-split) (to-G-split) (fixed-equiv)
                                  ( \ _ → refl))))))) in
        is-equiv-b-map-via-splits
          ( I^n n → Y) (I^n n → X)
          ( \ p t → Y-to-X (p t))
          ( Y-split) (X-split)
          ( to-Y-split) (to-X-split) (Y-to-X-split)
          ( \ _ → refl)
      ) in
    \ e0 e1 →
      transport X
        ( \ (F , (G , (alpha , w))) → (i : 𝕀) → is-equiv (first (F i)) (first (G i)) (alpha i))
        ( Y-to-X (first (second Y-to-X-is-equiv) (f , (g , (a , (e0 , e1))))))
        ( f , (g , (a , (e0 , e1))))
        ( second (second Y-to-X-is-equiv) (f , (g , (a , (e0 , e1)))))
        ( second (second (second (first (second Y-to-X-is-equiv) (f , (g , (a , (e0 , e1))))))))

#def dirglue-mor2fun=f uses (funext weakfunext extext)
  ( F : 𝕀 → S)
  : F = dirglue (F 0₂) (F 1₂) (second (second (mor2fun F)))
  :=
    let G : 𝕀 → S
      := dirglue (F 0₂) (F 1₂) (second (second (mor2fun F))) in
    let a : (j : 𝕀) → first (F j) → first (G j)
      := \ i x →
         ( covariant-transport-line-II
            ( \ (t : 𝕀 | TOP) → first (F (sup i t)))
            ( s-is-covariant-arrow-II (\ j → F (sup i j)))
            ( \ k → form k)
            x
         , \ (t : 1 | i ≡ 0₂) → (x , refl)) in
    let equiv-0 : is-equiv (first (F 0₂)) (first (G 0₂)) (a 0₂)
      := is-equiv-right-factor
           ( first (F 0₂)) (first (G 0₂)) (first (F 0₂))
           ( a 0₂)
           ( \ p → first ((second p) *₁))
           ( second (dirglue-equiv-0 (F 0₂) (F 1₂) (second (second (mor2fun F)))))
           ( is-equiv-identity (first (F 0₂))) in
    let equiv-1 : is-equiv (first (F 1₂)) (first (G 1₂)) (a 1₂)
      := is-equiv-right-factor
           ( first (F 1₂)) (first (G 1₂)) (first (F 1₂))
           ( a 1₂)
           ( \ p → first p)
           ( second (dirglue-equiv-1 (F 0₂) (F 1₂) (second (second (mor2fun F)))))
           ( is-equiv-homotopy (first (F 1₂)) (first (F 1₂))
               ( \ x → covariant-transport-line-II
                    ( \ (t : 𝕀 | TOP) → first (F 1₂))
                    ( s-is-covariant-arrow-II (\ j → F 1₂))
                    ( \ k → form k)
                    x)
               ( \ a → a)
               ( \ x → amazing-covariant-uniqueness-line-II
                    ( \ (t : 𝕀 | TOP) → first (F 1₂))
                    ( s-is-covariant-arrow-II (\ j → F 1₂))
                    x
                    x
                    ( \ _ → x))
               ( is-equiv-identity (first (F 1₂)))) in
    naiveextext-extext extext
      𝕀 ( \ _ → ⊤) (\ _ → BOT)
      ( \ _ → S) (\ _ → recBOT)
      ( F) (G)
      ( \ i →
        eq-pair U (is-a-cov funext weakfunext) (F i) (G i)
          ( first (ua (first (F i)) (first (G i)))
              ( a i , split-lemma F G a equiv-0 equiv-1 i)
          , first
              ( is-prop-is-a-cov funext weakfunext (first (G i))
                ( transport U (is-a-cov funext weakfunext) (first (F i)) (first (G i))
                    ( first (ua (first (F i)) (first (G i))) (a i , split-lemma F G a equiv-0 equiv-1 i))
                    ( second (F i)))
                ( second (G i)))))

```

Directed univalence

```rzk


#def dua uses (funext weakfunext extext)
  : Equiv (Σ (A : S) , (Σ (B : S) , (first A → first B))) ((i : 𝕀) → S)
  := (\ t → dirglue (first t) (first (second t)) (second (second t))
   , ( ( mor2fun , \ t → mor2fun-dirglue=f (first t) (first (second t)) (second (second t)))
   , ( mor2fun , \ F → rev (𝕀 → S) F (dirglue (F 0₂) (F 1₂) (second (second (mor2fun F)))) (dirglue-mor2fun=f F))))

```
