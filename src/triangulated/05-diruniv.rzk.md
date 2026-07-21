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
  ( A : 𝕀 → U)
  ( x : A 0₂)
  ( y : A 1₂)
  : U
  :=
    ( t : 𝕀)
  → ( A t) [ t ≡ 0₂ ↦ x
          , t ≡ 1₂ ↦ y]

#def is-cov-i (A : 𝕀 → U)
  : U
  := (a_0 : A 0₂) → is-contr (Σ (a_1 : A (1₂)) , dhom' (\ i → A i) a_0 a_1)

#def coe-i (A : 𝕀 → U) (phi : is-cov-i A)
  : A 0₂ → A 1₂
  :=
  \ a0 → first (first (phi a0))

#postulate is-prop-is-cov-i
  : ( A : 𝕀 → U) → is-prop (is-cov-i A)

#def is-cov-i-Prop (A : 𝕀 → U)
  : Prop
  := (is-cov-i A , is-prop-is-cov-i A)
```

## Amazing covariance

```rzk

#def is-a-cov (X : U)
  : U
  := amazing-predicate is-cov-i-Prop X

#def S
  : U
  := Σ (A : U) , is-a-cov A

#def S-b
  : ( ♭ U)
  := mod ♭ S

```

## S is covariant

```rzk
#def s-is-cov-i
  ( f : 𝕀 → S)
  : is-cov-i (\ b → first (f b))
  :=
    b-extract
      ( ( f : 𝕀 → S) → is-cov-i (\ b → first (f b)))
      ( amazing-transpose
        ( is-cov-i-Prop)
        ( S)
        ( ( \ s → first s))
        ( ( \ s → second s)))
    f

#def is-a-cov-transpose
  ( A :♭ U)
  ( h :♭ A → U)
  ( f :♭ (a : A) → is-a-cov (h a))
  : ( ♭ ( ( g : 𝕀 → A) → is-cov-i (\ b → h (g b))))
  := amazing-transpose (is-cov-i-Prop) (A) (h) (f)

#def is-a-cov-untranspose
  ( A :♭ U)
  ( h :♭ A → U)
  ( f :♭ (g : 𝕀 → A) → is-cov-i (\ b → h (g b)))
  : ( ♭ ( ( a : A) → is-a-cov (h a)))
  := amazing-untranspose (is-cov-i-Prop) (A) (h) (f)

#def is-a-cov-transposition-equiv
  ( A :♭ U)
  ( h :♭ A → U)
  : Equiv
    ( ♭ ( ( a : A) → is-a-cov (h a)))
    ( ♭ ( ( g : 𝕀 → A) → is-cov-i (\ b → h (g b))))
  := amazing-transpose-untranspose-equiv (is-cov-i-Prop) (A) (h)
```

## mor2fun

```rzk
#def mor2fun (f : 𝕀 → S)
  : Σ ( A : S) , (Σ (B : S) , (first A) → (first B))
  :=
  ( f 0₂ , (f 1₂ , coe-i (\ x → first (f x)) (s-is-cov-i f)))
```

## dirglue

### Amazing covariance closure properties

```rzk


#def is-a-cov-const-cov (A : U) (is-a-cov-A : is-a-cov A)
  : is-cov-i (\ i → A)
  := ?

#def is-cov-sigma-closed
  ( A : 𝕀 → U)
  ( B : (i : 𝕀) → A i → U)
  ( cov-a : is-cov-i A)
  ( is-cov-B : (s : (t : 𝕀) → A t) → is-cov-i (\ t → B t (s t)))
  : is-cov-i (\ i → Σ (a : A i) , B i a)
  := ?

#def is-a-cov-sigma-closed
  ( A : U) (B : A → U)
  ( is-a-cov-A : is-a-cov A)
  ( is-a-cov-B : (a : A) → is-a-cov (B a))
  : is-a-cov (Σ (a : A) , B a)
  :=
    b-extract
      ( ( w
        : Σ ( A' : U)
          , ( Σ ( _ : is-a-cov A')
          , ( Σ ( B' : A' → U)
          , ( ( a : A') → is-a-cov (B' a)))))
        → is-a-cov (Σ (a : first w) , (first (second (second w))) a))
      ( is-a-cov-untranspose
          ( Σ ( A' : U)
          , ( Σ ( _ : is-a-cov A')
          , ( Σ ( B' : A' → U)
          , ( ( a : A') → is-a-cov (B' a)))))
          ( \ (A' , (_ , (B' , _))) → Σ (a : A') , B' a)
          ( \ g →
            is-cov-sigma-closed
              ( \ c → first (g c))
              ( \ c a → (first (second (second (g c)))) a)
              ( b-extract
                  ( ( g' : 𝕀 → (Σ (A' : U) , (Σ (_ : is-a-cov A') , (Σ (B' : A' → U) , ((a : A') → is-a-cov (B' a))))))
                    → is-cov-i (\ b → first (g' b)))
                  ( is-a-cov-transpose
                      ( Σ ( A' : U) , (Σ (_ : is-a-cov A') , (Σ (B' : A' → U) , ((a : A') → is-a-cov (B' a)))))
                      ( \ (A' , _) → A')
                      ( \ (_ , (cA' , _)) → cA'))
                  ( g))
              ( \ s →
                b-extract
                  ( ( G : 𝕀 → (Σ (w : Σ (A' : U) , (Σ (_ : is-a-cov A') , (Σ (B' : A' → U) , ((a : A') → is-a-cov (B' a))))) , first w))
                    → is-cov-i (\ b → (first (second (second (first (G b))))) (second (G b))))
                  ( is-a-cov-transpose
                      ( Σ ( w : Σ (A' : U) , (Σ (_ : is-a-cov A') , (Σ (B' : A' → U) , ((a : A') → is-a-cov (B' a))))) , first w)
                      ( \ ((_ , (_ , (B' , _))) , a) → B' a)
                      ( \ ((_ , (_ , (_ , cB'))) , a) → cB' a))
                  ( \ c → (g c , s c)))))
      ( A , (is-a-cov-A , (B , is-a-cov-B)))

#def is-cov-path-closed
  ( A : 𝕀 → U)
  ( is-cov-A : is-cov-i A)
  ( u v : (i : 𝕀) → A i)
  : is-cov-i (\ t → u t = v t)
  := ?


#def is-a-cov-id-closed (A : U) (is-a-cov-A : is-a-cov A) (x y : A)
  : is-a-cov (x = y)
  :=
    b-extract
      ( ( w : Σ (A' : U) , (Σ (_ : is-a-cov A') , (Σ (_ : A') , A')))
        → is-a-cov ((first (second (second w))) = (second (second (second w)))))
      ( is-a-cov-untranspose
          ( Σ ( A' : U) , (Σ (_ : is-a-cov A') , (Σ (_ : A') , A')))
          ( \ (_ , (_ , (x' , y'))) → x' = y')
          ( \ g →
            is-cov-path-closed
              ( \ c → first (g c))
              ( b-extract
                  ( ( g' : 𝕀 → (Σ (A' : U) , (Σ (_ : is-a-cov A') , (Σ (_ : A') , A'))))
                    → is-cov-i (\ b → first (g' b)))
                  ( is-a-cov-transpose
                      ( Σ ( A' : U) , (Σ (_ : is-a-cov A') , (Σ (_ : A') , A')))
                      ( \ (A' , _) → A')
                      ( \ (_ , (cA' , _)) → cA'))
                  ( g))
              ( \ c → first (second (second (g c))))
              ( \ c → second (second (second (g c))))))
      ( A , (is-a-cov-A , (x , y)))

#def is-a-cov-fib (A B : U) (is-a-cov-A : is-a-cov A) (is-a-cov-B : is-a-cov B) (f : A → B) (b : B)
  : is-a-cov (fib A B f b)
  :=
    is-a-cov-sigma-closed
      A
      ( \ a → (f a) = b)
      is-a-cov-A
      ( \ a → is-a-cov-id-closed B is-a-cov-B (f a) b)

#postulate is-monotone (I : CUBE) (phi : I → TOPE)
  : U

#postulate i===0-is-monotone-op-1 (i : 𝕀)
  : is-monotone 1 (\ s → i ≡ 1₂)

#postulate is-a-cov-contr-ext
    ( phi : (ᵒᵖ TOPE))
    ( monotone : let mod ᵒᵖ phi_op := phi in (ᵒᵖ (is-monotone 1 (\ s → phi_op))))
    ( A : U)
  : is-a-cov ((t : 1 | uninvᵒᵖ phi) → A)


```

```rzk

#def dirglue-is-acov (A B : S) (f : (first A) → (first B)) (i : 𝕀)
  : is-a-cov (
    Σ ( b : (first B))
  , ( ( t : 1 | i ≡ 0₂) → fib (first A) (first B) f b)
  )
  :=
    is-a-cov-sigma-closed
      ( first B)
      ( \ b → (t : 1 | i ≡ 0₂) → fib (first A) (first B) f b)
      ( second B)
      ( \ b →
        let mod ᵒᵖ flip_i := flipᵒᵖ i in
        is-a-cov-contr-ext
          ( invᵒᵖ (i ≡ 0₂))
          ( ( mod ᵒᵖ (i===0-is-monotone-op-1 flip_i)))
          ( fib (first A) (first B) f b))

#def dirglue (A B : S) (f : (first A) → (first B))
  : 𝕀 → S
  :=
    \ i →
      ( Σ ( b : (first B))
      , ( ( t : 1 | i ≡ 0₂) → fib (first A) (first B) f b)
    , dirglue-is-acov A B f i)
```

First part of equivalence mor2fun (dirglue f) is f.

```rzk
#postulate is-prop-is-a-cov (A : U)
  : is-prop (is-a-cov A)

#def equiv-extent-0 (X : U)
  : Equiv ((t : 1 | 0₂ ≡ 0₂) → X) X
  :=
    ( ( \ h → h *₁)
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

#def dirglue-equiv-0 (A B : S) (f : (first A) → (first B))
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

#def dirglue-0=A-EqΣ (A B : S) (f : (first A) → (first B))
  : Eq-Σ U is-a-cov (dirglue A B f 0₂) A
  := (first (ua (first (dirglue A B f 0₂)) (first A)) (dirglue-equiv-0 A B f)
     , first
         ( is-prop-is-a-cov (first A)
           ( transport U is-a-cov
               ( first (dirglue A B f 0₂)) (first A)
               ( first (ua (first (dirglue A B f 0₂)) (first A)) (dirglue-equiv-0 A B f))
               ( second (dirglue A B f 0₂)))
           ( second A)))

#def dirglue_0=A (A B : S) (f : (first A) → (first B))
  : dirglue A B f 0₂ = A
  := eq-pair U is-a-cov (dirglue A B f 0₂) A (dirglue-0=A-EqΣ A B f)

#def dirglue-equiv-1 (A B : S) (f : (first A) → (first B))
  : Equiv (first (dirglue A B f 1₂)) (first B)
  := equiv-total-type-is-contr-fiber
       ( first B)
       ( \ b → (t : 1 | 1₂ ≡ 0₂) → fib (first A) (first B) f b)
       ( \ b → is-contr-extent-1 (fib (first A) (first B) f b))

#def dirglue-1=B-EqΣ (A B : S) (f : (first A) → (first B))
  : Eq-Σ U is-a-cov (dirglue A B f 1₂) B
  := (first (ua (first (dirglue A B f 1₂)) (first B)) (dirglue-equiv-1 A B f)
     , first
         ( is-prop-is-a-cov (first B)
           ( transport U is-a-cov
               ( first (dirglue A B f 1₂)) (first B)
               ( first (ua (first (dirglue A B f 1₂)) (first B)) (dirglue-equiv-1 A B f))
               ( second (dirglue A B f 1₂)))
           ( second B)))

#def dirglue_1=B (A B : S) (f : (first A) → (first B))
  : dirglue A B f 1₂ = B
  := eq-pair U is-a-cov (dirglue A B f 1₂) B (dirglue-1=B-EqΣ A B f)

#def coe-i-uniqueness
  ( A : 𝕀 → U)
  ( phi : is-cov-i A)
  ( a0 : A 0₂)
  ( a1 : A 1₂)
  ( h : dhom' (\ i → A i) a0 a1)
  : coe-i A phi a0 = a1
  :=
    ap
      ( Σ ( x : A 1₂) , dhom' (\ i → A i) a0 x)
      ( A 1₂)
      ( first (phi a0))
      ( a1 , h)
      ( \ z → first z)
      ( second (phi a0) (a1 , h))

#def coe-dirglue-is-f-pointwise
  ( A B : S) (f : (first A) → (first B))
  ( a : first A)
  : transport S (\ s → first s) (dirglue A B f 1₂) B (dirglue_1=B A B f)
      ( coe-i (\ i → first (dirglue A B f i)) (s-is-cov-i (dirglue A B f))
          ( transport-rev S (\ s → first s) (dirglue A B f 0₂) A (dirglue_0=A A B f) a))
    = f a
  :=
    let coe-dirglue : first (dirglue A B f 0₂) → first (dirglue A B f 1₂)
      := coe-i (\ i → first (dirglue A B f i)) (s-is-cov-i (dirglue A B f)) in
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
                           ( transport-first-eq-pair is-a-cov (dirglue A B f 0₂) A (dirglue-0=A-EqΣ A B f) a-in-dirglue-0)
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
              ( transport-first-eq-pair is-a-cov (dirglue A B f 1₂) B (dirglue-1=B-EqΣ A B f) (coe-dirglue a-in-dirglue-0))
              ( transport-ua (first (dirglue A B f 1₂)) (first B) (dirglue-equiv-1 A B f) (coe-dirglue a-in-dirglue-0)))
          -- first (coe-dirglue a-in-dirglue-0) = first a-in-dirglue-0
          ( ap (first (dirglue A B f 1₂)) (first B) (coe-dirglue a-in-dirglue-0) (first a-in-dirglue-0 , second a-in-dirglue-0)
              ( \ z → first z)
              ( coe-i-uniqueness (\ x → first (dirglue A B f x)) (s-is-cov-i (dirglue A B f))
                  ( a-in-dirglue-0) (first a-in-dirglue-0 , second a-in-dirglue-0) (\ (t : 𝕀) → (first a-in-dirglue-0 , second a-in-dirglue-0)))))
      ( base-is-f-a)

#def coe-dirglue-is-f
  ( A B : S) (f : (first A) → (first B))
  : product-transport S S (\ X Y → (first X) → (first Y))
      ( dirglue A B f 0₂) A
      ( dirglue A B f 1₂) B
      ( dirglue_0=A A B f) (dirglue_1=B A B f)
      ( coe-i (\ i → first (dirglue A B f i)) (s-is-cov-i (dirglue A B f)))
    = f
  :=
    let coe-dirglue : first (dirglue A B f 0₂) → first (dirglue A B f 1₂)
      := coe-i (\ i → first (dirglue A B f i)) (s-is-cov-i (dirglue A B f)) in
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


#def mor2fun-dirglue=f (A B : S) (f : (first A) → (first B))
  : mor2fun (dirglue A B f) = (A , (B , f))
  :=
    eq-triple S S (\ X Y → (first X) → (first Y))
      ( mor2fun (dirglue A B f))
      ( A , (B , f))
      ( dirglue_0=A A B f , (dirglue_1=B A B f , (coe-dirglue-is-f A B f)))

#def split-lemma (f g : 𝕀 → S) (a : (i : 𝕀) → first (f i) → first (g i))
  : ( is-equiv (first (f 0₂)) (first (g 0₂)) (a 0₂)) → (is-equiv (first (f 1₂)) (first (g 1₂)) (a 1₂))
    → ( ( i : 𝕀) → (is-equiv (first (f i)) (first (g i)) (a i)))
  := ?

#def dirglue-mor2fun=f
  ( F : 𝕀 → S)
  : F = dirglue (F 0₂) (F 1₂) (second (second (mor2fun F)))
  :=
    let G : 𝕀 → S
      := dirglue (F 0₂) (F 1₂) (second (second (mor2fun F))) in
    let a : (j : 𝕀) → first (F j) → first (G j)
      := \ i x →
         ( coe-i (\ j → first (F (sup i j))) (s-is-cov-i (\ j → F (sup i j))) x
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
               ( \ x → coe-i (\ j → first (F 1₂)) (s-is-cov-i (\ j → F 1₂)) x)
               ( \ a → a)
               ( \ x → coe-i-uniqueness (\ j → first (F 1₂)) (s-is-cov-i (\ j → F 1₂)) x x (\ (t : 𝕀) → x))
               ( is-equiv-identity (first (F 1₂)))) in
    naiveextext-extext extext
      𝕀 ( \ _ → ⊤) (\ _ → BOT)
      ( \ _ → S) (\ _ → recBOT)
      ( F) (G)
      ( \ i →
        eq-pair U is-a-cov (F i) (G i)
          ( first (ua (first (F i)) (first (G i)))
              ( a i , split-lemma F G a equiv-0 equiv-1 i)
          , first
              ( is-prop-is-a-cov (first (G i))
                ( transport U is-a-cov (first (F i)) (first (G i))
                    ( first (ua (first (F i)) (first (G i))) (a i , split-lemma F G a equiv-0 equiv-1 i))
                    ( second (F i)))
                ( second (G i)))))

```

Directed univalence

```rzk


#def dua
  : Equiv (Σ (A : S) , (Σ (B : S) , (first A → first B))) ((i : 𝕀) → S)
  := (\ t → dirglue (first t) (first (second t)) (second (second t))
   , ( ( mor2fun , \ t → mor2fun-dirglue=f (first t) (first (second t)) (second (second t)))
   , ( mor2fun , \ F → rev (𝕀 → S) F (dirglue (F 0₂) (F 1₂) (second (second (mor2fun F)))) (dirglue-mor2fun=f F))))

```
