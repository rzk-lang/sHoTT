# 4. Amazing covariance

This is a literate `rzk` file: `is-covariant-arrow-II`, amazing covariance
`is-a-cov`, and the extension theorem `is-a-cov-ext`. Directed univalence lives in
`05-diruniv.rzk.md`; the ordinary (non-amazing) covariance draft in `03-cub-covariant.rzk.md`.

```rzk
#lang rzk-1

#assume funext : FunExt
#assume weakfunext : WeakFunExt
#assume extext : ExtExt
```

## Prerequisites

- `hott/01-paths.rzk.md` — `ap`, `rev`, `concat`, `transport`.
- `hott/03-equivalences.rzk.md` — `Equiv`, `is-equiv`, `FunExt`, `eq-htpy`, `htpy-eq`, `equiv-comp`, `inv-ap-is-emb`.
- `hott/04-modalities.rzk.md` — `b-map`, `b-equiv`, `b-elim`, `b-path-commute-fwd`.
- `hott/05-half-adjoint-equivalences.rzk.md` — `is-emb-is-equiv`.
- `hott/06-sigma.rzk.md` — `eq-pair`, `total-type`.
- `hott/07-contractible.rzk.md` — `is-contr`, `WeakFunExt`, `equiv-total-type-is-contr-fiber`, `transport-section-eq-at`, `transport-section-eq-at-cancel`.
- `hott/08-fibers.rzk.md` — `fib`.
- `hott/09-families-of-maps.rzk.md` — `total-equiv-family-of-equiv`, `total-b-equiv-family2`.
- `hott/10-propositions.rzk.md` — `is-prop-Unit`, `is-prop-is-prop`, `is-prop-flat`.
- `hott/11-trivial-fibrations.rzk.md` — `is-equiv-domain-sum-of-fibers`.
- `simplicial-hott/03-extension-types.rzk.md` — `ExtExt`, `naiveextext-extext`, `ap-ext-eq-htpy-at`.
- `simplicial-hott/04-right-orthogonal.rzk.md` — RS17 Thm 8.5 / pullback via right orthogonality.
- `simplicial-hott/07-discrete.rzk.md` — `is-discrete`, `is-discrete-function-type`, `is-discrete-extension-type`, `is-discrete-Σ`, `is-discrete-Id`, `is-discrete-op`, `is-contr-of-op`.
- `hott/06-sigma.rzk.md` — `equiv-dependent-curry`, `inv-equiv-dependent-curry`, `equiv-choice3`.
- `simplicial-hott/03-extension-types.rzk.md` — `equiv-ext-shape-fun`.
- `hott/04-modalities.rzk.md` — Modality operations and type aliases.
- `simplicial-hott/05-segal-types.rzk.md` — `hom`, `hom-II`, `dhom-II`, `dhom-from-II`.
- `simplicial-hott/02-simplicial-type-theory.rzk.md` — `shape-at-1`, `equiv-shape-1-op-uninv`, `shape-at-1-of-eq-form-1`, `eq-form-1-of-shape-at-1`, `is-prop-shape-at-1`, `fun-monotonicity-at`, `fun-monotonicity`, `sec-shape-at-1-along-form`, `dhom-II-form-line-shape-at-1`, `is-prop-dhom-II-form-line-shape-at-1`, `is-prop-Σ-dhom-II-form-line-shape-at-1`.
- `triangulated/03-cub-covariant.rzk.md` — `is-covariant-arrow-II`, `covariant-transport-line-II`, `covariant-transport-line-inv-II`, `equiv-is-cov-i-coslice`, `is-covariant-arrow-II-coslice`, `is-covariant-ext`.


## Covariant families

```rzk

#def is-prop-is-covariant-arrow-II uses (weakfunext funext)
  ( A : (t : 𝕀 | TOP) → U)
  : is-prop (is-covariant-arrow-II A)
  := is-prop-is-covariant-II funext weakfunext (shape (_ : 𝕀 | TOP)) (\ (s : shape (_ : 𝕀 | TOP)) → A (unform s))

#def is-covariant-arrow-II-Prop uses (weakfunext funext) (A : (t : 𝕀 | TOP) → U)
  : Prop
  := (is-covariant-arrow-II A , is-prop-is-covariant-arrow-II A)

#def equiv-pointwise-op-I-U
  : Equiv ((i : 𝕀) → ᵒᵖ U) (ᵒᵖ (𝕀 → U))
  :=
    inv-equiv
      ( ᵒᵖ (𝕀 → U))
      ( (i : 𝕀) → ᵒᵖ U)
      ( op-ext-commute-equiv (\ (_ : 𝕀) → U))
```

## Amazing covariance

```rzk

#def is-a-cov uses (funext weakfunext) (X : U)
  : U
  := amazing-predicate is-covariant-arrow-II-Prop X

#def is-discrete-is-a-cov uses (funext weakfunext extext)
  ( A : U)
  ( is-a-cov-A : is-a-cov A)
  : is-discrete A
  := ?is-discrete-is-a-cov

#def is-prop-is-a-cov uses (funext weakfunext) (A : U)
  : is-prop (is-a-cov A)
  := ?is-prop-is-a-cov

```

## Amazing covariance machinery

```rzk
#def is-a-cov-transpose uses (funext weakfunext)
  ( A :♭ U)
  ( h :♭ A → U)
  ( f :♭ (a : A) → is-a-cov (h a))
  : ( ♭ ( ( g : 𝕀 → A) → is-covariant-arrow-II (\ b → h (g b))))
  := amazing-transpose funext weakfunext (is-covariant-arrow-II-Prop) (A) (h) (f)

#def is-a-cov-untranspose uses (funext weakfunext)
  ( A :♭ U)
  ( h :♭ A → U)
  ( f :♭ (g : 𝕀 → A) → is-covariant-arrow-II (\ b → h (g b)))
  : ( ♭ ( ( a : A) → is-a-cov (h a)))
  := amazing-untranspose (is-covariant-arrow-II-Prop) (A) (h) (f)

#def is-a-cov-transposition-equiv uses (funext weakfunext)
  ( A :♭ U)
  ( h :♭ A → U)
  : Equiv
    ( ♭ ( ( a : A) → is-a-cov (h a)))
    ( ♭ ( ( g : 𝕀 → A) → is-covariant-arrow-II (\ b → h (g b))))
  := amazing-transpose-untranspose-equiv funext weakfunext (is-covariant-arrow-II-Prop) (A) (h)

#def amazing-covariant-uniqueness-line-II
  ( A : (t : 𝕀 | TOP) → U)
  ( cov : is-covariant-arrow-II A)
  ( a0 : A 0₂)
  ( a1 : A 1₂)
  ( h : dhom-II (shape (_ : 𝕀 | TOP)) (form 0₂) (form 1₂) (\ t → form t) (\ s → A (unform s)) a0 a1)
  : covariant-transport-line-II A cov (\ k → form k) a0 = a1
  :=
    covariant-uniqueness-II
      ( shape (_ : 𝕀 | TOP))
      ( form 0₂) ( form 1₂)
      ( \ (t : 𝕀) → form t)
      ( \ (t : shape (_ : 𝕀 | TOP)) → A (unform t))
      ( cov)
      ( a0)
      ( a1 , h)

#def amazing-covariant-transport-line-II uses (funext weakfunext)
  ( A : 𝕀 → U)
  ( is-a-cov-A : (i : 𝕀) → is-a-cov (A i))
  ( l : 𝕀 → shape (_ : 𝕀 | TOP))
  : A (unform (l 0₂)) → A (unform (l 1₂))
  :=
    covariant-transport-line-II
      ( \ (t : 𝕀 | TOP) → A t)
      ( b-extract
          ( ( g' : 𝕀 → Σ (X : U) , is-a-cov X)
              → is-covariant-arrow-II (\ b → first (g' b)))
          ( is-a-cov-transpose
              ( Σ ( X : U) , is-a-cov X)
              ( \ (X , _) → X)
              ( \ (_ , cX) → cX))
          ( \ k → (A k , is-a-cov-A k)))
      ( l)

#def amazing-covariant-transport-line-const-II uses (funext weakfunext)
  ( A : 𝕀 → U)
  ( is-a-cov-A : (i : 𝕀) → is-a-cov (A i))
  ( j : 𝕀)
  ( x : A j)
  : amazing-covariant-transport-line-II A is-a-cov-A (\ k → form j) x = x
  :=
    covariant-transport-line-const-II
      ( \ (t : 𝕀 | TOP) → A t)
      ( b-extract
          ( ( g' : 𝕀 → Σ (X : U) , is-a-cov X)
              → is-covariant-arrow-II (\ b → first (g' b)))
          ( is-a-cov-transpose
              ( Σ ( X : U) , is-a-cov X)
              ( \ (X , _) → X)
              ( \ (_ , cX) → cX))
          ( \ k → (A k , is-a-cov-A k)))
      ( form j)
      ( x)

#def amazing-covariant-transport-line-const-at-0-II uses (funext weakfunext)
  ( A : 𝕀 → U)
  ( is-a-cov-A : (i : 𝕀) → is-a-cov (A i))
  ( x : A 0₂)
  : amazing-covariant-transport-line-II A is-a-cov-A (\ k → form (inf 0₂ k)) x = x
  :=
    covariant-transport-line-const-at-0-II
      ( \ (t : 𝕀 | TOP) → A t)
      ( b-extract
          ( ( g' : 𝕀 → Σ (X : U) , is-a-cov X)
              → is-covariant-arrow-II (\ b → first (g' b)))
          ( is-a-cov-transpose
              ( Σ ( X : U) , is-a-cov X)
              ( \ (X , _) → X)
              ( \ (_ , cX) → cX))
          ( \ k → (A k , is-a-cov-A k)))
      ( x)

#def amazing-covariant-transport-line-const-0-sup-II uses (funext weakfunext)
  ( A : 𝕀 → U)
  ( is-a-cov-A : (i : 𝕀) → is-a-cov (A i))
  ( j : 𝕀)
  ( x : A 0₂)
  : amazing-covariant-transport-line-II A is-a-cov-A (\ k → form (inf 0₂ (sup j k))) x = x
  :=
    covariant-transport-line-const-0-sup-II
      ( \ (t : 𝕀 | TOP) → A t)
      ( b-extract
          ( ( g' : 𝕀 → Σ (X : U) , is-a-cov X)
              → is-covariant-arrow-II (\ b → first (g' b)))
          ( is-a-cov-transpose
              ( Σ ( X : U) , is-a-cov X)
              ( \ (X , _) → X)
              ( \ (_ , cX) → cX))
          ( \ k → (A k , is-a-cov-A k)))
      ( j)
      ( x)

#def amazing-covariant-transport-line-const-1-sup-II uses (funext weakfunext)
  ( A : 𝕀 → U)
  ( is-a-cov-A : (i : 𝕀) → is-a-cov (A i))
  ( i : 𝕀)
  ( x : A i)
  : amazing-covariant-transport-line-II A is-a-cov-A (\ k → form (inf i (sup 1₂ k))) x = x
  := amazing-covariant-transport-line-const-II A is-a-cov-A i x

#def amazing-covariant-transport-line-const-0-sup-1-II uses (funext weakfunext)
  ( A : 𝕀 → U)
  ( is-a-cov-A : (i : 𝕀) → is-a-cov (A i))
  ( x : A 0₂)
  : amazing-covariant-transport-line-const-0-sup-II A is-a-cov-A 1₂ x
    = amazing-covariant-transport-line-const-1-sup-II A is-a-cov-A 0₂ x
  := refl

#def amazing-covariant-transport-line-inv-II uses (funext weakfunext)
  ( packed : ᵒᵖ (𝕀 → Σ (X : U) , is-a-cov X))
  ( l : 𝕀 → shape (_ : 𝕀 | TOP))
  : ( let mod ᵒᵖ p := packed in
      let mod ᵒᵖ j₁ := flip_op (unform (l 1₂)) in
      let mod ᵒᵖ j₀ := flip_op (unform (l 0₂)) in
      ᵒᵖ (first (p j₁)) → ᵒᵖ (first (p j₀)))
  :=
    \ x →
      let F-acov
        : (k : 𝕀) → ᵒᵖ (Σ (X : U) , is-a-cov X)
        :=
          \ (k : 𝕀) →
            let mod ᵒᵖ p0 := packed in
            let mod ᵒᵖ j : 𝕀 := flip_op (unform (l k)) in
              mod ᵒᵖ (p0 j)
      in
      let mod ᵒᵖ pA :=
        op-ext-commute-bwd (\ (_ : 𝕀) → Σ (X : U) , is-a-cov X) F-acov
      in
      let mod ᵒᵖ x0 := x in
        mod ᵒᵖ (
          amazing-covariant-transport-line-II
            ( \ i → first (pA i))
            ( \ i → second (pA i))
            ( \ k → form k)
            x0)
```

## Amazing covariance closure properties

```rzk


#def is-a-cov-const-cov uses (funext weakfunext) (A : U) (is-a-cov-A : is-a-cov A)
  : is-covariant-arrow-II (\ (_ : 𝕀 | TOP) → A)
  :=
    b-extract
      ( ( g : 𝕀 → Σ (A' : U) , is-a-cov A')
        → is-covariant-arrow-II (\ b → first (g b)))
      ( is-a-cov-transpose
          ( Σ ( A' : U) , is-a-cov A')
          ( \ (A' , _) → A')
          ( \ (_ , cA') → cA'))
      ( \ _ → (A , is-a-cov-A))

#def is-a-cov-sigma-closed uses (funext weakfunext)
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
            is-covariant-arrow-II-Σ
              ( \ c → first (g c))
              ( \ c a → (first (second (second (g c)))) a)
              ( b-extract
                  ( ( g' : 𝕀 → (Σ (A' : U) , (Σ (_ : is-a-cov A') , (Σ (B' : A' → U) , ((a : A') → is-a-cov (B' a))))))
                    → is-covariant-arrow-II (\ b → first (g' b)))
                  ( is-a-cov-transpose
                      ( Σ ( A' : U) , (Σ (_ : is-a-cov A') , (Σ (B' : A' → U) , ((a : A') → is-a-cov (B' a)))))
                      ( \ (A' , _) → A')
                      ( \ (_ , (cA' , _)) → cA'))
                  ( g))
              ( \ s →
                b-extract
                  ( ( G : 𝕀 → (Σ (w : Σ (A' : U) , (Σ (_ : is-a-cov A') , (Σ (B' : A' → U) , ((a : A') → is-a-cov (B' a))))) , first w))
                    → is-covariant-arrow-II (\ b → (first (second (second (first (G b))))) (second (G b))))
                  ( is-a-cov-transpose
                      ( Σ ( w : Σ (A' : U) , (Σ (_ : is-a-cov A') , (Σ (B' : A' → U) , ((a : A') → is-a-cov (B' a))))) , first w)
                      ( \ ((_ , (_ , (B' , _))) , a) → B' a)
                      ( \ ((_ , (_ , (_ , cB'))) , a) → cB' a))
                  ( \ c → (g c , s c)))))
      ( A , (is-a-cov-A , (B , is-a-cov-B)))

#def is-a-cov-id-closed uses (funext weakfunext) (A : U) (is-a-cov-A : is-a-cov A) (x y : A)
  : is-a-cov (x = y)
  :=
    b-extract
      ( ( w : Σ (A' : U) , (Σ (_ : is-a-cov A') , (Σ (_ : A') , A')))
        → is-a-cov ((first (second (second w))) = (second (second (second w)))))
      ( is-a-cov-untranspose
          ( Σ ( A' : U) , (Σ (_ : is-a-cov A') , (Σ (_ : A') , A')))
          ( \ (_ , (_ , (x' , y'))) → x' = y')
          ( \ g →
            is-covariant-arrow-II-Id
              ( \ c → first (g c))
              ( b-extract
                  ( ( g' : 𝕀 → (Σ (A' : U) , (Σ (_ : is-a-cov A') , (Σ (_ : A') , A'))))
                    → is-covariant-arrow-II (\ b → first (g' b)))
                  ( is-a-cov-transpose
                      ( Σ ( A' : U) , (Σ (_ : is-a-cov A') , (Σ (_ : A') , A')))
                      ( \ (A' , _) → A')
                      ( \ (_ , (cA' , _)) → cA'))
                  ( g))
              ( \ c → first (second (second (g c))))
              ( \ c → second (second (second (g c))))))
      ( A , (is-a-cov-A , (x , y)))

#def is-a-cov-fib uses (funext weakfunext) (A B : U) (is-a-cov-A : is-a-cov A) (is-a-cov-B : is-a-cov B) (f : A → B) (b : B)
  : is-a-cov (fib A B f b)
  :=
    is-a-cov-sigma-closed
      A
      ( \ a → (f a) = b)
      is-a-cov-A
      ( \ a → is-a-cov-id-closed B is-a-cov-B (f a) b)

#def is-a-cov-i===0 uses (funext weakfunext extext) (i : 𝕀)
  : is-a-cov (shape (_ : 1 | i ≡ 1₂))
  :=
    b-extract
      ( ( i' : 𝕀) → is-a-cov (shape (_ : 1 | i' ≡ 1₂)))
      ( first
          ( b-equiv
              ( ( t : shape (_ : 𝕀 | TOP))
                → is-a-cov (shape (_ : 1 | unform t ≡ 1₂)))
              ( ( i' : 𝕀) → is-a-cov (shape (_ : 1 | i' ≡ 1₂)))
              ( inv-equiv
                  ( ( i' : 𝕀) → is-a-cov (shape (_ : 1 | i' ≡ 1₂)))
                  ( ( t : shape (_ : 𝕀 | TOP))
                    → is-a-cov (shape (_ : 1 | unform t ≡ 1₂)))
                  ( equiv-ext-shape-fun
                      𝕀
                      ( \ _ → TOP)
                      ( \ i' → is-a-cov (shape (_ : 1 | i' ≡ 1₂))))))
          ( is-a-cov-untranspose
              ( shape (_ : 𝕀 | TOP))
              ( \ t → shape (_ : 1 | unform t ≡ 1₂))
              ( \ (f : 𝕀 → shape (_ : 𝕀 | TOP)) →
                  \ (x : shape (_ : 𝕀 | TOP)) (y : shape (_ : 𝕀 | TOP))
                    (arr : hom-II (shape (_ : 𝕀 | TOP)) x y)
                    (a0 : shape-at-1 (f (unform x))) →
                    let larr : 𝕀 → shape (_ : 𝕀 | TOP) := \ j → arr j in
                    let f : 𝕀 → shape (_ : 𝕀 | TOP) := \ j → f (unform (larr j)) in
                    let e0
                      : (f 0₂) = form (1₂)
                      := eq-form-1-of-shape-at-1 (f 0₂) a0
                    in
                    let e1
                      : (f 1₂) = form (1₂)
                      := fun-monotonicity f e0
                    in
                    let a1
                      : shape-at-1 (f 1₂)
                      := shape-at-1-of-eq-form-1 (f 1₂) e1
                    in
                    let h
                      : dhom-II (shape (_ : 𝕀 | TOP)) (form 0₂) (form 1₂) (\ t → form t) (\ s → shape-at-1 (f (unform s))) a0 a1
                      := dhom-II-form-line-shape-at-1 f a0 a1 e0
                    in
                      is-contr-is-inhabited-is-prop
                        ( Σ ( a1' : shape-at-1 (f 1₂))
                        , dhom-II (shape (_ : 𝕀 | TOP)) (form 0₂) (form 1₂) (\ t → form t) (\ s → shape-at-1 (f (unform s))) a0 a1')
                        ( is-prop-Σ-dhom-II-form-line-shape-at-1 extext f a0)
                        ( a1 , h))))
      ( i)
```

## Extension theorem

```rzk

#def is-a-cov-ext uses (funext weakfunext extext)
  ( phi : ᵒᵖ TOPE)
  ( shape-is-a-cov :
      let mod ᵒᵖ phi_op := phi in
        ᵒᵖ (is-a-cov (shape (_ : 1 | phi_op))))
  ( A : U)
  ( is-a-cov-A : is-a-cov A)
  : is-a-cov ((t : 1 | uninvᵒᵖ phi) → A)
  :=
    b-extract
      ( ( w
        : Σ ( phi' : ᵒᵖ TOPE)
        , ( Σ ( _ : let mod ᵒᵖ p := phi' in ᵒᵖ (is-a-cov (shape (_ : 1 | p))))
        , ( Σ ( B' : U)
        , is-a-cov B')))
        → is-a-cov ((t : 1 | uninvᵒᵖ (first w)) → first (second (second w))))
      ( is-a-cov-untranspose
          ( Σ ( phi' : ᵒᵖ TOPE)
          , ( Σ ( _ : let mod ᵒᵖ p := phi' in ᵒᵖ (is-a-cov (shape (_ : 1 | p))))
          , ( Σ ( B' : U)
          , is-a-cov B')))
          ( \ (phi' , (_ , (B' , _))) → (t : 1 | uninvᵒᵖ phi') → B')
          ( \ g →
            let phi-i : 𝕀 → ᵒᵖ TOPE
              := \ i → first (g i)
            in
            let phi-shape-i-is-acov
              : ( i : 𝕀)
                  → ( let mod ᵒᵖ p := phi-i i in
                        ᵒᵖ (is-a-cov (shape (_ : 1 | p))))
              := \ i → first (second (g i))
            in
            let D : 𝕀 → U
              := \ i → first (second (second (g i)))
            in
            let is-a-cov-D : (i : 𝕀) → is-a-cov (D i)
              := \ i → second (second (second (g i)))
            in
            let C : ᵒᵖ (𝕀 → U)
              :=
                op-ext-commute-bwd
                  (\ (_ : 𝕀) → U)
                  ( \ i →
                      let mod ᵒᵖ p := phi-i i in
                        mod ᵒᵖ (shape (_ : 1 | p)))
            in
            let is-a-cov-C
              : ( i : 𝕀)
                  → ( let mod ᵒᵖ X := op-ext-commute-fwd (\ (_ : 𝕀) → U) C i in
                        ᵒᵖ (is-a-cov X))
              :=
                \ i →
                  transport
                    ( ᵒᵖ U)
                    ( \ Z → let mod ᵒᵖ X := Z in ᵒᵖ (is-a-cov X))
                    ( let mod ᵒᵖ p := phi-i i in
                        mod ᵒᵖ (shape (_ : 1 | p)))
                    ( op-ext-commute-fwd (\ (_ : 𝕀) → U) C i)
                    refl
                    ( phi-shape-i-is-acov i)
            in
            let packed-S : ᵒᵖ (𝕀 → Σ (X : U) , is-a-cov X)
              :=
                op-ext-commute-bwd
                  (\ (_ : 𝕀) → Σ (X : U) , is-a-cov X)
                  ( \ i →
                      let mod ᵒᵖ X := op-ext-commute-fwd (\ (_ : 𝕀) → U) C i in
                      let mod ᵒᵖ c := is-a-cov-C i in
                        mod ᵒᵖ (X , c))
            in
            let is-cov-C
              : let mod ᵒᵖ C0 := C in ᵒᵖ (is-covariant-arrow-II C0)
              :=
                let mod ᵒᵖ packed := packed-S in
                  mod ᵒᵖ (
                    b-extract
                      ( ( g' : 𝕀 → Σ (X : U) , is-a-cov X)
                          → is-covariant-arrow-II (\ b → first (g' b)))
                      ( is-a-cov-transpose
                          ( Σ ( X : U) , is-a-cov X)
                          ( \ (X , _) → X)
                          ( \ (_ , cX) → cX))
                      packed)
            in
            let is-cov-D : is-covariant-arrow-II D
              :=
                b-extract
                  ( ( g' : 𝕀 →
                    (Σ (phi' : ᵒᵖ TOPE) ,
                    (Σ (_ : let mod ᵒᵖ p := phi' in ᵒᵖ (is-a-cov (shape (_ : 1 | p)))) ,
                    (Σ (B' : U) , is-a-cov B'))))
                    → is-covariant-arrow-II (\ b → first (second (second (g' b)))))
                  ( is-a-cov-transpose
                      ( Σ ( phi' : ᵒᵖ TOPE) , (Σ (_ : let mod ᵒᵖ p := phi' in ᵒᵖ (is-a-cov (shape (_ : 1 | p)))) , (Σ (B' : U) , is-a-cov B')))
                      ( \ (_ , (_ , (B' , _))) → B')
                      ( \ (_ , (_ , (_ , cB'))) → cB'))
                  g
            in
              is-covariant-ext
                funext
                extext
                ( phi-i)
                ( is-cov-C)
                ( D)
                ( is-cov-D)
                ( \ i → is-discrete-is-a-cov (D i) (is-a-cov-D i))))
      ( phi , (shape-is-a-cov , (A , is-a-cov-A)))
```
