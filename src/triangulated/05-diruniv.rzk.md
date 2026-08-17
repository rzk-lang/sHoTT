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
- `simplicial-hott/04-right-orthogonal.rzk.md` — RS17 Thm 8.5 / pullback via right orthogonality.
- `simplicial-hott/07-discrete.rzk.md` — `is-discrete`, `is-discrete-function-type`, `is-discrete-extension-type`, `is-discrete-Σ`, `is-discrete-Id`, `is-discrete-op`.
- `01-cubical-shapes.rzk.md` — `equiv-fun-curry`, `choice-sigma3`, `equiv-fun-cube-shape-TOP`.
- `02-modalities.rzk.md` — Modality operations and type aliases.
- `03-axioms.rzk.md` — Right adjoint, transpose adjunction, `I^n`, `zero-vec-I^n`, flat helpers.


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

-- unfold is-contr: the coe is the unique a1 connected to a0 by a dhom
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

-- (i : I) → ᵒᵖ U  ≃  ᵒᵖ (I → U)  via equiv-op-fun-I-const
#def equiv-pointwise-op-I-U
  : Equiv ((i : 𝕀) → ᵒᵖ U) (ᵒᵖ (𝕀 → U))
  :=
    inv-equiv
      ( ᵒᵖ (𝕀 → U))
      ( (i : 𝕀) → ᵒᵖ U)
      ( equiv-op-fun-I-const U)

-- ᵒᵖ (shape (_ : 1 | ψ))  ≃  shape (_ : 1 | uninv ψ)
-- Uses that inv/uninv are definitional on topes under ᵒᵖ (tope solver).
#def equiv-op-shape-uninv
  ( psi : ᵒᵖ TOPE)
  : Equiv
      ( let mod ᵒᵖ p := psi in ᵒᵖ (shape (_ : 1 | p)))
      ( shape (_ : 1 | uninvᵒᵖ psi))
  :=
    equiv-has-inverse
      ( let mod ᵒᵖ p := psi in ᵒᵖ (shape (_ : 1 | p)))
      ( shape (_ : 1 | uninvᵒᵖ psi))
      ( \ s →
          let mod ᵒᵖ s0 := s in
            form *₁)
      ( \ t → mod ᵒᵖ (form *₁))
      ( \ _ → refl)
      ( \ _ → refl)

#def is-prop-is-cov-i
  ( A : 𝕀 → U)
  : is-prop (is-cov-i A)
  := ?is-prop-is-cov-i

#def is-cov-i-Prop (A : 𝕀 → U)
  : Prop
  := (is-cov-i A , is-prop-is-cov-i A)
```

## Amazing covariance

```rzk

#def is-a-cov (X : U)
  : U
  := amazing-predicate is-cov-i-Prop X

-- Amazing covariance implies discreteness (RS-style: cov ⇒ discrete fibers).
#def is-discrete-is-a-cov uses (extext)
  ( A : U)
  ( is-a-cov-A : is-a-cov A)
  : is-discrete A
  := ?is-discrete-is-a-cov

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

-- transport along a line l : I → shape(I), from A(l 0) to A(l 1)
-- Reindexes via amazing covariance (same pattern as cov-D-l).
#def coe-i-line
  ( A : 𝕀 → U)
  ( is-a-cov-A : (i : 𝕀) → is-a-cov (A i))
  ( l : 𝕀 → shape (_ : 𝕀 | TOP))
  : A (unform (l 0₂)) → A (unform (l 1₂))
  :=
    coe-i
      ( \ k → A (unform (l k)))
      ( b-extract
          ( ( g' : 𝕀 → Σ (X : U) , is-a-cov X)
              → is-cov-i (\ b → first (g' b)))
          ( is-a-cov-transpose
              ( Σ ( X : U) , is-a-cov X)
              ( \ (X , _) → X)
              ( \ (_ , cX) → cX))
          ( \ k → (A (unform (l k)) , is-a-cov-A (unform (l k)))))

-- Constant line: unique covariant lift is the constant dhom, so coe is id.
#def coe-i-line-const
  ( A : 𝕀 → U)
  ( is-a-cov-A : (i : 𝕀) → is-a-cov (A i))
  ( j : 𝕀)
  ( x : A j)
  : coe-i-line A is-a-cov-A (\ k → form j) x = x
  :=
    let l : 𝕀 → shape (_ : 𝕀 | TOP)
      := \ k → form j
    in
      coe-i-uniqueness
        ( \ k → A (unform (l k)))
        ( b-extract
            ( ( g' : 𝕀 → Σ (X : U) , is-a-cov X)
                → is-cov-i (\ b → first (g' b)))
            ( is-a-cov-transpose
                ( Σ ( X : U) , is-a-cov X)
                ( \ (X , _) → X)
                ( \ (_ , cX) → cX))
            ( \ k → (A (unform (l k)) , is-a-cov-A (unform (l k)))))
        x
        x
        ( \ _ → x)

-- Degenerate case of `\k → form (inf i k)` at i=0 (used in is-a-cov-ext / phi0).
#def coe-i-line-const-at-0
  ( A : 𝕀 → U)
  ( is-a-cov-A : (i : 𝕀) → is-a-cov (A i))
  ( x : A 0₂)
  : coe-i-line A is-a-cov-A (\ k → form (inf 0₂ k)) x = x
  :=
    let l : 𝕀 → shape (_ : 𝕀 | TOP)
      := \ k → form (inf 0₂ k)
    in
      coe-i-uniqueness
        ( \ k → A (unform (l k)))
        ( b-extract
            ( ( g' : 𝕀 → Σ (X : U) , is-a-cov X)
                → is-cov-i (\ b → first (g' b)))
            ( is-a-cov-transpose
                ( Σ ( X : U) , is-a-cov X)
                ( \ (X , _) → X)
                ( \ (_ , cX) → cX))
            ( \ k → (A (unform (l k)) , is-a-cov-A (unform (l k)))))
        x
        x
        ( \ _ → x)

-- Degenerate case of H's line at i=0: `\k → form (inf 0 (sup j k))` (= const 0).
#def coe-i-line-const-0-sup
  ( A : 𝕀 → U)
  ( is-a-cov-A : (i : 𝕀) → is-a-cov (A i))
  ( j : 𝕀)
  ( x : A 0₂)
  : coe-i-line A is-a-cov-A (\ k → form (inf 0₂ (sup j k))) x = x
  :=
    let l : 𝕀 → shape (_ : 𝕀 | TOP)
      := \ k → form (inf 0₂ (sup j k))
    in
      coe-i-uniqueness
        ( \ k → A (unform (l k)))
        ( b-extract
            ( ( g' : 𝕀 → Σ (X : U) , is-a-cov X)
                → is-cov-i (\ b → first (g' b)))
            ( is-a-cov-transpose
                ( Σ ( X : U) , is-a-cov X)
                ( \ (X , _) → X)
                ( \ (_ , cX) → cX))
            ( \ k → (A (unform (l k)) , is-a-cov-A (unform (l k)))))
        x
        x
        ( \ _ → x)

-- Degenerate case of H's line at j=1: `\k → form (inf i (sup 1 k))` (= const i).
#def coe-i-line-const-1-sup
  ( A : 𝕀 → U)
  ( is-a-cov-A : (i : 𝕀) → is-a-cov (A i))
  ( i : 𝕀)
  ( x : A i)
  : coe-i-line A is-a-cov-A (\ k → form (inf i (sup 1₂ k))) x = x
  := coe-i-line-const A is-a-cov-A i x

-- Same collapse: coe along ℓ_{0,1} via either packaging.
#def coe-i-line-const-0-sup-1
  ( A : 𝕀 → U)
  ( is-a-cov-A : (i : 𝕀) → is-a-cov (A i))
  ( x : A 0₂)
  : coe-i-line-const-0-sup A is-a-cov-A 1₂ x
    = coe-i-line-const-1-sup A is-a-cov-A 0₂ x
  := refl

-- transport in (λ φ. φ 0 = f0) along b unfolds as ap(eval0)(b)⁻¹ ∙ α.
#def transport-eval0-endpoint
  ( E : 𝕀 → U)
  ( f0 : E 0₂)
  ( φ ψ : (i : 𝕀) → E i)
  ( b : φ = ψ)
  ( α : φ 0₂ = f0)
  : transport
      ( (i : 𝕀) → E i)
      ( \ χ → χ 0₂ = f0)
      φ ψ b α
    = concat
        ( E 0₂)
        ( ψ 0₂)
        ( φ 0₂)
        f0
        ( rev (E 0₂) (φ 0₂) (ψ 0₂)
            ( ap ((i : 𝕀) → E i) (E 0₂) φ ψ (\ χ → χ 0₂) b))
        α
  :=
    concat
      ( ψ 0₂ = f0)
      ( transport ((i : 𝕀) → E i) (\ χ → χ 0₂ = f0) φ ψ b α)
      ( transport (E 0₂) (\ z → z = f0) (φ 0₂) (ψ 0₂)
          ( ap ((i : 𝕀) → E i) (E 0₂) φ ψ (\ χ → χ 0₂) b)
          α)
      ( concat (E 0₂) (ψ 0₂) (φ 0₂) f0
          ( rev (E 0₂) (φ 0₂) (ψ 0₂)
              ( ap ((i : 𝕀) → E i) (E 0₂) φ ψ (\ χ → χ 0₂) b))
          α)
      ( transport-substitution
          ( (i : 𝕀) → E i)
          ( E 0₂)
          ( \ z → z = f0)
          ( \ χ → χ 0₂)
          φ ψ b α)
      ( concat-as-endpoint-transport (E 0₂) f0 (φ 0₂) (ψ 0₂)
          ( ap ((i : 𝕀) → E i) (E 0₂) φ ψ (\ χ → χ 0₂) b)
          α)

-- Given d1 = ap(eval0)(b), cancel: transport b (d1 ∙ q) = q.
#def pack1-transport-cancel
  ( E : 𝕀 → U)
  ( f0 : E 0₂)
  ( φ ψ : (i : 𝕀) → E i)
  ( b : φ = ψ)
  ( d1 : φ 0₂ = ψ 0₂)
  ( q : ψ 0₂ = f0)
  ( d1=ap : d1
      = ap ((i : 𝕀) → E i) (E 0₂) φ ψ (\ χ → χ 0₂) b)
  : transport
      ( (i : 𝕀) → E i)
      ( \ χ → χ 0₂ = f0)
      φ ψ b
      ( concat (E 0₂) (φ 0₂) (ψ 0₂) f0 d1 q)
    = q
  :=
    let apb
      := ap ((i : 𝕀) → E i) (E 0₂) φ ψ (\ χ → χ 0₂) b
    in
    let α
      := concat (E 0₂) (φ 0₂) (ψ 0₂) f0 d1 q
    in
      concat
        ( ψ 0₂ = f0)
        ( transport ((i : 𝕀) → E i) (\ χ → χ 0₂ = f0) φ ψ b α)
        ( concat (E 0₂) (ψ 0₂) (φ 0₂) f0 (rev (E 0₂) (φ 0₂) (ψ 0₂) apb) α)
        q
        ( transport-eval0-endpoint E f0 φ ψ b α)
        ( concat
            ( ψ 0₂ = f0)
            ( concat (E 0₂) (ψ 0₂) (φ 0₂) f0
                ( rev (E 0₂) (φ 0₂) (ψ 0₂) apb)
                ( concat (E 0₂) (φ 0₂) (ψ 0₂) f0 d1 q))
            ( concat (E 0₂) (ψ 0₂) (φ 0₂) f0
                ( rev (E 0₂) (φ 0₂) (ψ 0₂) apb)
                ( concat (E 0₂) (φ 0₂) (ψ 0₂) f0 apb q))
            q
            ( ap
                ( φ 0₂ = ψ 0₂)
                ( ψ 0₂ = f0)
                d1 apb
                ( \ u →
                    concat (E 0₂) (ψ 0₂) (φ 0₂) f0
                      ( rev (E 0₂) (φ 0₂) (ψ 0₂) apb)
                      ( concat (E 0₂) (φ 0₂) (ψ 0₂) f0 u q))
                d1=ap)
            ( retraction-preconcat (E 0₂) (φ 0₂) (ψ 0₂) f0 apb q))

-- ap(eval x0)(funext-section h) = h x0.
#def ap-eval-funext-section uses (funext)
  ( X : U)
  ( A : X → U)
  ( f g : (x : X) → A x)
  ( h : (x : X) → f x = g x)
  ( x0 : X)
  : ap
      ( (x : X) → A x)
      ( A x0)
      f g
      ( \ φ → φ x0)
      ( first (second (funext X A f g)) h)
    = h x0
  :=
    let s
      : ( (x : X) → f x = g x) → (f = g)
      := first (second (funext X A f g))
    in
    let η
      : htpy-eq X A f g (s h) = h
      := second (second (funext X A f g)) h
    in
    let ap=htpy
      : ap ((x : X) → A x) (A x0) f g (\ φ → φ x0) (s h)
        = htpy-eq X A f g (s h) x0
      :=
        ind-path
          ( (x : X) → A x)
          f
          ( \ g' p' →
              ap ((x : X) → A x) (A x0) f g' (\ φ → φ x0) p'
            = htpy-eq X A f g' p' x0)
          ( refl)
          g
          ( s h)
    in
      concat
        ( f x0 = g x0)
        ( ap ((x : X) → A x) (A x0) f g (\ φ → φ x0) (s h))
        ( htpy-eq X A f g (s h) x0)
        ( h x0)
        ap=htpy
        ( ap
            ( (x : X) → f x = g x)
            ( f x0 = g x0)
            ( htpy-eq X A f g (s h))
            h
            ( \ k → k x0)
            η)

-- Same β for cube maps via ExtExt on (I | TOP) with empty boundary.
#def ap-eval0-extext uses (extext)
  ( A : 𝕀 → U)
  ( f g : (i : 𝕀) → A i)
  ( h : (i : 𝕀) → f i = g i)
  : ap
      ( (i : 𝕀) → A i)
      ( A 0₂)
      f g
      ( \ φ → φ 0₂)
      ( first (second (extext 𝕀 (\ _ → TOP) (\ _ → BOT) A (\ _ → recBOT) f g)) h)
    = h 0₂
  :=
    let s
      : ( (i : 𝕀) → f i = g i) → (f = g)
      := first (second (extext 𝕀 (\ _ → TOP) (\ _ → BOT) A (\ _ → recBOT) f g))
    in
    let η
      : ext-htpy-eq 𝕀 (\ _ → TOP) (\ _ → BOT) A (\ _ → recBOT) f g (s h) = h
      := second (second (extext 𝕀 (\ _ → TOP) (\ _ → BOT) A (\ _ → recBOT) f g)) h
    in
    let ap=htpy
      : ap ((i : 𝕀) → A i) (A 0₂) f g (\ φ → φ 0₂) (s h)
        = ext-htpy-eq 𝕀 (\ _ → TOP) (\ _ → BOT) A (\ _ → recBOT) f g (s h) 0₂
      :=
        ind-path
          ( (i : 𝕀) → A i)
          f
          ( \ g' p' →
              ap ((i : 𝕀) → A i) (A 0₂) f g' (\ φ → φ 0₂) p'
            = ext-htpy-eq 𝕀 (\ _ → TOP) (\ _ → BOT) A (\ _ → recBOT) f g' p' 0₂)
          ( refl)
          g
          ( s h)
    in
      concat
        ( f 0₂ = g 0₂)
        ( ap ((i : 𝕀) → A i) (A 0₂) f g (\ φ → φ 0₂) (s h))
        ( ext-htpy-eq 𝕀 (\ _ → TOP) (\ _ → BOT) A (\ _ → recBOT) f g (s h) 0₂)
        ( h 0₂)
        ap=htpy
        ( ap
            ( (i : 𝕀) → f i = g i)
            ( f 0₂ = g 0₂)
            ( ext-htpy-eq 𝕀 (\ _ → TOP) (\ _ → BOT) A (\ _ → recBOT) f g (s h))
            h
            ( \ k → k 0₂)
            η)

-- transport along l from fiber(l 1) to fiber(l 0), reversing inside op via flip_op.
-- packed gives pointwise (X, is-a-cov X); op-fun-I-const-bwd flips the index.
#def coe-i-line-inv
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
        op-fun-I-const-bwd (Σ (X : U) , is-a-cov X) F-acov
      in
      let mod ᵒᵖ x0 := x in
        mod ᵒᵖ (
          coe-i-line
            ( \ i → first (pA i))
            ( \ i → second (pA i))
            ( \ k → form k)
            x0)
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
  :=
    b-extract
      ( ( g : 𝕀 → Σ (A' : U) , is-a-cov A')
        → is-cov-i (\ b → first (g b)))
      ( is-a-cov-transpose
          ( Σ ( A' : U) , is-a-cov A')
          ( \ (A' , _) → A')
          ( \ (_ , cA') → cA'))
      ( \ _ → (A , is-a-cov-A))

-- Σ of discrete types is discrete: see simplicial-hott/07-discrete (`is-discrete-Σ`).

#def is-cov-sigma-closed
  ( A : 𝕀 → U)
  ( B : (i : 𝕀) → A i → U)
  ( cov-a : is-cov-i A)
  ( is-cov-B : (s : (t : 𝕀) → A t) → is-cov-i (\ t → B t (s t)))
  : is-cov-i (\ i → Σ (a : A i) , B i a)
  := ?is-cov-sigma-closed

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
  := ?is-cov-path-closed


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


-- Phoa principle: maps out of 𝕀 are monotone, so f(0)=1 ⇒ f(t)=1.
#postulate fun-monotonicity-at
  ( f : 𝕀 → shape (_ : 𝕀 | TOP))
  ( e : (f 0₂) = (form 1₂))
  ( t : 𝕀)
  : (f t) = form (1₂)

#def fun-monotonicity
  ( f : 𝕀 → shape (_ : 𝕀 | TOP))
  ( e : (f 0₂) = (form 1₂))
  : (f 1₂) = form (1₂)
  := fun-monotonicity-at f e 1₂

#def shape-eq1-of-form-eq
  ( t : shape (_ : 𝕀 | TOP))
  ( e : t = form (1₂))
  : shape (_ : 1 | unform t ≡ 1₂)
  :=
    transport
      ( shape (_ : 𝕀 | TOP))
      ( \ t' → shape (_ : 1 | unform t' ≡ 1₂))
      ( form (1₂))
      ( t)
      ( rev (shape (_ : 𝕀 | TOP)) t (form (1₂)) e)
      ( form (*₁))

-- Bridge: shape-constraint (unform t ≡ 1) → path (t = form 1) (η for shapes).
#def form-eq-of-shape-eq1
  ( t : shape (_ : 𝕀 | TOP))
  ( s : shape (_ : 1 | unform t ≡ 1₂))
  : t = form (1₂)
  := refl

#def is-prop-shape-unform-≡-1
  ( t : shape (_ : 𝕀 | TOP))
  : is-prop (shape (_ : 1 | unform t ≡ 1₂))
  :=
    \ a b →
      is-prop-is-contr
        ( shape (_ : 1 | unform t ≡ 1₂))
        ( form (*₁)
        , \ x →
            rev
              ( shape (_ : 1 | unform t ≡ 1₂))
              ( x)
              ( form (*₁))
              ( refl))
        ( a)
        ( b)

#def is-prop-dhom'-shape-eq-1
  ( f : 𝕀 → shape (_ : 𝕀 | TOP))
  ( a0 : shape (_ : 1 | unform (f 0₂) ≡ 1₂))
  ( a1 : shape (_ : 1 | unform (f 1₂) ≡ 1₂))
  : is-prop (dhom' (\ j → shape (_ : 1 | unform (f j) ≡ 1₂)) a0 a1)
  :=
    is-prop-all-elements-equal
      ( dhom' (\ j → shape (_ : 1 | unform (f j) ≡ 1₂)) a0 a1)
      ( \ h h' →
          naiveextext-extext extext
            ( 𝕀)
            ( \ _ → TOP)
            ( \ t → (t ≡ 0₂) ∨ (t ≡ 1₂))
            ( \ j → shape (_ : 1 | unform (f j) ≡ 1₂))
            ( \ t → h t)
            ( h)
            ( h')
            ( \ t → first (is-prop-shape-unform-≡-1 (f t) (h t) (h' t))))

#def is-prop-Σ-dhom'-shape-eq-1
  ( f : 𝕀 → shape (_ : 𝕀 | TOP))
  ( a0 : shape (_ : 1 | unform (f 0₂) ≡ 1₂))
  : is-prop (
      Σ ( a1 : shape (_ : 1 | unform (f 1₂) ≡ 1₂))
    , dhom' (\ j → shape (_ : 1 | unform (f j) ≡ 1₂)) a0 a1)
  :=
    is-prop-total-type-is-fiberwise-prop-is-prop-base
      ( shape (_ : 1 | unform (f 1₂) ≡ 1₂))
      ( is-prop-shape-unform-≡-1 (f 1₂))
      ( \ a1 → dhom' (\ j → shape (_ : 1 | unform (f j) ≡ 1₂)) a0 a1)
      ( \ a1 → is-prop-dhom'-shape-eq-1 f a0 a1)

-- Section of the family j ↦ (f(j) = 1) via monotone.
#def sec-shape-eq-1
  ( f : 𝕀 → shape (_ : 𝕀 | TOP))
  ( e0 : (f 0₂) = form (1₂))
  : ( j : 𝕀) → shape (_ : 1 | unform (f j) ≡ 1₂)
  := \ j → shape-eq1-of-form-eq (f j) (fun-monotonicity-at f e0 j)

#def dhom'-shape-eq-1
  ( f : 𝕀 → shape (_ : 𝕀 | TOP))
  ( a0 : shape (_ : 1 | unform (f 0₂) ≡ 1₂))
  ( a1 : shape (_ : 1 | unform (f 1₂) ≡ 1₂))
  ( e0 : (f 0₂) = form (1₂))
  : dhom' (\ j → shape (_ : 1 | unform (f j) ≡ 1₂)) a0 a1
  :=
    let a0'
      : shape (_ : 1 | unform (f 0₂) ≡ 1₂)
      := sec-shape-eq-1 f e0 0₂
    in
    let a1'
      : shape (_ : 1 | unform (f 1₂) ≡ 1₂)
      := sec-shape-eq-1 f e0 1₂
    in
    let h'
      : dhom'
          ( \ j → shape (_ : 1 | unform (f j) ≡ 1₂))
          ( a0')
          ( a1')
      := sec-shape-eq-1 f e0
    in
    let p0
      : a0' = a0
      := first (is-prop-shape-unform-≡-1 (f 0₂) a0' a0)
    in
    let p1
      : a1' = a1
      := first (is-prop-shape-unform-≡-1 (f 1₂) a1' a1)
    in
    let h1
      : dhom' (\ j → shape (_ : 1 | unform (f j) ≡ 1₂)) a0' a1
      :=
        transport
          ( shape (_ : 1 | unform (f 1₂) ≡ 1₂))
          ( \ y → dhom' (\ j → shape (_ : 1 | unform (f j) ≡ 1₂)) a0' y)
          ( a1')
          ( a1)
          ( p1)
          ( h')
    in
      transport
        ( shape (_ : 1 | unform (f 0₂) ≡ 1₂))
        ( \ x → dhom' (\ j → shape (_ : 1 | unform (f j) ≡ 1₂)) x a1)
        ( a0')
        ( a0)
        ( p0)
        ( h1)

#def is-a-cov-i===0 (i : 𝕀)
  : is-a-cov (shape (_ : 1 | i ≡ 1₂))
  :=
    b-extract
      ( ( i' : 𝕀) → is-a-cov (shape (_ : 1 | i' ≡ 1₂)))
      ( first
          ( flat-equiv
              ( ( t : shape (_ : 𝕀 | TOP))
                → is-a-cov (shape (_ : 1 | unform t ≡ 1₂)))
              ( ( i' : 𝕀) → is-a-cov (shape (_ : 1 | i' ≡ 1₂)))
              ( inv-equiv
                  ( ( i' : 𝕀) → is-a-cov (shape (_ : 1 | i' ≡ 1₂)))
                  ( ( t : shape (_ : 𝕀 | TOP))
                    → is-a-cov (shape (_ : 1 | unform t ≡ 1₂)))
                  ( equiv-fun-cube-shape-TOP
                      𝕀
                      ( \ i' → is-a-cov (shape (_ : 1 | i' ≡ 1₂))))))
          ( is-a-cov-untranspose
              ( shape (_ : 𝕀 | TOP))
              ( \ t → shape (_ : 1 | unform t ≡ 1₂))
              ( \ (f : 𝕀 → shape (_ : 𝕀 | TOP)) →
                  \ (a0 : shape (_ : 1 | unform (f 0₂) ≡ 1₂)) →
                    let e0
                      : (f 0₂) = form (1₂)
                      := form-eq-of-shape-eq1 (f 0₂) a0
                    in
                    let e1
                      : (f 1₂) = form (1₂)
                      := fun-monotonicity f e0
                    in
                    let a1
                      : shape (_ : 1 | unform (f 1₂) ≡ 1₂)
                      := shape-eq1-of-form-eq (f 1₂) e1
                    in
                    let h
                      : dhom'
                          ( \ j → shape (_ : 1 | unform (f j) ≡ 1₂))
                          ( a0)
                          ( a1)
                      := dhom'-shape-eq-1 f a0 a1 e0
                    in
                      is-contr-is-inhabited-is-prop
                        ( Σ ( a1' : shape (_ : 1 | unform (f 1₂) ≡ 1₂))
                        , dhom' (\ j → shape (_ : 1 | unform (f j) ≡ 1₂)) a0 a1')
                        ( is-prop-Σ-dhom'-shape-eq-1 f a0)
                        ( a1 , h))))
      ( i)

-- dhom' A x y ≃ Σ(φ : (i:I) → A i), (φ 0 = x) × (φ 1 = y)
#def equiv-dhom'-Σ
  ( A : 𝕀 → U)
  ( x : A 0₂)
  ( y : A 1₂)
  : Equiv
      ( dhom' A x y)
      ( Σ (φ : (i : 𝕀) → A i) , product (φ 0₂ = x) (φ 1₂ = y))
  :=
    equiv-has-inverse
      ( dhom' A x y)
      ( Σ (φ : (i : 𝕀) → A i) , product (φ 0₂ = x) (φ 1₂ = y))
      ( \ h → (\ t → h t , (refl , refl)))
      ( \ (φ , (p , q)) →
          ind-path (A 0₂) (φ 0₂) (\ x' _ → dhom' A x' y) (
            ind-path (A 1₂) (φ 1₂) (\ y' _ → dhom' A (φ 0₂) y') (
              \ t → φ t
            ) y q
          ) x p)
      ( \ h → refl)
      ( \ (φ , (p , q)) →
          ind-path (A 0₂) (φ 0₂)
            ( \ x' p' →
                ( \ t →
                    ind-path (A 0₂) (φ 0₂) (\ x'' _ → dhom' A x'' y) (
                      ind-path (A 1₂) (φ 1₂) (\ y' _ → dhom' A (φ 0₂) y') (
                        \ t' → φ t'
                      ) y q
                    ) x' p' t
                , (refl , refl))
                =_{Σ (ψ : (i : 𝕀) → A i) , product (ψ 0₂ = x') (ψ 1₂ = y)}
                  (φ , (p' , q)))
            ( ind-path (A 1₂) (φ 1₂)
                ( \ y' q' →
                    ( \ t →
                        ind-path (A 1₂) (φ 1₂) (\ y'' _ → dhom' A (φ 0₂) y'') (
                          \ t' → φ t'
                        ) y' q' t
                    , (refl , refl))
                    =_{Σ (ψ : (i : 𝕀) → A i) , product (ψ 0₂ = φ 0₂) (ψ 1₂ = y')}
                      (φ , (refl , q')))
                ( refl)
                y q)
            x p)

-- is-cov-i A = (a₀:A 0) → isContr(Σ(a₁:A 1), dhom' A a₀ a₁)
--            ≃ (a₀:A 0) → isContr(Σ(φ:(i:I)→A i), φ 0 = a₀)
#def equiv-is-cov-i-coslice
  ( A : 𝕀 → U)
  ( a0 : A 0₂)
  : Equiv
      ( Σ (a1 : A 1₂) , dhom' A a0 a1)
      ( Σ (φ : (i : 𝕀) → A i) , φ 0₂ = a0)
  :=
    equiv-has-inverse
      ( Σ (a1 : A 1₂) , dhom' A a0 a1)
      ( Σ (φ : (i : 𝕀) → A i) , φ 0₂ = a0)
      ( \ (a1 , h) → (\ t → h t , refl))
      ( \ (φ , p) →
          ( φ 1₂
          , ind-path (A 0₂) (φ 0₂)
              ( \ a0' _ → dhom' A a0' (φ 1₂))
              ( \ t → φ t)
              a0 p))
      ( \ (a1 , h) → refl)
      ( \ (φ , p) →
          ind-path (A 0₂) (φ 0₂)
            ( \ a0' p' →
                ( \ t →
                    ind-path (A 0₂) (φ 0₂)
                      ( \ a0'' _ → dhom' A a0'' (φ 1₂))
                      ( \ t' → φ t')
                      a0' p' t
                , refl)
                =_{Σ (ψ : (i : 𝕀) → A i) , ψ 0₂ = a0'}
                  (φ , p'))
            ( refl)
            a0 p)

#def is-cov-i-coslice
  ( A : 𝕀 → U)
  ( cov : is-cov-i A)
  ( a0 : A 0₂)
  : is-contr (Σ (φ : (i : 𝕀) → A i) , φ 0₂ = a0)
  :=
    is-contr-equiv-is-contr
      ( Σ (a1 : A 1₂) , dhom' A a0 a1)
      ( Σ (φ : (i : 𝕀) → A i) , φ 0₂ = a0)
      ( equiv-is-cov-i-coslice A a0)
      ( cov a0)

#def is-a-cov-ext uses (funext extext)
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
                op-fun-I-const-bwd
                  U
                  ( \ i →
                      let mod ᵒᵖ p := phi-i i in
                        mod ᵒᵖ (shape (_ : 1 | p)))
            in
            let is-a-cov-C
              : ( i : 𝕀)
                  → ( let mod ᵒᵖ X := op-fun-I-const-fwd U C i in
                        ᵒᵖ (is-a-cov X))
              :=
                \ i →
                  transport
                    ( ᵒᵖ U)
                    ( \ Z → let mod ᵒᵖ X := Z in ᵒᵖ (is-a-cov X))
                    ( let mod ᵒᵖ p := phi-i i in
                        mod ᵒᵖ (shape (_ : 1 | p)))
                    ( op-fun-I-const-fwd U C i)
                    refl
                    ( phi-shape-i-is-acov i)
            in
            let packed-S : ᵒᵖ (𝕀 → Σ (X : U) , is-a-cov X)
              :=
                op-fun-I-const-bwd
                  ( Σ ( X : U) , is-a-cov X)
                  ( \ i →
                      let mod ᵒᵖ X := op-fun-I-const-fwd U C i in
                      let mod ᵒᵖ c := is-a-cov-C i in
                        mod ᵒᵖ (X , c))
            in
            let is-cov-C
              : let mod ᵒᵖ C0 := C in ᵒᵖ (is-cov-i C0)
              :=
                let mod ᵒᵖ packed := packed-S in
                  mod ᵒᵖ (
                    b-extract
                      ( ( g' : 𝕀 → Σ (X : U) , is-a-cov X)
                          → is-cov-i (\ b → first (g' b)))
                      ( is-a-cov-transpose
                          ( Σ ( X : U) , is-a-cov X)
                          ( \ (X , _) → X)
                          ( \ (_ , cX) → cX))
                      packed)
            in
            let is-cov-D : is-cov-i D
              :=
                b-extract
                  ( ( g' : 𝕀 →
                    (Σ (phi' : ᵒᵖ TOPE) ,
                    (Σ (_ : let mod ᵒᵖ p := phi' in ᵒᵖ (is-a-cov (shape (_ : 1 | p)))) ,
                    (Σ (B' : U) , is-a-cov B'))))
                    → is-cov-i (\ b → first (second (second (g' b)))))
                  ( is-a-cov-transpose
                      ( Σ ( phi' : ᵒᵖ TOPE) , (Σ (_ : let mod ᵒᵖ p := phi' in ᵒᵖ (is-a-cov (shape (_ : 1 | p)))) , (Σ (B' : U) , is-a-cov B')))
                      ( \ (_ , (_ , (B' , _))) → B')
                      ( \ (_ , (_ , (_ , cB'))) → cB'))
                  g
            in
            let E : 𝕀 → U
              := \ i → (t : 1 | uninvᵒᵖ (phi-i i)) → D i
            in
              \ (f0 : E 0₂) →
                let phi
                  : (i : 𝕀) → E i
                  :=
                    \ i _ →
                      let l : 𝕀 → shape (_ : 𝕀 | TOP)
                        := \ k → form (inf i k)
                      in
                      let s-op
                        : let mod ᵒᵖ p := phi-i 0₂ in
                            ᵒᵖ (shape (_ : 1 | p))
                        :=
                          coe-i-line-inv packed-S l (mod ᵒᵖ (form *₁))
                      in
                      let s0
                        := first (equiv-op-shape-uninv (phi-i 0₂)) s-op
                      in
                        coe-i-line D is-a-cov-D l
                          ( f0 (unform s0))
                in
                let phi0-eq-f0 : phi 0₂ = f0
                  :=
                    ap
                      ( (s : shape (_ : 1 | uninvᵒᵖ (phi-i 0₂))) → D 0₂)
                      ( (t : 1 | uninvᵒᵖ (phi-i 0₂)) → D 0₂)
                      ( \ (s : shape (_ : 1 | uninvᵒᵖ (phi-i 0₂))) → phi 0₂ (unform s))
                      ( \ (s : shape (_ : 1 | uninvᵒᵖ (phi-i 0₂))) → f0 (unform s))
                      ( \ pre t → pre (form t))
                      ( eq-htpy funext
                          ( shape (_ : 1 | uninvᵒᵖ (phi-i 0₂)))
                          ( \ _ → D 0₂)
                          ( \ (s : shape (_ : 1 | uninvᵒᵖ (phi-i 0₂))) → phi 0₂ (unform s))
                          ( \ (s : shape (_ : 1 | uninvᵒᵖ (phi-i 0₂))) → f0 (unform s))
                          ( \ (s : shape (_ : 1 | uninvᵒᵖ (phi-i 0₂))) →
                              coe-i-line-const-at-0 D is-a-cov-D
                                ( f0
                                    ( unform
                                        ( first
                                            ( equiv-op-shape-uninv (phi-i 0₂))
                                            ( coe-i-line-inv packed-S
                                                ( \ k → form (inf 0₂ k))
                                                ( mod ᵒᵖ (form *₁))))))))
                in
                let contr-center
                  : Σ (φ : (i : 𝕀) → E i) , φ 0₂ = f0
                  := (phi , phi0-eq-f0)
                in
                let contr-hom
                  : ( y : Σ (φ : (i : 𝕀) → E i) , φ 0₂ = f0)
                      → contr-center = y
                  :=
                    \ (p , q) →
                      let H
                        : ( i j : 𝕀)
                          → ( let mod ᵒᵖ C' := C in
                              let mod ᵒᵖ fi := flipᵒᵖ i in
                                ᵒᵖ (C' fi))
                          → D i
                        :=
                          \ i j c →
                            let l : 𝕀 → shape (_ : 𝕀 | TOP)
                              := \ k → form (inf i (sup j k))
                            in
                            let s-op
                              : let mod ᵒᵖ p := phi-i (inf i j) in
                                  ᵒᵖ (shape (_ : 1 | p))
                              :=
                                coe-i-line-inv packed-S l c
                            in
                            let s-mid
                              := first (equiv-op-shape-uninv (phi-i (inf i j))) s-op
                            in
                              coe-i-line D is-a-cov-D l
                                ( p (inf i j) (unform s-mid))
                      in
                      -- Ĥ j :≡ H(-,j) at the constant shape code.
                      let H-sec
                        : (j : 𝕀) → (i : 𝕀) → E i
                        :=
                          \ j i t →
                            H i j
                              ( let c
                                  : let mod ᵒᵖ C' := C in
                                    let mod ᵒᵖ fi := flipᵒᵖ i in
                                      ᵒᵖ (C' fi)
                                := mod ᵒᵖ (form *₁)
                              in
                                c)
                      in
                      -- d: i=0 row collapses (ℓ_{0,j} prop-const at 0 ⇒ coe = id).
                      -- d j : (Ĥ j) 0 = g 0.
                      let d
                        : (j : 𝕀) → H-sec j 0₂ = p 0₂
                        :=
                          \ j →
                            ap
                              ( (s : shape (_ : 1 | uninvᵒᵖ (phi-i 0₂))) → D 0₂)
                              ( (t : 1 | uninvᵒᵖ (phi-i 0₂)) → D 0₂)
                              ( \ (s : shape (_ : 1 | uninvᵒᵖ (phi-i 0₂))) →
                                  H-sec j 0₂ (unform s))
                              ( \ (s : shape (_ : 1 | uninvᵒᵖ (phi-i 0₂))) →
                                  p 0₂ (unform s))
                              ( \ pre t → pre (form t))
                              ( eq-htpy funext
                                  ( shape (_ : 1 | uninvᵒᵖ (phi-i 0₂)))
                                  ( \ _ → D 0₂)
                                  ( \ (s : shape (_ : 1 | uninvᵒᵖ (phi-i 0₂))) →
                                      H-sec j 0₂ (unform s))
                                  ( \ (s : shape (_ : 1 | uninvᵒᵖ (phi-i 0₂))) →
                                      p 0₂ (unform s))
                                  ( \ (s : shape (_ : 1 | uninvᵒᵖ (phi-i 0₂))) →
                                      coe-i-line-const-0-sup
                                        D is-a-cov-D j
                                        ( p 0₂ (unform s))))
                      in
                      -- r :≡ λj. d j ∙ q  (only: collapse to g0, then q to f0).
                      let r
                        : (j : 𝕀) → H-sec j 0₂ = f0
                        :=
                          \ j →
                            concat (E 0₂) (H-sec j 0₂) (p 0₂) f0 (d j) q
                      in
                      -- Pack H(-,j) with endpoint witness r j into the coslice fiber.
                      -- Endpoints: pack 0 ∼ center (phi), pack 1 ∼ (p, q);
                      -- `\t → pack t` is then a hom, and discreteness turns it into =.
                      let pack
                        : (j : 𝕀)
                          → Σ (φ : (i : 𝕀) → E i) , φ 0₂ = f0
                        := \ j → (H-sec j , r j)
                      in
                      -- discrete = hom ≃ Id; total = is-discrete-Σ of the two pieces
                      let is-discrete-E-i
                        : (i : 𝕀) → is-discrete (E i)
                        :=
                          \ i →
                            is-discrete-extension-type
                              extext
                              ( 1)
                              ( \ _ → uninvᵒᵖ (phi-i i))
                              ( \ _ → D i)
                              ( \ _ →
                                  is-discrete-is-a-cov (D i) (is-a-cov-D i))
                      in
                      let is-discrete-E-I
                        : is-discrete ((i : 𝕀) → E i)
                        :=
                          is-discrete-extension-type
                            extext
                            ( 𝕀)
                            ( \ _ → TOP)
                            ( \ i → E i)
                            ( is-discrete-E-i)
                      in
                      let is-discrete-fib
                        : ( φ : (i : 𝕀) → E i)
                          → is-discrete (φ 0₂ = f0)
                        :=
                          \ φ →
                            is-discrete-Id
                              ( E 0₂)
                              ( is-discrete-E-i 0₂)
                              ( φ 0₂)
                              f0
                      in
                      let is-discrete-total
                        : is-discrete
                            ( Σ (φ : (i : 𝕀) → E i) , φ 0₂ = f0)
                        :=
                          is-discrete-Σ
                            ( (i : 𝕀) → E i)
                            ( \ φ → φ 0₂ = f0)
                            ( is-discrete-E-I)
                            ( is-discrete-fib)
                      in
                      let pack0-eq
                        : pack 0₂ = contr-center
                        :=
                          -- J on q: take f0' := p 0, q' := refl. Then Ĥ 0 ≡ phi'
                          -- (same coe along ℓ_i from g0), so the j=0 corner is free.
                          ind-path
                            ( E 0₂)
                            ( p 0₂)
                            ( \ f0' q' →
                                let phi'
                                  : (i : 𝕀) → E i
                                  :=
                                    \ i _ →
                                      let l : 𝕀 → shape (_ : 𝕀 | TOP)
                                        := \ k → form (inf i k)
                                      in
                                      let s-op
                                        : let mod ᵒᵖ p' := phi-i 0₂ in
                                            ᵒᵖ (shape (_ : 1 | p'))
                                        :=
                                          coe-i-line-inv packed-S l (mod ᵒᵖ (form *₁))
                                      in
                                      let s0
                                        := first (equiv-op-shape-uninv (phi-i 0₂)) s-op
                                      in
                                        coe-i-line D is-a-cov-D l
                                          ( f0' (unform s0))
                                in
                                let phi0'
                                  : phi' 0₂ = f0'
                                  :=
                                    ap
                                      ( (s : shape (_ : 1 | uninvᵒᵖ (phi-i 0₂))) → D 0₂)
                                      ( (t : 1 | uninvᵒᵖ (phi-i 0₂)) → D 0₂)
                                      ( \ (s : shape (_ : 1 | uninvᵒᵖ (phi-i 0₂))) →
                                          phi' 0₂ (unform s))
                                      ( \ (s : shape (_ : 1 | uninvᵒᵖ (phi-i 0₂))) →
                                          f0' (unform s))
                                      ( \ pre t → pre (form t))
                                      ( eq-htpy funext
                                          ( shape (_ : 1 | uninvᵒᵖ (phi-i 0₂)))
                                          ( \ _ → D 0₂)
                                          ( \ (s : shape (_ : 1 | uninvᵒᵖ (phi-i 0₂))) →
                                              phi' 0₂ (unform s))
                                          ( \ (s : shape (_ : 1 | uninvᵒᵖ (phi-i 0₂))) →
                                              f0' (unform s))
                                          ( \ (s : shape (_ : 1 | uninvᵒᵖ (phi-i 0₂))) →
                                              coe-i-line-const-at-0 D is-a-cov-D
                                                ( f0'
                                                    ( unform
                                                        ( first
                                                            ( equiv-op-shape-uninv (phi-i 0₂))
                                                            ( coe-i-line-inv packed-S
                                                                ( \ k → form (inf 0₂ k))
                                                                ( mod ᵒᵖ (form *₁))))))))
                                in
                                let r'
                                  : (j : 𝕀) → H-sec j 0₂ = f0'
                                  :=
                                    \ j →
                                      concat
                                        ( E 0₂)
                                        ( H-sec j 0₂)
                                        ( p 0₂)
                                        ( f0')
                                        ( d j)
                                        ( q')
                                in
                                  ( H-sec 0₂ , r' 0₂)
                                  =_{Σ (φ : (i : 𝕀) → E i) , φ 0₂ = f0'}
                                    ( phi' , phi0'))
                            ( refl)
                            ( f0)
                            ( q)
                      in
                      let pack1-eq
                        : pack 1₂ = (p , q)
                        :=
                          let ptwise
                            : (i : 𝕀) → H-sec 1₂ i = p i
                            :=
                              \ i →
                                ap
                                  ( (s : shape (_ : 1 | uninvᵒᵖ (phi-i i))) → D i)
                                  ( (t : 1 | uninvᵒᵖ (phi-i i)) → D i)
                                  ( \ (s : shape (_ : 1 | uninvᵒᵖ (phi-i i))) →
                                      H-sec 1₂ i (unform s))
                                  ( \ (s : shape (_ : 1 | uninvᵒᵖ (phi-i i))) →
                                      p i (unform s))
                                  ( \ pre t → pre (form t))
                                  ( eq-htpy funext
                                      ( shape (_ : 1 | uninvᵒᵖ (phi-i i)))
                                      ( \ _ → D i)
                                      ( \ (s : shape (_ : 1 | uninvᵒᵖ (phi-i i))) →
                                          H-sec 1₂ i (unform s))
                                      ( \ (s : shape (_ : 1 | uninvᵒᵖ (phi-i i))) →
                                          p i (unform s))
                                      ( \ (s : shape (_ : 1 | uninvᵒᵖ (phi-i i))) →
                                          coe-i-line-const-1-sup
                                            D is-a-cov-D i
                                            ( p i (unform s))))
                          in
                          let H-sec1=p
                            : H-sec 1₂ = p
                            :=
                              first
                                ( second
                                    ( extext
                                        ( 𝕀)
                                        ( \ _ → TOP)
                                        ( \ _ → BOT)
                                        ( \ i → E i)
                                        ( \ _ → recBOT)
                                        ( H-sec 1₂)
                                        ( p)))
                                ( ptwise)
                          in
                          let d1=ap-eval
                            : d 1₂
                              = ap
                                  ( (i : 𝕀) → E i)
                                  ( E 0₂)
                                  ( H-sec 1₂)
                                  ( p)
                                  ( \ φ → φ 0₂)
                                  ( H-sec1=p)
                            :=
                              concat
                                ( H-sec 1₂ 0₂ = p 0₂)
                                ( d 1₂)
                                ( ptwise 0₂)
                                ( ap
                                    ( (i : 𝕀) → E i)
                                    ( E 0₂)
                                    ( H-sec 1₂)
                                    ( p)
                                    ( \ φ → φ 0₂)
                                    ( H-sec1=p))
                                ( refl)
                                ( rev
                                    ( H-sec 1₂ 0₂ = p 0₂)
                                    ( ap
                                        ( (i : 𝕀) → E i)
                                        ( E 0₂)
                                        ( H-sec 1₂)
                                        ( p)
                                        ( \ φ → φ 0₂)
                                        ( H-sec1=p))
                                    ( ptwise 0₂)
                                    ( ap-eval0-extext
                                        ( \ i → E i)
                                        ( H-sec 1₂)
                                        ( p)
                                        ( ptwise)))
                          in
                          let pack1-eq-second
                            : transport
                                ( (i : 𝕀) → E i)
                                ( \ φ → φ 0₂ = f0)
                                ( H-sec 1₂)
                                ( p)
                                ( H-sec1=p)
                                ( r 1₂)
                              = q
                            :=
                              pack1-transport-cancel
                                E f0
                                ( H-sec 1₂)
                                p
                                ( H-sec1=p)
                                ( d 1₂)
                                q
                                ( d1=ap-eval)
                          in
                            eq-pair
                              ( (i : 𝕀) → E i)
                              ( \ φ → φ 0₂ = f0)
                              ( pack 1₂)
                              ( p , q)
                              ( H-sec1=p
                              , pack1-eq-second)
                      in
                      let arrow-pack
                        : hom
                            ( Σ (φ : (i : 𝕀) → E i) , φ 0₂ = f0)
                            ( pack 0₂)
                            ( pack 1₂)
                        := \ t → pack t
                      in
                      let arrow
                        : hom
                            ( Σ (φ : (i : 𝕀) → E i) , φ 0₂ = f0)
                            ( contr-center)
                            ( p , q)
                        :=
                          transport
                            ( Σ (φ : (i : 𝕀) → E i) , φ 0₂ = f0)
                            ( \ z →
                                hom
                                  ( Σ (φ : (i : 𝕀) → E i) , φ 0₂ = f0)
                                  ( z)
                                  ( p , q))
                            ( pack 0₂)
                            ( contr-center)
                            ( pack0-eq)
                            ( transport
                                ( Σ (φ : (i : 𝕀) → E i) , φ 0₂ = f0)
                                ( \ z →
                                    hom
                                      ( Σ (φ : (i : 𝕀) → E i) , φ 0₂ = f0)
                                      ( pack 0₂)
                                      ( z))
                                ( pack 1₂)
                                ( p , q)
                                ( pack1-eq)
                                ( arrow-pack))
                      in
                        first
                          ( has-inverse-is-equiv
                              ( contr-center = (p , q))
                              ( hom
                                  ( Σ (φ : (i : 𝕀) → E i) , φ 0₂ = f0)
                                  ( contr-center)
                                  ( p , q))
                              ( hom-eq
                                  ( Σ (φ : (i : 𝕀) → E i) , φ 0₂ = f0)
                                  ( contr-center)
                                  ( p , q))
                              ( is-discrete-total contr-center (p , q)))
                          ( arrow)
                in
                  is-contr-equiv-is-contr'
                    ( Σ (f1 : E 1₂) , dhom' E f0 f1)
                    ( Σ (φ : (i : 𝕀) → E i) , φ 0₂ = f0)
                    ( equiv-is-cov-i-coslice E f0)
                    ( contr-center , contr-hom)))
      ( phi , (shape-is-a-cov , (A , is-a-cov-A)))

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
            is-a-cov-ext
              ( mod ᵒᵖ (flip_i ≡ 1₂))
              ( mod ᵒᵖ (is-a-cov-i===0 flip_i))
              ( fib (first A) (first B) f b)
              ( is-a-cov-fib
                  ( first A) ( first B)
                  ( second A) ( second B)
                  ( f) ( b)))

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
#def is-prop-is-a-cov (A : U)
  : is-prop (is-a-cov A)
  := ?is-prop-is-a-cov

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

-- data at the zero corner: base map c : I^m → Γ′ plus fiber of F0.
-- Γ′ is now the U-level product of the I^n n shape-type and the interval
-- shape-type (the cube layer must not depend on term-level types).
#def orthogonality-pullback-fiber
  ( n m : nat)
  ( F0 : product (I^n n) (shape (_ : 𝕀 | TOP)) → S)
  : U
  :=
    Σ ( c : I^n m → product (I^n n) (shape (_ : 𝕀 | TOP)))
    , first (F0 (c (zero-vec-I^n m)))

-- (I^m → F̃) ≃ orthogonality-pullback-fiber , for any m and F0
#def orthogonality-pullback-fwd
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

#def orthogonality-pullback
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

-- same fiber after splitting c ↦ (v , theta) by choice
#def orthogonality-pullback-split
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

#def equiv-orthogonality-pullback-split
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

#def orthogonality-pullback-flat-commute
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
    flat-sigma2-commute
      ( I^n m → I^n n)
      ( I^n m → shape (_ : 𝕀 | TOP))
      ( \ v theta →
          first
            ( F0
                ( v (zero-vec-I^n m)
                , theta (zero-vec-I^n m))))

-- ♭(I^m → F̃) ≃ ♭(orthogonality-pullback-split)
#def equiv-orthogonality-to-flat
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
    flat-equiv
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

#def split-lemma (f g : 𝕀 → S) (a : (i : 𝕀) → first (f i) → first (g i))
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
            ( flat-equiv (I^n n → X) X-cube
                ( equiv-comp (I^n n → X) X-uncurried X-cube
                    ( choice-sigma3 (I^n n) (𝕀 → S) (\ _ → 𝕀 → S)
                        ( \ F G → (i : 𝕀) → first (F i) → first (G i))
                        ( \ F G alpha → product
                            ( is-equiv (first (F 0₂)) (first (G 0₂)) (alpha 0₂))
                            ( is-equiv (first (F 1₂)) (first (G 1₂)) (alpha 1₂))))
                    ( curry-X)))
            ( flat-sigma3-commute (Gamma' → S) (\ _ → Gamma' → S) Hom-in-S E-X) in
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
            ( flat-equiv (I^n n → Y) Y-cube
                ( equiv-comp (I^n n → Y) Y-uncurried Y-cube
                    ( choice-sigma3 (I^n n) (𝕀 → S) (\ _ → 𝕀 → S)
                        ( \ F G → (i : 𝕀) → first (F i) → first (G i))
                        ( \ F G alpha → (theta : 𝕀) → is-equiv (first (F theta)) (first (G theta)) (alpha theta)))
                    ( curry-Y)))
            ( flat-sigma3-commute (Gamma' → S) (\ _ → Gamma' → S) Hom-in-S E-Y) in
        let Y-to-X-split : Equiv Y-split X-split :=
          total-equiv-flat-family3
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
                        let mod ♭ ã : F̃ → G̃ :=
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
 : is-prop (is-equiv F̃ G̃ ã)
                          :=
                            mod ♭ (is-prop-is-equiv funext F̃ G̃ ã) in
                        let mod ♭ to-E-Y : is-equiv F̃ G̃ ã → E-Y F0 G0 a0 :=
                          mod ♭ (first (inv-equiv
                            ( E-Y F0 G0 a0)
                            ( is-equiv F̃ G̃ ã)
                            ( equiv-comp
                                ( E-Y F0 G0 a0)
                                ( fiberwise-is-equiv)
                                ( is-equiv F̃ G̃ ã)
                                ( equiv-identity (E-Y F0 G0 a0))
                                ( equiv-iff-is-prop-is-prop
                                    ( fiberwise-is-equiv)
                                    ( is-equiv F̃ G̃ ã)
                                    ( fiberwise-is-equiv-is-prop)
                                    ( total-is-equiv-is-prop)
                                    ( is-equiv-total-iff-is-equiv-fiberwise
                                        ( Gamma')
                                        ( \ t → first (F0 t))
                                        ( \ t → first (G0 t))
                                        ( \ t → a0 t)))))) in
                        b-map (is-equiv F̃ G̃ ã) (E-Y F0 G0 a0) to-E-Y
                          ( mod ♭ (second (cubes-separate F̃ G̃ ã)
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
                                      ( flat-equiv
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
                                      ( flat-equiv
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
                                    total-equiv-flat-family2
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
                                            flat-equiv
                                              ( first (F0 (vc , form i)))
                                              ( first (G0 (vc , form i)))
                                              ( a0 (vc , form i)
                                              , is-equiv-discrete-I i
                                                  ( \ j → first (F0 (vc , form j)))
                                                  ( \ j → first (G0 (vc , form j)))
                                                  ( \ j → a0 (vc , form j))
                                                  ( first (e0 vc))
                                                  ( second (e0 vc)))) in
                                is-equiv-b-map-via-splits
                                  ( I^n m → F̃) (I^n m → G̃)
                                  ( \ p t → ã (p t))
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
