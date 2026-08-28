# 3. Cubical (ordinary) covariance

```rzk
#lang rzk-1
```

## Ordinary covariance over 𝕀

```rzk title="RS17 Def 8.2, cubical"
#def is-covariant-II
  ( A : U)
  ( C : A → U)
  : U
  :=
    ( x : A) → (y : A) → (f : hom-II A x y) → (u : C x)
  → is-contr (dhom-from-II A x y f C u)
```

```rzk
#def covariant-transport-II
  ( A : U)
  ( x y : A)
  ( f : hom-II A x y)
  ( C : A → U)
  ( cov : is-covariant-II A C)
  ( u : C x)
  : C y
  := first (center-contraction (dhom-from-II A x y f C u) (cov x y f u))

#def covariant-lift-II
  ( A : U)
  ( x y : A)
  ( f : hom-II A x y)
  ( C : A → U)
  ( cov : is-covariant-II A C)
  ( u : C x)
  : dhom-II A x y f C u (covariant-transport-II A x y f C cov u)
  := second (center-contraction (dhom-from-II A x y f C u) (cov x y f u))

#def covariant-uniqueness-II
  ( A : U)
  ( x y : A)
  ( f : hom-II A x y)
  ( C : A → U)
  ( cov : is-covariant-II A C)
  ( u : C x)
  ( lift : dhom-from-II A x y f C u)
  : covariant-transport-II A x y f C cov u = first lift
  :=
    first-path-Σ
      ( C y)
      ( \ v → dhom-II A x y f C u v)
      ( center-contraction (dhom-from-II A x y f C u) (cov x y f u))
      ( lift)
      ( homotopy-contraction (dhom-from-II A x y f C u) (cov x y f u) lift)

#def id-arr-covariant-transport-II
  ( A : U)
  ( x : A)
  ( C : A → U)
  ( cov : is-covariant-II A C)
  ( u : C x)
  : covariant-transport-II A x x (\ _ → x) C cov u = u
  := covariant-uniqueness-II A x x (\ _ → x) C cov u (u , \ _ → u)

#def is-covariant-II-substitution
  ( A B : U)
  ( C : A → U)
  ( cov : is-covariant-II A C)
  ( g : B → A)
  : is-covariant-II B (\ b → C (g b))
  := \ x y f u → cov (g x) (g y) (\ t → g (f t)) u
```

## Covariance is a proposition

```rzk
#def is-prop-is-covariant-II uses (weakfunext funext)
  ( A : U)
  ( C : A → U)
  : is-prop (is-covariant-II A C)
  :=
    is-prop-fiberwise-prop4 funext A
      ( \ _ → A)
      ( \ x y → hom-II A x y)
      ( \ x _ _ → C x)
      ( \ x y f u → is-contr (dhom-from-II A x y f C u))
      ( \ x y f u → is-prop-is-contr-itself weakfunext (dhom-from-II A x y f C u))

#def is-covariant-II-Prop uses (weakfunext funext)
  ( A : U)
  ( C : A → U)
  : Prop
  := (is-covariant-II A C , is-prop-is-covariant-II A C)
```

## Transport along a line in the interval

```rzk
#def is-covariant-arrow-II
  ( C : (t : 𝕀 | TOP) → U)
  : U
  := is-covariant-II (shape (_ : 𝕀 | TOP)) (\ (s : shape (_ : 𝕀 | TOP)) → C (unform s))

#def covariant-transport-line-II
  ( C : (t : 𝕀 | TOP) → U)
  ( cov : is-covariant-arrow-II C)
  ( l : 𝕀 → shape (_ : 𝕀 | TOP))
  : C (unform (l 0₂)) → C (unform (l 1₂))
  :=
    \ u →
      covariant-transport-II
        ( shape (_ : 𝕀 | TOP))
        ( l 0₂) ( l 1₂)
        ( \ (t : 𝕀) → l t)
        ( \ (s : shape (_ : 𝕀 | TOP)) → C (unform s))
        cov u

#def covariant-transport-line-const-II
  ( C : (t : 𝕀 | TOP) → U)
  ( cov : is-covariant-arrow-II C)
  ( j : shape (_ : 𝕀 | TOP))
  ( u : C (unform j))
  : covariant-transport-line-II C cov (\ _ → j) u = u
  := id-arr-covariant-transport-II (shape (_ : 𝕀 | TOP)) j (\ s → C (unform s)) cov u

#def covariant-transport-line-const-at-0-II
  ( C : (t : 𝕀 | TOP) → U)
  ( cov : is-covariant-arrow-II C)
  ( u : C 0₂)
  : covariant-transport-line-II C cov (\ k → form (inf 0₂ k)) u = u
  := id-arr-covariant-transport-II (shape (_ : 𝕀 | TOP)) (form 0₂) (\ s → C (unform s)) cov u

#def covariant-transport-line-const-0-sup-II
  ( C : (t : 𝕀 | TOP) → U)
  ( cov : is-covariant-arrow-II C)
  ( j : 𝕀)
  ( u : C 0₂)
  : covariant-transport-line-II C cov (\ k → form (inf 0₂ (sup j k))) u = u
  := id-arr-covariant-transport-II (shape (_ : 𝕀 | TOP)) (form 0₂) (\ s → C (unform s)) cov u

#def covariant-transport-line-const-1-sup-II
  ( C : (t : 𝕀 | TOP) → U)
  ( cov : is-covariant-arrow-II C)
  ( i : 𝕀)
  ( u : C i)
  : covariant-transport-line-II C cov (\ k → form (inf i (sup 1₂ k))) u = u
  := id-arr-covariant-transport-II (shape (_ : 𝕀 | TOP)) (form i) (\ s → C (unform s)) cov u
```

## The extension theorem

```rzk
#def covariant-transport-line-inv-II
  ( packed : ᵒᵖ (𝕀 → U))
  ( cov
    : let mod ᵒᵖ C0 := packed in
        ᵒᵖ (is-covariant-arrow-II (\ (t : 𝕀 | TOP) → C0 t)))
  ( l : 𝕀 → shape (_ : 𝕀 | TOP))
  : ( let mod ᵒᵖ p := packed in
      let mod ᵒᵖ j₁ := flip_op (unform (l 1₂)) in
      let mod ᵒᵖ j₀ := flip_op (unform (l 0₂)) in
      ᵒᵖ (p j₁) → ᵒᵖ (p j₀))
  :=
    \ x →
      let F : (k : 𝕀) → ᵒᵖ U
        :=
          \ (k : 𝕀) →
            let mod ᵒᵖ p0 := packed in
            let mod ᵒᵖ j : 𝕀 := flip_op (unform (l k)) in
              mod ᵒᵖ (p0 j)
      in
      let lamM : ᵒᵖ (𝕀 → shape (_ : 𝕀 | TOP))
        := op-ext-commute-bwd (\ (_ : 𝕀) → shape (_ : 𝕀 | TOP))
             ( \ (i : 𝕀) →
                 let mod ᵒᵖ j : 𝕀 := flip_op (unform (l i)) in
                   mod ᵒᵖ (form j))
      in
      let mod ᵒᵖ pA := op-ext-commute-bwd (\ (_ : 𝕀) → U) F in
      let mod ᵒᵖ p0 := packed in
      let mod ᵒᵖ cov0 := cov in
      let mod ᵒᵖ lam0 := lamM in
      let mod ᵒᵖ x0 := x in
        mod ᵒᵖ (
          covariant-transport-line-II
            ( \ (t : 𝕀 | TOP) → pA t)
            ( is-covariant-II-substitution
                ( shape (_ : 𝕀 | TOP)) ( shape (_ : 𝕀 | TOP))
                ( \ (s : shape (_ : 𝕀 | TOP)) → p0 (unform s))
                ( cov0)
                ( \ (s : shape (_ : 𝕀 | TOP)) → lam0 (unform s)))
            ( \ k → form k)
            x0)
#def equiv-is-cov-i-coslice
  ( A : 𝕀 → U)
  ( a0 : A 0₂)
  : Equiv
      ( Σ (a1 : A 1₂) , dhom-II (shape (_ : 𝕀 | TOP)) (form 0₂) (form 1₂) (\ t → form t) (\ s → A (unform s)) a0 a1)
      ( Σ (φ : (i : 𝕀) → A i) , φ 0₂ = a0)
  :=
    equiv-has-inverse
      ( Σ (a1 : A 1₂) , dhom-II (shape (_ : 𝕀 | TOP)) (form 0₂) (form 1₂) (\ t → form t) (\ s → A (unform s)) a0 a1)
      ( Σ (φ : (i : 𝕀) → A i) , φ 0₂ = a0)
      ( \ (a1 , h) → (\ t → h t , refl))
      ( \ (φ , p) →
          ( φ 1₂
          , ind-path (A 0₂) (φ 0₂)
              ( \ a0' _ → dhom-II (shape (_ : 𝕀 | TOP)) (form 0₂) (form 1₂) (\ t → form t) (\ s → A (unform s)) a0' (φ 1₂))
              ( \ t → φ t)
              a0 p))
      ( \ (a1 , h) → refl)
      ( \ (φ , p) →
          ind-path (A 0₂) (φ 0₂)
            ( \ a0' p' →
                ( \ t →
                    ind-path (A 0₂) (φ 0₂)
                      ( \ a0'' _ → dhom-II (shape (_ : 𝕀 | TOP)) (form 0₂) (form 1₂) (\ t → form t) (\ s → A (unform s)) a0'' (φ 1₂))
                      ( \ t' → φ t')
                      a0' p' t
                , refl)
                =_{Σ (ψ : (i : 𝕀) → A i) , ψ 0₂ = a0'}
                  (φ , p'))
            ( refl)
            a0 p)



#def is-covariant-arrow-II-coslice
  ( A : 𝕀 → U)
  ( cov : is-covariant-arrow-II A)
  ( a0 : A 0₂)
  : is-contr (Σ (φ : (i : 𝕀) → A i) , φ 0₂ = a0)
  :=
    is-contr-equiv-is-contr
      ( Σ (a1 : A 1₂) , dhom-II (shape (_ : 𝕀 | TOP)) (form 0₂) (form 1₂) (\ t → form t) (\ s → A (unform s)) a0 a1)
      ( Σ (φ : (i : 𝕀) → A i) , φ 0₂ = a0)
      ( equiv-is-cov-i-coslice A a0)
      ( cov (form 0₂) (form 1₂) (\ (t : 𝕀) → form t) a0)

```

## Closure properties

```rzk
#def is-covariant-II-Σ
  ( A : U)
  ( C : A → U)
  ( D : (Σ (a : A) , C a) → U)
  ( cov-C : is-covariant-II A C)
  ( cov-D : is-covariant-II (Σ (a : A) , C a) D)
  : is-covariant-II A (\ a → Σ (c : C a) , D (a , c))
  := ?is-covariant-II-Σ

#def is-covariant-II-Id
  ( A : U)
  ( C : A → U)
  ( cov-C : is-covariant-II A C)
  ( u v : (a : A) → C a)
  : is-covariant-II A (\ a → u a = v a)
  := ?is-covariant-II-Id

#def is-covariant-arrow-II-Σ
  ( A : 𝕀 → U)
  ( B : (i : 𝕀) → A i → U)
  ( cov-a : is-covariant-arrow-II A)
  ( is-cov-B : (s : (t : 𝕀) → A t) → is-covariant-arrow-II (\ t → B t (s t)))
  : is-covariant-arrow-II (\ i → Σ (a : A i) , B i a)
  := ?is-covariant-II-Σ

#def is-covariant-arrow-II-Id
  ( A : 𝕀 → U)
  ( is-cov-A : is-covariant-arrow-II A)
  ( u v : (i : 𝕀) → A i)
  : is-covariant-arrow-II (\ t → u t = v t)
  := ?is-covariant-II-Id

#def is-covariant-ext uses (funext extext)
  ( phi-i : 𝕀 → ᵒᵖ TOPE)
  ( shape-cov
    : let mod ᵒᵖ C0 :=
        op-ext-commute-bwd (\ (_ : 𝕀) → U)
          ( \ i → let mod ᵒᵖ p := phi-i i in mod ᵒᵖ (shape (_ : 1 | p)))
      in ᵒᵖ (is-covariant-arrow-II (\ (t : 𝕀 | TOP) → C0 t)))
  ( D : 𝕀 → U)
  ( cov-D : is-covariant-arrow-II (\ (t : 𝕀 | TOP) → D t))
  ( disc-D : (i : 𝕀) → is-discrete (D i))
  : is-covariant-II
      ( shape (_ : 𝕀 | TOP))
      ( \ (t : shape (_ : 𝕀 | TOP)) → (s : 1 | uninvᵒᵖ (phi-i (unform t))) → D (unform t))
  :=
    \ (x : shape (_ : 𝕀 | TOP)) (y : shape (_ : 𝕀 | TOP))
      (f : hom-II (shape (_ : 𝕀 | TOP)) x y)
      (u : (s : 1 | uninvᵒᵖ (phi-i (unform x))) → D (unform x)) →
    let l : 𝕀 → shape (_ : 𝕀 | TOP) := \ k → f k in
    let cov-D-r
      := is-covariant-II-substitution
           ( shape (_ : 𝕀 | TOP)) ( shape (_ : 𝕀 | TOP))
           ( \ (t : shape (_ : 𝕀 | TOP)) → D (unform t))
           ( cov-D)
           ( \ (t : shape (_ : 𝕀 | TOP)) → l (unform t))
    in
    let disc-D-r := \ (k : 𝕀) → disc-D (unform (l k)) in
    let shape-cov-r
      : let mod ᵒᵖ C0 :=
          op-ext-commute-bwd (\ (_ : 𝕀) → U)
            ( \ i → let mod ᵒᵖ p := phi-i (unform (l i)) in mod ᵒᵖ (shape (_ : 1 | p)))
        in ᵒᵖ (is-covariant-arrow-II (\ (t : 𝕀 | TOP) → C0 t))
      :=
        let lamM : ᵒᵖ (𝕀 → shape (_ : 𝕀 | TOP))
          := op-ext-commute-bwd (\ (_ : 𝕀) → shape (_ : 𝕀 | TOP))
               ( \ (i : 𝕀) → let mod ᵒᵖ j := flip_op (unform (l i)) in mod ᵒᵖ (form j))
        in
        let mod ᵒᵖ C0v :=
          op-ext-commute-bwd (\ (_ : 𝕀) → U)
            ( \ i → let mod ᵒᵖ p := phi-i i in mod ᵒᵖ (shape (_ : 1 | p)))
        in
        let mod ᵒᵖ cov0 := shape-cov in
        let mod ᵒᵖ lam0 := lamM in
          mod ᵒᵖ (is-covariant-II-substitution
                    ( shape (_ : 𝕀 | TOP)) ( shape (_ : 𝕀 | TOP))
                    ( \ (t : shape (_ : 𝕀 | TOP)) → C0v (unform t))
                    ( cov0)
                    ( \ (t : shape (_ : 𝕀 | TOP)) → lam0 (unform t)))
    in
    let phi-i : 𝕀 → ᵒᵖ TOPE := \ k → phi-i (unform (l k)) in
    let D : 𝕀 → U := \ k → D (unform (l k)) in
    let cov-D
      : is-covariant-arrow-II (\ (t : 𝕀 | TOP) → D t)
      := cov-D-r in
    let disc-D : (i : 𝕀) → is-discrete (D i) := disc-D-r in
    let shape-cov
      : let mod ᵒᵖ C0 :=
          op-ext-commute-bwd (\ (_ : 𝕀) → U)
            ( \ i → let mod ᵒᵖ p := phi-i i in mod ᵒᵖ (shape (_ : 1 | p)))
        in ᵒᵖ (is-covariant-arrow-II (\ (t : 𝕀 | TOP) → C0 t))
      := shape-cov-r in
    let C : ᵒᵖ (𝕀 → U)
      :=
        op-ext-commute-bwd (\ (_ : 𝕀) → U)
          ( \ i → let mod ᵒᵖ p := phi-i i in mod ᵒᵖ (shape (_ : 1 | p)))
    in
    let is-cov-C
      : let mod ᵒᵖ C0 := C in
          ᵒᵖ (is-covariant-arrow-II (\ (t : 𝕀 | TOP) → C0 t))
      := shape-cov
    in
    let DS : (t : 𝕀 | TOP) → U
      := \ t → D t
    in
    let E : 𝕀 → U
      := \ i → (t : 1 | uninvᵒᵖ (phi-i i)) → D i
    in
      let f0 : E 0₂ := u in
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
                  covariant-transport-line-inv-II C is-cov-C l (mod ᵒᵖ (form *₁))
              in
              let s0
                := first (equiv-shape-1-op-uninv (phi-i 0₂)) s-op
              in
                covariant-transport-line-II DS cov-D l
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
                      covariant-transport-line-const-at-0-II DS cov-D
                        ( f0
                            ( unform
                                ( first
                                    ( equiv-shape-1-op-uninv (phi-i 0₂))
                                    ( covariant-transport-line-inv-II C is-cov-C
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
                        covariant-transport-line-inv-II C is-cov-C l c
                    in
                    let s-mid
                      := first (equiv-shape-1-op-uninv (phi-i (inf i j))) s-op
                    in
                      covariant-transport-line-II DS cov-D l
                        ( p (inf i j) (unform s-mid))
              in
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
                              covariant-transport-line-const-0-sup-II
                                DS cov-D j
                                ( p 0₂ (unform s))))
              in
              let r
                : (j : 𝕀) → H-sec j 0₂ = f0
                :=
                  \ j →
                    concat (E 0₂) (H-sec j 0₂) (p 0₂) f0 (d j) q
              in
              let pack
                : (j : 𝕀)
                  → Σ (φ : (i : 𝕀) → E i) , φ 0₂ = f0
                := \ j → (H-sec j , r j)
              in
              let is-discrete-E-i
                : (i : 𝕀) → is-discrete (E i)
                :=
                  \ i →
                    is-discrete-extension-type
                      extext
                      ( 1)
                      ( \ _ → uninvᵒᵖ (phi-i i))
                      ( \ _ → D i)
                      ( \ _ → disc-D i)
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
                                  covariant-transport-line-inv-II C is-cov-C l (mod ᵒᵖ (form *₁))
                              in
                              let s0
                                := first (equiv-shape-1-op-uninv (phi-i 0₂)) s-op
                              in
                                covariant-transport-line-II DS cov-D l
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
                                      covariant-transport-line-const-at-0-II DS cov-D
                                        ( f0'
                                            ( unform
                                                ( first
                                                    ( equiv-shape-1-op-uninv (phi-i 0₂))
                                                    ( covariant-transport-line-inv-II C is-cov-C
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
                                  covariant-transport-line-const-1-sup-II
                                    DS cov-D i
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
                            ( ap-ext-eq-htpy-at
                                𝕀
                                ( \ _ → TOP)
                                ( \ _ → BOT)
                                ( \ i → E i)
                                ( \ _ → recBOT)
                                0₂
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
                      transport-section-eq-at-cancel
                        𝕀
                        E
                        0₂
                        f0
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
            ( Σ (f1 : E 1₂) , dhom-II (shape (_ : 𝕀 | TOP)) (form 0₂) (form 1₂) (\ t → form t) (\ s → E (unform s)) f0 f1)
            ( Σ (φ : (i : 𝕀) → E i) , φ 0₂ = f0)
            ( equiv-is-cov-i-coslice E f0)
            ( contr-center , contr-hom)
```
