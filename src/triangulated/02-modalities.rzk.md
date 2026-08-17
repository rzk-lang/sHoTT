# 1. Modalities

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Flat modality

```rzk
#def b-extract (A :♭ U) (x : ♭ A)
  : A
  := let mod ♭ bx := x in bx

#def b-map (A B :♭ U) (f :♭ A → B)
  : ( ♭ A) → (♭ B)
  :=
  \ (x : ♭ A) → let mod ♭ bx := x in mod ♭ (f bx)

#def b-dup (A :♭ U) (x :♭ A)
  : ( ♭ ( ♭ A))
  :=
  mod ♭ (mod ♭ (x))
```

## Opposite modality

```rzk
#def op-map (A B :ᵒᵖ U) (f :ᵒᵖ A → B)
  : ( ᵒᵖ A) → (ᵒᵖ B)
  :=
  \ (x : ᵒᵖ A) → let mod ᵒᵖ op-x := x in mod ᵒᵖ (f op-x)

#def double-op (A : U) (x : (ᵒᵖ (ᵒᵖ A)))
  : A
  :=
  let mod ᵒᵖ x_1 := x in
  let ᵒᵖ mod ᵒᵖ x_2 := x_1 in
  x_2

-- ᵒᵖ ((ᵒᵖ A) → B) → (A → ᵒᵖ B)
-- B must be :ᵒᵖ U, otherwise the left-hand type does not form (B inaccessible under ᵒᵖ).
#def op-fun-op-domain-fwd
  ( A : U)
  ( B :ᵒᵖ U)
  ( f : ᵒᵖ ((ᵒᵖ A) → B))
  ( a : A)
  : ᵒᵖ B
  :=
    let mod ᵒᵖ f0 := f in
      mod ᵒᵖ (f0 (mod ᵒᵖ a))

-- (A → ᵒᵖ B) → ᵒᵖ ((ᵒᵖ A) → B)
-- reverse via _id/ᵒᵖ and ᵒᵖ/ᵒᵖ eliminators
#def op-fun-op-domain-bwd
  ( A : U)
  ( B :ᵒᵖ U)
  ( g : A → ᵒᵖ B)
  : ᵒᵖ ((ᵒᵖ A) → B)
  :=
    mod ᵒᵖ (\ (x : ᵒᵖ A) →
      let mod ᵒᵖ a := x in
      let ᵒᵖ mod ᵒᵖ b := g a in
        b)

-- ᵒᵖ ((ᵒᵖ A) → B) ≃ (A → ᵒᵖ B)
#def equiv-op-fun-op-domain
  ( A : U)
  ( B :ᵒᵖ U)
  : Equiv (ᵒᵖ ((ᵒᵖ A) → B)) (A → ᵒᵖ B)
  :=
    equiv-has-inverse
      ( ᵒᵖ ((ᵒᵖ A) → B))
      ( A → ᵒᵖ B)
      ( op-fun-op-domain-fwd A B)
      ( op-fun-op-domain-bwd A B)
      ( \ _ → refl)
      ( \ _ → refl)

-- (3) Modal Π, forward: ᵒᵖ (Π x. B x) → ((x : ᵒᵖ A) → ᵒᵖ (B x))
#def op-Π-fwd
  ( A :ᵒᵖ U)
  ( B :ᵒᵖ A → U)
  ( f : ᵒᵖ ((x : A) → B x))
  : (x : ᵒᵖ A) → (let mod ᵒᵖ a := x in ᵒᵖ (B a))
  :=
    \ x →
      let mod ᵒᵖ a := x in
      let mod ᵒᵖ f0 := f in
        mod ᵒᵖ (f0 a)

-- (5) Σ under op, both directions
#def op-Σ-fwd
  ( A :ᵒᵖ U)
  ( B :ᵒᵖ A → U)
  ( w : ᵒᵖ (Σ (a : A) , B a))
  : Σ ( a' : ᵒᵖ A) , (let mod ᵒᵖ a := a' in ᵒᵖ (B a))
  :=
    let mod ᵒᵖ (a , b) := w in
      ( mod ᵒᵖ a , mod ᵒᵖ b)

#def op-Σ-bwd
  ( A :ᵒᵖ U)
  ( B :ᵒᵖ A → U)
  ( w : Σ ( a' : ᵒᵖ A) , (let mod ᵒᵖ a := a' in ᵒᵖ (B a)))
  : ᵒᵖ (Σ (a : A) , B a)
  :=
    let (a' , b') := w in
    let mod ᵒᵖ a := a' in
    let mod ᵒᵖ b := b' in
      mod ᵒᵖ (a , b)

-- ᵒᵖ (I → C) as a modal Π over (s : ᵒᵖ I)
#def op-fun-as-modal-Π
  ( C :ᵒᵖ (i : 𝕀) → U)
  ( f : ᵒᵖ ((i : 𝕀) → C i))
  : (s : ᵒᵖ 𝕀) → (let mod ᵒᵖ i := s in ᵒᵖ (C i))
  :=
    \ s →
      let mod ᵒᵖ i := s in
      let mod ᵒᵖ f0 := f in
        mod ᵒᵖ (f0 i)

-- Axiom 2 bridge: modal Π over ᵒᵖ I  ≃  (i:I) → ᵒᵖ (C (¬i))
#def modal-Π-to-flipped
  ( C :ᵒᵖ (i : 𝕀) → U)
  ( g : (s : ᵒᵖ 𝕀) → (let mod ᵒᵖ i := s in ᵒᵖ (C i)))
  : (i : 𝕀) → (let mod ᵒᵖ j := flipᵒᵖ i in ᵒᵖ (C j))
  :=
    \ i → g (flipᵒᵖ i)

#def flipped-to-modal-Π
  ( C :ᵒᵖ (i : 𝕀) → U)
  ( k : (i : 𝕀) → (let mod ᵒᵖ j := flipᵒᵖ i in ᵒᵖ (C j)))
  : (s : ᵒᵖ 𝕀) → (let mod ᵒᵖ i := s in ᵒᵖ (C i))
  :=
    \ s → k (unflipᵒᵖ s)

-- Analog of equiv-op-fun-op-domain for Π over I, using I ≃ ᵒᵖ I via flip/unflip:
--   ᵒᵖ ((i : I) → C i) ≃ ((i : I) → ᵒᵖ (C (¬i)))
#def op-fun-I-fwd
  ( C :ᵒᵖ (i : 𝕀) → U)
  ( f : ᵒᵖ ((i : 𝕀) → C i))
  : (i : 𝕀) → (let mod ᵒᵖ j := flipᵒᵖ i in ᵒᵖ (C j))
  :=
    \ i →
      let mod ᵒᵖ f0 := f in
      let mod ᵒᵖ j := flipᵒᵖ i in
        mod ᵒᵖ (f0 j)

#def op-fun-I-bwd
  ( C :ᵒᵖ (i : 𝕀) → U)
  ( k : (i : 𝕀) → (let mod ᵒᵖ j := flipᵒᵖ i in ᵒᵖ (C j)))
  : ᵒᵖ ((i : 𝕀) → C i)
  :=
    mod ᵒᵖ (\ (i : 𝕀) →
      let ᵒᵖ mod ᵒᵖ b := k (unflipᵒᵖ (mod ᵒᵖ i)) in
        b)

#def equiv-op-fun-I
  ( C :ᵒᵖ (i : 𝕀) → U)
  : Equiv
      ( ᵒᵖ ((i : 𝕀) → C i))
      ( (i : 𝕀) → (let mod ᵒᵖ j := flipᵒᵖ i in ᵒᵖ (C j)))
  :=
    equiv-has-inverse
      ( ᵒᵖ ((i : 𝕀) → C i))
      ( (i : 𝕀) → (let mod ᵒᵖ j := flipᵒᵖ i in ᵒᵖ (C j)))
      ( op-fun-I-fwd C)
      ( op-fun-I-bwd C)
      ( \ _ → refl)
      ( \ _ → refl)

-- Non-dependent special case: ᵒᵖ (I → B) ≃ (I → ᵒᵖ B)
#def op-fun-I-const-fwd
  ( B :ᵒᵖ U)
  ( f : ᵒᵖ (𝕀 → B))
  : (i : 𝕀) → ᵒᵖ B
  :=
    \ i →
      let mod ᵒᵖ f0 := f in
      let mod ᵒᵖ i' := flipᵒᵖ i in
        mod ᵒᵖ (f0 i')

#def op-fun-I-const-bwd
  ( B :ᵒᵖ U)
  ( g : (i : 𝕀) → ᵒᵖ B)
  : ᵒᵖ (𝕀 → B)
  :=
    mod ᵒᵖ (\ (i : 𝕀) →
      let ᵒᵖ mod ᵒᵖ b := g (unflipᵒᵖ (mod ᵒᵖ i)) in
        b)

#def equiv-op-fun-I-const
  ( B :ᵒᵖ U)
  : Equiv (ᵒᵖ (𝕀 → B)) ((i : 𝕀) → ᵒᵖ B)
  :=
    equiv-has-inverse
      ( ᵒᵖ (𝕀 → B))
      ( (i : 𝕀) → ᵒᵖ B)
      ( op-fun-I-const-fwd B)
      ( op-fun-I-const-bwd B)
      ( \ _ → refl)
      ( \ _ → refl)

-- Alias kept for earlier call sites
#def op-fun-I-to-flipped
  ( C :ᵒᵖ (i : 𝕀) → U)
  ( f : ᵒᵖ ((i : 𝕀) → C i))
  : (i : 𝕀) → (let mod ᵒᵖ j := flipᵒᵖ i in ᵒᵖ (C j))
  :=
    op-fun-I-fwd C f
```

## Sharp modality

```rzk
#def sharp-pure (A : U) (x : A)
  : ( ♯ A)
  := mod ♯ x

#def sharp-map (A B : U) (f : A → B)
  : ( ♯ A) → (♯ B)
  :=
  \ (x : ♯ A) → let mod ♯ sx := x in mod ♯ (f sx)

#def sharp-join (A : U) (a : (♯ (♯ A)))
  : ( ♯ A)
  :=
  let mod ♯ x_1 := a in
  let ♯ mod ♯ x_2 := x_1 in
  mod ♯ (x_2)
```

## Useful modal aliases

```rzk
#def U-b
  : ( ♭ U)
  := mod ♭ U

#def Prop-b
  : ( ♭ U)
  := mod ♭ Prop

#def univ-family-Prop-b
  : ( ♭ U)
  := mod ♭ univ-family-Prop

#def Unit-b
  : ( ♭ U)
  := mod ♭ Unit

#def b-extract-eq (A :♭ U) (x y : ♭ A)

  ( p : x = y)
  : b-extract A x = b-extract A y
  := ap (♭ A) A x y (b-extract A) p

#def flat-convoy
  ( A :♭ U)
  ( C : ♭ A → U)
  ( t : ♭ A)
  ( d : (x :_b A) → (mod ♭ x =_{♭ A} t) → C (mod ♭ x))
  : C t
  := ( let mod ♭ x := t into (\ (z : ♭ A) → (z =_{♭ A} t) → C z) in (\ (e : mod ♭ x =_{♭ A} t) → d x e)) refl

#def flat-flat-convoy
  ( A :♭ U)
  ( C : ♭ A → U)
  ( t :_b ♭ A)
  ( d : (x :_b A) → (♭ (mod ♭ x =_{♭ A} t)) → C (mod ♭ x))
  : C t
  := ( let ♭ mod ♭ x := t
         into (\ (z :_b ♭ A) → (♭ (z =_{♭ A} t)) → C z)
       in (\ (e : ♭ (mod ♭ x =_{♭ A} t)) → d x e))
     ( mod ♭ refl)

#def flat-beta (Q R :♭ U) (K :♭ Q → R) (a :♭ Q)
  : (let mod ♭ x := mod ♭ a in mod ♭ (K x)) =_{♭ R} mod ♭ (K a)
  := let mod ♭ x := mod ♭ a into (\ (z : ♭ Q) → (let mod ♭ y := z in mod ♭ (K y)) =_{♭ R} mod ♭ (K a)) in refl

#def flat-naturality (P Q R :♭ U)
  ( F :♭ (♭ Q) → (♭ R))
  ( G :♭ P → Q)
  ( w : ♭ P)
  : F (let mod ♭ x := w in mod ♭ (G x)) =_{♭ R} (let mod ♭ x := w in F (mod ♭ (G x)))
  := flat-convoy
       ( P)
       ( \ (z : ♭ P) → F (let mod ♭ y := z in mod ♭ (G y)) = (let mod ♭ y := z in F (mod ♭ (G y))))
       ( w)
       ( \ (x :_b P) → \ (e : mod ♭ x =_{♭ P} w) → refl)

#def flat-let-commute (P :♭ U) (D : U) (H : P → D) (w : ♭ P)
  : (let mod ♭ x := w in H x) =_{D} H (b-extract P w)
  := flat-convoy
       ( P)
       ( \ (z : ♭ P) → (let mod ♭ y := z in H y) = H (b-extract P z))
       ( w)
       ( \ (x :_b P) → \ (e : mod ♭ x =_{♭ P} w) → refl)

#def flat-sigma-commute (C :♭ U) (D :♭ C → U)
  : Equiv
      ( ♭ (Σ (c : C) , D c))
      ( Σ (c : ♭ C) , (let mod ♭ c0 := c in ♭ (D c0)))
  :=
    let fwd : ♭ (Σ (c : C) , D c) → (Σ (c : ♭ C) , (let mod ♭ c0 := c in ♭ (D c0)))
      := \ w → let mod ♭ (c , d) := w in (mod ♭ c , mod ♭ d) in
    let bwd : (Σ (c : ♭ C) , (let mod ♭ c0 := c in ♭ (D c0))) → ♭ (Σ (c : C) , D c)
      := \ (c' , d') →
          flat-convoy C
            (\ z → (let mod ♭ c0 := z in ♭ (D c0)) → ♭ (Σ (c : C) , D c))
            c'
            (\ (c :_b C) → \ _ → \ d'' →
              let mod ♭ d := d'' in
              mod ♭ (c , d))
            d' in
    equiv-has-inverse
      ( ♭ (Σ (c : C) , D c))
      ( Σ (c : ♭ C) , (let mod ♭ c0 := c in ♭ (D c0)))
      ( fwd)
      ( bwd)
      ( \ w →
          flat-convoy (Σ (c : C) , D c)
            (\ z → bwd (fwd z) = z)
            w
            (\ (p :_b (Σ (c : C) , D c)) → \ _ → refl))
      ( \ z →
          let c' := first z in
          let d' := second z in
          flat-convoy C
            (\ z' → (d'' : let mod ♭ c0 := z' in ♭ (D c0)) →
              fwd (bwd (z' , d'')) = (z' , d''))
            c'
            (\ (c :_b C) → \ _ → \ d'' →
              flat-convoy (D c)
                (\ dflat → fwd (bwd (mod ♭ c , dflat)) = (mod ♭ c , dflat))
                d''
                (\ (d :_b D c) → \ _ → refl))
            d')

#def flat-sigma2-commute
  ( A B :♭ U)
  ( C :♭ A → B → U)
  : Equiv
    ( ♭ (Σ (a : A) , Σ (b : B) , C a b))
    ( Σ (a : ♭ A)
    , ( let mod ♭ a0 := a in
        Σ (b : ♭ B)
        , ( let mod ♭ b0 := b in ♭ (C a0 b0))))
  :=
    let RHS : U
      := Σ (a : ♭ A)
         , ( let mod ♭ a0 := a in
             Σ (b : ♭ B)
             , ( let mod ♭ b0 := b in ♭ (C a0 b0))) in
    let fwd :
      ♭ (Σ (a : A) , Σ (b : B) , C a b) → RHS
      := \ w →
          let mod ♭ (a , (b , c)) := w in
          ( mod ♭ a , (mod ♭ b , mod ♭ c)) in
    let bwd :
      RHS → ♭ (Σ (a : A) , Σ (b : B) , C a b)
      := \ (a' , rest) →
          flat-convoy A
            (\ a →
              ( let mod ♭ a0 := a in
                Σ (b : ♭ B)
                , ( let mod ♭ b0 := b in ♭ (C a0 b0)))
              → ♭ (Σ (x : A) , Σ (y : B) , C x y))
            a'
            (\ (a :_b A) → \ _ → \ (b' , c') →
              flat-convoy B
                (\ b →
                  ( let mod ♭ b0 := b in ♭ (C a b0))
                  → ♭ (Σ (x : A) , Σ (y : B) , C x y))
                b'
                (\ (b :_b B) → \ _ → \ c'' →
                  let mod ♭ c := c'' in
                  mod ♭ (a , (b , c)))
                c')
            rest in
    equiv-has-inverse
      ( ♭ (Σ (a : A) , Σ (b : B) , C a b))
      ( RHS)
      ( fwd)
      ( bwd)
      ( \ w →
          flat-convoy (Σ (a : A) , Σ (b : B) , C a b)
            (\ z → bwd (fwd z) = z)
            w
            (\ (p :_b (Σ (a : A) , Σ (b : B) , C a b)) → \ _ → refl))
      ( \ z →
          flat-convoy A
            (\ a' →
              ( rest :
                let mod ♭ a0 := a' in
                Σ (b : ♭ B)
                , ( let mod ♭ b0 := b in ♭ (C a0 b0)))
              → fwd (bwd (a' , rest)) = (a' , rest))
            ( first z)
            (\ (a :_b A) → \ _ → \ rest →
              flat-convoy B
                (\ b' →
                  ( c' : let mod ♭ b0 := b' in ♭ (C a b0))
                  → fwd (bwd (mod ♭ a , (b' , c'))) = (mod ♭ a , (b' , c')))
                ( first rest)
                (\ (b :_b B) → \ _ → \ c' →
                  flat-convoy (C a b)
                    (\ cflat →
                      fwd (bwd (mod ♭ a , (mod ♭ b , cflat)))
                      = (mod ♭ a , (mod ♭ b , cflat)))
                    c'
                    (\ (c :_b C a b) → \ _ → refl))
                ( second rest))
            ( second z))

#def flat-sigma3-commute
  ( A :♭ U)
  ( B :♭ A → U)
  ( C :♭ (a : A) → B a → U)
  ( D :♭ (a : A) → (b : B a) → C a b → U)
  : Equiv
    ( ♭ (Σ (a : A) , Σ (b : B a) , Σ (c : C a b) , D a b c))
    ( Σ (a : ♭ A)
    , ( let mod ♭ a0 := a in
        Σ (b : ♭ (B a0))
        , ( let mod ♭ b0 := b in
            Σ (c : ♭ (C a0 b0))
            , ( let mod ♭ c0 := c in ♭ (D a0 b0 c0)))))
  :=
    let RHS : U
      := Σ (a : ♭ A)
         , ( let mod ♭ a0 := a in
             Σ (b : ♭ (B a0))
             , ( let mod ♭ b0 := b in
                 Σ (c : ♭ (C a0 b0))
                 , ( let mod ♭ c0 := c in ♭ (D a0 b0 c0)))) in
    let fwd :
      ♭ (Σ (a : A) , Σ (b : B a) , Σ (c : C a b) , D a b c) → RHS
      := \ w →
          let mod ♭ (a , (b , (c , d))) := w in
          ( mod ♭ a , (mod ♭ b , (mod ♭ c , mod ♭ d))) in
    let bwd :
      RHS → ♭ (Σ (a : A) , Σ (b : B a) , Σ (c : C a b) , D a b c)
      := \ (a' , rest) →
          flat-convoy A
            (\ a →
              ( let mod ♭ a0 := a in
                Σ (b : ♭ (B a0))
                , ( let mod ♭ b0 := b in
                    Σ (c : ♭ (C a0 b0))
                    , ( let mod ♭ c0 := c in ♭ (D a0 b0 c0))))
              → ♭ (Σ (x : A) , Σ (b : B x) , Σ (c : C x b) , D x b c))
            a'
            (\ (a :_b A) → \ _ → \ (b' , rest2) →
              flat-convoy (B a)
                (\ b →
                  ( let mod ♭ b0 := b in
                    Σ (c : ♭ (C a b0))
                    , ( let mod ♭ c0 := c in ♭ (D a b0 c0)))
                  → ♭ (Σ (x : A) , Σ (y : B x) , Σ (c : C x y) , D x y c))
                b'
                (\ (b :_b B a) → \ _ → \ (c' , d') →
                  flat-convoy (C a b)
                    (\ c →
                      ( let mod ♭ c0 := c in ♭ (D a b c0))
                      → ♭ (Σ (x : A) , Σ (y : B x) , Σ (z : C x y) , D x y z))
                    c'
                    (\ (c :_b C a b) → \ _ → \ d' →
                      let mod ♭ d := d' in
                      mod ♭ (a , (b , (c , d))))
                    d')
                rest2)
            rest in
    equiv-has-inverse
      ( ♭ (Σ (a : A) , Σ (b : B a) , Σ (c : C a b) , D a b c))
      ( RHS)
      ( fwd)
      ( bwd)
      ( \ w →
          flat-convoy (Σ (a : A) , Σ (b : B a) , Σ (c : C a b) , D a b c)
            (\ z → bwd (fwd z) = z)
            w
            (\ (p :_b (Σ (a : A) , Σ (b : B a) , Σ (c : C a b) , D a b c)) → \ _ → refl))
      ( \ z →
          flat-convoy A
            (\ a' →
              ( rest :
                let mod ♭ a0 := a' in
                Σ (b : ♭ (B a0))
                , ( let mod ♭ b0 := b in
                    Σ (c : ♭ (C a0 b0))
                    , ( let mod ♭ c0 := c in ♭ (D a0 b0 c0))))
              → fwd (bwd (a' , rest)) = (a' , rest))
            ( first z)
            (\ (a :_b A) → \ _ → \ rest →
              flat-convoy (B a)
                (\ b' →
                  ( rest2 :
                    let mod ♭ b0 := b' in
                    Σ (c : ♭ (C a b0))
                    , ( let mod ♭ c0 := c in ♭ (D a b0 c0)))
                  → fwd (bwd (mod ♭ a , (b' , rest2))) = (mod ♭ a , (b' , rest2)))
                ( first rest)
                (\ (b :_b B a) → \ _ → \ rest2 →
                  flat-convoy (C a b)
                    (\ c' →
                      ( d' : let mod ♭ c0 := c' in ♭ (D a b c0))
                      → fwd (bwd (mod ♭ a , (mod ♭ b , (c' , d'))))
                        = (mod ♭ a , (mod ♭ b , (c' , d'))))
                    ( first rest2)
                    (\ (c :_b C a b) → \ _ → \ d' →
                      flat-convoy (D a b c)
                        (\ dflat →
                          fwd (bwd (mod ♭ a , (mod ♭ b , (mod ♭ c , dflat))))
                          = (mod ♭ a , (mod ♭ b , (mod ♭ c , dflat))))
                        d'
                        (\ (d :_b D a b c) → \ _ → refl))
                    ( second rest2))
                ( second rest))
            ( second z))
```
