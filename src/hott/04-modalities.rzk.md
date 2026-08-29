# 4. Modalities

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Prerequisites

- `hott/01-paths.rzk.md` — `ap`.
- `hott/03-equivalences.rzk.md` — `Equiv`, `is-equiv`, `equiv-has-inverse`, `is-equiv-Equiv-is-equiv`.

## Flat

### Basics

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

### Elimination

```rzk
#def b-elim
  ( A :♭ U)
  ( C : ♭ A → U)
  ( t : ♭ A)
  ( d : (x :_b A) → (mod ♭ x =_{♭ A} t) → C (mod ♭ x))
  : C t
  := ( let mod ♭ x := t into (\ (z : ♭ A) → (z =_{♭ A} t) → C z) in (\ (e : mod ♭ x =_{♭ A} t) → d x e)) refl

#def b-b-elim
  ( A :♭ U)
  ( C : ♭ A → U)
  ( t :_b ♭ A)
  ( d : (x :_b A) → (♭ (mod ♭ x =_{♭ A} t)) → C (mod ♭ x))
  : C t
  := ( let ♭ mod ♭ x := t
         into (\ (z :_b ♭ A) → (♭ (z =_{♭ A} t)) → C z)
       in (\ (e : ♭ (mod ♭ x =_{♭ A} t)) → d x e))
     ( mod ♭ refl)

#def b-extract-eq (A :♭ U) (x y : ♭ A)

  ( p : x = y)
  : b-extract A x = b-extract A y
  := ap (♭ A) A x y (b-extract A) p

#def b-beta (Q R :♭ U) (K :♭ Q → R) (a :♭ Q)
  : (let mod ♭ x := mod ♭ a in mod ♭ (K x)) =_{♭ R} mod ♭ (K a)
  := let mod ♭ x := mod ♭ a into (\ (z : ♭ Q) → (let mod ♭ y := z in mod ♭ (K y)) =_{♭ R} mod ♭ (K a)) in refl

#def b-naturality (P Q R :♭ U)
  ( F :♭ (♭ Q) → (♭ R))
  ( G :♭ P → Q)
  ( w : ♭ P)
  : F (let mod ♭ x := w in mod ♭ (G x)) =_{♭ R} (let mod ♭ x := w in F (mod ♭ (G x)))
  := b-elim
       ( P)
       ( \ (z : ♭ P) → F (let mod ♭ y := z in mod ♭ (G y)) = (let mod ♭ y := z in F (mod ♭ (G y))))
       ( w)
       ( \ (x :_b P) → \ (e : mod ♭ x =_{♭ P} w) → refl)

#def b-let-commute (P :♭ U) (D : U) (H : P → D) (w : ♭ P)
  : (let mod ♭ x := w in H x) =_{D} H (b-extract P w)
  := b-elim
       ( P)
       ( \ (z : ♭ P) → (let mod ♭ y := z in H y) = H (b-extract P z))
       ( w)
       ( \ (x :_b P) → \ (e : mod ♭ x =_{♭ P} w) → refl)
```

### Interval

```rzk
#def discrete-interval-elim (i :♭ 𝕀) (A : 𝕀 → U) (x : A 0ᵢ) (y : A 1ᵢ)
  : A i
  :=
  recOR(
    ( i ≡ 0ᵢ) ↦ x
  , ( i ≡ 1ᵢ) ↦ y)

#def is-equiv-discrete-interval-elim
  ( i :♭ 𝕀)
  ( A B : 𝕀 → U)
  ( f : (j : 𝕀) → A j → B j)
  ( e0 : is-equiv (A 0ᵢ) (B 0ᵢ) (f 0ᵢ))
  ( e1 : is-equiv (A 1ᵢ) (B 1ᵢ) (f 1ᵢ))
  : is-equiv (A i) (B i) (f i)
  :=
  discrete-interval-elim i
    ( \ j → is-equiv (A j) (B j) (f j))
    ( e0)
    ( e1)

#def equiv-shape-I-bool
  : Equiv (shape (_ : (_b 𝕀) | TOP)) Bool
  :=
    equiv-has-inverse
      ( shape (_ : (_b 𝕀) | TOP))
      Bool
      ( \ p → let mod _b i := unform p in discrete-interval-elim i (\ _ → Bool) false true)
      ( \ b → match b (false ⇒ form (mod _b 0ᵢ) | true ⇒ form (mod _b 1ᵢ)))
      ( \ p →
          let mod _b i := unform p
            into
              ( \ (z : (_b 𝕀)) →
                  match (let mod _b j := z in discrete-interval-elim j (\ _ → Bool) false true)
                    ( false ⇒ form (mod _b 0ᵢ)
                    | true ⇒ form (mod _b 1ᵢ))
                  =_{shape (_ : (_b 𝕀) | TOP)} form z)
          in
            recOR(
              ( i ≡ 0ᵢ) ↦ refl
            , ( i ≡ 1ᵢ) ↦ refl))
      ( \ b → match b (false ⇒ refl | true ⇒ refl))
```

### Path

```rzk
#postulate b-path-commute-fwd (A :♭ U) (x y :♭ A)
  : ( ♭ ( x = y)) → (mod ♭ x) = (mod ♭ y)

#postulate b-path-commute-bwd (A :♭ U) (x y :♭ A)
  : ( ( mod ♭ x) = (mod ♭ y)) → (♭ (x = y))

#postulate b-path-commute-section (A :♭ U) (x y :♭ A)
  ( p : (♭ (x = y)))
  : b-path-commute-bwd A x y (b-path-commute-fwd A x y p) = p

#postulate b-path-commute-retraction (A :♭ U) (x y :♭ A)
  ( p : (mod ♭ x) = (mod ♭ y))
  : b-path-commute-fwd A x y (b-path-commute-bwd A x y p) = p

#def b-path-commute-equiv (A :♭ U) (x y :♭ A)
  : is-equiv
    ( ♭ ( x = y))
    ( ( mod ♭ x) = (mod ♭ y))
    ( b-path-commute-fwd A x y)
  :=
  ( ( b-path-commute-bwd A x y
    , b-path-commute-section A x y)
  , ( b-path-commute-bwd A x y
    , b-path-commute-retraction A x y))
```

### Crisp equivalences

Lifting equivalences through the flat (`♭`) modality.

```rzk
#def b-equiv (A B :♭ U) (e :♭ Equiv A B)
  : Equiv (♭ A) (♭ B)
  :=
    ( b-map A B (first e)
    , ( ( b-map B A (first (first (second e)))
        , \ x →
            b-elim A
              (\ z → b-map B A (first (first (second e))) (b-map A B (first e) z) = z) x
              (\ (a :_b A) → \ _ →
                b-path-commute-fwd A
                  ( first (first (second e)) (first e a))
                  a
                  ( mod ♭ (second (first (second e)) a))))
      , ( b-map B A (first (second (second e)))
        , \ y →
            b-elim B
              (\ z → b-map A B (first e) (b-map B A (first (second (second e))) z) = z) y
              (\ (b :_b B) → \ _ →
                b-path-commute-fwd B
                  ( first e (first (second (second e)) b))
                  b
                  ( mod ♭ (second (second (second e)) b))))))

#def is-equiv-b-map-via-splits
  ( A' A :♭ U)
  ( f :_b A' → A)
  ( B' B : U)
  ( eA' : Equiv (♭ A') B')
  ( eA : Equiv (♭ A) B)
  ( eB : Equiv B' B)
  ( η : (a :_b A') →
      first eB (first eA' (mod ♭ a))
      = first eA (b-map A' A f (mod ♭ a)))
  : is-equiv (♭ A') (♭ A) (b-map A' A f)
  :=
    is-equiv-Equiv-is-equiv
      ( ♭ A') ( ♭ A) ( b-map A' A f)
      ( B') ( B) ( first eB)
      ( ( ( first eA' , first eA)
        , \ w →
            b-elim A'
              ( \ z →
                  first eB (first eA' z)
                  = first eA (b-map A' A f z))
              w
              ( \ (a :_b A') → \ _ → η a))
      , ( second eA' , second eA))
      ( second eB)
```

### Sigma

```rzk
#def b-sigma-commute-fwd (C :♭ U) (D :♭ C → U)
  : ♭ (Σ (c : C) , D c) → (Σ (c : ♭ C) , (let mod ♭ c0 := c in ♭ (D c0)))
  := \ w → let mod ♭ (c , d) := w in (mod ♭ c , mod ♭ d)

#def b-sigma-commute-bwd (C :♭ U) (D :♭ C → U)
  : (Σ (c : ♭ C) , (let mod ♭ c0 := c in ♭ (D c0))) → ♭ (Σ (c : C) , D c)
  := \ (c' , d') →
      b-elim C
        (\ z → (let mod ♭ c0 := z in ♭ (D c0)) → ♭ (Σ (c : C) , D c))
        c'
        (\ (c :_b C) → \ _ → \ d'' →
          let mod ♭ d := d'' in
          mod ♭ (c , d))
        d'

#def b-sigma-commute-equiv (C :♭ U) (D :♭ C → U)
  : Equiv
      ( ♭ (Σ (c : C) , D c))
      ( Σ (c : ♭ C) , (let mod ♭ c0 := c in ♭ (D c0)))
  :=
    equiv-has-inverse
      ( ♭ (Σ (c : C) , D c))
      ( Σ (c : ♭ C) , (let mod ♭ c0 := c in ♭ (D c0)))
      ( b-sigma-commute-fwd C D)
      ( b-sigma-commute-bwd C D)
      ( \ w →
          b-elim (Σ (c : C) , D c)
            (\ z → b-sigma-commute-bwd C D (b-sigma-commute-fwd C D z) = z)
            w
            (\ (p :_b (Σ (c : C) , D c)) → \ _ → refl))
      ( \ z →
          let c' := first z in
          let d' := second z in
          b-elim C
            (\ z' → (d'' : let mod ♭ c0 := z' in ♭ (D c0)) →
              b-sigma-commute-fwd C D (b-sigma-commute-bwd C D (z' , d'')) = (z' , d''))
            c'
            (\ (c :_b C) → \ _ → \ d'' →
              b-elim (D c)
                (\ dflat →
                  b-sigma-commute-fwd C D (b-sigma-commute-bwd C D (mod ♭ c , dflat))
                  = (mod ♭ c , dflat))
                d''
                (\ (d :_b D c) → \ _ → refl))
            d')

#def b-sigma2-commute-fwd
  ( A B :♭ U)
  ( C :♭ A → B → U)
  : ♭ (Σ (a : A) , Σ (b : B) , C a b)
  → Σ (a : ♭ A)
    , ( let mod ♭ a0 := a in
        Σ (b : ♭ B)
        , ( let mod ♭ b0 := b in ♭ (C a0 b0)))
  := \ w →
      let mod ♭ (a , (b , c)) := w in
      ( mod ♭ a , (mod ♭ b , mod ♭ c))

#def b-sigma2-commute-bwd
  ( A B :♭ U)
  ( C :♭ A → B → U)
  : ( Σ (a : ♭ A)
    , ( let mod ♭ a0 := a in
        Σ (b : ♭ B)
        , ( let mod ♭ b0 := b in ♭ (C a0 b0))))
  → ♭ (Σ (a : A) , Σ (b : B) , C a b)
  := \ (a' , rest) →
      b-elim A
        (\ a →
          ( let mod ♭ a0 := a in
            Σ (b : ♭ B)
            , ( let mod ♭ b0 := b in ♭ (C a0 b0)))
          → ♭ (Σ (x : A) , Σ (y : B) , C x y))
        a'
        (\ (a :_b A) → \ _ → \ (b' , c') →
          b-elim B
            (\ b →
              ( let mod ♭ b0 := b in ♭ (C a b0))
              → ♭ (Σ (x : A) , Σ (y : B) , C x y))
            b'
            (\ (b :_b B) → \ _ → \ c'' →
              let mod ♭ c := c'' in
              mod ♭ (a , (b , c)))
            c')
        rest

#def b-sigma2-commute-equiv
  ( A B :♭ U)
  ( C :♭ A → B → U)
  : Equiv
    ( ♭ (Σ (a : A) , Σ (b : B) , C a b))
    ( Σ (a : ♭ A)
    , ( let mod ♭ a0 := a in
        Σ (b : ♭ B)
        , ( let mod ♭ b0 := b in ♭ (C a0 b0))))
  :=
    equiv-has-inverse
      ( ♭ (Σ (a : A) , Σ (b : B) , C a b))
      ( Σ (a : ♭ A)
        , ( let mod ♭ a0 := a in
            Σ (b : ♭ B)
            , ( let mod ♭ b0 := b in ♭ (C a0 b0))))
      ( b-sigma2-commute-fwd A B C)
      ( b-sigma2-commute-bwd A B C)
      ( \ w →
          b-elim (Σ (a : A) , Σ (b : B) , C a b)
            (\ z → b-sigma2-commute-bwd A B C (b-sigma2-commute-fwd A B C z) = z)
            w
            (\ (p :_b (Σ (a : A) , Σ (b : B) , C a b)) → \ _ → refl))
      ( \ z →
          b-elim A
            (\ a' →
              ( rest :
                let mod ♭ a0 := a' in
                Σ (b : ♭ B)
                , ( let mod ♭ b0 := b in ♭ (C a0 b0)))
              → b-sigma2-commute-fwd A B C (b-sigma2-commute-bwd A B C (a' , rest)) = (a' , rest))
            ( first z)
            (\ (a :_b A) → \ _ → \ rest →
              b-elim B
                (\ b' →
                  ( c' : let mod ♭ b0 := b' in ♭ (C a b0))
                  → b-sigma2-commute-fwd A B C (b-sigma2-commute-bwd A B C (mod ♭ a , (b' , c')))
                    = (mod ♭ a , (b' , c')))
                ( first rest)
                (\ (b :_b B) → \ _ → \ c' →
                  b-elim (C a b)
                    (\ cflat →
                      b-sigma2-commute-fwd A B C
                        (b-sigma2-commute-bwd A B C (mod ♭ a , (mod ♭ b , cflat)))
                      = (mod ♭ a , (mod ♭ b , cflat)))
                    c'
                    (\ (c :_b C a b) → \ _ → refl))
                ( second rest))
            ( second z))

#def b-sigma3-commute-fwd
  ( A :♭ U)
  ( B :♭ A → U)
  ( C :♭ (a : A) → B a → U)
  ( D :♭ (a : A) → (b : B a) → C a b → U)
  : ♭ (Σ (a : A) , Σ (b : B a) , Σ (c : C a b) , D a b c)
  → Σ (a : ♭ A)
    , ( let mod ♭ a0 := a in
        Σ (b : ♭ (B a0))
        , ( let mod ♭ b0 := b in
            Σ (c : ♭ (C a0 b0))
            , ( let mod ♭ c0 := c in ♭ (D a0 b0 c0))))
  := \ w →
      let mod ♭ (a , (b , (c , d))) := w in
      ( mod ♭ a , (mod ♭ b , (mod ♭ c , mod ♭ d)))

#def b-sigma3-commute-bwd
  ( A :♭ U)
  ( B :♭ A → U)
  ( C :♭ (a : A) → B a → U)
  ( D :♭ (a : A) → (b : B a) → C a b → U)
  : ( Σ (a : ♭ A)
    , ( let mod ♭ a0 := a in
        Σ (b : ♭ (B a0))
        , ( let mod ♭ b0 := b in
            Σ (c : ♭ (C a0 b0))
            , ( let mod ♭ c0 := c in ♭ (D a0 b0 c0)))))
  → ♭ (Σ (a : A) , Σ (b : B a) , Σ (c : C a b) , D a b c)
  := \ (a' , rest) →
      b-elim A
        (\ a →
          ( let mod ♭ a0 := a in
            Σ (b : ♭ (B a0))
            , ( let mod ♭ b0 := b in
                Σ (c : ♭ (C a0 b0))
                , ( let mod ♭ c0 := c in ♭ (D a0 b0 c0))))
          → ♭ (Σ (x : A) , Σ (b : B x) , Σ (c : C x b) , D x b c))
        a'
        (\ (a :_b A) → \ _ → \ (b' , rest2) →
          b-elim (B a)
            (\ b →
              ( let mod ♭ b0 := b in
                Σ (c : ♭ (C a b0))
                , ( let mod ♭ c0 := c in ♭ (D a b0 c0)))
              → ♭ (Σ (x : A) , Σ (y : B x) , Σ (c : C x y) , D x y c))
            b'
            (\ (b :_b B a) → \ _ → \ (c' , d') →
              b-elim (C a b)
                (\ c →
                  ( let mod ♭ c0 := c in ♭ (D a b c0))
                  → ♭ (Σ (x : A) , Σ (y : B x) , Σ (z : C x y) , D x y z))
                c'
                (\ (c :_b C a b) → \ _ → \ d' →
                  let mod ♭ d := d' in
                  mod ♭ (a , (b , (c , d))))
                d')
            rest2)
        rest

#def b-sigma3-commute-equiv
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
    equiv-has-inverse
      ( ♭ (Σ (a : A) , Σ (b : B a) , Σ (c : C a b) , D a b c))
      ( Σ (a : ♭ A)
        , ( let mod ♭ a0 := a in
            Σ (b : ♭ (B a0))
            , ( let mod ♭ b0 := b in
                Σ (c : ♭ (C a0 b0))
                , ( let mod ♭ c0 := c in ♭ (D a0 b0 c0)))))
      ( b-sigma3-commute-fwd A B C D)
      ( b-sigma3-commute-bwd A B C D)
      ( \ w →
          b-elim (Σ (a : A) , Σ (b : B a) , Σ (c : C a b) , D a b c)
            (\ z → b-sigma3-commute-bwd A B C D (b-sigma3-commute-fwd A B C D z) = z)
            w
            (\ (p :_b (Σ (a : A) , Σ (b : B a) , Σ (c : C a b) , D a b c)) → \ _ → refl))
      ( \ z →
          b-elim A
            (\ a' →
              ( rest :
                let mod ♭ a0 := a' in
                Σ (b : ♭ (B a0))
                , ( let mod ♭ b0 := b in
                    Σ (c : ♭ (C a0 b0))
                    , ( let mod ♭ c0 := c in ♭ (D a0 b0 c0))))
              → b-sigma3-commute-fwd A B C D (b-sigma3-commute-bwd A B C D (a' , rest)) = (a' , rest))
            ( first z)
            (\ (a :_b A) → \ _ → \ rest →
              b-elim (B a)
                (\ b' →
                  ( rest2 :
                    let mod ♭ b0 := b' in
                    Σ (c : ♭ (C a b0))
                    , ( let mod ♭ c0 := c in ♭ (D a b0 c0)))
                  → b-sigma3-commute-fwd A B C D
                      (b-sigma3-commute-bwd A B C D (mod ♭ a , (b' , rest2)))
                    = (mod ♭ a , (b' , rest2)))
                ( first rest)
                (\ (b :_b B a) → \ _ → \ rest2 →
                  b-elim (C a b)
                    (\ c' →
                      ( d' : let mod ♭ c0 := c' in ♭ (D a b c0))
                      → b-sigma3-commute-fwd A B C D
                          (b-sigma3-commute-bwd A B C D (mod ♭ a , (mod ♭ b , (c' , d'))))
                        = (mod ♭ a , (mod ♭ b , (c' , d'))))
                    ( first rest2)
                    (\ (c :_b C a b) → \ _ → \ d' →
                      b-elim (D a b c)
                        (\ dflat →
                          b-sigma3-commute-fwd A B C D
                            (b-sigma3-commute-bwd A B C D (mod ♭ a , (mod ♭ b , (mod ♭ c , dflat))))
                          = (mod ♭ a , (mod ♭ b , (mod ♭ c , dflat))))
                        d'
                        (\ (d :_b D a b c) → \ _ → refl))
                    ( second rest2))
                ( second rest))
            ( second z))
```

### Aliases

```rzk
#def U-b
  : ( ♭ U)
  := mod ♭ U

#def Unit-b
  : ( ♭ U)
  := mod ♭ Unit
```

## Opposite

### Basics

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
```

### Path

```rzk
#postulate op-path-commute-fwd (A :ᵒᵖ U) (x y :ᵒᵖ A)
  : ( ᵒᵖ (x = y)) → (mod ᵒᵖ x) = (mod ᵒᵖ y)

#postulate op-path-commute-bwd (A :ᵒᵖ U) (x y :ᵒᵖ A)
  : ( ( mod ᵒᵖ x) = (mod ᵒᵖ y)) → (ᵒᵖ (x = y))

#postulate op-path-commute-section (A :ᵒᵖ U) (x y :ᵒᵖ A)
  ( p : (ᵒᵖ (x = y)))
  : op-path-commute-bwd A x y (op-path-commute-fwd A x y p) = p

#postulate op-path-commute-retraction (A :ᵒᵖ U) (x y :ᵒᵖ A)
  ( p : (mod ᵒᵖ x) = (mod ᵒᵖ y))
  : op-path-commute-fwd A x y (op-path-commute-bwd A x y p) = p

#def op-path-commute-equiv (A :ᵒᵖ U) (x y :ᵒᵖ A)
  : is-equiv
    ( ᵒᵖ (x = y))
    ( ( mod ᵒᵖ x) = (mod ᵒᵖ y))
    ( op-path-commute-fwd A x y)
  :=
  ( ( op-path-commute-bwd A x y
    , op-path-commute-section A x y)
  , ( op-path-commute-bwd A x y
    , op-path-commute-retraction A x y))
```

### Sigma

```rzk
#def op-sigma-commute-fwd
  ( A :ᵒᵖ U)
  ( B :ᵒᵖ A → U)
  ( w : ᵒᵖ (Σ (a : A) , B a))
  : Σ ( a' : ᵒᵖ A) , (let mod ᵒᵖ a := a' in ᵒᵖ (B a))
  :=
    let mod ᵒᵖ (a , b) := w in
      ( mod ᵒᵖ a , mod ᵒᵖ b)

#def op-sigma-commute-bwd
  ( A :ᵒᵖ U)
  ( B :ᵒᵖ A → U)
  ( w : Σ ( a' : ᵒᵖ A) , (let mod ᵒᵖ a := a' in ᵒᵖ (B a)))
  : ᵒᵖ (Σ (a : A) , B a)
  :=
    let (a' , b') := w in
    let mod ᵒᵖ a := a' in
    let mod ᵒᵖ b := b' in
      mod ᵒᵖ (a , b)

#def op-sigma-commute-equiv
  ( A :ᵒᵖ U)
  ( B :ᵒᵖ A → U)
  : Equiv
      ( ᵒᵖ (Σ (a : A) , B a))
      ( Σ (a : ᵒᵖ A) , (let mod ᵒᵖ a := a in ᵒᵖ (B a)))
  :=
    equiv-has-inverse
      ( ᵒᵖ (Σ (a : A) , B a))
      ( Σ (a : ᵒᵖ A) , (let mod ᵒᵖ a := a in ᵒᵖ (B a)))
      ( op-sigma-commute-fwd A B)
      ( op-sigma-commute-bwd A B)
      ( \ _ → refl)
      ( \ _ → refl)

#def op-sigma2-commute-fwd
  ( A B :ᵒᵖ U)
  ( C :ᵒᵖ A → B → U)
  ( w : ᵒᵖ (Σ (a : A) , Σ (b : B) , C a b))
  : Σ ( a : ᵒᵖ A)
    , ( let mod ᵒᵖ a0 := a in
        Σ (b : ᵒᵖ B)
        , ( let mod ᵒᵖ b0 := b in ᵒᵖ (C a0 b0)))
  :=
    let mod ᵒᵖ (a , (b , c)) := w in
      ( mod ᵒᵖ a , (mod ᵒᵖ b , mod ᵒᵖ c))

#def op-sigma2-commute-bwd
  ( A B :ᵒᵖ U)
  ( C :ᵒᵖ A → B → U)
  ( w : Σ ( a : ᵒᵖ A)
        , ( let mod ᵒᵖ a0 := a in
            Σ (b : ᵒᵖ B)
            , ( let mod ᵒᵖ b0 := b in ᵒᵖ (C a0 b0))))
  : ᵒᵖ (Σ (a : A) , Σ (b : B) , C a b)
  :=
    let (a' , (b' , c')) := w in
    let mod ᵒᵖ a := a' in
    let mod ᵒᵖ b := b' in
    let mod ᵒᵖ c := c' in
      mod ᵒᵖ (a , (b , c))

#def op-sigma2-commute-equiv
  ( A B :ᵒᵖ U)
  ( C :ᵒᵖ A → B → U)
  : Equiv
      ( ᵒᵖ (Σ (a : A) , Σ (b : B) , C a b))
      ( Σ ( a : ᵒᵖ A)
        , ( let mod ᵒᵖ a0 := a in
            Σ (b : ᵒᵖ B)
            , ( let mod ᵒᵖ b0 := b in ᵒᵖ (C a0 b0))))
  :=
    equiv-has-inverse
      ( ᵒᵖ (Σ (a : A) , Σ (b : B) , C a b))
      ( Σ ( a : ᵒᵖ A)
        , ( let mod ᵒᵖ a0 := a in
            Σ (b : ᵒᵖ B)
            , ( let mod ᵒᵖ b0 := b in ᵒᵖ (C a0 b0))))
      ( op-sigma2-commute-fwd A B C)
      ( op-sigma2-commute-bwd A B C)
      ( \ _ → refl)
      ( \ _ → refl)

#def op-sigma3-commute-fwd
  ( A :ᵒᵖ U)
  ( B :ᵒᵖ A → U)
  ( C :ᵒᵖ ((a : A) → B a → U))
  ( D :ᵒᵖ ((a : A) → (b : B a) → C a b → U))
  ( w : ᵒᵖ (Σ (a : A) , Σ (b : B a) , Σ (c : C a b) , D a b c))
  : Σ ( a : ᵒᵖ A)
    , ( let mod ᵒᵖ a0 := a in
        Σ (b : ᵒᵖ (B a0))
        , ( let mod ᵒᵖ b0 := b in
            Σ (c : ᵒᵖ (C a0 b0))
            , ( let mod ᵒᵖ c0 := c in ᵒᵖ (D a0 b0 c0))))
  :=
    let mod ᵒᵖ (a , (b , (c , d))) := w in
      ( mod ᵒᵖ a , (mod ᵒᵖ b , (mod ᵒᵖ c , mod ᵒᵖ d)))

#def op-sigma3-commute-bwd
  ( A :ᵒᵖ U)
  ( B :ᵒᵖ A → U)
  ( C :ᵒᵖ ((a : A) → B a → U))
  ( D :ᵒᵖ ((a : A) → (b : B a) → C a b → U))
  ( w : Σ ( a : ᵒᵖ A)
        , ( let mod ᵒᵖ a0 := a in
            Σ (b : ᵒᵖ (B a0))
            , ( let mod ᵒᵖ b0 := b in
                Σ (c : ᵒᵖ (C a0 b0))
                , ( let mod ᵒᵖ c0 := c in ᵒᵖ (D a0 b0 c0)))))
  : ᵒᵖ (Σ (a : A) , Σ (b : B a) , Σ (c : C a b) , D a b c)
  :=
    let (a' , (b' , (c' , d'))) := w in
    let mod ᵒᵖ a := a' in
    let mod ᵒᵖ b := b' in
    let mod ᵒᵖ c := c' in
    let mod ᵒᵖ d := d' in
      mod ᵒᵖ (a , (b , (c , d)))

#def op-sigma3-commute-equiv
  ( A :ᵒᵖ U)
  ( B :ᵒᵖ A → U)
  ( C :ᵒᵖ ((a : A) → B a → U))
  ( D :ᵒᵖ ((a : A) → (b : B a) → C a b → U))
  : Equiv
      ( ᵒᵖ (Σ (a : A) , Σ (b : B a) , Σ (c : C a b) , D a b c))
      ( Σ ( a : ᵒᵖ A)
        , ( let mod ᵒᵖ a0 := a in
            Σ (b : ᵒᵖ (B a0))
            , ( let mod ᵒᵖ b0 := b in
                Σ (c : ᵒᵖ (C a0 b0))
                , ( let mod ᵒᵖ c0 := c in ᵒᵖ (D a0 b0 c0)))))
  :=
    equiv-has-inverse
      ( ᵒᵖ (Σ (a : A) , Σ (b : B a) , Σ (c : C a b) , D a b c))
      ( Σ ( a : ᵒᵖ A)
        , ( let mod ᵒᵖ a0 := a in
            Σ (b : ᵒᵖ (B a0))
            , ( let mod ᵒᵖ b0 := b in
                Σ (c : ᵒᵖ (C a0 b0))
                , ( let mod ᵒᵖ c0 := c in ᵒᵖ (D a0 b0 c0)))))
      ( op-sigma3-commute-fwd A B C D)
      ( op-sigma3-commute-bwd A B C D)
      ( \ _ → refl)
      ( \ _ → refl)
```

### Op functions

```rzk
#def op-fun-commute-fwd
  ( A :ᵒᵖ U)
  ( B :ᵒᵖ A → U)
  ( f : ᵒᵖ ((x : A) → B x))
  : (x : ᵒᵖ A) → (let mod ᵒᵖ a := x in ᵒᵖ (B a))
  :=
    \ x →
      let mod ᵒᵖ a := x in
      let mod ᵒᵖ f0 := f in
        mod ᵒᵖ (f0 a)

#def op-fun-commute-bwd
  ( A :ᵒᵖ U)
  ( B :ᵒᵖ A → U)
  ( g : (x : ᵒᵖ A) → (let mod ᵒᵖ a := x in ᵒᵖ (B a)))
  : ᵒᵖ ((x : A) → B x)
  :=
    mod ᵒᵖ (\ (a : A) →
      let ᵒᵖ mod ᵒᵖ b := g (mod ᵒᵖ a) in
        b)

#def op-fun-commute-equiv
  ( A :ᵒᵖ U)
  ( B :ᵒᵖ A → U)
  : Equiv
      ( ᵒᵖ ((x : A) → B x))
      ( (x : ᵒᵖ A) → (let mod ᵒᵖ a := x in ᵒᵖ (B a)))
  :=
    equiv-has-inverse
      ( ᵒᵖ ((x : A) → B x))
      ( (x : ᵒᵖ A) → (let mod ᵒᵖ a := x in ᵒᵖ (B a)))
      ( op-fun-commute-fwd A B)
      ( op-fun-commute-bwd A B)
      ( \ _ → refl)
      ( \ _ → refl)

#def op-fun-commute-op-fwd
  ( A : U)
  ( B :ᵒᵖ U)
  ( f : ᵒᵖ ((ᵒᵖ A) → B))
  ( a : A)
  : ᵒᵖ B
  :=
    let mod ᵒᵖ f0 := f in
      mod ᵒᵖ (f0 (mod ᵒᵖ a))

#def op-fun-commute-op-bwd
  ( A : U)
  ( B :ᵒᵖ U)
  ( g : A → ᵒᵖ B)
  : ᵒᵖ ((ᵒᵖ A) → B)
  :=
    mod ᵒᵖ (\ (x : ᵒᵖ A) →
      let mod ᵒᵖ a := x in
      let ᵒᵖ mod ᵒᵖ b := g a in
        b)

#def op-fun-commute-op-equiv
  ( A : U)
  ( B :ᵒᵖ U)
  : Equiv (ᵒᵖ ((ᵒᵖ A) → B)) (A → ᵒᵖ B)
  :=
    equiv-has-inverse
      ( ᵒᵖ ((ᵒᵖ A) → B))
      ( A → ᵒᵖ B)
      ( op-fun-commute-op-fwd A B)
      ( op-fun-commute-op-bwd A B)
      ( \ _ → refl)
      ( \ _ → refl)

#def op-ext-commute-fwd
  ( C :ᵒᵖ ((i : 𝕀) → U))
  ( f : ᵒᵖ ((i : 𝕀) → C i))
  : (i : 𝕀) → (let mod ᵒᵖ j := flipᵒᵖ i in ᵒᵖ (C j))
  :=
    \ i →
      let mod ᵒᵖ f0 := f in
      let mod ᵒᵖ j := flipᵒᵖ i in
        mod ᵒᵖ (f0 j)

#def op-ext-commute-bwd
  ( C :ᵒᵖ ((i : 𝕀) → U))
  ( k : (i : 𝕀) → (let mod ᵒᵖ j := flipᵒᵖ i in ᵒᵖ (C j)))
  : ᵒᵖ ((i : 𝕀) → C i)
  :=
    mod ᵒᵖ (\ (i : 𝕀) →
      let ᵒᵖ mod ᵒᵖ b := k (unflipᵒᵖ (mod ᵒᵖ i)) in
        b)

#def op-ext-commute-equiv
  ( C :ᵒᵖ ((i : 𝕀) → U))
  : Equiv
      ( ᵒᵖ ((i : 𝕀) → C i))
      ( (i : 𝕀) → (let mod ᵒᵖ j := flipᵒᵖ i in ᵒᵖ (C j)))
  :=
    equiv-has-inverse
      ( ᵒᵖ ((i : 𝕀) → C i))
      ( (i : 𝕀) → (let mod ᵒᵖ j := flipᵒᵖ i in ᵒᵖ (C j)))
      ( op-ext-commute-fwd C)
      ( op-ext-commute-bwd C)
      ( \ _ → refl)
      ( \ _ → refl)
```

## Sharp

### Basics

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

### Path

```rzk
#postulate sharp-path-commute-fwd (A :♯ U) (x y :♯ A)
  : ( ♯ ( x = y)) → (mod ♯ x) = (mod ♯ y)

#postulate sharp-path-commute-bwd (A :♯ U) (x y :♯ A)
  : ( ( mod ♯ x) = (mod ♯ y)) → (♯ (x = y))

#postulate sharp-path-commute-section (A :♯ U) (x y :♯ A)
  ( p : (♯ (x = y)))
  : sharp-path-commute-bwd A x y (sharp-path-commute-fwd A x y p) = p

#postulate sharp-path-commute-retraction (A :♯ U) (x y :♯ A)
  ( p : (mod ♯ x) = (mod ♯ y))
  : sharp-path-commute-fwd A x y (sharp-path-commute-bwd A x y p) = p

#def sharp-path-commute-equiv (A :♯ U) (x y :♯ A)
  : is-equiv
    ( ♯ ( x = y))
    ( ( mod ♯ x) = (mod ♯ y))
    ( sharp-path-commute-fwd A x y)
  :=
  ( ( sharp-path-commute-bwd A x y
    , sharp-path-commute-section A x y)
  , ( sharp-path-commute-bwd A x y
    , sharp-path-commute-retraction A x y))
```

### Sigma

```rzk
#def sharp-sigma-commute-fwd
  ( A :♯ U)
  ( B :♯ A → U)
  ( w : ♯ (Σ (a : A) , B a))
  : Σ ( a' : ♯ A) , (let mod ♯ a := a' in ♯ (B a))
  :=
    let mod ♯ (a , b) := w in
      ( mod ♯ a , mod ♯ b)

#def sharp-sigma-commute-bwd
  ( A :♯ U)
  ( B :♯ A → U)
  ( w : Σ ( a' : ♯ A) , (let mod ♯ a := a' in ♯ (B a)))
  : ♯ (Σ (a : A) , B a)
  :=
    let (a' , b') := w in
    let mod ♯ a := a' in
    let mod ♯ b := b' in
      mod ♯ (a , b)

#def sharp-sigma-commute-equiv
  ( A :♯ U)
  ( B :♯ A → U)
  : Equiv
      ( ♯ (Σ (a : A) , B a))
      ( Σ (a : ♯ A) , (let mod ♯ a := a in ♯ (B a)))
  :=
    equiv-has-inverse
      ( ♯ (Σ (a : A) , B a))
      ( Σ (a : ♯ A) , (let mod ♯ a := a in ♯ (B a)))
      ( sharp-sigma-commute-fwd A B)
      ( sharp-sigma-commute-bwd A B)
      ( \ _ → refl)
      ( \ _ → refl)

#def sharp-sigma2-commute-fwd
  ( A B :♯ U)
  ( C :♯ A → B → U)
  ( w : ♯ (Σ (a : A) , Σ (b : B) , C a b))
  : Σ ( a : ♯ A)
    , ( let mod ♯ a0 := a in
        Σ (b : ♯ B)
        , ( let mod ♯ b0 := b in ♯ (C a0 b0)))
  :=
    let mod ♯ (a , (b , c)) := w in
      ( mod ♯ a , (mod ♯ b , mod ♯ c))

#def sharp-sigma2-commute-bwd
  ( A B :♯ U)
  ( C :♯ A → B → U)
  ( w : Σ ( a : ♯ A)
        , ( let mod ♯ a0 := a in
            Σ (b : ♯ B)
            , ( let mod ♯ b0 := b in ♯ (C a0 b0))))
  : ♯ (Σ (a : A) , Σ (b : B) , C a b)
  :=
    let (a' , (b' , c')) := w in
    let mod ♯ a := a' in
    let mod ♯ b := b' in
    let mod ♯ c := c' in
      mod ♯ (a , (b , c))

#def sharp-sigma2-commute-equiv
  ( A B :♯ U)
  ( C :♯ A → B → U)
  : Equiv
      ( ♯ (Σ (a : A) , Σ (b : B) , C a b))
      ( Σ ( a : ♯ A)
        , ( let mod ♯ a0 := a in
            Σ (b : ♯ B)
            , ( let mod ♯ b0 := b in ♯ (C a0 b0))))
  :=
    equiv-has-inverse
      ( ♯ (Σ (a : A) , Σ (b : B) , C a b))
      ( Σ ( a : ♯ A)
        , ( let mod ♯ a0 := a in
            Σ (b : ♯ B)
            , ( let mod ♯ b0 := b in ♯ (C a0 b0))))
      ( sharp-sigma2-commute-fwd A B C)
      ( sharp-sigma2-commute-bwd A B C)
      ( \ _ → refl)
      ( \ _ → refl)

#def sharp-sigma3-commute-fwd
  ( A :♯ U)
  ( B :♯ A → U)
  ( C :♯ ((a : A) → B a → U))
  ( D :♯ ((a : A) → (b : B a) → C a b → U))
  ( w : ♯ (Σ (a : A) , Σ (b : B a) , Σ (c : C a b) , D a b c))
  : Σ ( a : ♯ A)
    , ( let mod ♯ a0 := a in
        Σ (b : ♯ (B a0))
        , ( let mod ♯ b0 := b in
            Σ (c : ♯ (C a0 b0))
            , ( let mod ♯ c0 := c in ♯ (D a0 b0 c0))))
  :=
    let mod ♯ (a , (b , (c , d))) := w in
      ( mod ♯ a , (mod ♯ b , (mod ♯ c , mod ♯ d)))

#def sharp-sigma3-commute-bwd
  ( A :♯ U)
  ( B :♯ A → U)
  ( C :♯ ((a : A) → B a → U))
  ( D :♯ ((a : A) → (b : B a) → C a b → U))
  ( w : Σ ( a : ♯ A)
        , ( let mod ♯ a0 := a in
            Σ (b : ♯ (B a0))
            , ( let mod ♯ b0 := b in
                Σ (c : ♯ (C a0 b0))
                , ( let mod ♯ c0 := c in ♯ (D a0 b0 c0)))))
  : ♯ (Σ (a : A) , Σ (b : B a) , Σ (c : C a b) , D a b c)
  :=
    let (a' , (b' , (c' , d'))) := w in
    let mod ♯ a := a' in
    let mod ♯ b := b' in
    let mod ♯ c := c' in
    let mod ♯ d := d' in
      mod ♯ (a , (b , (c , d)))

#def sharp-sigma3-commute-equiv
  ( A :♯ U)
  ( B :♯ A → U)
  ( C :♯ ((a : A) → B a → U))
  ( D :♯ ((a : A) → (b : B a) → C a b → U))
  : Equiv
      ( ♯ (Σ (a : A) , Σ (b : B a) , Σ (c : C a b) , D a b c))
      ( Σ ( a : ♯ A)
        , ( let mod ♯ a0 := a in
            Σ (b : ♯ (B a0))
            , ( let mod ♯ b0 := b in
                Σ (c : ♯ (C a0 b0))
                , ( let mod ♯ c0 := c in ♯ (D a0 b0 c0)))))
  :=
    equiv-has-inverse
      ( ♯ (Σ (a : A) , Σ (b : B a) , Σ (c : C a b) , D a b c))
      ( Σ ( a : ♯ A)
        , ( let mod ♯ a0 := a in
            Σ (b : ♯ (B a0))
            , ( let mod ♯ b0 := b in
                Σ (c : ♯ (C a0 b0))
                , ( let mod ♯ c0 := c in ♯ (D a0 b0 c0)))))
      ( sharp-sigma3-commute-fwd A B C D)
      ( sharp-sigma3-commute-bwd A B C D)
      ( \ _ → refl)
      ( \ _ → refl)
```
