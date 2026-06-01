# 3. Internal Universe

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

We formalize the internal universe construction following
Licata, Orton, Pitts, and Spitters' "Internal Universes in Models of Homotopy
Type Theory" (arXiv:1801.07664).
## Prerequisites

- `hott/01-paths.rzk.md` — `ap`, `rev`, `concat`, `transport`.
- `hott/03-equivalences.rzk.md` — `Equiv`, `is-equiv`, `UA`.
- `hott/04-half-adjoint-equivalences.rzk.md` — `is-emb-is-equiv`.
- `hott/05-sigma.rzk.md` — `eq-pair`.
- `hott/07-fibers.rzk.md` — `fib`.
- `hott/09-propositions.rzk.md` — `Prop`, `Unit-Prop`, `univ-family-Prop`, `ufp-first-eq-const-Unit`.
- `01-modalities.rzk.md` — Modality operations, `Prop-b`, `univ-family-Prop-b`.
- `02-axioms.rzk.md` — Right adjoint, transpose adjunction, crisp induction.

## Amazing predicate

Given a propositional predicate `pred : (2 → U) → Prop` on arrow types,
the amazing predicate lifts it to a predicate on types
via the right adjoint `rar`.

```rzk

#def univ-family-proj-1_i
  : b-extract U-b (rar univ-family-Prop-b) → b-extract U-b (rar Prop-b)
  :=
    b-extract
      ( mod ♭ (b-extract U-b (rar univ-family-Prop-b) → b-extract U-b (rar Prop-b)))
      ( rar-fmap univ-family-Prop-b Prop-b (mod ♭ (\ x → first x)))

#def univ-family-rar
  : ( b-extract U-b (rar Prop-b)) → U
  :=
  \ b →
    fib
      ( b-extract U-b (rar univ-family-Prop-b))
      ( b-extract U-b (rar Prop-b))
      ( univ-family-proj-1_i)
      ( b)

#def amazing-predicate
  ( pred : ♭ (2 → U) → Prop)
  : U → U
  := \ A →
    let mod ♭ tr_pred :=
      ( ( untranspose-ar Prop-b U-b) (mod ♭ pred))
    in univ-family-rar (tr_pred A)

#def const-Unit-Prop-tr (A : _b U)
  : A → b-extract U-b (rar Prop-b)
  :=
    b-extract
      ( mod ♭ (A → b-extract U-b (rar Prop-b)))
      ( ( untranspose-ar Prop-b (mod _b A)) (mod ♭ (\ h → Unit-Prop)))

#def const-Unit-Prop-ufp-tr
  : b-extract U-b (rar univ-family-Prop-b) → b-extract U-b (rar Prop-b)
  :=
    b-extract
      ( mod ♭ (b-extract U-b (rar univ-family-Prop-b) → b-extract U-b (rar Prop-b)))
      ( ( untranspose-ar Prop-b (rar univ-family-Prop-b)) (mod ♭ (\ h → Unit-Prop)))


#def ufp-proj_1-i-eq-const-Unit-tr
  :
    univ-family-proj-1_i
  = b-extract
      ( mod ♭ (b-extract U-b (rar univ-family-Prop-b) → b-extract U-b (rar Prop-b)))
      ( ( untranspose-ar Prop-b (rar univ-family-Prop-b)) (mod ♭ (\ h → Unit-Prop)))
  :=
    ap
      <| ♭ | univ-family-Prop → Prop |>
      ( b-extract U-b (rar univ-family-Prop-b) → b-extract U-b (rar Prop-b))
      ( mod ♭ (\ x → first x))
      ( mod ♭ (\ x → Unit-Prop))
      ( \ f →
        let mod ♭ fmap := rar-fmap univ-family-Prop-b Prop-b f
        in fmap)
      ( crisp-induction-flat
        ( mod ♭ (univ-family-Prop → Prop))
        ( mod ♭ (\ x → first x))
        ( mod ♭ (\ x → Unit-Prop))
        ( mod ♭ (ufp-first-eq-const-Unit funext weakfunext ua)))

#def pred-tr-eq-ufp-const-Unit
  ( pred : _b (2 → U) → Prop)
  ( A : _b U)
  ( h : _b A → U)
  ( f : _b (a : A) → amazing-predicate (mod _b pred) (h a))
  ( a : A)
  : let mod ♭ tr_pred := (untranspose-ar Prop-b U-b) (mod ♭ pred)
    in ( tr_pred (h a))
    = ( const-Unit-Prop-ufp-tr (first (f a)))
  :=
    let mod ♭ tr_pred := (untranspose-ar Prop-b U-b) (mod ♭ pred)
    in
    concat
      ( b-extract U-b (rar Prop-b))
      ( tr_pred (h a))
      ( univ-family-proj-1_i (first (f a)))
      ( const-Unit-Prop-ufp-tr (first (f a)))
      ( rev (b-extract U-b (rar Prop-b))
        ( univ-family-proj-1_i (first (f a)))
        ( tr_pred (h a))
        ( second (f a)))
      ( htpy-eq
        ( b-extract U-b (rar univ-family-Prop-b))
        ( \ _ → b-extract U-b (rar Prop-b))
        ( univ-family-proj-1_i)
        ( const-Unit-Prop-ufp-tr)
        ( ufp-proj_1-i-eq-const-Unit-tr)
        ( first (f a)))

#def ufp-const-Unit-eq-A-const-Unit
  ( pred : _b (2 → U) → Prop)
  ( A : _b U)
  ( h : _b A → U)
  ( f : _b (a : A) → amazing-predicate (mod _b pred) (h a))
  ( a : A)
  : ( const-Unit-Prop-ufp-tr (first (f a)))
    = ( const-Unit-Prop-tr (mod _b A) a)
  :=
      let lhs-inverse=const-unit
        : ( transpose-ar Prop-b (mod _b A)) (mod ♭ (\ x → const-Unit-Prop-ufp-tr (first (f x))))
        = mod ♭ (\ (_ : 2 → A) → Unit-Prop)
      := transpose-untranspose-comp
           Prop-b (rar univ-family-Prop-b) (mod _b A)
           ( mod ♭ (\ x → first (f x)))
           ( mod ♭ (\ _ → Unit-Prop))
      in
      let rhs-inverse=const-unit
        : ( transpose-ar Prop-b (mod _b A)) (mod ♭ (const-Unit-Prop-tr (mod _b A)))
        = mod ♭ (\ (_ : 2 → A) → Unit-Prop)
      := transpose-untranspose-ar Prop-b (mod _b A)
           ( mod ♭ (\ _ → Unit-Prop))
      in
      let transpose-f=transpose-g
        := concat
            <| ♭ | (2 → A) → Prop |>
            ( ( transpose-ar Prop-b (mod _b A)) (mod ♭ (\ x → const-Unit-Prop-ufp-tr (first (f x)))))
            ( mod ♭ (\ (_ : 2 → A) → Unit-Prop))
            ( ( transpose-ar Prop-b (mod _b A)) (mod ♭ (const-Unit-Prop-tr (mod _b A))))
            lhs-inverse=const-unit
            ( rev <| ♭ | (2 → A) → Prop |>
              ( ( transpose-ar Prop-b (mod _b A)) (mod ♭ (const-Unit-Prop-tr (mod _b A))))
              ( mod ♭ (\ (_ : 2 → A) → Unit-Prop))
              rhs-inverse=const-unit)
      in
      let f=g
        := inv-ap-is-emb
            <| ♭ | A → b-extract U-b (rar Prop-b) |>
            <| ♭ | (2 → A) → Prop |>
            ( transpose-ar Prop-b (mod _b A))
            ( is-emb-is-equiv
              <| ♭ | A → b-extract U-b (rar Prop-b) |>
              <| ♭ | (2 → A) → Prop |>
              ( transpose-ar Prop-b (mod _b A))
              ( transpose-ar-is-equiv Prop-b (mod _b A)))
            ( mod ♭ (\ x → const-Unit-Prop-ufp-tr (first (f x))))
            ( mod ♭ (const-Unit-Prop-tr (mod _b A)))
            transpose-f=transpose-g
      in
      ap
        <| ♭ | A → b-extract U-b (rar Prop-b) |>
        ( b-extract U-b (rar Prop-b))
        ( mod ♭ (\ x → const-Unit-Prop-ufp-tr (first (f x))))
        ( mod ♭ (const-Unit-Prop-tr (mod _b A)))
        ( \ F → let mod ♭ g := F in g a)
        f=g

#def pred-tr-eq-A-const-Unit
  ( pred : _b (2 → U) → Prop)
  ( A : _b U)
  ( h : _b A → U)
  ( f : _b (a : A) → amazing-predicate (mod _b pred) (h a))
  ( a : A)
  : let mod ♭ tr_pred := (untranspose-ar Prop-b U-b) (mod ♭ pred)
    in ( tr_pred (h a))
    = ( const-Unit-Prop-tr (mod _b A) a)
  :=
    let mod ♭ tr_pred := (untranspose-ar Prop-b U-b) (mod ♭ pred)
    in
    concat
      ( b-extract U-b (rar Prop-b))
      ( tr_pred (h a))
      ( const-Unit-Prop-ufp-tr (first (f a)))
      ( const-Unit-Prop-tr (mod _b A) a)
      ( pred-tr-eq-ufp-const-Unit (mod _b pred) (mod _b A) (mod _b h) (mod _b f) a)
      ( ufp-const-Unit-eq-A-const-Unit (mod _b pred) (mod _b A) (mod _b h) (mod _b f) a)
```

## Transposition

`amazing-transpose` converts a `amazing-predicate` into an
arrow predicate.

```rzk

#def amazing-transpose
  ( pred : _b (2 → U) → Prop)
  ( A : _b U)
  ( h : _b A → U)
  ( f : _b (a : A) → amazing-predicate (mod _b pred) (h a))
  : <| _b | ( g : 2 → A) → first (pred (\ b → h (g b))) |>
  :=
    let mod _b tr_pred := untranspose-ar (Prop-b) U-b (mod _b pred) in
    let mod _b f0 := mod _b (\ (a : A) → tr_pred (h a)) in
    let mod _b f1 := mod _b (const-Unit-Prop-tr (mod _b A)) in
    let mod _b A-is-pullback
      :=
        mod _b (\ (a : A) → pred-tr-eq-A-const-Unit (mod _b pred) (mod _b A) (mod _b h) (mod _b f) a)
    in
    let mod _b f0=f1 :=
        mod _b (crisp-induction-flat
          ( mod ♭ (A → b-extract U-b (rar Prop-b)))
          ( mod _b f0) (mod _b f1)
          ( mod ♭ (eq-htpy funext A (\ _ → b-extract U-b (rar Prop-b)) (f0) (f1) (A-is-pullback))))
    in
    let mod _b tr-f0 := (transpose-ar Prop-b (mod _b A) (mod _b f0)) in
    let mod _b tr-f1 := (transpose-ar Prop-b (mod _b A) (mod _b f1)) in
    let mod _b transpose-eq-is-cov :=
        mod _b (b-extract-eq
          ( mod ♭ ((2 → A) → Prop))
          ( transpose-ar Prop-b (mod _b A) (mod _b f0))
          ( mod ♭ (\ (g : 2 → A) → pred (\ b → h (g b))))
          ( transpose-untranspose-comp Prop-b U-b (mod _b A) (mod _b h) (mod _b pred)))
    in
    let mod _b transpose-eq-pure :=
        mod _b (b-extract-eq
          ( mod ♭ ((2 → A) → Prop))
          ( transpose-ar Prop-b (mod _b A) (mod _b f1))
          ( mod ♭ (\ (_ : (2 → A)) → Unit-Prop))
          ( transpose-untranspose-ar Prop-b (mod _b A) (mod ♭ (\ _ → Unit-Prop))))
    in
    let mod _b transposed-eq :=
        mod _b (concat
          ( ( 2 → A) → Prop)
          ( \ g → (pred (\ b → h (g b))))
          ( tr-f0)
          ( \ _ → Unit-Prop)
          ( rev
            ( ( 2 → A) → Prop)
            ( tr-f0)
            ( \ g → (pred (\ b → h (g b))))
            transpose-eq-is-cov)
          ( concat
            ( ( 2 → A) → Prop)
            ( tr-f0)
            ( tr-f1)
            ( \ _ → Unit-Prop)
            ( ap
              ( <| ♭ | A → b-extract U-b (rar Prop-b) |>)
              ( ( 2 → A) → Prop)
              (mod _b f0) (mod _b f1)
              ( \ x → let mod ♭ tr := (transpose-ar Prop-b (mod _b A) x) in tr)
              f0=f1)
            transpose-eq-pure))
    in
    mod _b (\f -> (transport U (\ B → B)
      Unit (first (pred (\ b → h (f b))))
      ( rev U
        ( first (pred (\ b → h (f b))))
        Unit
        ( ap Prop U
          ( pred (\ b → h (f b)))
          Unit-Prop
          ( \ p → first p)
          ( htpy-eq
            ( 2 → A)
            ( \ _ → Prop)
            ( \ g → (pred (\ b → h (g b))))
            ( \ _ → Unit-Prop)
            transposed-eq
            f))))
      unit)
```

`amazing-untranspose` is the converse: given that every arrow satisfies
`pred`, each fiber carries an `amazing-predicate` witness.

```rzk

#def amazing-untranspose
  ( pred : _b (2 → U) → Prop)
  ( A : _b U)
  ( h : _b A → U)
  ( f : _b (g : 2 → A) → first (pred (\ b → h (g b))))
  : <| _b | ( a : A) → amazing-predicate (mod _b pred) (h a) |>
  :=
    let mod _b tr_pred := untranspose-ar (Prop-b) U-b (mod _b pred) in
    let mod _b t : (g : 2 → A) → univ-family-Prop := mod _b (\(g : 2 -> A) -> (pred (\b -> h (g b)), f g)) in
    let mod _b beta := untranspose-ar univ-family-Prop-b (mod _b A) (mod _b t) in
    let mod _b fmap :=
      rar-fmap univ-family-Prop-b Prop-b
        (mod _b ( \ (x : univ-family-Prop) → first x)) in
    let mod _b rhs :=
      untranspose-ar Prop-b (mod _b A)
        (let mod ♭ t' := (mod _b t) in mod ♭ (\ (p : 2 → A) → first (t' p))) in
    let mod _b full-eq :=
        mod _b (concat <| ♭ | A → b-extract U-b (rar Prop-b) |>
          (mod ♭ (\ (x : A) → fmap (beta x)))
          (mod _b rhs)
          (mod ♭ (\ (x : A) → tr_pred (h x)))
          (untranspose-naturality-right-rev
            univ-family-Prop-b Prop-b (mod _b A)
            (mod _b ( \ (x : univ-family-Prop) → first x))
            ( mod _b t))
          (rev <| ♭ | A → b-extract U-b (rar Prop-b) |>
            (mod ♭ (\ (x : A) → tr_pred (h x)))
            (mod _b rhs)
            (untranspose-naturality-left
              Prop-b U-b (mod _b A) (mod _b h) (mod ♭ pred))))
    in
    let mod _b eq-beta :=
        mod _b (htpy-eq A (\ _ → b-extract U-b (rar Prop-b))
          (\ (x : A) → fmap (beta x))
          (\ (x : A) → tr_pred (h x))
          (b-extract-eq
            (mod ♭ (A → b-extract U-b (rar Prop-b)))
            (mod ♭ (\ (x : A) → fmap (beta x)))
            (mod ♭ (\ (x : A) → tr_pred (h x)))
            full-eq))
    in
    mod _b (\a -> (beta a, eq-beta a))
```

## Transposition equivalence

The transpose and untranspose form an equivalence, using
that `amazing-predicate` is a proposition.

```rzk

#postulate is-prop-amazing-predicate
  ( pred : _b (2 → U) → Prop)
  ( X : U)
  : is-prop (amazing-predicate (mod _b pred) X)

#def amazing-transpose-untranspose-section
  ( pred : _b (2 → U) → Prop)
  ( A : _b U)
  ( h : _b A → U)
  ( f : _b (a : A) → amazing-predicate (mod _b pred) (h a))
  :
    amazing-untranspose (mod _b pred) (mod _b A) (mod _b h)
      (amazing-transpose (mod _b pred) (mod _b A) (mod _b h) (mod _b f))
    = (mod _b f)
  :=
    let mod _b a-untranspose-transpose :=
      ( amazing-untranspose (mod _b pred) (mod _b A) (mod _b h)
        (amazing-transpose (mod _b pred) (mod _b A) (mod _b h) (mod _b f )))
    in
    crisp-induction-flat
      ( mod ♭ ((a : A) → amazing-predicate (mod _b pred) (h a)))
      ( mod _b a-untranspose-transpose) (mod _b f)
      ( mod ♭ (eq-htpy funext A (\ a → amazing-predicate (mod _b pred) (h a))
          a-untranspose-transpose
          ( f)
          ( \ a →
            first
              ( is-prop-amazing-predicate (mod _b pred) (h a)
                ( a-untranspose-transpose a)
                ( f a)))))

#def amazing-transpose-untranspose-retraction
  ( pred : _b (2 → U) → Prop)
  ( A : _b U)
  ( h : _b A → U)
  ( f : _b (g : 2 → A) → first (pred (\ b → h (g b))))
  :
    amazing-transpose (mod _b pred) (mod _b A) (mod _b h)
      (amazing-untranspose (mod _b pred) (mod _b A) (mod _b h) (mod _b f))
    = mod _b f
  :=
    let mod _b a-transpose-untranspose :=
      ( amazing-transpose (mod _b pred) (mod _b A) (mod _b h)
        (amazing-untranspose (mod _b pred) (mod _b A) (mod _b h) (mod _b f)))
    in
    crisp-induction-flat
      ( mod ♭ ((g : 2 → A) → first (pred (\ b → h (g b)))))
      ( mod _b a-transpose-untranspose) (mod _b f)
      ( mod ♭ (eq-htpy funext (2 → A) (\ g → first (pred (\ b → h (g b))))
        a-transpose-untranspose
        ( f)
        ( \ g →
          first
            ( second (pred (\ b → h (g b)))
              ( a-transpose-untranspose g)
              ( f g)))))

#def amazing-transpose-untranspose-equiv
  ( pred : _b (2 → U) → Prop)
  ( A : _b U)
  ( h : _b A → U)
  : Equiv
    <| _b | ( ( a : A) → amazing-predicate (mod _b pred) (h a)) |>
    <| _b | ( ( g : 2 → A) → first (pred (\ b → h (g b)))) |>
  :=
    ( amazing-transpose (mod _b pred) (mod _b A) (mod _b h)
    , (

      ( amazing-untranspose (mod _b pred) (mod _b A) (mod _b h)
        , amazing-transpose-untranspose-section (mod _b pred) (mod _b A) (mod _b h))

      , ( amazing-untranspose (mod _b pred) (mod _b A) (mod _b h)
        , amazing-transpose-untranspose-retraction (mod _b pred) (mod _b A) (mod _b h))

      ))
```
