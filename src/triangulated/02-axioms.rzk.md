# 2. Axioms

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

This file contains the axioms of triangulated type theory as described
in Gratzer, Weinberger, and Buchholtz,
"Directed univalence in simplicial homotopy type theory" (2024),
[arXiv:2407.09146](https://arxiv.org/abs/2407.09146).

Triangulated type theory extends simplicial homotopy type theory with
modalities and new reasoning principles that enable the construction of
a universe with directed univalence.

## Prerequisites

- `01-modalities.rzk.md` — Modality operations and type aliases.

## Axiom 1: Interval

The simplicial interval 2 with total order.

```rzk
#def total-order-interval : CUBE := 2
```

## Axiom 2: Negation of interval

The op modality induces interval flip/unflip operations.

```rzk
-- flip_op/unflip_op
```

It induces a more global inversion on the tope layer.

```rzk
-- inv_op/uninv_op
```

## Axiom 3: Right adjoint

First, introduce the exponentiation by interval functor.

```rzk
#def ar (A : U)
  : U
  := 2 → A

#def ar-fmap (A B : U) (f : A → B) : ar A → ar B
  := \ p → \ i → f (p i)

#def ar-pure (A : U) (a : A) : ar A
  := \ _ → a
```

We postulate its right adjoint functor with counit, transpose, and untranspose.

```rzk
#postulate rar (A : <| ♭ | U |>)
  : <| ♭ | U |>

#postulate ar-rar-counit
  : <| ♭ | (A : ♭ U) → (x : 2 → (b-extract U-b (rar (mod ♭ A)))) → A |>

#def transpose-ar (A B : ♭ U)
  : <| ♭ | B → (b-extract U-b (rar (mod ♭ A))) |> → <| ♭ | (ar B) → A |>
  :=
  \ (f : ♭ B → (b-extract U-b (rar (mod ♭ A)))) →
    mod ♭ (\ (g : 2 → B) → (let mod ♭ eta := ar-rar-counit in eta) (mod ♭ A) (\ i → f (g i)))

#postulate untranspose-ar (A B : ♭ U)
  : <| ♭ | (ar B) → A |> → <| ♭ | B → (b-extract U-b (rar (mod ♭ A))) |>

#postulate transpose-untranspose-ar (A B : ♭ U)
  ( f : <| ♭ | (ar B) → A |>)
  : transpose-ar (mod ♭ A) (mod ♭ B) (untranspose-ar (mod ♭ A) (mod ♭ B) f) = f

#postulate untranspose-transpose-ar (A B : ♭ U)
  ( f : <| ♭ | B → (b-extract U-b (rar (mod ♭ A))) |>)
  : untranspose-ar (mod ♭ A) (mod ♭ B) (transpose-ar (mod ♭ A) (mod ♭ B) f) = f

#def transpose-ar-is-equiv (A B : ♭ U)
  : is-equiv
    <| ♭ | B → (b-extract U-b (rar (mod ♭ A))) |>
    <| ♭ | (ar B) → A |>
    ( transpose-ar (mod ♭ A) (mod ♭ B))
  :=
  ( ( untranspose-ar (mod ♭ A) (mod ♭ B)
    , untranspose-transpose-ar (mod ♭ A) (mod ♭ B))
  , ( untranspose-ar (mod ♭ A) (mod ♭ B)
    , transpose-untranspose-ar (mod ♭ A) (mod ♭ B)))

#def transpose-ar-equiv (A B : ♭ U)
  : Equiv
    <| ♭ | B → (b-extract U-b (rar (mod ♭ A))) |>
    <| ♭ | (ar B) → A |>
  :=
  ( transpose-ar (mod ♭ A) (mod ♭ B)
  , transpose-ar-is-equiv (mod ♭ A) (mod ♭ B))

```

These operations induce canonical functorial actions.

```rzk
#def rar-pure (A : ♭ U) (a : ♭ A)
  : b-extract U-b (rar (mod ♭ A))
  :=
    let mod ♭ tr := (untranspose-ar (mod ♭ A) Unit-b) (mod ♭ (\ _ → a)) in
    tr unit

#def rar-fmap (A B : ♭ U) (f : ♭ A → B)
  : <| ♭ | b-extract U-b (rar (mod ♭ A)) → b-extract U-b (rar (mod ♭ B)) |>
  :=
  (untranspose-ar (mod ♭ B) (rar (mod ♭ A)))
    (mod ♭ (\ (p : 2 → b-extract U-b (rar (mod ♭ A))) → let mod ♭ eta := ar-rar-counit in f (eta (mod ♭ A) p)))
```

Naturality of transpositions.

```rzk
#def transpose-untranspose-comp
  ( A B C : ♭ U)
  ( h : ♭ C → B)
  ( f : <| ♭ | (ar B) → A |>)
  :
    let mod ♭ sec := (untranspose-ar (mod ♭ A) (mod ♭ B)) f in
    (transpose-ar (mod ♭ A) (mod ♭ C))
      ( mod ♭ (\ (x : C) → (sec) (h x)))
    = (let mod ♭ f' := f in mod ♭ (\ (p : 2 → C) →
        (f') (\ i → h (p i))))
  := ap
      <| ♭ | (ar B) → A |>
      <| ♭ | (ar C) → A |>
      ( (transpose-ar (mod ♭ A) (mod ♭ B))
        ( (untranspose-ar (mod ♭ A) (mod ♭ B)) f))
      ( f)
      ( \ g → let mod ♭ g' := g in mod ♭ (\ (p : 2 → C) → g' (\ i → h (p i))))
      ( transpose-untranspose-ar (mod ♭ A) (mod ♭ B) f)

#def untranspose-naturality-right-rev
  ( A B C : ♭ U)
  ( f : ♭ A → B)
  ( t : <| ♭ | (ar C) → A |>)
  :
    let mod ♭ fmap := rar-fmap (mod ♭ A) (mod ♭ B) (mod _b f) in
    let mod ♭ k := untranspose-ar (mod ♭ A) (mod ♭ C) t in
    ( mod ♭ (\ (x : C) → fmap (k x)))
    = ( untranspose-ar (mod ♭ B) (mod ♭ C)
        ( let mod ♭ t' := t in mod ♭ (\ (p : 2 → C) → f (t' p))))
  :=
    let mod ♭ fmap := rar-fmap (mod ♭ A) (mod ♭ B) (mod _b f) in
    let mod ♭ k := untranspose-ar (mod ♭ A) (mod ♭ C) t in
    let lhs := mod ♭ (\ (x : C) → fmap (k x)) in
    let mod ♭ t' := t in
    let ft := mod ♭ (\ (p : 2 → C) → f (t' p)) in
    let rhs := untranspose-ar (mod ♭ B) (mod ♭ C) ft in
    let tu := transpose-ar (mod ♭ A) (mod ♭ C)
      ( untranspose-ar (mod ♭ A) (mod ♭ C) t) in
    let step1 :=
      concat <| ♭ | (ar C) → B |>
        ( transpose-ar (mod ♭ B) (mod ♭ C) lhs)
        ( let mod ♭ q' := tu in mod ♭ (\ (p : 2 → C) → f (q' p)))
        ft
        ( transpose-untranspose-comp
            ( mod ♭ B) (rar (mod ♭ A)) (mod ♭ C)
            ( mod _b k)
            ( mod ♭ (\ (p : 2 → b-extract U-b (rar (mod ♭ A))) →
                let mod ♭ eta := ar-rar-counit in f (eta (mod ♭ A) p))))
        ( ap <| ♭ | (ar C) → A |> <| ♭ | (ar C) → B |>
            tu t
            ( \ (q : <| ♭ | (ar C) → A |>) →
                let mod ♭ q' := q in mod ♭ (\ (p : 2 → C) → f (q' p)))
            ( transpose-untranspose-ar (mod ♭ A) (mod ♭ C) t)) in
    let step2 := transpose-untranspose-ar (mod ♭ B) (mod ♭ C) ft in
    ( ap-cancel-has-retraction
        <| ♭ | C → (b-extract U-b (rar (mod ♭ B))) |>
        <| ♭ | (ar C) → B |>
        ( transpose-ar (mod ♭ B) (mod ♭ C))
        ( ( untranspose-ar (mod ♭ B) (mod ♭ C))
        , ( untranspose-transpose-ar (mod ♭ B) (mod ♭ C)))
        lhs
        rhs)
    ( concat <| ♭ | (ar C) → B |>
        ( transpose-ar (mod ♭ B) (mod ♭ C) lhs)
        ft
        ( transpose-ar (mod ♭ B) (mod ♭ C) rhs)
        step1
        ( rev <| ♭ | (ar C) → B |>
            ( transpose-ar (mod ♭ B) (mod ♭ C) rhs)
            ft
            step2))

#def untranspose-naturality-right
  ( A B C : ♭ U)
  ( f : ♭ A → B)
  ( t : <| ♭ | (ar C) → A |>)
  :
    let mod ♭ fmap := rar-fmap (mod ♭ A) (mod ♭ B) (mod _b f) in
    let mod ♭ k := untranspose-ar (mod ♭ A) (mod ♭ C) t in
    ( untranspose-ar (mod ♭ B) (mod ♭ C)
        ( let mod ♭ t' := t in mod ♭ (\ (p : 2 → C) → f (t' p))))
    = ( mod ♭ (\ (x : C) → fmap (k x)))
  :=
    let mod ♭ fmap := rar-fmap (mod ♭ A) (mod ♭ B) (mod _b f) in
    let mod ♭ k := untranspose-ar (mod ♭ A) (mod ♭ C) t in
    rev
      <| ♭ | C → (b-extract U-b (rar (mod ♭ B))) |>
      ( mod ♭ (\ (x : C) → fmap (k x)))
      ( untranspose-ar (mod ♭ B) (mod ♭ C)
        ( let mod ♭ t' := t in mod ♭ (\ (p : 2 → C) → f (t' p))))
      ( untranspose-naturality-right-rev (mod ♭ A) (mod ♭ B) (mod ♭ C) (mod _b f) t)

#def untranspose-naturality-left
  ( A B C : ♭ U)
  ( h : ♭ C → B)
  ( f : <| ♭ | (ar B) → A |>)
  :
    let mod ♭ sec := (untranspose-ar (mod ♭ A) (mod ♭ B)) f in
    ( mod ♭ (\ (x : C) → sec (h x)))
    = ( untranspose-ar (mod ♭ A) (mod ♭ C)
        ( let mod ♭ f' := f in mod ♭ (\ (p : 2 → C) → f' (\ i → h (p i)))))
  :=
    let mod ♭ sec := (untranspose-ar (mod ♭ A) (mod ♭ B)) f in
    let lhs := mod ♭ (\ (x : C) → sec (h x)) in
    let ft := let mod ♭ f' := f in mod ♭ (\ (p : 2 → C) → f' (\ i → h (p i))) in
    let rhs := untranspose-ar (mod ♭ A) (mod ♭ C) ft in
    ap-cancel-has-retraction
      <| ♭ | C → b-extract U-b (rar (mod ♭ A)) |>
      <| ♭ | (2 → C) → A |>
      (transpose-ar (mod ♭ A) (mod ♭ C))
      ( (untranspose-ar (mod ♭ A) (mod ♭ C))
      , (untranspose-transpose-ar (mod ♭ A) (mod ♭ C)))
      lhs
      rhs
      (concat <| ♭ | (2 → C) → A |>
        (transpose-ar (mod ♭ A) (mod ♭ C) lhs)
        ft
        (transpose-ar (mod ♭ A) (mod ♭ C) rhs)
        (transpose-untranspose-comp (mod ♭ A) (mod ♭ B) (mod ♭ C) (mod _b h) f)
        (rev <| ♭ | (2 → C) → A |>
          (transpose-ar (mod ♭ A) (mod ♭ C) rhs)
          ft
          (transpose-untranspose-ar (mod ♭ A) (mod ♭ C) ft)))

#def untranspose-naturality-left-rev
  ( A B C : ♭ U)
  ( h : ♭ C → B)
  ( f : <| ♭ | (ar B) → A |>)
  :
    let mod ♭ sec := (untranspose-ar (mod ♭ A) (mod ♭ B)) f in
    ( untranspose-ar (mod ♭ A) (mod ♭ C)
        ( let mod ♭ f' := f in mod ♭ (\ (p : 2 → C) → f' (\ i → h (p i)))))
    = ( mod ♭ (\ (x : C) → sec (h x)))
  :=
    let mod ♭ sec := (untranspose-ar (mod ♭ A) (mod ♭ B)) f in
    rev
      <| ♭ | C → (b-extract U-b (rar (mod ♭ A))) |>
      ( mod ♭ (\ (x : C) → sec (h x)))
      ( untranspose-ar (mod ♭ A) (mod ♭ C)
        ( let mod ♭ f' := f in mod ♭ (\ (p : 2 → C) → f' (\ i → h (p i)))))
      ( untranspose-naturality-left (mod ♭ A) (mod ♭ B) (mod ♭ C) (mod _b h) f)

```

## Axiom 4: Univalence

```rzk
#postulate ua
  : UA
```

## Axiom 5: Crisp induction

### Flat modality

```rzk
#postulate crisp-induction-flat (A : ♭ U) (x y : ♭ A)
  : <| ♭ | x = y |> → (mod ♭ x) = (mod ♭ y)

#postulate crisp-induction-flat-rev (A : ♭ U) (x y : ♭ A)
  : ((mod ♭ x) = (mod ♭ y)) → <| ♭ | x = y |>

#postulate crisp-induction-flat-section (A : ♭ U) (x y : ♭ A)
  (p : <| ♭ | x = y |>)
  : crisp-induction-flat-rev (mod _b A) (mod _b x) (mod _b y) (crisp-induction-flat (mod _b A) (mod _b x) (mod _b y) p) = p

#postulate crisp-induction-flat-retraction (A : ♭ U) (x y : ♭ A)
  (p : (mod ♭ x) = (mod ♭ y))
  : crisp-induction-flat (mod _b A) (mod _b x) (mod _b y) (crisp-induction-flat-rev (mod _b A) (mod _b x) (mod _b y) p) = p

#def crisp-induction-flat-is-equiv (A : ♭ U) (x y : ♭ A)
  : is-equiv
    <| ♭ | x = y |>
    ((mod ♭ x) = (mod ♭ y))
    (crisp-induction-flat (mod _b A) (mod _b x) (mod _b y))
  :=
  ( ( crisp-induction-flat-rev (mod _b A) (mod _b x) (mod _b y)
    , crisp-induction-flat-section (mod _b A) (mod _b x) (mod _b y))
  , ( crisp-induction-flat-rev (mod _b A) (mod _b x) (mod _b y)
    , crisp-induction-flat-retraction (mod _b A) (mod _b x) (mod _b y)))
```

### Sharp modality

```rzk
#postulate crisp-induction-sharp (A : _# U) (x y : ♯ A)
  : <| ♯ | x = y |> → (mod ♯ x) = (mod ♯ y)

#postulate crisp-induction-sharp-rev (A : _# U) (x y : ♯ A)
  : ((mod ♯ x) = (mod ♯ y)) → <| ♯ | x = y |>

#postulate crisp-induction-sharp-section (A : _# U) (x y : ♯ A)
  (p : <| ♯ | x = y |>)
  : crisp-induction-sharp-rev (mod _# A) (mod _# x) (mod _# y) (crisp-induction-sharp (mod _# A) (mod _# x) (mod _# y) p) = p

#postulate crisp-induction-sharp-retraction (A : _# U) (x y : ♯ A)
  (p : (mod ♯ x) = (mod ♯ y))
  : crisp-induction-sharp (mod _# A) (mod _# x) (mod _# y) (crisp-induction-sharp-rev (mod _# A) (mod _# x) (mod _# y) p) = p

#def crisp-induction-sharp-is-equiv (A  : _# U) (x y : ♯ A)
  : is-equiv
    <| ♯ | x = y |>
    ((mod ♯ x) = (mod ♯ y))
    (crisp-induction-sharp (mod _# A) (mod _# x) (mod _# y))
  :=
  ( ( crisp-induction-sharp-rev (mod _# A) (mod _# x) (mod _# y)
    , crisp-induction-sharp-section (mod _# A) (mod _# x) (mod _# y))
  , ( crisp-induction-sharp-rev (mod _# A) (mod _# x) (mod _# y)
    , crisp-induction-sharp-retraction (mod _# A) (mod _# x) (mod _# y)))
```

### Op modality

```rzk
#postulate crisp-induction-op (A : ᵒᵖ U) (x y : ᵒᵖ A)
  : <| ᵒᵖ | x = y |> → (mod ᵒᵖ x) = (mod ᵒᵖ y)

#postulate crisp-induction-op-rev (A : ᵒᵖ U) (x y : ᵒᵖ A)
  : ((mod ᵒᵖ x) = (mod ᵒᵖ y)) → <| ᵒᵖ | x = y |>

#postulate crisp-induction-op-section (A : ᵒᵖ U) (x y : ᵒᵖ A)
  (p : <| ᵒᵖ | x = y |>)
  : crisp-induction-op-rev (mod _op A) (mod _op x) (mod _op y) (crisp-induction-op (mod _op A) (mod _op x) (mod _op y) p) = p

#postulate crisp-induction-op-retraction (A : ᵒᵖ U) (x y : ᵒᵖ A)
  (p : (mod ᵒᵖ x) = (mod ᵒᵖ y))
  : crisp-induction-op (mod _op A) (mod _op x) (mod _op y) (crisp-induction-op-rev (mod _op A) (mod _op x) (mod _op y) p) = p

#def crisp-induction-op-is-equiv (A : ᵒᵖ U) (x y : ᵒᵖ A)
  : is-equiv
    <| ᵒᵖ | x = y |>
    ((mod ᵒᵖ x) = (mod ᵒᵖ y))
    (crisp-induction-op (mod _op A) (mod _op x) (mod _op y))
  :=
  ( ( crisp-induction-op-rev (mod _op A) (mod _op x) (mod _op y)
    , crisp-induction-op-section (mod _op A) (mod _op x) (mod _op y))
  , ( crisp-induction-op-rev (mod _op A) (mod _op x) (mod _op y)
    , crisp-induction-op-retraction (mod _op A) (mod _op x) (mod _op y)))
```

## Axiom 6: Interval detects discreteness

```rzk
#postulate I-detects-discreteness
  (A : _b U)
  : iff (Equiv A <| _b | A |>) (Equiv A (2 → A))
```

## Axiom 7: Global points of the interval

The discrete interval is equivalent to Bool.

```rzk
#def discrete-2-elim (i : ♭ 2) (A : U) (x y : A)
  : A
  :=
  recOR(
    ( i ≡ 0₂) ↦ x
  , ( i ≡ 1₂) ↦ y)
```

## Axiom 8: Cubes separate

```rzk
#postulate cubes-separate (A B : _b U) (f : _b A → B)
  : iff (is-equiv A B f) ((cube : _b CUBE) → Equiv <| _b | cube → A |> <| _b | cube → B |>)
```

## Extensionalities

```rzk
#postulate funext
  : FunExt

#postulate weakfunext
  : WeakFunExt

#postulate extext
  : ExtExt
```
