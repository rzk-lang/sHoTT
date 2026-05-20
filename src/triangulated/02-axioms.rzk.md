# 2. Axioms

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Prerequisites

- `01-modalities.rzk.md` — Modality operations and type aliases.

## Right adjoint

```rzk
#def ar (A : U)
  : U
  := 2 → A

#postulate rar (A : <| ♭ | U |>)
  : <| ♭ | U |>

#postulate ar-rar-counit
  : <| ♭ | (A : ♭ U) → (x : 2 → (b-extract U-b (rar (mod ♭ A)))) → A |>

#def discrete-2-elim (i : ♭ 2) (A : U) (x y : A)
  : A
  :=
  recOR(
    ( i ≡ 0₂) ↦ x
  , ( i ≡ 1₂) ↦ y)

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

#def rar-functorial-pure (A : ♭ U) (a : ♭ A)
  : b-extract U-b (rar (mod ♭ A))
  :=
    let mod ♭ tr := (untranspose-ar (mod ♭ A) Unit-b) (mod ♭ (\ _ → a)) in
    tr unit

#def rar-functorial-fmap (A B : ♭ U) (f : ♭ A → B)
  : <| ♭ | b-extract U-b (rar (mod ♭ A)) → b-extract U-b (rar (mod ♭ B)) |>
  :=
  (untranspose-ar (mod ♭ B) (rar (mod ♭ A)))
    (mod ♭ (\ (p : 2 → b-extract U-b (rar (mod ♭ A))) → let mod ♭ eta := ar-rar-counit in f (eta (mod ♭ A) p)))

#def transpose-ar-natural
  ( A B C : ♭ U)
  ( h : ♭ C → B)
  ( f : ♭ B → b-extract U-b (rar (mod ♭ A)))
  : (transpose-ar (mod ♭ A) (mod ♭ C)) (mod ♭ (\ x → f (h x)))
    = ( mod ♭ (\ (p : 2 → C) →
        ( let mod ♭ tr := (transpose-ar (mod ♭ A) (mod ♭ B)) (mod ♭ f) in tr)
        ( \ i → h (p i))))
  := refl

#def transpose-untranspose-ar-precompose
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
```

## Univalence and crisp induction

```rzk
#def UA
  : U
  := (A : U) → (B : U) → Equiv (Equiv A B) (A = B)

#postulate crisp-induction-flat (A : ♭ U) (x y : ♭ A)
  : <| ♭ | x = y |> → (mod ♭ x) = (mod ♭ y)

#postulate crisp-induction-flat-rev
  : (A : ♭ U) → (x : ♭ A) → (y : ♭ A) → ((mod ♭ x) = (mod ♭ y)) → <| ♭ | x = y |>
```
