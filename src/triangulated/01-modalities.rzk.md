# 1. Modalities

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Flat modality

```rzk
#def b-extract (A : ♭ U) (x : ♭ A)
  : A
  := x

#def b-map (A B : ♭ U) (f : ♭ A → B)
  : <| ♭ | A |> → <| ♭ | B |>
  :=
  \ (x : ♭ A) → mod ♭ (f x)

#def b-dup (A : ♭ U) (x : ♭ A)
  : <| ♭ | <| ♭ | A |> |>
  :=
  mod ♭ (mod ♭ (x))
```

## Opposite modality

```rzk
#def op-map (A B : ᵒᵖ U) (f : ᵒᵖ A → B)
  : <| ᵒᵖ | A |> → <| ᵒᵖ | B |>
  :=
  \ (x : ᵒᵖ A) → mod ᵒᵖ (f x)

#def double-op (A : U) (x : <| ᵒᵖ | <| ᵒᵖ | A |> |>)
  : A
  :=
  let mod ᵒᵖ x_1 := x in
  let mod ᵒᵖ / ᵒᵖ x_2 := x_1 in
  x_2
```

## Sharp modality

```rzk
#def sharp-pure (A : U) (x : A)
  : <| ♯ | A |>
  := mod ♯ x

#def sharp-map (A B : U) (f : A → B)
  : <| ♯ | A |> → <| ♯ | B |>
  :=
  \ (x : ♯ A) → mod ♯ (f x)

#def sharp-join (A : U) (a : <| ♯ | <| ♯ | A |> |>)
  : <| ♯ | A |>
  :=
  let mod ♯ x_1 := a in
  let mod ♯ / ♯ x_2 := x_1 in
  mod ♯ (x_2)
```

## Useful modal aliases

```rzk
#def U-b
  : <| ♭ | U |>
  := mod ♭ U

#def Prop-b
  : <| ♭ | U |>
  := mod ♭ Prop

#def univ-family-Prop-b
  : <| ♭ | U |>
  := mod ♭ univ-family-Prop

#def Unit-b
  : <| ♭ | U |>
  := mod ♭ Unit

#def b-extract-eq (A : ♭ U) (x y : <| ♭ | A |>)
  ( p : x = y)
  : b-extract (mod ♭ A) x = b-extract (mod ♭ A) y
  := ap <| ♭ | A |> A x y (b-extract (mod ♭ A)) p
```
