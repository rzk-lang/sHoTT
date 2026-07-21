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
  let mod ᵒᵖ / ᵒᵖ x_2 := x_1 in
  x_2
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
  let mod ♯ / ♯ x_2 := x_1 in
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
  := ( let mod ♭ / ♭ x := t
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
```
