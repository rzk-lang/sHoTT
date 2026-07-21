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

The cubical interval I with bounded order.

```rzk
#def cubical-interval
  : CUBE
  := 𝕀
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
  := 𝕀 → A

#def ar-fmap (A B : U) (f : A → B)
  : ar A → ar B
  := \ p → \ i → f (p i)

#def ar-pure (A : U) (a : A)
  : ar A
  := \ _ → a
```

We postulate its right adjoint functor with counit, transpose, and untranspose.

```rzk
#postulate rar (A : (♭ U))
  : ( ♭ U)

#postulate ar-rar-counit
  : ( ♭ ( ( A :♭ U) → (x : 𝕀 → (b-extract U (rar (mod ♭ A)))) → A))

#def transpose-ar (A B :♭ U) (f : ♭ (B → (b-extract U (rar (mod ♭ A)))))
  : ( ♭ ( ( ar B) → A))
  :=
  let mod ♭ f' := f in
  mod ♭ (\ (g : 𝕀 → B) → (let mod ♭ eta := ar-rar-counit in eta) A (\ i → f' (g i)))

#postulate untranspose-ar (A B :♭ U) (f : ♭ ((ar B) → A))
  : ( ♭ ( B → (b-extract U (rar (mod ♭ A)))))

#postulate transpose-untranspose-ar (A B :♭ U)
  ( f : (♭ ((ar B) → A)))
  : transpose-ar A B (untranspose-ar A B f) = f

#postulate untranspose-transpose-ar (A B :♭ U)
  ( f : (♭ (B → (b-extract U (rar (mod ♭ A))))))
  : untranspose-ar A B (transpose-ar A B f) = f

#def transpose-ar-is-equiv (A B :♭ U)
  : is-equiv
    ( ♭ ( B → (b-extract U (rar (mod ♭ A)))))
    ( ♭ ( ( ar B) → A))
    ( transpose-ar A B)
  :=
  ( ( untranspose-ar A B
    , untranspose-transpose-ar A B)
  , ( untranspose-ar A B
    , transpose-untranspose-ar A B))

#def transpose-ar-equiv (A B :♭ U)
  : Equiv
    ( ♭ ( B → (b-extract U (rar (mod ♭ A)))))
    ( ♭ ( ( ar B) → A))
  :=
  ( transpose-ar A B
  , transpose-ar-is-equiv A B)

```

These operations induce canonical functorial actions.

```rzk
#def rar-pure (A :♭ U) (a :♭ A)
  : b-extract U (rar (mod ♭ A))
  :=
    let mod ♭ tr := untranspose-ar A Unit (mod _b (\ _ → a)) in
    tr unit

#def rar-fmap (A B :♭ U) (f :♭ A → B)
  : ( ♭ ( b-extract U (rar (mod ♭ A)) → b-extract U (rar (mod ♭ B))))
  :=
  untranspose-ar B (b-extract U (rar (mod ♭ A)))
    mod _b ( \ (p : 𝕀 → b-extract U (rar (mod ♭ A))) → f ((let mod ♭ eta := ar-rar-counit in eta) A p))
```

Naturality of transpositions.

```rzk
#def transpose-precomp (A B C :♭ U) (h :♭ C → B)
  ( w : ♭ (B → (b-extract U (rar (mod ♭ A)))))
  : ( let mod ♭ sec := w in transpose-ar A C (mod ♭ (\ (x : C) → sec (h x))))
  =_{ ♭ ((ar C) → A)} ( let mod ♭ t := transpose-ar A B w in mod ♭ (\ (p : 𝕀 → C) → t (\ i → h (p i))))
  := flat-convoy
       ( B → (b-extract U (rar (mod ♭ A))))
       ( \ (z : ♭ (B → (b-extract U (rar (mod ♭ A))))) →
           ( let mod ♭ sec := z in transpose-ar A C (mod ♭ (\ (x : C) → sec (h x))))
           =_{ ♭ ((ar C) → A)} ( let mod ♭ t := transpose-ar A B z in mod ♭ (\ (p : 𝕀 → C) → t (\ i → h (p i)))))
       ( w)
       ( \ (sec :_b B → (b-extract U (rar (mod ♭ A)))) → \ (e : mod ♭ sec =_{♭ (B → (b-extract U (rar (mod ♭ A))))} w) → refl)

#def transpose-untranspose-comp
  ( A B C :♭ U)
  ( h :♭ C → B)
  ( f :♭ (ar B) → A)
  :
    (let mod ♭ sec := untranspose-ar A B (mod ♭ f) in
    ( transpose-ar A C)
      ( mod ♭ (\ (x : C) → (sec) (h x))))
    = ( let mod ♭ f' := mod ♭ f in mod ♭ (\ (p : 𝕀 → C)
      → ( f') (\ i → h (p i))))
  :=
    concat
      ( ♭ ( ( ar C) → A))
      ( let mod ♭ sec := untranspose-ar A B (mod ♭ f) in
        transpose-ar A C (mod ♭ (\ (x : C) → sec (h x))))
      ( let mod ♭ t := transpose-ar A B (untranspose-ar A B (mod ♭ f)) in
        mod ♭ (\ (p : 𝕀 → C) → t (\ i → h (p i))))
      ( let mod ♭ f' := mod ♭ f in mod ♭ (\ (p : 𝕀 → C) → f' (\ i → h (p i))))
      ( transpose-precomp A B C h (untranspose-ar A B (mod ♭ f)))
      ( ap
        ( ♭ ( ( ar B) → A))
        ( ♭ ( ( ar C) → A))
        ( transpose-ar A B (untranspose-ar A B (mod ♭ f)))
        ( mod ♭ f)
        ( \ (g : ♭ ((ar B) → A)) → let mod ♭ t := g in mod ♭ (\ (p : 𝕀 → C) → t (\ i → h (p i))))
        ( transpose-untranspose-ar A B (mod ♭ f)))

#def untranspose-naturality-left
  ( A B C :♭ U)
  ( h :♭ C → B)
  ( f :♭ (ar B) → A)
  :
    ( let mod ♭ sec := untranspose-ar A B (mod ♭ f) in mod ♭ (\ (x : C) → sec (h x)))
    = ( untranspose-ar A C
        ( mod ♭ (\ (p : 𝕀 → C) → f (\ i → h (p i)))))
  :=
    ap-cancel-has-retraction
      ( ♭ ( C → b-extract U (rar (mod ♭ A))))
      ( ♭ ( ( ar C) → A))
      ( transpose-ar A C)
      ( ( untranspose-ar A C)
      , ( untranspose-transpose-ar A C))
      ( let mod ♭ sec := untranspose-ar A B (mod ♭ f) in mod ♭ (\ (x : C) → sec (h x)))
      ( untranspose-ar A C (mod ♭ (\ (p : 𝕀 → C) → f (\ i → h (p i)))))
      ( concat ( ♭ ( ( ar C) → A))
        ( transpose-ar A C (let mod ♭ sec := untranspose-ar A B (mod ♭ f) in mod ♭ (\ (x : C) → sec (h x))))
        ( mod ♭ (\ (p : 𝕀 → C) → f (\ i → h (p i))))
        ( transpose-ar A C (untranspose-ar A C (mod ♭ (\ (p : 𝕀 → C) → f (\ i → h (p i))))))
        ( concat ( ♭ ( ( ar C) → A))
          ( transpose-ar A C (let mod ♭ sec := untranspose-ar A B (mod ♭ f) in mod ♭ (\ (x : C) → sec (h x))))
          ( let mod ♭ sec := untranspose-ar A B (mod ♭ f) in transpose-ar A C (mod ♭ (\ (x : C) → sec (h x))))
          ( mod ♭ (\ (p : 𝕀 → C) → f (\ i → h (p i))))
          ( flat-naturality
            ( B → (b-extract U (rar (mod ♭ A))))
            ( C → (b-extract U (rar (mod ♭ A))))
            ( ( ar C) → A)
            ( transpose-ar A C)
            ( \ (sec : B → (b-extract U (rar (mod ♭ A)))) → \ (x : C) → sec (h x))
            ( untranspose-ar A B (mod ♭ f)))
          ( concat ( ♭ ( ( ar C) → A))
            ( let mod ♭ sec := untranspose-ar A B (mod ♭ f) in transpose-ar A C (mod ♭ (\ (x : C) → sec (h x))))
            ( let mod ♭ f' := mod ♭ f in mod ♭ (\ (p : 𝕀 → C) → f' (\ i → h (p i))))
            ( mod ♭ (\ (p : 𝕀 → C) → f (\ i → h (p i))))
            ( transpose-untranspose-comp A B C h f)
            ( flat-beta
              ( ( ar B) → A)
              ( ( ar C) → A)
              ( \ (f' : (ar B) → A) → \ (p : 𝕀 → C) → f' (\ i → h (p i)))
              ( f))))
        ( rev ( ♭ ( ( ar C) → A))
          ( transpose-ar A C (untranspose-ar A C (mod ♭ (\ (p : 𝕀 → C) → f (\ i → h (p i))))))
          ( mod ♭ (\ (p : 𝕀 → C) → f (\ i → h (p i))))
          ( transpose-untranspose-ar A C (mod ♭ (\ (p : 𝕀 → C) → f (\ i → h (p i)))))))

#def untranspose-naturality-left-rev
  ( A B C :♭ U)
  ( h :♭ C → B)
  ( f :♭ (ar B) → A)
  : untranspose-ar A C (mod ♭ (\ (p : 𝕀 → C) → f (\ i → h (p i))))
  = ( let mod ♭ sec := untranspose-ar A B (mod ♭ f) in mod ♭ (\ (x : C) → sec (h x)))
  :=
    rev
      ( ♭ ( C → b-extract U (rar (mod ♭ A))))
      ( let mod ♭ sec := untranspose-ar A B (mod ♭ f) in mod ♭ (\ (x : C) → sec (h x)))
      ( untranspose-ar A C (mod ♭ (\ (p : 𝕀 → C) → f (\ i → h (p i)))))
      ( untranspose-naturality-left A B C h f)

#def untranspose-naturality-left-flat (A B C :♭ U) (hh : ♭ (C → B)) (f :♭ (ar B) → A)
  : ( let mod ♭ sec := untranspose-ar A B (mod ♭ f) in let mod ♭ h := hh in mod ♭ (\ (x : C) → sec (h x)))
  = ( let mod ♭ h := hh in untranspose-ar A C (mod ♭ (\ (p : 𝕀 → C) → f (\ i → h (p i)))))
  := flat-convoy
       ( C → B)
       ( \ (z : ♭ (C → B)) → (let mod ♭ sec := untranspose-ar A B (mod ♭ f) in let mod ♭ h' := z in mod ♭ (\ (x : C) → sec (h' x))) = (let mod ♭ h' := z in untranspose-ar A C (mod ♭ (\ (p : 𝕀 → C) → f (\ i → h' (p i))))))
       ( hh)
       ( \ (h :_b C → B) → \ (e : mod ♭ h =_{♭ (C → B)} hh) → untranspose-naturality-left A B C h f)

#def untranspose-naturality-right-rev
  ( A B C :♭ U)
  ( f :♭ A → B)
  ( t :♭ (ar C) → A)
  : ( let mod ♭ fmap := rar-fmap A B f in
      let mod ♭ k := untranspose-ar A C (mod ♭ t) in
      mod ♭ (\ (x : C) → fmap (k x)))
    = untranspose-ar B C (mod ♭ (\ (p : 𝕀 → C) → f (t p)))
  :=
    concat ( ♭ ( C → b-extract U (rar (mod ♭ B))))
      ( let mod ♭ fmap := rar-fmap A B f in
        let mod ♭ k := untranspose-ar A C (mod ♭ t) in
        mod ♭ (\ (x : C) → fmap (k x)))
      ( let mod ♭ k := untranspose-ar A C (mod ♭ t) in
        untranspose-ar B C (mod ♭ (\ (p : 𝕀 → C) → f ((let mod ♭ eta := ar-rar-counit in eta) A (\ i → k (p i))))))
      ( untranspose-ar B C (mod ♭ (\ (p : 𝕀 → C) → f (t p))))
      ( untranspose-naturality-left-flat B (b-extract U (rar (mod ♭ A))) C
          ( untranspose-ar A C (mod ♭ t))
          ( \ (q : 𝕀 → b-extract U (rar (mod ♭ A))) → f ((let mod ♭ eta := ar-rar-counit in eta) A q)))
      ( concat ( ♭ ( C → b-extract U (rar (mod ♭ B))))
        ( let mod ♭ k := untranspose-ar A C (mod ♭ t) in
          untranspose-ar B C (mod ♭ (\ (p : 𝕀 → C) → f ((let mod ♭ eta := ar-rar-counit in eta) A (\ i → k (p i))))))
        ( untranspose-ar B C
            ( let mod ♭ k := untranspose-ar A C (mod ♭ t) in
              mod ♭ (\ (p : 𝕀 → C) → f ((let mod ♭ eta := ar-rar-counit in eta) A (\ i → k (p i))))))
        ( untranspose-ar B C (mod ♭ (\ (p : 𝕀 → C) → f (t p))))
        ( rev ( ♭ ( C → b-extract U (rar (mod ♭ B))))
          ( untranspose-ar B C
              ( let mod ♭ k := untranspose-ar A C (mod ♭ t) in
                mod ♭ (\ (p : 𝕀 → C) → f ((let mod ♭ eta := ar-rar-counit in eta) A (\ i → k (p i))))))
          ( let mod ♭ k := untranspose-ar A C (mod ♭ t) in
            untranspose-ar B C (mod ♭ (\ (p : 𝕀 → C) → f ((let mod ♭ eta := ar-rar-counit in eta) A (\ i → k (p i))))))
          ( flat-naturality
              ( C → b-extract U (rar (mod ♭ A)))
              ( ( ar C) → B)
              ( C → b-extract U (rar (mod ♭ B)))
              ( untranspose-ar B C)
              ( \ (k : C → b-extract U (rar (mod ♭ A))) → \ (p : 𝕀 → C) → f ((let mod ♭ eta := ar-rar-counit in eta) A (\ i → k (p i))))
              ( untranspose-ar A C (mod ♭ t))))
        ( ap ( ♭ ( ( ar C) → B)) ( ♭ ( C → b-extract U (rar (mod ♭ B))))
          ( let mod ♭ k := untranspose-ar A C (mod ♭ t) in
            mod ♭ (\ (p : 𝕀 → C) → f ((let mod ♭ eta := ar-rar-counit in eta) A (\ i → k (p i)))))
          ( mod ♭ (\ (p : 𝕀 → C) → f (t p)))
          ( untranspose-ar B C)
          ( concat ( ♭ ( ( ar C) → B))
            ( let mod ♭ k := untranspose-ar A C (mod ♭ t) in
              mod ♭ (\ (p : 𝕀 → C) → f ((let mod ♭ eta := ar-rar-counit in eta) A (\ i → k (p i)))))
            ( b-map ( ( ar C) → A) ( ( ar C) → B)
                ( \ (m : (ar C) → A) → \ (p : ar C) → f (m p))
                ( transpose-ar A C (untranspose-ar A C (mod ♭ t))))
            ( mod ♭ (\ (p : 𝕀 → C) → f (t p)))
            ( rev ( ♭ ( ( ar C) → B))
              ( b-map ( ( ar C) → A) ( ( ar C) → B)
                  ( \ (m : (ar C) → A) → \ (p : ar C) → f (m p))
                  ( transpose-ar A C (untranspose-ar A C (mod ♭ t))))
              ( let mod ♭ k := untranspose-ar A C (mod ♭ t) in
                mod ♭ (\ (p : 𝕀 → C) → f ((let mod ♭ eta := ar-rar-counit in eta) A (\ i → k (p i)))))
              ( flat-naturality
                  ( C → b-extract U (rar (mod ♭ A)))
                  ( ( ar C) → A)
                  ( ( ar C) → B)
                  ( b-map ( ( ar C) → A) ( ( ar C) → B) ( \ (m : (ar C) → A) → \ (p : ar C) → f (m p)))
                  ( \ (k : C → b-extract U (rar (mod ♭ A))) → \ (g : ar C) → (let mod ♭ eta := ar-rar-counit in eta) A (\ i → k (g i)))
                  ( untranspose-ar A C (mod ♭ t))))
            ( ap ( ♭ ( ( ar C) → A)) ( ♭ ( ( ar C) → B))
              ( transpose-ar A C (untranspose-ar A C (mod ♭ t)))
              ( mod ♭ t)
              ( b-map ( ( ar C) → A) ( ( ar C) → B) ( \ (m : (ar C) → A) → \ (p : ar C) → f (m p)))
              ( transpose-untranspose-ar A C (mod ♭ t))))))

#def untranspose-naturality-right
  ( A B C :♭ U)
  ( f :♭ A → B)
  ( t :♭ (ar C) → A)
  : untranspose-ar B C (mod ♭ (\ (p : 𝕀 → C) → f (t p)))
    = ( let mod ♭ fmap := rar-fmap A B f in
        let mod ♭ k := untranspose-ar A C (mod ♭ t) in
        mod ♭ (\ (x : C) → fmap (k x)))
  := rev
       ( ♭ ( C → b-extract U (rar (mod ♭ B))))
       ( let mod ♭ fmap := rar-fmap A B f in
         let mod ♭ k := untranspose-ar A C (mod ♭ t) in
         mod ♭ (\ (x : C) → fmap (k x)))
       ( untranspose-ar B C (mod ♭ (\ (p : 𝕀 → C) → f (t p))))
       ( untranspose-naturality-right-rev A B C f t)

```

## Axiom 4: Univalence

```rzk
#def idtoeqv (A B : U) (p : A = B)
  : Equiv A B
  := equiv-transport U (\ Z → Z) A B p

#postulate univalence (A B : U)
  : is-equiv (A = B) (Equiv A B) (idtoeqv A B)

#def ua
  : UA
  := \ A B → inv-equiv (A = B) (Equiv A B) (idtoeqv A B , univalence A B)
```

### Propositional equality for univalent transport

```rzk
#def transport-ua
  ( X Y : U) (e : Equiv X Y) (x : X)
  : transport U (\ Z → Z) X Y (first (ua X Y) e) x = first e x
  :=
    ap ( Equiv X Y) Y
      ( idtoeqv X Y (first (ua X Y) e)) e
      ( \ ee → first ee x)
      ( inv-equiv-cancel' (X = Y) (Equiv X Y) (idtoeqv X Y , univalence X Y) e)

#def transport-transport-rev
  ( A : U) (B : A → U) (x y : A) (p : x = y) (u : B y)
  : transport A B x y p (transport-rev A B x y p u) = u
  :=
    ind-path A x
      ( \ y' p' → (u' : B y') → transport A B x y' p' (transport-rev A B x y' p' u') = u')
      ( \ u' → refl)
      ( y) p u

#def transport-first-eq-pair
  ( B : U → U)
  ( X Y : Σ (A : U) , B A)
  ( e : Eq-Σ U B X Y)
  ( w : first X)
  : transport (Σ (A : U) , B A) (\ s → first s) X Y (eq-pair U B X Y e) w
    = transport U (\ Z → Z) (first X) (first Y) (first e) w
  :=
    concat (first Y)
      ( transport (Σ (A : U) , B A) (\ s → first s) X Y (eq-pair U B X Y e) w)
      ( transport U (\ Z → Z) (first X) (first Y)
          ( ap (Σ (A : U) , B A) U X Y (\ z → first z) (eq-pair U B X Y e)) w)
      ( transport U (\ Z → Z) (first X) (first Y) (first e) w)
      ( transport-substitution (Σ (A : U) , B A) U (\ Z → Z) (\ z → first z) X Y
          ( eq-pair U B X Y e) w)
      ( ap ((first X) = (first Y)) (first Y)
          ( ap (Σ (A : U) , B A) U X Y (\ z → first z) (eq-pair U B X Y e))
          ( first e)
          ( \ pth → transport U (\ Z → Z) (first X) (first Y) pth w)
          ( first-path-Σ-eq-pair U B X Y e))

#def product-transport-fun
  ( W : U) (el : W → U)
  ( X X' Y Y' : W)
  ( p : X = X') (q : Y = Y')
  ( g : el X → el Y)
  : product-transport W W (\ S T → el S → el T) X X' Y Y' p q g
    = ( \ (x' : el X') →
        transport W el Y Y' q (g (transport-rev W el X X' p x')))
  :=
    ind-path W Y
      ( \ Y'' q' →
        product-transport W W (\ S T → el S → el T) X X' Y Y'' p q' g
        = ( \ (x' : el X') →
            transport W el Y Y'' q' (g (transport-rev W el X X' p x'))))
      ( ind-path W X
          ( \ X'' p' →
            product-transport W W (\ S T → el S → el T) X X'' Y Y p' refl g
            = ( \ (x' : el X'') →
                transport W el Y Y refl (g (transport-rev W el X X'' p' x'))))
          ( refl)
          ( X') p)
      ( Y') q
```

## Axiom 5: Crisp induction

### Flat modality

```rzk
#postulate crisp-induction-flat (A :♭ U) (x y :♭ A)
  : ( ♭ ( x = y)) → (mod ♭ x) = (mod ♭ y)

#postulate crisp-induction-flat-rev (A :♭ U) (x y :♭ A)
  : ( ( mod ♭ x) = (mod ♭ y)) → (♭ (x = y))

#postulate crisp-induction-flat-section (A :♭ U) (x y :♭ A)
  ( p : (♭ (x = y)))
  : crisp-induction-flat-rev A x y (crisp-induction-flat A x y p) = p

#postulate crisp-induction-flat-retraction (A :♭ U) (x y :♭ A)
  ( p : (mod ♭ x) = (mod ♭ y))
  : crisp-induction-flat A x y (crisp-induction-flat-rev A x y p) = p

#def crisp-induction-flat-is-equiv (A :♭ U) (x y :♭ A)
  : is-equiv
    ( ♭ ( x = y))
    ( ( mod ♭ x) = (mod ♭ y))
    ( crisp-induction-flat A x y)
  :=
  ( ( crisp-induction-flat-rev A x y
    , crisp-induction-flat-section A x y)
  , ( crisp-induction-flat-rev A x y
    , crisp-induction-flat-retraction A x y))
```

### Sharp modality

```rzk
#postulate crisp-induction-sharp (A :♯ U) (x y :♯ A)
  : ( ♯ ( x = y)) → (mod ♯ x) = (mod ♯ y)

#postulate crisp-induction-sharp-rev (A :♯ U) (x y :♯ A)
  : ( ( mod ♯ x) = (mod ♯ y)) → (♯ (x = y))

#postulate crisp-induction-sharp-section (A :♯ U) (x y :♯ A)
  ( p : (♯ (x = y)))
  : crisp-induction-sharp-rev A x y (crisp-induction-sharp A x y p) = p

#postulate crisp-induction-sharp-retraction (A :♯ U) (x y :♯ A)
  ( p : (mod ♯ x) = (mod ♯ y))
  : crisp-induction-sharp A x y (crisp-induction-sharp-rev A x y p) = p

#def crisp-induction-sharp-is-equiv (A :♯ U) (x y :♯ A)
  : is-equiv
    ( ♯ ( x = y))
    ( ( mod ♯ x) = (mod ♯ y))
    ( crisp-induction-sharp A x y)
  :=
  ( ( crisp-induction-sharp-rev A x y
    , crisp-induction-sharp-section A x y)
  , ( crisp-induction-sharp-rev A x y
    , crisp-induction-sharp-retraction A x y))
```

### Op modality

```rzk
#postulate crisp-induction-op (A :ᵒᵖ U) (x y :ᵒᵖ A)
  : ( ᵒᵖ (x = y)) → (mod ᵒᵖ x) = (mod ᵒᵖ y)

#postulate crisp-induction-op-rev (A :ᵒᵖ U) (x y :ᵒᵖ A)
  : ( ( mod ᵒᵖ x) = (mod ᵒᵖ y)) → (ᵒᵖ (x = y))

#postulate crisp-induction-op-section (A :ᵒᵖ U) (x y :ᵒᵖ A)
  ( p : (ᵒᵖ (x = y)))
  : crisp-induction-op-rev A x y (crisp-induction-op A x y p) = p

#postulate crisp-induction-op-retraction (A :ᵒᵖ U) (x y :ᵒᵖ A)
  ( p : (mod ᵒᵖ x) = (mod ᵒᵖ y))
  : crisp-induction-op A x y (crisp-induction-op-rev A x y p) = p

#def crisp-induction-op-is-equiv (A :ᵒᵖ U) (x y :ᵒᵖ A)
  : is-equiv
    ( ᵒᵖ (x = y))
    ( ( mod ᵒᵖ x) = (mod ᵒᵖ y))
    ( crisp-induction-op A x y)
  :=
  ( ( crisp-induction-op-rev A x y
    , crisp-induction-op-section A x y)
  , ( crisp-induction-op-rev A x y
    , crisp-induction-op-retraction A x y))
```

## Axiom 6: Interval detects discreteness

```rzk
#postulate I-detects-discreteness
  ( A :♭ U)
  : iff (Equiv A (♭ A)) (Equiv A (𝕀 → A))
```

## Axiom 7: Global points of the interval

The discrete interval is equivalent to Bool.

```rzk
#def discrete-I-elim (i :♭ 𝕀) (A : U) (x y : A)
  : A
  :=
  recOR(
    ( i ≡ 0ᵢ) ↦ x
  , ( i ≡ 1ᵢ) ↦ y)
```

## Axiom 8: Cubes separate

```rzk
#def I-power (n : nat) (A : U)
  : U
  := match n
      (zero ⇒ A
      | suc k ih ⇒ 𝕀 → ih)

#postulate cubes-separate (A B :♭ U) (f :♭ A → B)
  : iff (is-equiv A B f) ((n : nat) → Equiv (♭ (I-power n A)) (♭ (I-power n B)))
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
