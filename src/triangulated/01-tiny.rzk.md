# 1. Tiny interval

This is a literate `rzk` file: exponentiation by the interval (`ar`), its right adjoint
(`rar`), transpose/untranspose, and naturality lemmas.

```rzk
#lang rzk-1
```

## Prerequisites

- `hott/04-modalities.rzk.md` — `b-extract`, `b-elim`, `b-naturality`, `b-beta`, `b-map`, `mod ♭`, `_b`.
- `hott/01-paths.rzk.md` — `ap`, `concat`, `rev`.
- `hott/03-equivalences.rzk.md` — `is-equiv`, `Equiv`, `ap-cancel-has-retraction`.

## Right adjoint

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
  := b-elim
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
          ( b-naturality
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
            ( b-beta
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
  := b-elim
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
          ( b-naturality
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
              ( b-naturality
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
