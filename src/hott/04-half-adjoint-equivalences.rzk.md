# 4. Half adjoint equivalences

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Half adjoint equivalences

We'll require a more coherent notion of equivalence. Namely, the notion of
**half adjoint equivalences**.

```rzk
#def is-half-adjoint-equiv
  ( A B : U)
  ( f : A → B)
  : U
  :=
    Σ ( has-inverse-f : (has-inverse A B f))
    , ( ( a : A)
      → ( second (second has-inverse-f) (f a))
      = ( ap A B
          ( retraction-composite-has-inverse A B f has-inverse-f a)
          ( a)
          ( f)
          ( first (second has-inverse-f) a)))
```

By function extensionality, the previous definition coincides with the following
one:

```rzk
#def is-half-adjoint-equiv'
  ( A B : U)
  ( f : A → B)
  : U
  :=
    Σ ( has-inverse-f : (has-inverse A B f))
    , ( ( a : A)
      → ( second (second has-inverse-f) (f a))
      = ( ap A B
          ( retraction-composite-has-inverse A B f has-inverse-f a)
          ( a)
          ( f)
          ( first (second has-inverse-f) a)))
```

## Half adjoint equivalence data

```rzk
#section half-adjoint-equivalence-data

#variables A B : U
#variable f : A → B
#variable is-hae-f : is-half-adjoint-equiv A B f

#def map-inverse-is-half-adjoint-equiv uses (f)
  : B → A
  := map-inverse-has-inverse A B f (first is-hae-f)


#def retraction-htpy-is-half-adjoint-equiv
  : homotopy A A (comp A B A map-inverse-is-half-adjoint-equiv f) (identity A)
  := first (second (first is-hae-f))

#def section-htpy-is-half-adjoint-equiv
  : homotopy B B (comp B A B f map-inverse-is-half-adjoint-equiv) (identity B)
  := second (second (first is-hae-f))

#def coherence-is-half-adjoint-equiv
  ( a : A)
  : section-htpy-is-half-adjoint-equiv (f a)
  = ap A B (map-inverse-is-half-adjoint-equiv (f a)) a f
    ( retraction-htpy-is-half-adjoint-equiv a)
  := (second is-hae-f) a

#end half-adjoint-equivalence-data
```

## Coherence data from an invertible map

To promote an invertible map to a half adjoint equivalence we keep one homotopy
and discard the other.

```rzk
#def has-inverse-kept-htpy
  ( A B : U)
  ( f : A → B)
  ( has-inverse-f : has-inverse A B f)
  : homotopy A A
    ( retraction-composite-has-inverse A B f has-inverse-f) (identity A)
  := (first (second has-inverse-f))

#def has-inverse-discarded-htpy
  ( A B : U)
  ( f : A → B)
  ( has-inverse-f : has-inverse A B f)
  : homotopy B B
    ( section-composite-has-inverse A B f has-inverse-f) (identity B)
  := (second (second has-inverse-f))
```

The required coherence will be built by transforming an instance of the
following naturality square.

```rzk
#section has-inverse-coherence

#variables A B : U
#variable f : A → B
#variable has-inverse-f : has-inverse A B f
#variable a : A

#def has-inverse-discarded-naturality-square
  : concat B
    ( quintuple-composite-has-inverse A B f has-inverse-f a)
    ( triple-composite-has-inverse A B f has-inverse-f a)
    ( f a)
    ( ap A B (retraction-composite-has-inverse A B f has-inverse-f a) a
      ( triple-composite-has-inverse A B f has-inverse-f)
      ( has-inverse-kept-htpy A B f has-inverse-f a))
    ( has-inverse-discarded-htpy A B f has-inverse-f (f a))
  = concat B
    ( quintuple-composite-has-inverse A B f has-inverse-f a)
      ( triple-composite-has-inverse A B f has-inverse-f a)
      ( f a)
      ( has-inverse-discarded-htpy A B f has-inverse-f
        ( triple-composite-has-inverse A B f has-inverse-f a))
      ( ap A B (retraction-composite-has-inverse A B f has-inverse-f a) a
        f (has-inverse-kept-htpy A B f has-inverse-f a))
  :=
    nat-htpy A B
    ( triple-composite-has-inverse A B f has-inverse-f)
    ( f)
    ( \ x → has-inverse-discarded-htpy A B f has-inverse-f (f x))
    ( retraction-composite-has-inverse A B f has-inverse-f a)
    ( a)
    ( has-inverse-kept-htpy A B f has-inverse-f a)
```

We build a path that will be whiskered into the naturality square above:

```rzk
#def has-inverse-cocone-homotopy-coherence
  : has-inverse-kept-htpy A B f has-inverse-f
      ( retraction-composite-has-inverse A B f has-inverse-f a)
  = ap A A (retraction-composite-has-inverse A B f has-inverse-f a) a
      ( retraction-composite-has-inverse A B f has-inverse-f)
      ( has-inverse-kept-htpy A B f has-inverse-f a)
  :=
    cocone-naturality-coherence
      ( A)
      ( retraction-composite-has-inverse A B f has-inverse-f)
      ( has-inverse-kept-htpy A B f has-inverse-f)
      ( a)

#def has-inverse-ap-cocone-homotopy-coherence
  : ap A B
    ( retraction-composite-has-inverse A B f has-inverse-f
      ( retraction-composite-has-inverse A B f has-inverse-f a))
    ( retraction-composite-has-inverse A B f has-inverse-f a)
    ( f)
    ( has-inverse-kept-htpy A B f has-inverse-f
      ( retraction-composite-has-inverse A B f has-inverse-f a))
  = ap A B
    ( retraction-composite-has-inverse A B f has-inverse-f
      ( retraction-composite-has-inverse A B f has-inverse-f a))
    ( retraction-composite-has-inverse A B f has-inverse-f a)
    ( f)
    ( ap A A (retraction-composite-has-inverse A B f has-inverse-f a) a
      ( retraction-composite-has-inverse A B f has-inverse-f)
      ( has-inverse-kept-htpy A B f has-inverse-f a))
  :=
    ap-eq A B
      ( retraction-composite-has-inverse A B f has-inverse-f
        ( retraction-composite-has-inverse A B f has-inverse-f a))
      ( retraction-composite-has-inverse A B f has-inverse-f a)
      ( f)
      ( has-inverse-kept-htpy A B f has-inverse-f
        ( retraction-composite-has-inverse A B f has-inverse-f a))
      ( ap A A (retraction-composite-has-inverse A B f has-inverse-f a) a
        ( retraction-composite-has-inverse A B f has-inverse-f)
        ( has-inverse-kept-htpy A B f has-inverse-f a))
      ( has-inverse-cocone-homotopy-coherence)

#def has-inverse-cocone-coherence
  : ap A B
    ( retraction-composite-has-inverse A B f has-inverse-f
      ( retraction-composite-has-inverse A B f has-inverse-f a))
    ( retraction-composite-has-inverse A B f has-inverse-f a)
    ( f)
    ( has-inverse-kept-htpy A B f has-inverse-f
      ( retraction-composite-has-inverse A B f has-inverse-f a))
  = ( ap A B (retraction-composite-has-inverse A B f has-inverse-f a) a
      ( triple-composite-has-inverse A B f has-inverse-f)
      ( has-inverse-kept-htpy A B f has-inverse-f a))
  :=
    concat
      ( quintuple-composite-has-inverse A B f has-inverse-f a
      = triple-composite-has-inverse A B f has-inverse-f a)
      ( ap A B
        ( retraction-composite-has-inverse A B f has-inverse-f
          ( retraction-composite-has-inverse A B f has-inverse-f a))
        ( retraction-composite-has-inverse A B f has-inverse-f a)
        ( f)
        ( has-inverse-kept-htpy A B f has-inverse-f
          ( retraction-composite-has-inverse A B f has-inverse-f a)))
      ( ap A B
        ( retraction-composite-has-inverse A B f has-inverse-f
          ( retraction-composite-has-inverse A B f has-inverse-f a))
        ( retraction-composite-has-inverse A B f has-inverse-f a)
        ( f)
        ( ap A A
          ( retraction-composite-has-inverse A B f has-inverse-f a) a
          ( retraction-composite-has-inverse A B f has-inverse-f)
          ( has-inverse-kept-htpy A B f has-inverse-f a)))
      ( ap A B (retraction-composite-has-inverse A B f has-inverse-f a) a
        ( triple-composite-has-inverse A B f has-inverse-f)
        ( has-inverse-kept-htpy A B f has-inverse-f a))
      ( has-inverse-ap-cocone-homotopy-coherence)
      ( rev-ap-comp A A B
        ( retraction-composite-has-inverse A B f has-inverse-f a) a
        ( retraction-composite-has-inverse A B f has-inverse-f)
        ( f)
        ( has-inverse-kept-htpy A B f has-inverse-f a))
```

This morally gives the half adjoint inverse coherence. It just requires
rotation.

```rzk
#def has-inverse-replaced-naturality-square
  : concat B
    ( quintuple-composite-has-inverse A B f has-inverse-f a)
    ( triple-composite-has-inverse A B f has-inverse-f a)
    ( f a)
    ( ap A B
      ( retraction-composite-has-inverse A B f has-inverse-f
        ( retraction-composite-has-inverse A B f has-inverse-f a))
      ( retraction-composite-has-inverse A B f has-inverse-f a)
      ( f)
      ( has-inverse-kept-htpy A B f has-inverse-f
        ( retraction-composite-has-inverse A B f has-inverse-f a)))
    ( has-inverse-discarded-htpy A B f has-inverse-f (f a))
  = concat B
    ( quintuple-composite-has-inverse A B f has-inverse-f a)
    ( triple-composite-has-inverse A B f has-inverse-f a)
    ( f a)
    ( has-inverse-discarded-htpy A B f has-inverse-f
      ( triple-composite-has-inverse A B f has-inverse-f a))
    ( ap A B (retraction-composite-has-inverse A B f has-inverse-f a) a f
      ( has-inverse-kept-htpy A B f has-inverse-f a))
  :=
    concat
      ( quintuple-composite-has-inverse A B f has-inverse-f a = f a)
      ( concat B
        ( quintuple-composite-has-inverse A B f has-inverse-f a)
        ( triple-composite-has-inverse A B f has-inverse-f a)
        ( f a)
        ( ap A B
          ( retraction-composite-has-inverse A B f has-inverse-f
            ( retraction-composite-has-inverse A B f has-inverse-f a))
          ( retraction-composite-has-inverse A B f has-inverse-f a) f
          ( has-inverse-kept-htpy A B f has-inverse-f
            ( retraction-composite-has-inverse A B f has-inverse-f a)))
        ( has-inverse-discarded-htpy A B f has-inverse-f (f a)))
      ( concat B
        ( quintuple-composite-has-inverse A B f has-inverse-f a)
        ( triple-composite-has-inverse A B f has-inverse-f a)
        ( f a)
        ( ap A B (retraction-composite-has-inverse A B f has-inverse-f a) a
          ( triple-composite-has-inverse A B f has-inverse-f)
          ( has-inverse-kept-htpy A B f has-inverse-f a))
        ( has-inverse-discarded-htpy A B f has-inverse-f (f a)))
      ( concat B
        ( quintuple-composite-has-inverse A B f has-inverse-f a)
        ( triple-composite-has-inverse A B f has-inverse-f a) (f a)
        ( has-inverse-discarded-htpy A B f has-inverse-f
          ( triple-composite-has-inverse A B f has-inverse-f a))
        ( ap A B (retraction-composite-has-inverse A B f has-inverse-f a) a f
          ( has-inverse-kept-htpy A B f has-inverse-f a)))
      ( concat-eq-left B
        ( quintuple-composite-has-inverse A B f has-inverse-f a)
        ( triple-composite-has-inverse A B f has-inverse-f a)
        ( f a)
        ( ap A B
          ( retraction-composite-has-inverse A B f has-inverse-f
            ( retraction-composite-has-inverse A B f has-inverse-f a))
          ( retraction-composite-has-inverse A B f has-inverse-f a)
          ( f)
          ( has-inverse-kept-htpy A B f has-inverse-f
            ( retraction-composite-has-inverse A B f has-inverse-f a)))
        ( ap A B (retraction-composite-has-inverse A B f has-inverse-f a) a
          ( triple-composite-has-inverse A B f has-inverse-f)
          ( has-inverse-kept-htpy A B f has-inverse-f a))
        ( has-inverse-cocone-coherence)
        ( has-inverse-discarded-htpy A B f has-inverse-f (f a)))
      ( has-inverse-discarded-naturality-square)
```

This will replace the discarded homotopy.

```rzk
#def has-inverse-corrected-htpy
  : homotopy B B (section-composite-has-inverse A B f has-inverse-f) (\ b → b)
  :=
    \ b →
      concat B
        ( ( section-composite-has-inverse A B f has-inverse-f) b)
        ( ( section-composite-has-inverse A B f has-inverse-f)
          ( ( section-composite-has-inverse A B f has-inverse-f) b))
        ( b)
        ( rev B
          ( ( section-composite-has-inverse A B f has-inverse-f)
            ( ( section-composite-has-inverse A B f has-inverse-f) b))
          ( ( section-composite-has-inverse A B f has-inverse-f) b)
          ( has-inverse-discarded-htpy A B f has-inverse-f
            ( ( section-composite-has-inverse A B f has-inverse-f) b)))
        ( concat B
          ( ( section-composite-has-inverse A B f has-inverse-f)
            ( ( section-composite-has-inverse A B f has-inverse-f) b))
          ( ( section-composite-has-inverse A B f has-inverse-f) b)
          ( b)
          ( ap A B
            ( ( retraction-composite-has-inverse A B f has-inverse-f)
              ( map-inverse-has-inverse A B f has-inverse-f b))
            ( map-inverse-has-inverse A B f has-inverse-f b) f
            ( ( first (second has-inverse-f))
              ( map-inverse-has-inverse A B f has-inverse-f b)))
          ( ( has-inverse-discarded-htpy A B f has-inverse-f b)))
```

The following is the half adjoint coherence.

```rzk
#def has-inverse-coherence
  : ( has-inverse-corrected-htpy (f a))
  = ( ap A B (retraction-composite-has-inverse A B f has-inverse-f a) a f
      ( has-inverse-kept-htpy A B f has-inverse-f a))
  :=
    triangle-rotation B
      ( quintuple-composite-has-inverse A B f has-inverse-f a)
      ( triple-composite-has-inverse A B f has-inverse-f a)
      ( f a)
      ( concat B
        ( ( section-composite-has-inverse A B f has-inverse-f)
          ( ( section-composite-has-inverse A B f has-inverse-f) (f a)))
        ( ( section-composite-has-inverse A B f has-inverse-f) (f a))
        ( f a)
        ( ap A B
          ( ( retraction-composite-has-inverse A B f has-inverse-f)
            ( map-inverse-has-inverse A B f has-inverse-f (f a)))
          ( map-inverse-has-inverse A B f has-inverse-f (f a))
            ( f)
            ( ( first (second has-inverse-f))
              ( map-inverse-has-inverse A B f has-inverse-f (f a))))
        ( ( has-inverse-discarded-htpy A B f has-inverse-f (f a))))
      ( has-inverse-discarded-htpy A B f has-inverse-f
        ( triple-composite-has-inverse A B f has-inverse-f a))
      ( ap A B (retraction-composite-has-inverse A B f has-inverse-f a) a f
        ( has-inverse-kept-htpy A B f has-inverse-f a))
      ( has-inverse-replaced-naturality-square)
```

```rzk
#end has-inverse-coherence
```

## Invertible maps are half adjoint equivalences

To promote an invertible map to a half adjoint equivalence we change the data of
the invertible map by discarding the homotopy and replacing it with a corrected
one.

```rzk
#def corrected-has-inverse-has-inverse
  ( A B : U)
  ( f : A → B)
  ( has-inverse-f : has-inverse A B f)
  : has-inverse A B f
  :=
    ( map-inverse-has-inverse A B f has-inverse-f
    , ( has-inverse-kept-htpy A B f has-inverse-f
      , has-inverse-corrected-htpy A B f has-inverse-f))
```

```rzk title="Invertible maps are half adjoint equivalences!"
#def is-half-adjoint-equiv-has-inverse
  ( A B : U)
  ( f : A → B)
  ( has-inverse-f : has-inverse A B f)
  : is-half-adjoint-equiv A B f
  :=
    ( corrected-has-inverse-has-inverse A B f has-inverse-f
    , has-inverse-coherence A B f has-inverse-f)
```

```rzk title="Equivalences are half adjoint equivalences!"
#def is-half-adjoint-equiv-is-equiv
  ( A B : U)
  ( f : A → B)
  ( is-equiv-f : is-equiv A B f)
  : is-half-adjoint-equiv A B f
  :=
    is-half-adjoint-equiv-has-inverse A B f
      ( has-inverse-is-equiv A B f is-equiv-f)
```

## Equivalences are embeddings

We use the notion of half adjoint equivalence to prove that equivalent types
have equivalent identity types by showing that equivalences are embeddings.

```rzk
#section equiv-identity-types-equiv

#variables A B : U
#variable f : A → B
#variable is-hae-f : is-half-adjoint-equiv A B f

#def iff-ap-is-half-adjoint-equiv
  ( x y : A)
  : iff (x = y) (f x = f y)
  :=
    ( ap A B x y f
    , \ q →
      triple-concat A
        ( x)
        ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f x))
        ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f y))
        ( y)
        ( rev A (retraction-composite-has-inverse A B f (first is-hae-f) x) x
          ( ( first (second (first is-hae-f))) x))
        ( ap B A (f x) (f y) (map-inverse-has-inverse A B f (first is-hae-f)) q)
        ( ( first (second (first is-hae-f))) y))

#def has-retraction-ap-is-half-adjoint-equiv
  ( x y : A)
  : has-retraction (x = y) (f x = f y) (ap A B x y f)
  :=
    ( ( second (iff-ap-is-half-adjoint-equiv x y))
    , ( ind-path
          ( A)
          ( x)
          ( \ y' p' →
            ( second (iff-ap-is-half-adjoint-equiv x y')) (ap A B x y' f p')
          = ( p'))
          ( rev-refl-id-triple-concat A
            ( map-inverse-has-inverse A B f (first is-hae-f) (f x))
            ( x)
            ( first (second (first is-hae-f)) x))
          ( y)))

#def ap-triple-concat-is-half-adjoint-equiv
  ( x y : A)
  ( q : f x = f y)
  : ap A B x y f ((second (iff-ap-is-half-adjoint-equiv x y)) q)
  = ( triple-concat B
      ( f x)
      ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f x)))
      ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f y)))
      ( f y)
      ( ap A B x ((map-inverse-has-inverse A B f (first is-hae-f)) (f x)) f
        ( rev A (retraction-composite-has-inverse A B f (first is-hae-f) x) x
          ( ( first (second (first is-hae-f))) x)))
      ( ap A B
        ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f x))
        ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f y))
        ( f)
        ( ap B A (f x) (f y) (map-inverse-has-inverse A B f (first is-hae-f)) q))
      ( ap A B ((map-inverse-has-inverse A B f (first is-hae-f)) (f y)) y f
        ( ( first (second (first is-hae-f))) y)))
  :=
    ap-triple-concat A B
      ( x)
      ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f x))
      ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f y))
      ( y)
      ( f)
      ( rev A (retraction-composite-has-inverse A B f (first is-hae-f) x) x
        ( ( first (second (first is-hae-f))) x))
      ( ap B A (f x) (f y) (map-inverse-has-inverse A B f (first is-hae-f)) q)
      ( ( first (second (first is-hae-f))) y)

#def ap-rev-triple-concat-eq-first-is-half-adjoint-equiv
  ( x y : A)
  ( q : f x = f y)
  : triple-concat B
    ( f x)
    ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f x)))
    ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f y)))
    ( f y)
    ( ap A B x ((map-inverse-has-inverse A B f (first is-hae-f)) (f x)) f
      ( rev A (retraction-composite-has-inverse A B f (first is-hae-f) x) x
        ( ( first (second (first is-hae-f))) x)))
    ( ap A B
      ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f x))
      ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f y))
      ( f)
      ( ap B A (f x) (f y) (map-inverse-has-inverse A B f (first is-hae-f)) q))
    ( ap A B ((map-inverse-has-inverse A B f (first is-hae-f)) (f y)) y f
      ( ( first (second (first is-hae-f))) y))
  = triple-concat B
    ( f x)
    ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f x)))
    ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f y)))
    ( f y)
    ( rev B (f (retraction-composite-has-inverse A B f (first is-hae-f) x)) (f x)
      ( ap A B ((map-inverse-has-inverse A B f (first is-hae-f)) (f x)) x f
        ( ( first (second (first is-hae-f))) x)))
    ( ap A B
      ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f x))
      ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f y))
      ( f)
      ( ap B A (f x) (f y) (map-inverse-has-inverse A B f (first is-hae-f)) q))
    ( ap A B
      ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f y))
      ( y)
      ( f)
      ( ( first (second (first is-hae-f))) y))
  :=
    triple-concat-eq-first B
    ( f x)
    ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f x)))
    ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f y)))
    ( f y)
    ( ap A B
      ( x) ((map-inverse-has-inverse A B f (first is-hae-f)) (f x)) f
      ( rev A (retraction-composite-has-inverse A B f (first is-hae-f) x) x
        ( ( first (second (first is-hae-f))) x)))
    ( rev B (f (retraction-composite-has-inverse A B f (first is-hae-f) x)) (f x)
      ( ap A B ((map-inverse-has-inverse A B f (first is-hae-f)) (f x)) x f
        ( ( first (second (first is-hae-f))) x)))
    ( ap A B
      ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f x))
      ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f y))
      ( f)
      ( ap B A (f x) (f y) (map-inverse-has-inverse A B f (first is-hae-f)) q))
    ( ap A B ((map-inverse-has-inverse A B f (first is-hae-f)) (f y)) y f
      ( ( first (second (first is-hae-f))) y))
    ( ap-rev A B (retraction-composite-has-inverse A B f (first is-hae-f) x) x f
      ( ( first (second (first is-hae-f))) x))

#def ap-ap-triple-concat-eq-first-is-half-adjoint-equiv
  ( x y : A)
  ( q : f x = f y)
  : ( triple-concat B
      ( f x)
      ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f x)))
      ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f y)))
      ( f y)
      ( rev B
        ( f (retraction-composite-has-inverse A B f (first is-hae-f) x))
        ( f x)
        ( ap A B
          ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f x)) x f
          ( ( first (second (first is-hae-f))) x)))
      ( ap A B
        ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f x))
        ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f y))
        ( f)
        ( ap B A (f x) (f y) (map-inverse-has-inverse A B f (first is-hae-f)) q))
      ( ap A B ((map-inverse-has-inverse A B f (first is-hae-f)) (f y)) y f
        ( ( first (second (first is-hae-f))) y)))
  = ( triple-concat B
      ( f x)
      ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f x)))
      ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f y)))
      ( f y)
      ( rev B
        ( f (retraction-composite-has-inverse A B f (first is-hae-f) x)) (f x)
        ( ap A B ((map-inverse-has-inverse A B f (first is-hae-f)) (f x)) x f
          ( ( first (second (first is-hae-f))) x)))
      ( ap B B (f x) (f y)
        ( section-composite-has-inverse A B f (first is-hae-f)) q)
      ( ap A B ((map-inverse-has-inverse A B f (first is-hae-f)) (f y)) y
        ( f) ((first (second (first is-hae-f))) y)))
  :=
    triple-concat-eq-second B
      ( f x)
      ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f x)))
      ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f y)))
      ( f y)
      ( rev B (f (retraction-composite-has-inverse A B f (first is-hae-f) x)) (f x)
        ( ap A B ((map-inverse-has-inverse A B f (first is-hae-f)) (f x)) x f
          ( ( first (second (first is-hae-f))) x)))
      ( ap A B
        ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f x))
        ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f y))
        ( f)
        ( ap B A (f x) (f y) (map-inverse-has-inverse A B f (first is-hae-f)) q))
      ( ap B B (f x) (f y) (section-composite-has-inverse A B f (first is-hae-f)) q)
      ( ap A B ((map-inverse-has-inverse A B f (first is-hae-f)) (f y)) y f
        ( ( first (second (first is-hae-f))) y))
      ( rev-ap-comp B A B (f x) (f y)
        ( map-inverse-has-inverse A B f (first is-hae-f)) f q)

-- This needs to be reversed later.
#def triple-concat-higher-homotopy-is-half-adjoint-equiv
  ( x y : A)
  ( q : f x = f y)
  : triple-concat B
      ( f x)
      ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f x)))
      ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f y)))
      ( f y)
      ( rev B (f (retraction-composite-has-inverse A B f (first is-hae-f) x)) (f x)
        ( ( second (second (first is-hae-f))) (f x)))
      ( ap B B (f x) (f y)
        ( section-composite-has-inverse A B f (first is-hae-f)) q)
      ( ( second (second (first is-hae-f))) (f y))
  = triple-concat B
      ( f x)
      ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f x)))
      ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f y)))
      ( f y)
      ( rev B (f (retraction-composite-has-inverse A B f (first is-hae-f) x)) (f x)
        ( ap A B ((map-inverse-has-inverse A B f (first is-hae-f)) (f x)) x f ((first (second (first is-hae-f))) x)))
        ( ap B B (f x) (f y) (section-composite-has-inverse A B f (first is-hae-f)) q)
        ( ap A B ((map-inverse-has-inverse A B f (first is-hae-f)) (f y)) y f ((first (second (first is-hae-f))) y))
  :=
    triple-concat-higher-homotopy A B
      ( triple-composite-has-inverse A B f (first is-hae-f)) f
      ( \ a → (((second (second (first is-hae-f)))) (f a)))
      ( \ a →
        ( ap A B (retraction-composite-has-inverse A B f (first is-hae-f) a) a f
          ( ( ( first (second (first is-hae-f)))) a)))
      ( second is-hae-f)
      ( x)
      ( y)
      ( ap B B (f x) (f y)
        ( section-composite-has-inverse A B f (first is-hae-f)) q)

#def triple-concat-nat-htpy-is-half-adjoint-equiv
  ( x y : A)
  ( q : f x = f y)
  : triple-concat B
    ( f x)
    ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f x)))
    ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f y)))
    ( f y)
    ( rev B (f (retraction-composite-has-inverse A B f (first is-hae-f) x)) (f x)
      ( ( ( second (second (first is-hae-f)))) (f x)))
    ( ap B B (f x) (f y) (section-composite-has-inverse A B f (first is-hae-f)) q)
    ( ( ( second (second (first is-hae-f)))) (f y))
    = ap B B (f x) (f y) (identity B) q
  :=
    triple-concat-nat-htpy B B
      ( section-composite-has-inverse A B f (first is-hae-f))
      ( identity B)
      ( ( second (second (first is-hae-f))))
      ( f x)
      ( f y)
      q

#def zag-zig-concat-triple-concat-is-half-adjoint-equiv
  ( x y : A)
  ( q : f x = f y)
  : triple-concat B
    ( f x)
    ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f x)))
    ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f y)))
    ( f y)
    ( rev B (f (retraction-composite-has-inverse A B f (first is-hae-f) x)) (f x)
      ( ap A B ((map-inverse-has-inverse A B f (first is-hae-f)) (f x)) x f
        ( ( first (second (first is-hae-f))) x)))
    ( ap B B (f x) (f y) (section-composite-has-inverse A B f (first is-hae-f)) q)
    ( ap A B ((map-inverse-has-inverse A B f (first is-hae-f)) (f y)) y f
      ( ( first (second (first is-hae-f))) y))
  = ap B B (f x) (f y) (identity B) q
  :=
    zag-zig-concat (f x = f y)
      ( triple-concat B
        ( f x)
        ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f x)))
        ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f y)))
        ( f y)
        ( rev B
          ( f (retraction-composite-has-inverse A B f (first is-hae-f) x)) (f x)
          ( ap A B ((map-inverse-has-inverse A B f (first is-hae-f)) (f x)) x f
            ( ( first (second (first is-hae-f))) x)))
        ( ap B B (f x) (f y)
          ( section-composite-has-inverse A B f (first is-hae-f)) q)
        ( ap A B ((map-inverse-has-inverse A B f (first is-hae-f)) (f y)) y
          f ((first (second (first is-hae-f))) y)))
      ( triple-concat B
        ( f x)
        ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f x)))
        ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f y)))
        ( f y)
        ( rev B
          ( f (retraction-composite-has-inverse A B f (first is-hae-f) x))
          ( f x)
          ( ( ( second (second (first is-hae-f)))) (f x)))
        ( ap B B (f x) (f y)
          ( section-composite-has-inverse A B f (first is-hae-f)) q)
        ( ( ( second (second (first is-hae-f)))) (f y)))
      ( ap B B (f x) (f y) (identity B) q)
      ( triple-concat-higher-homotopy-is-half-adjoint-equiv x y q)
      ( triple-concat-nat-htpy-is-half-adjoint-equiv x y q)

#def triple-concat-reduction-is-half-adjoint-equiv
  ( x y : A)
  ( q : f x = f y)
  : ap B B (f x) (f y) (identity B) q = q
  := ap-id B (f x) (f y) q

#def section-htpy-ap-is-half-adjoint-equiv
  ( x y : A)
  ( q : f x = f y)
  : ap A B x y f ((second (iff-ap-is-half-adjoint-equiv x y)) q) = q
  :=
    alternating-quintuple-concat (f x = f y)
      ( ap A B x y f ((second (iff-ap-is-half-adjoint-equiv x y)) q))
      ( triple-concat B
        ( f x)
        ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f x)))
        ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f y)))
        ( f y)
        ( ap A B x ((map-inverse-has-inverse A B f (first is-hae-f)) (f x)) f
          ( rev A (retraction-composite-has-inverse A B f (first is-hae-f) x) x
            ( ( first (second (first is-hae-f))) x)))
        ( ap A B
          ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f x))
          ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f y)) f
          ( ap B A (f x) (f y) (map-inverse-has-inverse A B f (first is-hae-f)) q))
        ( ap A B ((map-inverse-has-inverse A B f (first is-hae-f)) (f y)) y f
          ( ( first (second (first is-hae-f))) y)))
      ( ap-triple-concat-is-half-adjoint-equiv x y q)
      ( triple-concat B
        ( f x)
        ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f x)))
        ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f y)))
        ( f y)
        ( rev B
          ( f (retraction-composite-has-inverse A B f (first is-hae-f) x)) (f x)
          ( ap A B ((map-inverse-has-inverse A B f (first is-hae-f)) (f x)) x f
            ( ( first (second (first is-hae-f))) x)))
        ( ap A B
          ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f x))
          ( ( map-inverse-has-inverse A B f (first is-hae-f)) (f y)) f
          ( ap B A (f x) (f y) (map-inverse-has-inverse A B f (first is-hae-f)) q))
        ( ap A B ((map-inverse-has-inverse A B f (first is-hae-f)) (f y)) y f
          ( ( first (second (first is-hae-f))) y)))
      ( ap-rev-triple-concat-eq-first-is-half-adjoint-equiv x y q)
      ( triple-concat B
        ( f x)
        ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f x)))
        ( f ((map-inverse-has-inverse A B f (first is-hae-f)) (f y)))
        ( f y)
        ( rev B
          ( f (retraction-composite-has-inverse A B f (first is-hae-f) x))
          ( f x)
          ( ap A B ((map-inverse-has-inverse A B f (first is-hae-f)) (f x)) x f
            ( ( first (second (first is-hae-f))) x)))
        ( ap B B (f x) (f y)
          ( section-composite-has-inverse A B f (first is-hae-f)) q)
        ( ap A B ((map-inverse-has-inverse A B f (first is-hae-f)) (f y)) y
          f ((first (second (first is-hae-f))) y)))
      ( ap-ap-triple-concat-eq-first-is-half-adjoint-equiv x y q)
      ( ap B B (f x) (f y) (identity B) q)
      ( zag-zig-concat-triple-concat-is-half-adjoint-equiv x y q)
      ( q)
      ( triple-concat-reduction-is-half-adjoint-equiv x y q)

#def has-section-ap-is-half-adjoint-equiv uses (is-hae-f)
  ( x y : A)
  : has-section (x = y) (f x = f y) (ap A B x y f)
  :=
    ( second (iff-ap-is-half-adjoint-equiv x y)
    , section-htpy-ap-is-half-adjoint-equiv x y)

#def is-equiv-ap-is-half-adjoint-equiv uses (is-hae-f)
  ( x y : A)
  : is-equiv (x = y) (f x = f y) (ap A B x y f)
  :=
    ( has-retraction-ap-is-half-adjoint-equiv x y
    , has-section-ap-is-half-adjoint-equiv x y)

#end equiv-identity-types-equiv

#def is-emb-is-equiv
  ( A B : U)
  ( f : A → B)
  ( is-equiv-f : is-equiv A B f)
  : is-emb A B f
  :=
    is-equiv-ap-is-half-adjoint-equiv A B f
    ( is-half-adjoint-equiv-is-equiv A B f is-equiv-f)

#def emb-is-equiv
  ( A B : U)
  ( f : A → B)
  ( is-equiv-f : is-equiv A B f)
  : Emb A B
  := (f , is-emb-is-equiv A B f is-equiv-f)

#def equiv-ap-is-equiv
  ( A B : U)
  ( f : A → B)
  ( is-equiv-f : is-equiv A B f)
  ( x y : A)
  : Equiv (x = y) (f x = f y)
  := (ap A B x y f , is-emb-is-equiv A B f is-equiv-f x y)
```

## Some further useful coherences

We prove some further coherences from half-adjoint equivalences. Some of the
lemmas below resemble lemmas from the section on embeddings.

For a half-adjoint equivalence $f$ with inverse $g$ and coherence
$G ⋅ f ∼ \text{ap}_f ⋅ H$ we show

$$
\text{ap}_f (H^{-1} a) ⋅ G (f a) = \texttt{refl}_{f (a)}.
$$

This is a consequence of cancelling the coherence on the left, and then applying
the equality $\text{ap}_f (H^{-1} a) = (\text{ap}_f (H a))^{-1}$. It is
cumbersome to state and prove only becaues of data revtrieval and the number of
reversals.

```rzk
#def ap-rev-retr-htpy-concat-sec-htpy-is-refl-is-hae
  ( A B : U)
  ( f : A → B)
  ( a : A)
  ( b : B)
  ( q : (f a) = b)
  ( is-hae : is-half-adjoint-equiv A B f)
  : ( concat (B)
      ( f a)
      ( f ((map-inverse-is-half-adjoint-equiv  A B f is-hae) (f a)))
      ( f a)
      ( ap (A) (B)
        ( a)
        ( ( ( map-inverse-is-half-adjoint-equiv A B f is-hae) (f a)))
        ( f)
        ( rev (A)
          ( ( map-inverse-is-half-adjoint-equiv A B f is-hae) (f a))
          ( a)
          ( ( retraction-htpy-is-half-adjoint-equiv A B f is-hae) a)))
      ( ( section-htpy-is-half-adjoint-equiv A B f is-hae) (f a)))
      = refl
  :=
  htpy-id-cancel-left-concat-left-eq
  ( B)
  ( f a)
  ( f ((map-inverse-is-half-adjoint-equiv A B f is-hae) (f a)))
  ( ap (A) (B)
    ( a)
    ( ( map-inverse-is-half-adjoint-equiv A B f is-hae) (f a))
    ( f)
    ( rev (A)
      ( ( ( map-inverse-is-half-adjoint-equiv A B f is-hae) (f a)))
      ( a)
      ( ( retraction-htpy-is-half-adjoint-equiv A B f is-hae) a)))
  ( rev (B)
    ( f ((map-inverse-is-half-adjoint-equiv A B f is-hae) (f a)))
    ( f a)
    ( ap (A) (B)
      ( ( map-inverse-is-half-adjoint-equiv A B f is-hae) (f a))
      ( a)
      ( f)
      ( ( retraction-htpy-is-half-adjoint-equiv A B f is-hae) a)))
  ( ap-rev (A) (B)
    ( ( ( map-inverse-is-half-adjoint-equiv A B f is-hae) (f a)))
    ( a)
    ( f)
    ( ( retraction-htpy-is-half-adjoint-equiv A B f is-hae) a))
  ( ( section-htpy-is-half-adjoint-equiv A B f is-hae) (f a))
  ( cancel-left-path
    ( B)
    ( f ((map-inverse-is-half-adjoint-equiv A B f is-hae) (f a)))
    ( f a)
    ( ( section-htpy-is-half-adjoint-equiv A B f is-hae) (f a))
    ( ( ap A B ((map-inverse-is-half-adjoint-equiv A B f is-hae) (f a)) a f
        ( ( retraction-htpy-is-half-adjoint-equiv A B f is-hae) a)))
    ( ( ( coherence-is-half-adjoint-equiv A B f is-hae) a)))
```

Let $f : A → B$ be an equivalence between $A$ and $B$. We prove that

$$
\text{ap}_f (H^-1 (a)) ⋅ \text{ap}_{f ∘ g} (q) ⋅ G (b) = q
$$

This expresses a relatively natural statement that if we start with
$q: f (a) = b$, apply $g$ to get $\text{ap}_g (q) : g (f (a)) = g(b)$,
precompose with $H (a)$ to get

$$
a = g(f(a)) = g(b)
$$

apply $g$ and then postcompose with $G : f (g (b)) = b$, the resulting path
$f(a) = b$ is equal to $q$.

An alternate proof could use `triple-concat-eq-first` and
`triple-concat-nat-htpy`. The proofs do not end up much shorter.

```rzk
#def id-conjugate-is-hae-ap-ap-is-hae
  ( A B : U)
  ( f : A → B)
  ( a : A)
  ( b : B)
  ( q : (f a) = b)
  ( is-hae : is-half-adjoint-equiv A B f)
  : ( concat (B)
    ( f a)
    ( f ((map-inverse-is-half-adjoint-equiv A B f is-hae) (b)))
    ( b)
    ( concat (B)
      ( f a)
      ( f ((map-inverse-is-half-adjoint-equiv A B f is-hae) (f a)))
      ( f ((map-inverse-is-half-adjoint-equiv A B f is-hae) b))
      ( ap (A) (B) (a)
        ( ( map-inverse-is-half-adjoint-equiv A B f is-hae) (f a))
        ( f)
        ( rev (A)
          ( ( map-inverse-is-half-adjoint-equiv A B f is-hae) (f a))
          ( a)
          ( ( retraction-htpy-is-half-adjoint-equiv A B f is-hae) a)))
      ( ap (B) (B) (f a) (b)
        ( \ z → (f ((map-inverse-is-half-adjoint-equiv A B f is-hae) z)))
        ( q)))
    ( ( section-htpy-is-half-adjoint-equiv A B f is-hae) (b))) = q
  :=
  concat
  ( ( f a) = b)
  ( ( concat (B)
    ( f a)
    ( f ((map-inverse-is-half-adjoint-equiv A B f is-hae) (b)))
    ( b)
    ( concat (B)
      ( f a)
      ( f ((map-inverse-is-half-adjoint-equiv A B f is-hae) (f a)))
      ( f ((map-inverse-is-half-adjoint-equiv A B f is-hae) b))
      ( ap (A) (B) (a)
        ( ( map-inverse-is-half-adjoint-equiv A B f is-hae) (f a))
        ( f)
        ( rev (A)
          ( ( map-inverse-is-half-adjoint-equiv A B f is-hae) (f a))
          ( a)
          ( ( retraction-htpy-is-half-adjoint-equiv A B f is-hae) a)))
      ( ap (B) (B) (f a) (b)
        ( \ z → (f ((map-inverse-is-half-adjoint-equiv A B f is-hae) z)))
        ( q)))
    ( ( section-htpy-is-half-adjoint-equiv A B f is-hae) (b))))
  ( ( ap B B (f a) b (identity B) q))
  ( q)
  ( rev-eq-top-cancel-commutative-square'
    ( B)
    ( f a)
    ( f ((map-inverse-is-half-adjoint-equiv A B f is-hae) (f a)))
    ( f ((map-inverse-is-half-adjoint-equiv A B f is-hae)  b))
    ( b)
    ( ap (A) (B)
      ( a)
      ( ( map-inverse-is-half-adjoint-equiv A B f is-hae) (f a))
      ( f)
      ( rev (A)
        ( ( map-inverse-is-half-adjoint-equiv A B f is-hae) (f a))
        ( a)
        ( ( retraction-htpy-is-half-adjoint-equiv A B f is-hae) a)))
    ( ( section-htpy-is-half-adjoint-equiv A B f is-hae) (f a))
    ( ap (B) (B) (f a) (b)
      ( \ z → (f ((map-inverse-is-half-adjoint-equiv A B f is-hae) z)))
      ( q))
    ( ap B B (f a) b (identity B) q)
    ( ( section-htpy-is-half-adjoint-equiv A B f is-hae) b)
    ( rev-nat-htpy (B) (B)
      ( \ x → f ((map-inverse-is-half-adjoint-equiv A B f is-hae) (x)))
      ( identity B)
      ( section-htpy-is-half-adjoint-equiv A B f is-hae)
      ( f a)
      ( b)
      ( q))
    ( ap-rev-retr-htpy-concat-sec-htpy-is-refl-is-hae A B f a b q is-hae))
  ( ap-id B (f a) b q)
```
