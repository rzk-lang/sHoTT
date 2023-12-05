# 7. Fibers

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Fibers

The homotopy fiber of a map is the following type:

```rzk title="The fiber of a map"
#def fib
  ( A B : U)
  ( f : A → B)
  ( b : B)
  : U
  := Σ (a : A) , (f a) = b

#def rev-fib
  ( A B : U)
  ( f : A → B)
  ( b : B)
  : U
  := Σ (a : A) , b = (f a)
```

We calculate the transport of `#!rzk (a , q) : fib b` along `#!rzk p : a = a'`:

```rzk
#def transport-in-fiber
  ( A B : U)
  ( f : A → B)
  ( b : B)
  ( a a' : A)
  ( u : (f a) = b)
  ( p : a = a')
  : ( transport A (\ x → (f x) = b) a a' p u)
  = ( concat B (f a') (f a) b (ap A B a' a f (rev A a a' p)) u)
  :=
    ind-path
      ( A)
      ( a)
      ( \ a'' p' →
        ( transport (A) (\ x → (f x) = b) (a) (a'') (p') (u))
      = ( concat (B) (f a'') (f a) (b) (ap A B a'' a f (rev A a a'' p')) (u)))
      ( rev
        ( ( f a) = b) (concat B (f a) (f a) b refl u) (u)
        ( left-unit-concat B (f a) b u))
      ( a')
      ( p)
```

### Induction principle for fibers

The family of fibers has the following induction principle: To prove/construct
something about/for every point in every fiber, it suffices to do so for points
of the form `#!rzk (a, refl : f a = f a) : fib A B f`.

```rzk
#def ind-fib
  ( A B : U)
  ( f : A → B)
  ( C : (b : B) → fib A B f b → U)
  ( s : (a : A) → C (f a) (a , refl))
  ( b : B)
  ( ( a , q) : fib A B f b)
  : C b (a , q)
  :=
    ind-path B (f a) (\ b p → C b (a , p)) (s a) b q

#def ind-rev-fib
  ( A B : U)
  ( f : A → B)
  ( C : (b : B) → rev-fib A B f b → U)
  ( s : (a : A) → C (f a) (a , refl))
  ( b : B)
  ( ( a , q) : rev-fib A B f b)
  : C b (a , q)
  :=
    ind-path-end B (f a) (\ b p → C b (a , p)) (s a) b q

#def compute-ind-fib
  ( A B : U)
  ( f : A → B)
  ( C : (b : B) → fib A B f b → U)
  ( s : (a : A) → C (f a) (a , refl))
  ( a : A)
  : ind-fib A B f C s (f a) (a , refl) = s a
  := refl
```

## Contractible maps

A map is contractible just when its fibers are contractible.

```rzk title="Contractible maps"
#def is-contr-map
  ( A B : U)
  ( f : A → B)
  : U
  := (b : B) → is-contr (fib A B f b)
```

### Contractible maps are equivalences

Contractible maps are equivalences:

```rzk
#section is-equiv-is-contr-map

#variables A B : U
#variable f : A → B
#variable is-contr-f : is-contr-map A B f
```

```rzk title="The inverse to a contractible map"
#def is-contr-map-inverse
  : B → A
  := \ b → first (center-contraction (fib A B f b) (is-contr-f b))

#def has-section-is-contr-map
  : has-section A B f
  :=
    ( is-contr-map-inverse
    , \ b → second (center-contraction (fib A B f b) (is-contr-f b)))

#def is-contr-map-data-in-fiber uses (is-contr-f)
  ( a : A)
  : fib A B f (f a)
  := (is-contr-map-inverse (f a) , (second has-section-is-contr-map) (f a))

#def is-contr-map-path-in-fiber
  ( a : A)
  : ( is-contr-map-data-in-fiber a) =_{fib A B f (f a)} (a , refl)
  :=
    all-elements-equal-is-contr
      ( fib A B f (f a))
      ( is-contr-f (f a))
      ( is-contr-map-data-in-fiber a)
      ( a , refl)

#def is-contr-map-has-retraction uses (is-contr-f)
  : has-retraction A B f
  :=
    ( is-contr-map-inverse
    , \ a → (ap (fib A B f (f a)) A
                ( is-contr-map-data-in-fiber a)
                ( ( a , refl))
                ( \ u → first u)
                ( is-contr-map-path-in-fiber a)))

#def is-equiv-is-contr-map uses (is-contr-f)
  : is-equiv A B f
  := (is-contr-map-has-retraction , has-section-is-contr-map)

#end is-equiv-is-contr-map
```

### Half adjoint equivalences are contractible maps

We prove the converse by fiber induction. To define the contracting homotopy to
the point `#!rzk (f a, refl)` in the fiber over `#!rzk f a` we find it easier to
work from the assumption that `f` is a half adjoint equivalence.

```rzk
#section is-contr-map-is-equiv

#variables A B : U
#variable f : A → B
#variable is-hae-f : is-half-adjoint-equiv A B f

#def is-split-surjection-is-half-adjoint-equiv
  ( b : B)
  : fib A B f b
  :=
    ( map-inverse-is-half-adjoint-equiv A B f is-hae-f b
    , section-htpy-is-half-adjoint-equiv A B f is-hae-f b)

#def calculate-is-split-surjection-is-half-adjoint-equiv
  ( a : A)
  : is-split-surjection-is-half-adjoint-equiv (f a) = (a , refl)
  :=
    path-of-pairs-pair-of-paths
    ( A)
    ( \ a' → f a' = f a)
    ( map-inverse-is-half-adjoint-equiv A B f is-hae-f (f a))
    ( a)
    ( retraction-htpy-is-half-adjoint-equiv A B f is-hae-f a)
    ( section-htpy-is-half-adjoint-equiv A B f is-hae-f (f a))
    ( refl)
    ( triple-concat
      ( f a = f a)
      ( transport A (\ x → (f x) = (f a))
        ( map-inverse-is-half-adjoint-equiv A B f is-hae-f (f a))
        ( a)
        ( retraction-htpy-is-half-adjoint-equiv A B f is-hae-f a)
        ( section-htpy-is-half-adjoint-equiv A B f is-hae-f (f a)))
      ( concat B
        ( f a)
        ( f (map-inverse-is-half-adjoint-equiv A B f is-hae-f (f a)))
        ( f a)
        ( ap A B
          ( a)
          ( map-inverse-is-half-adjoint-equiv A B f is-hae-f (f a))
          ( f)
          ( rev A (map-inverse-is-half-adjoint-equiv A B f is-hae-f (f a)) a
            ( retraction-htpy-is-half-adjoint-equiv A B f is-hae-f a)))
        ( section-htpy-is-half-adjoint-equiv A B f is-hae-f (f a)))
      ( concat B
        ( f a)
        ( f (map-inverse-is-half-adjoint-equiv A B f is-hae-f (f a)))
        ( f a)
        ( ap A B
          ( a)
          ( map-inverse-is-half-adjoint-equiv A B f is-hae-f (f a))
          ( f)
          ( rev A (map-inverse-is-half-adjoint-equiv A B f is-hae-f (f a)) a
            ( retraction-htpy-is-half-adjoint-equiv A B f is-hae-f a)))
        ( ap A B (map-inverse-is-half-adjoint-equiv A B f is-hae-f (f a)) a f
          ( retraction-htpy-is-half-adjoint-equiv A B f is-hae-f a)))
      ( refl)
      ( transport-in-fiber A B f (f a)
        ( map-inverse-is-half-adjoint-equiv A B f is-hae-f (f a))
        ( a)
        ( section-htpy-is-half-adjoint-equiv A B f is-hae-f (f a))
        ( retraction-htpy-is-half-adjoint-equiv A B f is-hae-f a))
      ( concat-eq-right B
        ( f a)
        ( f (map-inverse-is-half-adjoint-equiv A B f is-hae-f (f a)))
        ( f a)
        ( ap A B
          ( a)
          ( map-inverse-is-half-adjoint-equiv A B f is-hae-f (f a))
          ( f)
          ( rev A (map-inverse-is-half-adjoint-equiv A B f is-hae-f (f a)) a
            ( retraction-htpy-is-half-adjoint-equiv A B f is-hae-f a)))
        ( section-htpy-is-half-adjoint-equiv A B f is-hae-f (f a))
        ( ap A B (map-inverse-is-half-adjoint-equiv A B f is-hae-f (f a)) a f
          ( retraction-htpy-is-half-adjoint-equiv A B f is-hae-f a))
        ( coherence-is-half-adjoint-equiv A B f is-hae-f a))
      ( concat-ap-rev-ap-id A B
        ( map-inverse-is-half-adjoint-equiv A B f is-hae-f (f a))
        ( a)
        ( f)
        ( retraction-htpy-is-half-adjoint-equiv A B f is-hae-f a)))

#def contraction-fib-is-half-adjoint-equiv uses (is-hae-f)
  ( b : B)
  ( z : fib A B f b)
  : is-split-surjection-is-half-adjoint-equiv b = z
  :=
    ind-fib
    ( A) (B) (f)
    ( \ b' z' → is-split-surjection-is-half-adjoint-equiv b' = z')
    ( calculate-is-split-surjection-is-half-adjoint-equiv)
    ( b)
    ( z)

#def is-contr-map-is-half-adjoint-equiv uses (is-hae-f)
  : is-contr-map A B f
  :=
    \ b →
      ( is-split-surjection-is-half-adjoint-equiv b
      , contraction-fib-is-half-adjoint-equiv b)

#end is-contr-map-is-equiv
```

### Equivalences are contractible maps

```rzk
#def is-contr-map-is-equiv
  ( A B : U)
  ( f : A → B)
  ( is-equiv-f : is-equiv A B f)
  : is-contr-map A B f
  :=
    \ b →
    ( is-split-surjection-is-half-adjoint-equiv A B f
      ( is-half-adjoint-equiv-is-equiv A B f is-equiv-f) b
    , \ z → contraction-fib-is-half-adjoint-equiv A B f
        ( is-half-adjoint-equiv-is-equiv A B f is-equiv-f) b z)

#def is-contr-map-iff-is-equiv
  ( A B : U)
  ( f : A → B)
  : iff (is-contr-map A B f) (is-equiv A B f)
  := (is-equiv-is-contr-map A B f , is-contr-map-is-equiv A B f)
```

## Fibers of projections

For a family of types `#!rzk B : A → U`, the fiber of the projection from
`#!rzk total-type A B` to `#!rzk A` over `#!rzk a : A` is equivalent to
`#!rzk B a`. While both types deserve the name "fibers" to disambiguate, we
temporarily refer to the fiber as the "homotopy fiber" and `#!rzk B a` as the
"strict fiber."

```rzk
#section strict-vs-homotopy-fiber

#variable A : U
#variable B : A → U

#def homotopy-fiber-strict-fiber
  ( a : A)
  ( b : B a)
  : fib (total-type A B) A (projection-total-type A B) a
  := ((a , b) , refl)

#def strict-fiber-homotopy-fiber
  ( a : A)
  ( ( ( a' , b') , p) : fib (total-type A B) A (projection-total-type A B) a)
  : B a
  := transport A B a' a p b'

#def retract-homotopy-fiber-strict-fiber
  ( a : A)
  ( b : B a)
  : strict-fiber-homotopy-fiber a (homotopy-fiber-strict-fiber a b) = b
  := refl

#def calculation-retract-strict-fiber-homotopy-fiber
  ( a : A)
  ( b : B a)
  : homotopy-fiber-strict-fiber a
    ( strict-fiber-homotopy-fiber a ((a , b) , refl))
  = ( ( a , b) , refl)
  := refl

#def retract-strict-fiber-homotopy-fiber
  ( a : A)
  ( ( ( a' , b') , p) : fib (total-type A B) A (projection-total-type A B) a)
  : homotopy-fiber-strict-fiber a (strict-fiber-homotopy-fiber a ((a' , b') , p))
    = ( ( a' , b') , p)
  :=
    ind-fib
    ( total-type A B)
    ( A)
    ( projection-total-type A B)
    ( \ a0 ((a'' , b'') , p') →
      homotopy-fiber-strict-fiber a0
      ( strict-fiber-homotopy-fiber a0 ((a'' , b'') , p')) = ((a'' , b'') , p'))
    ( \ (a'' , b'') → refl)
    ( a)
    ( ( ( a' , b') , p))

#def equiv-homotopy-fiber-strict-fiber
  ( a : A)
  : Equiv
    ( B a)
    ( fib (total-type A B) A (projection-total-type A B) a)
  :=
    ( homotopy-fiber-strict-fiber a
    , ( ( strict-fiber-homotopy-fiber a
        , retract-homotopy-fiber-strict-fiber a)
      , ( strict-fiber-homotopy-fiber a
        , retract-strict-fiber-homotopy-fiber a)))

#end strict-vs-homotopy-fiber
```

## Fibers of composites

The fiber of a composite function is a sum over the fiber of the second function
of the fibers of the first function.

```rzk
#section fiber-composition

#variables A B C : U
#variable f : A → B
#variable g : B → C

#def fiber-sum-fiber-comp
  ( c : C)
  ( ( a , r) : fib A C (comp A B C g f) c)
  : ( Σ ( ( b , q) : fib B C g c) , fib A B f b)
  := ((f a , r) , (a , refl))

#def fiber-comp-fiber-sum
  ( c : C)
  ( ( ( b , q) , (a , p)) : Σ ((b , q) : fib B C g c) , fib A B f b)
  : fib A C (comp A B C g f) c
  := (a , concat C (g (f a)) (g b) c (ap B C (f a) b g p) q)

#def is-retract-fiber-sum-fiber-comp
  ( c : C)
  ( ( a , r) : fib A C (comp A B C g f) c)
  : fiber-comp-fiber-sum c (fiber-sum-fiber-comp c (a , r)) = (a , r)
  :=
    eq-eq-fiber-Σ
    ( A)
    ( \ a0 → (g (f a0)) = c)
    ( a)
    ( concat C (g (f a)) (g (f a)) c refl r)
    ( r)
    ( left-unit-concat C (g (f a)) c r)

#def is-retract-fiber-comp-fiber-sum'
  ( c : C)
  ( ( b , q) : fib B C g c)
  : ( ( a , p) : fib A B f b)
  → fiber-sum-fiber-comp c (fiber-comp-fiber-sum c ((b , q) , (a , p)))
  = ( ( b , q) , (a , p))
  :=
    ind-fib B C g
    ( \ c' (b' , q') → ((a , p) : fib A B f b')
    → fiber-sum-fiber-comp c' (fiber-comp-fiber-sum c' ((b' , q') , (a , p)))
    = ( ( b' , q') , (a , p)))
    ( \ b0 (a , p) →
      ( ind-fib A B f
        ( \ b0' (a' , p') →
          fiber-sum-fiber-comp (g b0')
          ( fiber-comp-fiber-sum (g b0') ((b0' , refl) , (a' , p')))
        = ( ( b0' , refl) , (a' , p')))
        ( \ a0 → refl)
        ( b0)
        ( ( a , p))))
    ( c)
    ( ( b , q))

#def is-retract-fiber-comp-fiber-sum
  ( c : C)
  ( ( ( b , q) , (a , p)) : Σ ((b , q) : fib B C g c) , fib A B f b)
  : fiber-sum-fiber-comp c (fiber-comp-fiber-sum c ((b , q) , (a , p)))
  = ( ( b , q) , (a , p))
  := is-retract-fiber-comp-fiber-sum' c (b , q) (a , p)

#def equiv-fiber-sum-fiber-comp
  ( c : C)
  : Equiv
    ( fib A C (comp A B C g f) c)
    ( Σ ( ( b , q) : fib B C g c) , fib A B f b)
  :=
    ( fiber-sum-fiber-comp c
    , ( ( fiber-comp-fiber-sum c
        , is-retract-fiber-sum-fiber-comp c)
      , ( fiber-comp-fiber-sum c
        , is-retract-fiber-comp-fiber-sum c)))

#end fiber-composition
```
