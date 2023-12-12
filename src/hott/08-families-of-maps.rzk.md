# 8. Families of maps

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Fiber of total map

We now calculate the fiber of the map on total spaces associated to a family of
maps.

```rzk
#def total-map
  ( A : U)
  ( B C : A → U)
  ( f : (a : A) → (B a) → (C a))
  : ( total-type A B) → (total-type A C)
  := \ (a , b) → (a , f a b)

#def fib-total-map-fib-fiberwise
  ( A : U)
  ( B C : A → U)
  ( f : (a : A) → (B a) → (C a))
  ( ( a , c) : total-type A C)
  : fib (B a) (C a) (f a) (c)
  → fib (total-type A B) (total-type A C) (total-map A B C f) (a , c)
  := \ (b , p) → ((a , b) , eq-eq-fiber-Σ A C a (f a b) c p)

#def fib-fiberwise-fib-total-map
  ( A : U)
  ( B C : A → U)
  ( f : (a : A) → (B a) → (C a))
  : ( ( a , c) : total-type A C)
  → fib (total-type A B) (total-type A C) (total-map A B C f) (a , c)
  → fib (B a) (C a) (f a) (c)
  :=
    ind-fib (total-type A B) (total-type A C) (total-map A B C f)
    ( \ (a' , c') _ → fib (B a') (C a') (f a') c')
    ( \ (_ , b') → (b' , refl))

#def has-retraction-fib-total-map-fib-fiberwise
  ( A : U)
  ( B C : A → U)
  ( f : (a : A) → (B a) → (C a))
  ( ( a , c) : total-type A C)
  : has-retraction
    ( fib (B a) (C a) (f a) (c))
    ( fib (total-type A B) (total-type A C) (total-map A B C f) (a , c))
    ( fib-total-map-fib-fiberwise A B C f (a , c))
  :=
    ( ( fib-fiberwise-fib-total-map A B C f (a , c))
    , ( \ (b , p) →
        ind-path (C a) (f a b)
        ( \ c' p' →
          ( ( fib-fiberwise-fib-total-map A B C f ((a , c')))
            ( ( fib-total-map-fib-fiberwise A B C f (a , c')) (b , p'))
          = ( b , p')))
        ( refl)
        ( c)
        ( p)))

#def has-section-fib-total-map-fib-fiberwise
  ( A : U)
  ( B C : A → U)
  ( f : (a : A) → (B a) → (C a))
  ( ( a , c) : (Σ (x : A) , C x))
  : has-section
    ( fib (B a) (C a) (f a) c)
    ( fib (total-type A B) (total-type A C) (total-map A B C f) (a , c))
    ( fib-total-map-fib-fiberwise A B C f (a , c))
  :=
    ( ( fib-fiberwise-fib-total-map A B C f (a , c))
    , ( \ ((a' , b') , p) →
        ind-path
          ( total-type A C)
          ( a' , f a' b')
          ( \ w' p' →
            ( ( fib-total-map-fib-fiberwise A B C f w')
              ( ( fib-fiberwise-fib-total-map A B C f w') ((a' , b') , p'))
            = ( ( a' , b') , p')))
          ( refl)
          ( a , c)
          ( p)))

#def is-equiv-fib-total-map-fib-fiberwise
  ( A : U)
  ( B C : A → U)
  ( f : (a : A) → (B a) → (C a))
  ( ( a , c) : total-type A C)
  : is-equiv
    ( fib (B a) (C a) (f a) c)
    ( fib (total-type A B) (total-type A C) (total-map A B C f) (a , c))
    ( fib-total-map-fib-fiberwise A B C f (a , c))
  :=
    ( has-retraction-fib-total-map-fib-fiberwise A B C f (a , c)
    , has-section-fib-total-map-fib-fiberwise A B C f (a , c))

#def equiv-fib-total-map-fib-fiberwise
  ( A : U)
  ( B C : A → U)
  ( f : (a : A) → (B a) → (C a))
  ( ( a , c) : total-type A C)
  : Equiv
    ( fib (B a) (C a) (f a) c)
    ( fib (total-type A B) (total-type A C) (total-map A B C f) (a , c))
  :=
    ( fib-total-map-fib-fiberwise A B C f (a , c)
    , is-equiv-fib-total-map-fib-fiberwise A B C f (a , c))
```

## Families of equivalences

A family of equivalences induces an equivalence on total spaces and conversely.
It will be easiest to work with the incoherent notion of two-sided-inverses.

```rzk
#def map-inverse-total-has-inverse-fiberwise
  ( A : U)
  ( B C : A → U)
  ( f : (a : A) → (B a) → (C a))
  ( invfamily : (a : A) → has-inverse (B a) (C a) (f a))
  : ( total-type A C) → (total-type A B)
  :=
    \ (a , c) →
      ( a , (map-inverse-has-inverse (B a) (C a) (f a) (invfamily a)) c)

#def has-retraction-total-has-inverse-fiberwise
  ( A : U)
  ( B C : A → U)
  ( f : (a : A) → (B a) → (C a))
  ( invfamily : (a : A) → has-inverse (B a) (C a) (f a))
  : has-retraction (total-type A B) (total-type A C) (total-map A B C f)
  :=
    ( map-inverse-total-has-inverse-fiberwise A B C f invfamily
    , \ (a , b) →
        ( eq-eq-fiber-Σ A B a
          ( ( map-inverse-has-inverse (B a) (C a) (f a) (invfamily a)) (f a b)) b
          ( ( first (second (invfamily a))) b)))

#def has-section-total-has-inverse-fiberwise
  ( A : U)
  ( B C : A → U)
  ( f : (a : A) → (B a) → (C a))
  ( invfamily : (a : A) → has-inverse (B a) (C a) (f a))
  : has-section (total-type A B) (total-type A C) (total-map A B C f)
  :=
    ( map-inverse-total-has-inverse-fiberwise A B C f invfamily
    , \ (a , c) →
        ( eq-eq-fiber-Σ A C a
          ( f a ((map-inverse-has-inverse (B a) (C a) (f a) (invfamily a)) c)) c
          ( ( second (second (invfamily a))) c)))

#def has-inverse-total-has-inverse-fiberwise
  ( A : U)
  ( B C : A → U)
  ( f : (a : A) → (B a) → (C a))
  ( invfamily : (a : A) → has-inverse (B a) (C a) (f a))
  : has-inverse (total-type A B) (total-type A C) (total-map A B C f)
  :=
    ( map-inverse-total-has-inverse-fiberwise A B C f invfamily
    , ( second (has-retraction-total-has-inverse-fiberwise A B C f invfamily)
      , second (has-section-total-has-inverse-fiberwise A B C f invfamily)))
```

The one-way result: that a family of equivalence gives an invertible map (and
thus an equivalence) on total spaces.

```rzk
#def has-inverse-total-is-equiv-fiberwise
  ( A : U)
  ( B C : A → U)
  ( f : (a : A) → (B a) → (C a))
  ( familyequiv : (a : A) → is-equiv (B a) (C a) (f a))
  : has-inverse (total-type A B) (total-type A C) (total-map A B C f)
  :=
    has-inverse-total-has-inverse-fiberwise A B C f
    ( \ a → has-inverse-is-equiv (B a) (C a) (f a) (familyequiv a))

#def is-equiv-total-is-equiv-fiberwise
  ( A : U)
  ( B C : A → U)
  ( f : (a : A) → (B a) → (C a))
  ( familyequiv : (a : A) → is-equiv (B a) (C a) (f a))
  : is-equiv (total-type A B) (total-type A C) (total-map A B C f)
  :=
    is-equiv-has-inverse
    ( total-type A B) (total-type A C) (total-map A B C f)
    ( has-inverse-total-is-equiv-fiberwise A B C f familyequiv)

#def total-equiv-family-of-equiv
  ( A : U)
  ( B C : A → U)
  ( familyeq : (a : A) → Equiv (B a) (C a))
  : Equiv (total-type A B) (total-type A C)
  :=
    ( total-map A B C (\ a → first (familyeq a))
    , is-equiv-total-is-equiv-fiberwise A B C
      ( \ a → first (familyeq a))
      ( \ a → second (familyeq a)))
```

For the converse, we make use of our calculation on fibers. The first
implication could be proven similarly.

```rzk
#def is-contr-map-total-is-contr-map-fiberwise
  ( A : U)
  ( B C : A → U)
  ( f : (a : A) → (B a) → (C a))
  ( totalcontrmap
 : is-contr-map (total-type A B) (total-type A C) (total-map A B C f))
  ( a : A)
  : is-contr-map (B a) (C a) (f a)
  :=
    \ c →
      is-contr-equiv-is-contr'
      ( fib (B a) (C a) (f a) c)
      ( fib (total-type A B) (total-type A C) (total-map A B C f) (a , c))
      ( equiv-fib-total-map-fib-fiberwise A B C f (a , c))
      ( totalcontrmap (a , c))

#def is-equiv-fiberwise-is-equiv-total
  ( A : U)
  ( B C : A → U)
  ( f : (a : A) → (B a) → (C a))
  ( totalequiv
 : is-equiv (total-type A B) (total-type A C) (total-map A B C f))
  ( a : A)
  : is-equiv (B a) (C a) (f a)
  :=
    is-equiv-is-contr-map (B a) (C a) (f a)
    ( is-contr-map-total-is-contr-map-fiberwise A B C f
      ( is-contr-map-is-equiv
        ( total-type A B) (total-type A C) (total-map A B C f)
        ( totalequiv))
      ( a))

#def family-of-equiv-is-equiv-total
  ( A : U)
  ( B C : A → U)
  ( f : (a : A) → (B a) → (C a))
  ( totalequiv
 : is-equiv (total-type A B) (total-type A C) (total-map A B C f))
  ( a : A)
  : Equiv (B a) (C a)
  := (f a , is-equiv-fiberwise-is-equiv-total A B C f totalequiv a)
```

In summary, a family of maps is an equivalence iff the map on total spaces is an
equivalence.

```rzk
#def is-equiv-total-iff-is-equiv-fiberwise
  ( A : U)
  ( B C : A → U)
  ( f : (a : A) → (B a) → (C a))
  : iff
      ( ( a : A) → is-equiv (B a) (C a) (f a))
      ( is-equiv (Σ (x : A) , B x) (Σ (x : A) , C x)
        ( total-map A B C f))
  :=
    ( is-equiv-total-is-equiv-fiberwise A B C f
    , is-equiv-fiberwise-is-equiv-total A B C f)
```

## Path spaces

### Based path spaces

```rzk title="An equivalence between the based path spaces"
#def equiv-based-paths
  ( A : U)
  ( a : A)
  : Equiv (Σ (x : A) , x = a) (Σ (x : A) , a = x)
  := total-equiv-family-of-equiv A (\ x → x = a) (\ x → a = x) (\ x → equiv-rev A x a)
```

```rzk title="Endpoint based path spaces are contractible"
#def is-contr-endpoint-based-paths
  ( A : U)
  ( a : A)
  : is-contr (Σ (x : A) , x = a)
  :=
    is-contr-equiv-is-contr' (Σ (x : A) , x = a) (Σ (x : A) , a = x)
      ( equiv-based-paths A a)
      ( is-contr-based-paths A a)
```

### Free path spaces

The canonical map from a type to its the free path type is an equivalence.

```rzk
#def free-paths
  ( A : U)
  : U
  := Σ ((x , y) : product A A) , (x = y)

#def constant-free-path
  ( A : U)
  ( a : A)
  : free-paths A
  := ((a , a) , refl)

#def is-constant-free-path
  ( A : U)
  ( ( ( a , y) , p) : free-paths A)
  : constant-free-path A a = ((a , y) , p)
  :=
    ind-path A a
    ( \ x p' → constant-free-path A a = ((a , x) , p'))
    ( refl)
    ( y) (p)

#def start-free-path
  ( A : U)
  : free-paths A → A
  := \ ((a , _) , _) → a

#def is-equiv-constant-free-path
  ( A : U)
  : is-equiv A (free-paths A) (constant-free-path A)
  :=
    ( ( start-free-path A , \ _ → refl)
    , ( start-free-path A , is-constant-free-path A))
```

## Pullback of a type family

A family of types over B pulls back along any function f : A → B to define a
family of types over A.

```rzk
#def pullback
  ( A B : U)
  ( f : A → B)
  ( C : B → U)
  : A → U
  := \ a → C (f a)
```

The pullback of a family along homotopic maps is equivalent.

```rzk
#section is-equiv-pullback-htpy

#variables A B : U
#variables f g : A → B
#variable α : homotopy A B f g
#variable C : B → U
#variable a : A

#def pullback-homotopy
  : ( pullback A B f C a) → (pullback A B g C a)
  := transport B C (f a) (g a) (α a)

#def map-inverse-pullback-homotopy
  : ( pullback A B g C a) → (pullback A B f C a)
  := transport B C (g a) (f a) (rev B (f a) (g a) (α a))

#def has-retraction-pullback-homotopy
  : has-retraction
    ( pullback A B f C a)
    ( pullback A B g C a)
    ( pullback-homotopy)
  :=
    ( map-inverse-pullback-homotopy
    , \ c →
        concat
        ( pullback A B f C a)
        ( transport B C (g a) (f a)
          ( rev B (f a) (g a) (α a))
          ( transport B C (f a) (g a) (α a) c))
        ( transport B C (f a) (f a)
          ( concat B (f a) (g a) (f a) (α a) (rev B (f a) (g a) (α a))) c)
        ( c)
        ( transport-concat-rev B C (f a) (g a) (f a) (α a)
          ( rev B (f a) (g a) (α a)) c)
        ( transport2 B C (f a) (f a)
          ( concat B (f a) (g a) (f a) (α a) (rev B (f a) (g a) (α a))) refl
          ( right-inverse-concat B (f a) (g a) (α a)) c))

#def has-section-pullback-homotopy
  : has-section (pullback A B f C a) (pullback A B g C a)
    ( pullback-homotopy)
  :=
    ( map-inverse-pullback-homotopy
    , \ c →
      concat
        ( pullback A B g C a)
        ( transport B C (f a) (g a) (α a)
          ( transport B C (g a) (f a) (rev B (f a) (g a) (α a)) c))
        ( transport B C (g a) (g a)
          ( concat B (g a) (f a) (g a) (rev B (f a) (g a) (α a)) (α a)) c)
        ( c)
        ( transport-concat-rev B C (g a) (f a) (g a)
          ( rev B (f a) (g a) (α a)) (α a) (c))
        ( transport2 B C (g a) (g a)
          ( concat B (g a) (f a) (g a) (rev B (f a) (g a) (α a)) (α a))
          ( refl)
          ( left-inverse-concat B (f a) (g a) (α a)) c))

#def is-equiv-pullback-homotopy uses (α)
  : is-equiv
      ( pullback A B f C a)
      ( pullback A B g C a)
      ( pullback-homotopy)
  := (has-retraction-pullback-homotopy , has-section-pullback-homotopy)

#def equiv-pullback-homotopy uses (α)
  : Equiv (pullback A B f C a) (pullback A B g C a)
  := (pullback-homotopy , is-equiv-pullback-homotopy)

#end is-equiv-pullback-htpy
```

The total space of a pulled back family of types maps to the original total
space.

```rzk
#def pullback-comparison-map
  ( A B : U)
  ( f : A → B)
  ( C : B → U)
  : ( Σ ( a : A) , (pullback A B f C) a) → (Σ (b : B) , C b)
  := \ (a , c) → (f a , c)
```

Now we show that if a family is pulled back along an equivalence, the total
spaces are equivalent by proving that the comparison is a contractible map. For
this, we first prove that each fiber is equivalent to a fiber of the original
map.

```rzk
#def pullback-comparison-fiber
  ( A B : U)
  ( f : A → B)
  ( C : B → U)
  ( z : Σ (b : B) , C b)
  : U
  :=
    fib
      ( Σ ( a : A) , (pullback A B f C) a)
      ( Σ ( b : B) , C b)
      ( pullback-comparison-map A B f C) z

#def pullback-comparison-fiber-to-fiber
  ( A B : U)
  ( f : A → B)
  ( C : B → U)
  ( z : Σ (b : B) , C b)
  : ( pullback-comparison-fiber A B f C z) → (fib A B f (first z))
  :=
    \ (w , p) →
    ind-path
      ( Σ ( b : B) , C b)
      ( pullback-comparison-map A B f C w)
      ( \ z' p' →
        ( fib A B f (first z')))
      ( first w , refl)
      ( z)
      ( p)

#def from-base-fiber-to-pullback-comparison-fiber
  ( A B : U)
  ( f : A → B)
  ( C : B → U)
  ( b : B)
  : ( fib A B f b) → (c : C b) → (pullback-comparison-fiber A B f C (b , c))
  :=
    \ (a , p) →
    ind-path
      ( B)
      ( f a)
      ( \ b' p' →
          ( c : C b') → (pullback-comparison-fiber A B f C ((b' , c))))
      ( \ c → ((a , c) , refl))
      ( b)
      ( p)

#def pullback-comparison-fiber-to-fiber-inv
  ( A B : U)
  ( f : A → B)
  ( C : B → U)
  ( z : Σ (b : B) , C b)
  : ( fib A B f (first z)) → (pullback-comparison-fiber A B f C z)
  :=
    \ (a , p) →
      from-base-fiber-to-pullback-comparison-fiber A B f C
      ( first z) (a , p) (second z)

#def pullback-comparison-fiber-to-fiber-retracting-homotopy
  ( A B : U)
  ( f : A → B)
  ( C : B → U)
  ( z : Σ (b : B) , C b)
  ( ( w , p) : pullback-comparison-fiber A B f C z)
  : ( ( pullback-comparison-fiber-to-fiber-inv A B f C z)
      ( ( pullback-comparison-fiber-to-fiber A B f C z) (w , p))) = (w , p)
  :=
    ind-path
      ( Σ ( b : B) , C b)
      ( pullback-comparison-map A B f C w)
      ( \ z' p' →
        ( ( pullback-comparison-fiber-to-fiber-inv A B f C z')
          ( ( pullback-comparison-fiber-to-fiber A B f C z') (w , p')))
      = ( w , p'))
      ( refl)
      ( z)
      ( p)

#def pullback-comparison-fiber-to-fiber-section-homotopy-map
  ( A B : U)
  ( f : A → B)
  ( C : B → U)
  ( b : B)
  ( ( a , p) : fib A B f b)
  : ( c : C b)
    → ( ( pullback-comparison-fiber-to-fiber A B f C (b , c))
        ( ( pullback-comparison-fiber-to-fiber-inv A B f C (b , c)) (a , p)))
    = ( a , p)
  :=
    ind-path
      ( B)
      ( f a)
      ( \ b' p' →
        ( c : C b')
      → ( ( pullback-comparison-fiber-to-fiber A B f C (b' , c))
          ( ( pullback-comparison-fiber-to-fiber-inv A B f C (b' , c)) (a , p')))
      = ( a , p'))
      ( \ c → refl)
      ( b)
      ( p)

#def pullback-comparison-fiber-to-fiber-section-homotopy
  ( A B : U)
  ( f : A → B)
  ( C : B → U)
  ( z : Σ (b : B) , C b)
  ( ( a , p) : fib A B f (first z))
  : ( pullback-comparison-fiber-to-fiber A B f C z
      ( pullback-comparison-fiber-to-fiber-inv A B f C z (a , p))) = (a , p)
  :=
    pullback-comparison-fiber-to-fiber-section-homotopy-map A B f C
      ( first z) (a , p) (second z)

#def equiv-pullback-comparison-fiber
  ( A B : U)
  ( f : A → B)
  ( C : B → U)
  ( z : Σ (b : B) , C b)
  : Equiv (pullback-comparison-fiber A B f C z) (fib A B f (first z))
  :=
    ( pullback-comparison-fiber-to-fiber A B f C z
    , ( ( pullback-comparison-fiber-to-fiber-inv A B f C z
        , pullback-comparison-fiber-to-fiber-retracting-homotopy A B f C z)
      , ( pullback-comparison-fiber-to-fiber-inv A B f C z
        , pullback-comparison-fiber-to-fiber-section-homotopy A B f C z)))
```

As a corollary, we show that pullback along an equivalence induces an
equivalence of total spaces.

```rzk
#def equiv-total-pullback-is-equiv
  ( A B : U)
  ( f : A → B)
  ( is-equiv-f : is-equiv A B f)
  ( C : B → U)
  : Equiv (Σ (a : A) , (pullback A B f C) a) (Σ (b : B) , C b)
  :=
    ( pullback-comparison-map A B f C
    , is-equiv-is-contr-map
        ( Σ ( a : A) , (pullback A B f C) a)
        ( Σ ( b : B) , C b)
        ( pullback-comparison-map A B f C)
        ( \ z →
          ( is-contr-equiv-is-contr'
            ( pullback-comparison-fiber A B f C z)
            ( fib A B f (first z))
            ( equiv-pullback-comparison-fiber A B f C z)
            ( is-contr-map-is-equiv A B f is-equiv-f (first z)))))
```

## Fundamental theorem of identity types

The fundamental theorem of identity types concerns the following question: Given
a type family `B : A → U`, when is `B` equivalent to `\ x → a x` for some
`a : A`?

We start by fixing `a : A` and investigating when a map of families
`x : A → (a = x) → B x` is a (fiberwise) equivalence.

```rzk
#section fundamental-thm-id-types

#variable A : U
#variable a : A
#variable B : A → U
#variable f : (x : A) → (a = x) → B x

#def is-contr-total-are-equiv-from-paths
  : ( ( x : A) → (is-equiv (a = x) (B x) (f x)))
  → ( is-contr (Σ (x : A) , B x))
  :=
    ( \ familyequiv →
      ( equiv-with-contractible-domain-implies-contractible-codomain
        ( Σ ( x : A) , a = x) (Σ (x : A) , B x)
        ( ( total-map A (\ x → (a = x)) B f)
        , ( is-equiv-has-inverse (Σ (x : A) , a = x) (Σ (x : A) , B x)
            ( total-map A (\ x → (a = x)) B f)
            ( has-inverse-total-is-equiv-fiberwise A
              ( \ x → (a = x)) B f familyequiv)))
        ( is-contr-based-paths A a)))

#def are-equiv-from-paths-is-contr-total
  : ( is-contr (Σ (x : A) , B x))
  → ( ( x : A) → (is-equiv (a = x) (B x) (f x)))
  :=
    ( \ is-contr-Σ-A-B x →
      is-equiv-fiberwise-is-equiv-total A
        ( \ x' → (a = x'))
        ( B)
        ( f)
        ( is-equiv-are-contr
          ( Σ ( x' : A) , (a = x'))
          ( Σ ( x' : A) , (B x'))
          ( is-contr-based-paths A a)
          ( is-contr-Σ-A-B)
          ( total-map A (\ x' → (a = x')) B f))
        ( x))
```

This allows us to apply "based path induction" to a family satisfying the
fundamental theorem:

```rzk
-- Please suggest a better name.
#def ind-based-path
  ( familyequiv : (z : A) → (is-equiv (a = z) (B z) (f z)))
  ( P : (z : A) → B z → U)
  ( p0 : P a (f a refl))
  ( u : A)
  ( p : B u)
  : P u p
  :=
    ind-sing
      ( Σ ( v : A) , B v)
      ( a , f a refl)
      ( \ (u' , p') → P u' p')
      ( contr-implies-singleton-induction-pointed
        ( Σ ( z : A) , B z)
        ( is-contr-total-are-equiv-from-paths familyequiv)
        ( \ (x' , p') → P x' p'))
      ( p0)
      ( u , p)

#end fundamental-thm-id-types
```

We can now answer the original question. A type family `B : A → U` is equivalent
to the family of based paths at a point if and only if its total space is
contractible.

```rzk
#def map-from-paths-inhabited-total
  ( A : U)
  ( B : A → U)
  ( ( a , b) : total-type A B)
  ( x : A)
  : ( a = x) → B x
  := ind-path A a (\ y _ → B y) b x

#def fundamental-theorem-of-identity-types
  ( A : U)
  ( B : A → U)
  : iff
    ( is-contr (total-type A B))
    ( Σ ( a : A) , ((x : A) → Equiv (a = x) (B x)))
  :=
  ( ( \ ((a , b) , h) →
      ( a
      , \ x →
        ( map-from-paths-inhabited-total A B (a , b) x
        , are-equiv-from-paths-is-contr-total A a B
          ( map-from-paths-inhabited-total A B (a , b))
          ( ( a , b) , h)
          ( x))))
  , ( \ (a , familyequiv) →
      is-contr-total-are-equiv-from-paths A a B
      ( \ x → first (familyequiv x))
      ( \ x → second (familyequiv x))))
```

## Maps over product types

For later use, we specialize the previous results to the case of a family of
types over a product type.

```rzk
#section fibered-map-over-product

#variables A A' B B' : U
#variable C : A → B → U
#variable C' : A' → B' → U
#variable f : A → A'
#variable g : B → B'
#variable h : (a : A) → (b : B) → (C a b) → C' (f a) (g b)

#def total-map-fibered-map-over-product
  : ( Σ ( a : A) , (Σ (b : B) , C a b))
  → ( Σ ( a' : A') , (Σ (b' : B') , C' a' b'))
  := \ (a , (b , c)) → (f a , (g b , h a b c))

#def pullback-is-equiv-base-is-equiv-total-is-equiv
  ( is-equiv-total
 : is-equiv
      ( Σ ( a : A) , (Σ (b : B) , C a b))
      ( Σ ( a' : A') , (Σ (b' : B') , C' a' b'))
      ( total-map-fibered-map-over-product))
  ( is-equiv-f : is-equiv A A' f)
  : is-equiv
    ( Σ ( a : A) , (Σ (b : B) , C a b))
    ( Σ ( a : A) , (Σ (b' : B') , C' (f a) b'))
    ( \ (a , (b , c)) → (a , (g b , h a b c)))
  :=
    is-equiv-right-factor
    ( Σ ( a : A) , (Σ (b : B) , C a b))
    ( Σ ( a : A) , (Σ (b' : B') , C' (f a) b'))
    ( Σ ( a' : A') , (Σ (b' : B') , C' a' b'))
    ( \ (a , (b , c)) → (a , (g b , h a b c)))
    ( \ (a , (b' , c')) → (f a , (b' , c')))
    ( second
      ( equiv-total-pullback-is-equiv
        ( A) (A')
        ( f) (is-equiv-f)
        ( \ a' → (Σ (b' : B') , C' a' b'))))
    ( is-equiv-total)

#def pullback-is-equiv-bases-are-equiv-total-is-equiv
  ( is-equiv-total
 : is-equiv
      ( Σ ( a : A) , (Σ (b : B) , C a b))
      ( Σ ( a' : A') , (Σ (b' : B') , C' a' b'))
      ( total-map-fibered-map-over-product))
  ( is-equiv-f : is-equiv A A' f)
  ( is-equiv-g : is-equiv B B' g)
  : is-equiv
    ( Σ ( a : A) , (Σ (b : B) , C a b))
    ( Σ ( a : A) , (Σ (b : B) , C' (f a) (g b)))
    ( \ (a , (b , c)) → (a , (b , h a b c)))
  :=
    is-equiv-right-factor
    ( Σ ( a : A) , (Σ (b : B) , C a b))
    ( Σ ( a : A) , (Σ (b : B) , C' (f a) (g b)))
    ( Σ ( a : A) , (Σ (b' : B') , C' (f a) b'))
    ( \ (a , (b , c)) → (a , (b , h a b c)))
    ( \ (a , (b , c)) → (a , (g b , c)))
    ( is-equiv-total-is-equiv-fiberwise A
      ( \ a → (Σ (b : B) , C' (f a) (g b)))
      ( \ a → (Σ (b' : B') , C' (f a) b'))
      ( \ a (b , c) → (g b , c))
      ( \ a →
        ( second
          ( equiv-total-pullback-is-equiv
            ( B) (B')
            ( g) (is-equiv-g)
            ( \ b' → C' (f a) b')))))
    ( pullback-is-equiv-base-is-equiv-total-is-equiv is-equiv-total is-equiv-f)

#def fibered-map-is-equiv-bases-are-equiv-total-map-is-equiv
  ( is-equiv-total
 : is-equiv
      ( Σ ( a : A) , (Σ (b : B) , C a b))
      ( Σ ( a' : A') , (Σ (b' : B') , C' a' b'))
      ( total-map-fibered-map-over-product))
  ( is-equiv-f : is-equiv A A' f)
  ( is-equiv-g : is-equiv B B' g)
  ( a0 : A)
  ( b0 : B)
  : is-equiv (C a0 b0) (C' (f a0) (g b0)) (h a0 b0)
  :=
    is-equiv-fiberwise-is-equiv-total B
      ( \ b → C a0 b)
      ( \ b → C' (f a0) (g b))
      ( \ b c → h a0 b c)
      ( is-equiv-fiberwise-is-equiv-total
        ( A)
        ( \ a → (Σ (b : B) , C a b))
        ( \ a → (Σ (b : B) , C' (f a) (g b)))
        ( \ a (b , c) → (b , h a b c))
        ( pullback-is-equiv-bases-are-equiv-total-is-equiv
            is-equiv-total is-equiv-f is-equiv-g)
        ( a0))
      ( b0)

#end fibered-map-over-product
```
