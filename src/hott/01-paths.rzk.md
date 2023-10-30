# 1. Paths

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Path induction

We define path induction in terms of the built-in J rule, so that we can apply
it like any other function.

```rzk
#define ind-path
  ( A : U)
  ( a : A)
  ( C : (x : A) -> (a = x) -> U)
  ( d : C a refl)
  ( x : A)
  ( p : a = x)
  : C x p
  := idJ (A , a , C , d , x , p)
```

To emphasize the fact that this version of path induction is biased towards
paths with fixed starting point, we introduce the synonym `ind-path-start`.
Later we will construct the analogous path induction `ind-path-end`, for paths
with fixed end point.

```rzk
#define ind-path-start
  ( A : U)
  ( a : A)
  ( C : (x : A) -> (a = x) -> U)
  ( d : C a refl)
  ( x : A)
  ( p : a = x)
  : C x p
  :=
    ind-path A a C d x p
```

## Some basic path algebra

```rzk
#section path-algebra

#variable A : U
#variables x y z : A
```

### Path reversal

```rzk
#def rev
  ( p : x = y)
  : y = x
  := ind-path (A) (x) (\ y' p' → y' = x) (refl) (y) (p)
```

### Path concatenation

We take path concatenation defined by induction on the second path variable as
our main definition.

```rzk
#def concat
  ( p : x = y)
  ( q : y = z)
  : (x = z)
  := ind-path (A) (y) (\ z' q' → (x = z')) (p) (z) (q)
```

We also introduce a version defined by induction on the first path variable, for
situations where it is easier to induct on the first path.

```rzk
#def concat'
  ( p : x = y)
  : (y = z) → (x = z)
  := ind-path (A) (x) (\ y' p' → (y' = z) → (x = z)) (\ q' → q') (y) (p)

#end path-algebra
```

## Some basic coherences in path algebra

```rzk
#section basic-path-coherence

#variable A : U
#variables w x y z : A

#def rev-rev
  ( p : x = y)
  : (rev A y x (rev A x y p)) = p
  :=
    ind-path
    ( A) (x) (\ y' p' → (rev A y' x (rev A x y' p')) = p') (refl) (y) (p)
```

### Left unit law for path concatenation

The left unit law for path concatenation does not hold definitionally due to our
choice of definition.

```rzk
#def left-unit-concat
  ( p : x = y)
  : (concat A x x y refl p) = p
  := ind-path (A) (x) (\ y' p' → (concat A x x y' refl p') = p') (refl) (y) (p)
```

### Associativity of path concatenation

```rzk
#def associative-concat
  ( p : w = x)
  ( q : x = y)
  ( r : y = z)
  : ( concat A w y z (concat A w x y p q) r) =
    ( concat A w x z p (concat A x y z q r))
  :=
    ind-path
      ( A)
      ( y)
      ( \ z' r' →
        concat A w y z' (concat A w x y p q) r' =
        concat A w x z' p (concat A x y z' q r'))
      ( refl)
      ( z)
      ( r)

#def rev-associative-concat
  ( p : w = x)
  ( q : x = y)
  ( r : y = z)
  : ( concat A w x z p (concat A x y z q r)) =
    ( concat A w y z (concat A w x y p q) r)
  :=
    ind-path
      ( A)
      ( y)
      ( \ z' r' →
          concat A w x z' p (concat A x y z' q r') =
          concat A w y z' (concat A w x y p q) r')
      ( refl)
      ( z)
      ( r)

#def right-inverse-concat
  ( p : x = y)
  : (concat A x y x p (rev A x y p)) = refl
  :=
    ind-path
      ( A)
      ( x)
      ( \ y' p' → concat A x y' x p' (rev A x y' p') = refl)
      ( refl)
      ( y)
      ( p)

#def left-inverse-concat
  ( p : x = y)
  : (concat A y x y (rev A x y p) p) = refl
  :=
    ind-path
      ( A)
      ( x)
      ( \ y' p' → concat A y' x y' (rev A x y' p') p' = refl)
      ( refl)
      ( y)
      ( p)
```

### Concatenation of two paths with common codomain

Concatenation of two paths with common codomain; defined using `#!rzk concat`
and `#!rzk rev`.

```rzk
#def zig-zag-concat
  ( p : x = y)
  ( q : z = y)
  : (x = z)
  := concat A x y z p (rev A z y q)
```

### Concatenation of two paths with common domain

Concatenation of two paths with common domain; defined using `#!rzk concat` and
`#!rzk rev`.

```rzk
#def zag-zig-concat
  (p : y = x)
  (q : y = z)
  : (x = z)
  := concat A x y z (rev A y x p) q

#def right-cancel-concat
  ( p q : x = y)
  ( r : y = z)
  : ((concat A x y z p r) = (concat A x y z q r)) → (p = q)
  :=
    ind-path
      ( A)
      ( y)
      ( \ z' r' → ((concat A x y z' p r') = (concat A x y z' q r')) → (p = q))
      ( \ H → H)
      ( z)
      ( r)

#end basic-path-coherence
```

## Some derived coherences in path algebra

The statements or proofs of the following path algebra coherences reference one
of the path algebra coherences defined above.

```rzk
#section derived-path-coherence
#variable A : U
#variables x y z : A

#def rev-concat
  ( p : x = y)
  ( q : y = z)
  : ( rev A x z (concat A x y z p q)) =
    ( concat A z y x (rev A y z q) (rev A x y p))
  :=
    ind-path
      ( A)
      ( y)
      ( \ z' q' →
          (rev A x z' (concat A x y z' p q')) =
          (concat A z' y x (rev A y z' q') (rev A x y p)))
      ( rev
          ( y = x)
          ( concat A y y x refl (rev A x y p))
          ( rev A x y p)
          ( left-unit-concat A y x (rev A x y p)))
      ( z)
      ( q)
```

### Postwhiskering paths of paths

```rzk
#def concat-eq-left
  ( p q : x = y)
  ( H : p = q)
  ( r : y = z)
  : (concat A x y z p r) = (concat A x y z q r)
  :=
    ind-path
      ( A)
      ( y)
      ( \ z' r' → (concat A x y z' p r') = (concat A x y z' q r'))
      ( H)
      ( z)
      ( r)
```

### Prewhiskering paths of paths

Prewhiskering paths of paths is much harder.

```rzk
#def concat-eq-right
  ( p : x = y)
  : ( q : y = z) →
    ( r : y = z) →
    ( H : q = r) →
    ( concat A x y z p q) = (concat A x y z p r)
  :=
    ind-path
      ( A)
      ( x)
      ( \ y' p' →
        ( q : y' = z) →
        ( r : y' = z) →
        ( H : q = r) →
        ( concat A x y' z p' q) = (concat A x y' z p' r))
      ( \ q r H →
        concat
          ( x = z)
          ( concat A x x z refl q)
          ( r)
          ( concat A x x z refl r)
          ( concat (x = z) (concat A x x z refl q) q r (left-unit-concat A x z q) H)
          ( rev (x = z) (concat A x x z refl r) r (left-unit-concat A x z r)))
      ( y)
      ( p)
```

### Identifying the two definitions of path concatenation

```rzk
#def concat-concat'
  ( p : x = y)
  : ( q : y = z) →
    ( concat A x y z p q) = (concat' A x y z p q)
  :=
    ind-path
      ( A)
      ( x)
      ( \ y' p' →
          (q' : y' =_{A} z) →
          (concat A x y' z p' q') =_{x =_{A} z} concat' A x y' z p' q')
      ( \ q' → left-unit-concat A x z q')
      ( y)
      ( p)

#def concat'-concat
  ( p : x = y)
  ( q : y = z)
  : concat' A x y z p q = concat A x y z p q
  :=
    rev
      ( x = z)
      ( concat A x y z p q)
      ( concat' A x y z p q)
      ( concat-concat' p q)
```

This is easier to prove for `#!rzk concat'` than for `#!rzk concat`.

```rzk
#def alt-triangle-rotation
  ( p : x = z)
  ( q : x = y)
  : ( r : y = z) →
    ( H : p = concat' A x y z q r) →
    ( concat' A y x z (rev A x y q) p) = r
  :=
    ind-path
      ( A)
      ( x)
      ( \ y' q' →
        ( r' : y' =_{A} z) →
        ( H' : p = concat' A x y' z q' r') →
        ( concat' A y' x z (rev A x y' q') p) = r')
      ( \ r' H' → H')
      ( y)
      ( q)
```

The following needs to be outside the previous section because of the usage of
`#!rzk concat-concat' A y x`.

```rzk
#end derived-path-coherence

#def triangle-rotation
  ( A : U)
  ( x y z : A)
  ( p : x = z)
  ( q : x = y)
  ( r : y = z)
  ( H : p = concat A x y z q r)
  : (concat A y x z (rev A x y q) p) = r
  :=
    concat
      ( y = z)
      ( concat A y x z (rev A x y q) p)
      ( concat' A y x z (rev A x y q) p)
      ( r)
      ( concat-concat' A y x z (rev A x y q) p)
      ( alt-triangle-rotation
        ( A) (x) (y) (z) (p) (q) (r)
        ( concat
          ( x = z)
          ( p)
          ( concat A x y z q r)
          ( concat' A x y z q r)
          ( H)
          ( concat-concat' A x y z q r)))
```

A special case of this is sometimes useful

```rzk
#def cancel-left-path
  (A : U)
  (x y : A)
  (p q : x = y)
  : (p = q) → ( concat A y x y (rev A x y q) p) = refl
  := triangle-rotation A x y y p q refl
```

### Concatenation with a path and its reversal

```rzk
#def retraction-preconcat
  ( A : U)
  ( x y z : A)
  ( p : x = y)
  ( q : y = z)
  : concat A y x z (rev A x y p) (concat A x y z p q) = q
  :=
    ind-path (A) (y)
    ( \ z' q' → concat A y x z' (rev A x y p) (concat A x y z' p q') = q') (left-inverse-concat A x y p) (z) (q)

#def section-preconcat
  ( A : U)
  ( x y z : A)
  ( p : x = y)
  ( r : x = z)
  : concat A x y z p (concat A y x z (rev A x y p) r) = r
  :=
    ind-path (A) (x)
    ( \ z' r' → concat A x y z' p (concat A y x z' (rev A x y p) r') = r') (right-inverse-concat A x y p) (z) (r)

#def retraction-postconcat
  ( A : U)
  ( x y z : A)
  ( q : y = z)
  ( p : x = y)
  : concat A x z y (concat A x y z p q) (rev A y z q) = p
  :=
    ind-path (A) (y)
    ( \ z' q' → concat A x z' y (concat A x y z' p q') (rev A y z' q') = p)
    ( refl) (z) (q)

#def section-postconcat
  ( A : U)
  ( x y z : A)
  ( q : y = z)
  ( r : x = z)
  : concat A x y z (concat A x z y r (rev A y z q)) q = r
  :=
    concat
      ( x = z)
      ( concat A x y z (concat A x z y r (rev A y z q)) q)
      ( concat A x z z r (concat A z y z (rev A y z q) q))
      ( r)
      ( associative-concat A x z y z r (rev A y z q) q)
      ( concat-eq-right A x z z r
        ( concat A z y z (rev A y z q) q)
        ( refl)
        ( left-inverse-concat A y z q))
```

## Application of functions to paths

```rzk
#def ap
  ( A B : U)
  ( x y : A)
  ( f : A → B)
  ( p : x = y)
  : (f x = f y)
  := ind-path (A) (x) (\ y' p' → (f x = f y')) (refl) (y) (p)

#def ap-rev
  ( A B : U)
  ( x y : A)
  ( f : A → B)
  ( p : x = y)
  : (ap A B y x f (rev A x y p)) = (rev B (f x) (f y) (ap A B x y f p))
  :=
    ind-path
      ( A)
      ( x)
      ( \ y' p' →
        ap A B y' x f (rev A x y' p') = rev B (f x) (f y') (ap A B x y' f p'))
      ( refl)
      ( y)
      ( p)

#def ap-concat
  ( A B : U)
  ( x y z : A)
  ( f : A → B)
  ( p : x = y)
  ( q : y = z)
  : ( ap A B x z f (concat A x y z p q)) =
    ( concat B (f x) (f y) (f z) (ap A B x y f p) (ap A B y z f q))
  :=
    ind-path
      ( A)
      ( y)
      ( \ z' q' →
        ( ap A B x z' f (concat A x y z' p q')) =
        ( concat B (f x) (f y) (f z') (ap A B x y f p) (ap A B y z' f q')))
      ( refl)
      ( z)
      ( q)

#def rev-ap-rev
  ( A B : U)
  ( x y : A)
  ( f : A → B)
  ( p : x = y)
  : (rev B (f y) (f x) (ap A B y x f (rev A x y p))) = (ap A B x y f p)
  :=
    ind-path
      ( A)
      ( x)
      ( \ y' p' →
        (rev B (f y') (f x) (ap A B y' x f (rev A x y' p'))) =
        (ap A B x y' f p'))
      ( refl)
      ( y)
      ( p)
```

The following is for a specific use.

```rzk
#def concat-ap-rev-ap-id
  ( A B : U)
  ( x y : A)
  ( f : A → B)
  ( p : x = y)
  : ( concat
      ( B) (f y) (f x) (f y)
      ( ap A B y x f (rev A x y p))
      ( ap A B x y f p)) =
    ( refl)
  :=
    ind-path
      ( A)
      ( x)
      ( \ y' p' →
        ( concat
          ( B) (f y') (f x) (f y')
          ( ap A B y' x f (rev A x y' p')) (ap A B x y' f p')) =
        ( refl))
      ( refl)
      ( y)
      ( p)

#def ap-id
  ( A : U)
  ( x y : A)
  ( p : x = y)
  : (ap A A x y (identity A) p) = p
  := ind-path (A) (x) (\ y' p' → (ap A A x y' (\ z → z) p') = p') (refl) (y) (p)
```

Application of a function to homotopic paths yields homotopic paths.

```rzk
#def ap-eq
  ( A B : U)
  ( x y : A)
  ( f : A → B)
  ( p q : x = y)
  ( H : p = q)
  : (ap A B x y f p) = (ap A B x y f q)
  :=
    ind-path
      ( x = y)
      ( p)
      ( \ q' H' → (ap A B x y f p) = (ap A B x y f q'))
      ( refl)
      ( q)
      ( H)

#def ap-comp
  ( A B C : U)
  ( x y : A)
  ( f : A → B)
  ( g : B → C)
  ( p : x = y)
  : ( ap A C x y (comp A B C g f) p) =
    ( ap B C (f x) (f y) g (ap A B x y f p))
  :=
    ind-path
      ( A)
      ( x)
      ( \ y' p' →
        ( ap A C x y' (\ z → g (f z)) p') =
        ( ap B C (f x) (f y') g (ap A B x y' f p')))
      ( refl)
      ( y)
      ( p)

#def rev-ap-comp
  ( A B C : U)
  ( x y : A)
  ( f : A → B)
  ( g : B → C)
  ( p : x = y)
  : ( ap B C (f x) (f y) g (ap A B x y f p)) =
    ( ap A C x y (comp A B C g f) p)
  :=
    rev
      ( g (f x) = g (f y))
      ( ap A C x y (\ z → g (f z)) p)
      ( ap B C (f x) (f y) g (ap A B x y f p))
      ( ap-comp A B C x y f g p)
```

## Transport

```rzk
#section transport

#variable A : U
#variable B : A → U
```

### Transport in a type family along a path in the base

```rzk
#def transport
  ( x y : A)
  ( p : x = y)
  ( u : B x)
  : B y
  := ind-path (A) (x) (\ y' p' → B y') (u) (y) (p)
```

### The lift of a base path to a path from a term in the total space to its transport

```rzk
#def transport-lift
  ( x y : A)
  ( p : x = y)
  ( u : B x)
  : (x , u) =_{Σ (z : A) , B z} (y , transport x y p u)
  :=
    ind-path
      ( A)
      ( x)
      ( \ y' p' → (x , u) =_{Σ (z : A) , B z} (y' , transport x y' p' u))
      ( refl)
      ( y)
      ( p)
```

### Transport along concatenated paths

```rzk
#def transport-concat
  ( x y z : A)
  ( p : x = y)
  ( q : y = z)
  ( u : B x)
  : ( transport x z (concat A x y z p q) u) =
    ( transport y z q (transport x y p u))
  :=
    ind-path
      ( A)
      ( y)
      ( \ z' q' →
        ( transport x z' (concat A x y z' p q') u) =
        ( transport y z' q' (transport x y p u)))
      ( refl)
      ( z)
      ( q)

#def transport-concat-rev
  ( x y z : A)
  ( p : x = y)
  ( q : y = z)
  ( u : B x)
  : ( transport y z q (transport x y p u)) =
    ( transport x z (concat A x y z p q) u)
  :=
    ind-path
      ( A)
      ( y)
      ( \ z' q' →
        ( transport y z' q' (transport x y p u)) =
        ( transport x z' (concat A x y z' p q') u))
      ( refl)
      ( z)
      ( q)
```

### Transport along homotopic paths

```rzk
#def transport2
  ( x y : A)
  ( p q : x = y)
  ( H : p = q)
  ( u : B x)
  : (transport x y p u) = (transport x y q u)
  :=
    ind-path
      ( x = y)
      ( p)
      ( \ q' H' → (transport x y p u) = (transport x y q' u))
      ( refl)
      ( q)
      ( H)
```

### Transport along a loop

```rzk
#def transport-loop
  ( a : A)
  ( b : B a)
  : (a = a) → B a
  := \ p → (transport a a p b)
```

```rzk
#end transport
```

### Substitution law for transport

```rzk
#def transport-substitution
  ( A' A : U)
  ( B : A → U)
  ( f : A' → A)
  ( x y : A')
  ( p : x = y)
  ( u : B (f x))
  : transport A' (\ x → B (f x)) x y p u =
    transport A B (f x) (f y) (ap A' A x y f p) u
  :=
    ind-path
      ( A')
      ( x)
      ( \ y' p' →
        transport A' (\ x → B (f x)) x y' p' u =
        transport A B (f x) (f y') (ap A' A x y' f p') u)
      ( refl)
      ( y)
      ( p)
```

### Path induction

Using `rev` we can deduce a path induction principle with fixed end point.

```rzk
#def ind-path-end
  ( A : U)
  ( a : A)
  ( C : (x : A) → (x = a) -> U)
  ( d : C a refl)
  ( x : A)
  ( p : x = a)
  : C x p
  :=
    transport (x = a) (\ q → C x q) (rev A a x (rev A x a p)) p
      (rev-rev A x a p)
      (ind-path A a (\ y q → C y (rev A a y q)) d x (rev A x a p))
```

## Dependent application

```rzk
#def apd
  ( A : U)
  ( B : A → U)
  ( x y : A)
  ( f : (z : A) → B z)
  ( p : x = y)
  : (transport A B x y p (f x)) = f y
  :=
    ind-path
      ( A)
      ( x)
      ( (\ y' p' → (transport A B x y' p' (f x)) = f y'))
      ( refl)
      ( y)
      ( p)
```

## Higher-order concatenation

For convenience, we record lemmas for higher-order concatenation here.

```rzk
#section higher-concatenation
#variable A : U

#def triple-concat
  ( a0 a1 a2 a3 : A)
  ( p1 : a0 = a1)
  ( p2 : a1 = a2)
  ( p3 : a2 = a3)
  : a0 = a3
  := concat A a0 a1 a3 p1 (concat A a1 a2 a3 p2 p3)

#def quadruple-concat
  ( a0 a1 a2 a3 a4 : A)
  ( p1 : a0 = a1)
  ( p2 : a1 = a2)
  ( p3 : a2 = a3)
  ( p4 : a3 = a4)
  : a0 = a4
  := triple-concat a0 a1 a2 a4 p1 p2 (concat A a2 a3 a4 p3 p4)

#def quintuple-concat
  ( a0 a1 a2 a3 a4 a5 : A)
  ( p1 : a0 = a1)
  ( p2 : a1 = a2)
  ( p3 : a2 = a3)
  ( p4 : a3 = a4)
  ( p5 : a4 = a5)
  : a0 = a5
  := quadruple-concat a0 a1 a2 a3 a5 p1 p2 p3 (concat A a3 a4 a5 p4 p5)

#def alternating-quintuple-concat
  ( a0 : A)
  ( a1 : A) (p1 : a0 = a1)
  ( a2 : A) (p2 : a1 = a2)
  ( a3 : A) (p3 : a2 = a3)
  ( a4 : A) (p4 : a3 = a4)
  ( a5 : A) (p5 : a4 = a5)
  : a0 = a5
  := quadruple-concat a0 a1 a2 a3 a5 p1 p2 p3 (concat A a3 a4 a5 p4 p5)

#def 12ary-concat
  ( a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 : A)
  ( p1 : a0 = a1)
  ( p2 : a1 = a2)
  ( p3 : a2 = a3)
  ( p4 : a3 = a4)
  ( p5 : a4 = a5)
  ( p6 : a5 = a6)
  ( p7 : a6 = a7)
  ( p8 : a7 = a8)
  ( p9 : a8 = a9)
  ( p10 : a9 = a10)
  ( p11 : a10 = a11)
  ( p12 : a11 = a12)
  : a0 = a12
  :=
    quintuple-concat
      a0 a1 a2 a3 a4 a12
      p1 p2 p3 p4
      ( quintuple-concat
        a4 a5 a6 a7 a8 a12
        p5 p6 p7 p8
        ( quadruple-concat
          a8 a9 a10 a11 a12
          p9 p10 p11 p12))
```

The following is the same as above but with alternating arguments.

```rzk
#def alternating-12ary-concat
  ( a0 : A)
  ( a1 : A) (p1 : a0 = a1)
  ( a2 : A) (p2 : a1 = a2)
  ( a3 : A) (p3 : a2 = a3)
  ( a4 : A) (p4 : a3 = a4)
  ( a5 : A) (p5 : a4 = a5)
  ( a6 : A) (p6 : a5 = a6)
  ( a7 : A) (p7 : a6 = a7)
  ( a8 : A) (p8 : a7 = a8)
  ( a9 : A) (p9 : a8 = a9)
  ( a10 : A) (p10 : a9 = a10)
  ( a11 : A) (p11 : a10 = a11)
  ( a12 : A) (p12 : a11 = a12)
  : a0 = a12
  :=
    12ary-concat
      a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
      p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12

#end higher-concatenation
```

## Higher-order coherences

```rzk
#def rev-refl-id-triple-concat
  ( A : U)
  ( x y : A)
  ( p : x = y)
  : triple-concat A y x x y (rev A x y p) refl p = refl
  :=
    ind-path
      ( A)
      ( x)
      ( \ y' p' → triple-concat A y' x x y' (rev A x y' p') refl p' = refl)
      ( refl)
      ( y)
      ( p)

#def ap-rev-refl-id-triple-concat
  ( A B : U)
  ( x y : A)
  ( f : A → B)
  ( p : x = y)
  : (ap A B y y f (triple-concat A y x x y (rev A x y p) refl p)) = refl
  :=
    ind-path
      ( A)
      ( x)
      ( \ y' p' →
        ( ap A B y' y' f (triple-concat A y' x x y' (rev A x y' p') refl p')) =
        ( refl))
      ( refl)
      ( y)
      ( p)

#def ap-triple-concat
  ( A B : U)
  ( w x y z : A)
  ( f : A → B)
  ( p : w = x)
  ( q : x = y)
  ( r : y = z)
  : ( ap A B w z f (triple-concat A w x y z p q r)) =
    ( triple-concat
      ( B)
      ( f w)
      ( f x)
      ( f y)
      ( f z)
      ( ap A B w x f p)
      ( ap A B x y f q)
      ( ap A B y z f r))
  :=
    ind-path
      ( A)
      ( y)
      ( \ z' r' →
        ( ap A B w z' f (triple-concat A w x y z' p q r')) =
        ( triple-concat
          ( B)
          ( f w) (f x) (f y) (f z')
          ( ap A B w x f p)
          ( ap A B x y f q)
          ( ap A B y z' f r')))
      ( ap-concat A B w x y f p q)
      ( z)
      ( r)

#def triple-concat-eq-first
  ( A : U)
  ( w x y z : A)
  ( p q : w = x)
  ( r : x = y)
  ( s : y = z)
  ( H : p = q)
  : (triple-concat A w x y z p r s) = (triple-concat A w x y z q r s)
  := concat-eq-left A w x z p q H (concat A x y z r s)

#def triple-concat-eq-second
  ( A : U)
  ( w x y z : A)
  ( p : w = x)
  ( q r : x = y)
  ( s : y = z)
  ( H : q = r)
  : (triple-concat A w x y z p q s) = (triple-concat A w x y z p r s)
  :=
    ind-path
      ( x = y)
      ( q)
      ( \ r' H' →
        triple-concat A w x y z p q s = triple-concat A w x y z p r' s)
      ( refl)
      ( r)
      ( H)
```

The function below represents a somewhat special situation, which nevertheless
arises when dealing with certain naturality diagrams. One has a commutative
square and a path that cancels that top path. Then the type below witnesses the
equivalence between the right side of the square (in blue) and a particular
zig-zag of paths, the red zig-zag. We choose the assocativity order for the
triple compostion for ease of use in a later proof.

<?xml version='1.0' encoding='UTF-8'?>
<!-- This file was generated by dvisvgm 3.0.3 -->
<svg version='1.1' xmlns='http://www.w3.org/2000/svg' xmlns:xlink='http://www.w3.org/1999/xlink' width='138.267922pt' height='99.356869pt' viewBox='-65.137809 -68.568977 138.267922 99.356869'>
  <defs>
  <path id='g1-48' d='M1.793275-2.316314C1.798257-2.321295 1.843088-2.41594 1.843088-2.49066C1.843088-2.669988 1.683686-2.784558 1.534247-2.784558C1.330012-2.784558 1.275218-2.630137 1.250311-2.555417L.483188-.398506C.463263-.33873 .463263-.323786 .463263-.318804C.463263-.239103 .672478-.18929 .67746-.18929C.722291-.18929 .732254-.214197 .762142-.273973L1.793275-2.316314Z'/>
  <path id='g0-101' d='M2.977833-1.311083C3.110336-1.311083 3.277709-1.311083 3.277709-1.57609C3.277709-2.412951 2.803487-3.061519 1.903861-3.061519C1.046077-3.061519 .369614-2.364134 .369614-1.513325C.369614-.683437 1.066999 .034869 2.015442 .034869C2.970859 .034869 3.277709-.578829 3.277709-.753176C3.277709-.9066 3.159153-.969365 3.012702-.969365C2.894147-.969365 2.824408-.962391 2.75467-.808966C2.615193-.495143 2.273474-.425405 2.050311-.425405C1.54122-.425405 1.03213-.760149 .920548-1.311083H2.977833ZM.927522-1.764384C1.03213-2.252553 1.443587-2.601245 1.903861-2.601245C2.531507-2.601245 2.691905-2.113076 2.733748-1.764384H.927522Z'/>
  <path id='g0-102' d='M1.806227-2.545455H2.636115C2.740722-2.545455 2.93599-2.545455 2.93599-2.775592S2.740722-3.005729 2.636115-3.005729H1.806227V-3.326526C1.806227-3.765878 2.140971-3.835616 2.433873-3.835616C2.454795-3.612453 2.636115-3.514819 2.761644-3.514819C2.908095-3.514819 3.089415-3.626401 3.089415-3.849564C3.089415-4.29589 2.503611-4.29589 2.39203-4.29589C1.855044-4.29589 1.276214-4.002989 1.276214-3.347447V-3.005729H.606725C.502117-3.005729 .299875-3.005729 .299875-2.775592S.495143-2.545455 .599751-2.545455H1.276214V-.460274H.599751C.502117-.460274 .292902-.460274 .292902-.230137S.502117 0 .599751 0H2.48269C2.580324 0 2.789539 0 2.789539-.230137S2.580324-.460274 2.48269-.460274H1.806227V-2.545455Z'/>
  <path id='g0-108' d='M2.113076-3.961146C2.113076-4.198257 2.043337-4.261021 1.8132-4.261021H.711333C.606725-4.261021 .404483-4.261021 .404483-4.030884S.613699-3.800747 .711333-3.800747H1.583064V-.460274H.711333C.606725-.460274 .404483-.460274 .404483-.230137S.613699 0 .711333 0H2.984807C3.089415 0 3.291656 0 3.291656-.230137S3.082441-.460274 2.984807-.460274H2.113076V-3.961146Z'/>
  <path id='g0-114' d='M1.57609-1.276214C1.57609-2.036364 2.12005-2.580324 2.796513-2.580324C2.810461-2.308344 3.005729-2.252553 3.11731-2.252553C3.291656-2.252553 3.438107-2.378082 3.438107-2.580324C3.438107-2.75467 3.312578-3.040598 2.768618-3.040598C2.127024-3.040598 1.750436-2.670984 1.57609-2.496638V-2.705853C1.57609-2.942964 1.506351-3.005729 1.276214-3.005729H.516065C.418431-3.005729 .209215-3.005729 .209215-2.775592S.418431-2.545455 .516065-2.545455H1.046077V-.460274H.516065C.418431-.460274 .209215-.460274 .209215-.230137S.418431 0 .516065 0H2.315318C2.426899 0 2.615193 0 2.615193-.230137S2.426899-.460274 2.315318-.460274H1.57609V-1.276214Z'/>
  <path id='g2-118' d='M4.662516-3.706102C4.662516-4.244085 4.403487-4.403487 4.224159-4.403487C3.975093-4.403487 3.73599-4.144458 3.73599-3.92528C3.73599-3.795766 3.785803-3.73599 3.895392-3.626401C4.104608-3.427148 4.234122-3.16812 4.234122-2.809465C4.234122-2.391034 3.626401-.109589 2.460772-.109589C1.952677-.109589 1.723537-.458281 1.723537-.976339C1.723537-1.534247 1.992528-2.261519 2.30137-3.088418C2.371108-3.257783 2.420922-3.39726 2.420922-3.58655C2.420922-4.034869 2.102117-4.403487 1.603985-4.403487C.667497-4.403487 .288917-2.958904 .288917-2.86924C.288917-2.769614 .388543-2.769614 .408468-2.769614C.508095-2.769614 .518057-2.789539 .56787-2.948941C.856787-3.955168 1.285181-4.184309 1.574097-4.184309C1.653798-4.184309 1.823163-4.184309 1.823163-3.865504C1.823163-3.616438 1.723537-3.347447 1.653798-3.16812C1.215442-2.012453 1.085928-1.554172 1.085928-1.125778C1.085928-.049813 1.96264 .109589 2.420922 .109589C4.094645 .109589 4.662516-3.188045 4.662516-3.706102Z'/>
  <path id='g2-119' d='M4.60274-3.377335C4.652553-3.596513 4.752179-3.965131 4.752179-4.024907C4.752179-4.204234 4.612702-4.293898 4.463263-4.293898C4.343711-4.293898 4.164384-4.214197 4.094645-4.014944C4.064757-3.945205 3.596513-2.042341 3.526775-1.783313C3.457036-1.484433 3.437111-1.305106 3.437111-1.125778C3.437111-1.016189 3.437111-.996264 3.447073-.946451C3.217933-.418431 2.919054-.109589 2.530511-.109589C1.733499-.109589 1.733499-.846824 1.733499-1.016189C1.733499-1.334994 1.783313-1.723537 2.251557-2.948941C2.361146-3.247821 2.420922-3.387298 2.420922-3.58655C2.420922-4.034869 2.092154-4.403487 1.603985-4.403487C.657534-4.403487 .288917-2.958904 .288917-2.86924C.288917-2.769614 .388543-2.769614 .408468-2.769614C.508095-2.769614 .518057-2.789539 .56787-2.948941C.836862-3.875467 1.225405-4.184309 1.574097-4.184309C1.663761-4.184309 1.823163-4.174346 1.823163-3.855542C1.823163-3.606476 1.713574-3.327522 1.643836-3.158157C1.205479-1.982565 1.085928-1.524284 1.085928-1.145704C1.085928-.239103 1.753425 .109589 2.500623 .109589C2.669988 .109589 3.138232 .109589 3.536737-.587796C3.795766 .049813 4.483188 .109589 4.782067 .109589C5.529265 .109589 5.967621-.518057 6.22665-1.115816C6.56538-1.892902 6.884184-3.227895 6.884184-3.706102C6.884184-4.254047 6.615193-4.403487 6.445828-4.403487C6.196762-4.403487 5.947696-4.144458 5.947696-3.92528C5.947696-3.795766 6.007472-3.73599 6.097136-3.656289C6.206725-3.5467 6.455791-3.287671 6.455791-2.809465C6.455791-2.470735 6.166874-1.494396 5.907846-.986301C5.648817-.458281 5.300125-.109589 4.811955-.109589C4.343711-.109589 4.07472-.408468 4.07472-.976339C4.07472-1.255293 4.144458-1.564134 4.184309-1.703611L4.60274-3.377335Z'/>
  <path id='g2-121' d='M4.841843-3.795766C4.881694-3.935243 4.881694-3.955168 4.881694-4.024907C4.881694-4.204234 4.742217-4.293898 4.592777-4.293898C4.493151-4.293898 4.333748-4.234122 4.244085-4.084682C4.224159-4.034869 4.144458-3.726027 4.104608-3.5467C4.034869-3.287671 3.965131-3.01868 3.905355-2.749689L3.457036-.956413C3.417186-.806974 2.988792-.109589 2.331258-.109589C1.823163-.109589 1.713574-.547945 1.713574-.916563C1.713574-1.374844 1.882939-1.992528 2.221669-2.86924C2.381071-3.277709 2.420922-3.387298 2.420922-3.58655C2.420922-4.034869 2.102117-4.403487 1.603985-4.403487C.657534-4.403487 .288917-2.958904 .288917-2.86924C.288917-2.769614 .388543-2.769614 .408468-2.769614C.508095-2.769614 .518057-2.789539 .56787-2.948941C.836862-3.88543 1.235367-4.184309 1.574097-4.184309C1.653798-4.184309 1.823163-4.184309 1.823163-3.865504C1.823163-3.616438 1.723537-3.35741 1.653798-3.16812C1.255293-2.11208 1.075965-1.544209 1.075965-1.075965C1.075965-.18929 1.703611 .109589 2.291407 .109589C2.67995 .109589 3.01868-.059776 3.297634-.33873C3.16812 .179328 3.048568 .667497 2.650062 1.195517C2.391034 1.534247 2.012453 1.823163 1.554172 1.823163C1.414695 1.823163 .966376 1.793275 .797011 1.404732C.956413 1.404732 1.085928 1.404732 1.225405 1.285181C1.325031 1.195517 1.424658 1.066002 1.424658 .876712C1.424658 .56787 1.155666 .52802 1.05604 .52802C.826899 .52802 .498132 .687422 .498132 1.175592C.498132 1.673724 .936488 2.042341 1.554172 2.042341C2.580324 2.042341 3.606476 1.135741 3.88543 .009963L4.841843-3.795766Z'/>
  <path id='g2-122' d='M1.325031-.826899C1.863014-1.404732 2.15193-1.653798 2.510585-1.96264C2.510585-1.972603 3.128269-2.500623 3.486924-2.859278C4.433375-3.785803 4.652553-4.26401 4.652553-4.303861C4.652553-4.403487 4.562889-4.403487 4.542964-4.403487C4.473225-4.403487 4.443337-4.383562 4.393524-4.293898C4.094645-3.815691 3.88543-3.656289 3.646326-3.656289S3.287671-3.805729 3.138232-3.975093C2.948941-4.204234 2.779577-4.403487 2.450809-4.403487C1.703611-4.403487 1.24533-3.476961 1.24533-3.267746C1.24533-3.217933 1.275218-3.158157 1.364882-3.158157S1.474471-3.20797 1.494396-3.267746C1.683686-3.726027 2.261519-3.73599 2.34122-3.73599C2.550436-3.73599 2.739726-3.666252 2.968867-3.58655C3.367372-3.437111 3.476961-3.437111 3.73599-3.437111C3.377335-3.008717 2.540473-2.291407 2.351183-2.132005L1.454545-1.295143C.777086-.627646 .428394-.059776 .428394 .009963C.428394 .109589 .52802 .109589 .547945 .109589C.627646 .109589 .647572 .089664 .707347-.019925C.936488-.368618 1.235367-.637609 1.554172-.637609C1.783313-.637609 1.882939-.547945 2.132005-.259029C2.30137-.049813 2.480697 .109589 2.769614 .109589C3.755915 .109589 4.333748-1.155666 4.333748-1.424658C4.333748-1.474471 4.293898-1.524284 4.214197-1.524284C4.124533-1.524284 4.104608-1.464508 4.07472-1.39477C3.845579-.747198 3.20797-.557908 2.879203-.557908C2.67995-.557908 2.500623-.617684 2.291407-.687422C1.952677-.816936 1.803238-.856787 1.594022-.856787C1.574097-.856787 1.414695-.856787 1.325031-.826899Z'/>
  <path id='g3-72' d='M5.865006-4.198257C5.927771-4.456289 5.941719-4.51208 6.457783-4.51208C6.611208-4.51208 6.694894-4.51208 6.694894-4.665504C6.694894-4.6934 6.673973-4.763138 6.583313-4.763138C6.381071-4.763138 5.87198-4.735243 5.669738-4.735243C5.551183-4.735243 5.307098-4.735243 5.188543-4.742217C5.049066-4.749191 4.881694-4.763138 4.749191-4.763138C4.707347-4.763138 4.60274-4.763138 4.60274-4.609714C4.60274-4.51208 4.686426-4.51208 4.825903-4.51208C4.832877-4.51208 4.96538-4.51208 5.090909-4.498132C5.23736-4.484184 5.251308-4.470237 5.251308-4.400498C5.251308-4.393524 5.251308-4.351681 5.223412-4.247073L4.811955-2.601245H2.475716L2.880199-4.219178C2.942964-4.456289 2.956912-4.51208 3.493898-4.51208C3.612453-4.51208 3.703113-4.51208 3.703113-4.665504C3.703113-4.6934 3.682192-4.763138 3.591532-4.763138C3.38929-4.763138 2.880199-4.735243 2.677958-4.735243C2.559402-4.735243 2.315318-4.735243 2.196762-4.742217C2.057285-4.749191 1.889913-4.763138 1.75741-4.763138C1.715567-4.763138 1.610959-4.763138 1.610959-4.609714C1.610959-4.51208 1.694645-4.51208 1.834122-4.51208C1.841096-4.51208 1.973599-4.51208 2.099128-4.498132C2.245579-4.484184 2.259527-4.470237 2.259527-4.400498C2.259527-4.38655 2.259527-4.351681 2.231631-4.247073L1.30411-.54396C1.248319-.306849 1.234371-.251059 .690411-.251059C.571856-.251059 .481196-.251059 .481196-.104608C.481196-.034869 .530012 0 .592777 0C.795019 0 1.297136-.027895 1.499377-.027895C1.617933-.027895 1.862017-.027895 1.980573-.020922C2.12005-.013948 2.294396 0 2.426899 0C2.461768 0 2.57335 0 2.57335-.146451C2.57335-.251059 2.503611-.251059 2.343213-.251059C2.231631-.251059 2.203736-.251059 2.078207-.265006C1.924782-.285928 1.924782-.299875 1.924782-.369614C1.924782-.376588 1.924782-.418431 1.952677-.523039L2.412951-2.350187H4.749191L4.29589-.54396C4.2401-.306849 4.226152-.251059 3.682192-.251059C3.563636-.251059 3.472976-.251059 3.472976-.104608C3.472976-.034869 3.521793 0 3.584558 0C3.7868 0 4.288917-.027895 4.491158-.027895C4.609714-.027895 4.853798-.027895 4.972354-.020922C5.111831-.013948 5.286177 0 5.41868 0C5.453549 0 5.565131 0 5.565131-.146451C5.565131-.251059 5.495392-.251059 5.334994-.251059C5.223412-.251059 5.195517-.251059 5.069988-.265006C4.916563-.285928 4.916563-.299875 4.916563-.369614C4.916563-.411457 4.937484-.481196 4.944458-.523039L5.865006-4.198257Z'/>
  <path id='g3-112' d='M.523039 .850809C.474222 1.046077 .460274 1.101868 .18132 1.101868C.09066 1.101868-.006974 1.101868-.006974 1.248319C-.006974 1.325031 .055791 1.352927 .09066 1.352927C.27198 1.352927 .502117 1.325031 .690411 1.325031C.927522 1.325031 1.192528 1.352927 1.422665 1.352927C1.48543 1.352927 1.562142 1.332005 1.562142 1.199502C1.562142 1.101868 1.464508 1.101868 1.380822 1.101868C1.227397 1.101868 1.039103 1.101868 1.039103 1.018182C1.039103 .983313 1.08792 .801993 1.115816 .697385C1.199502 .327771 1.297136-.048817 1.373848-.341719C1.457534-.202242 1.673724 .069738 2.092154 .069738C2.942964 .069738 3.884433-.871731 3.884433-1.910834C3.884433-2.726775 3.319552-3.075467 2.838356-3.075467C2.405978-3.075467 2.036364-2.782565 1.84807-2.587298C1.729514-2.984807 1.338979-3.075467 1.129763-3.075467C.857783-3.075467 .690411-2.894147 .578829-2.705853C.439352-2.468742 .327771-2.050311 .327771-2.008468C.327771-1.917808 .425405-1.917808 .446326-1.917808C.54396-1.917808 .550934-1.93873 .599751-2.127024C.704359-2.531507 .836862-2.880199 1.108842-2.880199C1.290162-2.880199 1.338979-2.726775 1.338979-2.538481C1.338979-2.461768 1.325031-2.371108 1.318057-2.329265L.523039 .850809ZM1.841096-2.238605C2.245579-2.775592 2.594271-2.880199 2.817435-2.880199C3.089415-2.880199 3.326526-2.677958 3.326526-2.203736C3.326526-1.917808 3.173101-1.206476 2.963885-.801993C2.789539-.460274 2.447821-.125529 2.092154-.125529C1.597011-.125529 1.471482-.662516 1.471482-.732254C1.471482-.760149 1.48543-.808966 1.492403-.836862L1.841096-2.238605Z'/>
  <path id='g3-113' d='M3.549689-2.873225C3.556663-2.901121 3.563636-2.942964 3.563636-2.977833C3.563636-3.019676 3.535741-3.075467 3.472976-3.075467C3.403238-3.075467 3.110336-2.838356 2.970859-2.615193C2.901121-2.75467 2.670984-3.075467 2.224658-3.075467C1.332005-3.075467 .425405-2.092154 .425405-1.08792C.425405-.411457 .878705 .069738 1.478456 .069738C1.875965 .069738 2.203736-.18132 2.357161-.313823C2.350187-.292902 2.133998 .585803 2.106102 .704359C2.008468 1.08792 2.001494 1.094894 1.569116 1.101868C1.48543 1.101868 1.387796 1.101868 1.387796 1.255293C1.387796 1.297136 1.422665 1.352927 1.492403 1.352927C1.72254 1.352927 1.980573 1.325031 2.217684 1.325031S2.747696 1.352927 2.963885 1.352927C3.02665 1.352927 3.103362 1.332005 3.103362 1.199502C3.103362 1.101868 3.005729 1.101868 2.922042 1.101868C2.768618 1.101868 2.580324 1.101868 2.580324 1.018182C2.580324 .99726 2.580324 .983313 2.615193 .864757L3.549689-2.873225ZM2.496638-.878705C2.461768-.760149 2.461768-.746202 2.371108-.63462C2.099128-.313823 1.771357-.125529 1.499377-.125529C1.241345-.125529 .990286-.306849 .990286-.801993C.990286-1.171606 1.192528-1.93873 1.352927-2.217684C1.673724-2.775592 2.02939-2.880199 2.224658-2.880199C2.712827-2.880199 2.84533-2.343213 2.84533-2.273474C2.84533-2.238605 2.831382-2.196762 2.824408-2.168867L2.496638-.878705Z'/>
  <path id='g3-114' d='M1.638854-1.408717C1.645828-1.45056 1.806227-2.078207 1.820174-2.113076C1.834122-2.168867 2.036364-2.517559 2.259527-2.684932C2.336239-2.740722 2.524533-2.880199 2.824408-2.880199C2.894147-2.880199 3.068493-2.873225 3.20797-2.782565C2.984807-2.719801 2.901121-2.524533 2.901121-2.399004C2.901121-2.245579 3.019676-2.140971 3.180075-2.140971S3.57061-2.273474 3.57061-2.566376C3.57061-2.929016 3.187049-3.075467 2.831382-3.075467C2.468742-3.075467 2.154919-2.929016 1.84807-2.580324C1.72254-3.005729 1.297136-3.075467 1.129763-3.075467C.871731-3.075467 .697385-2.915068 .585803-2.719801C.425405-2.447821 .327771-2.043337 .327771-2.008468C.327771-1.917808 .425405-1.917808 .446326-1.917808C.54396-1.917808 .550934-1.93873 .599751-2.127024C.704359-2.552428 .836862-2.880199 1.108842-2.880199C1.290162-2.880199 1.338979-2.726775 1.338979-2.538481C1.338979-2.405978 1.276214-2.147945 1.227397-1.959651S1.108842-1.48543 1.073973-1.332005L.850809-.439352C.822914-.348692 .781071-.174346 .781071-.153425C.781071 0 .9066 .069738 1.018182 .069738C1.12279 .069738 1.262267 .006974 1.318057-.132503C1.332005-.174346 1.408717-.481196 1.45056-.655542L1.638854-1.408717Z'/>
  <path id='g3-115' d='M3.005729-2.622167C2.824408-2.580324 2.712827-2.433873 2.712827-2.294396C2.712827-2.133998 2.852304-2.071233 2.942964-2.071233C3.012702-2.071233 3.277709-2.113076 3.277709-2.468742C3.277709-2.922042 2.775592-3.075467 2.350187-3.075467C1.262267-3.075467 1.066999-2.273474 1.066999-2.057285C1.066999-1.799253 1.21345-1.63188 1.311083-1.548194C1.492403-1.408717 1.617933-1.380822 2.099128-1.297136C2.245579-1.26924 2.691905-1.185554 2.691905-.836862C2.691905-.718306 2.615193-.4533 2.322291-.278954C2.050311-.125529 1.708593-.125529 1.624907-.125529C1.345953-.125529 .948443-.188294 .788045-.418431C1.018182-.446326 1.171606-.620672 1.171606-.81594C1.171606-.990286 1.046077-1.073973 .899626-1.073973C.697385-1.073973 .495143-.913574 .495143-.606725C.495143-.188294 .941469 .069738 1.617933 .069738C2.901121 .069738 3.138232-.808966 3.138232-1.080946C3.138232-1.72254 2.433873-1.84807 2.175841-1.896887C2.113076-1.910834 1.93873-1.93873 1.896887-1.952677C1.638854-2.001494 1.513325-2.147945 1.513325-2.30137C1.513325-2.461768 1.638854-2.650062 1.792279-2.747696C1.980573-2.866252 2.224658-2.880199 2.343213-2.880199C2.489664-2.880199 2.852304-2.859278 3.005729-2.622167Z'/>
  <path id='g3-116' d='M1.715567-2.75467H2.426899C2.559402-2.75467 2.650062-2.75467 2.650062-2.908095C2.650062-3.005729 2.559402-3.005729 2.440847-3.005729H1.778331L2.036364-4.037858C2.043337-4.072727 2.057285-4.107597 2.057285-4.135492C2.057285-4.261021 1.959651-4.358655 1.820174-4.358655C1.645828-4.358655 1.54122-4.2401 1.492403-4.05878C1.443587-3.884433 1.534247-4.219178 1.227397-3.005729H.516065C.383562-3.005729 .292902-3.005729 .292902-2.852304C.292902-2.75467 .376588-2.75467 .502117-2.75467H1.164633L.753176-1.108842C.711333-.934496 .648568-.683437 .648568-.592777C.648568-.18132 .99726 .069738 1.39477 .069738C2.168867 .069738 2.608219-.9066 2.608219-.99726S2.517559-1.08792 2.496638-1.08792C2.412951-1.08792 2.405978-1.073973 2.350187-.955417C2.154919-.516065 1.799253-.125529 1.415691-.125529C1.26924-.125529 1.171606-.216189 1.171606-.467248C1.171606-.536986 1.199502-.683437 1.21345-.753176L1.715567-2.75467Z'/>
  </defs>
  <g id='page1'>
  <g transform='matrix(1.6 0 0 1.6 -34.01492 26.29416)'>
  <use x='-19.451805' y='-30.848582' xlink:href='#g2-118'/>
  </g>
  <g transform='matrix(1.6 0 0 1.6 -35.78614 26.29416)'>
  <use x='19.330936' y='-30.848582' xlink:href='#g2-119'/>
  </g>
  <g transform='matrix(1.6 0 0 1.6 -34.01492 26.29416)'>
  <use x='58.113678' y='-30.848582' xlink:href='#g2-118'/>
  </g>
  <g transform='matrix(1.6 0 0 1.6 -34.05928 26.294136)'>
  <use x='19.330936' y='-1.334215' xlink:href='#g2-121'/>
  </g>
  <g transform='matrix(1.6 0 0 1.6 -33.92272 26.294136)'>
  <use x='58.113678' y='-1.334215' xlink:href='#g2-122'/>
  </g>
  <path d='M-49.65632-27.05085H-12.039072' stroke='#d65c5c' fill='none' stroke-width='3.725984' stroke-miterlimit='10'/>
  <path d='M-49.65632-27.05085H-12.039072' stroke='#fff' fill='none' stroke-width='2.4508' stroke-miterlimit='10'/>
  <g fill='#d65c5c' transform='matrix(1.6 0 0 1.6 8.0022 -30.834564)'>
  <use x='-26.334534' y='-1.334215' xlink:href='#g3-112'/>
  </g>
  <path d='M14.167968-27.05085H51.78512' stroke='#000' fill='none' stroke-width='3.725984' stroke-miterlimit='10'/>
  <path d='M14.167968-27.05085H51.78512' stroke='#fff' fill='none' stroke-width='2.4508' stroke-miterlimit='10'/>
  <g transform='matrix(1.6 0 0 1.6 71.9908 -30.834564)'>
  <use x='-26.334534' y='-1.334215' xlink:href='#g3-113'/>
  </g>
  <path d='M1.066402-16.910162V11.144526' stroke='#d65c5c' fill='none' stroke-width='3.725984' stroke-miterlimit='10'/>
  <path d='M1.066402-16.910162V11.144526' stroke='#fff' fill='none' stroke-width='2.4508' stroke-miterlimit='10'/>
  <g fill='#d65c5c' transform='matrix(1.6 0 0 1.6 33.4332 1.652862)'>
  <use x='-26.334534' y='-1.334215' xlink:href='#g3-115'/>
  </g>
  <path d='M12.441408 20.17571H51.87888' stroke='#d65c5c' fill='none' stroke-width='3.725984' stroke-miterlimit='10'/>
  <path d='M12.441408 20.17571H51.87888' stroke='#fff' fill='none' stroke-width='2.4508' stroke-miterlimit='10'/>
  <g fill='#d65c5c' transform='matrix(1.6 0 0 1.6 71.8872 32.922636)'>
  <use x='-26.334534' y='-1.334215' xlink:href='#g3-116'/>
  </g>
  <path d='M63.11712-16.910162V11.144526' stroke='#5c5cd6' fill='none' stroke-width='3.725984' stroke-miterlimit='10'/>
  <path d='M63.11712-16.910162V11.144526' stroke='#fff' fill='none' stroke-width='2.4508' stroke-miterlimit='10'/>
  <g fill='#5c5cd6' transform='matrix(1.6 0 0 1.6 109.0036 1.652862)'>
  <use x='-26.334534' y='-1.334215' xlink:href='#g3-114'/>
  </g>
  <path d='M-50.73824-36.07805C-17.55072-65.30461 19.67968-65.30461 52.8672-36.07805' stroke='#000' fill='none' stroke-width='3.725984' stroke-miterlimit='10'/>
  <path d='M-50.73824-36.07805C-17.55072-65.30461 19.67968-65.30461 52.8672-36.07805' stroke='#fff' fill='none' stroke-width='2.4508' stroke-miterlimit='10'/>
  <g transform='matrix(1.6 0 0 1.6 31.3442 -59.615364)'>
  <use x='-26.334534' y='-1.334215' xlink:href='#g0-114'/>
  <use x='-22.629624' y='-1.334215' xlink:href='#g0-101'/>
  <use x='-18.924714' y='-1.334215' xlink:href='#g0-102'/>
  <use x='-15.219804' y='-1.334215' xlink:href='#g0-108'/>
  </g>
  <path d='M12.441408 11.519534L51.78512-18.42973' stroke='#000' fill='none' stroke-width='3.725984' stroke-miterlimit='10'/>
  <path d='M12.441408 11.519534L51.78512-18.42973' stroke='#fff' fill='none' stroke-width='2.4508' stroke-miterlimit='10'/>
  <path d='M23.0352 3.78907H41.19136V-10.699218H23.0352Z' fill='#fff'/>
  <g transform='matrix(1.6 0 0 1.6 68.6021 2.492462)'>
  <use x='-26.334534' y='-1.334215' xlink:href='#g3-72'/>
  </g>
  <path d='M1.066402-53.69533V-36.07805' stroke='#000' fill='none' stroke-width='3.725984' stroke-miterlimit='10'/>
  <path d='M1.066402-53.69533V-36.07805' stroke='#fff' fill='none' stroke-width='2.4508' stroke-miterlimit='10'/>
  <g transform='matrix(1.6 0 0 1.6 46.95037 -39.727964)'>
  <use x='-26.334534' y='-1.334215' xlink:href='#g3-72'/>
  <use x='-19.276269' y='-4.340732' xlink:href='#g1-48'/>
  </g>
  </g>
  </svg>

```rzk
#def eq-top-cancel-commutative-square
  (A : U)
  (v w y z : A)
  (p : v = w)
  (q : w = v)
  (s : w = y)
  (r : v = z)
  (t : y = z)
  (H : (concat A w v z q r) = (concat A w y z s t))
  (H' : (concat A v w v p q) = refl)
  : r = (concat A v w z p (concat A w y z s t))
  :=
  (concat
    (v = z)
    ( r)
    ( concat A v v z refl r)
    ( concat A v w z p (concat A w y z s t))
    (rev
      (v = z)
      (concat  A v v z refl r)
      ( r )
      (left-unit-concat A v z r))
    (concat
      ( v = z)
      ( concat A v v z refl r)
      ( concat A v v z (concat A v w v p q) r)
      ( concat A v w z p (concat A w y z s t ))
      (rev
        ( v = z )
        (concat A v v z  (concat A v w v p q) r)
        (concat A v v z refl r)
        ( concat-eq-left
          ( A)
          ( v)
          ( v)
          ( z)
          ( concat A v w v p q)
          ( refl )
          ( H')
          ( r) ))
      ( concat
        ( v = z)
        ( concat A v v z (concat A v w v p q) r)
        ( concat A v w z p (concat A w v z q r))
        ( concat A v w z p (concat A w y z s t))
        ( associative-concat A v w v z p q r)
        ( concat-eq-right
          ( A)
          ( v)
          ( w)
          ( z)
          ( p)
          ( concat A w v z q r)
          ( concat A w y z s t)
          ( H)))))
```

It is also convenient to have a a version with the opposite associativity.

```rzk
#def eq-top-cancel-commutative-square'
  ( A : U)
  ( v w y z : A)
  ( p : v = w)
  ( q : w = v)
  ( s : w = y)
  ( r : v = z)
  ( t : y = z)
  ( H : (concat A w v z q r) = (concat A w y z s t))
  ( H' : (concat A v w v p q) = refl)
  : r = ( concat A v y z (concat A v w y p s) t)
  :=
  concat
  ( v = z)
  ( r)
  ( concat A v w z p (concat A w y z s t))
  ( concat A v y z (concat A v w y p s) t)
  ( eq-top-cancel-commutative-square A v w y z p q s r t H H')
  ( rev-associative-concat A v w y z p s t)

```

And a reversed version.

```rzk
#def rev-eq-top-cancel-commutative-square'
  ( A : U)
  ( v w y z : A)
  ( p : v = w)
  ( q : w = v)
  ( s : w = y)
  ( r : v = z)
  ( t : y = z)
  ( H : (concat A w v z q r) = (concat A w y z s t))
  ( H' : (concat A v w v p q) = refl)
  : ( concat A v y z (concat A v w y p s) t) = r
  :=
  rev
  ( v = z)
  ( r)
  ( concat A v y z (concat A v w y p s) t)
  ( eq-top-cancel-commutative-square' A v w y z p q s r t H H')
```

<?xml version='1.0' encoding='UTF-8'?>
<!-- This file was generated by dvisvgm 3.0.3 -->
<svg version='1.1' xmlns='http://www.w3.org/2000/svg' xmlns:xlink='http://www.w3.org/1999/xlink' width='112.891585pt' height='110.568967pt' viewBox='-59.824269 -71.99996 112.891585 110.568967'>
  <defs>
  <path id='g1-48' d='M1.793275-2.316314C1.798257-2.321295 1.843088-2.41594 1.843088-2.49066C1.843088-2.669988 1.683686-2.784558 1.534247-2.784558C1.330012-2.784558 1.275218-2.630137 1.250311-2.555417L.483188-.398506C.463263-.33873 .463263-.323786 .463263-.318804C.463263-.239103 .672478-.18929 .67746-.18929C.722291-.18929 .732254-.214197 .762142-.273973L1.793275-2.316314Z'/>
  <path id='g0-101' d='M2.977833-1.311083C3.110336-1.311083 3.277709-1.311083 3.277709-1.57609C3.277709-2.412951 2.803487-3.061519 1.903861-3.061519C1.046077-3.061519 .369614-2.364134 .369614-1.513325C.369614-.683437 1.066999 .034869 2.015442 .034869C2.970859 .034869 3.277709-.578829 3.277709-.753176C3.277709-.9066 3.159153-.969365 3.012702-.969365C2.894147-.969365 2.824408-.962391 2.75467-.808966C2.615193-.495143 2.273474-.425405 2.050311-.425405C1.54122-.425405 1.03213-.760149 .920548-1.311083H2.977833ZM.927522-1.764384C1.03213-2.252553 1.443587-2.601245 1.903861-2.601245C2.531507-2.601245 2.691905-2.113076 2.733748-1.764384H.927522Z'/>
  <path id='g0-102' d='M1.806227-2.545455H2.636115C2.740722-2.545455 2.93599-2.545455 2.93599-2.775592S2.740722-3.005729 2.636115-3.005729H1.806227V-3.326526C1.806227-3.765878 2.140971-3.835616 2.433873-3.835616C2.454795-3.612453 2.636115-3.514819 2.761644-3.514819C2.908095-3.514819 3.089415-3.626401 3.089415-3.849564C3.089415-4.29589 2.503611-4.29589 2.39203-4.29589C1.855044-4.29589 1.276214-4.002989 1.276214-3.347447V-3.005729H.606725C.502117-3.005729 .299875-3.005729 .299875-2.775592S.495143-2.545455 .599751-2.545455H1.276214V-.460274H.599751C.502117-.460274 .292902-.460274 .292902-.230137S.502117 0 .599751 0H2.48269C2.580324 0 2.789539 0 2.789539-.230137S2.580324-.460274 2.48269-.460274H1.806227V-2.545455Z'/>
  <path id='g0-108' d='M2.113076-3.961146C2.113076-4.198257 2.043337-4.261021 1.8132-4.261021H.711333C.606725-4.261021 .404483-4.261021 .404483-4.030884S.613699-3.800747 .711333-3.800747H1.583064V-.460274H.711333C.606725-.460274 .404483-.460274 .404483-.230137S.613699 0 .711333 0H2.984807C3.089415 0 3.291656 0 3.291656-.230137S3.082441-.460274 2.984807-.460274H2.113076V-3.961146Z'/>
  <path id='g0-114' d='M1.57609-1.276214C1.57609-2.036364 2.12005-2.580324 2.796513-2.580324C2.810461-2.308344 3.005729-2.252553 3.11731-2.252553C3.291656-2.252553 3.438107-2.378082 3.438107-2.580324C3.438107-2.75467 3.312578-3.040598 2.768618-3.040598C2.127024-3.040598 1.750436-2.670984 1.57609-2.496638V-2.705853C1.57609-2.942964 1.506351-3.005729 1.276214-3.005729H.516065C.418431-3.005729 .209215-3.005729 .209215-2.775592S.418431-2.545455 .516065-2.545455H1.046077V-.460274H.516065C.418431-.460274 .209215-.460274 .209215-.230137S.418431 0 .516065 0H2.315318C2.426899 0 2.615193 0 2.615193-.230137S2.426899-.460274 2.315318-.460274H1.57609V-1.276214Z'/>
  <path id='g2-97' d='M3.716065-3.765878C3.536737-4.134496 3.247821-4.403487 2.799502-4.403487C1.633873-4.403487 .398506-2.938979 .398506-1.484433C.398506-.547945 .946451 .109589 1.723537 .109589C1.92279 .109589 2.420922 .069738 3.01868-.637609C3.098381-.219178 3.447073 .109589 3.92528 .109589C4.273973 .109589 4.503113-.119552 4.662516-.438356C4.83188-.797011 4.961395-1.404732 4.961395-1.424658C4.961395-1.524284 4.871731-1.524284 4.841843-1.524284C4.742217-1.524284 4.732254-1.484433 4.702366-1.344956C4.533001-.697385 4.353674-.109589 3.945205-.109589C3.676214-.109589 3.646326-.368618 3.646326-.56787C3.646326-.787049 3.666252-.86675 3.775841-1.305106C3.88543-1.723537 3.905355-1.823163 3.995019-2.201743L4.353674-3.596513C4.423412-3.875467 4.423412-3.895392 4.423412-3.935243C4.423412-4.104608 4.303861-4.204234 4.134496-4.204234C3.895392-4.204234 3.745953-3.985056 3.716065-3.765878ZM3.068493-1.185554C3.01868-1.006227 3.01868-.986301 2.86924-.816936C2.430884-.268991 2.022416-.109589 1.743462-.109589C1.24533-.109589 1.105853-.657534 1.105853-1.046077C1.105853-1.544209 1.424658-2.769614 1.653798-3.227895C1.96264-3.815691 2.410959-4.184309 2.809465-4.184309C3.457036-4.184309 3.596513-3.367372 3.596513-3.307597S3.576588-3.188045 3.566625-3.138232L3.068493-1.185554Z'/>
  <path id='g2-98' d='M2.381071-6.804483C2.381071-6.814446 2.381071-6.914072 2.251557-6.914072C2.022416-6.914072 1.295143-6.834371 1.036115-6.814446C.956413-6.804483 .846824-6.794521 .846824-6.615193C.846824-6.495641 .936488-6.495641 1.085928-6.495641C1.564134-6.495641 1.58406-6.425903 1.58406-6.326276C1.58406-6.256538 1.494396-5.917808 1.444583-5.708593L.627646-2.460772C.508095-1.96264 .468244-1.803238 .468244-1.454545C.468244-.508095 .996264 .109589 1.733499 .109589C2.909091 .109589 4.134496-1.374844 4.134496-2.809465C4.134496-3.716065 3.606476-4.403487 2.809465-4.403487C2.351183-4.403487 1.942715-4.11457 1.643836-3.805729L2.381071-6.804483ZM1.444583-3.038605C1.504359-3.257783 1.504359-3.277709 1.594022-3.387298C2.082192-4.034869 2.530511-4.184309 2.789539-4.184309C3.148194-4.184309 3.417186-3.88543 3.417186-3.247821C3.417186-2.660025 3.088418-1.514321 2.909091-1.135741C2.580324-.468244 2.122042-.109589 1.733499-.109589C1.39477-.109589 1.066002-.37858 1.066002-1.115816C1.066002-1.305106 1.066002-1.494396 1.225405-2.122042L1.444583-3.038605Z'/>
  <path id='g3-72' d='M5.865006-4.198257C5.927771-4.456289 5.941719-4.51208 6.457783-4.51208C6.611208-4.51208 6.694894-4.51208 6.694894-4.665504C6.694894-4.6934 6.673973-4.763138 6.583313-4.763138C6.381071-4.763138 5.87198-4.735243 5.669738-4.735243C5.551183-4.735243 5.307098-4.735243 5.188543-4.742217C5.049066-4.749191 4.881694-4.763138 4.749191-4.763138C4.707347-4.763138 4.60274-4.763138 4.60274-4.609714C4.60274-4.51208 4.686426-4.51208 4.825903-4.51208C4.832877-4.51208 4.96538-4.51208 5.090909-4.498132C5.23736-4.484184 5.251308-4.470237 5.251308-4.400498C5.251308-4.393524 5.251308-4.351681 5.223412-4.247073L4.811955-2.601245H2.475716L2.880199-4.219178C2.942964-4.456289 2.956912-4.51208 3.493898-4.51208C3.612453-4.51208 3.703113-4.51208 3.703113-4.665504C3.703113-4.6934 3.682192-4.763138 3.591532-4.763138C3.38929-4.763138 2.880199-4.735243 2.677958-4.735243C2.559402-4.735243 2.315318-4.735243 2.196762-4.742217C2.057285-4.749191 1.889913-4.763138 1.75741-4.763138C1.715567-4.763138 1.610959-4.763138 1.610959-4.609714C1.610959-4.51208 1.694645-4.51208 1.834122-4.51208C1.841096-4.51208 1.973599-4.51208 2.099128-4.498132C2.245579-4.484184 2.259527-4.470237 2.259527-4.400498C2.259527-4.38655 2.259527-4.351681 2.231631-4.247073L1.30411-.54396C1.248319-.306849 1.234371-.251059 .690411-.251059C.571856-.251059 .481196-.251059 .481196-.104608C.481196-.034869 .530012 0 .592777 0C.795019 0 1.297136-.027895 1.499377-.027895C1.617933-.027895 1.862017-.027895 1.980573-.020922C2.12005-.013948 2.294396 0 2.426899 0C2.461768 0 2.57335 0 2.57335-.146451C2.57335-.251059 2.503611-.251059 2.343213-.251059C2.231631-.251059 2.203736-.251059 2.078207-.265006C1.924782-.285928 1.924782-.299875 1.924782-.369614C1.924782-.376588 1.924782-.418431 1.952677-.523039L2.412951-2.350187H4.749191L4.29589-.54396C4.2401-.306849 4.226152-.251059 3.682192-.251059C3.563636-.251059 3.472976-.251059 3.472976-.104608C3.472976-.034869 3.521793 0 3.584558 0C3.7868 0 4.288917-.027895 4.491158-.027895C4.609714-.027895 4.853798-.027895 4.972354-.020922C5.111831-.013948 5.286177 0 5.41868 0C5.453549 0 5.565131 0 5.565131-.146451C5.565131-.251059 5.495392-.251059 5.334994-.251059C5.223412-.251059 5.195517-.251059 5.069988-.265006C4.916563-.285928 4.916563-.299875 4.916563-.369614C4.916563-.411457 4.937484-.481196 4.944458-.523039L5.865006-4.198257Z'/>
  <path id='g3-112' d='M.523039 .850809C.474222 1.046077 .460274 1.101868 .18132 1.101868C.09066 1.101868-.006974 1.101868-.006974 1.248319C-.006974 1.325031 .055791 1.352927 .09066 1.352927C.27198 1.352927 .502117 1.325031 .690411 1.325031C.927522 1.325031 1.192528 1.352927 1.422665 1.352927C1.48543 1.352927 1.562142 1.332005 1.562142 1.199502C1.562142 1.101868 1.464508 1.101868 1.380822 1.101868C1.227397 1.101868 1.039103 1.101868 1.039103 1.018182C1.039103 .983313 1.08792 .801993 1.115816 .697385C1.199502 .327771 1.297136-.048817 1.373848-.341719C1.457534-.202242 1.673724 .069738 2.092154 .069738C2.942964 .069738 3.884433-.871731 3.884433-1.910834C3.884433-2.726775 3.319552-3.075467 2.838356-3.075467C2.405978-3.075467 2.036364-2.782565 1.84807-2.587298C1.729514-2.984807 1.338979-3.075467 1.129763-3.075467C.857783-3.075467 .690411-2.894147 .578829-2.705853C.439352-2.468742 .327771-2.050311 .327771-2.008468C.327771-1.917808 .425405-1.917808 .446326-1.917808C.54396-1.917808 .550934-1.93873 .599751-2.127024C.704359-2.531507 .836862-2.880199 1.108842-2.880199C1.290162-2.880199 1.338979-2.726775 1.338979-2.538481C1.338979-2.461768 1.325031-2.371108 1.318057-2.329265L.523039 .850809ZM1.841096-2.238605C2.245579-2.775592 2.594271-2.880199 2.817435-2.880199C3.089415-2.880199 3.326526-2.677958 3.326526-2.203736C3.326526-1.917808 3.173101-1.206476 2.963885-.801993C2.789539-.460274 2.447821-.125529 2.092154-.125529C1.597011-.125529 1.471482-.662516 1.471482-.732254C1.471482-.760149 1.48543-.808966 1.492403-.836862L1.841096-2.238605Z'/>
  <path id='g3-113' d='M3.549689-2.873225C3.556663-2.901121 3.563636-2.942964 3.563636-2.977833C3.563636-3.019676 3.535741-3.075467 3.472976-3.075467C3.403238-3.075467 3.110336-2.838356 2.970859-2.615193C2.901121-2.75467 2.670984-3.075467 2.224658-3.075467C1.332005-3.075467 .425405-2.092154 .425405-1.08792C.425405-.411457 .878705 .069738 1.478456 .069738C1.875965 .069738 2.203736-.18132 2.357161-.313823C2.350187-.292902 2.133998 .585803 2.106102 .704359C2.008468 1.08792 2.001494 1.094894 1.569116 1.101868C1.48543 1.101868 1.387796 1.101868 1.387796 1.255293C1.387796 1.297136 1.422665 1.352927 1.492403 1.352927C1.72254 1.352927 1.980573 1.325031 2.217684 1.325031S2.747696 1.352927 2.963885 1.352927C3.02665 1.352927 3.103362 1.332005 3.103362 1.199502C3.103362 1.101868 3.005729 1.101868 2.922042 1.101868C2.768618 1.101868 2.580324 1.101868 2.580324 1.018182C2.580324 .99726 2.580324 .983313 2.615193 .864757L3.549689-2.873225ZM2.496638-.878705C2.461768-.760149 2.461768-.746202 2.371108-.63462C2.099128-.313823 1.771357-.125529 1.499377-.125529C1.241345-.125529 .990286-.306849 .990286-.801993C.990286-1.171606 1.192528-1.93873 1.352927-2.217684C1.673724-2.775592 2.02939-2.880199 2.224658-2.880199C2.712827-2.880199 2.84533-2.343213 2.84533-2.273474C2.84533-2.238605 2.831382-2.196762 2.824408-2.168867L2.496638-.878705Z'/>
  <path id='g3-114' d='M1.638854-1.408717C1.645828-1.45056 1.806227-2.078207 1.820174-2.113076C1.834122-2.168867 2.036364-2.517559 2.259527-2.684932C2.336239-2.740722 2.524533-2.880199 2.824408-2.880199C2.894147-2.880199 3.068493-2.873225 3.20797-2.782565C2.984807-2.719801 2.901121-2.524533 2.901121-2.399004C2.901121-2.245579 3.019676-2.140971 3.180075-2.140971S3.57061-2.273474 3.57061-2.566376C3.57061-2.929016 3.187049-3.075467 2.831382-3.075467C2.468742-3.075467 2.154919-2.929016 1.84807-2.580324C1.72254-3.005729 1.297136-3.075467 1.129763-3.075467C.871731-3.075467 .697385-2.915068 .585803-2.719801C.425405-2.447821 .327771-2.043337 .327771-2.008468C.327771-1.917808 .425405-1.917808 .446326-1.917808C.54396-1.917808 .550934-1.93873 .599751-2.127024C.704359-2.552428 .836862-2.880199 1.108842-2.880199C1.290162-2.880199 1.338979-2.726775 1.338979-2.538481C1.338979-2.405978 1.276214-2.147945 1.227397-1.959651S1.108842-1.48543 1.073973-1.332005L.850809-.439352C.822914-.348692 .781071-.174346 .781071-.153425C.781071 0 .9066 .069738 1.018182 .069738C1.12279 .069738 1.262267 .006974 1.318057-.132503C1.332005-.174346 1.408717-.481196 1.45056-.655542L1.638854-1.408717Z'/>
  </defs>
  <g id='page1'>
  <g transform='matrix(1.6 0 0 1.6 -21.42228 46.44758)'>
  <use x='-24.001243' y='-52.37128' xlink:href='#g2-97'/>
  </g>
  <g transform='matrix(1.6 0 0 1.6 -20.62984 46.44758)'>
  <use x='37.664422' y='-52.37128' xlink:href='#g2-98'/>
  </g>
  <g transform='matrix(1.6 0 0 1.6 -21.42234 46.447592)'>
  <use x='37.664422' y='-4.924116' xlink:href='#g2-97'/>
  </g>
  <path d='M-44.21488-41.33196H32.45312' stroke='#000' fill='none' stroke-width='3.725984' stroke-miterlimit='10'/>
  <path d='M-44.21488-41.33196H32.45312' stroke='#fff' fill='none' stroke-width='2.4508' stroke-miterlimit='10'/>
  <path d='M-12.4336-34.41404H.671872V-48.25004H-12.4336Z' fill='#fff'/>
  <g transform='matrix(1.6 0 0 1.6 40.47484 -32.136708)'>
  <use x='-30.92377' y='-4.924116' xlink:href='#g3-113'/>
  </g>
  <path d='M43.05472-31.19532V25.55476' stroke='#000' fill='none' stroke-width='3.725984' stroke-miterlimit='10'/>
  <path d='M43.05472-31.19532V25.55476' stroke='#fff' fill='none' stroke-width='2.4508' stroke-miterlimit='10'/>
  <g transform='matrix(1.6 0 0 1.6 96.28358 7.459848)'>
  <use x='-30.92377' y='-4.924116' xlink:href='#g3-114'/>
  </g>
  <path d='M-44.74608-50.36332C-21.078128-70.02348 8.51952-70.02348 32.45312-50.1406' stroke='#000' fill='none' stroke-width='3.725984' stroke-miterlimit='10'/>
  <path d='M-44.74608-50.36332C-21.078128-70.02348 8.51952-70.02348 32.45312-50.1406' stroke='#fff' fill='none' stroke-width='2.4508' stroke-miterlimit='10'/>
  <path d='M-12.960944-58.16412H.472656V-71.99996H-12.960944Z' fill='#fff'/>
  <g transform='matrix(1.6 0 0 1.6 39.9474 -55.886108)'>
  <use x='-30.92377' y='-4.924116' xlink:href='#g3-112'/>
  </g>
  <path d='M-44.21488-32.56636L31.66016 25.8242' stroke='#000' fill='none' stroke-width='3.725984' stroke-miterlimit='10'/>
  <path d='M-44.21488-32.56636L31.66016 25.8242' stroke='#fff' fill='none' stroke-width='2.4508' stroke-miterlimit='10'/>
  <g transform='matrix(1.6 0 0 1.6 15.73798 15.077092)'>
  <use x='-30.92377' y='-4.924116' xlink:href='#g0-114'/>
  <use x='-27.21886' y='-4.924116' xlink:href='#g0-101'/>
  <use x='-23.51395' y='-4.924116' xlink:href='#g0-102'/>
  <use x='-19.80904' y='-4.924116' xlink:href='#g0-108'/>
  </g>
  <path d='M-6.156254-59.18364L-5.972661-47.23052' stroke='#000' fill='none' stroke-width='3.725984' stroke-miterlimit='10'/>
  <path d='M-6.156254-59.18364L-5.972661-47.23052' stroke='#fff' fill='none' stroke-width='2.4508' stroke-miterlimit='10'/>
  <g transform='matrix(1.6 0 0 1.6 47.16496 -41.516308)'>
  <use x='-30.92377' y='-4.924116' xlink:href='#g3-72'/>
  </g>
  <path d='M32.45312-33.1758L2.417968-10.062504' stroke='#000' fill='none' stroke-width='3.725984' stroke-miterlimit='10'/>
  <path d='M32.45312-33.1758L2.417968-10.062504' stroke='#fff' fill='none' stroke-width='2.4508' stroke-miterlimit='10'/>
  <path d='M2.41016-10.652344H24.87888V-26.75388H2.41016Z' fill='#fff'/>
  <g transform='matrix(1.6 0 0 1.6 55.32066 -6.204908)'>
  <use x='-30.92377' y='-4.924116' xlink:href='#g3-72'/>
  <use x='-23.865504' y='-7.930633' xlink:href='#g1-48'/>
  </g>
  </g>
  </svg>

Given a homotopy between paths `#! H : p = q`, then we can cancel on the left to
get a homotopy between `#!rzk concat (rev p) q` and `#! refl`.

```rzk

#def htpy-id-cancel-left-concat-left-eq
  (A : U)
  (a b : A)
  (p : a = b)
  (q : a = b)
  (H : p = q)
  (r : b = a)
  (H' : (concat A a b a q r) = refl)
  : (concat A a b a p r) = refl
  :=
  concat
  ( a = a)
  ( concat A a b a p r )
  ( concat A a b a q r )
  ( refl )
  ( concat-eq-left A a b a p q H r)
  ( H' )
```
