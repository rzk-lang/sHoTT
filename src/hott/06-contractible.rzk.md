# 6. Contractible

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Contractible types

```rzk title="The type of contractibility proofs"
#def is-contr (A : U)
  : U
  := Σ (x : A) , ((y : A) → x = y)
```

## Contractible type data

```rzk
#section contractible-data

#variable A : U
#variable is-contr-A : is-contr A

#def center-contraction
  : A
  := (first is-contr-A)
```

```rzk title="The path from the contraction center to any point"
#def homotopy-contraction
  : ( z : A) → center-contraction = z
  := second is-contr-A

#def realign-homotopy-contraction uses (is-contr-A)
  : ( z : A) → center-contraction = z
  :=
    \ z →
      ( concat A center-contraction center-contraction z
          ( rev A center-contraction center-contraction
            ( homotopy-contraction center-contraction))
          ( homotopy-contraction z))

#def path-realign-homotopy-contraction uses (is-contr-A)
  : ( realign-homotopy-contraction center-contraction) = refl
  :=
    ( left-inverse-concat A center-contraction center-contraction
      ( homotopy-contraction center-contraction))
```

```rzk title="A path between any pair of terms in a contractible type"
#def all-elements-equal-is-contr uses (is-contr-A)
  ( x y : A)
  : x = y
  :=
    zag-zig-concat A x center-contraction y
      ( homotopy-contraction x) (homotopy-contraction y)

#end contractible-data
```

## Unit type

The prototypical contractible type is the unit type, which is built-in to rzk.

```rzk
#def ind-unit
  ( C : Unit → U)
  ( C-unit : C unit)
  ( x : Unit)
  : C x
  := C-unit

#def is-contr-Unit
  : is-contr Unit
  := (unit , \ _ → refl)
```

```rzk title="The terminal projection as a constant map"
#def terminal-map
  ( A : U)
  : A → Unit
  := constant A Unit unit
```

## Identity types of unit types

```rzk
#def has-retraction-terminal-map-path-types-Unit
  ( x y : Unit)
  : has-retraction (x = y) Unit (terminal-map (x = y))
  :=
    ( \ a → refl
    , \ p → ind-path (Unit) (x) (\ y' p' → refl =_{x = y'} p') (refl) (y) (p))

#def has-section-terminal-map-path-types-Unit
  ( x y : Unit)
  : has-section (x = y) Unit (terminal-map (x = y))
  := (\ a → refl , \ a → refl)

#def is-equiv-terminal-map-path-types-Unit
  ( x y : Unit)
  : is-equiv (x = y) Unit (terminal-map (x = y))
  :=
    ( has-retraction-terminal-map-path-types-Unit x y
    , has-section-terminal-map-path-types-Unit x y)
```

## Characterization of contractibility

A type is contractible if and only if its terminal map is an equivalence.

```rzk
#def terminal-map-is-equiv
  ( A : U)
  : U
  := is-equiv A Unit (terminal-map A)

#def has-retraction-terminal-map-is-contr
  ( A : U)
  ( is-contr-A : is-contr A)
  : has-retraction A Unit (terminal-map A)
  :=
    ( constant Unit A (center-contraction A is-contr-A)
    , \ y → (homotopy-contraction A is-contr-A) y)

#def has-section-terminal-map-is-contr
  ( A : U)
  ( is-contr-A : is-contr A)
  : has-section A Unit (terminal-map A)
  := (constant Unit A (center-contraction A is-contr-A) , \ z → refl)

#def is-equiv-terminal-map-is-contr
  ( A : U)
  ( is-contr-A : is-contr A)
  : is-equiv A Unit (terminal-map A)
  :=
    ( has-retraction-terminal-map-is-contr A is-contr-A
    , has-section-terminal-map-is-contr A is-contr-A)

#def is-contr-is-equiv-terminal-map
  ( A : U)
  ( e : terminal-map-is-equiv A)
  : is-contr A
  := ((first (first e)) unit , (second (first e)))

#def is-equiv-terminal-map-iff-is-contr
  ( A : U)
  : iff (is-contr A) (terminal-map-is-equiv A)
  :=
    ( ( is-equiv-terminal-map-is-contr A)
    , ( is-contr-is-equiv-terminal-map A))

#def equiv-with-contractible-domain-implies-contractible-codomain
  ( A B : U)
  ( f : Equiv A B)
  ( is-contr-A : is-contr A)
  : is-contr B
  :=
    ( is-contr-is-equiv-terminal-map B
      ( second
        ( equiv-comp B A Unit
          ( inv-equiv A B f)
          ( ( terminal-map A)
          , ( is-equiv-terminal-map-is-contr A is-contr-A)))))

#def is-contr-path-types-Unit
  ( x y : Unit)
  : is-contr (x = y)
  :=
    ( is-contr-is-equiv-terminal-map
      ( x = y) (is-equiv-terminal-map-path-types-Unit x y))
```

## Retracts of contractible types

A retract of contractible types is contractible.

```rzk title="If A is a retract of a contractible type it has a term"
#section is-contr-is-retract-of-is-contr

#variables A B : U
#variable is-retr-of-A-B : is-retract-of A B

#def is-inhabited-is-contr-is-retract-of uses (is-retr-of-A-B)
  ( is-contr-B : is-contr B)
  : A
  :=
    retraction-is-retract-of A B is-retr-of-A-B
    ( center-contraction B is-contr-B)
```

```rzk title="If A is a retract of a contractible type it has a contracting homotopy"
#def has-homotopy-is-contr-is-retract-of uses (is-retr-of-A-B)
  ( is-contr-B : is-contr B)
  ( a : A)
  : ( is-inhabited-is-contr-is-retract-of is-contr-B) = a
  :=
    concat
      ( A)
      ( is-inhabited-is-contr-is-retract-of is-contr-B)
      ( comp A B A
        ( retraction-is-retract-of A B is-retr-of-A-B)
        ( section-is-retract-of A B is-retr-of-A-B)
        ( a))
      ( a)
      ( ap B A
        ( center-contraction B is-contr-B)
        ( section-is-retract-of A B is-retr-of-A-B a)
        ( retraction-is-retract-of A B is-retr-of-A-B)
        ( homotopy-contraction B is-contr-B
          ( section-is-retract-of A B is-retr-of-A-B a)))
      ( homotopy-is-retract-of A B is-retr-of-A-B a)
```

```rzk title="If A is a retract of a contractible type it is contractible"
#def is-contr-is-retract-of-is-contr uses (is-retr-of-A-B)
  ( is-contr-B : is-contr B)
  : is-contr A
  :=
    ( is-inhabited-is-contr-is-retract-of is-contr-B
    , has-homotopy-is-contr-is-retract-of is-contr-B)

#end is-contr-is-retract-of-is-contr
```

```rzk

```

## Functions between contractible types

```rzk title="Any function between contractible types is an equivalence"
#def is-equiv-are-contr
  ( A B : U)
  ( is-contr-A : is-contr A)
  ( is-contr-B : is-contr B)
  ( f : A → B)
  : is-equiv A B f
  :=
    ( ( \ b → center-contraction A is-contr-A
      , \ a → homotopy-contraction A is-contr-A a)
    , ( \ b → center-contraction A is-contr-A
      , \ b → all-elements-equal-is-contr B is-contr-B
                ( f (center-contraction A is-contr-A)) b))
```

```rzk title="A type equivalent to a contractible type is contractible"
#def is-contr-equiv-is-contr'
  ( A B : U)
  ( e : Equiv A B)
  ( is-contr-B : is-contr B)
  : is-contr A
  :=
    is-contr-is-retract-of-is-contr A B (first e , first (second e)) is-contr-B

#def is-contr-equiv-is-contr
  ( A B : U)
  ( e : Equiv A B)
  ( is-contr-A : is-contr A)
  : is-contr B
  :=
    is-contr-is-retract-of-is-contr B A
      ( first (second (second e)) , (first e , second (second (second e))))
      ( is-contr-A)
```

## Based path spaces

For example, we prove that based path spaces are contractible.

```rzk title="Transport in the space of paths starting at a is concatenation"
#def concat-as-based-transport
  ( A : U)
  ( a x y : A)
  ( p : a = x)
  ( q : x = y)
  : ( transport A (\ z → (a = z)) x y q p) = (concat A a x y p q)
  :=
    ind-path
      ( A)
      ( x)
      ( \ y' q' →
        ( transport A (\ z → (a = z)) x y' q' p) = (concat A a x y' p q'))
      ( refl)
      ( y)
      ( q)
```

The center of contraction in the based path space is `#!rzk (a , refl)`.

```rzk title="The center of contraction in the based path space"
#def center-based-paths
  ( A : U)
  ( a : A)
  : Σ ( x : A) , (a = x)
  := (a , refl)
```

```rzk title="The contracting homotopy in the based path space"
#def contraction-based-paths
  ( A : U)
  ( a : A)
  ( p : Σ (x : A) , a = x)
  : ( center-based-paths A a) = p
  :=
    path-of-pairs-pair-of-paths
      A (\ z → a = z) a (first p) (second p) (refl) (second p)
      ( concat
        ( a = (first p))
        ( transport A (\ z → (a = z)) a (first p) (second p) (refl))
        ( concat A a a (first p) (refl) (second p))
        ( second p)
        ( concat-as-based-transport A a a (first p) (refl) (second p))
        ( left-unit-concat A a (first p) (second p)))
```

```rzk title="Based path spaces are contractible"
#def is-contr-based-paths
  ( A : U)
  ( a : A)
  : is-contr (Σ (x : A) , a = x)
  := (center-based-paths A a , contraction-based-paths A a)
```

## Contractible products

```rzk
#def is-contr-product
  ( A B : U)
  ( is-contr-A : is-contr A)
  ( is-contr-B : is-contr B)
  : is-contr (product A B)
  :=
    ( ( first is-contr-A , first is-contr-B)
    , \ p → path-product A B
              ( first is-contr-A) (first p)
              ( first is-contr-B) (second p)
              ( second is-contr-A (first p))
              ( second is-contr-B (second p)))

#def first-is-contr-product
  ( A B : U)
  ( AxB-is-contr : is-contr (product A B))
  : is-contr A
  :=
    ( first (first AxB-is-contr)
    , \ a → first-path-product A B
              ( first AxB-is-contr)
              ( a , second (first AxB-is-contr))
              ( second AxB-is-contr (a , second (first AxB-is-contr))))

#def is-contr-base-is-contr-Σ
  ( A : U)
  ( B : A → U)
  ( b : (a : A) → B a)
  ( is-contr-AB : is-contr (Σ (a : A) , B a))
  : is-contr A
  :=
    ( first (first is-contr-AB)
    , \ a → first-path-Σ A B
              ( first is-contr-AB)
              ( a , b a)
              ( second is-contr-AB (a , b a)))
```

## Weak function extensionality

The weak function extensionality axiom asserts that if a dependent type is
locally contractible then its dependent function type is contractible.

Weak function extensionality is logically equivalent to function extensionality.
However, for various applications it may be useful to have it stated as a
separate hypothesis.

```rzk title="Weak function extensionality gives us contractible pi types"
#def WeakFunExt
  : U
  :=
    ( A : U) → (C : A → U)
  → ( is-contr-C : (a : A) → is-contr (C a))
  → ( is-contr ((a : A) → C a))

```

Function extensionality implies weak function extensionality.

```rzk
#def map-weakfunext
  ( A : U)
  ( C : A → U)
  ( is-contr-C : (a : A) → is-contr (C a))
  : ( a : A) → C a
  :=
  \ a → first (is-contr-C a)

#def weakfunext-funext
  ( funext : FunExt)
  : WeakFunExt
  :=
  \ A C is-contr-C →
  ( map-weakfunext A C is-contr-C
  , ( \ g →
      ( eq-htpy funext
        ( A)
        ( C)
        ( map-weakfunext A C is-contr-C)
        ( g)
        ( \ a → second (is-contr-C a) (g a)))))
```

## Singleton induction

A type is contractible if and only if it has singleton induction.

```rzk
#def ev-pt
  ( A : U)
  ( a : A)
  ( B : A → U)
  : ( ( x : A) → B x) → B a
  := \ f → f a

#def has-singleton-induction-pointed
  ( A : U)
  ( a : A)
  ( B : A → U)
  : U
  := has-section ((x : A) → B x) (B a) (ev-pt A a B)

#def has-singleton-induction-pointed-structure
  ( A : U)
  ( a : A)
  : U
  := (B : A → U) → has-section ((x : A) → B x) (B a) (ev-pt A a B)

#def has-singleton-induction
  ( A : U)
  : U
  := Σ (a : A) , (B : A → U) → (has-singleton-induction-pointed A a B)

#def ind-sing
  ( A : U)
  ( a : A)
  ( B : A → U)
  ( singleton-ind-A : has-singleton-induction-pointed A a B)
  : ( B a) → ((x : A) → B x)
  := (first singleton-ind-A)

#def compute-ind-sing
  ( A : U)
  ( a : A)
  ( B : A → U)
  ( singleton-ind-A : has-singleton-induction-pointed A a B)
  : ( homotopy
      ( B a)
      ( B a)
      ( comp
        ( B a)
        ( ( x : A) → B x)
        ( B a)
        ( ev-pt A a B)
        ( ind-sing A a B singleton-ind-A))
      ( identity (B a)))
  := (second singleton-ind-A)

#def contr-implies-singleton-induction-ind
  ( A : U)
  ( is-contr-A : is-contr A)
  : ( has-singleton-induction A)
  :=
    ( ( center-contraction A is-contr-A)
    , \ B →
        ( ( \ b x →
                ( transport A B
                  ( center-contraction A is-contr-A) x
                  ( realign-homotopy-contraction A is-contr-A x) b))
        , ( \ b →
                ( ap
                  ( ( center-contraction A is-contr-A)
                  = ( center-contraction A is-contr-A))
                  ( B (center-contraction A is-contr-A))
                  ( realign-homotopy-contraction A is-contr-A
                    ( center-contraction A is-contr-A))
                  refl_{(center-contraction A is-contr-A)}
                  ( \ p →
                    ( transport-loop A B (center-contraction A is-contr-A) b p))
                  ( path-realign-homotopy-contraction A is-contr-A)))))

#def contr-implies-singleton-induction-pointed
  ( A : U)
  ( is-contr-A : is-contr A)
  ( B : A → U)
  : has-singleton-induction-pointed A (center-contraction A is-contr-A) B
  := (second (contr-implies-singleton-induction-ind A is-contr-A)) B

#def singleton-induction-ind-implies-contr
  ( A : U)
  ( a : A)
  ( f : has-singleton-induction-pointed-structure A a)
  : ( is-contr A)
  := (a , (first (f (\ x → a = x))) (refl_{a}))
```

## Identity types of contractible types

We show that any two paths between the same endpoints in a contractible type are
the same.

In a contractible type any path $p : x = y$ is equal to the path constructed in
`all-elements-equal-is-contr`.

```rzk
#define path-eq-path-through-center-is-contr
  ( A : U)
  ( is-contr-A : is-contr A)
  ( x y : A)
  ( p : x = y)
  : ( ( all-elements-equal-is-contr A is-contr-A x y) = p)
  :=
    ind-path
    ( A)
    ( x)
    ( \ y' p' → (all-elements-equal-is-contr A is-contr-A x y') = p')
    ( left-inverse-concat A (center-contraction A is-contr-A) x (homotopy-contraction A is-contr-A x))
    ( y)
    ( p)

```

Finally, in a contractible type any two paths between the same end points are
equal. There are many possible proofs of this (e.g. identifying contractible
types with the unit type where it is more transparent), but we proceed by gluing
together the two identifications to the out and back path.

```rzk
#define all-paths-equal-is-contr
 ( A : U)
 ( is-contr-A : is-contr A)
 ( x y : A)
 ( p q : x = y)
  : ( p = q)
  :=
  concat
    ( x = y)
    ( p)
    ( all-elements-equal-is-contr A is-contr-A x y)
    ( q)
    ( rev
      ( x = y)
      ( all-elements-equal-is-contr A is-contr-A x y)
      ( p)
      ( path-eq-path-through-center-is-contr A is-contr-A x y p))
    ( path-eq-path-through-center-is-contr A is-contr-A x y q)
```
