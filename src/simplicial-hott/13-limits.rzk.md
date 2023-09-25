# 13. Limits and colimits

These formalisations correspond in part to Section 3 of the BM22 paper.

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

Some of the definitions in this file rely on function extensionality and
extension extensionality:

```rzk
-- #assume funext : FunExt
-- #assume extext : ExtExt
```

## Uniqueness of initial and final objects. [From 10-rezk-types.rzk.md]

In a Segal type, initial objects are isomorphic.

```rzk
#def iso-initial
  ( A : U)
  ( is-segal-A : is-segal A)
  ( a b : A)
  ( is-initial-a : is-initial A a)
  ( is-initial-b : is-initial A b)
  : Iso A is-segal-A a b
  :=
    ( first (is-initial-a b) ,
      ( ( first (is-initial-b a) ,
          eq-is-contr
            ( hom A a a)
            ( is-initial-a a)
            ( comp-is-segal A is-segal-A a b a
              ( first (is-initial-a b))
              ( first (is-initial-b a)))
            ( id-hom A a)) ,
        ( first (is-initial-b a) ,
          eq-is-contr
            ( hom A b b)
            ( is-initial-b b)
            ( comp-is-segal A is-segal-A b a b
              ( first (is-initial-b a))
              ( first (is-initial-a b)))
            ( id-hom A b))))
```

In a Segal type, final objects are isomorphic.

```rzk
#def iso-final
  ( A : U)
  ( is-segal-A : is-segal A)
  ( a b : A)
  ( is-final-a : is-final A a)
  ( is-final-b : is-final A b)
  ( iso : Iso A is-segal-A a b)
  : Iso A is-segal-A a b
  :=
    ( first (is-final-b a) ,
      ( ( first (is-final-a b) ,
          eq-is-contr
            ( hom A a a)
            ( is-final-a a)
            ( comp-is-segal A is-segal-A a b a
              ( first (is-final-b a))
              ( first (is-final-a b)))
            ( id-hom A a)) ,
        ( first (is-final-a b) ,
          eq-is-contr
            ( hom A b b)
            ( is-final-b b)
            ( comp-is-segal A is-segal-A b a b
              ( first (is-final-a b))
              ( first (is-final-b a)))
            ( id-hom A b))))
```

## Definition (co)limits

Given a function $f: A → B$ and $b:B$ we define the type of cones over f.

```rzk
#def cone
  ( A B : U )
  ( f : A → B )
  : U
  := ∑ (b : B), hom ( A → B) (constant A B b) f
```

Given a function $f: A → B$ and $b:B$ we define the type of cocones under f.

```rzk
#def cocone
  ( A B : U )
  ( f : A → B )
  : U
  := ∑ (b : B), hom ( A → B) f (constant A B b)
```

We give the definition of a colimit for $ f : A → B$ as an initial cocone under
$f$.

```rzk
#def colimit
  ( A B : U )
  ( f : A → B )
  : U
  := ( x : cocone A B f ) → is-initial (cocone A B f) x
```

Now the definition of a limit of $ f : A →
B$, this is terminal element in the space of cones
over $f$.

```rzk
#def limit
  ( A B : U )
  ( f : A → B )
  : U
  := ( x : cone A B f ) → is-final (cone A B f) x
```

## Uniqueness up to isomophism of (co)limits

