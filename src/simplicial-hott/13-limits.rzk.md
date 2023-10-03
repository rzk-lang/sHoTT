# 13. Limits and colimits

These formalisations correspond in part to Section 3 of the BM22 paper.

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Definition limits and colimits

Given a function `#!rzk f : A → B` and `#!rzk b:B` we define the type of cones
over `#!rzk f`.

```rzk
#def cone
  ( A B : U )
  ( f : A → B )
  : U
  := Σ (b : B), hom (A → B) (constant A B b) f
```

```rzk
#def cone2
  (A B : U)
  : (A → B) → (B) → U
  := \ f → \ b → (hom (A → B) (constant A B b) f)
```
```rzk
#def constant-nat-trans-components
  (A B : U)
  ( x y : B )
  ( k : hom B x y)
  : hom (A → B) (constant A B x) (constant A B y)
  := \ t a → ( constant A ( hom B x y ) k ) a t
```



```rzk
#def cone-precomposition
  ( A B : U)
  ( is-segal-B : is-segal B)
  ( f : A → B )
  ( b x : B )
  : (cone2 A B f x) → (hom B b x) →  (cone2 A B f b)
  := \ α k → vertical-comp-nat-trans
              ( A)
              ( \ a → B )
              ( \ a → is-segal-B )
              ( constant A B b)
              ( constant A B x)
              ( \ a → \ t → constant-nat-trans A B b x k a t)
              ( α)
```

Given a function `#!rzk f : A → B` and `#!rzk b:B` we define the type of cocones
under `#!rzk f`.

```rzk
#def cocone
  ( A B : U )
  ( f : A → B )
  : U
  := Σ (b : B), hom ( A → B) f (constant A B b)
```

```rzk
#def cocone2
  (A B : U)
  : (f : A → B) → (b : B) → U
  := \ f → \ b → (hom ( A → B) f (constant A B b))
```

We define a colimit for `#!rzk f : A → B` as an initial cocone under `#!rzk f`.

```rzk
#def colimit
  ( A B : U )
  ( f : A → B )
  : U
  := Σ ( x : cocone A B f ) , is-initial (cocone A B f) x
```

We define a limit of `#!rzk f : A → B` as a terminal cone over `#!rzk f`.

```rzk
#def limit
  ( A B : U )
  ( f : A → B )
  : U
  :=  Σ ( x : cone A B f ) , is-final (cone A B f) x
```

## Uniqueness of initial and final objects.

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

## Uniqueness up to isomophism of (co)limits
