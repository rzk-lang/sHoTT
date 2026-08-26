# LARI adjunctions

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Prerequisites

- `hott/*` -
-

## Definition of LARI adjunctions

LARI adjunctions (abbreviation for left adjoint right inverse adjunctions) are
transposing adjunctions with an invertible unit.

```rzk title="BW23, Definition B.1.1"
#def is-transposing-LARI-adj
  ( A B : U)
  ( is-segal-A : is-segal A)
  ( f : A → B)
  ( u : B → A)
  ( adj : is-transposing-adj A B f u)
  : U
  :=
  ( a : A)
  → is-iso-arrow A is-segal-A a (u (f a)) (π₁ (adj a (f a)) (id-hom B (f a)))

#def is-transposing-LARI
  ( A B : U)
  ( is-segal-A : is-segal A)
  ( f : A → B)
  : U
  :=
  Σ ( u : B → A)
  , ( Σ ( adj : is-transposing-adj A B f u)
    , is-transposing-LARI-adj A B is-segal-A f u adj)
```

A dependent initial section gives rise to a LARI adjunction. We first show that
it gives rise to an adjunction:

```rzk
#def is-transposing-adj-is-dependent-initial-section
  ( A : U)
  ( B : A → U)
  ( s : (a : A) → B a)
  ( is-dependent-initial-section-s : is-dependent-initial-section A B s)
  : is-transposing-adj A (total-type A B)
    ( \ a → (a , s a))
    ( projection-total-type A B)
  :=
  \ x (y , Y) →
  equiv-comp
  ( hom (total-type A B) (x , s x) (y , Y))
  ( Σ ( f : hom A x y) , dhom A x y f B (s x) Y)
  ( hom A x y)
  ( axiom-choice-dhom A x y B (s x) Y)
  ( projection-total-type (hom A x y) (\ f → dhom A x y f B (s x) Y)
  , is-equiv-projection-total-type-is-contr-fiber
    ( hom A x y)
    ( \ f → dhom A x y f B (s x) Y)
    ( is-dependent-initial-section-s x y Y))
```

Now we note that this adjunction is a LARI adjunction since it sends `#!rzk
id-hom (total-type A B) (a, s a)` to `#!rzk id-hom A a`.

```rzk
#def is-transposing-LARI-is-dhom-initial-section
  ( A : U)
  ( is-segal-A : is-segal A)
  ( B : A → U)
  ( s : (a : A) → B a)
  ( is-dependent-initial-section-s : is-dependent-initial-section A B s)
  : is-transposing-LARI A (total-type A B) is-segal-A (\ a → (a , s a))
  :=
  ( projection-total-type A B
  , ( is-transposing-adj-is-dependent-initial-section A B s
      ( is-dependent-initial-section-s)
    , \ a → is-iso-arrow-id-hom A is-segal-A a))
```

## LARI adjunctions are initial sections






## Closure properties of LARI adjunctions





