# LARI adjunctions

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Prerequisites

- `hott/*` -
-

```rzk
#assume extext : ExtExt
```

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

```rzk
#section is-initial-section-is-transposing-LARI-adj-is-rezk

#variables A B : U
#variable is-rezk-A : is-rezk A
#variable is-segal-B : is-segal B
#variable f : A → B
#variable u : B → A
#variable adj : is-transposing-adj A B f u
#variable is-LARI-f-u : is-transposing-LARI-adj A B (π₁ is-rezk-A) f u adj

#def total-hom-iso
  ( a : A)
  ( (b, g) : Σ (b : B) , Iso A (π₁ is-rezk-A) a (u b))
  : Σ (b : B) , hom A a (u b)
  := (b, π₁ g)

#def temp-7828-embedding uses (adj is-rezk-A)
  ( a : A)
  : fib B A u a → (Σ (b : B) , hom B (f a) b)
  :=
  \ (b , p) →
  ( b
  , quadruple-comp
    ( u b = a)
    ( a = u b)
    ( Iso A (π₁ is-rezk-A) a (u b))
    ( hom A a (u b))
    ( hom B (f a) b)
    ( π₁ (inv-equiv (hom B (f a) b) (hom A a (u b)) (adj a b)))
    ( \ f → π₁ f)
    ( iso-eq A (π₁ is-rezk-A) a (u b))
    ( rev A (u b) a)
    ( p))

#def is-full-emb-temp-7828-embedding
  uses (adj is-rezk-A extext)
  ( a : A)
  : is-full-emb (fib B A u a) (Σ (b : B) , hom B (f a) b)
  ( temp-7828-embedding a)
  :=
  is-full-emb-quadruple-comp
  ( fib B A u a)
  ( rev-fib B A u a)
  ( Σ (b : B) , Iso A (π₁ is-rezk-A) a (u b))
  ( Σ (b : B) , hom A a (u b))
  ( Σ (b : B) , hom B (f a) b)
  ( \ (b, p) → (b, rev A (u b) a p))
  ( is-full-emb-is-equiv extext
    ( fib B A u a)
    ( rev-fib B A u a)
    ( \ (b, p) → (b, rev A (u b) a p))
    ( is-equiv-total-is-equiv-fiberwise
      ( B)
      ( \ b → u b = a)
      ( \ b → a = u b)
      ( \ b → rev A (u b) a)
      ( \ b → is-equiv-rev A (u b) a)))
  ( \ (b, p) → (b, iso-eq A (π₁ is-rezk-A) a (u b) p))
  ( is-full-emb-is-equiv extext
    ( rev-fib B A u a)
    ( Σ (b : B) , Iso A (π₁ is-rezk-A) a (u b))
    ( \ (b, p) → (b, iso-eq A (π₁ is-rezk-A) a (u b) p))
    ( is-equiv-total-is-equiv-fiberwise
      ( B)
      ( \ b → a = u b)
      ( \ b → Iso A (π₁ is-rezk-A) a (u b))
      ( \ b → iso-eq A (π₁ is-rezk-A) a (u b))
      ( \ b → π₂ is-rezk-A a (u b))))
  ( total-hom-iso a)
  ( is-full-emb-total-type-hom-iso extext A B is-rezk-A (\ _ → a) u)
  ( \ (b, g) → (b, π₁ (inv-equiv (hom B (f a) b) (hom A a (u b)) (adj a b)) g))
  ( is-full-emb-is-equiv extext
    ( Σ (b : B) , hom A a (u b))
    ( Σ (b : B) , hom B (f a) b)
    ( \ (b, g) → (b, π₁ (inv-equiv (hom B (f a) b) (hom A a (u b)) (adj a b)) g))
    ( is-equiv-total-is-equiv-fiberwise
      ( B)
      ( \ b → hom A a (u b))
      ( \ b → hom B (f a) b)
      ( \ b → π₁ (inv-equiv (hom B (f a) b) (hom A a (u b)) (adj a b)))
      ( \ b → π₂ (inv-equiv (hom B (f a) b) (hom A a (u b)) (adj a b)))))


```

```rzk
#def section-is-transposing-LARI-adj
  ( a : A)
  : fib B A u a
  :=
  ( f a
  , rev A a (u (f a))
    ( eq-iso-is-rezk A is-rezk-A a (u (f a))
      ( π₁ (adj a (f a)) (id-hom B (f a)), is-LARI-f-u a)))

#def tmpp-eq
  ( a : A)
  : ( id-hom B (f a))
  = ( quadruple-comp
      ( u (f a) = a)
      ( a = u (f a))
      ( Iso A (π₁ is-rezk-A) a (u (f a)))
      ( hom A a (u (f a)))
      ( hom B (f a) (f a))
      ( π₁ (inv-equiv (hom B (f a) (f a)) (hom A a (u (f a))) (adj a (f a))))
      ( \ f → π₁ f)
      ( iso-eq A (π₁ is-rezk-A) a (u (f a)))
      ( rev A (u (f a)) a)
      ( rev A a (u (f a))
        ( eq-iso-is-rezk A is-rezk-A a (u (f a))
          ( π₁ (adj a (f a)) (id-hom B (f a)), is-LARI-f-u a))))
  :=
  sextuple-concat (hom B (f a) (f a))
  ( id-hom B (f a))
  ( π₁ (inv-equiv (hom B (f a) (f a)) (hom A a (u (f a))) (adj a (f a)))
    (π₁ (adj a (f a)) (id-hom B (f a))))
  ( comp
    ( Iso A (π₁ is-rezk-A) a (u (f a)))
    ( hom A a (u (f a)))
    ( hom B (f a) (f a))
    ( π₁ (inv-equiv (hom B (f a) (f a)) (hom A a (u (f a))) (adj a (f a))))
    ( \ f → π₁ f)
    ( π₁ (adj a (f a)) (id-hom B (f a)), is-LARI-f-u a))
  ( comp
    ( Iso A (π₁ is-rezk-A) a (u (f a)))
    ( hom A a (u (f a)))
    ( hom B (f a) (f a))
    ( π₁ (inv-equiv (hom B (f a) (f a)) (hom A a (u (f a))) (adj a (f a))))
    ( \ f → π₁ f)
    ( iso-eq A (π₁ is-rezk-A) a (u (f a)) (eq-iso-is-rezk A is-rezk-A a (u (f a))
      ( π₁ (adj a (f a)) (id-hom B (f a)), is-LARI-f-u a))))
  ( triple-comp
    ( a = u (f a))
    ( Iso A (π₁ is-rezk-A) a (u (f a)))
    ( hom A a (u (f a)))
    ( hom B (f a) (f a))
    ( π₁ (inv-equiv (hom B (f a) (f a)) (hom A a (u (f a))) (adj a (f a))))
    ( \ f → π₁ f)
    ( iso-eq A (π₁ is-rezk-A) a (u (f a)))
    ( eq-iso-is-rezk A is-rezk-A a (u (f a))
      ( π₁ (adj a (f a)) (id-hom B (f a)), is-LARI-f-u a)))
  ( triple-comp
    ( a = u (f a))
    ( Iso A (π₁ is-rezk-A) a (u (f a)))
    ( hom A a (u (f a)))
    ( hom B (f a) (f a))
    ( π₁ (inv-equiv (hom B (f a) (f a)) (hom A a (u (f a))) (adj a (f a))))
    ( \ f → π₁ f)
    ( iso-eq A (π₁ is-rezk-A) a (u (f a)))
    ( rev A (u (f a)) a (rev A a (u (f a))
      ( eq-iso-is-rezk A is-rezk-A a (u (f a))
        ( π₁ (adj a (f a)) (id-hom B (f a)), is-LARI-f-u a)))))
  ( quadruple-comp
    ( u (f a) = a)
    ( a = u (f a))
    ( Iso A (π₁ is-rezk-A) a (u (f a)))
    ( hom A a (u (f a)))
    ( hom B (f a) (f a))
    ( π₁ (inv-equiv (hom B (f a) (f a)) (hom A a (u (f a))) (adj a (f a))))
    ( \ f → π₁ f)
    ( iso-eq A (π₁ is-rezk-A) a (u (f a)))
    ( rev A (u (f a)) a)
    ( rev A a (u (f a))
      ( eq-iso-is-rezk A is-rezk-A a (u (f a))
        ( π₁ (adj a (f a)) (id-hom B (f a)), is-LARI-f-u a))))
  ( rev (hom B (f a) (f a))
    ( π₁ (inv-equiv (hom B (f a) (f a)) (hom A a (u (f a))) (adj a (f a)))
      (π₁ (adj a (f a)) (id-hom B (f a))))
    ( id-hom B (f a))
    ( inv-equiv-cancel (hom B (f a) (f a)) (hom A a (u (f a)))
      ( adj a (f a))
      ( id-hom B (f a))))
  ( refl)
  ( ap (Iso A (π₁ is-rezk-A) a (u (f a))) (hom B (f a) (f a))
    ( π₁ (adj a (f a)) (id-hom B (f a)), is-LARI-f-u a)
    ( iso-eq A (π₁ is-rezk-A) a (u (f a)) (eq-iso-is-rezk A is-rezk-A a (u (f a))
      ( π₁ (adj a (f a)) (id-hom B (f a)), is-LARI-f-u a)))
    ( comp
      ( Iso A (π₁ is-rezk-A) a (u (f a)))
      ( hom A a (u (f a)))
      ( hom B (f a) (f a))
      ( π₁ (inv-equiv (hom B (f a) (f a)) (hom A a (u (f a))) (adj a (f a))))
      ( \ f → π₁ f))
    ( rev (Iso A (π₁ is-rezk-A) a (u (f a)))
      ( iso-eq A (π₁ is-rezk-A) a (u (f a)) (eq-iso-is-rezk A is-rezk-A a (u (f a))
        ( π₁ (adj a (f a)) (id-hom B (f a)), is-LARI-f-u a)))
      ( π₁ (adj a (f a)) (id-hom B (f a)), is-LARI-f-u a)
      ( compute-iso-eq-eq-iso-is-rezk A is-rezk-A a (u (f a))
        ( π₁ (adj a (f a)) (id-hom B (f a)), is-LARI-f-u a))))
  ( refl)
  ( ap (a = u (f a)) (hom B (f a) (f a))
    ( eq-iso-is-rezk A is-rezk-A a (u (f a))
      ( π₁ (adj a (f a)) (id-hom B (f a)), is-LARI-f-u a))
    ( rev A (u (f a)) a (rev A a (u (f a))
      ( eq-iso-is-rezk A is-rezk-A a (u (f a))
        ( π₁ (adj a (f a)) (id-hom B (f a)), is-LARI-f-u a))))
    ( triple-comp
      ( a = u (f a))
      ( Iso A (π₁ is-rezk-A) a (u (f a)))
      ( hom A a (u (f a)))
      ( hom B (f a) (f a))
      ( π₁ (inv-equiv (hom B (f a) (f a)) (hom A a (u (f a))) (adj a (f a))))
      ( \ f → π₁ f)
      ( iso-eq A (π₁ is-rezk-A) a (u (f a))))
    ( rev-rev' A a (u (f a)) (eq-iso-is-rezk A is-rezk-A a (u (f a))
      ( π₁ (adj a (f a)) (id-hom B (f a)), is-LARI-f-u a))))
  ( refl)

#def tmpp uses (is-LARI-f-u adj u is-rezk-A)
  ( a : A)
  : (f a, id-hom B (f a))
  =_{coslice B (f a)} (temp-7828-embedding a (section-is-transposing-LARI-adj a))
  :=
  path-of-pairs-pair-of-paths B (\ b → hom B (f a) b)
  ( f a)
  ( f a)
  ( refl)
  ( id-hom B (f a))
  ( quadruple-comp
    ( u (f a) = a)
    ( a = u (f a))
    ( Iso A (π₁ is-rezk-A) a (u (f a)))
    ( hom A a (u (f a)))
    ( hom B (f a) (f a))
    ( π₁ (inv-equiv (hom B (f a) (f a)) (hom A a (u (f a))) (adj a (f a))))
    ( \ f → π₁ f)
    ( iso-eq A (π₁ is-rezk-A) a (u (f a)))
    ( rev A (u (f a)) a)
    ( rev A a (u (f a))
      ( eq-iso-is-rezk A is-rezk-A a (u (f a))
        ( π₁ (adj a (f a)) (id-hom B (f a)), is-LARI-f-u a))))
  ( tmpp-eq a)

#def is-initial-section-is-transposing-LARI-adj
  uses (is-LARI-f-u adj is-rezk-A f extext)
  : is-initial-section A (fib B A u) section-is-transposing-LARI-adj
  :=
  \ a → is-initial-is-full-emb-is-initial
  ( fib B A u a)
  ( Σ (b : B) , hom B (f a) b)
  ( temp-7828-embedding a)
  ( is-full-emb-temp-7828-embedding a)
  ( section-is-transposing-LARI-adj a)
  ( transport (coslice B (f a)) (\ x → is-initial (coslice B (f a)) x)
    ( f a, id-hom B (f a))
    ( temp-7828-embedding a (section-is-transposing-LARI-adj a))
    ( tmpp a)
    ( is-initial-id-hom-is-segal B is-segal-B (f a)))


#end is-initial-section-is-transposing-LARI-adj-is-rezk
```
