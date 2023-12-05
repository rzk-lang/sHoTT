# 9. Propositions

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

Some of the definitions in this file rely on function extensionality and weak
function extensionality:

```rzk
#assume funext : FunExt
#assume weakfunext : WeakFunExt
```

## Propositions

A type is a proposition when its identity types are contractible.

```rzk
#def is-prop
  ( A : U)
  : U
  := (a : A) → (b : A) → is-contr (a = b)
```

For example, the type `Unit` is a proposition. In fact we will show below that
this is true for every contractible type.

```rzk
#def is-prop-Unit
  : is-prop Unit
  := \ x y → (is-contr-path-types-Unit x y)
```

## Alternative characterizations: definitions

```rzk
#def all-elements-equal
  ( A : U)
  : U
  := (a : A) → (b : A) → (a = b)

#def is-contr-is-inhabited
  ( A : U)
  : U
  := A → is-contr A

#def is-emb-terminal-map
  ( A : U)
  : U
  := is-emb A Unit (terminal-map A)
```

## Alternative characterizations: proofs

```rzk
#def all-elements-equal-is-prop
  ( A : U)
  ( is-prop-A : is-prop A)
  : all-elements-equal A
  := \ a b → (first (is-prop-A a b))

#def is-contr-is-inhabited-all-elements-equal
  ( A : U)
  ( all-elements-equal-A : all-elements-equal A)
  : is-contr-is-inhabited A
  := \ a → (a , all-elements-equal-A a)

#def is-contr-is-inhabited-is-prop
  ( A : U)
  ( is-prop-A : is-prop A)
  : is-contr-is-inhabited A
  :=
    \ a → (a , \ b → first (is-prop-A a b))

#def terminal-map-is-emb-is-inhabited-is-contr-is-inhabited
  ( A : U)
  ( c : is-contr-is-inhabited A)
  : A → (is-emb-terminal-map A)
  :=
    \ x →
      ( is-emb-is-equiv A Unit (terminal-map A)
        ( is-equiv-terminal-map-is-contr A (c x)))

#def terminal-map-is-emb-is-contr-is-inhabited
  ( A : U)
  ( c : is-contr-is-inhabited A)
  : ( is-emb-terminal-map A)
  :=
    ( is-emb-is-inhabited-emb A Unit (terminal-map A)
      ( terminal-map-is-emb-is-inhabited-is-contr-is-inhabited A c))

#def is-prop-is-emb-terminal-map
  ( A : U)
  ( f : is-emb-terminal-map A)
  : is-prop A
  :=
    \ x y →
      ( is-contr-equiv-is-contr' (x = y) (unit = unit)
        ( ( ap A Unit x y (terminal-map A)) , (f x y))
        ( is-contr-path-types-Unit unit unit))

#def is-prop-is-contr-is-inhabited
  ( A : U)
  ( c : is-contr-is-inhabited A)
  : is-prop A
  :=
    ( is-prop-is-emb-terminal-map A
      ( terminal-map-is-emb-is-contr-is-inhabited A c))

#def is-prop-all-elements-equal
  ( A : U)
  ( all-elements-equal-A : all-elements-equal A)
  : is-prop A
  :=
    is-prop-is-contr-is-inhabited A
    ( is-contr-is-inhabited-all-elements-equal A all-elements-equal-A)
```

## Properties of propositions

If two propositions are logically equivalent, then they are equivalent:

```rzk
#def is-equiv-iff-is-prop-is-prop
  ( A B : U)
  ( is-prop-A : is-prop A)
  ( is-prop-B : is-prop B)
  ( ( f , g) : iff A B)
  : is-equiv A B f
  :=
    ( ( g
      , \ a →
          ( all-elements-equal-is-prop A is-prop-A) ((comp A B A g f) a) a)
    , ( g
      , \ b →
          ( all-elements-equal-is-prop B is-prop-B) ((comp B A B f g) b) b))

#def equiv-iff-is-prop-is-prop
  ( A B : U)
  ( is-prop-A : is-prop A)
  ( is-prop-B : is-prop B)
  ( e : iff A B)
  : Equiv A B
  := (first e , is-equiv-iff-is-prop-is-prop A B is-prop-A is-prop-B e)
```

Every contractible type is a proposition:

```rzk
#def is-prop-is-contr
  ( A : U)
  ( is-contr-A : is-contr A)
  : is-prop A
  :=
    is-prop-is-contr-is-inhabited A (\ _ → is-contr-A)
```

All parallel paths in a proposition are equal.

```rzk
#def all-paths-equal-is-prop
  ( A : U)
  ( is-prop-A : is-prop A)
  ( a b : A)
  : ( p : a = b) → (q : a = b) → p = q
  :=
    all-elements-equal-is-prop (a = b)
    ( is-prop-is-contr (a = b)
      ( is-prop-A a b))
```

## Proposition induction

```rzk
#def ind-prop
  ( A : U)
  ( is-prop-A : is-prop A)
  ( B : A → U)
  ( a : A)
  ( b : B a)
  ( x : A)
  : B x
  :=
    transport A B a x (first (is-prop-A a x)) b
```

It is convenient to able to apply this to contractible types without explicitly
invoking `is-prop-is-contr`.

```rzk
#def ind-prop-is-contr
  ( A : U)
  ( is-contr-A : is-contr A)
  : ( B : A → U) → (a : A) → (b : B a) → (x : A) → B x
  := ind-prop A (is-prop-is-contr A is-contr-A)
```

## Closure properties of propositions

### Retracts and equivalences

Retracts of propositions are propositions:

```rzk
#def is-prop-is-retract-of-is-prop
  ( A B : U)
  ( ( f , (g , η)) : is-retract-of A B) -- f : A → B with retraction g
  ( is-prop-B : is-prop B)
  : is-prop A
  :=
    is-prop-all-elements-equal A
    ( \ a a' →
      triple-concat A a (g (f a)) (g (f a')) a'
      ( rev A (g (f a)) a (η a))
      ( ap B A (f a) (f a') g (first (is-prop-B (f a) (f a'))))
      ( η a'))
```

In particular, propositions are closed under equivalences:

```rzk
#def is-prop-Equiv-is-prop
  ( A B : U)
  ( ( f , (rec-f , _)) : Equiv A B)
  : is-prop B → is-prop A
  := is-prop-is-retract-of-is-prop A B (f , rec-f)

#def is-prop-Equiv-is-prop'
  ( A B : U)
  ( A≃B : Equiv A B)
  : is-prop A → is-prop B
  := is-prop-Equiv-is-prop B A (inv-equiv A B A≃B)
```

### Product types

If some family `#!rzk B : A → U` is fiberwise a proposition, then the type of
dependent functions `#!rzk (x : A) → B x` is a proposition.

```rzk
#def is-prop-fiberwise-prop uses (funext weakfunext)
  ( A : U)
  ( B : A → U)
  ( fiberwise-prop-B : (x : A) → is-prop (B x))
  : is-prop ((x : A) → B x)
  :=
    \ f g →
    is-contr-equiv-is-contr'
      ( f = g)
      ( ( x : A) → f x = g x)
      ( equiv-FunExt funext A B f g)
      ( weakfunext A (\ x → f x = g x) (\ x → fiberwise-prop-B x (f x) (g x)))
```

### Sum types over a propositions

We consider a type family `C : A → U` over a proposition `A`.

```rzk
#section families-over-propositions
#variable A : U
#variable is-prop-A : is-prop A
#variable C : A → U
```

If each `C a` is a proposition, then so is the total type `total-type A C`.

```rzk
#def is-prop-total-type-is-fiberwise-prop-is-prop-base uses (is-prop-A)
  ( is-fiberwise-prop-C : (a : A) → is-prop (C a))
  : is-prop (total-type A C)
  :=
    is-prop-all-elements-equal (total-type A C)
    ( \ (a , c) (a' , c') →
      eq-pair A C (a , c) (a' , c')
      ( first (is-prop-A a a')
      , first
        ( is-fiberwise-prop-C a'
          ( transport A C a a' (first (is-prop-A a a')) c)
          ( c'))))
```

Conversely, if the total type `#!rzk total-type A C` is a proposition, then so
is every fiber `#!rzk C a`.

```rzk
#def is-fiberwise-prop-is-prop-total-type-is-prop-base uses (is-prop-A)
  ( is-prop-ΣC : is-prop (total-type A C))
  ( a : A)
  : is-prop (C a)
  :=
    is-prop-all-elements-equal (C a)
    ( \ c c' →
      transport
      ( a = a)
      ( \ p → transport A C a a p c = c')
      ( first-path-Σ A C (a , c) (a , c') (first (is-prop-ΣC (a , c) (a , c'))))
      ( refl)
      ( all-paths-equal-is-prop A is-prop-A a a
        ( first-path-Σ A C (a , c) (a , c') (first (is-prop-ΣC (a , c) (a , c'))))
        ( refl))
      ( second-path-Σ A C (a , c) (a , c') (first (is-prop-ΣC (a , c) (a , c')))))

#end families-over-propositions
```

## Propositions and embeddings

A map `#!rzk f : A → B` is an embedding if and only if its fibers are
propositions.

```rzk
#def is-contr-image-based-paths-is-emb
  ( A B : U)
  ( f : A → B)
  ( is-emb-f : is-emb A B f)
  ( x : A)
  : is-contr (Σ (y : A) , f x = f y)
  :=
  is-contr-total-are-equiv-from-paths A x
  ( \ y → f x = f y)
  ( \ y → ap A B x y f)
  ( \ y → is-emb-f x y)

#def is-contr-image-endpoint-based-paths-is-emb
  ( A B : U)
  ( f : A → B)
  ( is-emb-f : is-emb A B f)
  ( y : A)
  : is-contr (Σ (x : A) , f x = f y)
  :=
    is-contr-equiv-is-contr'
    ( Σ ( x : A) , f x = f y)
    ( Σ ( x : A) , f y = f x)
    ( total-equiv-family-of-equiv A (\ x → f x = f y) (\ x → f y = f x)
      ( \ x → equiv-rev B (f x) (f y)))
    ( is-contr-image-based-paths-is-emb A B f is-emb-f y)

#def is-contr-fib-over-image-is-emb
  ( A B : U)
  ( f : A → B)
  ( is-emb-f : is-emb A B f)
  ( y : A)
  : is-contr (fib A B f (f y))
  := is-contr-image-endpoint-based-paths-is-emb A B f is-emb-f y

#def is-contr-is-inhabited-fib-is-emb
  ( A B : U)
  ( f : A → B)
  ( is-emb-f : is-emb A B f)
  : ( b : B) → is-contr-is-inhabited (fib A B f b)
  :=
  ind-fib A B f
  ( \ b p → is-contr (fib A B f b))
  ( \ a → is-contr-fib-over-image-is-emb A B f is-emb-f a)

#def is-prop-fib-is-emb
  ( A B : U)
  ( f : A → B)
  ( is-emb-f : is-emb A B f)
  ( b : B)
  : is-prop (fib A B f b)
  :=
  is-prop-is-contr-is-inhabited (fib A B f b)
  ( is-contr-is-inhabited-fib-is-emb A B f is-emb-f b)

#def is-contr-image-based-paths-is-contr-is-inhabited-fib
  ( A B : U)
  ( f : A → B)
  ( is-contr-is-inhabited-fib-f : (b : B) → is-contr-is-inhabited (fib A B f b))
  ( x : A)
  : is-contr (Σ (y : A) , f x = f y)
  :=
  is-contr-equiv-is-contr'
  ( Σ ( y : A) , f x = f y)
  ( Σ ( y : A) , f y = f x)
  ( total-equiv-family-of-equiv A (\ y → f x = f y) (\ y → f y = f x)
    ( \ y → equiv-rev B (f x) (f y)))
  ( is-contr-is-inhabited-fib-f (f x) ((x , refl)))

#def is-emb-is-contr-is-inhabited-fib
  ( A B : U)
  ( f : A → B)
  ( is-contr-is-inhabited-fib-f : (b : B) → is-contr-is-inhabited (fib A B f b))
  : is-emb A B f
  :=
  \ x y →
  are-equiv-from-paths-is-contr-total A x (\ z → f x = f z)(\ z → ap A B x z f)
  ( is-contr-image-based-paths-is-contr-is-inhabited-fib A B f is-contr-is-inhabited-fib-f x) y

#def is-emb-is-prop-fib
  ( A B : U)
  ( f : A → B)
  ( is-prop-fib-f : (b : B) → is-prop (fib A B f b))
  : is-emb A B f
  :=
  is-emb-is-contr-is-inhabited-fib A B f
  ( \ b → is-contr-is-inhabited-is-prop (fib A B f b) (is-prop-fib-f b))

#def is-emb-iff-is-prop-fib
  ( A B : U)
  ( f : A → B)
  : iff (is-emb A B f) ((b : B) → is-prop (fib A B f b))
  := (is-prop-fib-is-emb A B f , is-emb-is-prop-fib A B f)
```

## Subtypes

A family of propositions `#!rzk P : A → U` over a type `#!rzk A` may be thought
of as a predicate.

```rzk
#def is-predicate
  ( A : U)
  ( P : A → U)
  : U
  := (a : A) → is-prop (P a)
```

When `#!rzk P` is a predicate on `#!rzk A` then `#!rzk total-type A P` is
referred to a subtype of `#!rzk A`.

```rzk
#def is-emb-subtype-projection
  ( A : U)
  ( P : A → U)
  ( is-predicate-P : is-predicate A P)
  : is-emb (total-type A P) A (projection-total-type A P)
  :=
  is-emb-is-prop-fib (total-type A P) A (projection-total-type A P)
  ( \ a →
    is-prop-Equiv-is-prop'
    ( P a) (fib (total-type A P) A (projection-total-type A P) a)
    ( equiv-homotopy-fiber-strict-fiber A P a) (is-predicate-P a))
```

The subtype projection embedding reflects identifications.

```rzk
#def subtype-eq-reflection
  ( A : U)
  ( P : A → U)
  ( is-predicate-P : is-predicate A P)
  : ( ( a , p) : total-type A P)
    → ( ( b , q) : total-type A P)
    → ( a = b) → (a , p) =_{total-type A P} (b , q)
  :=
  inv-ap-is-emb (total-type A P) A (projection-total-type A P)
  ( is-emb-subtype-projection A P is-predicate-P)
```
