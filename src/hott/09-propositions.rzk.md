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
  (A : U)
  : U
  := (a : A) → (b : A) → is-contr (a = b)

#def is-prop-Unit
  : is-prop Unit
  := \ x y → (path-types-of-Unit-are-contractible x y)
```

## Alternative characterizations: definitions

```rzk
#def all-elements-equal
  (A : U)
  : U
  := (a : A) → (b : A) → (a = b)

#def is-contr-is-inhabited
  (A : U)
  : U
  := A → is-contr A

#def is-emb-terminal-map
  (A : U)
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

#def terminal-map-is-emb-is-inhabited-is-contr-is-inhabited
  ( A : U)
  ( c : is-contr-is-inhabited A)
  : A → (is-emb-terminal-map A)
  :=
    \ x →
      ( is-emb-is-equiv A Unit (terminal-map A)
        ( contr-implies-terminal-map-is-equiv A (c x)))

#def terminal-map-is-emb-is-contr-is-inhabited
  ( A : U)
  ( c : is-contr-is-inhabited A)
  : (is-emb-terminal-map A)
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
        ( (ap A Unit x y (terminal-map A)) , (f x y))
        ( path-types-of-Unit-are-contractible unit unit))

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
    (  is-contr-is-inhabited-all-elements-equal A all-elements-equal-A)
```

## Properties of propositions

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
      ( (x : A) → f x = g x)
      ( equiv-FunExt funext A B f g)
      ( weakfunext A (\ x → f x = g x) (\ x → fiberwise-prop-B x (f x) (g x)))
```

If two propositions are logically equivalent, then they are equivalent:

```rzk
#def is-equiv-iff-is-prop-is-prop
  ( A B : U)
  ( is-prop-A : is-prop A)
  ( is-prop-B : is-prop B)
  ( (f , g) : iff A B)
  : is-equiv A B f
  :=
    ( ( g ,
        \ a →
          (all-elements-equal-is-prop A is-prop-A) ((comp A B A g f) a) a) ,
      ( g ,
        \ b →
          (all-elements-equal-is-prop B is-prop-B) ((comp B A B f g) b) b))

#def equiv-iff-is-prop-is-prop
  ( A B : U)
  ( is-prop-A : is-prop A)
  ( is-prop-B : is-prop B)
  ( e : iff A B)
  : Equiv A B
  := (first e, is-equiv-iff-is-prop-is-prop A B is-prop-A is-prop-B e)
```

Every contractible type is a proposition:

```rzk
#def is-prop-is-contr
  ( A : U)
  ( is-contr-A : is-contr A)
  : is-prop A
  :=
    is-prop-is-contr-is-inhabited A ( \ _ → is-contr-A)
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

It is convenient to able to apply this to contractible types
without explicitly invoking `is-prop-is-contr`.

```rzk
#def ind-prop-is-contr
  ( A : U)
  ( is-contr-A : is-contr A)
  : ( B : A → U) → ( a : A) → ( b : B a) → ( x : A) →  B x
  := ind-prop A (is-prop-is-contr A is-contr-A)
```

## Families of propositions over a propositions

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
    ( \ (a, c) (a', c') →
      eq-pair A C (a, c) (a', c')
      ( first ( is-prop-A a a')
      , first
        ( is-fiberwise-prop-C a'
          ( transport A C a a' (first (is-prop-A a a')) c)
          ( c'))))
```

Conversely, if the total type `total-type A C` is a proposition,
then so is every fiber `C a`.

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
      ( first-path-Σ A C (a, c) (a, c') ( first (is-prop-ΣC (a, c) (a, c'))))
      ( refl)
      ( all-paths-equal-is-prop A is-prop-A a a
        ( first-path-Σ A C (a, c) (a, c') ( first (is-prop-ΣC (a, c) (a, c'))))
        ( refl))
      ( second-path-Σ A C (a, c) (a, c') ( first (is-prop-ΣC (a, c) (a, c')))))

#end families-over-propositions
```
