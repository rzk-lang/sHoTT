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
```

## Properties of propositions

If some family $B$ is fiberwise a proposition, then the type of dependent
functions over $B$ is a proposition:

```rzk
#def fiberwise-prop-is-prop uses (funext weakfunext)
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

If two propositions are bijective, then they are equivalent:

```rzk
#def bijective-props-are-equiv
  ( A B : U)
  ( is-prop-A : is-prop A)
  ( is-prop-B : is-prop B)
  ( f : A → B)
  ( g : B → A)
  : is-equiv A B f
  :=
    ( ( g ,
        \ a →
          (all-elements-equal-is-prop A is-prop-A) ((comp A B A g f) a) a) ,
      ( g ,
        \ b →
          (all-elements-equal-is-prop B is-prop-B) ((comp B A B f g) b) b))
```
