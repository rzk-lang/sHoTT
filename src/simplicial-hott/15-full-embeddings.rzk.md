# ?. Full Embeddings

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Prerequisites

- `hott/*` - We require various prerequisites from homotopy type theory, for
  instance equivalences.
- `03-extension-types.rzk.md` - We use extension extensionality for certain
  proofs in this section.
- `06-2cat-of-segal-types.rzk.md` - We make use of the functoriality of
  functions.
- `09-yoneda.rzk.md` - We make use of initial and final objects.

```rzk
#assume extext : ExtExt
```

## Full Embeddings

A full embedding is a map that is an equivalence on hom-types:

```rzk
#def is-full-emb
  ( A B : U)
  ( f : A → B)
  : U
  :=
    ( x : A)
  → ( y : A)
  → is-equiv (hom A x y) (hom B (f x) (f y)) (ap-hom A B f x y)
```

This property is also known under the term "fully faithful". We chose the name
full embedding, since from the type theoretic viewpoint this is closer to the
already existing concept `is-emb` from HoTT. Additionally, it should be possible
to prove that `is-full-emb` implies `is-emb`. However, this proof is rather
challenging and has not been finished due to time constraints.

## Equivalences are full embeddings

Equivalences are full embeddings -- the proof is already present in
`06-2cat-of-segal-types.rzk.md` by using extension extensionality.

```rzk
#def is-full-emb-is-equiv
  ( A B : U)
  ( f : A → B)
  ( is-equiv-f : is-equiv A B f)
  : is-full-emb A B f
  := is-equiv-ap-hom-is-equiv extext A B f is-equiv-f
```

## Compositions of full embeddings are full embeddings

Since equivalences compose, we can easily derive that full embeddings also have
this property.

```rzk
#def is-full-emb-comp
  ( A B C : U)
  ( f : A → B)
  ( is-full-emb-f : is-full-emb A B f)
  ( g : B → C)
  ( is-full-emb-g : is-full-emb B C g)
  : is-full-emb A C (comp A B C g f)
  :=
  \ x y →
  is-equiv-comp
  ( hom A x y)
  ( hom B (f x) (f y))
  ( hom C (g (f x)) (g (f y)))
  ( ap-hom A B f x y)
  ( is-full-emb-f x y)
  ( ap-hom B C g (f x) (f y))
  ( is-full-emb-g (f x) (f y))
```

```rzk
#def is-full-emb-triple-comp
  ( A B C D : U)
  ( f : A → B)
  ( is-full-emb-f : is-full-emb A B f)
  ( g : B → C)
  ( is-full-emb-g : is-full-emb B C g)
  ( h : C → D)
  ( is-full-emb-h : is-full-emb C D h)
  : is-full-emb A D (triple-comp A B C D h g f)
  :=
  is-full-emb-comp A B D
  ( f) (is-full-emb-f)
  ( comp B C D h g)
  ( is-full-emb-comp B C D
    ( g) (is-full-emb-g)
    ( h) (is-full-emb-h))
```

```rzk
#def is-full-emb-quadruple-comp
  ( A B C D E : U)
  ( f : A → B)
  ( is-full-emb-f : is-full-emb A B f)
  ( g : B → C)
  ( is-full-emb-g : is-full-emb B C g)
  ( h : C → D)
  ( is-full-emb-h : is-full-emb C D h)
  ( i : D → E)
  ( is-full-emb-i : is-full-emb D E i)
  : is-full-emb A E (quadruple-comp A B C D E i h g f)
  :=
  is-full-emb-comp A B E
  ( f) (is-full-emb-f)
  ( triple-comp B C D E i h g)
  ( is-full-emb-triple-comp B C D E
    ( g) (is-full-emb-g)
    ( h) (is-full-emb-h)
    ( i) (is-full-emb-i))
```

## Full embeddings detect initial and final objects

A simple fact that follows from the equivalence of hom types is that initial and
final objects can be detected by full embeddings:

```rzk
#def is-initial-is-full-emb-is-initial
  ( A B : U)
  ( f : A → B)
  ( is-full-emb-f : is-full-emb A B f)
  ( a : A)
  ( is-initial-fa : is-initial B (f a))
  : is-initial A a
  :=
  \ y →
  is-contr-equiv-is-contr' (hom A a y) (hom B (f a) (f y))
  ( ap-hom A B f a y , is-full-emb-f a y)
  ( is-initial-fa (f y))

#def is-final-is-full-emb-is-final
  ( A B : U)
  ( f : A → B)
  ( is-full-emb-f : is-full-emb A B f)
  ( a : A)
  ( is-final-fa : is-final B (f a))
  : is-final A a
  :=
  \ x →
  is-contr-equiv-is-contr' (hom A x a) (hom B (f x) (f a))
  ( ap-hom A B f x a , is-full-emb-f x a)
  ( is-final-fa (f x))
```
