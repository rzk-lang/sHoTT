# 0. Common

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## products of types

```rzk
#def product
  ( A B : U)
  : U
  := Σ (x : A) , B
```

The following demonstrates the syntax for constructing terms in Sigma types:

```rzk
#def diagonal
  ( A : U)
  ( a : A)
  : product A A
  := (a , a)
```

## The type of logical equivalences between types

```rzk
#def iff
  ( A B : U)
  : U
  := product (A → B) (B → A)
```

## Basic function definitions

```rzk
#section basic-functions

#variables A B C D E : U

#def comp
  ( g : B → C)
  ( f : A → B)
  : A → C
  := \ z → g (f z)

#def triple-comp
  ( h : C → D)
  ( g : B → C)
  ( f : A → B)
  : A → D
  := \ z → h (g (f z))

#def quadruple-comp
  ( k : D → E)
  ( h : C → D)
  ( g : B → C)
  ( f : A → B)
  : A → E
  := \ z → k (h (g (f z)))

#def identity
  : A → A
  := \ a → a

#def constant
  ( b : B)
  : A → B
  := \ a → b

#end basic-functions
```

## Substitution

```rzk title="Reindexing a type family along a function into the base type"
#def reindex
  ( A B : U)
  ( f : B → A)
  ( C : A → U)
  : B → U
  := \ b → C (f b)
```

## Maps

```rzk
#def Map
  : U
  := Σ ((A' , A) : product U U) , (A' → A)

#def the-map-Map
  ( ( ( A' , A) , α) : Map)
  : A' → A
  := α

#def the-domain-Map
  ( ( ( A' , _) , _) : Map)
  : U
  := A'

#def the-codomain-Map
  ( ( ( _ , A) , _) : Map)
  : U
  := A
```
