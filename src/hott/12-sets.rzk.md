# 12. Propositions

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Sets

A type is a set when its identity types are propositions.

```rzk
#def is-set
  ( A : U)
  : U
  := (x : A) → (y : A) → (p : x = y) → (q : x = y) → p = q
```
