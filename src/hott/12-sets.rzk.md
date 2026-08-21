# 12. Sets

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

## Sets

A type is a set when its identity types are propositions.

```rzk
#def is-set
  ( A : U)
  : U
  := (x : A) → (y : A) → (p : x = y) → (q : x = y) → p = q
```

Being a set is a proposition.

```rzk
#def is-property-is-set uses (funext)
  ( A : U)
  : is-prop (is-set A)
  -- This proof was written by ChatGPT 5.6 Sol.
  := \ s →
    ( is-prop-fiberwise-prop2 funext A
      ( \ _ → A)
      ( \ x y → all-elements-equal (x = y))
      ( \ x y →
        is-prop-fiberwise-prop2 funext (x = y)
          ( \ _ → x = y)
          ( \ p q → p = q)
          ( \ p q →
            is-prop-is-contr (p = q)
              ( (is-prop-all-elements-equal (x = y) (s x y)) p q)))) s
```

An equivalent definition is a 0-type.

```rzk
#def is-0-type
  ( A : U)
  : U
  := (x y : A) → is-prop (x = y)
```

Being a 0-type is also a proposition.

```rzk
#def is-property-is-0-type uses (weakfunext funext)
  ( A : U)
  : is-prop (is-0-type A)
  -- This proof was written by ChatGPT 5.6 Sol.
  := is-prop-fiberwise-prop2 funext A
    (\ _ → A) (\ x y → is-prop (x = y))
    (\ x y → is-prop-is-prop funext weakfunext (x = y))
```

Next, we explicitly construct the equivalence between sets and 0-types.

```rzk
#def is-set-to-is-0-type
  ( A : U)
  : is-set A → is-0-type A
  := \ s x y → is-prop-all-elements-equal (x = y) (s x y)

#def is-0-type-to-is-set
  ( A : U)
  : is-0-type A → is-set A
  := \ t x y → all-elements-equal-is-prop (x = y) (t x y)

#def is-set-is-0-type uses (weakfunext funext)
  ( A : U)
  : Equiv (is-set A) (is-0-type A)
  := equiv-iff-is-prop-is-prop (is-set A) (is-0-type A)
      (is-property-is-set A)
      (is-property-is-0-type A)
      (is-set-to-is-0-type A, is-0-type-to-is-set A)
```
