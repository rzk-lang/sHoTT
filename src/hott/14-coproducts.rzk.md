# 14. Coproducts

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

We define binary coproducts and describe their maps and identity types. The
identity-type characterization follows the encode-decode argument in the HoTT
Book, Section 2.12.

We first define the empty type, which we will use to describe identity types of
a coproduct.

```rzk
#data Empty

#check ind-Empty : (C : Empty → U) → (x : Empty) → C x

#check rec-Empty : (C : U) → Empty → C

#def is-empty
  ( A : U)
  : U
  := A → Empty
```

## Coproduct types

The type `#!rzk coproduct A B` represents $A+B$. Its constructors are the two
inclusions `#!rzk inl A B : A → coproduct A B` and
`#!rzk inr A B : B → coproduct A B`.

```rzk
#data coproduct
  ( A B : U)
  := inl (a : A)
   | inr (b : B)
```

### Uniqueness by coproduct induction

A dependent function on a coproduct is pointwise equal to the function obtained
by restricting it to each summand and then applying induction.

```rzk
#def htpy-ind-coproduct
  ( A B : U)
  ( C : coproduct A B → U)
  ( h : (z : coproduct A B) → C z)
  ( z : coproduct A B)
  : ind-coproduct A B C
    ( \ a → h (inl A B a))
    ( \ b → h (inr A B b))
    ( z)
  = h z
  :=
  match z
    ( inl a ⇒ refl
    | inr b ⇒ refl)

#def htpy-rec-coproduct
  ( A B C : U)
  ( h : coproduct A B → C)
  ( z : coproduct A B)
  : rec-coproduct A B C
    ( \ a → h (inl A B a))
    ( \ b → h (inr A B b))
    ( z)
  = h z
  :=
  match z
    ( inl a ⇒ refl
    | inr b ⇒ refl)
```

### Maps between coproducts

Maps `#!rzk f : A → C` and `#!rzk g : B → D` induce a map $f+g: A + B \to C+D$,
acting separately on the two summands.

```rzk
#def map-coproduct
  ( A B C D : U)
  ( f : A → C)
  ( g : B → D)
  : coproduct A B → coproduct C D
  :=
  rec-coproduct A B (coproduct C D)
  ( \ a → inl C D (f a))
  ( \ b → inr C D (g b))
```

The action of `#!rzk map-coproduct` preserves identities, composition, and
homotopies.

```rzk
#def htpy-map-coproduct-identity
  ( A B : U)
  ( z : coproduct A B)
  : map-coproduct A B A B (identity A) (identity B) z = z
  :=
  match z
    ( inl a ⇒ refl
    | inr b ⇒ refl)

#def htpy-map-coproduct-comp
  ( A B C D E F : U)
  ( f : A → C)
  ( g : B → D)
  ( h : C → E)
  ( k : D → F)
  ( z : coproduct A B)
  : map-coproduct A B E F (comp A C E h f) (comp B D F k g) z
  = map-coproduct C D E F h k (map-coproduct A B C D f g z)
  :=
  match z
    ( inl a ⇒ refl
    | inr b ⇒ refl)

#def htpy-map-coproduct
  ( A B C D : U)
  ( f f' : A → C)
  ( g g' : B → D)
  ( H : homotopy A C f f')
  ( K : homotopy B D g g')
  ( z : coproduct A B)
  : map-coproduct A B C D f g z = map-coproduct A B C D f' g' z
  :=
  match z
    ( inl a ⇒ ap C (coproduct C D) (f a) (f' a) (inl C D) (H a)
    | inr b ⇒ ap D (coproduct C D) (g b) (g' b) (inr C D) (K b))
```

### Swapping the summands

```rzk
#def swap-coproduct
  ( A B : U)
  : coproduct A B → coproduct B A
  := rec-coproduct A B (coproduct B A) (inr B A) (inl B A)

#def htpy-swap-swap-coproduct
  ( A B : U)
  ( z : coproduct A B)
  : swap-coproduct B A (swap-coproduct A B z) = z
  :=
  match z
    ( inl a ⇒ refl
    | inr b ⇒ refl)

#def equiv-swap-coproduct
  ( A B : U)
  : Equiv (coproduct A B) (coproduct B A)
  :=
  ( swap-coproduct A B
  , is-equiv-has-inverse
    ( coproduct A B)
    ( coproduct B A)
    ( swap-coproduct A B)
    ( swap-coproduct B A
    , ( htpy-swap-swap-coproduct A B
      , htpy-swap-swap-coproduct B A)))
```

### Transport in families of coproducts

Transport preserves each summand and transports its element in the corresponding
family.

```rzk
#def compute-transport-coproduct-inl
  ( X : U)
  ( A B : X → U)
  ( x y : X)
  ( p : x = y)
  ( a : A x)
  : transport X (\ z → coproduct (A z) (B z)) x y p (inl (A x) (B x) a)
  = inl (A y) (B y) (transport X A x y p a)
  :=
  ind-path X x
  ( \ y' p' →
    transport X (\ z → coproduct (A z) (B z)) x y' p'
    ( inl (A x) (B x) a)
    = inl (A y') (B y') (transport X A x y' p' a))
  ( refl)
  ( y)
  ( p)

#def compute-transport-coproduct-inr
  ( X : U)
  ( A B : X → U)
  ( x y : X)
  ( p : x = y)
  ( b : B x)
  : transport X (\ z → coproduct (A z) (B z)) x y p (inr (A x) (B x) b)
  = inr (A y) (B y) (transport X B x y p b)
  :=
  ind-path X x
  ( \ y' p' →
    transport X (\ z → coproduct (A z) (B z)) x y' p'
    ( inr (A x) (B x) b)
    = inr (A y') (B y') (transport X B x y' p' b))
  ( refl)
  ( y)
  ( p)
```

### Identity types of coproducts

We define a family `#!rzk Eq-coproduct A B x y` by four cases. Within a summand
it is the identity type of that summand; between different summands it is the
empty type. We then prove that it is equivalent to `#!rzk x = y`.

```rzk
#def Eq-coproduct
  ( A B : U)
  ( x y : coproduct A B)
  : U
  :=
  match x
    ( inl a ⇒
      match y
        ( inl a' ⇒ a = a'
        | inr b' ⇒ Empty)
    | inr b ⇒
      match y
        ( inl a' ⇒ Empty
        | inr b' ⇒ b = b'))

#def refl-Eq-coproduct
  ( A B : U)
  ( x : coproduct A B)
  : Eq-coproduct A B x x
  :=
  match x
    ( inl a ⇒ refl
    | inr b ⇒ refl)
```

```rzk
#def coproduct-eq
  ( A B : U)
  ( x y : coproduct A B)
  ( p : x = y)
  : Eq-coproduct A B x y
  :=
  transport (coproduct A B) (Eq-coproduct A B x) x y p
  ( refl-Eq-coproduct A B x)

#def eq-coproduct
  ( A B : U)
  ( x y : coproduct A B)
  : Eq-coproduct A B x y → (x = y)
  :=
  match x
    ( inl a ⇒
      match y
        ( inl a' ⇒ ap A (coproduct A B) a a' (inl A B)
        | inr b' ⇒ rec-Empty (inl A B a = inr A B b'))
    | inr b ⇒
      match y
        ( inl a' ⇒ rec-Empty (inr A B b = inl A B a')
        | inr b' ⇒ ap B (coproduct A B) b b' (inr A B)))
```

```rzk
#def eq-coproduct-refl
  ( A B : U)
  ( x : coproduct A B)
  : eq-coproduct A B x x (refl-Eq-coproduct A B x) = refl
  :=
  match x
    ( inl a ⇒ refl
    | inr b ⇒ refl)

#def eq-coproduct-coproduct-eq
  ( A B : U)
  ( x y : coproduct A B)
  ( p : x = y)
  : eq-coproduct A B x y (coproduct-eq A B x y p) = p
  :=
  ind-path (coproduct A B) x
  ( \ y' p' →
    eq-coproduct A B x y' (coproduct-eq A B x y' p') = p')
  ( eq-coproduct-refl A B x)
  ( y)
  ( p)
```

```rzk
#def coproduct-eq-eq-coproduct
  ( A B : U)
  ( x y : coproduct A B)
  : ( e : Eq-coproduct A B x y)
  → coproduct-eq A B x y (eq-coproduct A B x y e) = e
  :=
  match x
    ( inl a ⇒
      match y
        ( inl a' ⇒
          ind-path A a
          ( \ a'' p →
            coproduct-eq A B (inl A B a) (inl A B a'')
            ( eq-coproduct A B (inl A B a) (inl A B a'') p)
            = p)
          ( refl)
          ( a')
        | inr b' ⇒
          ind-Empty
          ( \ e →
            coproduct-eq A B (inl A B a) (inr A B b')
            ( eq-coproduct A B (inl A B a) (inr A B b') e)
            = e))
    | inr b ⇒
      match y
        ( inl a' ⇒
          ind-Empty
          ( \ e →
            coproduct-eq A B (inr A B b) (inl A B a')
            ( eq-coproduct A B (inr A B b) (inl A B a') e)
            = e)
        | inr b' ⇒
          ind-path B b
          ( \ b'' p →
            coproduct-eq A B (inr A B b) (inr A B b'')
            ( eq-coproduct A B (inr A B b) (inr A B b'') p)
            = p)
          ( refl)
          ( b')))
```

```rzk
#def is-equiv-coproduct-eq
  ( A B : U)
  ( x y : coproduct A B)
  : is-equiv (x = y) (Eq-coproduct A B x y) (coproduct-eq A B x y)
  :=
  is-equiv-has-inverse
  ( x = y)
  ( Eq-coproduct A B x y)
  ( coproduct-eq A B x y)
  ( eq-coproduct A B x y
  , ( eq-coproduct-coproduct-eq A B x y
    , coproduct-eq-eq-coproduct A B x y))

#def extensionality-coproduct
  ( A B : U)
  ( x y : coproduct A B)
  : Equiv (x = y) (Eq-coproduct A B x y)
  := (coproduct-eq A B x y , is-equiv-coproduct-eq A B x y)
```

For easy access we also write down the other direction of the equivalence.

```rzk
#def is-equiv-eq-coproduct
  ( A B : U)
  ( x y : coproduct A B)
  : is-equiv (Eq-coproduct A B x y) (x = y) (eq-coproduct A B x y)
  :=
  is-equiv-has-inverse
  ( Eq-coproduct A B x y)
  ( x = y)
  ( eq-coproduct A B x y)
  ( coproduct-eq A B x y
  , ( coproduct-eq-eq-coproduct A B x y
    , eq-coproduct-coproduct-eq A B x y))
```

Specializing the equivalence to constructors gives all four identity-type
computations directly.

```rzk
#def equiv-eq-inl
  ( A B : U)
  ( a a' : A)
  : Equiv (inl A B a = inl A B a') (a = a')
  := extensionality-coproduct A B (inl A B a) (inl A B a')

#def equiv-eq-inr
  ( A B : U)
  ( b b' : B)
  : Equiv (inr A B b = inr A B b') (b = b')
  := extensionality-coproduct A B (inr A B b) (inr A B b')

#def equiv-eq-inl-inr
  ( A B : U)
  ( a : A)
  ( b : B)
  : Equiv (inl A B a = inr A B b) Empty
  := extensionality-coproduct A B (inl A B a) (inr A B b)

#def equiv-eq-inr-inl
  ( A B : U)
  ( b : B)
  ( a : A)
  : Equiv (inr A B b = inl A B a) Empty
  := extensionality-coproduct A B (inr A B b) (inl A B a)
```

### The coproduct inclusions are disjoint embeddings

```rzk
#def is-emb-inl
  ( A B : U)
  : is-emb A (coproduct A B) (inl A B)
  := \ a a' → is-equiv-eq-coproduct A B (inl A B a) (inl A B a')

#def is-emb-inr
  ( A B : U)
  : is-emb B (coproduct A B) (inr A B)
  := \ b b' → is-equiv-eq-coproduct A B (inr A B b) (inr A B b')

#def is-empty-eq-inl-inr
  ( A B : U)
  ( a : A)
  ( b : B)
  : is-empty (inl A B a = inr A B b)
  := coproduct-eq A B (inl A B a) (inr A B b)

#def is-empty-eq-inr-inl
  ( A B : U)
  ( b : B)
  ( a : A)
  : is-empty (inr A B b = inl A B a)
  := coproduct-eq A B (inr A B b) (inl A B a)
```

### The universal property of coproducts

This is the coproduct universal property as discussed in Section 2.15 of the
HoTT Book.

```rzk
#assume funext
  : FunExt
```

```rzk
#def restrict-coproduct
  ( A B C : U)
  ( h : coproduct A B → C)
  : product (A → C) (B → C)
  := (\ a → h (inl A B a) , \ b → h (inr A B b))

#def equiv-universal-property-coproduct
  uses (funext)
  ( A B C : U)
  : Equiv (coproduct A B → C) (product (A → C) (B → C))
  :=
  ( restrict-coproduct A B C
  , is-equiv-has-inverse
    ( coproduct A B → C)
    ( product (A → C) (B → C))
    ( restrict-coproduct A B C)
    ( \ fg → rec-coproduct A B C (first fg) (second fg)
    , ( \ h →
        eq-htpy funext (coproduct A B) (\ _ → C)
        ( rec-coproduct A B C
          ( \ a → h (inl A B a))
          ( \ b → h (inr A B b)))
        ( h)
        ( htpy-rec-coproduct A B C h)
      , \ (f , g) → refl)))
```

### Coproducts of (k+2)-truncated types are (k+2)-truncated types

```rzk
#def is-trunc-succ-Empty
  ( k : 𝕋)
  : is-trunc (succ-𝕋 k) Empty
  := \ u v → rec-Empty (is-trunc k (u = v)) u

#def is-trunc-coproduct-is-trunc
  ( k : 𝕋)
  ( A B : U)
  ( is-trunc-A : is-trunc (succ-𝕋 (succ-𝕋 k)) A)
  ( is-trunc-B : is-trunc (succ-𝕋 (succ-𝕋 k)) B)
  : is-trunc (succ-𝕋 (succ-𝕋 k)) (coproduct A B)
  :=
  \ x y →
  is-trunc-equiv-is-trunc
  ( succ-𝕋 k)
  ( x = y)
  ( Eq-coproduct A B x y)
  ( extensionality-coproduct A B x y)
  ( match x
      ( inl a ⇒
        match y
          ( inl a' ⇒ is-trunc-A a a'
          | inr b' ⇒ is-trunc-succ-Empty k)
      | inr b ⇒
        match y
          ( inl a' ⇒ is-trunc-succ-Empty k
          | inr b' ⇒ is-trunc-B b b')))
```
