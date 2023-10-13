# 4a. Right orthogonal fibrations

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Prerequisites

Some of the definitions in this file rely on extension extensionality:

```rzk
#assume naiveextext : NaiveExtExt
#assume extext : ExtExt
```

## Right orthogonal maps with respect to shapes

For every shape inclusion `ϕ ⊂ ψ`, we obtain a fibrancy condition for a map
`α : A' → A` in terms of unique extension along `ϕ ⊂ ψ`. This is a relative
version of unique extension along `ϕ ⊂ ψ`.

We say that `α : A' → A` is _right orthogonal_ to the shape inclusion `ϕ ⊂ ψ`,
if the square

```
(ψ → A') → (ψ → A)

   ↓          ↓

(ϕ → A') → (ϕ → A)
```

is homotopy cartesian.

Equivalently, we can interpret this orthogonality as a cofibrancy condition on
the shape inclusion. We say that the shape inclusion `ϕ ⊂ ψ` is _left
orthogonal_ to the map `α`, if `α : A' → A` is right orthogonal to `ϕ ⊂ ψ`.

```rzk title="BW23, Section 3"
#def is-right-orthogonal-to-shape
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( A' A : U)
  ( α : A' → A)
  : U
  :=
    is-homotopy-cartesian
      ( ϕ → A' ) ( \ σ' → (t : ψ) → A' [ϕ t ↦ σ' t])
      ( ϕ → A ) ( \ σ → (t : ψ) → A [ϕ t ↦ σ t])
      ( \ σ' t → α (σ' t)) ( \ _ τ' x → α (τ' x) )
```

## Contractible relative extension types

Using `ExtExt`, we can characterize right orthogonal maps in terms of the
contractibility of relative extension types or, equivalently, generalized
extension types.

```rzk
#section has-contr-relative-extension-types-iff-is-right-orthogonal

#variable I : CUBE
#variable ψ : I → TOPE
#variable ϕ : ψ → TOPE
#variables A' A : U
#variable α : A' → A

#def is-right-orthogonal-to-shape-has-contr-relative-extension-types uses (extext)
  ( are-contr-relext-α
    : has-contr-relative-extension-types I ψ ϕ
      ( \ _ → A') (\ _ → A) (\ _ → α))
  : is-right-orthogonal-to-shape I ψ ϕ A' A α
  :=
    \ σ' →
    is-equiv-is-contr-map
    ( (t : ψ) → A' [ϕ t ↦ σ' t])
    ( (t : ψ) → A [ϕ t ↦ α (σ' t)])
    ( \ τ' t → α (τ' t))
    ( \ τ →
      is-contr-equiv-is-contr'
      ( fib
        ( (t : ψ) → A' [ϕ t ↦ σ' t])
        ( (t : ψ) → A [ϕ t ↦ α (σ' t)])
        ( \ τ' t → α (τ' t))
        ( τ))
      ( relative-extension-type I ψ ϕ
        ( \ _ → A') (\ _ → A) (\ _ → α) σ' τ)
      ( equiv-relative-extension-type-fib extext I ψ ϕ
        ( \ _ → A') (\ _ → A) (\ _ → α) σ' τ)
      ( are-contr-relext-α σ' τ))

#def has-contr-relative-extension-types-is-right-orthogonal-to-shape uses (extext)
  ( is-orth-α : is-right-orthogonal-to-shape I ψ ϕ A' A α)
  : has-contr-relative-extension-types I ψ ϕ (\ _ → A') (\ _ → A) (\ _ → α)
  :=
    \ σ' τ →
      is-contr-equiv-is-contr
      ( fib
        ( (t : ψ) → A' [ϕ t ↦ σ' t])
        ( (t : ψ) → A [ϕ t ↦ α (σ' t)])
        ( \ τ' t → α (τ' t))
        ( τ))
      ( relative-extension-type I ψ ϕ
        ( \ _ → A') (\ _ → A) (\ _ → α) σ' τ)
      ( equiv-relative-extension-type-fib extext I ψ ϕ
        ( \ _ → A') (\ _ → A) (\ _ → α) σ' τ)
      ( is-contr-map-is-equiv
        ( (t : ψ) → A' [ϕ t ↦ σ' t])
        ( (t : ψ) → A [ϕ t ↦ α (σ' t)])
        ( \ τ' t → α (τ' t))
        ( is-orth-α σ')
        ( τ))

#def has-contr-general-relative-extension-types-is-right-orthogonal-to-shape
  uses (extext)
  ( is-orth-α : is-right-orthogonal-to-shape I ψ ϕ A' A α)
  : has-contr-general-relative-extension-types I ψ ϕ
      ( \ _ → A') (\ _ → A) (\ _ → α)
  :=
    has-contr-relative-extension-types-generalize extext I ψ ϕ
      ( \ _ → A') (\ _ → A) (\ _ → α)
    ( has-contr-relative-extension-types-is-right-orthogonal-to-shape is-orth-α)

#end has-contr-relative-extension-types-iff-is-right-orthogonal
```

## Stability properties of left orthogonal shape inclusions

We fix a map `α : A' → A`.

```rzk
#section left-orthogonal-calculus-1

#variables A' A : U
#variable α : A' → A
```

Consider nested shapes `ϕ ⊂ χ ⊂ ψ` and the three possible right orthogonality
conditions.

```rzk
#variable I : CUBE
#variable ψ : I → TOPE
#variable χ : ψ → TOPE
#variable ϕ : χ → TOPE
#variable is-orth-ψ-χ : is-right-orthogonal-to-shape I ψ χ A' A α
#variable is-orth-χ-ϕ : is-right-orthogonal-to-shape
                          I ( \ t → χ t) ( \ t → ϕ t) A' A α
#variable is-orth-ψ-ϕ : is-right-orthogonal-to-shape I ψ ( \ t → ϕ t) A' A α
```

Using the vertical pasting calculus for homotopy cartesian squares, it is not
hard to deduce the corresponding composition and cancellation properties for
left orthogonality of shape inclusion with respect to `α : A' → A`.

### Σ over an intermediate shape

The only fact that stops some of these laws from being a direct corollary is
that the `Σ`-types appearing in the vertical pasting of the relevant squares
(such as `Σ (\ σ : ϕ → A), ( (t : χ) → A [ϕ t ↦ σ t])`) are not literally equal
to the corresponding extension types (such as `τ → A `). Therefore we have to
occasionally go back or forth along the functorial equivalence
`cofibration-composition-functorial`.

```rzk
#def is-homotopy-cartesian-Σ-is-right-orthogonal-to-shape uses (is-orth-ψ-ϕ)
  : is-homotopy-cartesian
    ( ϕ → A')
    ( \ σ' → Σ ( τ' : (t : χ) → A' [ϕ t ↦ σ' t]), ( t : ψ) → A' [χ t ↦ τ' t])
    ( ϕ → A)
    ( \ σ → Σ ( τ : (t : χ) → A [ϕ t ↦ σ t]), ( t : ψ) → A [χ t ↦ τ t])
    ( \ σ' t → α (σ' t))
    ( \ _ (τ', υ') → ( \ t → α (τ' t), \ t → α (υ' t) ))
  :=
    ( \ (σ' : ϕ → A') →
    is-equiv-Equiv-is-equiv'
      ( ( t : ψ) → A' [ϕ t ↦ σ' t])
      ( ( t : ψ) → A [ϕ t ↦ α (σ' t)])
      ( \ υ' t → α ( υ' t))
      ( Σ ( τ' : (t : χ) → A' [ϕ t ↦ σ' t])
        , ( ( t : ψ) → A' [χ t ↦ τ' t]))
      ( Σ ( τ : ( t : χ) → A [ϕ t ↦ α (σ' t)])
        , ( ( t : ψ) → A [χ t ↦ τ t]))
      ( \ (τ', υ') → ( \ t → α (τ' t), \t → α (υ' t)))
      ( cofibration-composition-functorial I ψ χ ϕ
        ( \ _ → A') ( \ _ → A) ( \ _ → α) σ')
      ( is-orth-ψ-ϕ σ'))
```

### Stability under composition

Left orthogonal shape inclusions are preserved under composition.

```rzk title="right-orthogonality for composition of shape inclusions"

#def is-right-orthogonal-to-shape-comp uses (is-orth-ψ-χ is-orth-χ-ϕ)
  : is-right-orthogonal-to-shape I ψ ( \ t → ϕ t) A' A α
  :=
    \ σ' →
      is-equiv-Equiv-is-equiv
        ( ( t : ψ) → A' [ϕ t ↦ σ' t])
        ( ( t : ψ) → A [ϕ t ↦ α (σ' t)])
        ( \ υ' t → α ( υ' t))
        ( Σ ( τ' : (t : χ) → A' [ϕ t ↦ σ' t])
          , ( ( t : ψ) → A' [χ t ↦ τ' t]))
        ( Σ ( τ : ( t : χ) → A [ϕ t ↦ α (σ' t)])
          , ( ( t : ψ) → A [χ t ↦ τ t]))
        ( \ (τ', υ') → ( \ t → α (τ' t), \t → α (υ' t)))
        ( cofibration-composition-functorial I ψ χ ϕ
          ( \ _ → A') ( \ _ → A) ( \ _ → α) σ')
        ( is-homotopy-cartesian-vertical-pasting-from-fibers
          ( ϕ → A' )
          ( \ σ' → (t : χ) → A' [ϕ t ↦ σ' t])
          ( \ _ τ' → (t : ψ) → A' [χ t ↦ τ' t])
          ( ϕ → A )
          ( \ σ → (t : χ) → A [ϕ t ↦ σ t])
          ( \ _ τ → (t : ψ) → A [χ t ↦ τ t])
          ( \ σ' t → α (σ' t))
          ( \ _ τ' x → α (τ' x) )
          ( \ _ _ υ' x → α (υ' x) )
          is-orth-χ-ϕ
          ( \ _ τ' → is-orth-ψ-χ τ')
          σ')
```

### Cancellation laws

If `ϕ ⊂ χ` and `ϕ ⊂ ψ` are left orthogonal to `α : A' → A`, then so is `χ ⊂ ψ`.

```rzk
#def is-right-orthogonal-to-shape-left-cancel uses (is-orth-χ-ϕ is-orth-ψ-ϕ)
  : is-right-orthogonal-to-shape I ψ χ A' A α
  :=
    \ τ' →
        is-homotopy-cartesian-lower-cancel-to-fibers
          ( ϕ → A' )
          ( \ σ' → (t : χ) → A' [ϕ t ↦ σ' t])
          ( \ _ τ' → (t : ψ) → A' [χ t ↦ τ' t])
          ( ϕ → A )
          ( \ σ → (t : χ) → A [ϕ t ↦ σ t])
          ( \ _ τ → (t : ψ) → A [χ t ↦ τ t])
          ( \ σ' t → α (σ' t))
          ( \ _ τ' x → α (τ' x) )
          ( \ _ _ υ' x → α (υ' x) )
          ( is-orth-χ-ϕ )
          (is-homotopy-cartesian-Σ-is-right-orthogonal-to-shape)
          ( \ ( t : ϕ) → τ' t)
          ( τ')
```

If `ϕ ⊂ ψ` is left orthogonal to `α : A' → A` and `χ ⊂ ψ` is a (functorial)
shape retract, then `ϕ ⊂ ψ` is left orthogonal to `α : A' → A`.

```rzk
#def is-right-orthogonal-to-shape-right-cancel-retract uses (is-orth-ψ-ϕ)
  ( is-fretract-ψ-χ : is-functorial-shape-retract I ψ χ)
  : is-right-orthogonal-to-shape I ( \ t → χ t) ( \ t → ϕ t) A' A α
  :=
    is-homotopy-cartesian-upper-cancel-with-section
      ( ϕ → A' )
      ( \ σ' → (t : χ) → A' [ϕ t ↦ σ' t])
      ( \ _ τ' → (t : ψ) → A' [χ t ↦ τ' t])
      ( ϕ → A )
      ( \ σ → (t : χ) → A [ϕ t ↦ σ t])
      ( \ _ τ → (t : ψ) → A [χ t ↦ τ t])
      ( \ σ' t → α (σ' t))
      ( \ _ τ' x → α (τ' x) )
      ( \ _ _ υ' x → α (υ' x) )
      ( relativize-is-functorial-shape-retract I ψ χ is-fretract-ψ-χ ϕ A' A α)
      ( is-homotopy-cartesian-Σ-is-right-orthogonal-to-shape)

#end left-orthogonal-calculus-1
```

### Stability under exponentiation

If `ϕ ⊂ ψ` is left orthogonal to `α : A' → A` then so is `χ × ϕ ⊂ χ × ψ` for
every other shape `χ`.

The following proof uses a lot of currying and uncurrying and relies on (the
naive form of) extension extensionality.

```rzk
#def is-right-orthogonal-to-shape-× uses (naiveextext)
-- this should be refactored by introducing cofibration-product-functorial
  ( A' A : U)
  ( α : A' → A)
  ( J : CUBE)
  ( χ : J → TOPE)
  ( I : CUBE)
  ( ψ : I → TOPE )
  ( ϕ : ψ → TOPE )
  ( is-orth-ψ-ϕ : is-right-orthogonal-to-shape I ψ ϕ A' A α)
  : is-right-orthogonal-to-shape
      ( J × I) ( \ (t,s) → χ t ∧ ψ s) ( \ (t,s) → χ t ∧ ϕ s) A' A α
  :=
    \ ( σ' : ( (t,s) : J × I | χ t ∧ ϕ s) → A') →
      ( ( \ ( τ : ( (t,s) : J × I | χ t ∧ ψ s) → A[ϕ s ↦ α (σ' (t,s))])
            ( t, s) →
          ( first (first (is-orth-ψ-ϕ (\ s' → σ' (t, s'))))) ( \ s' → τ (t, s')) s
        , \ ( τ' : ( (t,s) : J × I | χ t ∧ ψ s) → A' [ϕ s ↦ σ' (t,s)]) →
            naiveextext
              ( J × I) ( \ (t,s) → χ t ∧ ψ s) ( \ (t,s) → χ t ∧ ϕ s)
              ( \ _ → A')
              ( \ ( t,s) → σ' (t,s))
              ( \ ( t,s) →
                ( first (first (is-orth-ψ-ϕ (\ s' → σ' (t, s')))))
                  ( \ s' → α (τ' (t, s'))) s)
              ( τ')
              ( \ ( t,s) →
                ext-htpy-eq I ψ ϕ (\ _ → A') ( \ s' → σ' (t, s'))
                  ( ( first (first (is-orth-ψ-ϕ (\ s' → σ' (t, s')))))
                    ( \ s' → α (τ' (t, s'))))
                  ( \ s' → τ' (t, s') )
                  ( ( second (first (is-orth-ψ-ϕ (\ s' → σ' (t, s')))))
                    ( \ s' → τ' (t, s')))
                  ( s)))
      , ( \ ( τ : ( (t,s) : J × I | χ t ∧ ψ s) → A [ϕ s ↦ α (σ' (t,s))])
            ( t, s) →
          ( first (second (is-orth-ψ-ϕ (\ s' → σ' (t, s'))))) ( \ s' → τ (t, s')) s
        , \ ( τ : ( (t,s) : J × I | χ t ∧ ψ s) → A [ϕ s ↦ α (σ' (t,s))]) →
            naiveextext
              ( J × I) ( \ (t,s) → χ t ∧ ψ s) ( \ (t,s) → χ t ∧ ϕ s)
              ( \ _ → A)
              ( \ (t,s) → α (σ' (t,s)))
              ( \ (t,s) →
                α ( ( first ( second ( is-orth-ψ-ϕ (\ s' → σ' (t, s')))))
                      ( \ s' → τ (t, s')) s))
              ( τ)
              ( \ ( t,s) →
                ext-htpy-eq I ψ ϕ (\ _ → A) ( \ s' → α (σ' (t, s')))
                  ( \ s'' →
                      α ( ( first (second (is-orth-ψ-ϕ (\ s' → σ' (t, s')))))
                          ( \ s' → τ (t, s'))
                          ( s'')))
                  ( \ s' → τ (t, s') )
                  ( ( second ( second (is-orth-ψ-ϕ (\ s' → σ' (t, s')))))
                    ( \ s' → τ (t, s')))
                  ( s))))
```

### Stability under exact pushouts

For any two shapes `ϕ, ψ ⊂ I`, if `ϕ ∩ ψ ⊂ ϕ` is left orthogonal to
`α : A' → A`, then so is `ψ ⊂ ϕ ∪ ψ`.

```rzk
#def is-right-orthogonal-to-shape-pushout
  ( A' A : U)
  ( α : A' → A)
  ( I : CUBE)
  ( ϕ ψ : I → TOPE)
  ( is-orth-ϕ-ψ∧ϕ : is-right-orthogonal-to-shape I ϕ ( \ t → ϕ t ∧ ψ t) A' A α)
  : is-right-orthogonal-to-shape I ( \ t → ϕ t ∨ ψ t) ( \ t → ψ t) A' A α
  := \ ( τ' : ψ → A') →
       is-equiv-Equiv-is-equiv
         ( (t : I | ϕ t ∨ ψ t) → A' [ψ t ↦ τ' t])
         ( (t : I | ϕ t ∨ ψ t) → A [ψ t ↦ α (τ' t)])
         ( \ υ' t → α (υ' t))
         ( (t : ϕ) → A' [ϕ t ∧ ψ t ↦ τ' t])
         ( (t : ϕ) → A [ϕ t ∧ ψ t ↦ α (τ' t)])
         ( \ ν' t → α (ν' t))
         ( cofibration-union-functorial I ϕ ψ (\ _ → A') (\ _ → A) (\ _ → α) τ')
         ( is-orth-ϕ-ψ∧ϕ ( \ t → τ' t))
```

## Stability properties of right orthogonal maps

Now we change perspective. We fix a shape inclusion `ϕ ⊂ ψ` and investigate
stability properties of maps right orthogonal to it.

```rzk
#section right-orthogonal-calculus
#variable I : CUBE
#variable ψ : I → TOPE
#variable ϕ : ψ → TOPE
```

### Stability under composition

```rzk
#variables A'' A' A : U
#variable α' : A'' → A'
#variable α : A' → A

#variable is-orth-ψ-ϕ-α' : is-right-orthogonal-to-shape I ψ ϕ A'' A' α'
#variable is-orth-ψ-ϕ-α : is-right-orthogonal-to-shape I ψ ϕ A' A α
#variable is-orth-ψ-ϕ-αα' : is-right-orthogonal-to-shape I ψ ϕ A'' A
                            ( comp A'' A' A α α')

#def is-right-orthogonal-comp-to-shape
  uses (is-orth-ψ-ϕ-α' is-orth-ψ-ϕ-α)
  : is-right-orthogonal-to-shape I ψ ϕ A'' A (comp A'' A' A α α')
  :=
    \ σ'' →
      is-equiv-comp
      ( extension-type I ψ ϕ (\ _ → A'') σ'')
      ( extension-type I ψ ϕ (\ _ → A') (\ t → α' (σ'' t)))
      ( extension-type I ψ ϕ (\ _ → A) (\ t → α (α' (σ'' t))))
      ( \ τ'' t → α' (τ'' t))
      ( is-orth-ψ-ϕ-α' σ'')
      ( \ τ' t → α (τ' t))
      ( is-orth-ψ-ϕ-α (\ t → α' (σ'' t)))
```

### Right cancellation

```rzk
#def is-right-orthogonal-right-cancel-to-shape
  uses (is-orth-ψ-ϕ-α is-orth-ψ-ϕ-αα')
  : is-right-orthogonal-to-shape I ψ ϕ A'' A' α'
  :=
    \ σ'' →
    is-equiv-right-factor
      ( extension-type I ψ ϕ (\ _ → A'') σ'')
      ( extension-type I ψ ϕ (\ _ → A') (\ t → α' (σ'' t)))
      ( extension-type I ψ ϕ (\ _ → A) (\ t → α (α' (σ'' t))))
      ( \ τ'' t → α' (τ'' t))
      ( \ τ' t → α (τ' t))
      ( is-orth-ψ-ϕ-α (\ t → α' (σ'' t)))
      ( is-orth-ψ-ϕ-αα' σ'')
```

### Stability under pullback

Right orthogonal maps are stable under pullback. More precisely: If `α : A' → A`
is right orthogonal, then so is the second projection
`relative-product A A' α B f → B` for every `f : B → A`.

To prove this, we first show that each relative extension type of
`relative-product A A' α B f → B`, is a retract of a generalized extension type
for `A' → A`. Since the latter are all contractible by assumption, the same
follows for the former.

```rzk
#variable B : U
#variable f : B → A

#def relative-extension-type-pullback-general-relative-extension-type
  ( σB' : ϕ → relative-product A A' α B f)
  ( τB : (t : ψ) → B [ϕ t ↦ second-relative-product A A' α B f (σB' t)])
  ( (τA', hA)
    : general-relative-extension-type I ψ ϕ (\ _ → A') (\ _ → A) (\ _ → α)
      ( \ t → first-relative-product A A' α B f (σB' t))
      ( \ t → f (τB t))
      ( \ t → homotopy-relative-product A A' α B f (σB' t)))
  : relative-extension-type I ψ ϕ
    ( \ _ → relative-product A A' α B f) ( \ _ → B)
    ( \ _ → second-relative-product A A' α B f)
    ( σB') ( τB)
  :=
    ( \ t → ( (τA' t, τB t) , hA t)
    , \ t → refl)

#def general-relative-extension-type-relative-extension-type-pullback
  ( σB' : ϕ → relative-product A A' α B f)
  ( τB : (t : ψ) → B [ϕ t ↦ second-relative-product A A' α B f (σB' t)])
  ( (τB', hB)
    : relative-extension-type I ψ ϕ
      ( \ _ → relative-product A A' α B f) ( \ _ → B)
      ( \ _ → second-relative-product A A' α B f)
      ( σB') ( τB))
  : general-relative-extension-type I ψ ϕ (\ _ → A') (\ _ → A) (\ _ → α)
    ( \ t → first-relative-product A A' α B f (σB' t))
    ( \ t → f (τB t))
    ( \ t → homotopy-relative-product A A' α B f (σB' t))
  :=
    ( \ t → first-relative-product A A' α B f (τB' t)
    , \ t →
      concat A
      ( α (first-relative-product A A' α B f (τB' t)))
      ( f (second-relative-product A A' α B f (τB' t)))
      ( f (τB t))
      ( homotopy-relative-product A A' α B f (τB' t))
      ( ap B A
        ( second-relative-product A A' α B f (τB' t))
        ( τB t)
        ( f) ( hB t)))

#def is-id-rel-ext-type-pb-gen-rel-ext-type-rel-ext-type-pb uses (extext)
  ( σB' : ϕ → relative-product A A' α B f)
  ( τB : (t : ψ) → B [ϕ t ↦ second-relative-product A A' α B f (σB' t)])
  : ( τhB
      : relative-extension-type I ψ ϕ
        ( \ _ → relative-product A A' α B f) ( \ _ → B)
        ( \ _ → second-relative-product A A' α B f)
        ( σB') ( τB))
  → ( relative-extension-type-pullback-general-relative-extension-type σB' τB
      ( general-relative-extension-type-relative-extension-type-pullback σB' τB τhB)
    = τhB)
  :=
    ind-has-section-equiv
    ( relative-extension-type' I ψ ϕ
      ( \ _ → relative-product A A' α B f) ( \ _ → B)
      ( \ _ → second-relative-product A A' α B f)
      ( σB') ( τB))
    ( relative-extension-type I ψ ϕ
      ( \ _ → relative-product A A' α B f) ( \ _ → B)
      ( \ _ → second-relative-product A A' α B f)
      ( σB') ( τB))
    ( equiv-relative-extension-type-fib extext I ψ ϕ
      ( \ _ → relative-product A A' α B f) ( \ _ → B)
      ( \ _ → second-relative-product A A' α B f)
      ( σB') ( τB))
    ( \ τhB →
      ( relative-extension-type-pullback-general-relative-extension-type σB' τB
        ( general-relative-extension-type-relative-extension-type-pullback σB' τB τhB)
      = τhB))
    ( ind-fib
      ( (t : ψ) → relative-product A A' α B f [ϕ t ↦ σB' t])
      ( (t : ψ) → B [ϕ t ↦ second-relative-product A A' α B f (σB' t)])
      ( \ τB' t → second-relative-product A A' α B f (τB' t))
      ( \ τB₁ (τB'₁, h₁) →
        ( relative-extension-type-pullback-general-relative-extension-type σB' τB₁
          ( general-relative-extension-type-relative-extension-type-pullback σB' τB₁
            ( τB'₁
            , ext-htpy-eq I ψ ϕ (\ _ → B)
              ( \ t → second-relative-product A A' α B f (σB' t))
              ( \ t → second-relative-product A A' α B f (τB'₁ t))
              ( τB₁) ( h₁)))
        = ( τB'₁
          , ext-htpy-eq I ψ ϕ (\ _ → B)
            ( \ t → second-relative-product A A' α B f (σB' t))
            ( \ t → second-relative-product A A' α B f (τB'₁ t))
            ( τB₁) ( h₁))))
      ( \ τB' → refl)
      ( τB))

#def is-retract-of-rel-ext-type-pb-gen-rel-ext-type uses (extext)
  ( σB' : ϕ → relative-product A A' α B f)
  ( τB : (t : ψ) → B [ϕ t ↦ second-relative-product A A' α B f (σB' t)])
  : is-retract-of
    ( relative-extension-type I ψ ϕ
      ( \ _ → relative-product A A' α B f) ( \ _ → B)
      ( \ _ → second-relative-product A A' α B f)
      ( σB') ( τB))
    ( general-relative-extension-type I ψ ϕ (\ _ → A') (\ _ → A) (\ _ → α)
      ( \ t → first-relative-product A A' α B f (σB' t))
      ( \ t → f (τB t))
      ( \ t → homotopy-relative-product A A' α B f (σB' t)))
  :=
    ( general-relative-extension-type-relative-extension-type-pullback σB' τB
    , ( relative-extension-type-pullback-general-relative-extension-type σB' τB
      , is-id-rel-ext-type-pb-gen-rel-ext-type-rel-ext-type-pb σB' τB))
```

Then we can deduce that right orthogonal maps are preserved under pullback:

```rzk
#def is-right-orthoponal-pullback-to-shape uses (extext is-orth-ψ-ϕ-α)
  : is-right-orthogonal-to-shape I ψ ϕ
    ( relative-product A A' α B f) ( B)
    ( second-relative-product A A' α B f)
  :=
    is-right-orthogonal-to-shape-has-contr-relative-extension-types I ψ ϕ
    ( relative-product A A' α B f) ( B)
    ( second-relative-product A A' α B f)
    ( \ σB' τB →
      is-contr-is-retract-of-is-contr
      ( relative-extension-type I ψ ϕ
        ( \ _ → relative-product A A' α B f) ( \ _ → B)
        ( \ _ → second-relative-product A A' α B f)
        ( σB') ( τB))
      ( general-relative-extension-type I ψ ϕ (\ _ → A') (\ _ → A) (\ _ → α)
        ( \ t → first-relative-product A A' α B f (σB' t))
        ( \ t → f (τB t))
        ( \ t → homotopy-relative-product A A' α B f (σB' t)))
      ( is-retract-of-rel-ext-type-pb-gen-rel-ext-type σB' τB)
      ( has-contr-general-relative-extension-types-is-right-orthogonal-to-shape
        I ψ ϕ A' A α
        ( is-orth-ψ-ϕ-α)
        ( \ t → first-relative-product A A' α B f (σB' t))
        ( \ t → f (τB t))
        ( \ t → homotopy-relative-product A A' α B f (σB' t))))

#end right-orthogonal-calculus
```

## Types with unique extension

We say that an type `A` has unique extensions for a shape inclusion `ϕ ⊂ ψ`, if
for each `σ : ϕ → A` the type of `ψ`-extensions is contractible.

```rzk
#def has-unique-extensions
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( A : U)
  : U
  := ( σ : ϕ → A) → is-contr ( (t : ψ) → A [ϕ t ↦ σ t])
```

The property of having unique extension can be pulled back along any right
orthogonal map.

```rzk
#def has-unique-extensions-domain-right-orthogonal-has-unique-extensions-codomain
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( A' A : U)
  ( α : A' → A)
  ( is-orth-ψ-ϕ-α : is-right-orthogonal-to-shape I ψ ϕ A' A α)
  : has-unique-extensions I ψ ϕ A → has-unique-extensions I ψ ϕ A'
  :=
    \ has-ue-A ( σ' : ϕ → A') →
      is-contr-equiv-is-contr'
        ( ( t : ψ) → A' [ϕ t ↦ σ' t])
        ( ( t : ψ) → A [ϕ t ↦ α (σ' t)])
        ( \ τ' t → α (τ' t) , is-orth-ψ-ϕ-α σ')
        ( has-ue-A (\ t → α (σ' t)))
```

Alternatively, we can ask that the canonical restriction map `(ψ → A) → (ϕ → A)`
is an equivalence.

```rzk
#section is-local-type
#variable I : CUBE
#variable ψ : I → TOPE
#variable ϕ : ψ → TOPE
#variable A : U

#def is-local-type
  : U
  :=
    is-equiv (ψ → A) (ϕ → A) ( \ τ t → τ t)
```

This follows straightforwardly from the fact that for every `σ : ϕ → A` we have
an equivalence between the extension type `(t : ψ) → A [ϕ t ↦ σ t]` and the
fiber of the restriction map `(ψ → A) → (ϕ → A)`.

```rzk
#def is-local-type-has-unique-extensions
  ( has-ue-ψ-ϕ-A : has-unique-extensions I ψ ϕ A)
  : is-local-type
  :=
    is-equiv-is-contr-map (ψ → A) (ϕ → A) ( \ τ t → τ t)
      ( \ ( σ : ϕ → A) →
        is-contr-equiv-is-contr
          ( extension-type I ψ ϕ ( \ t → A) σ)
          ( homotopy-extension-type I ψ ϕ ( \ t → A) σ)
          ( extension-type-weakening I ψ ϕ ( \ t → A) σ)
          ( has-ue-ψ-ϕ-A σ))

#def has-unique-extensions-is-local-type
  ( is-lt-ψ-ϕ-A : is-local-type)
  : has-unique-extensions I ψ ϕ A
  :=
    \ σ →
      is-contr-equiv-is-contr'
        ( extension-type I ψ ϕ ( \ t → A) σ)
        ( homotopy-extension-type I ψ ϕ ( \ t → A) σ)
        ( extension-type-weakening I ψ ϕ ( \ t → A) σ)
        ( is-contr-map-is-equiv
            ( ψ → A) (ϕ → A) ( \ τ t → τ t)
            ( is-lt-ψ-ϕ-A)
            ( σ))

#end is-local-type
```

Since the property of having unique extensions passes from the codomain to the
domain of a right orthogonal map, the same is true for locality of types.

```rzk
#def is-local-type-domain-right-orthogonal-is-local-type-codomain
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( A' A : U)
  ( α : A' → A)
  ( is-orth-α : is-right-orthogonal-to-shape I ψ ϕ A' A α)
  ( is-local-A : is-local-type I ψ ϕ A)
  : is-local-type I ψ ϕ A'
  :=
    is-local-type-has-unique-extensions I ψ ϕ A'
      ( has-unique-extensions-domain-right-orthogonal-has-unique-extensions-codomain
          I ψ ϕ A' A α is-orth-α
          ( has-unique-extensions-is-local-type I ψ ϕ A is-local-A))

```
