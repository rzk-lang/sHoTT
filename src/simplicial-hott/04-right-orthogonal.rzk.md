# 4a. Right orthogonal fibrations

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Prerequisites

Some of the definitions in this file rely on extension extensionality or
function extensionality:

```rzk
#assume extext : ExtExt
#assume funext : FunExt
```

## Right orthogonal maps with respect to shapes

For every shape inclusion `ϕ ⊂ ψ`, we obtain a fibrancy condition for a map
`α : A' → A` in terms of unique extension along `ϕ ⊂ ψ`. This is a relative
version of unique extension along `ϕ ⊂ ψ`.

We say that `α : A' → A` is **right orthogonal** to the shape inclusion `ϕ ⊂ ψ`,
if the square

```
(ψ → A') → (ψ → A)

   ↓          ↓

(ϕ → A') → (ϕ → A)
```

is homotopy cartesian.

Equivalently, we can interpret this orthogonality as a cofibrancy condition on
the shape inclusion. We say that the shape inclusion `ϕ ⊂ ψ` is **left
orthogonal** to the map `α`, if `α : A' → A` is right orthogonal to `ϕ ⊂ ψ`.

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
      ( ϕ → A') (\ σ' → (t : ψ) → A' [ϕ t ↦ σ' t])
      ( ϕ → A) (\ σ → (t : ψ) → A [ϕ t ↦ σ t])
      ( \ σ' t → α (σ' t)) (\ _ τ' x → α (τ' x))
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
    ( ( t : ψ) → A' [ϕ t ↦ σ' t])
    ( ( t : ψ) → A [ϕ t ↦ α (σ' t)])
    ( \ τ' t → α (τ' t))
    ( \ τ →
      is-contr-equiv-is-contr'
      ( fib
        ( ( t : ψ) → A' [ϕ t ↦ σ' t])
        ( ( t : ψ) → A [ϕ t ↦ α (σ' t)])
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
        ( ( t : ψ) → A' [ϕ t ↦ σ' t])
        ( ( t : ψ) → A [ϕ t ↦ α (σ' t)])
        ( \ τ' t → α (τ' t))
        ( τ))
      ( relative-extension-type I ψ ϕ
        ( \ _ → A') (\ _ → A) (\ _ → α) σ' τ)
      ( equiv-relative-extension-type-fib extext I ψ ϕ
        ( \ _ → A') (\ _ → A) (\ _ → α) σ' τ)
      ( is-contr-map-is-equiv
        ( ( t : ψ) → A' [ϕ t ↦ σ' t])
        ( ( t : ψ) → A [ϕ t ↦ α (σ' t)])
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
                          I (\ t → χ t) (\ t → ϕ t) A' A α
#variable is-orth-ψ-ϕ : is-right-orthogonal-to-shape I ψ (\ t → ϕ t) A' A α
```

Using the vertical pasting calculus for homotopy cartesian squares, it is not
hard to deduce the corresponding composition and cancellation properties for
left orthogonality of shape inclusion with respect to `α : A' → A`.

### Σ over an intermediate shape

The only fact that stops some of these laws from being a direct corollary is
that the `Σ`-types appearing in the vertical pasting of the relevant squares
(such as `Σ (\ σ : ϕ → A), ( (t : χ) → A [ϕ t ↦ σ t])`) are not literally equal
to the corresponding extension types (such as `χ → A `). Therefore we have to
occasionally go back or forth along the functorial equivalence
`cofibration-composition-functorial`.

```rzk
#def is-homotopy-cartesian-Σ-is-right-orthogonal-to-shape uses (is-orth-ψ-ϕ)
  : is-homotopy-cartesian
    ( ϕ → A')
    ( \ σ' →
      Σ ( τ' : (t : χ) → A' [ϕ t ↦ σ' t])
      , ( t : ψ) → A' [χ t ↦ τ' t])
    ( ϕ → A)
    ( \ σ →
      Σ ( τ : (t : χ) → A [ϕ t ↦ σ t])
      , ( t : ψ) → A [χ t ↦ τ t])
    ( \ σ' t → α (σ' t))
    ( \ _ (τ' , υ') → (\ t → α (τ' t) , \ t → α (υ' t)))
  :=
    ( \ (σ' : ϕ → A')
  → is-equiv-Equiv-is-equiv'
      ( ( t : ψ) → A' [ϕ t ↦ σ' t])
      ( ( t : ψ) → A [ϕ t ↦ α (σ' t)])
      ( \ υ' t → α (υ' t))
      ( Σ ( τ' : (t : χ) → A' [ϕ t ↦ σ' t])
        , ( ( t : ψ) → A' [χ t ↦ τ' t]))
      ( Σ ( τ : (t : χ) → A [ϕ t ↦ α (σ' t)])
        , ( ( t : ψ) → A [χ t ↦ τ t]))
      ( \ (τ' , υ') → (\ t → α (τ' t) , \ t → α (υ' t)))
      ( cofibration-composition-functorial I ψ χ ϕ
        ( \ _ → A') (\ _ → A) (\ _ → α) σ')
      ( is-orth-ψ-ϕ σ'))
```

### Composition

Left orthogonal shape inclusions are preserved under composition.

```rzk title="right-orthogonality for composition of shape inclusions"

#def is-right-orthogonal-to-shape-comp uses (is-orth-ψ-χ is-orth-χ-ϕ)
  : is-right-orthogonal-to-shape I ψ (\ t → ϕ t) A' A α
  :=
    \ σ' →
      is-equiv-Equiv-is-equiv
        ( ( t : ψ) → A' [ϕ t ↦ σ' t])
        ( ( t : ψ) → A [ϕ t ↦ α (σ' t)])
        ( \ υ' t → α (υ' t))
        ( Σ ( τ' : (t : χ) → A' [ϕ t ↦ σ' t])
          , ( ( t : ψ) → A' [χ t ↦ τ' t]))
        ( Σ ( τ : (t : χ) → A [ϕ t ↦ α (σ' t)])
          , ( ( t : ψ) → A [χ t ↦ τ t]))
        ( \ (τ' , υ') → (\ t → α (τ' t) , \ t → α (υ' t)))
        ( cofibration-composition-functorial I ψ χ ϕ
          ( \ _ → A') (\ _ → A) (\ _ → α) σ')
        ( is-homotopy-cartesian-vertical-pasting-from-fibers
          ( ϕ → A')
          ( \ σ' → (t : χ) → A' [ϕ t ↦ σ' t])
          ( \ _ τ' → (t : ψ) → A' [χ t ↦ τ' t])
          ( ϕ → A)
          ( \ σ → (t : χ) → A [ϕ t ↦ σ t])
          ( \ _ τ → (t : ψ) → A [χ t ↦ τ t])
          ( \ σ' t → α (σ' t))
          ( \ _ τ' x → α (τ' x))
          ( \ _ _ υ' x → α (υ' x))
          is-orth-χ-ϕ
          ( \ _ τ' → is-orth-ψ-χ τ')
          σ')
```

### Cancellation

If `ϕ ⊂ χ` and `ϕ ⊂ ψ` are left orthogonal to `α : A' → A`, then so is `χ ⊂ ψ`.

```rzk
#def is-right-orthogonal-to-shape-left-cancel uses (is-orth-χ-ϕ is-orth-ψ-ϕ)
  : is-right-orthogonal-to-shape I ψ χ A' A α
  :=
    \ τ' →
        is-homotopy-cartesian-lower-cancel-to-fibers
          ( ϕ → A')
          ( \ σ' → (t : χ) → A' [ϕ t ↦ σ' t])
          ( \ _ τ' → (t : ψ) → A' [χ t ↦ τ' t])
          ( ϕ → A)
          ( \ σ → (t : χ) → A [ϕ t ↦ σ t])
          ( \ _ τ → (t : ψ) → A [χ t ↦ τ t])
          ( \ σ' t → α (σ' t))
          ( \ _ τ' x → α (τ' x))
          ( \ _ _ υ' x → α (υ' x))
          ( is-orth-χ-ϕ)
          ( is-homotopy-cartesian-Σ-is-right-orthogonal-to-shape)
          ( \ (t : ϕ) → τ' t)
          ( τ')
```

If `ϕ ⊂ ψ` is left orthogonal to `α : A' → A` and `χ ⊂ ψ` is a (functorial)
shape retract, then `ϕ ⊂ ψ` is left orthogonal to `α : A' → A`.

```rzk
#def is-right-orthogonal-to-shape-right-cancel-retract uses (is-orth-ψ-ϕ)
  ( is-fretract-ψ-χ : is-functorial-shape-retract I ψ χ)
  : is-right-orthogonal-to-shape I (\ t → χ t) (\ t → ϕ t) A' A α
  :=
    is-homotopy-cartesian-upper-cancel-with-section
      ( ϕ → A')
      ( \ σ' → (t : χ) → A' [ϕ t ↦ σ' t])
      ( \ _ τ' → (t : ψ) → A' [χ t ↦ τ' t])
      ( ϕ → A)
      ( \ σ → (t : χ) → A [ϕ t ↦ σ t])
      ( \ _ τ → (t : ψ) → A [χ t ↦ τ t])
      ( \ σ' t → α (σ' t))
      ( \ _ τ' x → α (τ' x))
      ( \ _ _ υ' x → α (υ' x))
      ( relativize-is-functorial-shape-retract I ψ χ is-fretract-ψ-χ ϕ A' A α)
      ( is-homotopy-cartesian-Σ-is-right-orthogonal-to-shape)

#end left-orthogonal-calculus-1
```

### Transposition

Inside a product of cube `I × J`, we can interchange the two factors without
affecting left orthogonality.

```rzk
#def is-right-orthogonal-to-shape-transpose
  ( A' A : U)
  ( α : A' → A)
  ( I J : CUBE)
  ( ψ : (I × J) → TOPE)
  ( ϕ : ψ → TOPE)
  ( is-orth-ψ-ϕ : is-right-orthogonal-to-shape (I × J)
    ( \ (s , t) → ψ (s , t))
    ( \ (s , t) → ϕ (s , t))
    ( A') (A) (α))
  : is-right-orthogonal-to-shape (J × I)
    ( \ (t , s) → ψ (s , t))
    ( \ (t , s) → ϕ (s , t))
    ( A') (A) (α)
  :=
    \ σ' →
    is-equiv-Equiv-is-equiv
    ( ( ( t , s) : J × I | ψ (s , t)) → A' [ϕ (s , t) ↦ σ' (t , s)])
    ( ( ( t , s) : J × I | ψ (s , t)) → A [ϕ (s , t) ↦ α (σ' (t , s))])
    ( \ τ' ts → α (τ' ts))
    ( ( ( s , t) : I × J | ψ (s , t)) → A' [ϕ (s , t) ↦ σ' (t , s)])
    ( ( ( s , t) : I × J | ψ (s , t)) → A [ϕ (s , t) ↦ α (σ' (t , s))])
    ( \ τ' st → α (τ' st))
    ( ( ( ( \ v (x , y) → v (y , x))
        , ( \ v (x , y) → v (y , x))
        )
      , ( \ _ → refl)
      )
    , ( ( ( ( \ v (x , y) → v (y , x)) , (\ _ → refl))
        , ( ( \ v (x , y) → v (y , x)) , (\ _ → refl)))
      , ( ( ( \ v (x , y) → v (y , x)) , (\ _ → refl))
        , ( ( \ v (x , y) → v (y , x)) , (\ _ → refl)))))
    ( is-orth-ψ-ϕ (\ (s , t) → σ' (t , s)))
```

### Tensoring

If `ϕ ⊂ ψ` is left orthogonal to `α : A' → A` then so is `χ × ϕ ⊂ χ × ψ` for
every other shape `χ`.

The following proof uses a lot of currying and uncurrying and relies extension
extensionality.

```rzk
#def is-right-orthogonal-to-shape-product uses (extext)
  ( A' A : U)
  ( α : A' → A)
  ( J : CUBE)
  ( χ : J → TOPE)
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( is-orth-ψ-ϕ : is-right-orthogonal-to-shape I ψ ϕ A' A α)
  : is-right-orthogonal-to-shape
      ( J × I) (\ (t , s) → χ t ∧ ψ s) (\ (t , s) → χ t ∧ ϕ s) A' A α
  :=
    \ (σ' : ((t , s) : J × I | χ t ∧ ϕ s) → A')
    → ( ( \ (τ : ((t , s) : J × I | χ t ∧ ψ s) → A[ϕ s ↦ α (σ' (t , s))])
            ( t , s)
        → ( first (first (is-orth-ψ-ϕ (\ s' → σ' (t , s'))))) (\ s' → τ (t , s')) s
        , \ (τ' : ((t , s) : J × I | χ t ∧ ψ s) → A' [ϕ s ↦ σ' (t , s)])
          → naiveextext-extext extext
              ( J × I) (\ (t , s) → χ t ∧ ψ s) (\ (t , s) → χ t ∧ ϕ s)
              ( \ _ → A')
              ( \ (t , s) → σ' (t , s))
              ( \ (t , s) →
                ( first (first (is-orth-ψ-ϕ (\ s' → σ' (t , s')))))
                  ( \ s' → α (τ' (t , s'))) s)
              ( τ')
              ( \ (t , s) →
                ext-htpy-eq I ψ ϕ (\ _ → A') (\ s' → σ' (t , s'))
                  ( ( first (first (is-orth-ψ-ϕ (\ s' → σ' (t , s')))))
                    ( \ s' → α (τ' (t , s'))))
                  ( \ s' → τ' (t , s'))
                  ( ( second (first (is-orth-ψ-ϕ (\ s' → σ' (t , s')))))
                    ( \ s' → τ' (t , s')))
                  ( s)))
      , ( \ (τ : ((t , s) : J × I | χ t ∧ ψ s) → A [ϕ s ↦ α (σ' (t , s))])
            ( t , s)
        → ( first (second (is-orth-ψ-ϕ (\ s' → σ' (t , s'))))) (\ s' → τ (t , s')) s
        , \ (τ : ((t , s) : J × I | χ t ∧ ψ s) → A [ϕ s ↦ α (σ' (t , s))])
          → naiveextext-extext extext
              ( J × I) (\ (t , s) → χ t ∧ ψ s) (\ (t , s) → χ t ∧ ϕ s)
              ( \ _ → A)
              ( \ (t , s) → α (σ' (t , s)))
              ( \ (t , s) →
                α ((first (second (is-orth-ψ-ϕ (\ s' → σ' (t , s')))))
                      ( \ s' → τ (t , s')) s))
              ( τ)
              ( \ (t , s) →
                ext-htpy-eq I ψ ϕ (\ _ → A) (\ s' → α (σ' (t , s')))
                  ( \ s'' →
                      α ((first (second (is-orth-ψ-ϕ (\ s' → σ' (t , s')))))
                          ( \ s' → τ (t , s'))
                          ( s'')))
                  ( \ s' → τ (t , s'))
                  ( ( second (second (is-orth-ψ-ϕ (\ s' → σ' (t , s')))))
                    ( \ s' → τ (t , s')))
                  ( s))))

#def is-right-orthogonal-to-shape-product' uses (extext)
  ( A' A : U)
  ( α : A' → A)
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( J : CUBE)
  ( χ : J → TOPE)
  ( is-orth-ψ-ϕ : is-right-orthogonal-to-shape I ψ ϕ A' A α)
  : is-right-orthogonal-to-shape
      ( I × J) (\ (s , t) → ψ s ∧ χ t) (\ (s , t) → ϕ s ∧ χ t) A' A α
  :=
    is-right-orthogonal-to-shape-transpose A' A α J I
    ( \ (t , s) → χ t ∧ ψ s)
    ( \ (t , s) → χ t ∧ ϕ s)
    ( is-right-orthogonal-to-shape-product A' A α J χ I ψ ϕ is-orth-ψ-ϕ)
```

### Exact pushouts

For any two shapes `ϕ, ψ ⊂ I`, if `ϕ ∩ ψ ⊂ ϕ` is left orthogonal to
`α : A' → A`, then so is `ψ ⊂ ϕ ∪ ψ`.

```rzk
#def is-right-orthogonal-to-shape-pushout
  ( A' A : U)
  ( α : A' → A)
  ( I : CUBE)
  ( ϕ ψ : I → TOPE)
  ( is-orth-ϕ-ψ∧ϕ : is-right-orthogonal-to-shape I ϕ (\ t → ϕ t ∧ ψ t) A' A α)
  : is-right-orthogonal-to-shape I (\ t → ϕ t ∨ ψ t) (\ t → ψ t) A' A α
  := \ (τ' : ψ → A')
     → is-equiv-Equiv-is-equiv
         ( ( t : I | ϕ t ∨ ψ t) → A' [ψ t ↦ τ' t])
         ( ( t : I | ϕ t ∨ ψ t) → A [ψ t ↦ α (τ' t)])
         ( \ υ' t → α (υ' t))
         ( ( t : ϕ) → A' [ϕ t ∧ ψ t ↦ τ' t])
         ( ( t : ϕ) → A [ϕ t ∧ ψ t ↦ α (τ' t)])
         ( \ ν' t → α (ν' t))
         ( cofibration-union-functorial I ϕ ψ (\ _ → A') (\ _ → A) (\ _ → α) τ')
         ( is-orth-ϕ-ψ∧ϕ (\ t → τ' t))
```

### Pushout products

Combining the stability under pushouts and crossing with a shape, we get
stability under pushout products.

```rzk
#def is-right-orthogonal-to-shape-pushout-product uses (extext)
  ( A' A : U)
  ( α : A' → A)
  ( J : CUBE)
  ( χ : J → TOPE)
  ( ζ : χ → TOPE)
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( is-orth-ψ-ϕ : is-right-orthogonal-to-shape I ψ ϕ A' A α)
  : is-right-orthogonal-to-shape (J × I)
    ( \ (t , s) → χ t ∧ ψ s)
    ( \ (t , s) → (ζ t ∧ ψ s) ∨ (χ t ∧ ϕ s))
    ( A') (A) (α)
  :=
    is-right-orthogonal-to-shape-left-cancel A' A α (J × I)
    ( \ (t , s) → χ t ∧ ψ s)
    ( \ (t , s) → (ζ t ∧ ψ s) ∨ (χ t ∧ ϕ s))
    ( \ (t , s) → χ t ∧ ϕ s)
    ( is-right-orthogonal-to-shape-pushout A' A α (J × I)
      ( \ (t , s) → ζ t ∧ ψ s)
      ( \ (t , s) → χ t ∧ ϕ s)
      ( is-right-orthogonal-to-shape-product A' A α J (\ t → ζ t) I ψ ϕ
        ( is-orth-ψ-ϕ)))
    ( is-right-orthogonal-to-shape-product A' A α J χ I ψ ϕ
      ( is-orth-ψ-ϕ))

#def is-right-orthogonal-to-shape-pushout-product' uses (extext)
  ( A' A : U)
  ( α : A' → A)
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( J : CUBE)
  ( χ : J → TOPE)
  ( ζ : χ → TOPE)
  ( is-orth-ψ-ϕ : is-right-orthogonal-to-shape I ψ ϕ A' A α)
  : is-right-orthogonal-to-shape (I × J)
    ( \ (s , t) → ψ s ∧ χ t)
    ( \ (s , t) → (ϕ s ∧ χ t) ∨ (ψ s ∧ ζ t))
    ( A') (A) (α)
  :=
    is-right-orthogonal-to-shape-transpose A' A α J I
    ( \ (t , s) → χ t ∧ ψ s)
    ( \ (t , s) → (ζ t ∧ ψ s) ∨ (χ t ∧ ϕ s))
    ( is-right-orthogonal-to-shape-pushout-product A' A α J χ ζ I ψ ϕ
      ( is-orth-ψ-ϕ))
```

### Functorial isomorphisms

If two pairs of shape inclusions `ϕ ⊂ ψ` and `ζ ⊂ χ` are (functorially)
isomorphic, then `ϕ ⊂ ψ` is left orthogonal if and only if `ζ ⊂ χ` is left
orthogonal.

```rzk
#def is-right-orthogonal-to-shape-isomorphism'
  ( A' A : U)
  ( α : A' → A)
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( J : CUBE)
  ( χ : J → TOPE)
  ( ζ : χ → TOPE)
  ( ( ( f , F) , (e , E)) : functorial-isomorphism-shape-inclusions I ψ ϕ J χ ζ)
  : is-right-orthogonal-to-shape I ψ ϕ A' A α
  → is-right-orthogonal-to-shape J χ ζ A' A α
  :=
  is-homotopy-cartesian-in-cube
  ( ζ → A') (\ σ' → (t : χ) → A' [ζ t ↦ σ' t])
  ( ζ → A) (\ σ' → (t : χ) → A [ζ t ↦ σ' t])
  ( \ σ' t → α (σ' t))
  ( \ _ τ' t → α (τ' t))
  ( ϕ → A') (\ σ' → (t : ψ) → A' [ϕ t ↦ σ' t])
  ( ϕ → A) (\ σ' → (t : ψ) → A [ϕ t ↦ σ' t])
  ( \ σ' t → α (σ' t))
  ( \ _ τ' t → α (τ' t))
  ( first (f A')) (first (f A))
  ( e A' A α)
  ( \ σ' → first (F A' σ')) (\ σ → first (F A σ))
  ( E A' A α)
  ( \ σ' → second (F A' σ')) (\ σ → second (F A σ))

#def is-right-orthogonal-to-shape-isomorphism
  ( A' A : U)
  ( α : A' → A)
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( J : CUBE)
  ( χ : J → TOPE)
  ( ζ : χ → TOPE)
  ( ( ( f , F) , (e , E)) : functorial-isomorphism-shape-inclusions I ψ ϕ J χ ζ)
  : is-right-orthogonal-to-shape J χ ζ A' A α
  → is-right-orthogonal-to-shape I ψ ϕ A' A α
  :=
  is-homotopy-cartesian-in-cube'
  ( ζ → A') (\ σ' → (t : χ) → A' [ζ t ↦ σ' t])
  ( ζ → A) (\ σ' → (t : χ) → A [ζ t ↦ σ' t])
  ( \ σ' t → α (σ' t))
  ( \ _ τ' t → α (τ' t))
  ( ϕ → A') (\ σ' → (t : ψ) → A' [ϕ t ↦ σ' t])
  ( ϕ → A) (\ σ' → (t : ψ) → A [ϕ t ↦ σ' t])
  ( \ σ' t → α (σ' t))
  ( \ _ τ' t → α (τ' t))
  ( first (f A')) (first (f A))
  ( e A' A α)
  ( \ σ' → first (F A' σ')) (\ σ → first (F A σ))
  ( E A' A α)
  ( \ σ' → second (F A' σ')) (\ σ → second (F A σ))
  ( second (second (f A')))
```

### Functorial retracts

If `ϕ ⊂ ψ` is a left orthogonal shape inclusion and `ζ ⊂ χ` is a (functorial)
retract of it, then `ζ ⊂ χ` is also left orthogonal.

```rzk
#def is-right-orthogonal-to-shape-retract
  ( A' A : U)
  ( α : A' → A)
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ χ : ψ → TOPE)
  -- ζ := χ ∧ ϕ
  ( ( ( s , S) , (h , H)) : functorial-retract-shape-inclusion I ψ ϕ χ)
  : is-right-orthogonal-to-shape I ψ ϕ A' A α
  → is-right-orthogonal-to-shape I (\ t → χ t) (\ t → χ t ∧ ϕ t) A' A α
  :=
  \ is-orth-ψ-ϕ (σ' : (t : I | χ t ∧ ϕ t) → A')
  → push-down-equiv-with-section
    ( ( t : χ) → A' [χ t ∧ ϕ t ↦ σ' t])
    ( \ τ' → (t : ψ) → A' [χ t ↦ τ' t , ϕ t ↦ s A' σ' t])
    ( ( t : χ) → A [χ t ∧ ϕ t ↦ α (σ' t)])
    ( \ τ → (t : ψ) → A [χ t ↦ τ t , ϕ t ↦ s A (\ t' → α (σ' t')) t])
    ( \ τ' t → α (τ' t))
    ( \ τ' υ →
      ( transport
        ( ( t : ϕ) → A [χ t ∧ ϕ t ↦ α (σ' t)])
        ( \ σ → (t : ψ) → A [χ t ↦ α (τ' t) , ϕ t ↦ σ t])
        ( \ t → α (s A' σ' t))
        ( s A (\ t → α (σ' t)))
        ( h A' A α σ')
        ( \ t → α (υ t))))
    ( ( S A' σ' , S A (\ t → α (σ' t)))
    , H A' A α σ')
    ( second
      ( equiv-comp
      ( Σ ( τ' : (t : χ) → A' [χ t ∧ ϕ t ↦ σ' t])
      , ( t : ψ) → A' [χ t ↦ τ' t , ϕ t ↦ s A' σ' t])
      ( Σ ( τ : (t : χ) → A [χ t ∧ ϕ t ↦ α (σ' t)])
          , ( t : ψ) → A [χ t ↦ τ t , ϕ t ↦ α (s A' σ' t)])
        ( Σ ( τ : (t : χ) → A [χ t ∧ ϕ t ↦ α (σ' t)])
          , ( t : ψ) → A [χ t ↦ τ t , ϕ t ↦ s A (\ t' → α (σ' t')) t])
        ( ( \ (τ' , υ') →
            ( ( \ t → α (τ' t))
            , ( \ t → α (υ' t))))
        , ( is-equiv-Equiv-is-equiv'
            ( ( t : ψ) → A' [ϕ t ↦ s A' σ' t])
            ( ( t : ψ) → A [ϕ t ↦ α (s A' σ' t)])
            ( \ υ' t → α (υ' t))
            ( Σ ( τ' : (t : χ) → A' [χ t ∧ ϕ t ↦ σ' t])
              , ( t : ψ) → A' [χ t ↦ τ' t , ϕ t ↦ s A' σ' t])
            ( Σ ( τ : (t : χ) → A [χ t ∧ ϕ t ↦ α (σ' t)])
              , ( t : ψ) → A [χ t ↦ τ t , ϕ t ↦ α (s A' σ' t)])
              ( \ (τ' , υ') → ((\ t → α (τ' t)) , (\ t → α (υ' t))))
              ( cofibration-composition-functorial'' I ψ ϕ χ
                ( \ _ → A') (\ _ → A) (\ _ → α) (s A' σ'))
            ( is-orth-ψ-ϕ (s A' σ'))))
        ( total-equiv-family-of-equiv
          ( ( t : χ) → A [χ t ∧ ϕ t ↦ α (σ' t)])
          ( \ τ → (t : ψ) → A [χ t ↦ τ t , ϕ t ↦ α (s A' σ' t)])
          ( \ τ → (t : ψ) → A [χ t ↦ τ t , ϕ t ↦ s A (\ t' → α (σ' t')) t])
          ( \ τ →
            equiv-transport
            ( ( t : ϕ) → A [χ t ∧ ϕ t ↦ α (σ' t)])
            ( \ σ → (t : ψ) → A [χ t ↦ τ t , ϕ t ↦ σ t])
            ( \ t → α (s A' σ' t))
            ( s A (\ t → α (σ' t)))
            ( h A' A α σ')))))
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

### Equivalences are right orthogonal

Every equivalence `α : A' → A` is right orthogonal to `ϕ ⊂ ψ`.

```rzk
#def is-right-orthogonal-is-equiv-to-shape uses (extext)
  ( A' A : U)
  ( α : A' → A)
  ( is-equiv-α : is-equiv A' A α)
  : is-right-orthogonal-to-shape I ψ ϕ A' A α
  :=
    ( \ a → is-equiv-extensions-is-equiv extext I ψ ϕ
      ( \ _ → A') (\ _ → A) (\ _ → α) (a) (\ _ → is-equiv-α))
```

Right orthogonality is closed under homotopy.

```rzk
#def is-right-orthogonal-homotopy-to-shape uses (funext)
  ( A' A : U)
  ( α β : A' → A)
  ( h : homotopy A' A α β)
  : is-right-orthogonal-to-shape I ψ ϕ A' A α
  → is-right-orthogonal-to-shape I ψ ϕ A' A β
  :=
    transport (A' → A) (is-right-orthogonal-to-shape I ψ ϕ A' A) α β
    ( first (first (funext A' (\ _ → A) α β)) h)
```

### Composition

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

One can always cancel right orthogonal maps from the right.

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

### Left cancellation with section

If the map `α' : A'' → A'` has a section, then we can also cancel it from the
right (whether it is right orthogonal or not.)

```rzk
#def is-right-orthogonal-left-cancel-with-section-to-shape
  uses (extext is-orth-ψ-ϕ-αα')
  ( has-section-α' : has-section A'' A' α')
  : is-right-orthogonal-to-shape I ψ ϕ A' A α
  :=
    is-homotopy-cartesian-left-cancel-with-section'
        ( ϕ → A'') (\ σ'' → (t : ψ) → A'' [ϕ t ↦ σ'' t])
        ( ϕ → A') (\ σ' → (t : ψ) → A' [ϕ t ↦ σ' t])
        ( ϕ → A) (\ σ → (t : ψ) → A [ϕ t ↦ σ t])
        ( \ σ'' t → α' (σ'' t)) (\ _ τ'' x → α' (τ'' x))
        ( \ σ' t → α (σ' t)) (\ _ τ' x → α (τ' x))
    ( has-section-extensions-BOT-has-section extext I (\ t → ϕ t)
          ( \ _ → A'') (\ _ → A') (\ _ → α')
      ( \ _ → has-section-α'))
    ( has-section-extensions-has-section extext I ψ ϕ
          ( \ _ → A'') (\ _ → A') (\ _ → α')
      ( \ _ → has-section-α'))
    ( is-orth-ψ-ϕ-αα')
```

### Pullback

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
  ( ( τA' , hA)
 : general-relative-extension-type I ψ ϕ (\ _ → A') (\ _ → A) (\ _ → α)
      ( \ t → first-relative-product A A' α B f (σB' t))
      ( \ t → f (τB t))
      ( \ t → homotopy-relative-product A A' α B f (σB' t)))
  : relative-extension-type I ψ ϕ
    ( \ _ → relative-product A A' α B f) (\ _ → B)
    ( \ _ → second-relative-product A A' α B f)
    ( σB') (τB)
  :=
    ( \ t → ((τA' t , τB t) , hA t)
    , \ t → refl)

#def general-relative-extension-type-relative-extension-type-pullback
  ( σB' : ϕ → relative-product A A' α B f)
  ( τB : (t : ψ) → B [ϕ t ↦ second-relative-product A A' α B f (σB' t)])
  ( ( τB' , hB)
 : relative-extension-type I ψ ϕ
      ( \ _ → relative-product A A' α B f) (\ _ → B)
      ( \ _ → second-relative-product A A' α B f)
      ( σB') (τB))
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
        ( f) (hB t)))

#def is-id-rel-ext-type-pb-gen-rel-ext-type-rel-ext-type-pb uses (extext)
  ( σB' : ϕ → relative-product A A' α B f)
  ( τB : (t : ψ) → B [ϕ t ↦ second-relative-product A A' α B f (σB' t)])
  : ( τhB
 : relative-extension-type I ψ ϕ
        ( \ _ → relative-product A A' α B f) (\ _ → B)
        ( \ _ → second-relative-product A A' α B f)
        ( σB') (τB))
  → ( relative-extension-type-pullback-general-relative-extension-type σB' τB
      ( general-relative-extension-type-relative-extension-type-pullback σB' τB τhB)
    = τhB)
  :=
    ind-has-section-equiv
    ( fiber-postcomp-Π-ext I ψ ϕ
      ( \ _ → relative-product A A' α B f) (\ _ → B)
      ( \ _ → second-relative-product A A' α B f)
      ( σB') (τB))
    ( relative-extension-type I ψ ϕ
      ( \ _ → relative-product A A' α B f) (\ _ → B)
      ( \ _ → second-relative-product A A' α B f)
      ( σB') (τB))
    ( equiv-relative-extension-type-fib extext I ψ ϕ
      ( \ _ → relative-product A A' α B f) (\ _ → B)
      ( \ _ → second-relative-product A A' α B f)
      ( σB') (τB))
    ( \ τhB →
      ( relative-extension-type-pullback-general-relative-extension-type σB' τB
        ( general-relative-extension-type-relative-extension-type-pullback σB' τB τhB)
      = τhB))
    ( ind-fib
      ( ( t : ψ) → relative-product A A' α B f [ϕ t ↦ σB' t])
      ( ( t : ψ) → B [ϕ t ↦ second-relative-product A A' α B f (σB' t)])
      ( \ τB' t → second-relative-product A A' α B f (τB' t))
      ( \ τB₁ (τB'₁ , h₁) →
        ( relative-extension-type-pullback-general-relative-extension-type σB' τB₁
          ( general-relative-extension-type-relative-extension-type-pullback σB' τB₁
            ( τB'₁
            , ext-htpy-eq I ψ ϕ (\ _ → B)
              ( \ t → second-relative-product A A' α B f (σB' t))
              ( \ t → second-relative-product A A' α B f (τB'₁ t))
              ( τB₁) (h₁)))
        = ( τB'₁
          , ext-htpy-eq I ψ ϕ (\ _ → B)
            ( \ t → second-relative-product A A' α B f (σB' t))
            ( \ t → second-relative-product A A' α B f (τB'₁ t))
            ( τB₁) (h₁))))
      ( \ τB' → refl)
      ( τB))

#def is-retract-of-rel-ext-type-pb-gen-rel-ext-type uses (extext)
  ( σB' : ϕ → relative-product A A' α B f)
  ( τB : (t : ψ) → B [ϕ t ↦ second-relative-product A A' α B f (σB' t)])
  : is-retract-of
    ( relative-extension-type I ψ ϕ
      ( \ _ → relative-product A A' α B f) (\ _ → B)
      ( \ _ → second-relative-product A A' α B f)
      ( σB') (τB))
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
#def is-right-orthogonal-pullback-to-shape uses (extext is-orth-ψ-ϕ-α B f)
  : is-right-orthogonal-to-shape I ψ ϕ
    ( relative-product A A' α B f) (B)
    ( second-relative-product A A' α B f)
  :=
    is-right-orthogonal-to-shape-has-contr-relative-extension-types I ψ ϕ
    ( relative-product A A' α B f) (B)
    ( second-relative-product A A' α B f)
    ( \ σB' τB →
      is-contr-is-retract-of-is-contr
      ( relative-extension-type I ψ ϕ
        ( \ _ → relative-product A A' α B f) (\ _ → B)
        ( \ _ → second-relative-product A A' α B f)
        ( σB') (τB))
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

### Stability under equivalence

If two maps `α : A' → A` and `β : B' → B` are equivalent, then if one is right
orthogonal to `ϕ ⊂ ψ`, then so is the other.

```rzk
#section is-right-orthogonal-equiv-to-shape

#variable I : CUBE
#variable ψ : I → TOPE
#variable ϕ : ψ → TOPE
#variables A' A : U
#variable α : A' → A
#variables B' B : U
#variable β : B' → B

#def is-right-orthogonal-equiv-to-shape uses (funext extext)
  ( ( ( ( s' , s) , η) , (is-equiv-s' , is-equiv-s)) : Equiv-of-maps A' A α B' B β)
  ( is-orth-ψ-ϕ-β : is-right-orthogonal-to-shape I ψ ϕ B' B β)
  : is-right-orthogonal-to-shape I ψ ϕ A' A α
  :=
    is-right-orthogonal-right-cancel-to-shape I ψ ϕ A' A B α s
    ( is-right-orthogonal-is-equiv-to-shape I ψ ϕ A B s is-equiv-s)
    ( is-right-orthogonal-homotopy-to-shape I ψ ϕ A' B
      ( \ a' → β (s' a')) (\ a' → s (α a')) (η)
      ( is-right-orthogonal-comp-to-shape I ψ ϕ A' B' B s' β
        ( is-right-orthogonal-is-equiv-to-shape I ψ ϕ A' B' s' is-equiv-s')
        ( is-orth-ψ-ϕ-β)))

#def is-right-orthogonal-equiv-to-shape'
  uses (funext extext)
  ( ( ( ( s' , s) , η) , (is-equiv-s' , is-equiv-s)) : Equiv-of-maps A' A α B' B β)
  ( is-orth-ψ-ϕ-α : is-right-orthogonal-to-shape I ψ ϕ A' A α)
  : is-right-orthogonal-to-shape I ψ ϕ B' B β
  :=
    is-right-orthogonal-left-cancel-with-section-to-shape
          I ψ ϕ A' B' B s' β
    ( is-right-orthogonal-homotopy-to-shape I ψ ϕ A' B
      ( \ a' → s (α a')) (\ a' → β (s' a'))
      ( rev-homotopy A' B (\ a' → β (s' a')) (\ a' → s (α a')) (η))
      ( is-right-orthogonal-comp-to-shape I ψ ϕ A' A B α s
        ( is-orth-ψ-ϕ-α)
        ( is-right-orthogonal-is-equiv-to-shape I ψ ϕ A B s is-equiv-s)))
    ( second is-equiv-s')

#end is-right-orthogonal-equiv-to-shape
```

### Exponentiation / product types

Let `α : A' → A` be right orthogonal to `ϕ ⊂ ψ`. Then the same is true for the
induced map `(X → A') → (X → A)` for any type `X`. More generally, if
`α x : A' x → A x` is a right orthogonal map for each `x : X`, then so is the
map on dependent products `Π α : Π A' → Π A`.

```rzk
#def is-right-orthogonal-Π-to-shape uses (funext)
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( X : U)
  ( A' A : X → U)
  ( α : (x : X) → (A' x) → (A x))
  ( are-right-orth-ψ-ϕ-α
 : ( x : X) → is-right-orthogonal-to-shape I ψ ϕ (A' x) (A x) (α x))
  : is-right-orthogonal-to-shape I ψ ϕ
    ( ( x : X) → A' x)
    ( ( x : X) → A x)
    ( \ a' x → α x (a' x))
  :=
  \ σ' →
    is-equiv-Equiv-is-equiv
    ( ( t : ψ) → ((x : X) → A' x) [ϕ t ↦ σ' t])
    ( ( t : ψ) → ((x : X) → A x) [ϕ t ↦ \ x → α x (σ' t x)])
    ( \ τ' t x → α x (τ' t x))
    ( ( x : X) → (t : ψ) → A' x [ϕ t ↦ σ' t x])
    ( ( x : X) → (t : ψ) → A x [ϕ t ↦ α x (σ' t x)])
    ( \ τ' x t → α x (τ' x t))
    ( flip-ext-fun-functorial I ψ ϕ X
      ( \ _ → A') (\ _ → A) (\ _ → α)
      ( σ'))
    ( is-equiv-function-is-equiv-family funext X
      ( \ x → (t : ψ) → A' x [ϕ t ↦ σ' t x])
      ( \ x → (t : ψ) → A x [ϕ t ↦ α x (σ' t x)])
      ( \ x τ' t → α x (τ' t))
      ( \ x → are-right-orth-ψ-ϕ-α x (\ t → σ' t x)))
```

### Sigma types

Warning: It is _not_ true that right orthogonal maps are preserved under
dependent sums.

Indeed, every map `f: A → B` can be written as
`Σ (b : B) , fib f b → Σ (b : B) , Unit`; and it is not true that `f` is right
orthogonal if and only if each `fib f b → Unit` is right orthogonal. For
example, the map `{0} → Δ¹` is not a left fibration even though its fibers are
all left fibrant (i.e. discrete).

## Types with unique extension

We say that an type `A` has unique extensions for a shape inclusion `ϕ ⊂ ψ`, if
for each `σ : ϕ → A` the type of `ψ`-extensions is contractible.

```rzk
#section has-unique-extensions
#variable I : CUBE
#variable ψ : I → TOPE
#variable ϕ : ψ → TOPE
#variable A : U

#def has-unique-extensions
  : U
  := (σ : ϕ → A) → is-contr ((t : ψ) → A [ϕ t ↦ σ t])
```

There are other equivalent characterizations which we shall prove below:

We can ask that the canonical restriction map `(ψ → A) → (ϕ → A)` is an
equivalence.

```rzk
#def is-local-type
  : U
  := is-equiv (ψ → A) (ϕ → A) (\ τ t → τ t)
```

We can ask that the terminal map `A → Unit` is right orthogonal to `ϕ ⊂ ψ`.

```rzk
#def is-right-orthogonal-terminal-map
  : U
  := is-right-orthogonal-to-shape I ψ ϕ A Unit (terminal-map A)
```

### Unique extensions types are local types

The equivalence between `is-local-type` and `has-unique-extensions` follows
straightforwardly from the fact that for every `σ : ϕ → A` we have an
equivalence between the extension type `(t : ψ) → A [ϕ t ↦ σ t]` and the fiber
of the restriction map `(ψ → A) → (ϕ → A)`.

```rzk
#def is-local-type-has-unique-extensions
  ( has-ue-ψ-ϕ-A : has-unique-extensions)
  : is-local-type
  :=
    is-equiv-is-contr-map (ψ → A) (ϕ → A) (\ τ t → τ t)
      ( \ (σ : ϕ → A)
      → is-contr-equiv-is-contr
          ( extension-type I ψ ϕ (\ t → A) σ)
          ( homotopy-extension-type I ψ ϕ (\ t → A) σ)
          ( extension-type-weakening I ψ ϕ (\ t → A) σ)
          ( has-ue-ψ-ϕ-A σ))

#def has-unique-extensions-is-local-type
  ( is-lt-ψ-ϕ-A : is-local-type)
  : has-unique-extensions
  :=
    \ σ →
      is-contr-equiv-is-contr'
        ( extension-type I ψ ϕ (\ t → A) σ)
        ( homotopy-extension-type I ψ ϕ (\ t → A) σ)
        ( extension-type-weakening I ψ ϕ (\ t → A) σ)
        ( is-contr-map-is-equiv
            ( ψ → A) (ϕ → A) (\ τ t → τ t)
            ( is-lt-ψ-ϕ-A)
            ( σ))

#end has-unique-extensions
```

### Properties of local types / unique extension types

We fix a shape inclusion `ϕ ⊂ ψ`.

```rzk
#section stability-properties-local-types
#variable I : CUBE
#variable ψ : I → TOPE
#variable ϕ : ψ → TOPE
```

Every map between types with unique extensions / local types is right
orthogonal.

```rzk
#def is-right-orthogonal-have-unique-extensions
  ( A' A : U)
  ( has-ue-ψ-ϕ-A' : has-unique-extensions I ψ ϕ A')
  ( has-ue-ψ-ϕ-A : has-unique-extensions I ψ ϕ A)
  ( α : A' → A)
  : is-right-orthogonal-to-shape I ψ ϕ A' A α
  :=
    \ σ →
      is-equiv-are-contr
      ( extension-type I ψ ϕ (\ _ → A') (σ))
      ( extension-type I ψ ϕ (\ _ → A) (\ t → α (σ t)))
      ( has-ue-ψ-ϕ-A' σ)
      ( has-ue-ψ-ϕ-A (\ t → α (σ t)))
      ( \ τ t → α (τ t))

#def is-right-orthogonal-are-local-types
  ( A' A : U)
  ( is-lt-ψ-ϕ-A' : is-local-type I ψ ϕ A')
  ( is-lt-ψ-ϕ-A : is-local-type I ψ ϕ A)
  : ( α : A' → A)
  → is-right-orthogonal-to-shape I ψ ϕ A' A α
  :=
    is-right-orthogonal-have-unique-extensions A' A
    ( has-unique-extensions-is-local-type I ψ ϕ A' is-lt-ψ-ϕ-A')
    ( has-unique-extensions-is-local-type I ψ ϕ A is-lt-ψ-ϕ-A)
```

Conversely, the property of having unique extension can be pulled back along any
right orthogonal map.

```rzk
#def has-unique-extensions-right-orthogonal-has-unique-extensions
  ( A' A : U)
  ( α : A' → A)
  ( is-orth-ψ-ϕ-α : is-right-orthogonal-to-shape I ψ ϕ A' A α)
  : has-unique-extensions I ψ ϕ A → has-unique-extensions I ψ ϕ A'
  :=
    \ has-ue-A (σ' : ϕ → A')
    → is-contr-equiv-is-contr'
        ( ( t : ψ) → A' [ϕ t ↦ σ' t])
        ( ( t : ψ) → A [ϕ t ↦ α (σ' t)])
        ( \ τ' t → α (τ' t) , is-orth-ψ-ϕ-α σ')
        ( has-ue-A (\ t → α (σ' t)))

#def is-local-type-right-orthogonal-is-local-type
  ( A' A : U)
  ( α : A' → A)
  ( is-orth-α : is-right-orthogonal-to-shape I ψ ϕ A' A α)
  ( is-local-A : is-local-type I ψ ϕ A)
  : is-local-type I ψ ϕ A'
  :=
    is-local-type-has-unique-extensions I ψ ϕ A'
      ( has-unique-extensions-right-orthogonal-has-unique-extensions
          ( A') (A) (α) (is-orth-α)
          ( has-unique-extensions-is-local-type I ψ ϕ A is-local-A))
```

Weak extension extensionality says that every contractible type has unique
extensions for every shape inclusion `ϕ ⊂ ψ`.

```rzk
#def has-unique-extensions-is-contr uses (extext)
  ( C : U)
  ( is-contr-C : is-contr C)
  : has-unique-extensions I ψ ϕ C
  :=
    weakextext-extext extext I ψ ϕ
    ( \ _ → C) (\ _ → is-contr-C)

#def is-local-type-is-contr uses (extext)
  ( C : U)
  ( is-contr-C : is-contr C)
  : is-local-type I ψ ϕ C
  :=
    is-local-type-has-unique-extensions I ψ ϕ C
    ( has-unique-extensions-is-contr C is-contr-C)

#def has-unique-extensions-Unit uses (extext)
  : has-unique-extensions I ψ ϕ Unit
  := has-unique-extensions-is-contr Unit is-contr-Unit
```

Unique extension types are closed under equivalence.

```rzk
#def is-local-type-equiv-is-local-type uses (extext)
  ( A' A : U)
  ( A'≃A : Equiv A' A)
  : is-local-type I ψ ϕ A → is-local-type I ψ ϕ A'
  :=
    is-equiv-Equiv-is-equiv
      ( ψ → A') (ϕ → A') (\ τ' t → τ' t)
      ( ψ → A)  (ϕ → A)  (\ τ t → τ t)
      ( equiv-of-restriction-maps-equiv extext I ψ ϕ
        ( \ _ → A') (\ _ → A) (\ _ → A'≃A))

#def has-unique-extensions-equiv-has-unique-extensions uses (extext)
  ( A' A : U)
  ( ( α , is-equiv-α) : Equiv A' A)
  : has-unique-extensions I ψ ϕ A → has-unique-extensions I ψ ϕ A'
  :=
    has-unique-extensions-right-orthogonal-has-unique-extensions A' A α
    ( is-right-orthogonal-is-equiv-to-shape I ψ ϕ A' A α is-equiv-α)

#end stability-properties-local-types
```

### Unique extension types are types with right orthogonal terminal map

Next we prove the logical equivalence between `has-unique-extensions` and
`is-right-orthogonal-terminal-map`. This follows directly from the fact that
`Unit` has unique extensions (using `extext`).

```rzk
#section is-right-orthogonal-terminal-map
#variable I : CUBE
#variable ψ : I → TOPE
#variable ϕ : ψ → TOPE
#variable A : U

#def has-unique-extensions-is-right-orthogonal-terminal-map
  uses (extext)
  ( is-orth-ψ-ϕ-tm-A : is-right-orthogonal-terminal-map I ψ ϕ A)
  : has-unique-extensions I ψ ϕ A
  :=
    has-unique-extensions-right-orthogonal-has-unique-extensions
      I ψ ϕ A Unit (terminal-map A)
    ( is-orth-ψ-ϕ-tm-A)
    ( has-unique-extensions-Unit I ψ ϕ)

#def has-unique-extensions-is-right-orthogonal-a-terminal-map
  uses (extext)
  ( tm : A → Unit)
  ( is-orth-ψ-ϕ-tm : is-right-orthogonal-to-shape I ψ ϕ A Unit tm)
  : has-unique-extensions I ψ ϕ A
  :=
    has-unique-extensions-right-orthogonal-has-unique-extensions
      I ψ ϕ A Unit tm
    ( is-orth-ψ-ϕ-tm)
    ( has-unique-extensions-Unit I ψ ϕ)

#def is-right-orthogonal-terminal-map-has-unique-extensions
  uses (extext)
  ( has-ue-ψ-ϕ-A : has-unique-extensions I ψ ϕ A)
  : is-right-orthogonal-terminal-map I ψ ϕ A
  :=
    is-right-orthogonal-have-unique-extensions I ψ ϕ A Unit
    ( has-ue-ψ-ϕ-A) (has-unique-extensions-Unit I ψ ϕ)
    ( terminal-map A)

#def is-right-orthogonal-terminal-map-is-local-type
  uses (extext)
  ( is-lt-ψ-ϕ-A : is-local-type I ψ ϕ A)
  : is-right-orthogonal-terminal-map I ψ ϕ A
  :=
    is-right-orthogonal-terminal-map-has-unique-extensions
    ( has-unique-extensions-is-local-type I ψ ϕ A is-lt-ψ-ϕ-A)

#def is-local-type-is-right-orthogonal-terminal-map
  uses (extext)
  ( is-orth-ψ-ϕ-tm-A : is-right-orthogonal-terminal-map I ψ ϕ A)
  : is-local-type I ψ ϕ A
  :=
    is-local-type-has-unique-extensions I ψ ϕ A
    ( has-unique-extensions-is-right-orthogonal-terminal-map
      ( is-orth-ψ-ϕ-tm-A))

#end is-right-orthogonal-terminal-map
```

## Fibers of right orthogonal maps

Let `α : A' → A` be right orthogonal to `ϕ ⊂ ψ`. Then every fiber of `α` has
unique extensions along `ϕ ⊂ ψ`. This follows immediately since the fibers of
`α` are just the relative products of `α : A' → A` with the maps `a : Unit → A`
from the unit type.

```rzk
#def has-fiberwise-unique-extensions-is-right-orthogonal-to-shape
  uses (extext)
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( A' A : U)
  ( α : A' → A)
  ( is-orth-ψ-ϕ-α : is-right-orthogonal-to-shape I ψ ϕ A' A α)
  ( a : A)
  : has-unique-extensions I ψ ϕ (fib A' A α a)
  :=
    has-unique-extensions-equiv-has-unique-extensions I ψ ϕ
    ( fib A' A α a)
    ( relative-product A A' α Unit (\ unit → a))
    ( compute-pullback-to-Unit A' A α a)
    ( has-unique-extensions-is-right-orthogonal-terminal-map I ψ ϕ
      ( relative-product A A' α Unit (\ unit → a))
      ( is-right-orthogonal-pullback-to-shape I ψ ϕ A' A α
        ( is-orth-ψ-ϕ-α) (Unit) (\ unit → a)))
```

Corollary: Given two types `A'` and `A` with unique extensions w.r.t. `ϕ ⊂ ψ`,
every fiber of every map `α : A' → A` also has unique extensions.

```rzk
#def has-fiberwise-unique-extensions-have-unique-extensions
  uses (extext)
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( A' A : U)
  ( α : A' → A)
  ( has-ue-ψ-ϕ-A' : has-unique-extensions I ψ ϕ A')
  ( has-ue-ψ-ϕ-A : has-unique-extensions I ψ ϕ A)
  : ( a : A) → has-unique-extensions I ψ ϕ (fib A' A α a)
  :=
    has-fiberwise-unique-extensions-is-right-orthogonal-to-shape I ψ ϕ A' A α
    ( is-right-orthogonal-have-unique-extensions I ψ ϕ A' A
      ( has-ue-ψ-ϕ-A') (has-ue-ψ-ϕ-A) (α))
```

## Anodyne shape inclusions

Fix a shape inclusion `ϕ ⊂ ψ`. We say that another shape inclusion `χ ⊂ ζ` is
**anodyne for** `ϕ ⊂ ψ`, is every map that is right orthogonal to `ϕ ⊂ ψ` is
also right orthogonal to `χ ⊂ ζ`.

```rzk
#section anodyne

#variable I₀ : CUBE
#variable ψ₀ : I₀ → TOPE
#variable ϕ₀ : ψ₀ → TOPE


#def is-anodyne-for-shape
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  : U
  :=
    ( ( A' : U) → (A : U) → (α : A' → A)
    → is-right-orthogonal-to-shape I₀ ψ₀ ϕ₀ A' A α
    → is-right-orthogonal-to-shape I ψ ϕ A' A α)
```

Of course every shape inclusion is anodyne for itself.

```rzk
#def is-anodyne-for-self
  : is-anodyne-for-shape I₀ ψ₀ ϕ₀
  := \ _ _ _ is-orth₀ → is-orth₀
```

All the stability properties above can be seen as implications between
conditions of being anodyne.

```rzk
#def is-anodyne-comp-for-shape
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( χ : ψ → TOPE)
  ( ϕ : χ → TOPE)
  : is-anodyne-for-shape I ψ χ
  → is-anodyne-for-shape I (\ t → χ t) (\ t → ϕ t)
  → is-anodyne-for-shape I ψ (\ t → ϕ t)
  :=
    \ f g A' A α is-orth₀ →
    ( is-right-orthogonal-to-shape-comp A' A α I ψ χ ϕ
      ( f A' A α is-orth₀)
      ( g A' A α is-orth₀))

#def is-anodyne-left-cancel-for-shape
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( χ : ψ → TOPE)
  ( ϕ : χ → TOPE)
  : is-anodyne-for-shape I (\ t → χ t) (\ t → ϕ t)
  → is-anodyne-for-shape I ψ (\ t → ϕ t)
  → is-anodyne-for-shape I ψ χ
  :=
    \ f g A' A α is-orth₀ →
    ( is-right-orthogonal-to-shape-left-cancel A' A α I ψ χ ϕ
      ( f A' A α is-orth₀)
      ( g A' A α is-orth₀))

#def is-anodyne-right-cancel-retract-for-shape
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( χ : ψ → TOPE)
  ( ϕ : χ → TOPE)
  : is-functorial-shape-retract I ψ χ
  → is-anodyne-for-shape I ψ (\ t → ϕ t)
  → is-anodyne-for-shape I (\ t → χ t) (\ t → ϕ t)
  :=
    \ r f A' A α is-orth₀ →
    ( is-right-orthogonal-to-shape-right-cancel-retract A' A α I ψ χ ϕ
      ( f A' A α is-orth₀) (r))

#def is-anodyne-pushout-product-for-shape uses (extext)
  ( J : CUBE)
  ( χ : J → TOPE)
  ( ζ : χ → TOPE)
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  : is-anodyne-for-shape I ψ ϕ
  → is-anodyne-for-shape (J × I)
    ( \ (t , s) → χ t ∧ ψ s)
    ( \ (t , s) → (ζ t ∧ ψ s) ∨ (χ t ∧ ϕ s))
  :=
    \ f A' A α is-orth₀ →
    ( is-right-orthogonal-to-shape-pushout-product A' A α J χ ζ I ψ ϕ
      ( f A' A α is-orth₀))

#def is-anodyne-pushout-product-for-shape' uses (extext)
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( J : CUBE)
  ( χ : J → TOPE)
  ( ζ : χ → TOPE)
  : is-anodyne-for-shape I ψ ϕ
  → is-anodyne-for-shape (I × J)
    ( \ (s , t) → ψ s ∧ χ t)
    ( \ (s , t) → (ϕ s ∧ χ t) ∨ (ψ s ∧ ζ t))
  :=
    \ f A' A α is-orth₀ →
    ( is-right-orthogonal-to-shape-pushout-product' A' A α I ψ ϕ J χ ζ
      ( f A' A α is-orth₀))
```

### Weak anodyne shape inclusions

Instead of an implication with respect to right orthogonality, we ask for a mere
implication with respect to types with unique extensions.

```rzk
#def is-weak-anodyne-for-shape
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  : U
  :=
    ( ( A : U)
    → has-unique-extensions I₀ ψ₀ ϕ₀ A
    → has-unique-extensions I ψ ϕ A)
```

Every anodyne shape inclusion is weak anodyne.

```rzk
#def is-weak-anodyne-is-anodyne-for-shape uses (extext)
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  : is-anodyne-for-shape I ψ ϕ
  → is-weak-anodyne-for-shape I ψ ϕ
  :=
    \ f A has-ue₀ →
    ( has-unique-extensions-is-right-orthogonal-terminal-map I ψ ϕ A
      ( f A Unit (terminal-map A)
        ( is-right-orthogonal-terminal-map-has-unique-extensions I₀ ψ₀ ϕ₀ A
          has-ue₀)))
```

The inference rules that we saw above for anodyne shape inclusions all have an
analog fo weak anodyne shape inclusions.

```rzk
-- add them as you use them

#def is-weak-anodyne-for-self
  : is-weak-anodyne-for-shape I₀ ψ₀ ϕ₀
  := \ _ has-ue₀ → has-ue₀

#def implication-has-unique-extension-implication-right-orthogonal
  uses (extext)
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( J : CUBE)
  ( χ : J → TOPE)
  ( ζ : χ → TOPE)
  ( impl
 : ( A' : U) → (A : U) → (α : A' → A)
    → is-right-orthogonal-to-shape I ψ ϕ A' A α
    → is-right-orthogonal-to-shape J χ ζ A' A α)
  ( A : U)
  : has-unique-extensions I ψ ϕ A
  → has-unique-extensions J χ ζ A
  :=
    \ has-ue-ψ-ϕ →
    has-unique-extensions-is-right-orthogonal-terminal-map J χ ζ A
    ( impl A Unit (terminal-map A)
      ( is-right-orthogonal-terminal-map-has-unique-extensions I ψ ϕ A
        has-ue-ψ-ϕ))

#def is-weak-anodyne-pushout-product-for-shape uses (extext)
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( J : CUBE)
  ( χ : J → TOPE)
  ( ζ : χ → TOPE)
  : is-weak-anodyne-for-shape I ψ ϕ
  → is-weak-anodyne-for-shape (J × I)
    ( \ (t , s) → χ t ∧ ψ s)
    ( \ (t , s) → (ζ t ∧ ψ s) ∨ (χ t ∧ ϕ s))

  :=
    \ f A has-ue₀ →
    implication-has-unique-extension-implication-right-orthogonal I ψ ϕ
    ( J × I) (\ (t , s) → χ t ∧ ψ s) (\ (t , s) → (ζ t ∧ ψ s) ∨ (χ t ∧ ϕ s))
    ( \ A'₁ A₁ α₁ →
      is-right-orthogonal-to-shape-pushout-product A'₁ A₁ α₁ J χ ζ I ψ ϕ)
    ( A) (f A has-ue₀)

#def is-weak-anodyne-pushout-product-for-shape' uses (extext)
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( J : CUBE)
  ( χ : J → TOPE)
  ( ζ : χ → TOPE)
  : is-weak-anodyne-for-shape I ψ ϕ
  → is-weak-anodyne-for-shape (I × J)
    ( \ (s , t) → ψ s ∧ χ t)
    ( \ (s , t) → (ϕ s ∧ χ t) ∨ (ψ s ∧ ζ t))
  :=
    \ f A has-ue₀ →
    implication-has-unique-extension-implication-right-orthogonal I ψ ϕ
    ( I × J) (\ (s , t) → ψ s ∧ χ t) (\ (s , t) → (ϕ s ∧ χ t) ∨ (ψ s ∧ ζ t))
    ( \ A'₁ A₁ α₁ →
      is-right-orthogonal-to-shape-pushout-product' A'₁ A₁ α₁ I ψ ϕ J χ ζ)
    ( A) (f A has-ue₀)

#end anodyne
```
