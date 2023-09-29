# 4a. Right orthogonal fibrations

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Prerequisites

Some of the definitions in this file rely on naive extension extensionality:

```rzk
#assume naiveextext : NaiveExtExt
```

## Right orthogonal maps with respect to shapes

For every shape inclusion `ϕ ⊂ ψ`,
we obtain a fibrancy condition for a map `α : A' → A`
in terms of unique extension along `ϕ ⊂ ψ`.
This is a relative version of unique extension along `ϕ ⊂ ψ`.

We say that `α : A' → A` is _right orthogonal_ to the shape inclusion `ϕ ⊂ ψ`,
if the square
```
(ψ → A') → (ψ → A)

   ↓          ↓

(ϕ → A') → (ϕ → A)
```
is homotopy cartesian.

Equivalently, we can interpret this orthogonality
as a cofibrancy condition on the shape inclusion.
We say that the shape inclusion `ϕ ⊂ ψ` is _left orthogonal_ to the map `α`,
if `α : A' → A` is right orthogonal to `ϕ ⊂ ψ`.

```rzk title="BW23, Section 3"
#def is-right-orthogonal-to-shape
  ( I : CUBE)
  ( ψ : I → TOPE )
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

## Stability properties of left orthogonal shape inclusions

We fix a map `α : A' → A`.

```rzk
#section left-orthogonal-calculus

#variables A' A : U
#variable α : A' → A
```

### Stability under composition

Left orthogonal shape inclusions are preserved under composition.

```rzk title="right-orthogonality for composition of shape inclusions"

#def is-right-orthogonal-to-shape-comp
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( χ : ψ → TOPE)
  ( ϕ : χ → TOPE)
  ( is-orth-ψ-χ : is-right-orthogonal-to-shape I ψ χ A' A α)
  ( is-orth-χ-ϕ : is-right-orthogonal-to-shape I ( \ t → χ t) ( \ t → ϕ t) A' A α)
  : is-right-orthogonal-to-shape I ψ ( \ t → ϕ t) A' A α
  :=
    \ σ' →
      is-equiv-equiv-is-equiv
        ( ( t : ψ) → A' [ϕ t ↦ σ' t])
        ( ( t : ψ) → A [ϕ t ↦ α (σ' t)])
        ( \ υ' t → α ( υ' t))
        ( Σ ( τ' : (t : χ) → A' [ϕ t ↦ σ' t]),
          ( ( t : ψ) → A' [χ t ↦ τ' t]))
        ( Σ ( τ : ( t : χ) → A [ϕ t ↦ α (σ' t)]),
          ( ( t : ψ) → A [χ t ↦ τ t]))
        ( \ (τ', υ') → ( \ t → α (τ' t), \t → α (υ' t)))
        ( ( ( first ( cofibration-composition I ψ χ ϕ ( \ _ → A') σ'))
          ,
            ( first ( cofibration-composition I ψ χ ϕ
                      ( \ _ → A) ( \ t → α (σ' t))))
          ),
          ( \ _ → refl))
        ( second ( cofibration-composition I ψ χ ϕ ( \ _ → A') σ'))
        ( second ( cofibration-composition I ψ χ ϕ ( \ _ → A) ( \ t → α (σ' t))))
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

### Stability under exponentiation

If `ϕ ⊂ ψ` is left orthogonal to `α : A' → A`
then so is `χ × ϕ ⊂ χ × ψ` for every other shape `χ`.

```rzk title="uncurried version of BW23, Corollary 3.16"
#def is-right-orthogonal-to-shape-× uses (naiveextext)
  ( J : CUBE)
  ( χ : J → TOPE)
  ( I : CUBE)
  ( ψ : I → TOPE )
  ( ϕ : ψ → TOPE )
  ( is-orth : is-right-orthogonal-to-shape I ψ ϕ A' A α)
  : is-right-orthogonal-to-shape
      ( J × I) ( shape-prod J I χ ψ) ( \ (t,s) → χ t ∧ ϕ s) A' A α
  :=
    \ ( σ' : ( (t,s) : J × I | χ t ∧ ϕ s) → A') →
      (
        ( \ ( τ : ( (t,s) : J × I | χ t ∧ ψ s) → A[ϕ s ↦ α (σ' (t,s))])
            ( t, s) →
          ( first (first (is-orth (\ s' → σ' (t, s'))))) ( \ s' → τ (t, s')) s
        ,
          \ ( τ' : ( (t,s) : J × I | χ t ∧ ψ s) → A' [ϕ s ↦ σ' (t,s)]) →
            naiveextext
              ( J × I) ( \ (t,s) → χ t ∧ ψ s) ( \ (t,s) → χ t ∧ ϕ s)
              ( \ _ → A')
              ( \ ( t,s) → σ' (t,s))
              ( \ ( t,s) →
                ( first (first (is-orth (\ s' → σ' (t, s')))))
                  ( \ s' → α (τ' (t, s'))) s)
              ( τ')
              ( \ ( t,s) →
                ext-htpy-eq I ψ ϕ (\ _ → A') ( \ s' → σ' (t, s'))
                  ( ( first (first (is-orth (\ s' → σ' (t, s')))))
                    ( \ s' → α (τ' (t, s'))))
                  ( \ s' → τ' (t, s') )
                  ( ( second (first (is-orth (\ s' → σ' (t, s')))))
                    ( \ s' → τ' (t, s')))
                  ( s)
              )
        )
      ,
        ( \ ( τ : ( (t,s) : J × I | χ t ∧ ψ s) → A [ϕ s ↦ α (σ' (t,s))])
            ( t, s) →
          ( first (second (is-orth (\ s' → σ' (t, s'))))) ( \ s' → τ (t, s')) s
        ,
          \ ( τ : ( (t,s) : J × I | χ t ∧ ψ s) → A [ϕ s ↦ α (σ' (t,s))]) →
            naiveextext
              ( J × I) ( \ (t,s) → χ t ∧ ψ s) ( \ (t,s) → χ t ∧ ϕ s)
              ( \ _ → A)
              ( \ (t,s) → α (σ' (t,s)))
              ( \ (t,s) →
                α ( ( first ( second ( is-orth (\ s' → σ' (t, s')))))
                      ( \ s' → τ (t, s')) s))
              ( τ)
              ( \ ( t,s) →
                ext-htpy-eq I ψ ϕ (\ _ → A) ( \ s' → α (σ' (t, s')))
                  ( \ s'' →
                      α ( ( first (second (is-orth (\ s' → σ' (t, s')))))
                          ( \ s' → τ (t, s'))
                          (s'')))
                  ( \ s' → τ (t, s') )
                  ( ( second ( second (is-orth (\ s' → σ' (t, s')))))
                    ( \ s' → τ (t, s')))
                  ( s)
              )
        )
      )

#end left-orthogonal-calculus
```
