# 4a. Right orthogonal fibrations

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

For every shape inclusion `ϕ ⊂ ψ`,
we obtain a fibrancy condition for a map `α : A' → A`
in terms of unique extension along `ϕ ⊂ ψ`.
This is a relative version of unique extension along `ϕ ⊂ ψ`.

We say that `α : A' → A` is _j-orthogonal_ to the shape inclusion `ϕ ⊂ ψ`,
or a right orthogonal fibration with respect to `ϕ ⊂ ψ`,
if the square
```
(ψ → A') → (ψ → A)

   ↓          ↓

(ϕ → A') → (ϕ → A)
```
is homotopy cartesian.

```rzk title="BW23, Section 3"
#def is-j-orthogonal-to-shape
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

## Stability properties of right orthogonal fibrations

Right orthogonal fibrations with respect to a shape inclusion `ϕ ⊂ ψ`
are stable under many operations.

### Stability under exponentiation

The j-orthogonality condition is preserved when crossing the inclusion `ϕ ⊂ ψ`
with another shape `χ`.

```rzk title="uncurried version of BW23, Corollary 3.16"
#def is-j-orthogonal-to-shape-×
  ( naiveextext : NaiveExtExt)
  ( J : CUBE)
  ( χ : J → TOPE)
  ( I : CUBE)
  ( ψ : I → TOPE )
  ( ϕ : ψ → TOPE )
  ( A' A : U)
  ( α : A' → A)
  ( is-jo : is-j-orthogonal-to-shape I ψ ϕ A' A α)
  : is-j-orthogonal-to-shape
      ( J × I) ( shape-prod J I χ ψ) ( \ (t,s) → χ t ∧ ϕ s) A' A α
  :=
    \ ( σ' : ( (t,s) : J × I | χ t ∧ ϕ s) → A') →
      (
        ( \ ( τ : ( (t,s) : J × I | χ t ∧ ψ s) → A[ϕ s ↦ α (σ' (t,s))])
            ( t, s) →
          ( first (first (is-jo (\ s' → σ' (t, s'))))) ( \ s' → τ (t, s')) s
        ,
          \ ( τ' : ( (t,s) : J × I | χ t ∧ ψ s) → A'[ϕ s ↦ σ' (t,s)]) →
            naiveextext
              ( J × I) ( \ (t,s) → χ t ∧ ψ s) ( \ (t,s) → χ t ∧ ϕ s)
              ( \ _ → A')
              ( \ ( t,s) → σ' (t,s))
              ( \ ( t,s) →
                ( first (first (is-jo (\ s' → σ' (t, s')))))
                  ( \ s' → α (τ' (t, s'))) s
              )
              ( τ')
              ( \ ( t,s) →
                ext-htpy-eq I ψ ϕ (\ _ → A') ( \ s' → σ' (t, s'))
                  ( ( first (first (is-jo (\ s' → σ' (t, s')))))
                    ( \ s' → α (τ' (t, s')))
                  )
                  ( \ s' → τ' (t, s') )
                  ( ( second (first (is-jo (\ s' → σ' (t, s')))))
                    ( \ s' → τ' (t, s'))
                  )
                  ( s)
              )
        )
      ,
        ( \ ( τ : ( (t,s) : J × I | χ t ∧ ψ s) → A[ϕ s ↦ α (σ' (t,s))])
            ( t, s) →
          ( first (second (is-jo (\ s' → σ' (t, s'))))) ( \ s' → τ (t, s')) s
        ,
          \ ( τ : ( (t,s) : J × I | χ t ∧ ψ s) → A[ϕ s ↦ α (σ' (t,s))]) →
            naiveextext
              ( J × I) ( \ (t,s) → χ t ∧ ψ s) ( \ (t,s) → χ t ∧ ϕ s)
              ( \ _ → A)
              ( \ (t,s) → α (σ' (t,s)))
              ( \ (t,s) →
                α ( ( first ( second ( is-jo (\ s' → σ' (t, s')))))
                      ( \ s' → τ (t, s')) s
                  )
              )
              ( τ)
              ( \ ( t,s) →
                ext-htpy-eq I ψ ϕ (\ _ → A) ( \ s' → α (σ' (t, s')))
                  ( \ s'' →
                      α ( ( first (second (is-jo (\ s' → σ' (t, s')))))
                          ( \ s' → τ (t, s'))
                          (s'')
                        )
                  )
                  ( \ s' → τ (t, s') )
                  ( ( second ( second (is-jo (\ s' → σ' (t, s')))))
                    ( \ s' → τ (t, s'))
                  )
                  ( s)

              )
        )
      )
```
