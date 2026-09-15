# Orthogonal families

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Prerequisites

- `hott/*` - We require various prerequisites from homotopy type theory, for
  instance the notion of equivalence (`#!rzk Equiv`, `#!rzk is-equiv`).
- `shott/03-extension-types.rzk.md`

## Definition of orthogonal families

```rzk title="BW23, Corollary 3.1.2"
#def is-right-orthogonal-family
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( φ : ψ → TOPE)
  ( A : U)
  ( C : A → U)
  : U
  :=
    ( a : ψ → A)
  → ( f : (t : φ) → C (a t))
  → is-contr ((t : ψ) → C (a t) [φ t ↦ f t])
```

## A family is orthogonal if and only if the restriction is an equivalence

```rzk

#section is-right-orthogonal-iff-is-equiv-restrict-sections

#variable I : CUBE
#variable ψ : I → TOPE
#variable φ : ψ → TOPE
#variable A : U
#variable C : A → U


#def is-right-orthogonal-family-is-equiv-restrict-sections
  ( is-equiv-restriction : (a : ψ → A)
  → is-equiv
      ( ( t : ψ) → C (a t))
      ( ( t : φ) → C (a t))
      ( \ s t → s t))
  :
  is-right-orthogonal-family I ψ φ A C
  := \ a f →
    equiv-with-contractible-domain-implies-contractible-codomain
      ( fib
        ( ( t : ψ) → C (a t))
        ( ( t : φ) → C (a t))
        ( \ s t → s t)
        f)
      ( ( t : ψ) → C (a t) [φ t ↦ f t])
      ( inv-equiv
        ( ( t : ψ) → C (a t) [φ t ↦ f t])
        ( fib
          ( ( t : ψ) → C (a t))
          ( ( t : φ) → C (a t))
          ( \ s t → s t)
          f)
        ( extension-type-weakening-map I ψ φ
          ( \ t → C (a t))
          f
        , is-equiv-extension-type-weakening I ψ φ
            ( \ t → C (a t))
            f))
      ( is-contr-map-is-equiv
        ( ( t : ψ) → C (a t))
        ( ( t : φ) → C (a t))
        ( \ s t → s t)
        ( is-equiv-restriction a)
        f)

#def is-equiv-restrict-sections-is-right-orthogonal-family
  ( is-right-orthogonal-C : is-right-orthogonal-family I ψ φ A C)
  :
  ( a : ψ → A)
  → is-equiv
      ( ( t : ψ) → C (a t))
      ( ( t : φ) → C (a t))
      ( \ s t → s t)
  := \ a →
    is-equiv-is-contr-map
      ( ( t : ψ) → C (a t))
      ( ( t : φ) → C (a t))
      ( \ s t → s t)
      ( \ f →
        equiv-with-contractible-domain-implies-contractible-codomain
          ( ( t : ψ) → C (a t) [φ t ↦ f t])
          ( fib
            ( ( t : ψ) → C (a t))
            ( ( t : φ) → C (a t))
            ( \ s t → s t)
            f)
          ( extension-type-weakening-map I ψ φ
            ( \ t → C (a t))
            f
          , is-equiv-extension-type-weakening I ψ φ
              ( \ t → C (a t))
              f)
          ( is-right-orthogonal-C a f))

#end is-right-orthogonal-iff-is-equiv-restrict-sections

```
