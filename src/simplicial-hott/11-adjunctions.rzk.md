# Adjunctions

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Transposing adjunctions

Transposing adjunctions are defined by opposing functors `#!rzk f : A → B` and
`#!rzk u : B → A` together with a family of "transposing equivalences" between
appropriate hom types.

```rzk title="RS17, Definition 11.1"
#def is-transposing-adj
  ( A B : U)
  ( f : A → B)
  ( u : B → A)
  : U
  := (a : A) → (b : B) → Equiv (hom B (f a) b) (hom A a (u b))

#def transposing-adj
  ( A B : U)
  : U
  := Σ (f : A → B), Σ (u : B → A), is-transposing-adj A B f u
```

A functor `#!rzk f : A → B` is a transposing left adjoint if it has a
transposing right adjoint. Later we will show that the type
`#!rzk is-transposing-ladj A B f` is a proposition when `#!rzk A` is Rezk and
`#!rzk B` is Segal.

```rzk
#def is-transposing-ladj
  ( A B : U)
  ( f : A → B)
  : U
  := Σ (u : B → A), is-transposing-adj A B f u

#def is-transposing-radj
  ( A B : U)
  ( u : B → A)
  : U
  := Σ (f : A → B), is-transposing-adj A B f u
```

## Quasi-diagrammatic adjunctions

Quasi-diagrammatic adjunctions are defined by opposing functors
`#!rzk f : A → B` and `#!rzk u : B → A`, unit and counit natural
transformations, and a pair of witnesses to the triangle identities.

```rzk title="RS17, Definition 11.2"
#def is-quasi-diagrammatic-adj
  ( A B : U)
  ( f : A → B)
  ( u : B → A)
  : U
  :=
    Σ (η : nat-trans A (\ _ → A) (identity A) (comp A B A u f)),
    Σ (ϵ : nat-trans B (\ _ → B) (comp B A B f u) (identity B)),
    product
      ( hom2 (B → A) u (triple-comp B A B A u f u) u
        ( prewhisker-nat-trans B A A u (identity A) (comp A B A u f) η )
        ( postwhisker-nat-trans B B A (comp B A B f u) (identity B) u ϵ )
        ( id-hom (B → A) u))
      ( hom2 (A → B) f (triple-comp A B A B f u f) f
        ( postwhisker-nat-trans A A B (identity A) (comp A B A u f) f η )
        ( prewhisker-nat-trans A B B f (comp B A B f u) (identity B) ϵ )
        ( id-hom (A → B) f))

#def quasi-diagrammatic-adj
  ( A B : U)
  : U
  := Σ (f : A → B), Σ (u : B → A), is-quasi-diagrammatic-adj A B f u
```

Quasi-diagrammatic adjunctions have left and right adjoints, but being the left
or right adjoint part of a quasi-diagrammatic adjunction is not a proposition.
Thus, we assign slightly different names to the following types.

```rzk
#def has-quasi-diagrammatic-radj
  ( A B : U)
  ( f : A → B)
  : U
  := Σ (u : B → A), is-quasi-diagrammatic-adj A B f u

#def has-quasi-diagrammatic-ladj
  ( A B : U)
  ( u : B → A)
  : U
  := Σ (f : A → B), is-quasi-diagrammatic-adj A B f u
```

The following projection functions extract the core data of a quasi-diagrammatic
adjunction.

```rzk
#def unit-is-quasi-diagrammatic-adj
  ( A B : U)
  ( f : A → B)
  ( u : B → A)
  ( is-quasi-diagrammatic-adj-fu : is-quasi-diagrammatic-adj A B f u)
  : nat-trans A (\ _ → A) (identity A) (comp A B A u f)
  := first (is-quasi-diagrammatic-adj-fu)

#def counit-is-quasi-diagrammatic-adj
  ( A B : U)
  ( f : A → B)
  ( u : B → A)
  ( is-quasi-diagrammatic-adj-fu : is-quasi-diagrammatic-adj A B f u)
  : nat-trans B (\ _ → B) (comp B A B f u) (identity B)
  := first (second (is-quasi-diagrammatic-adj-fu))

#def radj-triangle-is-quasi-diagrammatic-adj
  ( A B : U)
  ( f : A → B)
  ( u : B → A)
  ( is-quasi-diagrammatic-adj-fu : is-quasi-diagrammatic-adj A B f u)
  : hom2 (B → A) u (triple-comp B A B A u f u) u
    ( prewhisker-nat-trans B A A u (identity A) (comp A B A u f)
      ( unit-is-quasi-diagrammatic-adj A B f u is-quasi-diagrammatic-adj-fu))
    ( postwhisker-nat-trans B B A (comp B A B f u) (identity B) u
      ( counit-is-quasi-diagrammatic-adj A B f u is-quasi-diagrammatic-adj-fu))
    ( id-hom (B → A) u)
  := first (second (second (is-quasi-diagrammatic-adj-fu)))

#def ladj-triangle-is-quasi-diagrammatic-adj
  ( A B : U)
  ( f : A → B)
  ( u : B → A)
  ( is-quasi-diagrammatic-adj-fu : is-quasi-diagrammatic-adj A B f u)
  : hom2 (A → B) f (triple-comp A B A B f u f) f
    ( postwhisker-nat-trans A A B (identity A) (comp A B A u f) f
      ( unit-is-quasi-diagrammatic-adj A B f u is-quasi-diagrammatic-adj-fu))
    ( prewhisker-nat-trans A B B f (comp B A B f u) (identity B)
      ( counit-is-quasi-diagrammatic-adj A B f u is-quasi-diagrammatic-adj-fu))
    ( id-hom (A → B) f)
  := second (second (second (is-quasi-diagrammatic-adj-fu)))
```

## Half-adjoint diagrammatic adjunctions

A half-adjoint diagrammatic adjunction extends a quasi-diagrammatic adjunction
with higher coherence data that makes the specified witnesses to the triangle
identities coherent. This extra coherence data involves a pair of 3-simplices
belonging to a `#!rzk hom3` type we now define.

Unlike the convention used by the arguments of `#!rzk hom2`, we introduce the
boundary data of a 3-simplex in lexicographic order.

```rzk
#def hom3
  ( A : U)
  ( w x y z : A)
  ( f : hom A w x)
  ( gf : hom A w y)
  ( hgf : hom A w z)
  ( g : hom A x y)
  ( hg : hom A x z)
  ( h : hom A y z)
  ( α₃ : hom2 A w x y f g gf)
  ( α₂ : hom2 A w x z f hg hgf)
  ( α₁ : hom2 A w y z gf h hgf)
  ( α₀ : hom2 A x y z g h hg)
  : U
  :=
    ( ((t₁ , t₂ ) , t₃ ) : Δ³) →
    A [ t₃ ≡ 0₂ ↦ α₃ (t₁ , t₂ ),
        t₂ ≡ t₃ ↦ α₂ (t₁ , t₃ ),
        t₁ ≡ t₂ ↦ α₁ (t₁ , t₃ ),
        t₁ ≡ 1₂ ↦ α₀ (t₂ , t₃ )]
```

```rzk title="RS17, Definition 11.3"
#def is-half-adjoint-diagrammatic-adj
  ( A B : U)
  ( f : A → B)
  ( u : B → A)
  : U
  :=
    Σ ( (η , (ϵ , (α , β))) : is-quasi-diagrammatic-adj A B f u),
    Σ ( μ : hom2
            ( B → B)
            ( comp B A B f u)
            ( quadruple-comp B A B A B f u f u)
            ( identity B)
            ( whisker-nat-trans B A A B u (identity A) (comp A B A u f) f η)
            ( horizontal-comp-nat-trans B B B
              ( comp B A B f u) (identity B) (comp B A B f u) (identity B)
              ( ϵ) ( ϵ))
            ( ϵ)),
    product
    ( hom3 (B → B)
      ( comp B A B f u)
      ( quadruple-comp B A B A B f u f u)
      ( comp B A B f u)
      ( identity B)
      ( whisker-nat-trans B A A B u (identity A) (comp A B A u f) f η)
      ( id-hom (B → B) (comp B A B f u))
      ( ϵ)
      ( postwhisker-nat-trans B B B
        ( comp B A B f u) (identity B) (comp B A B f u) ϵ)
      ( horizontal-comp-nat-trans B B B
              ( comp B A B f u) (identity B) (comp B A B f u) (identity B)
              ( ϵ) ( ϵ))
      ( ϵ)
      ( \ t a → f (α t a))
      ( μ)
      ( id-comp-witness (B → B) (comp B A B f u) (identity B) ϵ)
      ( left-gray-interchanger-horizontal-comp-nat-trans B B B
        ( comp B A B f u) (identity B) ( comp B A B f u) (identity B)
        ( ϵ)
        ( ϵ)))
    ( hom3
      ( B → B)
      ( comp B A B f u)
      ( quadruple-comp B A B A B f u f u)
      ( comp B A B f u)
      ( identity B)
      ( whisker-nat-trans B A A B u (identity A) (comp A B A u f) f η)
      ( id-hom (B → B) (comp B A B f u))
      ( ϵ)
      ( prewhisker-nat-trans B B B
        ( comp B A B f u) (comp B A B f u) (identity B) ϵ)
      ( horizontal-comp-nat-trans B B B
              ( comp B A B f u) (identity B) (comp B A B f u) (identity B)
              ( ϵ) ( ϵ))
      ( ϵ)
      ( \ t b → β t (u b))
      ( μ)
      ( id-comp-witness (B → B) (comp B A B f u) (identity B) ϵ)
      ( right-gray-interchanger-horizontal-comp-nat-trans B B B
        ( comp B A B f u) (identity B) ( comp B A B f u) (identity B)
        ( ϵ)
        ( ϵ)))

#def half-adjoint-diagrammatic-adj
  ( A B : U)
  : U
  := Σ (f : A → B), Σ (u : B → A), is-half-adjoint-diagrammatic-adj A B f u

```

## Bi-diagrammatic adjunction

Bi-diagrammatic adjunctions are defined by opposing functors `#!rzk f : A → B`
and `#!rzk u : B → A`, a unit natural transformation `#! η`, two counit natural
transformations `#!rzk ϵ` and `#!rzk ϵ'`, and a pair of witnesses to the
triangle identities, one involving each counit.

```rzk title="RS17, Definition 11.6"
#def is-bi-diagrammatic-adj
  ( A B : U)
  ( f : A → B)
  ( u : B → A)
  : U
  :=
    Σ (η : nat-trans A (\ _ → A) (identity A) (comp A B A u f)),
    Σ (ϵ : nat-trans B (\ _ → B) (comp B A B f u) (identity B)),
    Σ (ϵ' : nat-trans B (\ _ → B) (comp B A B f u) (identity B)),
    product
      ( hom2 (B → A) u (triple-comp B A B A u f u) u
        ( prewhisker-nat-trans B A A u (identity A) (comp A B A u f) η )
        ( postwhisker-nat-trans B B A (comp B A B f u) (identity B) u ϵ )
        ( id-hom (B → A) u))
      ( hom2 (A → B) f (triple-comp A B A B f u f) f
        ( postwhisker-nat-trans A A B (identity A) (comp A B A u f) f η )
        ( prewhisker-nat-trans A B B f (comp B A B f u) (identity B) ϵ' )
        ( id-hom (A → B) f))

#def bi-diagrammatic-adj
  (A B : U)
  : U
  := Σ (f : A → B), Σ (u : B → A), is-bi-diagrammatic-adj A B f u

#def is-bi-diagrammatic-ladj
  ( A B : U)
  ( f : A → B)
  : U
  := Σ (u : B → A), is-bi-diagrammatic-adj A B f u

#def is-bi-diagrammatic-radj
  ( A B : U)
  ( u : B → A)
  : U
  := Σ (f : A → B), is-bi-diagrammatic-adj A B f u
```
