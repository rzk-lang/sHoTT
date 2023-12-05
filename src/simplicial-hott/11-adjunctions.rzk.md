# Adjunctions

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

Some of the definitions in this file rely on function extensionality:

```rzk
#assume funext : FunExt
#assume extext : ExtExt
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
  := Σ (f : A → B) , Σ (u : B → A) , is-transposing-adj A B f u
```

A functor `#!rzk f : A → B` is a transposing left adjoint if it has a
transposing right adjoint. Later we will show that the type
`#!rzk is-transposing-left-adj A B f` is a proposition when `#!rzk A` is Rezk
and `#!rzk B` is Segal.

```rzk
#def is-transposing-left-adj
  ( A B : U)
  ( f : A → B)
  : U
  := Σ (u : B → A) , is-transposing-adj A B f u

#def is-transposing-right-adj
  ( A B : U)
  ( u : B → A)
  : U
  := Σ (f : A → B) , is-transposing-adj A B f u
```

## Quasi-diagrammatic adjunctions

Quasi-diagrammatic adjunctions are defined by opposing functors
`#!rzk f : A → B` and `#!rzk u : B → A`, unit and counit natural
transformations, and a pair of witnesses to the triangle identities.

```rzk title="RS17, Definition 11.2"
#def has-quasi-diagrammatic-adj
  ( A B : U)
  ( f : A → B)
  ( u : B → A)
  : U
  :=
  Σ ( η : nat-trans A (\ _ → A) (identity A) (comp A B A u f))
  , Σ ( ϵ : nat-trans B (\ _ → B) (comp B A B f u) (identity B))
    , product
      ( hom2 (B → A) u (triple-comp B A B A u f u) u
        ( prewhisker-nat-trans B A A u (identity A) (comp A B A u f) η)
        ( postwhisker-nat-trans B B A (comp B A B f u) (identity B) u ϵ)
        ( id-hom (B → A) u))
      ( hom2 (A → B) f (triple-comp A B A B f u f) f
        ( postwhisker-nat-trans A A B (identity A) (comp A B A u f) f η)
        ( prewhisker-nat-trans A B B f (comp B A B f u) (identity B) ϵ)
        ( id-hom (A → B) f))

#def quasi-diagrammatic-adj
  ( A B : U)
  : U
  := Σ (f : A → B) , Σ (u : B → A) , has-quasi-diagrammatic-adj A B f u
```

Quasi-diagrammatic adjunctions have left and right adjoints, but being the left
or right adjoint part of a quasi-diagrammatic adjunction is not a proposition.
Thus, we assign slightly different names to the following types.

```rzk
#def has-quasi-diagrammatic-right-adj
  ( A B : U)
  ( f : A → B)
  : U
  := Σ (u : B → A) , has-quasi-diagrammatic-adj A B f u

#def has-quasi-diagrammatic-left-adj
  ( A B : U)
  ( u : B → A)
  : U
  := Σ (f : A → B) , has-quasi-diagrammatic-adj A B f u
```

The following projection functions extract the core data of a quasi-diagrammatic
adjunction.

```rzk
#def unit-has-quasi-diagrammatic-adj
  ( A B : U)
  ( f : A → B)
  ( u : B → A)
  ( has-quasi-diagrammatic-adj-fu : has-quasi-diagrammatic-adj A B f u)
  : nat-trans A (\ _ → A) (identity A) (comp A B A u f)
  := first (has-quasi-diagrammatic-adj-fu)

#def counit-has-quasi-diagrammatic-adj
  ( A B : U)
  ( f : A → B)
  ( u : B → A)
  ( has-quasi-diagrammatic-adj-fu : has-quasi-diagrammatic-adj A B f u)
  : nat-trans B (\ _ → B) (comp B A B f u) (identity B)
  := first (second (has-quasi-diagrammatic-adj-fu))

#def right-adj-triangle-has-quasi-diagrammatic-adj
  ( A B : U)
  ( f : A → B)
  ( u : B → A)
  ( has-quasi-diagrammatic-adj-fu : has-quasi-diagrammatic-adj A B f u)
  : hom2 (B → A) u (triple-comp B A B A u f u) u
    ( prewhisker-nat-trans B A A u (identity A) (comp A B A u f)
      ( unit-has-quasi-diagrammatic-adj A B f u
        ( has-quasi-diagrammatic-adj-fu)))
    ( postwhisker-nat-trans B B A (comp B A B f u) (identity B) u
      ( counit-has-quasi-diagrammatic-adj A B f u
        ( has-quasi-diagrammatic-adj-fu)))
    ( id-hom (B → A) u)
  := first (second (second (has-quasi-diagrammatic-adj-fu)))

#def left-adj-triangle-has-quasi-diagrammatic-adj
  ( A B : U)
  ( f : A → B)
  ( u : B → A)
  ( has-quasi-diagrammatic-adj-fu : has-quasi-diagrammatic-adj A B f u)
  : hom2 (A → B) f (triple-comp A B A B f u f) f
    ( postwhisker-nat-trans A A B (identity A) (comp A B A u f) f
      ( unit-has-quasi-diagrammatic-adj A B f u
        ( has-quasi-diagrammatic-adj-fu)))
    ( prewhisker-nat-trans A B B f (comp B A B f u) (identity B)
      ( counit-has-quasi-diagrammatic-adj A B f u
        ( has-quasi-diagrammatic-adj-fu)))
    ( id-hom (A → B) f)
  := second (second (second (has-quasi-diagrammatic-adj-fu)))
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
  ( ( ( t₁ , t₂) , t₃) : Δ³)
  → A [ t₃ ≡ 0₂ ↦ α₃ (t₁ , t₂)
      , t₂ ≡ t₃ ↦ α₂ (t₁ , t₃)
      , t₁ ≡ t₂ ↦ α₁ (t₁ , t₃)
      , t₁ ≡ 1₂ ↦ α₀ (t₂ , t₃)]
```

```rzk title="RS17, Definition 11.3"
#def is-half-adjoint-diagrammatic-adj
  ( A B : U)
  ( f : A → B)
  ( u : B → A)
  : U
  :=
  Σ ( ( η , (ϵ , (α , β))) : has-quasi-diagrammatic-adj A B f u)
  , Σ ( μ : hom2 (B → B)
            ( comp B A B f u)
            ( quadruple-comp B A B A B f u f u)
            ( identity B)
            ( whisker-nat-trans B A A B u (identity A) (comp A B A u f) f η)
            ( horizontal-comp-nat-trans B B B
              ( comp B A B f u) (identity B) (comp B A B f u) (identity B)
              ( ϵ) (ϵ))
            ( ϵ))
    , product
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
          ( comp B A B f u) (identity B) (comp B A B f u) (identity B) (ϵ) (ϵ))
        ( ϵ)
        ( \ t a → f (α t a))
        ( μ)
        ( id-comp-witness (B → B) (comp B A B f u) (identity B) ϵ)
        ( left-gray-interchanger-horizontal-comp-nat-trans B B B
          ( comp B A B f u) (identity B) (comp B A B f u) (identity B) (ϵ) (ϵ)))
      ( hom3 (B → B)
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
          ( comp B A B f u) (identity B) (comp B A B f u) (identity B) (ϵ) (ϵ))
        ( ϵ)
        ( \ t b → β t (u b))
        ( μ)
        ( id-comp-witness (B → B) (comp B A B f u) (identity B) ϵ)
        ( right-gray-interchanger-horizontal-comp-nat-trans B B B
          ( comp B A B f u) (identity B) (comp B A B f u) (identity B) (ϵ) (ϵ)))

#def half-adjoint-diagrammatic-adj
  ( A B : U)
  : U
  := Σ (f : A → B) , Σ (u : B → A) , is-half-adjoint-diagrammatic-adj A B f u
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
  Σ ( η : nat-trans A (\ _ → A) (identity A) (comp A B A u f))
  , Σ ( ϵ : nat-trans B (\ _ → B) (comp B A B f u) (identity B))
    , Σ ( ϵ' : nat-trans B (\ _ → B) (comp B A B f u) (identity B))
      , product
        ( hom2 (B → A) u (triple-comp B A B A u f u) u
          ( prewhisker-nat-trans B A A u (identity A) (comp A B A u f) η)
          ( postwhisker-nat-trans B B A (comp B A B f u) (identity B) u ϵ)
          ( id-hom (B → A) u))
        ( hom2 (A → B) f (triple-comp A B A B f u f) f
          ( postwhisker-nat-trans A A B (identity A) (comp A B A u f) f η)
          ( prewhisker-nat-trans A B B f (comp B A B f u) (identity B) ϵ')
          ( id-hom (A → B) f))

#def bi-diagrammatic-adj
  ( A B : U)
  : U
  := Σ (f : A → B) , Σ (u : B → A) , is-bi-diagrammatic-adj A B f u

#def is-bi-diagrammatic-left-adj
  ( A B : U)
  ( f : A → B)
  : U
  := Σ (u : B → A) , is-bi-diagrammatic-adj A B f u

#def is-bi-diagrammatic-right-adj
  ( A B : U)
  ( u : B → A)
  : U
  := Σ (f : A → B) , is-bi-diagrammatic-adj A B f u
```

## Quasi-transposing adjunction

Quasi-transposing adjunctions are defined by opposing functors `#!rzk f : A → B`
and `#!rzk u : B → A` together with a family of "transposing quasi-equivalences"
where "quasi-equivalence" is another name for "invertible map."

```rzk title="RS17, Definition 11.7"
#def has-quasi-transposing-adj
  ( A B : U)
  ( f : A → B)
  ( u : B → A)
  : U
  :=
  ( a : A)
  → ( b : B)
  → Σ ( ϕ : (hom B (f a) b) → (hom A a (u b)))
    , has-inverse (hom B (f a) b) (hom A a (u b)) ϕ

#def quasi-transposing-adj
  ( A B : U)
  : U
  := Σ (f : A → B) , Σ (u : B → A) , has-quasi-transposing-adj A B f u

#def has-quasi-transposing-right-adj
  ( A B : U)
  ( f : A → B)
  : U
  := Σ (u : B → A) , has-quasi-transposing-adj A B f u

#def has-quasi-transposing-left-adj
  ( A B : U)
  ( u : B → A)
  : U
  := Σ (f : A → B) , has-quasi-transposing-adj A B f u
```

## Equivalence of quasi-transposing and quasi-diagrammatic adjunctions

When `#!rzk A` and `#!rzk B` are Segal types, `#!rzk quasi-transposing-adj A B`
and `#!rzk quasi-diagrammatic-adj A B` are equivalent.

We first connect the components of the unit and counit to the transposition maps
in the usual way, as an application of the Yoneda lemma.

```rzk
#section unit-counit-transposition

#variables A B : U
#variable is-segal-A : is-segal A
#variable is-segal-B : is-segal B
#variable f : A → B
#variable u : B → A

#def equiv-transposition-unit-component uses (funext)
  ( a : A)
  : Equiv ((b : B) → (hom B (f a) b) → (hom A a (u b))) (hom A a (u (f a)))
  :=
  ( evid B (f a) (\ b → hom A a (u b))

  , yoneda-lemma funext B is-segal-B
    ( f a)
    ( \ b → hom A a (u b))
    ( is-covariant-substitution-is-covariant A B
      ( hom A a)
      ( is-covariant-representable-is-segal A is-segal-A a)
      ( u)))

#def equiv-unit-components
  : Equiv
    ( ( a : A) → hom A a (u (f a)))
    ( nat-trans A (\ _ → A) (identity A) (comp A B A u f))
  :=
  inv-equiv
  ( nat-trans A (\ _ → A) (identity A) (comp A B A u f))
  ( ( a : A) → hom A a (u (f a)))
  ( equiv-components-nat-trans A (\ _ → A)
    ( identity A)
    ( comp A B A u f))

#def equiv-transposition-unit uses (is-segal-A is-segal-B funext)
  : Equiv
    ( ( a : A) → (b : B) → (hom B (f a) b) → (hom A a (u b)))
    ( nat-trans A (\ _ → A) (identity A) (comp A B A u f))
  :=
  equiv-comp
  ( ( a : A) → (b : B) → (hom B (f a) b) → (hom A a (u b)))
  ( ( a : A) → hom A a (u (f a)))
  ( nat-trans A (\ _ → A) (identity A) (comp A B A u f))
  ( equiv-function-equiv-family funext A
    ( \ a → (b : B) → (hom B (f a) b) → (hom A a (u b)))
    ( \ a → hom A a (u (f a)))
    ( equiv-transposition-unit-component))
  ( equiv-unit-components)
```

We now reverse direction of the equivalence and extract the explicit map
defining the transposition function associated to a unit natural transformation.

```rzk
#def is-equiv-unit-component-transposition uses (funext)
  ( a : A)
  : is-equiv (hom A a (u (f a))) ((b : B) → (hom B (f a) b) → (hom A a (u b)))
    ( \ ηa b k →
      comp-is-segal A is-segal-A a (u (f a)) (u b) ηa (ap-hom B A u (f a) b k))
  :=
  inv-yoneda-lemma funext B is-segal-B
  ( f a)
  ( \ b → hom A a (u b))
  ( is-covariant-substitution-is-covariant A B
    ( hom A a)
    ( is-covariant-representable-is-segal A is-segal-A a)
    ( u))

#def is-equiv-unit-transposition uses (is-segal-A is-segal-B funext)
  : is-equiv
    ( nat-trans A (\ _ → A) (identity A) (comp A B A u f))
    ( ( a : A) → (b : B) → (hom B (f a) b) → (hom A a (u b)))
    ( \ η a b k →
      comp-is-segal A is-segal-A a (u (f a)) (u b)
      ( \ t → η t a)
      ( ap-hom B A u (f a) b k))
  :=
  is-equiv-comp
  ( nat-trans A (\ _ → A) (identity A) (comp A B A u f))
  ( ( a : A) → hom A a (u (f a)))
  ( ( a : A) → (b : B) → (hom B (f a) b) → (hom A a (u b)))
  ( ev-components-nat-trans A (\ _ → A) (identity A) (comp A B A u f))
  ( is-equiv-ev-components-nat-trans A (\ _ → A)(identity A)(comp A B A u f))
  ( \ η a b k →
    comp-is-segal A is-segal-A a (u (f a)) (u b)
    ( η a)
    ( ap-hom B A u (f a) b k))
  ( is-equiv-function-is-equiv-family funext A
    ( \ a → hom A a (u (f a)))
    ( \ a → (b : B) → (hom B (f a) b) → (hom A a (u b)))
    ( \ a ηa b k →
      comp-is-segal A is-segal-A a (u (f a)) (u b)
      ( ηa)
      ( ap-hom B A u (f a) b k))
    ( is-equiv-unit-component-transposition))
```

The results for counits are dual.

```rzk
#def equiv-transposition-counit-component uses (funext)
  ( b : B)
  : Equiv ((a : A) → (hom A a (u b)) → (hom B (f a) b)) (hom B (f (u b)) b)
  :=
  ( contra-evid A (u b) (\ a → hom B (f a) b)

  , contra-yoneda-lemma funext A is-segal-A
    ( u b)
    ( \ a → hom B (f a) b)
    ( is-contravariant-substitution-is-contravariant B A
      ( \ x → hom B x b)
      ( is-contravariant-representable-is-segal B is-segal-B b)
      ( f)))

#def equiv-counit-components
  : Equiv
    ( ( b : B) → hom B (f (u b)) b)
    ( nat-trans B (\ _ → B) (comp B A B f u) (identity B))
  :=
  inv-equiv
  ( nat-trans B (\ _ → B) (comp B A B f u) (identity B))
  ( ( b : B) → hom B (f (u b)) b)
  ( equiv-components-nat-trans B (\ _ → B)
    ( comp B A B f u)
    ( identity B))

#def equiv-transposition-counit uses (is-segal-A is-segal-B funext)
  : Equiv
    ( ( b : B) → (a : A) → (hom A a (u b)) → (hom B (f a) b))
    ( nat-trans B (\ _ → B) (comp B A B f u) (identity B))
  :=
  equiv-comp
  ( ( b : B) → (a : A) → (hom A a (u b)) → (hom B (f a) b))
  ( ( b : B) → hom B (f (u b)) b)
  ( nat-trans B (\ _ → B) (comp B A B f u) (identity B))
  ( equiv-function-equiv-family funext B
    ( \ b → (a : A) → (hom A a (u b)) → (hom B (f a) b))
    ( \ b → hom B (f (u b)) b)
    ( equiv-transposition-counit-component))
  ( equiv-counit-components)
```

We again reverse direction of the equivalence and extract the explicit map
defining the transposition function associated to a counit natural
transformation.

```rzk
#def is-equiv-counit-component-transposition uses (funext)
  ( b : B)
  : is-equiv (hom B (f (u b)) b)
    ( ( a : A) → (hom A a (u b)) → (hom B (f a) b))
    ( \ ϵb a k →
      comp-is-segal B is-segal-B (f a) (f (u b)) b (ap-hom A B f a (u b) k) ϵb)
  :=
  inv-contra-yoneda-lemma funext A is-segal-A
  ( u b)
  ( \ a → hom B (f a) b)
  ( is-contravariant-substitution-is-contravariant B A
    ( \ z → hom B z b)
    ( is-contravariant-representable-is-segal B is-segal-B b)
    ( f))

#def is-equiv-counit-transposition uses (is-segal-A is-segal-B funext)
  : is-equiv
    ( nat-trans B (\ _ → B) (comp B A B f u) (identity B))
    ( ( b : B) → (a : A) → (hom A a (u b)) → (hom B (f a) b))
    ( \ ϵ b a k →
      comp-is-segal B is-segal-B (f a) (f (u b)) b
      ( ap-hom A B f a (u b) k)
      ( \ t → ϵ t b))
  :=
  is-equiv-comp
  ( nat-trans B (\ _ → B) (comp B A B f u) (identity B))
  ( ( b : B) → hom B (f (u b)) b)
  ( ( b : B) → (a : A) → (hom A a (u b)) → (hom B (f a) b))
  ( ev-components-nat-trans B (\ _ → B) (comp B A B f u) (identity B))
  ( is-equiv-ev-components-nat-trans B (\ _ → B)(comp B A B f u) (identity B))
  ( \ ϵ b a k →
    comp-is-segal B is-segal-B (f a) (f (u b)) b
    ( ap-hom A B f a (u b) k)
    ( ϵ b))
  ( is-equiv-function-is-equiv-family funext B
    ( \ b → hom B (f (u b)) b)
    ( \ b → (a : A) → (hom A a (u b)) → (hom B (f a) b))
    ( \ b ϵb a k →
      comp-is-segal B is-segal-B (f a) (f (u b)) b
      ( ap-hom A B f a (u b) k)
      ( ϵb))
    ( is-equiv-counit-component-transposition))

#end unit-counit-transposition
```

We next connect the triangle identity witnesses to the usual triangle identities
as an application of the dependent Yoneda lemma.

```rzk
#section triangle-identities

#variables A B : U
#variable is-segal-A : is-segal A
#variable is-segal-B : is-segal B
#variable f : A → B
#variable u : B → A
#variable η : nat-trans A (\ _ → A) (identity A) (comp A B A u f)
#variable ϵ : nat-trans B (\ _ → B) (comp B A B f u) (identity B)

#def equiv-radj-triangle uses (funext)
  : Equiv
    ( hom2 (B → A) u (triple-comp B A B A u f u) u
      ( prewhisker-nat-trans B A A u (identity A) (comp A B A u f) η)
      ( postwhisker-nat-trans B B A (comp B A B f u) (identity B) u ϵ)
      ( id-hom (B → A) u))
    ( ( comp-is-segal
        ( B → A)
        ( is-segal-function-type
          ( funext)
          ( B)
          ( \ _ → A)
          ( \ _ → is-segal-A))
        ( u)
        ( triple-comp B A B A u f u)
        ( u)
        ( prewhisker-nat-trans B A A u (identity A) (comp A B A u f) η)
        ( postwhisker-nat-trans B B A (comp B A B f u) (identity B) u ϵ))

    = ( id-hom (B → A) u))
  :=
  inv-equiv
  ( ( comp-is-segal
      ( B → A)
      ( is-segal-function-type funext B (\ _ → A) (\ _ → is-segal-A))
      ( u) (triple-comp B A B A u f u) (u)
      ( prewhisker-nat-trans B A A u (identity A) (comp A B A u f) η)
      ( postwhisker-nat-trans B B A (comp B A B f u) (identity B) u ϵ))
  = ( id-hom (B → A) u))
  ( hom2 (B → A) u (triple-comp B A B A u f u) u
    ( prewhisker-nat-trans B A A u (identity A) (comp A B A u f) η)
    ( postwhisker-nat-trans B B A (comp B A B f u) (identity B) u ϵ)
    ( id-hom (B → A) u))
  ( equiv-hom2-eq-comp-is-segal
    ( B → A)
    ( is-segal-function-type funext B (\ _ → A) (\ _ → is-segal-A))
    ( u) (triple-comp B A B A u f u) (u)
    ( prewhisker-nat-trans B A A u (identity A) (comp A B A u f) η)
    ( postwhisker-nat-trans B B A (comp B A B f u) (identity B) u ϵ)
    ( id-hom (B → A) u))

#def equiv-ev-components-radj-triangle
  : Equiv
    ( ( comp-is-segal
        ( B → A)
        ( is-segal-function-type
          ( funext)
          ( B)
          ( \ _ → A)
          ( \ _ → is-segal-A))
        ( u)
        ( triple-comp B A B A u f u)
        ( u)
        ( prewhisker-nat-trans B A A u (identity A) (comp A B A u f) η)
        ( postwhisker-nat-trans B B A (comp B A B f u) (identity B) u ϵ))

    = ( id-hom (B → A) u))
    ( ( ev-components-nat-trans B (\ _ → A) u u
        ( comp-is-segal
          ( B → A)
          ( is-segal-function-type
            ( funext)
            ( B)
            ( \ _ → A)
            ( \ _ → is-segal-A))
          ( u)
          ( triple-comp B A B A u f u)
          ( u)
          ( prewhisker-nat-trans B A A u (identity A) (comp A B A u f) η)
          ( postwhisker-nat-trans B B A (comp B A B f u) (identity B) u ϵ)))

    = ( \ b → id-hom A (u b)))
  :=
  equiv-ap-is-equiv
  ( nat-trans B (\ _ → A) u u)
  ( nat-trans-components B (\ _ → A) u u)
  ( ev-components-nat-trans B (\ _ → A) u u)
  ( is-equiv-ev-components-nat-trans B (\ _ → A) u u)
  ( comp-is-segal (B → A)
    ( is-segal-function-type funext B (\ _ → A) (\ _ → is-segal-A))
    ( u) (triple-comp B A B A u f u) (u)
    ( prewhisker-nat-trans B A A u (identity A) (comp A B A u f) η)
    ( postwhisker-nat-trans B B A (comp B A B f u) (identity B) u ϵ))
  ( id-hom (B → A) u)

#def equiv-components-radj-triangle-funext uses (funext)
  : Equiv
    ( ev-components-nat-trans B (\ _ → A) u u
      ( comp-is-segal (B → A)
        ( is-segal-function-type funext B (\ _ → A) (\ _ → is-segal-A))
        ( u) (triple-comp B A B A u f u) (u)
        ( prewhisker-nat-trans B A A u (identity A) (comp A B A u f) η)
        ( postwhisker-nat-trans B B A (comp B A B f u) (identity B) u ϵ))

    = ( \ b → id-hom A (u b)))
    ( ( b : B)
    → ( ev-components-nat-trans B (\ _ → A) u u
        ( comp-is-segal (B → A)
          ( is-segal-function-type funext B (\ _ → A) (\ _ → is-segal-A))
          ( u) (triple-comp B A B A u f u) (u)
          ( prewhisker-nat-trans B A A u (identity A) (comp A B A u f) η)
          ( postwhisker-nat-trans B B A (comp B A B f u) (identity B) u ϵ))
        ( b)

      = id-hom A (u b)))
  :=
  equiv-FunExt funext B
  ( \ b → (hom A (u b) (u b)))
  ( ev-components-nat-trans B (\ _ → A) u u
    ( comp-is-segal (B → A)
      ( is-segal-function-type funext B (\ _ → A) (\ _ → is-segal-A))
      ( u) (triple-comp B A B A u f u) (u)
      ( prewhisker-nat-trans B A A u (identity A) (comp A B A u f) η)
      ( postwhisker-nat-trans B B A (comp B A B f u) (identity B) u ϵ)))
  ( \ b → id-hom A (u b))

#def eq-ladj-triangle-comp-components-comp-nat-trans-is-segal uses (funext)
  ( b : B)
  : comp-is-segal A is-segal-A (u b) (u (f (u b))) (u b)
    ( \ t → η t (u b))
    ( ap-hom B A u (f (u b)) b (\ t → ϵ t b))

  = ev-components-nat-trans B (\ _ → A) u u
    ( comp-is-segal (B → A)
      ( is-segal-function-type (funext) (B) (\ _ → A) (\ _ → is-segal-A))
      ( u) (triple-comp B A B A u f u) (u)
      ( prewhisker-nat-trans B A A u (identity A) (comp A B A u f) η)
      ( postwhisker-nat-trans B B A (comp B A B f u) (identity B) u ϵ))
    ( b)
  :=
  comp-components-comp-nat-trans-is-segal funext B (\ _ → A) (\ _ → is-segal-A)
  ( u) (triple-comp B A B A u f u) (u)
  ( prewhisker-nat-trans B A A u (identity A) (comp A B A u f) η)
  ( postwhisker-nat-trans B B A (comp B A B f u) (identity B) u ϵ)
  ( b)

#def equiv-preconcat-radj-triangle uses (funext)
  ( b : B)
  : Equiv
    ( ev-components-nat-trans B (\ _ → A) u u
      ( comp-is-segal (B → A)
        ( is-segal-function-type funext B (\ _ → A) (\ _ → is-segal-A))
        ( u) (triple-comp B A B A u f u) (u)
        ( prewhisker-nat-trans B A A u (identity A) (comp A B A u f) η)
        ( postwhisker-nat-trans B B A (comp B A B f u) (identity B) u ϵ))
      ( b)

    = id-hom A (u b))
    ( ( comp-is-segal A is-segal-A (u b) (u (f (u b))) (u b)
        ( \ t → η t (u b))
        ( ap-hom B A u (f (u b)) b (\ t → ϵ t b)))

    = ( id-hom A (u b)))
  :=
  equiv-preconcat (hom A (u b) (u b))
  ( comp-is-segal A is-segal-A (u b) (u (f (u b))) (u b)
    ( \ t → η t (u b))
    ( ap-hom B A u (f (u b)) b (\ t → ϵ t b)))
  ( ev-components-nat-trans B (\ _ → A) u u
    ( comp-is-segal (B → A)
      ( is-segal-function-type (funext) (B) (\ _ → A) (\ _ → is-segal-A))
      ( u) (triple-comp B A B A u f u) (u)
      ( prewhisker-nat-trans B A A u (identity A) (comp A B A u f) η)
      ( postwhisker-nat-trans B B A (comp B A B f u) (identity B) u ϵ))
    ( b))
  ( id-hom A (u b))
  ( eq-ladj-triangle-comp-components-comp-nat-trans-is-segal b)

#def equiv-component-comp-segal-comp-radj-triangle uses (funext)
  : Equiv
    ( comp-is-segal (B → A)
      ( is-segal-function-type funext B (\ _ → A) (\ _ → is-segal-A))
      ( u) (triple-comp B A B A u f u) (u)
      ( prewhisker-nat-trans B A A u (identity A) (comp A B A u f) η)
      ( postwhisker-nat-trans B B A (comp B A B f u) (identity B) u ϵ)

    = id-hom (B → A) u)
    ( ( b : B)
    → ( comp-is-segal A is-segal-A (u b) (u (f (u b))) (u b)
        ( \ t → η t (u b))
        ( ap-hom B A u (f (u b)) b (\ t → ϵ t b)))

    = ( id-hom A (u b)))
  :=
  equiv-triple-comp
  ( ( comp-is-segal (B → A)
      ( is-segal-function-type funext B (\ _ → A) (\ _ → is-segal-A))
      ( u) (triple-comp B A B A u f u) (u)
      ( prewhisker-nat-trans B A A u (identity A) (comp A B A u f) η)
      ( postwhisker-nat-trans B B A (comp B A B f u) (identity B) u ϵ))
  = ( id-hom (B → A) u))
  ( ( ev-components-nat-trans B (\ _ → A) u u
      ( comp-is-segal (B → A)
        ( is-segal-function-type funext B (\ _ → A) (\ _ → is-segal-A))
        ( u) (triple-comp B A B A u f u) (u)
        ( prewhisker-nat-trans B A A u (identity A) (comp A B A u f) η)
        ( postwhisker-nat-trans B B A (comp B A B f u) (identity B) u ϵ)))

  = ( \ b → id-hom A (u b)))
  ( ( b : B)
    → ( ( ev-components-nat-trans B (\ _ → A) u u
          ( comp-is-segal (B → A)
            ( is-segal-function-type funext B (\ _ → A) (\ _ → is-segal-A))
            ( u) (triple-comp B A B A u f u) (u)
            ( prewhisker-nat-trans B A A u (identity A) (comp A B A u f) η)
            ( postwhisker-nat-trans B B A (comp B A B f u) (identity B) u ϵ))
          ( b))

      = ( id-hom A (u b))))
  ( ( b : B)
    → ( comp-is-segal A is-segal-A (u b) (u (f (u b))) (u b)
        ( \ t → η t (u b))
        ( ap-hom B A u (f (u b)) b (\ t → ϵ t b)))

    = ( id-hom A (u b)))
  ( equiv-ev-components-radj-triangle)
  ( equiv-components-radj-triangle-funext)
  ( equiv-function-equiv-family funext B
    ( \ b →
      ( ev-components-nat-trans B (\ _ → A) u u
        ( comp-is-segal (B → A)
          ( is-segal-function-type funext B (\ _ → A) (\ _ → is-segal-A))
          ( u) (triple-comp B A B A u f u) (u)
          ( prewhisker-nat-trans B A A u (identity A) (comp A B A u f) η)
          ( postwhisker-nat-trans B B A (comp B A B f u) (identity B) u ϵ))
        ( b))

    = ( id-hom A (u b)))
    ( \ b →
      ( comp-is-segal A is-segal-A (u b) (u (f (u b))) (u b)
        ( \ t → η t (u b))
        ( ap-hom B A u (f (u b)) b (\ t → ϵ t b)))

    = ( id-hom A (u b)))
    ( equiv-preconcat-radj-triangle))
```

We finally arrive at the desired equivalence.

```rzk
#def equiv-components-radj-triangle uses (funext)
  : Equiv
    ( hom2 (B → A) u (triple-comp B A B A u f u) u
      ( prewhisker-nat-trans B A A u (identity A) (comp A B A u f) η)
      ( postwhisker-nat-trans B B A (comp B A B f u) (identity B) u ϵ)
      ( id-hom (B → A) u))
    ( ( b : B)
      → ( comp-is-segal A is-segal-A (u b) (u (f (u b))) (u b)
          ( \ t → η t (u b))
          ( ap-hom B A u (f (u b)) b (\ t → ϵ t b)))
      = ( id-hom A (u b)))
  :=
  equiv-comp
  ( hom2 (B → A) u (triple-comp B A B A u f u) u
    ( prewhisker-nat-trans B A A u (identity A) (comp A B A u f) η)
    ( postwhisker-nat-trans B B A (comp B A B f u) (identity B) u ϵ)
    ( id-hom (B → A) u))
  ( ( comp-is-segal (B → A)
      ( is-segal-function-type funext B (\ _ → A) (\ _ → is-segal-A))
      ( u) (triple-comp B A B A u f u) (u)
      ( prewhisker-nat-trans B A A u (identity A) (comp A B A u f) η)
      ( postwhisker-nat-trans B B A (comp B A B f u) (identity B) u ϵ))

  = ( id-hom (B → A) u))
  ( ( b : B)
    → ( comp-is-segal A is-segal-A (u b) (u (f (u b))) (u b)
        ( \ t → η t (u b))
        ( ap-hom B A u (f (u b)) b (\ t → ϵ t b)))

    = ( id-hom A (u b)))
  ( equiv-radj-triangle)
  ( equiv-component-comp-segal-comp-radj-triangle)
```

The calculation for the other triangle identity is dual.

```rzk
#def equiv-ladj-triangle uses (funext)
  : Equiv
    ( hom2 (A → B) f (triple-comp A B A B f u f) f
      ( postwhisker-nat-trans A A B (identity A) (comp A B A u f) f η)
      ( prewhisker-nat-trans A B B f (comp B A B f u) (identity B) ϵ)
      ( id-hom (A → B) f))
    ( comp-is-segal (A → B)
      ( is-segal-function-type funext A (\ _ → B) (\ _ → is-segal-B))
      ( f) (triple-comp A B A B f u f) (f)
      ( postwhisker-nat-trans A A B (identity A) (comp A B A u f) f η)
      ( prewhisker-nat-trans A B B f (comp B A B f u) (identity B) ϵ)

    = id-hom (A → B) f)
  :=
  inv-equiv
  ( comp-is-segal (A → B)
    ( is-segal-function-type funext A (\ _ → B) (\ _ → is-segal-B))
    ( f) (triple-comp A B A B f u f) (f)
    ( postwhisker-nat-trans A A B (identity A) (comp A B A u f) f η)
    ( prewhisker-nat-trans A B B f (comp B A B f u) (identity B) ϵ)

  = id-hom (A → B) f)
  ( hom2 (A → B) f (triple-comp A B A B f u f) f
    ( postwhisker-nat-trans A A B (identity A) (comp A B A u f) f η)
    ( prewhisker-nat-trans A B B f (comp B A B f u) (identity B) ϵ)
    ( id-hom (A → B) f))
  ( equiv-hom2-eq-comp-is-segal (A → B)
    ( is-segal-function-type funext A (\ _ → B) (\ _ → is-segal-B))
    ( f) (triple-comp A B A B f u f) (f)
    ( postwhisker-nat-trans A A B (identity A) (comp A B A u f) f η)
    ( prewhisker-nat-trans A B B f (comp B A B f u) (identity B) ϵ)
    ( id-hom (A → B) f))

#def equiv-ev-components-ladj-triangle
  : Equiv
    ( comp-is-segal (A → B)
      ( is-segal-function-type funext A (\ _ → B) (\ _ → is-segal-B))
      ( f) (triple-comp A B A B f u f) (f)
      ( postwhisker-nat-trans A A B (identity A) (comp A B A u f) f η)
      ( prewhisker-nat-trans A B B f (comp B A B f u) (identity B) ϵ)

    = id-hom (A → B) f)
    ( ev-components-nat-trans A (\ _ → B) f f
      ( comp-is-segal (A → B)
        ( is-segal-function-type funext A (\ _ → B) (\ _ → is-segal-B))
        ( f) (triple-comp A B A B f u f) (f)
        ( postwhisker-nat-trans A A B (identity A) (comp A B A u f) f η)
        ( prewhisker-nat-trans A B B f (comp B A B f u) (identity B) ϵ))

    = ( \ a → id-hom B (f a)))
  :=
  equiv-ap-is-equiv
  ( nat-trans A (\ _ → B) f f)
  ( nat-trans-components A (\ _ → B) f f)
  ( ev-components-nat-trans A (\ _ → B) f f)
  ( is-equiv-ev-components-nat-trans A (\ _ → B) f f)
  ( comp-is-segal (A → B)
    ( is-segal-function-type funext A (\ _ → B) (\ _ → is-segal-B))
    ( f) (triple-comp A B A B f u f) (f)
    ( postwhisker-nat-trans A A B (identity A) (comp A B A u f) f η)
    ( prewhisker-nat-trans A B B f (comp B A B f u) (identity B) ϵ))
  ( id-hom (A → B) f)

#def equiv-components-ladj-triangle-funext uses (funext)
  : Equiv
    ( ev-components-nat-trans A (\ _ → B) f f
      ( comp-is-segal (A → B)
        ( is-segal-function-type funext A (\ _ → B) (\ _ → is-segal-B))
        ( f) (triple-comp A B A B f u f) (f)
        ( postwhisker-nat-trans A A B (identity A) (comp A B A u f) f η)
        ( prewhisker-nat-trans A B B f (comp B A B f u) (identity B) ϵ))

    = ( \ a → id-hom B (f a)))
    ( ( a : A)
      → ( ev-components-nat-trans A (\ _ → B) f f
          ( comp-is-segal (A → B)
            ( is-segal-function-type funext A (\ _ → B) (\ _ → is-segal-B))
            ( f) (triple-comp A B A B f u f) (f)
            ( postwhisker-nat-trans A A B (identity A) (comp A B A u f) f η)
            ( prewhisker-nat-trans A B B f (comp B A B f u) (identity B) ϵ))
          ( a)

      = id-hom B (f a)))
  :=
  equiv-FunExt funext A
  ( \ a → (hom B (f a) (f a)))
  ( ev-components-nat-trans A (\ _ → B) f f
    ( comp-is-segal (A → B)
      ( is-segal-function-type funext A (\ _ → B) (\ _ → is-segal-B))
      ( f) (triple-comp A B A B f u f) (f)
      ( postwhisker-nat-trans A A B (identity A) (comp A B A u f) f η)
      ( prewhisker-nat-trans A B B f (comp B A B f u) (identity B) ϵ)))
  ( \ a → id-hom B (f a))

#def eq-radj-triangle-comp-components-comp-nat-trans-is-segal uses (funext)
  ( a : A)
  : ( comp-is-segal B is-segal-B (f a) (f (u (f a))) (f a)
      ( ap-hom A B f a (u (f a)) (\ t → η t a))
      ( \ t → ϵ t (f a)))
  = ( ev-components-nat-trans A (\ _ → B) f f
      ( comp-is-segal
        ( A → B)
        ( is-segal-function-type (funext) (A) (\ _ → B) (\ _ → is-segal-B))
        ( f)
        ( triple-comp A B A B f u f)
        ( f)
        ( postwhisker-nat-trans A A B (identity A) (comp A B A u f) f η)
        ( prewhisker-nat-trans A B B f (comp B A B f u) (identity B) ϵ))
      ( a))
  :=
    comp-components-comp-nat-trans-is-segal
    ( funext)
    ( A)
    ( \ _ → B)
    ( \ _ → is-segal-B)
    ( f)
    ( triple-comp A B A B f u f)
    ( f)
    ( postwhisker-nat-trans A A B (identity A) (comp A B A u f) f η)
    ( prewhisker-nat-trans A B B f (comp B A B f u) (identity B) ϵ)
    ( a)

#def equiv-preconcat-ladj-triangle uses (funext)
  ( a : A)
  : Equiv
    ( ev-components-nat-trans A (\ _ → B) f f
      ( comp-is-segal (A → B)
        ( is-segal-function-type funext A (\ _ → B) (\ _ → is-segal-B))
        ( f) (triple-comp A B A B f u f) (f)
        ( postwhisker-nat-trans A A B (identity A) (comp A B A u f) f η)
        ( prewhisker-nat-trans A B B f (comp B A B f u) (identity B) ϵ))
      ( a)

    = id-hom B (f a))
    ( comp-is-segal B is-segal-B (f a) (f (u (f a))) (f a)
      ( ap-hom A B f a (u (f a)) (\ t → η t a))
      ( \ t → ϵ t (f a))

    = id-hom B (f a))
  :=
  equiv-preconcat (hom B (f a) (f a))
  ( comp-is-segal B is-segal-B (f a) (f (u (f a))) (f a)
    ( ap-hom A B f a (u (f a)) (\ t → η t a))
    ( \ t → ϵ t (f a)))
  ( ev-components-nat-trans A (\ _ → B) f f
    ( comp-is-segal (A → B)
      ( is-segal-function-type funext A (\ _ → B) (\ _ → is-segal-B))
      ( f) (triple-comp A B A B f u f) (f)
      ( postwhisker-nat-trans A A B (identity A) (comp A B A u f) f η)
      ( prewhisker-nat-trans A B B f (comp B A B f u) (identity B) ϵ))
    ( a))
  ( id-hom B (f a))
  ( eq-radj-triangle-comp-components-comp-nat-trans-is-segal a)

#def equiv-component-comp-segal-comp-ladj-triangle uses (funext)
  : Equiv
    ( comp-is-segal (A → B)
      ( is-segal-function-type funext A (\ _ → B) (\ _ → is-segal-B))
      ( f) (triple-comp A B A B f u f) (f)
      ( postwhisker-nat-trans A A B (identity A) (comp A B A u f) f η)
      ( prewhisker-nat-trans A B B f (comp B A B f u) (identity B) ϵ)

    = id-hom (A → B) f)
    ( ( a : A)
      → comp-is-segal B is-segal-B (f a) (f (u (f a))) (f a)
        ( ap-hom A B f a (u (f a)) (\ t → η t a))
        ( \ t → ϵ t (f a))

      = id-hom B (f a))
  :=
  equiv-triple-comp
  ( comp-is-segal (A → B)
    ( is-segal-function-type funext A (\ _ → B) (\ _ → is-segal-B))
    ( f) (triple-comp A B A B f u f) (f)
    ( postwhisker-nat-trans A A B (identity A) (comp A B A u f) f η)
    ( prewhisker-nat-trans A B B f (comp B A B f u) (identity B) ϵ)

  = id-hom (A → B) f)
  ( ( ev-components-nat-trans A (\ _ → B) f f
      ( comp-is-segal (A → B)
        ( is-segal-function-type funext A (\ _ → B) (\ _ → is-segal-B))
        ( f) (triple-comp A B A B f u f) (f)
        ( postwhisker-nat-trans A A B (identity A) (comp A B A u f) f η)
        ( prewhisker-nat-trans A B B f (comp B A B f u) (identity B) ϵ)))

  = ( \ a → id-hom B (f a)))
  ( ( a : A)
    → ( ev-components-nat-trans A (\ _ → B) f f
        ( comp-is-segal (A → B)
          ( is-segal-function-type funext A (\ _ → B) (\ _ → is-segal-B))
          ( f) (triple-comp A B A B f u f) (f)
          ( postwhisker-nat-trans A A B (identity A) (comp A B A u f) f η)            (prewhisker-nat-trans A B B f (comp B A B f u) (identity B) ϵ))
        ( a)

      = id-hom B (f a)))
    ( ( a : A)
      → comp-is-segal B is-segal-B (f a) (f (u (f a))) (f a)
        ( ap-hom A B f a (u (f a)) (\ t → η t a))
        ( \ t → ϵ t (f a))

      = id-hom B (f a))
    ( equiv-ev-components-ladj-triangle)
    ( equiv-components-ladj-triangle-funext)
    ( equiv-function-equiv-family funext A
      ( \ a →
        ev-components-nat-trans A (\ _ → B) f f
        ( comp-is-segal (A → B)
          ( is-segal-function-type funext A (\ _ → B) (\ _ → is-segal-B))
          ( f) (triple-comp A B A B f u f) (f)
          ( postwhisker-nat-trans A A B (identity A) (comp A B A u f) f η)            (prewhisker-nat-trans A B B f (comp B A B f u) (identity B) ϵ))
        ( a)

      = id-hom B (f a))
      ( \ a →
        comp-is-segal B is-segal-B (f a) (f (u (f a))) (f a)
          ( ap-hom A B f a (u (f a)) (\ t → η t a))
          ( \ t → ϵ t (f a))

      = id-hom B (f a))
      ( equiv-preconcat-ladj-triangle))

#def equiv-components-ladj-triangle uses (funext)
  : Equiv
    ( hom2 (A → B) f (triple-comp A B A B f u f) f
        ( postwhisker-nat-trans A A B (identity A) (comp A B A u f) f η)
        ( prewhisker-nat-trans A B B f (comp B A B f u) (identity B) ϵ)
        ( id-hom (A → B) f))
    ( ( a : A)
      → comp-is-segal B is-segal-B (f a) (f (u (f a))) (f a)
        ( ap-hom A B f a (u (f a)) (\ t → η t a))
        ( \ t → ϵ t (f a))

      = id-hom B (f a))
  :=
  equiv-comp
  ( hom2 (A → B) f (triple-comp A B A B f u f) f
    ( postwhisker-nat-trans A A B (identity A) (comp A B A u f) f η)
    ( prewhisker-nat-trans A B B f (comp B A B f u) (identity B) ϵ)
    ( id-hom (A → B) f))
  ( comp-is-segal (A → B)
    ( is-segal-function-type funext A (\ _ → B) (\ _ → is-segal-B))
    ( f) (triple-comp A B A B f u f) (f)
    ( postwhisker-nat-trans A A B (identity A) (comp A B A u f) f η)
    ( prewhisker-nat-trans A B B f (comp B A B f u) (identity B) ϵ)

  = id-hom (A → B) f)
  ( ( a : A)
    → comp-is-segal B is-segal-B (f a) (f (u (f a))) (f a)
      ( ap-hom A B f a (u (f a)) (\ t → η t a))
      ( \ t → ϵ t (f a))

    = id-hom B (f a))
  ( equiv-ladj-triangle)
  ( equiv-component-comp-segal-comp-ladj-triangle)

#end triangle-identities
```

## Adjunctions between Rezk types

Given a functor `#!rzk u : B → A` from a Rezk type to a Segal type, we show that
the type given by functors `#!rzk f : A → B` and unit transformations that
induce a transposing equivalence is a proposition. This data is nearly the data
of `#!rzk is-transposing-right-adj A B u`

```rzk
#section all-unit-arrows-equal-is-rezk-is-segal

#variables B A : U
#variable is-rezk-B : is-rezk B
#variable is-segal-A : is-segal A
#variable u : B → A
#variable a : A
#variables fa fa' : B
#variable ηa : hom A a (u fa)
#variable ηa' : hom A a (u fa')

#def ηa-transposition
  ( b : B)
  ( k : hom B fa b)
  : ( hom A a (u b))
  := comp-is-segal A is-segal-A a (u fa) (u b) ηa (ap-hom B A u fa b k)

#def ηa'-transposition
  ( b : B)
  ( k : hom B fa' b)
  : ( hom A a (u b))
  := comp-is-segal A is-segal-A a (u fa') (u b) ηa' (ap-hom B A u fa' b k)

#variable ω
 : ( b : B) → is-equiv (hom B fa b) (hom A a (u b)) (ηa-transposition b)

#variable ω'
 : ( b : B) → is-equiv (hom B fa' b) (hom A a (u b)) (ηa'-transposition b)

#def to-left-adjoint-components-is-rezk-is-segal uses (A is-segal-A u a ηa)
  : hom B fa fa'
  :=
  section-is-equiv (hom B fa fa') (hom A a (u fa'))
  ( ηa-transposition fa') (ω fa')
  ( ηa')

#def triangle-to-left-adjoint-components-is-rezk-is-segal
  : comp-is-segal A is-segal-A a (u fa) (u fa')
    ( ηa)
    ( ap-hom B A u fa fa' to-left-adjoint-components-is-rezk-is-segal)

  = ηa'
  :=
  ( second
    ( has-section-is-equiv (hom B fa fa') (hom A a (u fa'))
      ( ηa-transposition fa') (ω fa')))
  ( ηa')

#def from-left-adjoint-components-is-rezk-is-segal uses (A is-segal-A u a ηa')
  : hom B fa' fa
  :=
  section-is-equiv (hom B fa' fa) (hom A a (u fa))
  ( ηa'-transposition fa) (ω' fa)
  ( ηa)

#def triangle-from-left-adjoint-components-is-rezk-is-segal
  : comp-is-segal A is-segal-A a (u fa') (u fa)
    ( ηa')
    ( ap-hom B A u fa' fa from-left-adjoint-components-is-rezk-is-segal)

  = ηa
  :=
  ( second
    ( has-section-is-equiv (hom B fa' fa) (hom A a (u fa))
      ( ηa'-transposition fa) (ω' fa)))
  ( ηa)

#def ηa-automorphism uses (extext ω ω')
  : comp-is-segal A is-segal-A a (u fa) (u fa)
    ( ηa)
    ( ap-hom B A u fa fa
      ( comp-is-segal B (first is-rezk-B) fa fa' fa
        ( to-left-adjoint-components-is-rezk-is-segal)
        ( from-left-adjoint-components-is-rezk-is-segal)))

  = ηa
  :=
  quadruple-concat (hom A a (u fa))
  ( comp-is-segal A is-segal-A a (u fa) (u fa)
    ( ηa)
    ( ap-hom B A u fa fa
      ( comp-is-segal B (first is-rezk-B) fa fa' fa
        ( to-left-adjoint-components-is-rezk-is-segal)
        ( from-left-adjoint-components-is-rezk-is-segal))))
  ( comp-is-segal A is-segal-A a (u fa) (u fa)
    ( ηa)
    ( comp-is-segal A is-segal-A (u fa) (u fa') (u fa)
      ( ap-hom B A u fa fa' to-left-adjoint-components-is-rezk-is-segal)
      ( ap-hom B A u fa' fa from-left-adjoint-components-is-rezk-is-segal)))
  ( comp-is-segal A is-segal-A a (u fa') (u fa)
    ( comp-is-segal A is-segal-A a (u fa) (u fa')
      ( ηa)
      ( ap-hom B A u fa fa' to-left-adjoint-components-is-rezk-is-segal))
    ( ap-hom B A u fa' fa from-left-adjoint-components-is-rezk-is-segal))
  ( comp-is-segal A is-segal-A a (u fa') (u fa)
    ( ηa')
    ( ap-hom B A u fa' fa from-left-adjoint-components-is-rezk-is-segal))
  ( ηa)
  ( prewhisker-homotopy-is-segal A is-segal-A a (u fa) (u fa)
    ( ηa)
    ( ap-hom B A u fa fa
      ( comp-is-segal B (first is-rezk-B) fa fa' fa
        ( to-left-adjoint-components-is-rezk-is-segal)
        ( from-left-adjoint-components-is-rezk-is-segal)))
    ( comp-is-segal A is-segal-A (u fa) (u fa') (u fa)
      ( ap-hom B A u fa fa' to-left-adjoint-components-is-rezk-is-segal)
      ( ap-hom B A u fa' fa from-left-adjoint-components-is-rezk-is-segal))
    ( rev-functors-pres-comp B A (first is-rezk-B) is-segal-A u fa fa' fa
      ( to-left-adjoint-components-is-rezk-is-segal)
      ( from-left-adjoint-components-is-rezk-is-segal)))
  ( rev-associative-is-segal extext A is-segal-A a (u fa) (u fa') (u fa)
    ( ηa)
    ( ap-hom B A u fa fa' to-left-adjoint-components-is-rezk-is-segal)
    ( ap-hom B A u fa' fa from-left-adjoint-components-is-rezk-is-segal))
   ( postwhisker-homotopy-is-segal (A) (is-segal-A) (a) (u fa') (u fa)
    ( comp-is-segal A is-segal-A a (u fa) (u fa')
      ( ηa)
      ( ap-hom B A u fa fa' to-left-adjoint-components-is-rezk-is-segal))
    ( ηa')
    ( ap-hom B A u fa' fa from-left-adjoint-components-is-rezk-is-segal)
    ( triangle-to-left-adjoint-components-is-rezk-is-segal))
  ( triangle-from-left-adjoint-components-is-rezk-is-segal)

#def ηa'-automorphism uses (extext ω ω')
  : comp-is-segal A is-segal-A a (u fa') (u fa')
    ( ηa')
    ( ap-hom B A u fa' fa'
      ( comp-is-segal B (first is-rezk-B) fa' fa fa'
        ( from-left-adjoint-components-is-rezk-is-segal)
        ( to-left-adjoint-components-is-rezk-is-segal)))

  = ηa'
  :=
  quadruple-concat (hom A a (u fa'))
  ( comp-is-segal A is-segal-A a (u fa') (u fa')
    ( ηa')
    ( ap-hom B A u fa' fa'
      ( comp-is-segal B (first is-rezk-B) fa' fa fa'
        ( from-left-adjoint-components-is-rezk-is-segal)
        ( to-left-adjoint-components-is-rezk-is-segal))))
  ( comp-is-segal A is-segal-A a (u fa') (u fa')
    ( ηa')
    ( comp-is-segal A is-segal-A (u fa') (u fa) (u fa')
      ( ap-hom B A u fa' fa from-left-adjoint-components-is-rezk-is-segal)
      ( ap-hom B A u fa fa' to-left-adjoint-components-is-rezk-is-segal)))
  ( comp-is-segal A is-segal-A a (u fa) (u fa')
    ( comp-is-segal A is-segal-A a (u fa') (u fa)
      ( ηa')
      ( ap-hom B A u fa' fa from-left-adjoint-components-is-rezk-is-segal))
    ( ap-hom B A u fa fa' to-left-adjoint-components-is-rezk-is-segal))
  ( comp-is-segal A is-segal-A a (u fa) (u fa')
    ( ηa)
    ( ap-hom B A u fa fa' to-left-adjoint-components-is-rezk-is-segal))
  ( ηa')
  ( prewhisker-homotopy-is-segal A is-segal-A a (u fa') (u fa')
    ( ηa')
    ( ap-hom B A u fa' fa'
      ( comp-is-segal B (first is-rezk-B) fa' fa fa'
        ( from-left-adjoint-components-is-rezk-is-segal)
        ( to-left-adjoint-components-is-rezk-is-segal)))
    ( comp-is-segal A is-segal-A (u fa') (u fa) (u fa')
      ( ap-hom B A u fa' fa from-left-adjoint-components-is-rezk-is-segal)
      ( ap-hom B A u fa fa' to-left-adjoint-components-is-rezk-is-segal))
    ( rev-functors-pres-comp B A (first is-rezk-B) is-segal-A u fa' fa fa'
      ( from-left-adjoint-components-is-rezk-is-segal)
      ( to-left-adjoint-components-is-rezk-is-segal)))
  ( rev-associative-is-segal extext A is-segal-A a (u fa') (u fa) (u fa')
    ( ηa')
    ( ap-hom B A u fa' fa from-left-adjoint-components-is-rezk-is-segal)
    ( ap-hom B A u fa fa' to-left-adjoint-components-is-rezk-is-segal))
  ( postwhisker-homotopy-is-segal (A) (is-segal-A) (a) (u fa) (u fa')
    ( comp-is-segal A is-segal-A a (u fa') (u fa)
      ( ηa')
      ( ap-hom B A u fa' fa from-left-adjoint-components-is-rezk-is-segal))
    ( ηa)
    ( ap-hom B A u fa fa' to-left-adjoint-components-is-rezk-is-segal)
    ( triangle-from-left-adjoint-components-is-rezk-is-segal))
  ( triangle-to-left-adjoint-components-is-rezk-is-segal)

#def eq-id-from-to-left-adjoint-components-is-rezk-is-segal uses (extext ηa' ω ω')
  : comp-is-segal B (first is-rezk-B) fa fa' fa
    ( to-left-adjoint-components-is-rezk-is-segal)
    ( from-left-adjoint-components-is-rezk-is-segal)

  = id-hom B fa
  :=
  inv-ap-is-emb (hom B fa fa) (hom A a (u fa))
  ( ηa-transposition fa)
  ( is-emb-is-equiv (hom B fa fa) (hom A a (u fa))
    ( ηa-transposition fa)
    ( ω fa))
  ( comp-is-segal B (first is-rezk-B) fa fa' fa
    ( to-left-adjoint-components-is-rezk-is-segal)
    ( from-left-adjoint-components-is-rezk-is-segal))
  ( id-hom B fa)
  ( zig-zag-concat (hom A a (u fa))
    ( ηa-transposition fa
      ( comp-is-segal B (first is-rezk-B) fa fa' fa
        ( to-left-adjoint-components-is-rezk-is-segal)
        ( from-left-adjoint-components-is-rezk-is-segal)))
    ( ηa)
    ( ηa-transposition fa (id-hom B fa))
    ( ηa-automorphism)
    ( concat (hom A a (u fa))
      ( ηa-transposition fa (id-hom B fa))
      ( comp-is-segal A is-segal-A a (u fa) (u fa) ηa (id-hom A (u fa)))
      ( ηa)
      ( prewhisker-homotopy-is-segal A is-segal-A a (u fa) (u fa) ηa
        ( ap-hom B A u fa fa (id-hom B fa))
        ( id-hom A (u fa))
        ( functors-pres-id extext B A u fa))
      ( comp-id-is-segal A is-segal-A a (u fa) ηa)))

#def eq-id-to-from-left-adjoint-components-is-rezk-is-segal uses (extext ηa ω ω')
  : comp-is-segal B (first is-rezk-B) fa' fa fa'
    ( from-left-adjoint-components-is-rezk-is-segal)
    ( to-left-adjoint-components-is-rezk-is-segal)

  = id-hom B fa'
  :=
  inv-ap-is-emb (hom B fa' fa') (hom A a (u fa'))
  ( ηa'-transposition fa')
  ( is-emb-is-equiv
    ( hom B fa' fa')
    ( hom A a (u fa'))
    ( ηa'-transposition fa')
    ( ω' fa'))
  ( comp-is-segal B (first is-rezk-B) fa' fa fa'
    ( from-left-adjoint-components-is-rezk-is-segal)
    ( to-left-adjoint-components-is-rezk-is-segal))
  ( id-hom B fa')
  ( zig-zag-concat (hom A a (u fa'))
    ( ηa'-transposition fa'
      ( comp-is-segal B (first is-rezk-B) fa' fa fa'
        ( from-left-adjoint-components-is-rezk-is-segal)
        ( to-left-adjoint-components-is-rezk-is-segal)))
    ( ηa')
    ( ηa'-transposition fa' (id-hom B fa'))
    ( ηa'-automorphism)
    ( concat (hom A a (u fa'))
      ( ηa'-transposition fa' (id-hom B fa'))
      ( comp-is-segal A is-segal-A a (u fa') (u fa') ηa' (id-hom A (u fa')))
      ( ηa')
      ( prewhisker-homotopy-is-segal A is-segal-A a (u fa') (u fa') ηa'
        ( ap-hom B A u fa' fa' (id-hom B fa'))
        ( id-hom A (u fa'))
        ( functors-pres-id extext B A u fa'))
      ( comp-id-is-segal A is-segal-A a (u fa') ηa')))

#def all-left-adjoint-components-equal-is-rezk-is-segal uses (extext A is-segal-A u a ηa ηa' ω ω')
  : fa = fa'
  :=
  eq-iso-is-rezk B is-rezk-B fa fa'
  ( to-left-adjoint-components-is-rezk-is-segal

  , ( ( from-left-adjoint-components-is-rezk-is-segal

      , eq-id-from-to-left-adjoint-components-is-rezk-is-segal)

    , ( from-left-adjoint-components-is-rezk-is-segal

      , eq-id-to-from-left-adjoint-components-is-rezk-is-segal)))

#def iso-eq-iso-to-left-adjoint-components-is-rezk uses (extext A is-segal-A u a ηa ηa' ω ω')
  : first (iso-eq B (first is-rezk-B) fa fa'
    ( all-left-adjoint-components-equal-is-rezk-is-segal))
  = to-left-adjoint-components-is-rezk-is-segal
  :=
  iso-eq-iso-is-rezk B is-rezk-B fa fa'
  ( to-left-adjoint-components-is-rezk-is-segal

  , ( ( from-left-adjoint-components-is-rezk-is-segal

      , eq-id-from-to-left-adjoint-components-is-rezk-is-segal)

    , ( from-left-adjoint-components-is-rezk-is-segal

      , eq-id-to-from-left-adjoint-components-is-rezk-is-segal)))

#def compute-transport-all-left-adjoint-components-equal-is-rezk-is-segal uses (extext ηa' ω ω')
  : transport B (\ b → hom A a (u b)) fa fa'
    ( all-left-adjoint-components-equal-is-rezk-is-segal) ηa

  = ηa'
  :=
  quintuple-concat (hom A a (u fa'))
  ( transport B (\ b → hom A a (u b)) fa fa'
    ( all-left-adjoint-components-equal-is-rezk-is-segal) ηa)
  ( covariant-transport B fa fa'
    ( first
      ( iso-eq B (first is-rezk-B) fa fa'
        ( all-left-adjoint-components-equal-is-rezk-is-segal)))
    ( \ b → hom A a (u b))
    ( is-covariant-substitution-is-covariant A B (hom A a)
      ( is-covariant-representable-is-segal A is-segal-A a) u)
    ( ηa))
  ( covariant-transport B fa fa'
    ( to-left-adjoint-components-is-rezk-is-segal)
    ( \ b → hom A a (u b))
    ( is-covariant-substitution-is-covariant A B (hom A a)
      ( is-covariant-representable-is-segal A is-segal-A a) u)
    ( ηa))
  ( covariant-transport A (u fa) (u fa')
    ( ap-hom B A u fa fa' to-left-adjoint-components-is-rezk-is-segal)
    ( hom A a)
    ( is-covariant-representable-is-segal A is-segal-A a)
    ( ηa))
  ( comp-is-segal A is-segal-A a (u fa) (u fa') ηa
    ( ap-hom B A u fa fa' to-left-adjoint-components-is-rezk-is-segal))
  ( ( ηa'))
  ( rev (hom A a (u fa'))
    ( covariant-transport B fa fa'
      ( first
        ( iso-eq B (first is-rezk-B) fa fa'
          ( all-left-adjoint-components-equal-is-rezk-is-segal)))
      ( \ b → hom A a (u b))
      ( is-covariant-substitution-is-covariant A B (hom A a)
        ( is-covariant-representable-is-segal A is-segal-A a) u)
      ( ηa))
    ( transport B (\ b → hom A a (u b)) fa fa'
      ( all-left-adjoint-components-equal-is-rezk-is-segal) ηa)
    ( compute-covariant-transport-of-hom-family-iso-eq-is-segal B
      ( first is-rezk-B)
      ( \ b → hom A a (u b))
      ( is-covariant-substitution-is-covariant A B (hom A a)
        ( is-covariant-representable-is-segal A is-segal-A a) u)
      ( fa) (fa')
      ( all-left-adjoint-components-equal-is-rezk-is-segal)
      ( ηa)))
  ( ap (hom B fa fa') (hom A a (u fa'))
    ( first
      ( iso-eq B (first is-rezk-B) fa fa'
        ( all-left-adjoint-components-equal-is-rezk-is-segal)))
    ( to-left-adjoint-components-is-rezk-is-segal)
    ( ηa-transposition fa')
    ( iso-eq-iso-to-left-adjoint-components-is-rezk))
  ( compute-covariant-transport-of-hom-family-is-segal A is-segal-A
    ( a) (u fa) (u fa') (ηa)
    ( ap-hom B A u fa fa' to-left-adjoint-components-is-rezk-is-segal))
  ( compute-covariant-transport-of-substitution A B (hom A a)
    ( is-covariant-representable-is-segal A is-segal-A a) u (fa) (fa')
    ( to-left-adjoint-components-is-rezk-is-segal)
    ( ηa))
  ( triangle-to-left-adjoint-components-is-rezk-is-segal)

#def all-unit-components-equal-is-rezk-is-segal uses (extext A is-segal-A u a ω ω')
  : ( fa , ηa) =_{Σ (b : B) , hom A a (u b)} (fa' , ηa')
  :=
  path-of-pairs-pair-of-paths B (\ b → hom A a (u b)) (fa) (fa')
  ( all-left-adjoint-components-equal-is-rezk-is-segal)
  ( ηa) (ηa')
  ( compute-transport-all-left-adjoint-components-equal-is-rezk-is-segal)

#end all-unit-arrows-equal-is-rezk-is-segal

#def is-transposing-unit
  ( B A : U)
  ( is-segal-A : is-segal A)
  ( u : B → A)
  ( f : A → B)
  ( η : nat-trans A (\ _ → A) (identity A) (comp A B A u f))
  : U
  :=
  ( a : A) → (b : B)
  → is-equiv (hom B (f a) b) (hom A a (u b))
    ( \ k →
      comp-is-segal A is-segal-A a (u (f a)) (u b)
      ( \ t → η t a)
      ( ap-hom B A u (f a) b k))

#def is-transposing-unit-components
  ( B A : U)
  ( is-segal-A : is-segal A)
  ( u : B → A)
  ( f : A → B)
  ( η : nat-trans-components A (\ _ → A) (identity A) (comp A B A u f))
  : U
  :=
  ( a : A) → (b : B)
  → is-equiv (hom B (f a) b) (hom A a (u b))
    ( \ k →
      comp-is-segal A is-segal-A a (u (f a)) (u b)
      ( η a)
      ( ap-hom B A u (f a) b k))

#def equiv-transposing-unit-transposing-unit-components
  ( B A : U)
  ( is-segal-A : is-segal A)
  ( u : B → A)
  : Equiv
    ( Σ ( f : A → B)
      , Σ ( η : nat-trans A (\ _ → A) (identity A) (comp A B A u f))
        , is-transposing-unit B A is-segal-A u f η)
    ( Σ ( f : A → B)
      , Σ ( η : nat-trans-components A (\ _ → A) (identity A) (comp A B A u f))
        , is-transposing-unit-components B A is-segal-A u f η)
  :=
  total-equiv-family-of-equiv
  ( A → B)
  ( \ f →
    Σ ( η : nat-trans A (\ _ → A) (identity A) (comp A B A u f))
    , is-transposing-unit B A is-segal-A u f η)
  ( \ f →
    Σ ( η : nat-trans-components A (\ _ → A) (identity A) (comp A B A u f))
        , is-transposing-unit-components B A is-segal-A u f η)
  ( \ f →
    equiv-total-pullback-is-equiv
    ( nat-trans A (\ _ → A) (identity A) (comp A B A u f))
    ( nat-trans-components A (\ _ → A) (identity A) (comp A B A u f))
    ( ev-components-nat-trans A (\ _ → A) (identity A) (comp A B A u f))
    ( is-equiv-ev-components-nat-trans A (\ _ → A)
      ( identity A) (comp A B A u f))
    ( \ η → is-transposing-unit-components B A is-segal-A u f η))

#def equiv-choice-transposing-unit-components
  ( B A : U)
  ( is-segal-A : is-segal A)
  ( u : B → A)
  : Equiv
    ( Σ ( f : A → B)
      , Σ ( η : nat-trans-components A (\ _ → A) (identity A) (comp A B A u f))
        , is-transposing-unit-components B A is-segal-A u f η)
    ( ( a : A)
      → Σ ( fa : B)
        , Σ ( ηa : hom A a (u fa))
          , ( b : B)
            → is-equiv (hom B fa b) (hom A a (u b))
              ( \ k →
                comp-is-segal A is-segal-A a (u fa) (u b)
                ( ηa) (ap-hom B A u fa b k)))
  :=
  equiv-comp
  ( Σ ( f : A → B)
    , Σ ( η : nat-trans-components A (\ _ → A) (identity A) (comp A B A u f))
      , is-transposing-unit-components B A is-segal-A u f η)
  ( Σ ( f : A → B)
    , ( a : A)
    → Σ ( ηa : hom A a (u (f a)))
      , ( b : B)
        → is-equiv (hom B (f a) b) (hom A a (u b))
          ( \ k →
            comp-is-segal A is-segal-A a (u (f a)) (u b)
            ( ηa) (ap-hom B A u (f a) b k)))
  ( ( a : A)
      → Σ ( fa : B)
        , Σ ( ηa : hom A a (u fa))
          , ( b : B)
            → is-equiv (hom B fa b) (hom A a (u b))
              ( \ k →
                comp-is-segal A is-segal-A a (u fa) (u b)
                ( ηa) (ap-hom B A u fa b k)))
  ( total-equiv-family-of-equiv
    ( A → B)
    ( \ f →
      Σ ( η : nat-trans-components A (\ _ → A) (identity A) (comp A B A u f))
          , is-transposing-unit-components B A is-segal-A u f η)
    ( \ f →
      ( a : A)
        → Σ ( ηa : hom A a (u (f a)))
          , ( b : B)
            → is-equiv (hom B (f a) b) (hom A a (u b))
              ( \ k →
                comp-is-segal A is-segal-A a (u (f a)) (u b)
                ( ηa)
                ( ap-hom B A u (f a) b k)))
    ( \ f →
      inv-equiv-choice A (\ a → hom A a (u (f a)))
      ( \ a ηa →
        ( b : B)
          → is-equiv (hom B (f a) b) (hom A a (u b))
            ( \ k →
              comp-is-segal A is-segal-A a (u (f a)) (u b)
              ( ηa) (ap-hom B A u (f a) b k)))))
  ( inv-equiv-choice A (\ _ → B)
    ( \ a fa →
      Σ ( ηa : hom A a (u fa))
          , ( b : B)
            → is-equiv (hom B fa b) (hom A a (u b))
              ( \ k →
                comp-is-segal A is-segal-A a (u fa) (u b)
                ( ηa) (ap-hom B A u fa b k))))

#def equiv-choice-transposing-unit
  ( B A : U)
  ( is-segal-A : is-segal A)
  ( u : B → A)
  : Equiv
    ( Σ ( f : A → B)
      , Σ ( η : nat-trans A (\ _ → A) (identity A) (comp A B A u f))
        , is-transposing-unit B A is-segal-A u f η)
    ( ( a : A)
      → Σ ( fa : B)
        , Σ ( ηa : hom A a (u fa))
          , ( b : B)
            → is-equiv (hom B fa b) (hom A a (u b))
              ( \ k →
                comp-is-segal A is-segal-A a (u fa) (u b)
                ( ηa) (ap-hom B A u fa b k)))
  :=
  equiv-comp
  ( Σ ( f : A → B)
    , Σ ( η : nat-trans A (\ _ → A) (identity A) (comp A B A u f))
      , is-transposing-unit B A is-segal-A u f η)
  ( Σ ( f : A → B)
    , Σ ( η : nat-trans-components A (\ _ → A) (identity A) (comp A B A u f))
      , is-transposing-unit-components B A is-segal-A u f η)
  ( ( a : A)
    → Σ ( fa : B)
      , Σ ( ηa : hom A a (u fa))
        , ( b : B)
          → is-equiv (hom B fa b) (hom A a (u b))
            ( \ k →
              comp-is-segal A is-segal-A a (u fa) (u b)
              ( ηa) (ap-hom B A u fa b k)))
  ( equiv-transposing-unit-transposing-unit-components B A is-segal-A u)
  ( equiv-choice-transposing-unit-components B A is-segal-A u)
```
