# ?. Full Embeddings

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Prerequisites

- `hott/*` - We require various prerequisites from homotopy type theory, for
  instance equivalences.
- `03-extension-types.rzk.md` - We use extension extensionality for certain
  proofs in this section.
- `06-2cat-of-segal-types.rzk.md` - We make use of the functoriality of
  functions.
- `09-yoneda.rzk.md` - We make use of initial and final objects.

```rzk
#assume extext : ExtExt
```

## find a place

```rzk
-- TODO: needs better name?
#def dhom-fabricate-is-locally-contr-extext
  ( A : Δ¹ → U)
  ( is-contr-A : (t : Δ¹) → is-contr (A t))
  ( x : A 0₂)
  ( y : A 1₂)
  : ( t : Δ¹) → A t [t ≡ 0₂ ↦ x , t ≡ 1₂ ↦ y]
  :=
  center-contraction
  ( ( t : Δ¹) → A t [t ≡ 0₂ ↦ x , t ≡ 1₂ ↦ y])
  ( weakextext-extext extext 2 Δ¹ ∂Δ¹ A is-contr-A
    ( \ t → recOR(t ≡ 0₂ ↦ x , t ≡ 1₂ ↦ y)))
```

```rzk
-- TODO: needs better name?
#def eq-dhom-refl-is-locally-contr-extext uses (extext)
  ( A : Δ¹ → U)
  ( is-contr-A : (t : Δ¹) → is-contr (A t))
  ( x : A 0₂)
  ( y : A 1₂)
  ( f g : (t : Δ¹) → A t [t ≡ 0₂ ↦ x , t ≡ 1₂ ↦ y])
  : ( t : Δ¹) → (f t = g t) [t ≡ 0₂ ↦ refl , t ≡ 1₂ ↦ refl]
  :=
  dhom-fabricate-is-locally-contr-extext
  ( \ t → f t = g t)
  ( \ t → is-prop-is-contr (A t) (is-contr-A t) (f t) (g t))
  ( refl)
  ( refl)
```

## Full Embeddings

A full embedding is a map that is an equivalence on hom-types:

```rzk
#def is-full-emb
  ( A B : U)
  ( f : A → B)
  : U
  :=
    ( x : A)
  → ( y : A)
  → is-equiv (hom A x y) (hom B (f x) (f y)) (ap-hom A B f x y)
```

This property is also known under the term "fully faithful". We chose the name
full embedding, since from the type theoretic viewpoint this is closer to the
already existing concept `is-emb` from HoTT. Additionally, it should be possible
to prove that `is-full-emb` implies `is-emb`. However, this proof is rather
challenging and has not been finished due to time constraints.

## Equivalences are full embeddings

Equivalences are full embeddings -- the proof is already present in
`06-2cat-of-segal-types.rzk.md` by using extension extensionality.

```rzk
#def is-full-emb-is-equiv
  ( A B : U)
  ( f : A → B)
  ( is-equiv-f : is-equiv A B f)
  : is-full-emb A B f
  := is-equiv-ap-hom-is-equiv extext A B f is-equiv-f
```

## Compositions of full embeddings are full embeddings

Since equivalences compose, we can easily derive that full embeddings also have
this property.

```rzk
#def is-full-emb-comp
  ( A B C : U)
  ( f : A → B)
  ( is-full-emb-f : is-full-emb A B f)
  ( g : B → C)
  ( is-full-emb-g : is-full-emb B C g)
  : is-full-emb A C (comp A B C g f)
  :=
  \ x y →
  is-equiv-comp
  ( hom A x y)
  ( hom B (f x) (f y))
  ( hom C (g (f x)) (g (f y)))
  ( ap-hom A B f x y)
  ( is-full-emb-f x y)
  ( ap-hom B C g (f x) (f y))
  ( is-full-emb-g (f x) (f y))
```

```rzk
#def is-full-emb-triple-comp
  ( A B C D : U)
  ( f : A → B)
  ( is-full-emb-f : is-full-emb A B f)
  ( g : B → C)
  ( is-full-emb-g : is-full-emb B C g)
  ( h : C → D)
  ( is-full-emb-h : is-full-emb C D h)
  : is-full-emb A D (triple-comp A B C D h g f)
  :=
  is-full-emb-comp A B D
  ( f) (is-full-emb-f)
  ( comp B C D h g)
  ( is-full-emb-comp B C D
    ( g) (is-full-emb-g)
    ( h) (is-full-emb-h))
```

```rzk
#def is-full-emb-quadruple-comp
  ( A B C D E : U)
  ( f : A → B)
  ( is-full-emb-f : is-full-emb A B f)
  ( g : B → C)
  ( is-full-emb-g : is-full-emb B C g)
  ( h : C → D)
  ( is-full-emb-h : is-full-emb C D h)
  ( i : D → E)
  ( is-full-emb-i : is-full-emb D E i)
  : is-full-emb A E (quadruple-comp A B C D E i h g f)
  :=
  is-full-emb-comp A B E
  ( f) (is-full-emb-f)
  ( triple-comp B C D E i h g)
  ( is-full-emb-triple-comp B C D E
    ( g) (is-full-emb-g)
    ( h) (is-full-emb-h)
    ( i) (is-full-emb-i))
```

## Full embeddings detect initial and final objects

A simple fact that follows from the equivalence of hom types is that initial and
final objects can be detected by full embeddings:

```rzk
#def is-initial-is-full-emb-is-initial
  ( A B : U)
  ( f : A → B)
  ( is-full-emb-f : is-full-emb A B f)
  ( a : A)
  ( is-initial-fa : is-initial B (f a))
  : is-initial A a
  :=
  \ y →
  is-contr-equiv-is-contr' (hom A a y) (hom B (f a) (f y))
  ( ap-hom A B f a y , is-full-emb-f a y)
  ( is-initial-fa (f y))

#def is-final-is-full-emb-is-final
  ( A B : U)
  ( f : A → B)
  ( is-full-emb-f : is-full-emb A B f)
  ( a : A)
  ( is-final-fa : is-final B (f a))
  : is-final A a
  :=
  \ x →
  is-contr-equiv-is-contr' (hom A x a) (hom B (f x) (f a))
  ( ap-hom A B f x a , is-full-emb-f x a)
  ( is-final-fa (f x))
```

## The inclusion of isomorphisms into morphisms is a full embedding

We opt to show a more general statement

```rzk
#def is-equiv-hom-iso-dhom
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : arr A)
  ( f : Iso A (is-segal-A) (x 0₂) (y 0₂))
  ( g : Iso A (is-segal-A) (x 1₂) (y 1₂))
  : is-equiv
    ( ( t : Δ¹) → Iso A is-segal-A (x t) (y t) [t ≡ 0₂ ↦ f , t ≡ 1₂ ↦ g])
    ( Σ ( F : (t : Δ¹) → hom A (x t) (y t) [t ≡ 0₂ ↦ first f , t ≡ 1₂ ↦ first g])
      , ( t : Δ¹) → is-iso-arrow A is-segal-A (x t) (y t) (F t)
        [ t ≡ 0₂ ↦ second f , t ≡ 1₂ ↦ second g])
    ( \ σ → (\ t → first (σ t) , \ t → second (σ t)))
  :=
  is-equiv-has-inverse
  ( ( t : Δ¹) → Iso A is-segal-A (x t) (y t) [t ≡ 0₂ ↦ f , t ≡ 1₂ ↦ g])
  ( Σ ( F : (t : Δ¹) → hom A (x t) (y t) [t ≡ 0₂ ↦ first f , t ≡ 1₂ ↦ first g])
    , ( t : Δ¹)
      → is-iso-arrow A is-segal-A (x t) (y t) (F t)
      [ t ≡ 0₂ ↦ second f , t ≡ 1₂ ↦ second g])
  ( \ σ → (\ t → first (σ t) , \ t → second (σ t)))
  ( \ (σ , is-iso-σ) t → (σ t , is-iso-σ t)
    , ( ( \ _ → refl)
      , ( \ _ → refl)))
```

```rzk
#def is-contr-hom-is-iso-arrow-sides-iso-is-rezk
  ( A : U)
  ( is-rezk-A : is-rezk A)
  ( x₁ y₁ x₂ y₂ : A)
  ( f : hom A x₁ y₁)
  ( g : hom A x₂ y₂)
  ( h : Iso A (first is-rezk-A) x₁ x₂)
  ( k : Iso A (first is-rezk-A) y₁ y₂)
  ( F : (t : Δ¹) → hom A (f t) (g t) [t ≡ 0₂ ↦ first h , t ≡ 1₂ ↦ first k])
  : is-contr
    ( ( t : Δ¹) → is-iso-arrow A (first is-rezk-A) (f t) (g t) (F t)
      [ t ≡ 0₂ ↦ second h , t ≡ 1₂ ↦ second k])
  :=
  iso-ind-is-rezk A is-rezk-A x₁
  ( \ x₂' h' →
    ( g' : hom A x₂' y₂)
    → ( F' : (t : Δ¹) → hom A (f t) (g' t) [t ≡ 0₂ ↦ first h' , t ≡ 1₂ ↦ first k])
    → is-contr
      ( ( t : Δ¹) → is-iso-arrow A (first is-rezk-A) (f t) (g' t) (F' t)
        [ t ≡ 0₂ ↦ second h' , t ≡ 1₂ ↦ second k]))
  ( iso-ind-is-rezk A is-rezk-A y₁
    ( \ y₂' k' →
      ( g' : hom A x₁ y₂')
      → ( F' : (t : Δ¹) → hom A (f t) (g' t)
               [ t ≡ 0₂ ↦ id-hom A x₁ , t ≡ 1₂ ↦ first k'])
      → is-contr
        ( ( t : Δ¹) → is-iso-arrow A (first is-rezk-A) (f t) (g' t) (F' t)
          [ t ≡ 0₂ ↦ is-iso-arrow-id-hom A (first is-rezk-A) x₁
          , t ≡ 1₂ ↦ second k']))
    ( \ g' F' →
      ind-curried-square-sides-id-is-segal A (first is-rezk-A) x₁ y₁ f
      ( \ g'' F'' →
        is-contr
        ( ( t : Δ¹) → is-iso-arrow A (first is-rezk-A) (f t) (g'' t) (F'' t)
          [ t ≡ 0₂ ↦ is-iso-arrow-id-hom A (first is-rezk-A) x₁
          , t ≡ 1₂ ↦ is-iso-arrow-id-hom A (first is-rezk-A) y₁]))
      ( weakextext-extext extext 2 Δ¹ ∂Δ¹
        ( \ t → is-iso-arrow A (first is-rezk-A) (f t) (f t) (\ (s : Δ¹) → (f t)))
        ( \ t →
          is-contr-is-inhabited-is-prop
          ( is-iso-arrow A (first is-rezk-A) (f t) (f t) (\ (s : Δ¹) → (f t)))
          ( is-prop-is-iso-arrow extext A (first is-rezk-A)
            ( f t) (f t) (\ (s : Δ¹) → (f t)))
          ( is-iso-arrow-id-hom A (first is-rezk-A) (f t)))
        ( \ t →
          recOR
          ( t ≡ 0₂ ↦ is-iso-arrow-id-hom A (first is-rezk-A) x₁
          , t ≡ 1₂ ↦ is-iso-arrow-id-hom A (first is-rezk-A) y₁)))
      ( g')
      ( \ t s → F' t s))
    ( y₂)
    ( k))
  ( x₂)
  ( h)
  ( g)
  ( F)
```

```rzk
#def is-equiv-ap-hom-hom-iso uses (extext)
  ( A : U)
  ( is-rezk-A : is-rezk A)
  ( x y : arr A)
  ( f : Iso A (first is-rezk-A) (x 0₂) (y 0₂))
  ( g : Iso A (first is-rezk-A) (x 1₂) (y 1₂))
  : is-equiv
    ( ( t : Δ¹) → Iso A (first is-rezk-A) (x t) (y t) [t ≡ 0₂ ↦ f , t ≡ 1₂ ↦ g])
    ( ( t : Δ¹) → hom A (x t) (y t) [t ≡ 0₂ ↦ first f , t ≡ 1₂ ↦ first g])
    ( \ σ t → hom-iso A (first is-rezk-A) (x t) (y t) (σ t))
  :=
  is-equiv-comp
  ( ( t : Δ¹) → Iso A (first is-rezk-A) (x t) (y t) [t ≡ 0₂ ↦ f , t ≡ 1₂ ↦ g])
  ( Σ ( F : (t : Δ¹) → hom A (x t) (y t) [t ≡ 0₂ ↦ first f , t ≡ 1₂ ↦ first g])
    , ( t : Δ¹) → is-iso-arrow A (first is-rezk-A) (x t) (y t) (F t)
      [ t ≡ 0₂ ↦ second f , t ≡ 1₂ ↦ second g])
  ( ( t : Δ¹) → hom A (x t) (y t) [t ≡ 0₂ ↦ first f , t ≡ 1₂ ↦ first g])
  ( \ σ → (\ t → first (σ t) , \ t → second (σ t)))
  ( is-equiv-hom-iso-dhom A (first is-rezk-A) x y f g)
  ( projection-total-type
    ( ( t : Δ¹) → hom A (x t) (y t) [t ≡ 0₂ ↦ first f , t ≡ 1₂ ↦ first g])
    ( \ F →
      ( t : Δ¹) → is-iso-arrow A (first is-rezk-A) (x t) (y t) (F t)
      [ t ≡ 0₂ ↦ second f , t ≡ 1₂ ↦ second g]))
  ( is-equiv-projection-contractible-fibers
    ( ( t : Δ¹) → hom A (x t) (y t) [t ≡ 0₂ ↦ first f , t ≡ 1₂ ↦ first g])
    ( \ F →
      ( t : Δ¹) → is-iso-arrow A (first is-rezk-A) (x t) (y t) (F t)
      [ t ≡ 0₂ ↦ second f , t ≡ 1₂ ↦ second g])
    ( is-contr-hom-is-iso-arrow-sides-iso-is-rezk A is-rezk-A
      ( x 0₂) (x 1₂) (y 0₂) (y 1₂)
      ( x) (y)
      ( f) (g)))
```

```rzk
#def is-full-emb-hom-iso uses (extext)
  ( A : U)
  ( is-rezk-A : is-rezk A)
  ( x y : A)
  : is-full-emb
    ( Iso A (first is-rezk-A) x y)
    ( hom A x y)
    ( hom-iso A (first is-rezk-A) x y)
  :=
  \ f g → is-equiv-ap-hom-hom-iso A is-rezk-A (\ _ → x) (\ _ → y) f g
```

```rzk
#def is-full-emb-total-type-hom-iso uses (extext)
  ( A B : U)
  ( is-rezk-A : is-rezk A)
  ( x y : B → A)
  : is-full-emb
    ( Σ ( b : B) , Iso A (first is-rezk-A) (x b) (y b))
    ( Σ ( b : B) , hom A (x b) (y b))
    ( \ (b , f) → (b , hom-iso A (first is-rezk-A) (x b) (y b) f))
  :=
  \ (v , f) (w , g) →
  is-equiv-triple-comp
  ( hom (Σ (b : B) , Iso A (first is-rezk-A) (x b) (y b)) (v , f) (w , g))
  ( Σ ( h : hom B v w)
    , dhom B v w h (\ b → Iso A (first is-rezk-A) (x b) (y b)) f g)
  ( Σ ( h : hom B v w)
    , dhom B v w h (\ b → hom A (x b) (y b)) (first f) (first g))
  ( hom (Σ (b : B) , hom A (x b) (y b)) (v , first f) (w , first g))
  ( sigma-dhom-hom B (\ b → Iso A (first is-rezk-A) (x b) (y b)) (v , f) (w , g))
  ( is-equiv-sigma-dhom-hom B (\ b → Iso A (first is-rezk-A) (x b) (y b))
    ( v , f) (w , g))
  ( \ (h , γ) → (h , \ t → first (γ t)))
  ( is-equiv-total-is-equiv-fiberwise (hom B v w)
    ( \ h → dhom B v w h (\ b → Iso A (first is-rezk-A) (x b) (y b)) f g)
    ( \ h → dhom B v w h (\ b → hom A (x b) (y b)) (first f) (first g))
    ( \ h γ → \ t → first (γ t))
    ( \ h →
      is-equiv-ap-hom-hom-iso A is-rezk-A
      ( \ t → x (h t)) (\ t → y (h t))
      ( f) (g)))
  ( hom-sigma-dhom B (\ b → hom A (x b) (y b)) (v , first f) (w , first g))
  ( is-equiv-hom-sigma-dhom B (\ b → hom A (x b) (y b))
    ( v , first f) (w , first g))
```
