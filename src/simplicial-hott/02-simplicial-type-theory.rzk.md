# 3. Simplicial Type Theory

These formalisations correspond in part to Section 3 of the RS17 paper.

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Simplices and their subshapes

### Simplices

```rzk title="The 1-simplex"
#def Δ¹
  : 2 → TOPE
  := \ t → TOP
```

```rzk title="The 2-simplex"
#def Δ²
  : ( 2 × 2) → TOPE
  := \ (t , s) → s ≤ t
```

```rzk title="The 3-simplex"
#def Δ³
  : ( 2 × 2 × 2) → TOPE
  := \ ((t1 , t2) , t3) → t3 ≤ t2 ∧ t2 ≤ t1
```

### Boundaries of simplices

```rzk title="The boundary of a 1-simplex"
#def ∂Δ¹
  : Δ¹ → TOPE
  := \ t → (t ≡ 0₂ ∨ t ≡ 1₂)
```

```rzk title="The boundary of a 2-simplex"
#def ∂Δ²
  : Δ² → TOPE
  :=
    \ (t , s) → (s ≡ 0₂ ∨ t ≡ 1₂ ∨ s ≡ t)
```

### The 2 dimensional inner horn

```rzk
#def Λ
  : ( 2 × 2) → TOPE
  := \ (t , s) → (s ≡ 0₂ ∨ t ≡ 1₂)

#def Λ²₁
  : Δ² → TOPE
  := \ (s , t) → Λ (s , t)
```

### The 3 dimensional inner horns

```rzk
#def Λ³₁
  : Δ³ → TOPE
  := \ ((t1 , t2) , t3) → t3 ≡ 0₂ ∨ t2 ≡ t1 ∨ t1 ≡ 1₂

#def Λ³₂
  : Δ³ → TOPE
  := \ ((t1 , t2) , t3) → t3 ≡ 0₂ ∨ t3 ≡ t2 ∨ t1 ≡ 1₂
```

### Products

The product of topes defines the product of shapes.

```rzk
#def shape-prod
  ( I J : CUBE)
  ( ψ : I → TOPE)
  ( χ : J → TOPE)
  : ( I × J) → TOPE
  := \ (t , s) → ψ t ∧ χ s
```

```rzk title="The square as a product"
#def Δ¹×Δ¹
  : ( 2 × 2) → TOPE
  := shape-prod 2 2 Δ¹ Δ¹
```

```rzk title="The total boundary of the square"
#def ∂□
  : ( 2 × 2) → TOPE
  := \ (t , s) → ((∂Δ¹ t) ∧ (Δ¹ s)) ∨ ((Δ¹ t) ∧ (∂Δ¹ s))
```

```rzk title="The vertical boundary of the square"
#def ∂Δ¹×Δ¹
  : ( 2 × 2) → TOPE
  := shape-prod 2 2 ∂Δ¹ Δ¹
```

```rzk title="The horizontal boundary of the square"
#def Δ¹×∂Δ¹
  : ( 2 × 2) → TOPE
  := shape-prod 2 2 Δ¹ ∂Δ¹
```

```rzk title="The prism from a 2-simplex in an arrow type"
#def Δ²×Δ¹
  : ( 2 × 2 × 2) → TOPE
  := shape-prod (2 × 2) 2 Δ² Δ¹
```

```rzk
#def Δ³×Δ²
  : ( ( 2 × 2 × 2) × (2 × 2)) → TOPE
  := shape-prod (2 × 2 × 2) (2 × 2) Δ³ Δ²
```

Maps out of $Δ²$ are a retract of maps out of $Δ¹×Δ¹$.

```rzk title="RS17, Proposition 3.6"
#def Δ²-is-retract-Δ¹×Δ¹
  ( A : U)
  : is-retract-of (Δ² → A) (Δ¹×Δ¹ → A)
  :=
    ( ( \ f → \ (t , s) →
        recOR
          ( t ≤ s ↦ f (t , t)
          , s ≤ t ↦ f (t , s)))
    , ( ( \ f → \ ts → f ts) , \ _ → refl))
```

Maps out of $Δ³$ are a retract of maps out of $Δ²×Δ¹$.

```rzk title="RS17, Proposition 3.7"

#def Δ³-is-retract-Δ²×Δ¹-retraction
  ( A : U)
  : ( Δ²×Δ¹ → A) → (Δ³ → A)
  := \ f → \ ((t1 , t2) , t3) → f ((t1 , t3) , t2)

#def Δ³-is-retract-Δ²×Δ¹-section
  ( A : U)
  : ( Δ³ → A) → (Δ²×Δ¹ → A)
  :=
    \ f → \ ((t1 , t2) , t3) →
    recOR
      ( t3 ≤ t2 ↦ f ((t1 , t2) , t2)
      , t2 ≤ t3 ↦
          recOR
            ( t3 ≤ t1 ↦ f ((t1 , t3) , t2)
            , t1 ≤ t3 ↦ f ((t1 , t1) , t2)))

#def Δ³-is-retract-Δ²×Δ¹
  ( A : U)
  : is-retract-of (Δ³ → A) (Δ²×Δ¹ → A)
  :=
    ( Δ³-is-retract-Δ²×Δ¹-section A
    , ( Δ³-is-retract-Δ²×Δ¹-retraction A , \ _ → refl))
```

### Pushout product

Pushout product Φ×ζ ∪\_{Φ×χ} ψ×χ of Φ ↪ ψ and χ ↪ ζ, domain of the co-gap map.

```rzk
#def shape-pushout-prod
  ( I J : CUBE)
  ( ψ : I → TOPE)
  ( Φ : ψ → TOPE)
  ( ζ : J → TOPE)
  ( χ : ζ → TOPE)
  : ( shape-prod I J ψ ζ) → TOPE
  := \ (t , s) → (Φ t ∧ ζ s) ∨ (ψ t ∧ χ s)
```

### Intersections

The intersection of shapes is defined by conjunction on topes.

```rzk
#def shape-intersection
  ( I : CUBE)
  ( ψ χ : I → TOPE)
  : I → TOPE
  := \ t → ψ t ∧ χ t
```

### Unions

The union of shapes is defined by disjunction on topes.

```rzk
#def shape-union
  ( I : CUBE)
  ( ψ χ : I → TOPE)
  : I → TOPE
  := \ t → ψ t ∨ χ t
```

### Connection squares

<!-- This is manually adjusted diagram (hopefully fully supported in the future by rzk) -->
<svg class="rzk-render" viewBox="-175 -100 350 375" width="150" height="150">
  <path d="M -99.0358460500274 -31.444756515260025 L -89.86020976982607 109.04996702489628 L 78.85622687537837 109.04996702489628 Z" style="fill: purple; opacity: 0.2"><title>f</title></path>
  <text x="-36.6799429814917" y="62.21839251151084" fill="purple" stroke="white" stroke-width="10" stroke-opacity=".8" paint-order="stroke"></text>
  <path d="M -88.57160646618001 -39.70915201762215 L 98.4961027394271 -39.70915201762215 L 89.32046645922577 100.78557152253414 Z" style="fill: purple; opacity: 0.2"><title>f</title></path>
  <text x="33.08165424415762" y="7.122422495763279" fill="purple" stroke="white" stroke-width="10" stroke-opacity=".8" paint-order="stroke"></text>
  <polyline points="-108.73641627786154,-28.016064827507464 -100.54837539908667,97.35687983478158" stroke="purple" stroke-width="3" marker-end="url(#arrow)"><title>f</title></polyline>
  <text x="-104.6423958384741" y="34.67040750363706" fill="purple" stroke="white" stroke-width="10" stroke-opacity=".8" paint-order="stroke">f</text>
  <polyline points="-90.03982894447489,-47.97354751998429 90.03982894447466,-47.97354751998429" stroke="purple" stroke-width="3" marker-end="url(#arrow)"><title>f</title></polyline>
  <text x="-1.1368683772161603e-13" y="-47.97354751998429" fill="purple" stroke="white" stroke-width="10" stroke-opacity=".8" paint-order="stroke">f</text>
  <polyline points="-94.34447446980596,-35.57774791227483 83.54960825780415,104.91856291954896" stroke="purple" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <text x="-5.3974331060009035" y="34.670407503637065" fill="purple" stroke="white" stroke-width="10" stroke-opacity=".8" paint-order="stroke">f</text>
  <polyline points="-79.24496273247331,114.31436252725841 79.24496273247308,114.31436252725841" stroke="purple" stroke-width="3"></polyline>
  <polyline points="-79.24496273247331,120.31436252725841 79.24496273247308,120.31436252725841" stroke="purple" stroke-width="3"></polyline>
  <text x="-1.1368683772161603e-13" y="117.31436252725841" fill="purple" stroke="white" stroke-width="10" stroke-opacity=".8" paint-order="stroke"></text>
  <polyline points="105.73641627786131,-28.016064827507464  97.54837539908644,97.35687983478158" stroke="purple" stroke-width="3"></polyline>
  <polyline points="111.73641627786131,-28.016064827507464 103.54837539908644,97.35687983478158" stroke="purple" stroke-width="3"></polyline>
  <text x="104.64239583847387" y="34.67040750363706" fill="purple" stroke="white" stroke-width="10" stroke-opacity=".8" paint-order="stroke"></text>
  <text x="-110.03982894447489" y="-47.97354751998429" fill="purple" stroke="white" stroke-width="10" stroke-opacity=".8" paint-order="stroke">•</text>
  <text x="-99.24496273247331" y="117.31436252725841" fill="purple" stroke="white" stroke-width="10" stroke-opacity=".8" paint-order="stroke">•</text>
  <text x="110.03982894447466" y="-47.97354751998429" fill="purple" stroke="white" stroke-width="10" stroke-opacity=".8" paint-order="stroke">•</text>
  <text x="99.24496273247308" y="117.31436252725841" fill="purple" stroke="white" stroke-width="10" stroke-opacity=".8" paint-order="stroke">•</text>
</svg>

```rzk title="RS17 Proposition 3.5(a)"
#define join-square-arrow
  ( A : U)
  ( f : 2 → A)
  : ( 2 × 2) → A
  := \ (t , s) → recOR (t ≤ s ↦ f s , s ≤ t ↦ f t)
```

<!-- This is manually adjusted diagram (hopefully fully supported in the future by rzk) -->
<svg class="rzk-render" viewBox="-175 -100 350 375" width="150" height="150">
  <path d="M -99.0358460500274 -31.444756515260025 L -89.86020976982607 109.04996702489628 L 78.85622687537837 109.04996702489628 Z" style="fill: purple; opacity: 0.2"><title>f</title></path>
  <text x="-36.6799429814917" y="62.21839251151084" fill="purple" stroke="white" stroke-width="10" stroke-opacity=".8" paint-order="stroke"></text>
  <path d="M -88.57160646618001 -39.70915201762215 L 98.4961027394271 -39.70915201762215 L 89.32046645922577 100.78557152253414 Z" style="fill: purple; opacity: 0.2"><title>f</title></path>
  <text x="33.08165424415762" y="7.122422495763279" fill="purple" stroke="white" stroke-width="10" stroke-opacity=".8" paint-order="stroke"></text>
  <polyline points="-105.73641627786154,-28.016064827507464 -97.54837539908667,97.35687983478158" stroke="purple" stroke-width="3"></polyline>
  <polyline points="-111.73641627786154,-28.016064827507464 -103.54837539908667,97.35687983478158" stroke="purple" stroke-width="3"></polyline>
  <text x="-104.6423958384741" y="34.67040750363706" fill="purple" stroke="white" stroke-width="10" stroke-opacity=".8" paint-order="stroke"></text>
  <polyline points="-90.03982894447489,-44.97354751998429 90.03982894447466,-44.97354751998429" stroke="purple" stroke-width="3"></polyline>
  <polyline points="-90.03982894447489,-50.97354751998429 90.03982894447466,-50.97354751998429" stroke="purple" stroke-width="3"></polyline>
  <text x="-1.1368683772161603e-13" y="-47.97354751998429" fill="purple" stroke="white" stroke-width="10" stroke-opacity=".8" paint-order="stroke"></text>
  <polyline points="-94.34447446980596,-35.57774791227483 83.54960825780415,104.91856291954896" stroke="purple" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <text x="-5.3974331060009035" y="34.670407503637065" fill="purple" stroke="white" stroke-width="10" stroke-opacity=".8" paint-order="stroke">f</text>
  <polyline points="-79.24496273247331,117.31436252725841 79.24496273247308,117.31436252725841" stroke="purple" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <text x="-1.1368683772161603e-13" y="117.31436252725841" fill="purple" stroke="white" stroke-width="10" stroke-opacity=".8" paint-order="stroke">f</text>
  <polyline points="108.73641627786131,-28.016064827507464 100.54837539908644,97.35687983478158" stroke="purple" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <text x="104.64239583847387" y="34.67040750363706" fill="purple" stroke="white" stroke-width="10" stroke-opacity=".8" paint-order="stroke">f</text>
  <text x="-110.03982894447489" y="-47.97354751998429" fill="purple" stroke="white" stroke-width="10" stroke-opacity=".8" paint-order="stroke">•</text>
  <text x="-99.24496273247331" y="117.31436252725841" fill="purple" stroke="white" stroke-width="10" stroke-opacity=".8" paint-order="stroke">•</text>
  <text x="110.03982894447466" y="-47.97354751998429" fill="purple" stroke="white" stroke-width="10" stroke-opacity=".8" paint-order="stroke">•</text>
  <text x="99.24496273247308" y="117.31436252725841" fill="purple" stroke="white" stroke-width="10" stroke-opacity=".8" paint-order="stroke">•</text>
</svg>

```rzk title="RS17 Proposition 3.5(b)"
#define meet-square-arrow
  ( A : U)
  ( f : 2 → A)
  : ( 2 × 2) → A
  := \ (t , s) → recOR (t ≤ s ↦ f t , s ≤ t ↦ f s)
```

<!-- Definitions for the SVG images above -->
<svg width="0" height="0">
  <defs>
    <style data-bx-fonts="Noto Serif">@import url(https://fonts.googleapis.com/css2?family=Noto+Serif&display=swap);</style>
    <marker id="arrow" viewBox="0 0 10 10" refX="5" refY="5"
      markerWidth="5" markerHeight="5" orient="auto-start-reverse">
      <path d="M 0 2 L 5 5 L 0 8 z" stroke="black" fill="black" />
    </marker>
  </defs>
  <style>
    text, textPath {
      font-family: Noto Serif;
      font-size: 28px;
      dominant-baseline: middle;
      text-anchor: middle;
    }
  </style>
</svg>

## Functorial comparisons of shapes

### Functorial retracts

For a subshape `ϕ ⊂ ψ` we have an easy way of stating that it is a retract in a
strict and functorial way. Intuitively this happens when there is a map from `ψ`
to `ϕ` that fixes the subshape `ψ`. But in the definition below we actually ask
for a section of the family of extensions of a function `ϕ → A` to a function
`ψ → A` and we ask for this section to be natural in the type `A`.

```rzk
#def is-functorial-shape-retract
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  : U
  :=
    ( A' : U) → (A : U) → (α : A' → A)
  → has-section-family-over-map
      ( ϕ → A') (\ f → (t : ψ) → A' [ϕ t ↦ f t])
      ( ϕ → A) (\ f → (t : ψ) → A [ϕ t ↦ f t])
      ( \ f t → α (f t))
      ( \ _ g t → α (g t))
```

For example, this applies to `Δ² ⊂ Δ¹×Δ¹`.

```rzk
#def is-functorial-retract-Δ²-Δ¹×Δ¹
  : is-functorial-shape-retract (2 × 2) (Δ¹×Δ¹) (Δ²)
  :=
    \ A' A α →
      ( ( first (Δ²-is-retract-Δ¹×Δ¹ A') , first (Δ²-is-retract-Δ¹×Δ¹ A))
        , \ a' → refl)
```

Every functorial shape retract automatically induces a section when restricting
to diagrams extending a fixed diagram `σ': ϕ → A'` (or, respectively, its image
`ϕ → A` under α).

```rzk
#def relativize-is-functorial-shape-retract
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( χ : ψ → TOPE)
  ( is-fretract-ψ-χ : is-functorial-shape-retract I ψ χ)
  ( ϕ : χ → TOPE)
  ( A' A : U)
  ( α : A' → A)
  ( σ' : ϕ → A')
  : has-section-family-over-map
      ( ( t : χ) → A' [ϕ t ↦ σ' t])
      ( \ τ' → (t : ψ) → A' [χ t ↦ τ' t])
      ( ( t : χ) → A [ϕ t ↦ α (σ' t)])
      ( \ τ → (t : ψ) → A [χ t ↦ τ t])
      ( \ τ' t → α (τ' t))
      ( \ _ υ' t → α (υ' t))
  :=
    ( ( \ τ' → first (first (is-fretract-ψ-χ A' A α)) τ'
      , \ τ → second (first (is-fretract-ψ-χ A' A α)) τ
      )
    , \ τ' → second (is-fretract-ψ-χ A' A α) τ'
    )
```

### Isomorphisms of shape inclusions

Consider two shape inclusions `ϕ ⊂ ψ` and `ζ ⊂ χ`. We want to express the fact
that there is an isomorphism `ψ ≅ χ` of shapes which restricts to an isomorphism
`ϕ ≅ ζ`. Since shapes are not types themselves, the best we can currently do is
describe this isomorphism on representables.

```rzk
#def isomorphism-shape-inclusions
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( J : CUBE)
  ( χ : J → TOPE)
  ( ζ : χ → TOPE)
  : U
  :=
    ( Σ ( f : (A : U) → Equiv (ζ → A) (ϕ → A))
      , ( ( A : U)
        → ( σ : ζ → A)
        → ( Equiv
            ( ( t : χ) → A [ζ t ↦ σ t])
            ( ( t : ψ) → A [ϕ t ↦ first (f A) σ t]))))

#def functorial-isomorphism-shape-inclusions
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( J : CUBE)
  ( χ : J → TOPE)
  ( ζ : χ → TOPE)
  : U
  :=
  Σ ( ( f , F) : isomorphism-shape-inclusions I ψ ϕ J χ ζ)
  , ( Σ ( e
 : ( A' : U)
        → ( A : U)
        → ( α : A' → A)
        → ( σ' : ζ → A')
        → ( ( \ (t : I | ϕ t) → α (first (f A') σ' t))
          = ( first (f A) (\ t → α (σ' t)))))
      , ( ( A' : U)
        → ( A : U)
        → ( α : A' → A)
        → ( σ' : ζ → A')
        → ( τ' : (t : χ) → A' [ζ t ↦ σ' t])
        → ( ( transport (ϕ → A) (\ σ → (t : ψ) → A [ϕ t ↦ σ t])
              ( \ (t : I | ϕ t) → α (first (f A') σ' t))
              ( first (f A) (\ t → α (σ' t)))
              ( e A' A α σ')
              ( \ (t : ψ) → α (first (F A' σ') τ' t)))
            = ( first (F A (\ (t : ζ) → α (σ' t))) (\ (t : χ) → α (τ' t))))))
```

In practice, the isomorphisms are usually given via an explicit formula, which
would define a map `ψ → ϕ` if `ψ` and `ϕ` were themselves types. In this case
all the coherences are just `refl`, hence it is easy to produce a term of type
`functorial-isomorphism-shape-inclusions I ψ ϕ J χ ζ`.

For example, consider the two shape inclusions `{0} ⊂ Δ¹` (subshapes of `2`) and
`{1} ⊂ right-leg-of-Λ` (subshapes of `2 × 2`), where

```rzk
#def right-leg-of-Λ
  : Λ → TOPE
  := \ (t , s) → t ≡ 1₂
```

These two shape inclusions are canonically isomorphic via the formulas

```
-- not valid rzk code
#def f : Δ¹ → right-leg-of-Λ
  \ s → (1₂ , s)

#def g : right-leg-of-Λ → Δ¹
  \ (t , s) → s
```

We turn these formulas into a functorial shape inclusion as follows.
Unfortunately we have to repeat the same formula multiple times, leading to some
ugly boilerplate code.

```rzk
#def isomorphism-0-Δ¹-1-right-leg-of-Λ
  : isomorphism-shape-inclusions
    ( 2 × 2) (\ ts → right-leg-of-Λ ts) (\ (t , s) → t ≡ 1₂ ∧ s ≡ 0₂)
    2 Δ¹ (\ t → t ≡ 0₂)
  :=
    ( \ A →
      ( \ τ (t , s) → τ s
      , ( ( \ υ s → υ (1₂ , s) , \ _ → refl)
        , ( \ υ s → υ (1₂ , s) , \ _ → refl)))
    , \ A _ →
      ( \ τ (t , s) → τ s
      , ( ( \ υ s → υ (1₂ , s) , \ _ → refl)
        , ( \ υ s → υ (1₂ , s) , \ _ → refl))))

#def functorial-isomorphism-0-Δ¹-1-right-leg-of-Λ
  : functorial-isomorphism-shape-inclusions
    ( 2 × 2) (\ ts → right-leg-of-Λ ts) (\ (t , s) → t ≡ 1₂ ∧ s ≡ 0₂)
    2 Δ¹ (\ t → t ≡ 0₂)
  :=
    ( isomorphism-0-Δ¹-1-right-leg-of-Λ
    , ( \ _ _ _ _ → refl , \ _ _ _ _ _ → refl))
```

### Functorial retracts of shape inclusions

We want to express what it means for a shape inclusion `ζ ⊂ χ` to be a retract
of another shape inclusion `ϕ ⊂ ψ`.

If these shapes were types, we would require a commutative diagram

```
ζ ⊂ χ
↓   ↓
ϕ ⊂ ψ
↓   ↓
ζ ⊂ χ
```

such that the vertical composites are the identity. As before, we cannot say
this directly; instead we express this property on representables. Since the
upper vertical maps are necessarily monomorphisms, we may we may assume up to
isomorphism (which we already dealt with) that `ζ ⊂ χ` are actual subshapes of
`ϕ ⊂ ψ`.

We observe that we must have `ζ = χ ∧ ϕ`. Thus we have the following setting:

```rzk
#section retracts-shape-inclusions

#variable I : CUBE
#variable ψ : I → TOPE
#variables ϕ χ : ψ → TOPE
-- ζ := χ ∧ ϕ

#def retract-shape-inclusion
  : U
  :=
  Σ ( s
 : ( A : U)
    → ( σ : (t : I | χ t ∧ ϕ t) → A)
    → ( t : ϕ)
    → A [ χ t ∧ ϕ t ↦ σ t])
  , ( ( A : U)
    → ( σ : (t : I | χ t ∧ ϕ t) → A)
    → ( τ : (t : χ) → A [χ t ∧ ϕ t ↦ σ t])
    → ( t : ψ)
    → A [χ t ↦ τ t , ϕ t ↦ s A σ t])

#def functorial-retract-shape-inclusion
  : U
  :=
  Σ ( ( s , S) : retract-shape-inclusion)
  , Σ ( h
 : ( A' : U)
      → ( A : U)
      → ( α : A' → A)
      → ( σ' : (t : I | χ t ∧ ϕ t) → A')
      → ( ( \ (t : I | ϕ t) → α (s A' σ' t))
        =_{ ϕ → A}
          ( s A (\ t → α (σ' t)))))
    , ( ( A' : U)
      → ( A : U)
      → ( α : A' → A)
      → ( σ' : (t : I | χ t ∧ ϕ t) → A')
      → ( τ' : (t : χ) → A' [χ t ∧ ϕ t ↦ σ' t])
      → ( ( transport
            ( ( t : ϕ) → A [χ t ∧ ϕ t ↦ α (σ' t)])
            ( \ σ → (t : ψ) → A [χ t ↦ α (τ' t) , ϕ t ↦ σ t])
            ( \ t → α (s A' σ' t))
            ( \ t → s A (\ t' → α (σ' t')) t)
            ( h A' A α σ')
            ( \ t → α (S A' σ' τ' t)))
        =_{ (t : ψ) → A [ϕ t ↦ s A (\ t' → α (τ' t')) t]}
          ( S A (\ t → α (σ' t)) (\ t → α (τ' t)))))

#end retracts-shape-inclusions
```

For example the pair `{00} ⊂ Δ²` is a retract of `{0} × Δ¹ ⊂ Δ¹ × Δ¹`.

```rzk
#def functorial-retract-00-Δ²-0Δ¹-Δ¹×Δ¹
  : functorial-retract-shape-inclusion (2 × 2)
    ( Δ¹×Δ¹) (\ (t , _) → t ≡ 0₂)
    ( \ ts → Δ² ts)
  :=
  ( ( ( \ _ f (t , s) → recOR (t ≤ s ↦ f (t , t) , s ≤ t ↦ f (t , s)))
    , ( \ _ _ f (t , s) → recOR (t ≤ s ↦ f (t , t) , s ≤ t ↦ f (t , s))))
  , ( \ _ _ _ _ → refl , \ _ _ _ _ _ → refl))

```

For completeness we verify that the intesection `Δ² ∧ {0}×Δ¹` is indeed `{00}`.

```rzk
#def verify-functorial-retract-0-Δ²-0Δ¹-Δ¹×Δ¹
  ( A : U)
  : ( ( shape-intersection (2 × 2) (\ ts → Δ² ts) (\ (t , _) → t ≡ 0₂) → A)
    = ( ( ( t , s) : 2 × 2 | t ≡ 0₂ ∧ s ≡ 0₂) → A))
  := refl
```
