# Segal Types

These formalisations correspond to Section 5 of the RS17 paper.

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Prerequisites

- `hott/01-paths.rzk.md` - We require basic path algebra.
- `hott/02-contractible.rzk.md` - We require the notion of contractible types
  and their data.
- `hott/total-space.md` — We rely on
  `#!rzk is-equiv-projection-contractible-fibers` and
  `#!rzk projection-total-type` in the proof of Theorem 5.5.
- `02-simplicial-type-theory.rzk.md` — We rely on definitions of simplicies and
  their subshapes.
- `03-extension-types.rzk.md` — We use the fubini theorem and extension
  extensionality.

Some of the definitions in this file rely on function extensionality and
extension extensionality:

```rzk
#assume funext : FunExt
#assume weakextext : WeakExtExt
#assume extext : ExtExt
```

## Hom types

Extension types are used to define the type of arrows between fixed terms:

<svg style="float: right" viewBox="0 0 200 60" width="150" height="60">
  <polyline points="40,30 160,30" stroke="blue" stroke-width="3" marker-end="url(#arrow-blue)"></polyline>
  <text x="30" y="30">x</text>
  <text x="170" y="30">y</text>
</svg>

```rzk title="RS17, Definition 5.1"
#def hom
  ( A : U)
  ( x y : A)
  : U
  :=
    ( t : Δ¹) →
    A [ t ≡ 0₂ ↦ x ,  -- the left endpoint is exactly x
        t ≡ 1₂ ↦ y]   -- the right endpoint is exactly y

```

For each `a : A`, the total types of the representables `\ z → hom A a z` and
`\ z → hom A z a` are called the coslice and slice, respectively.

```rzk
#def coslice
  ( A : U)
  ( a : A)
  : U
  := Σ ( z : A) , (hom A a z)

#def slice
  ( A : U)
  ( a : A)
  : U
  := Σ (z : A) , (hom A z a)
```

The types `coslice A a` and `slice A a` are functorial in `A` in the following
sense:

```rzk
#def coslice-fun
  (A B : U)
  (f : A → B)
  (a : A)
  : coslice A a → coslice B (f a)
  :=
    \ (a', g) → (f a', \ t → f (g t))

#def slice-fun
  (A B : U)
  (f : A → B)
  (a : A)
  : slice A a → slice B (f a)
  :=
    \ (a', g) → (f a', \ t → f (g t))
```

Slices and coslices can also be defined directly as extension types:

```rzk
#section coslice-as-extension-type
#variable A : U
#variable a : A

#def coslice'
  : U
  := ( t : Δ¹) → A [t ≡ 0₂ ↦ a]

#def coslice'-coslice
  : coslice A a → coslice'
  := \ (_, f) → f

#def coslice-coslice'
  : coslice' → coslice A a
  := \ f → ( f 1₂ , \ t → f t) -- does not typecheck after η-reduction

#def is-id-coslice-coslice'-coslice
  ( (a', f) : coslice A a)
  : ( coslice-coslice' ( coslice'-coslice (a', f)) = (a', f))
  :=
    eq-pair A (hom A a)
      ( coslice-coslice' ( coslice'-coslice (a', f))) (a', f)
      (refl, refl)

#def is-id-coslice'-coslice-coslice'
  ( f : coslice')
  : ( coslice'-coslice ( coslice-coslice' f) = f)
  :=
    refl

#def is-equiv-coslice'-coslice
  : is-equiv (coslice A a) coslice' coslice'-coslice
  :=
    ( ( coslice-coslice', is-id-coslice-coslice'-coslice),
      ( coslice-coslice', is-id-coslice'-coslice-coslice')
    )

#def is-equiv-coslice-coslice'
  : is-equiv coslice' (coslice A a)  coslice-coslice'
  :=
    ( ( coslice'-coslice, is-id-coslice'-coslice-coslice'),
      ( coslice'-coslice, is-id-coslice-coslice'-coslice)
    )

#end coslice-as-extension-type

#section slice-as-extension-type
#variable A : U
#variable a : A

#def slice'
  : U
  := ( t : Δ¹) → A[t ≡ 1₂ ↦ a]

#def slice'-slice
  : slice A a → slice'
  := \ (_, f) → f

#def slice-slice'
  : slice' → slice A a
  := \ f → ( f 0₂ , \ t → f t) -- does not typecheck after η-reduction

#def is-id-slice-slice'-slice
  ( (a', f) : slice A a)
  : ( slice-slice' ( slice'-slice (a', f)) = (a', f))
  :=
    eq-pair A (\ a' → hom A a' a)
      ( slice-slice' ( slice'-slice (a', f))) (a', f)
      (refl, refl)

#def is-id-slice'-slice-slice'
  ( f : slice')
  : ( slice'-slice ( slice-slice' f) = f)
  :=
    refl

#def is-equiv-slice'-slice
  : is-equiv (slice A a) slice' slice'-slice
  :=
    ( ( slice-slice', is-id-slice-slice'-slice),
      ( slice-slice', is-id-slice'-slice-slice')
    )

#def is-equiv-slice-slice'
  : is-equiv slice' (slice A a)  slice-slice'
  :=
    ( ( slice'-slice, is-id-slice'-slice-slice'),
      ( slice'-slice, is-id-slice-slice'-slice)
    )

#end slice-as-extension-type
```

Extension types are also used to define the type of commutative triangles:

<svg style="float: right" viewBox="0 0 200 200" width="150" height="200">
  <path style="fill: rgb(0,128,255,0.5); stroke-cap: round;" d="M 52 40 L 160 40 L 160 148 Z"></path>
  <polyline points="40,30 160,30" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="170,40 170,160" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="40,40 160,160" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <text x="30" y="30">x</text>
  <text x="170" y="30">y</text>
  <text x="170" y="170">z</text>
  <text x="100" y="15">f</text>
  <text x="185" y="100">g</text>
  <text x="90" y="110">h</text>
</svg>

```rzk title="RS17, Definition 5.2"
#def hom2
  ( A : U)
  ( x y z : A)
  ( f : hom A x y)
  ( g : hom A y z)
  ( h : hom A x z)
  : U
  :=
    ( (t₁ , t₂) : Δ²) →
    A [ t₂ ≡ 0₂ ↦ f t₁ ,  -- the top edge is exactly `f`,
        t₁ ≡ 1₂ ↦ g t₂ ,  -- the right edge is exactly `g`, and
        t₂ ≡ t₁ ↦ h t₂]   -- the diagonal is exactly `h`
```

## Arrow types

We define the arrow type:

```rzk
#def arr
  ( A : U)
  : U
  := Δ¹ → A
```

For later convenience we give an alternative characterizations of the arrow
type.

```rzk
#def fibered-arr
  ( A : U)
  : U
  := Σ (x : A) , (Σ (y : A) , hom A x y)

#def fibered-arr-free-arr
  ( A : U)
  : arr A → fibered-arr A
  := \ k → (k 0₂ , (k 1₂ , k))

#def is-equiv-fibered-arr-free-arr
  ( A : U)
  : is-equiv (arr A) (fibered-arr A) (fibered-arr-free-arr A)
  :=
    ( ( (\ (_ , (_ , f)) → f) , (\ _ → refl))
    , ( (\ (_ , (_ , f)) → f) , (\ _ → refl)))

#def equiv-fibered-arr-free-arr
  ( A : U)
  : Equiv (arr A) (fibered-arr A)
  := (fibered-arr-free-arr A , is-equiv-fibered-arr-free-arr A)
```

And the corresponding uncurried version.

```rzk
#def fibered-arr'
  ( A : U)
  : U
  :=
    Σ ((a,b) : product A A), hom A a b

#def fibered-arr-free-arr'
  ( A : U)
  : arr A → fibered-arr' A
  := \ σ → ((σ 0₂ , σ 1₂) , σ)

#def is-equiv-fibered-arr-free-arr'
  ( A : U)
  : is-equiv (arr A) (fibered-arr' A) (fibered-arr-free-arr' A)
  :=
    ( ( (\ ((_ , _) , σ) → σ) , (\ _ → refl))
    , ( (\ ((_ , _) , σ) → σ) , (\ _ → refl)))
```

## The Segal condition

A type is **Segal** if every composable pair of arrows has a unique composite.
Note this is a considerable simplification of the usual Segal condition, which
also requires homotopical uniqueness of higher-order composites.

```rzk title="RS17, Definition 5.3"
#def is-segal
  ( A : U)
  : U
  :=
    (x : A) → (y : A) → (z : A) →
    (f : hom A x y) → (g : hom A y z) →
    is-contr (Σ (h : hom A x z) , (hom2 A x y z f g h))
```

Segal types have a composition functor and witnesses to the composition
relation. Composition is written in diagrammatic order to match the order of
arguments in `#!rzk is-segal`.

```rzk
#def comp-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y z : A)
  ( f : hom A x y)
  ( g : hom A y z)
  : hom A x z
  := first (first (is-segal-A x y z f g))

#def witness-comp-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y z : A)
  ( f : hom A x y)
  ( g : hom A y z)
  : hom2 A x y z f g (comp-is-segal A is-segal-A x y z f g)
  := second (first (is-segal-A x y z f g))
```

Composition in a Segal type is unique in the following sense. If there is a
witness that an arrow $h$ is a composite of $f$ and $g$, then the specified
composite equals $h$.

<svg style="float: right" viewBox="0 0 200 380" width="125">
  <path style="fill: rgb(175,175,175,0.5); stroke-cap: round;" d="M 52 40 L 160 40 L 160 148 Z"></path>
  <polyline points="40,30 160,30" stroke="grey" stroke-width="3" marker-end="url(#arrow-grey)"></polyline>
  <polyline points="170,45 170,160" stroke="grey" stroke-width="3" marker-end="url(#arrow-grey)"></polyline>
  <polyline points="40,40 160,160" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <text x="30" y="30" fill="grey">x</text>
  <text x="170" y="30" fill="grey">y</text>
  <text x="170" y="170" fill="grey">z</text>
  <text x="100" y="15" fill="grey">f</text>
  <text x="185" y="100" fill="grey">g</text>
  <text x="90" y="110">h</text>
  <text x="125" y="75" fill="grey">α</text>
  <text x="100" y="145" fill="red" rotate="90" style="font-size: 50px">=</text>
  <path style="fill: rgb(128,0,0,0.5); stroke-cap: round;" d="M 52 240 L 160 240 L 160 348 Z"></path>
  <polyline points="40,230 160,230" stroke="grey" stroke-width="3" marker-end="url(#arrow-grey)"></polyline>
  <polyline points="170,245 170,360" stroke="grey" stroke-width="3" marker-end="url(#arrow-grey)"></polyline>
  <polyline points="40,240 160,360" stroke="red" stroke-width="3" marker-end="url(#arrow-red)"></polyline>
  <text x="30" y="230" fill="grey">x</text>
  <text x="170" y="230" fill="grey">y</text>
  <text x="170" y="370" fill="grey">z</text>
  <text x="100" y="215" fill="grey">f</text>
  <text x="185" y="300" fill="grey">g</text>
  <text x="90" y="310" transform="rotate(45, 90, 310)" fill="red">comp-is-segal</text>
  <text x="120" y="280" fill="rgb(128,0,0)" transform="rotate(45, 120, 280)" style="font-size: 10px">witness-comp-is-segal</text>
</svg>

```rzk
#def uniqueness-comp-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y z : A)
  ( f : hom A x y)
  ( g : hom A y z)
  ( h : hom A x z)
  ( alpha : hom2 A x y z f g h)
  : ( comp-is-segal A is-segal-A x y z f g) = h
  :=
    first-path-Σ
      ( hom A x z)
      ( hom2 A x y z f g)
      ( comp-is-segal A is-segal-A x y z f g ,
        witness-comp-is-segal A is-segal-A x y z f g)
      ( h , alpha)
      ( homotopy-contraction
        ( Σ (k : hom A x z) , (hom2 A x y z f g k))
        ( is-segal-A x y z f g)
        ( h , alpha))
```

## Characterizing Segal types

Our aim is to prove that a type is Segal if and only if the
`#!rzk horn-restriction` map, defined below, is an equivalence.

<svg style="float: right" viewBox="0 0 200 180" width="150" height="150">
  <polyline points="40,30 160,30" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="170,45 170,160" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <text x="30" y="30">x</text>
  <text x="170" y="30">y</text>
  <text x="170" y="170">z</text>
  <text x="100" y="15">f</text>
  <text x="185" y="100">g</text>
</svg>

A pair of composable arrows form a horn.

```rzk
#def horn
  ( A : U)
  ( x y z : A)
  ( f : hom A x y)
  ( g : hom A y z)
  : Λ → A
  :=
    \ (t , s) →
    recOR
      ( s ≡ 0₂ ↦ f t ,
        t ≡ 1₂ ↦ g s)
```

The underlying horn of a simplex:

```rzk
#def horn-restriction
  ( A : U)
  : (Δ² → A) → (Λ → A)
  := \ f t → f t
```

This provides an alternate definition of Segal types as types which are local
for the inclusion `Λ ⊂ Δ¹`.

```rzk
#def is-local-horn-inclusion
  : U → U
  := is-local-type (2 × 2) Δ² (\ t → Λ t)

#def unpack-is-local-horn-inclusion
  ( A : U)
  : is-local-horn-inclusion A = is-equiv (Δ² → A) (Λ → A) (horn-restriction A)
  := refl
```

Now we prove this definition is equivalent to the original one. Here, we prove
the equivalence used in [RS17, Theorem 5.5]. However, we do this by constructing
the equivalence directly, instead of using a composition of equivalences, as it
is easier to write down and it computes better (we can use refl for the
witnesses of the equivalence).

```rzk
#def compositions-are-horn-fillings
  ( A : U)
  ( x y z : A)
  ( f : hom A x y)
  ( g : hom A y z)
  : Equiv
    ( Σ (h : hom A x z) , (hom2 A x y z f g h))
    ( (t : Δ²) → A [Λ t ↦ horn A x y z f g t])
  :=
    ( \ hh t → (second hh) t ,
      ( ( \ k → (\ t → k (t , t) , \ (t , s) → k (t , s)) ,
          \ hh → refl) ,
        ( \ k → (\ t → k (t , t) , \ (t , s) → k (t , s)) ,
          \ hh → refl)))

#def equiv-horn-restriction
  ( A : U)
  : Equiv
    ( Δ² → A)
    ( Σ ( k : Λ → A) ,
        ( Σ ( h : hom A (k (0₂ , 0₂)) (k (1₂ , 1₂))) ,
            ( hom2 A
              ( k (0₂ , 0₂)) (k (1₂ , 0₂)) (k (1₂ , 1₂))
              ( \ t → k (t , 0₂)) (\ t → k (1₂ , t))
              ( h))))
  :=
    ( \ k →
      ( ( \ t → k t) ,
        ( \ t → k (t , t) , \ t → k t)) ,
      ( ( \ khh t → (second (second khh)) t , \ k → refl) ,
        ( \ khh t → (second (second khh)) t , \ k → refl)))
```

```rzk title="RS17, Theorem 5.5 (the hard direction)"
#def equiv-horn-restriction-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  : Equiv (Δ² → A) (Λ → A)
  :=
    equiv-comp
      ( Δ² → A)
      ( Σ ( k : Λ → A) ,
          ( Σ ( h : hom A (k (0₂ , 0₂)) (k (1₂ , 1₂))) ,
              ( hom2 A
                ( k (0₂ , 0₂)) (k (1₂ , 0₂)) (k (1₂ , 1₂))
                ( \ t → k (t , 0₂)) (\ t → k (1₂ , t))
                ( h))))
      ( Λ → A)
      ( equiv-horn-restriction A)
      ( projection-total-type
        ( Λ → A)
        ( \ k →
          Σ ( h : hom A (k (0₂ , 0₂)) (k (1₂ , 1₂))) ,
            ( hom2 A
              ( k (0₂ , 0₂)) (k (1₂ , 0₂)) (k (1₂ , 1₂))
              ( \ t → k (t , 0₂)) (\ t → k (1₂ , t))
              ( h))) ,
      ( is-equiv-projection-contractible-fibers
          ( Λ → A)
          ( \ k →
            Σ ( h : hom A (k (0₂ , 0₂)) (k (1₂ , 1₂))) ,
              ( hom2 A
                ( k (0₂ , 0₂)) (k (1₂ , 0₂)) (k (1₂ , 1₂))
                ( \ t → k (t , 0₂)) (\ t → k (1₂ , t))
                ( h)))
          ( \ k →
            is-segal-A
              ( k (0₂ , 0₂)) (k (1₂ , 0₂)) (k (1₂ , 1₂))
              ( \ t → k (t , 0₂)) (\ t → k (1₂ , t)))))
```

We verify that the mapping in `#!rzk Segal-equiv-horn-restriction A is-segal-A`
is exactly `#!rzk horn-restriction A`.

```rzk
#def test-equiv-horn-restriction-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  : (first (equiv-horn-restriction-is-segal A is-segal-A)) = (horn-restriction A)
  := refl
```

```rzk title="Segal types are types that are local at the horn inclusion"
#def is-local-horn-inclusion-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  : is-local-horn-inclusion A
  := second (equiv-horn-restriction-is-segal A is-segal-A)
```

```rzk title="Types that are local at the horn inclusion are Segal types"
#def is-segal-is-local-horn-inclusion
  ( A : U)
  ( is-local-horn-inclusion-A : is-local-horn-inclusion A)
  : is-segal A
  :=
    \ x y z f g →
    contractible-fibers-is-equiv-projection
      ( Λ → A)
      ( \ k →
        Σ ( h : hom A (k (0₂ , 0₂)) (k (1₂ , 1₂))) ,
          ( hom2 A
            ( k (0₂ , 0₂)) (k (1₂ , 0₂)) (k (1₂ , 1₂))
            ( \ t → k (t , 0₂))
            ( \ t → k (1₂ , t))
            ( h)))
      ( second
        ( equiv-comp
          ( Σ ( k : Λ → A) ,
            Σ ( h : hom A (k (0₂ , 0₂)) (k (1₂ , 1₂))) ,
              ( hom2 A
                ( k (0₂ , 0₂)) (k (1₂ , 0₂)) (k (1₂ , 1₂))
                ( \ t → k (t , 0₂))
                ( \ t → k (1₂ , t))
                ( h)))
          ( Δ² → A)
          ( Λ  → A)
          ( inv-equiv
            ( Δ² → A)
            ( Σ ( k : Λ → A) ,
              Σ ( h : hom A (k (0₂ , 0₂)) (k (1₂ , 1₂))) ,
                ( hom2 A
                  ( k (0₂ , 0₂)) (k (1₂ , 0₂)) (k (1₂ , 1₂))
                  ( \ t → k (t , 0₂))
                  ( \ t → k (1₂ , t))
                  ( h)))
            ( equiv-horn-restriction A))
          ( horn-restriction A , is-local-horn-inclusion-A)))
      ( horn A x y z f g)
```

We have now proven that both notions of Segal types are logically equivalent.

```rzk title="RS17, Theorem 5.5"
#def is-segal-iff-is-local-horn-inclusion
  ( A : U)
  : iff (is-segal A) (is-local-horn-inclusion A)
  := (is-local-horn-inclusion-is-segal A , is-segal-is-local-horn-inclusion A)
```

Similarly, Segal types are characterized by having unique extensions along
`Λ ⊂ Δ²`.

```rzk
#def is-segal-has-unique-inner-extensions
  ( A : U)
  ( has-inner-ue-A : has-unique-extensions (2 × 2) (Δ²) (\ t → Λ t) A)
  : is-segal A
  :=
    is-segal-is-local-horn-inclusion A
    ( is-local-type-has-unique-extensions (2 × 2) (Δ²) (\ t → Λ t) A
      has-inner-ue-A)

#def has-unique-inner-extensions-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  : has-unique-extensions (2 × 2) (Δ²) (\ t → Λ t) A
  :=
    has-unique-extensions-is-local-type (2 × 2) (Δ²) (\ t → Λ t) A
    ( is-local-horn-inclusion-is-segal A is-segal-A)
```

## Segal function and extension types

Using the new characterization of Segal types, we can show that the type of
functions or extensions into a family of Segal types is again a Segal type. For
instance if $X$ is a type and $A : X → U$ is such that $A x$ is a Segal type for
all $x$ then $(x : X) → A x$ is a Segal type.

```rzk title="RS17, Corollary 5.6(i)"
#def is-local-horn-inclusion-function-type uses (funext)
  ( X : U)
  ( A : X → U)
  ( fiberwise-is-segal-A : (x : X) → is-local-horn-inclusion (A x))
  : is-local-horn-inclusion ((x : X) → A x)
  :=
    is-equiv-triple-comp
      ( Δ² → ((x : X) → A x))
      ( (x : X) → Δ² → A x)
      ( (x : X) → Λ → A x)
      ( Λ → ((x : X) → A x))
      ( \ g x t → g t x) -- first equivalence
      ( second (flip-ext-fun
        ( 2 × 2)
        ( Δ²)
        ( \ t → BOT)
        ( X)
        ( \ t → A)
        ( \ t → recBOT)))
      ( \ h x t → h x t) -- second equivalence
      ( second (equiv-function-equiv-family
        ( funext)
        ( X)
        ( \ x → (Δ² → A x))
        ( \ x → (Λ → A x))
        ( \ x → (horn-restriction (A x) , fiberwise-is-segal-A x))))
      ( \ h t x → (h x) t) -- third equivalence
      ( second (flip-ext-fun-inv
        ( 2 × 2)
        ( Λ)
        ( \ t → BOT)
        ( X)
        ( \ t → A)
        ( \ t → recBOT)))

#def is-segal-function-type uses (funext)
  ( X : U)
  ( A : X → U)
  ( fiberwise-is-segal-A : (x : X) → is-segal (A x))
  : is-segal ((x : X) → A x)
  :=
    is-segal-is-local-horn-inclusion
      ( (x : X) → A x)
      ( is-local-horn-inclusion-function-type
        ( X) (A)
        ( \ x → is-local-horn-inclusion-is-segal (A x)(fiberwise-is-segal-A x)))
```

If $X$ is a shape and $A : X → U$ is such that $A x$ is a Segal type for all $x$
then $(x : X) → A x$ is a Segal type.

```rzk title="RS17, Corollary 5.6(ii)"
#def is-local-horn-inclusion-extension-type uses (extext)
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( A : ψ → U)
  ( fiberwise-is-segal-A : (s : ψ) → is-local-horn-inclusion (A s))
  : is-local-horn-inclusion ((s : ψ) → A s)
  :=
    is-equiv-triple-comp
      ( Δ² → (s : ψ) → A s)
      ( (s : ψ) → Δ² → A s)
      ( (s : ψ) → Λ → A s)
      ( Λ → (s : ψ) → A s)
      ( \ g s t → g t s)  -- first equivalence
      ( second
        ( fubini
          ( 2 × 2)
          ( I)
          ( Δ²)
          ( \ t → BOT)
          ( ψ)
          ( \ s → BOT)
          ( \ t s → A s)
          ( \ u → recBOT)))
      ( \ h s t → h s t) -- second equivalence
      ( second (equiv-extensions-BOT-equiv extext I ψ
        ( \ s → Δ² → A s)
        ( \ s → Λ → A s)
        ( \ s → (horn-restriction (A s) , fiberwise-is-segal-A s))))
      ( \ h t s → (h s) t) -- third equivalence
      ( second
        ( fubini
          ( I)
          ( 2 × 2)
          ( ψ)
          ( \ s → BOT)
          ( Λ)
          ( \ t → BOT)
          ( \ s t → A s)
          ( \ u → recBOT)))

#def is-segal-extension-type uses (extext)
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( A : ψ → U)
  ( fiberwise-is-segal-A : (s : ψ) → is-segal (A s))
  : is-segal ((s : ψ) → A s)
  :=
    is-segal-is-local-horn-inclusion
      ( (s : ψ) → A s)
      ( is-local-horn-inclusion-extension-type
        ( I) (ψ) (A)
        ( \ s → is-local-horn-inclusion-is-segal (A s)(fiberwise-is-segal-A s)))
```

In particular, the arrow type of a Segal type is Segal.

```rzk title="RS17, Corollary 5.6(ii), special case for locality at the horn inclusion"
#def is-local-horn-inclusion-arr uses (extext)
  ( A : U)
  ( is-segal-A : is-local-horn-inclusion A)
  : is-local-horn-inclusion (arr A)
  :=
    is-local-horn-inclusion-extension-type
      ( 2)
      ( Δ¹)
      ( \ _ → A)
      ( \ _ → is-segal-A)
```

```rzk title="RS17, Corollary 5.6(ii), special case for the Segal condition"
#def is-segal-arr uses (extext)
  ( A : U)
  ( is-segal-A : is-segal A)
  : is-segal (arr A)
  :=
    is-segal-extension-type
      ( 2)
      ( Δ¹)
      ( \ _ → A)
      ( \ _ → is-segal-A)
```

## Identity

All types have identity arrows and witnesses to the identity composition law.

<svg style="float: right" viewBox="0 0 200 180" width="150" height="150">
  <polyline points="40,30 160,30" stroke="red" stroke-width="3" marker-end="url(#arrow-red)"></polyline>
  <text x="30" y="30">x</text>
  <text x="170" y="30">x</text>
  <text x="100" y="15" fill="red">x</text>
</svg>

```rzk title="RS17, Definition 5.7"
#def id-hom
  ( A : U)
  ( x : A)
  : hom A x x
  := \ t → x
```

Witness for the right identity law:

<svg style="float: right" viewBox="0 0 200 180" width="150" height="150">
  <path style="fill: rgb(255,128,0,0.5); stroke-cap: round;" d="M 52 40 L 160 40 L 160 148 Z"></path>
  <polyline points="40,30 160,30" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="170,45 170,160" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="40,40 160,160" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <text x="30" y="30">x</text>
  <text x="170" y="30">y</text>
  <text x="170" y="170">y</text>
  <text x="100" y="15">f</text>
  <text x="185" y="100">y</text>
  <text x="90" y="110">f</text>
  <text x="125" y="75" stroke="red" fill="red">f</text>
</svg>

```rzk title="RS17, Proposition 5.8a"
#def comp-id-witness
  ( A : U)
  ( x y : A)
  ( f : hom A x y)
  : hom2 A x y y f (id-hom A y) f
  := \ (t , s) → f t
```

Witness for the left identity law:

<svg style="float: right" viewBox="0 0 200 180" width="150" height="150">
  <path style="fill: rgb(255,128,0,0.5); stroke-cap: round;" d="M 52 40 L 160 40 L 160 148 Z"></path>
  <polyline points="40,30 160,30" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="170,45 170,160" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="40,40 160,160" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <text x="30" y="30">x</text>
  <text x="170" y="30">x</text>
  <text x="170" y="170">y</text>
  <text x="100" y="15">x</text>
  <text x="185" y="100">f</text>
  <text x="90" y="110">f</text>
  <text x="125" y="75" stroke="red" fill="red">f</text>
</svg>

```rzk title="RS17, Proposition 5.8b"
#def id-comp-witness
  ( A : U)
  ( x y : A)
  ( f : hom A x y)
  : hom2 A x x y (id-hom A x) f f
  := \ (t , s) → f s
```

In a Segal type, where composition is unique, it follows that composition with
an identity arrow recovers the original arrow. Thus, an identity axiom was not
needed in the definition of Segal types.

```rzk title="If A is Segal then the right unit law holds"
#def comp-id-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  ( f : hom A x y)
  : ( comp-is-segal A is-segal-A x y y f (id-hom A y)) = f
  :=
    uniqueness-comp-is-segal
      ( A)
      ( is-segal-A)
      ( x) (y) (y)
      ( f)
      ( id-hom A y)
      ( f)
      ( comp-id-witness A x y f)
```

```rzk title="If A is Segal then the left unit law holds"
#def id-comp-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  ( f : hom A x y)
  : (comp-is-segal A is-segal-A x x y (id-hom A x) f) =_{hom A x y} f
  :=
    uniqueness-comp-is-segal
      ( A)
      ( is-segal-A)
      ( x) (x) (y)
      ( id-hom A x)
      ( f)
      ( f)
      ( id-comp-witness A x y f)
```

## Associativity

We now prove that composition in a Segal type is associative, by using the fact
that the type of arrows in a Segal type is itself a Segal type.

<svg style="float: right" viewBox="0 0 200 180" width="150" height="150">
  <path style="fill: rgb(128,128,128,0.5); stroke-cap: round;" d="M 52 40 L 160 40 L 160 148 Z"></path>
  <path style="fill: rgb(256,128,0,0.5); stroke-cap: round;" d="M 40 52 L 40 160 L 148 160 Z"></path>
  <polyline points="40,30 160,30" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="170,45 170,160" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="40,40 160,160" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="30,40 30,160" stroke="red" stroke-width="3" marker-end="url(#arrow-red)"></polyline>
  <polyline points="45,170 160,170" stroke="red" stroke-width="3" marker-end="url(#arrow-red)"></polyline>
  <text x="30" y="30">•</text>
  <text x="170" y="30">•</text>
  <text x="170" y="170">•</text>
  <text x="30" y="170" fill="red">•</text>
</svg>

```rzk
#def unfolding-square
  ( A : U)
  ( triangle : Δ² → A)
  : Δ¹×Δ¹ → A
  :=
    \ (t , s) →
    recOR
      ( t ≤ s ↦ triangle (s , t) ,
        s ≤ t ↦ triangle (t , s))
```

For use in the proof of associativity:

<svg style="float: right" viewBox="0 0 200 200" width="150" height="150">
  <path style="fill: rgb(256,128,0,0.5); stroke-cap: round;" d="M 52 40 L 160 40 L 160 148 Z"></path>
  <path style="fill: rgb(256,128,0,0.5); stroke-cap: round;" d="M 40 52 L 40 160 L 148 160 Z"></path>
  <polyline points="40,30 160,30" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="170,45 170,160" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="40,40 160,160" stroke="red" stroke-width="3" marker-end="url(#arrow-red)"></polyline>
  <polyline points="30,40 30,160" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="45,170 160,170" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <text x="30" y="30">x</text>
  <text x="170" y="30">y</text>
  <text x="170" y="170">z</text>
  <text x="30" y="170">y</text>
  <text x="100" y="15">f</text>
  <text x="185" y="100">g</text>
  <text x="90" y="110" transform="rotate(45, 90, 110)" fill="red">comp-is-segal</text>
  <text x="100" y="190">g</text>
  <text x="15" y="100">f</text>
</svg>

```rzk
#def witness-square-comp-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y z : A)
  ( f : hom A x y)
  ( g : hom A y z)
  : Δ¹×Δ¹ → A
  := unfolding-square A (witness-comp-is-segal A is-segal-A x y z f g)
```

The `#!rzk witness-square-comp-is-segal` as an arrow in the arrow type:

<svg style="float: right" viewBox="0 0 200 200" width="150" height="150">
  <polyline points="170,45 170,160" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="30,40 30,160" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="40,100 160,100" stroke="red" stroke-width="6" marker-end="url(#arrow-red)"></polyline>
  <text x="30" y="30">x</text>
  <text x="170" y="30">y</text>
  <text x="170" y="170">z</text>
  <text x="30" y="170">y</text>
  <text x="15" y="100">f</text>
  <text x="185" y="100">g</text>
</svg>

```rzk
#def arr-in-arr-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y z : A)
  ( f : hom A x y)
  ( g : hom A y z)
  : hom (arr A) f g
  := \ t s → witness-square-comp-is-segal A is-segal-A x y z f g (t , s)
```

<svg style="float: right" viewBox="0 0 200 250" width="150" height="200">
  <polyline points="170,45 170,160" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="30,40 30,160" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="40,100 160,100" stroke="red" stroke-width="6" marker-end="url(#arrow-red)"></polyline>
  <polyline points="40,30 160,30" stroke="lightgrey" stroke-width="3"></polyline>
  <polyline points="40,170 160,170" stroke="lightgrey" stroke-width="3"></polyline>
  <path style="fill: rgb(256,128,0,0.5); stroke-cap: round;" d="M 40 100 L 160 100 L 100 130 Z"></path>
  <polyline points="100,70 100,190" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="155,105 105,130" stroke="red" stroke-width="6" marker-end="url(#arrow-red)"></polyline>
  <polyline points="45,105 95,130" stroke="red" stroke-width="6" marker-end="url(#arrow-red)"></polyline>
  <polyline points="155,35 105,55" stroke="lightgrey" stroke-width="3"></polyline>
  <polyline points="45,35 95,55" stroke="lightgrey" stroke-width="3"></polyline>
  <polyline points="155,175 105,195" stroke="lightgrey" stroke-width="3"></polyline>
  <polyline points="45,175 95,195" stroke="lightgrey" stroke-width="3"></polyline>
  <text x="30" y="30">w</text>
  <text x="170" y="30">x</text>
  <text x="30" y="170">x</text>
  <text x="170" y="170">y</text>
  <text x="100" y="60">y</text>
  <text x="100" y="200">z</text>
  <text x="15" y="100">f</text>
  <text x="185" y="100">g</text>
  <text x="90" y="150">h</text>
</svg>

```rzk
#def witness-asociative-is-segal uses (extext)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( w x y z : A)
  ( f : hom A w x)
  ( g : hom A x y)
  ( h : hom A y z)
  : hom2 (arr A) f g h
      ( arr-in-arr-is-segal A is-segal-A w x y f g)
      ( arr-in-arr-is-segal A is-segal-A x y z g h)
      ( comp-is-segal (arr A) (is-segal-arr A is-segal-A) f g h
        ( arr-in-arr-is-segal A is-segal-A w x y f g)
        ( arr-in-arr-is-segal A is-segal-A x y z g h))
  :=
    witness-comp-is-segal
      ( arr A)
      ( is-segal-arr A is-segal-A)
      ( f) ( g) ( h)
      ( arr-in-arr-is-segal A is-segal-A w x y f g)
      ( arr-in-arr-is-segal A is-segal-A x y z g h)
```

<svg style="float: right" viewBox="0 0 200 250" width="150" height="200">
  <path style="fill: rgb(256,128,0,0.5); stroke-cap: round;"
    d="M 35 35 L 165 35 L 165 165 L 102 190 Z"></path>
  <polyline points="170,45 170,160" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="30,40 95,190" stroke="red" stroke-width="3" marker-end="url(#arrow-red)"></polyline>
  <polyline points="40,40 160,160" stroke="red" stroke-width="3" marker-end="url(#arrow-red)"></polyline>
  <polyline points="160,40 110,180" stroke="red" stroke-width="3" marker-end="url(#arrow-red)"></polyline>
  <polyline points="40,30 160,30" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="155,175 110,195" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <text x="30" y="30">w</text>
  <text x="170" y="30">x</text>
  <text x="170" y="170">y</text>
  <text x="100" y="200">z</text>
  <text x="185" y="100">g</text>
  <text x="100" y="15">f</text>
  <text x="140" y="205">h</text>
</svg>

The `#!rzk witness-associative-is-segal` curries to define a diagram
$Δ²×Δ¹ → A$. The `#!rzk tetrahedron-associative-is-segal` is extracted via the
middle-simplex map $((t , s) , r) ↦ ((t , r) , s)$ from $Δ³$ to $Δ²×Δ¹$.

```rzk
#def tetrahedron-associative-is-segal uses (extext)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( w x y z : A)
  ( f : hom A w x)
  ( g : hom A x y)
  ( h : hom A y z)
  : Δ³ → A
  :=
    \ ((t , s) , r) →
    (witness-asociative-is-segal A is-segal-A w x y z f g h) (t , r) s
```

<svg style="float: right" viewBox="0 0 200 250" width="150" height="200">
  <path style="fill: rgb(128,128,128,0.5); stroke-cap: round;"
    d="M 35 35 L 165 35 L 165 165 L 102 190 Z"></path>
  <polyline points="170,45 170,160" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="30,40 95,190" stroke="red" stroke-width="3" marker-end="url(#arrow-red)"></polyline>
  <polyline points="40,40 160,160" stroke="grey" stroke-width="3" marker-end="url(#arrow-grey)"></polyline>
  <polyline points="160,40 110,180" stroke="grey" stroke-width="3" marker-end="url(#arrow-grey)"></polyline>
  <polyline points="40,30 160,30" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="155,175 110,195" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <text x="30" y="30">w</text>
  <text x="170" y="30">x</text>
  <text x="170" y="170">y</text>
  <text x="100" y="200">z</text>
  <text x="185" y="100">g</text>
  <text x="100" y="15">f</text>
  <text x="140" y="205">h</text>
</svg>

The diagonal composite of three arrows extracted from the
`#!rzk tetrahedron-associative-is-segal`.

```rzk
#def triple-comp-is-segal uses (extext)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( w x y z : A)
  ( f : hom A w x)
  ( g : hom A x y)
  ( h : hom A y z)
  : hom A w z
  :=
    \ t →
    tetrahedron-associative-is-segal A is-segal-A w x y z f g h
      ( (t , t) , t)
```

<svg style="float: right" viewBox="0 0 200 250" width="150" height="200">
  <path style="fill: rgb(128,128,128,0.5); stroke-cap: round;"
    d="M 40 35 L 165 35 L 165 160 Z"></path>
  <path style="fill: rgb(256,128,0,0.5); stroke-cap: round;"
    d="M 35 40 L 160 165 L 102 190 Z"></path>
  <polyline points="170,45 170,160" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="30,40 95,190" stroke="red" stroke-width="3" marker-end="url(#arrow-red)"></polyline>
  <polyline points="40,40 160,160" stroke="red" stroke-width="3" marker-end="url(#arrow-red)"></polyline>
  <polyline points="160,40 110,180" stroke="grey" stroke-width="3" marker-end="url(#arrow-grey)"></polyline>
  <polyline points="40,30 160,30" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="155,175 110,195" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <text x="30" y="30">w</text>
  <text x="170" y="30">x</text>
  <text x="170" y="170">y</text>
  <text x="100" y="200">z</text>
  <text x="185" y="100">g</text>
  <text x="100" y="15">f</text>
  <text x="140" y="205">h</text>
</svg>

```rzk
#def left-witness-asociative-is-segal uses (extext)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( w x y z : A)
  ( f : hom A w x)
  ( g : hom A x y)
  ( h : hom A y z)
  : hom2 A w y z
    (comp-is-segal A is-segal-A w x y f g)
    h
    (triple-comp-is-segal A is-segal-A w x y z f g h)
  :=
    \ (t , s) →
    tetrahedron-associative-is-segal A is-segal-A w x y z f g h
      ( (t , t) , s)
```

The front face:

<svg style="float: right" viewBox="0 0 200 250" width="150" height="200">
  <path style="fill: rgb(256,128,0,0.5); stroke-cap: round;"
    d="M 35 35 L 155 35 L 100 185 Z"></path>
  <path style="fill: rgb(128,128,128,0.5); stroke-cap: round;"
    d="M 165 40 L 165 165 L 115 185 Z"></path>
  <polyline points="170,45 170,160" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="30,40 95,190" stroke="red" stroke-width="3" marker-end="url(#arrow-red)"></polyline>
  <polyline points="40,40 160,160" stroke="grey" stroke-width="3" marker-end="url(#arrow-grey)"></polyline>
  <polyline points="160,40 110,180" stroke="red" stroke-width="3" marker-end="url(#arrow-red)"></polyline>
  <polyline points="40,30 160,30" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="155,175 110,195" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <text x="30" y="30">w</text>
  <text x="170" y="30">x</text>
  <text x="170" y="170">y</text>
  <text x="100" y="200">z</text>
  <text x="185" y="100">g</text>
  <text x="100" y="15">f</text>
  <text x="140" y="205">h</text>
</svg>

```rzk
#def right-witness-asociative-is-segal uses (extext)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( w x y z : A)
  ( f : hom A w x)
  ( g : hom A x y)
  ( h : hom A y z)
  : hom2 A w x z
    ( f)
    ( comp-is-segal A is-segal-A x y z g h)
    ( triple-comp-is-segal A is-segal-A w x y z f g h)
  :=
    \ (t , s) →
    tetrahedron-associative-is-segal A is-segal-A w x y z f g h
      ( (t , s) , s)
```

```rzk
#def left-associative-is-segal uses (extext)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( w x y z : A)
  ( f : hom A w x)
  ( g : hom A x y)
  ( h : hom A y z)
  : ( comp-is-segal A is-segal-A w y z (comp-is-segal A is-segal-A w x y f g) h) =
    ( triple-comp-is-segal A is-segal-A w x y z f g h)
  :=
    uniqueness-comp-is-segal
      A is-segal-A w y z (comp-is-segal A is-segal-A w x y f g) h
      ( triple-comp-is-segal A is-segal-A w x y z f g h)
      ( left-witness-asociative-is-segal A is-segal-A w x y z f g h)

#def right-associative-is-segal uses (extext)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( w x y z : A)
  ( f : hom A w x)
  ( g : hom A x y)
  ( h : hom A y z)
  : ( comp-is-segal A is-segal-A w x z f (comp-is-segal A is-segal-A x y z g h)) =
    ( triple-comp-is-segal A is-segal-A w x y z f g h)
  :=
    uniqueness-comp-is-segal
      ( A) (is-segal-A) (w) (x) (z) (f) (comp-is-segal A is-segal-A x y z g h)
      ( triple-comp-is-segal A is-segal-A w x y z f g h)
      ( right-witness-asociative-is-segal A is-segal-A w x y z f g h)
```

We conclude that Segal composition is associative.

```rzk title="RS17, Proposition 5.9"
#def associative-is-segal uses (extext)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( w x y z : A)
  ( f : hom A w x)
  ( g : hom A x y)
  ( h : hom A y z)
  : ( comp-is-segal A is-segal-A w y z (comp-is-segal A is-segal-A w x y f g) h) =
    ( comp-is-segal A is-segal-A w x z f (comp-is-segal A is-segal-A x y z g h))
  :=
    zig-zag-concat
    ( hom A w z)
    ( comp-is-segal A is-segal-A w y z (comp-is-segal A is-segal-A w x y f g) h)
    ( triple-comp-is-segal A is-segal-A w x y z f g h)
    ( comp-is-segal A is-segal-A w x z f (comp-is-segal A is-segal-A x y z g h))
    ( left-associative-is-segal A is-segal-A w x y z f g h)
    ( right-associative-is-segal A is-segal-A w x y z f g h)

#def rev-associative-is-segal uses (extext)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( w x y z : A)
  ( f : hom A w x)
  ( g : hom A x y)
  ( h : hom A y z)
  : ( comp-is-segal A is-segal-A w x z f (comp-is-segal A is-segal-A x y z g h)) =
    ( comp-is-segal A is-segal-A w y z (comp-is-segal A is-segal-A w x y f g) h)
  :=
    rev (hom A w z)
    ( comp-is-segal A is-segal-A w y z (comp-is-segal A is-segal-A w x y f g) h)
    ( comp-is-segal A is-segal-A w x z f (comp-is-segal A is-segal-A x y z g h))
    ( associative-is-segal A is-segal-A w x y z f g h)

#def postcomp-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  ( f : hom A x y)
  : (z : A) → (hom A z x) → (hom A z y)
  := \ z g → comp-is-segal A is-segal-A z x y g f

#def precomp-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  ( f : hom A x y)
  : (z : A) → (hom A y z) → (hom A x z)
  := \ z → comp-is-segal A is-segal-A x y z f
```

## Homotopies

We may define a "homotopy" to be a path between parallel arrows. In a Segal
type, homotopies are equivalent to terms in hom2 types involving an identity
arrow.

```rzk
#def map-hom2-homotopy
  ( A : U)
  ( x y : A)
  ( f g : hom A x y)
  : (f = g) → (hom2 A x x y (id-hom A x) f g)
  :=
    ind-path
      ( hom A x y)
      ( f)
      ( \ g' p' → (hom2 A x x y (id-hom A x) f g'))
      ( id-comp-witness A x y f)
      ( g)

#def map-total-hom2-homotopy
  ( A : U)
  ( x y : A)
  ( f : hom A x y)
  : ( Σ (g : hom A x y) , (f = g)) →
    ( Σ (g : hom A x y) , (hom2 A x x y (id-hom A x) f g))
  := \ (g , p) → (g , map-hom2-homotopy A x y f g p)

#def is-equiv-map-total-hom2-homotopy-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  ( f : hom A x y)
  : is-equiv
      ( Σ (g : hom A x y) , f = g)
      ( Σ (g : hom A x y) , (hom2 A x x y (id-hom A x) f g))
      ( map-total-hom2-homotopy A x y f)
  :=
    is-equiv-are-contr
      ( Σ (g : hom A x y) , (f = g))
      ( Σ (g : hom A x y) , (hom2 A x x y (id-hom A x) f g))
      ( is-contr-based-paths (hom A x y) f)
      ( is-segal-A x x y (id-hom A x) f)
      ( map-total-hom2-homotopy A x y f)
```

```rzk title="RS17, Proposition 5.10"
#def equiv-homotopy-hom2-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  ( f h : hom A x y)
  : Equiv (f = h) (hom2 A x x y (id-hom A x) f h)
  :=
    ( ( map-hom2-homotopy A x y f h) ,
      ( is-equiv-fiberwise-is-equiv-total
        ( hom A x y)
        ( \ k → (f = k))
        ( \ k → (hom2 A x x y (id-hom A x) f k))
        ( map-hom2-homotopy A x y f)
        ( is-equiv-map-total-hom2-homotopy-is-segal A is-segal-A x y f)
        ( h)))
```

A dual notion of homotopy can be defined similarly.

```rzk
#def map-hom2-homotopy'
  ( A : U)
  ( x y : A)
  ( f g : hom A x y)
  ( p : f = g)
  : (hom2 A x y y f (id-hom A y) g)
  :=
    ind-path
      ( hom A x y)
      ( f)
      ( \ g' p' → (hom2 A x y y f (id-hom A y) g'))
      ( comp-id-witness A x y f)
      ( g)
      ( p)

#def map-total-hom2-homotopy'
  ( A : U)
  ( x y : A)
  ( f : hom A x y)
  : ( Σ (g : hom A x y) , (f = g)) →
    ( Σ (g : hom A x y) , (hom2 A x y y f (id-hom A y) g))
  := \ (g , p) → (g , map-hom2-homotopy' A x y f g p)

#def is-equiv-map-total-hom2-homotopy'-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  ( f : hom A x y)
  : is-equiv
      ( Σ (g : hom A x y) , f = g)
      ( Σ (g : hom A x y) , (hom2 A x y y f (id-hom A y) g))
      ( map-total-hom2-homotopy' A x y f)
  :=
    is-equiv-are-contr
      ( Σ (g : hom A x y) , (f = g))
      ( Σ (g : hom A x y) , (hom2 A x y y f (id-hom A y) g))
      ( is-contr-based-paths (hom A x y) f)
      ( is-segal-A x y y f (id-hom A y))
      ( map-total-hom2-homotopy' A x y f)
```

```rzk title="RS17, Proposition 5.10"
#def equiv-homotopy-hom2'-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  ( f h : hom A x y)
  : Equiv (f = h) (hom2 A x y y f (id-hom A y) h)
  :=
    ( ( map-hom2-homotopy' A x y f h) ,
      ( is-equiv-fiberwise-is-equiv-total
        ( hom A x y)
        ( \ k → (f = k))
        ( \ k → (hom2 A x y y f (id-hom A y) k))
        ( map-hom2-homotopy' A x y f)
        ( is-equiv-map-total-hom2-homotopy'-is-segal A is-segal-A x y f)
        ( h)))
```

More generally, a homotopy between a composite and another map is equivalent to
the data provided by a commutative triangle with that boundary.

```rzk
#def map-hom2-eq-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y z : A)
  ( f : hom A x y)
  ( g : hom A y z)
  ( h : hom A x z)
  ( p : (comp-is-segal A is-segal-A x y z f g) = h)
  : ( hom2 A x y z f g h)
  :=
    ind-path
      ( hom A x z)
      ( comp-is-segal A is-segal-A x y z f g)
      ( \ h' p' → hom2 A x y z f g h')
      ( witness-comp-is-segal A is-segal-A x y z f g)
      ( h)
      ( p)

#def map-total-hom2-eq-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y z : A)
  ( f : hom A x y)
  ( g : hom A y z)
  : ( Σ (h : hom A x z) , (comp-is-segal A is-segal-A x y z f g) = h) →
    ( Σ (h : hom A x z) , (hom2 A x y z f g h))
  := \ (h , p) → (h , map-hom2-eq-is-segal A is-segal-A x y z f g h p)

#def is-equiv-map-total-hom2-eq-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y z : A)
  ( f : hom A x y)
  ( g : hom A y z)
  : is-equiv
      ( Σ (h : hom A x z) , (comp-is-segal A is-segal-A x y z f g) = h)
      ( Σ (h : hom A x z) , (hom2 A x y z f g h))
      ( map-total-hom2-eq-is-segal A is-segal-A x y z f g)
  :=
    is-equiv-are-contr
      ( Σ (h : hom A x z) , (comp-is-segal A is-segal-A x y z f g) = h)
      ( Σ (h : hom A x z) , (hom2 A x y z f g h))
      ( is-contr-based-paths (hom A x z) (comp-is-segal A is-segal-A x y z f g))
      ( is-segal-A x y z f g)
      ( map-total-hom2-eq-is-segal A is-segal-A x y z f g)
```

```rzk title="RS17, Proposition 5.12"
#def equiv-hom2-eq-comp-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y z : A)
  ( f : hom A x y)
  ( g : hom A y z)
  ( k : hom A x z)
  : Equiv ((comp-is-segal A is-segal-A x y z f g) = k) (hom2 A x y z f g k)
  :=
    ( ( map-hom2-eq-is-segal A is-segal-A x y z f g k) ,
      ( is-equiv-fiberwise-is-equiv-total
        ( hom A x z)
        ( \ m → (comp-is-segal A is-segal-A x y z f g) = m)
        ( hom2 A x y z f g)
        ( map-hom2-eq-is-segal A is-segal-A x y z f g)
        ( is-equiv-map-total-hom2-eq-is-segal A is-segal-A x y z f g)
        ( k)))
```

Homotopies form a congruence, meaning that homotopies are respected by
composition:

```rzk title="RS17, Proposition 5.13"
#def congruence-homotopy-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y z : A)
  ( f g : hom A x y)
  ( h k : hom A y z)
  ( p : f = g)
  ( q : h = k)
  : ( comp-is-segal A is-segal-A x y z f h) =
    ( comp-is-segal A is-segal-A x y z g k)
  :=
    ind-path
      ( hom A y z)
      ( h)
      ( \ k' q' →
        ( comp-is-segal A is-segal-A x y z f h) =
        ( comp-is-segal A is-segal-A x y z g k'))
      ( ind-path
        ( hom A x y)
        ( f)
        ( \ g' p' →
          ( comp-is-segal A is-segal-A x y z f h) =
          ( comp-is-segal A is-segal-A x y z g' h))
        ( refl)
        ( g)
        ( p))
      ( k)
      ( q)
```

As a special case of the above:

```rzk
#def postwhisker-homotopy-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y z : A)
  ( f g : hom A x y)
  ( h : hom A y z)
  ( p : f = g)
  : ( comp-is-segal A is-segal-A x y z f h) = (comp-is-segal A is-segal-A x y z g h)
  := congruence-homotopy-is-segal A is-segal-A x y z f g h h p refl
```

As a special case of the above:

```rzk
#def prewhisker-homotopy-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( w x y : A)
  ( k : hom A w x)
  ( f g : hom A x y)
  ( p : f = g)
  : ( comp-is-segal A is-segal-A w x y k f) =
    ( comp-is-segal A is-segal-A w x y k g)
  := congruence-homotopy-is-segal A is-segal-A w x y k k f g refl p
```

```rzk title="RS17, Proposition 5.14(a)"
#def compute-postwhisker-homotopy-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y z : A)
  ( f g : hom A x y)
  ( h : hom A y z)
  ( p : f = g)
  : ( postwhisker-homotopy-is-segal A is-segal-A x y z f g h p) =
    ( ap (hom A x y) (hom A x z) f g (\ k → comp-is-segal A is-segal-A x y z k h) p)
  :=
    ind-path
      ( hom A x y)
      ( f)
      ( \ g' p' →
        ( postwhisker-homotopy-is-segal A is-segal-A x y z f g' h p') =
        ( ap
          (hom A x y) (hom A x z)
          (f) (g') (\ k → comp-is-segal A is-segal-A x y z k h) (p')))
      ( refl)
      ( g)
      ( p)
```

```rzk title="RS17, Proposition 5.14(b)"
#def prewhisker-homotopy-is-ap-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( w x y : A)
  ( k : hom A w x)
  ( f g : hom A x y)
  ( p : f = g)
  : ( prewhisker-homotopy-is-segal A is-segal-A w x y k f g p) =
    ( ap (hom A x y) (hom A w y) f g (comp-is-segal A is-segal-A w x y k) p)
  :=
    ind-path
      ( hom A x y)
      ( f)
      ( \ g' p' →
        ( prewhisker-homotopy-is-segal A is-segal-A w x y k f g' p') =
        ( ap (hom A x y) (hom A w y) f g' (comp-is-segal A is-segal-A w x y k) p'))
      ( refl)
      ( g)
      ( p)

#section is-segal-Unit

#def is-contr-Δ²→Unit uses (extext)
  : is-contr (Δ² → Unit)
  :=
    ( \ _ → unit ,
      \ k →
      naiveextext-extext extext
        ( 2 × 2) Δ² (\ _ → BOT)
        ( \ _ → Unit) (\ _ → recBOT)
        ( \ _ → unit) k
        ( \ _ → refl))

#def is-segal-Unit uses (extext)
  : is-segal Unit
  :=
    \ x y z f g →
    is-contr-is-retract-of-is-contr
      ( Σ (h : hom Unit x z) , (hom2 Unit x y z f g h))
      ( Δ² → Unit)
      ( ( \ (_ , k) → k) ,
        ( \ k → ((\ t → k (t , t)) , k) , \ _ → refl))
      ( is-contr-Δ²→Unit)

#end is-segal-Unit
```

<!-- Definitions for the SVG images above -->
<svg width="0" height="0">
  <defs>
    <style data-bx-fonts="Noto Serif">@import url(https://fonts.googleapis.com/css2?family=Noto+Serif&display=swap);</style>
    <marker
      id="arrow-blue"
      viewBox="0 0 10 10"
      refX="5"
      refY="5"
      markerWidth="5"
      markerHeight="5"
      orient="auto-start-reverse">
      <path d="M 0 2 L 5 5 L 0 8 z" stroke="blue" fill="blue" />
    </marker>
    <marker
      id="arrow-red"
      viewBox="0 0 10 10"
      refX="5"
      refY="5"
      markerWidth="5"
      markerHeight="5"
      orient="auto-start-reverse">
      <path d="M 0 2 L 5 5 L 0 8 z" stroke="red" fill="red" />
    </marker>
    <marker
      id="arrow-grey"
      viewBox="0 0 10 10"
      refX="5"
      refY="5"
      markerWidth="5"
      markerHeight="5"
      orient="auto-start-reverse">
      <path d="M 0 2 L 5 5 L 0 8 z" stroke="grey" fill="grey" />
    </marker>
    <marker
      id="arrow"
      viewBox="0 0 10 10"
      refX="5"
      refY="5"
      markerWidth="5"
      markerHeight="5"
      orient="auto-start-reverse">
      <path d="M 0 2 L 5 5 L 0 8 z" stroke="black" fill="black" />
    </marker>
  </defs>
  <style>
    text, textPath {
      font-family: Noto Serif;
      font-size: 20px;
      dominant-baseline: middle;
      text-anchor: middle;
    }
  </style>
</svg>

Interchange law

```rzk
#section homotopy-interchange-law

#variable A : U
#variable is-segal-A : is-segal A
#variables x y z : A

#def statement-homotopy-interchange-law
  ( f1 f2 f3 : hom A x y)
  ( h1 h2 h3 : hom A y z)
  ( p : f1 = f2)
  ( q : f2 = f3)
  ( p' : h1 = h2)
  ( q' : h2 = h3)
  : U
  := congruence-homotopy-is-segal A is-segal-A x y z f1 f3 h1 h3
      ( concat (hom A x y) f1 f2 f3 p q)
      ( concat (hom A y z) h1 h2 h3 p' q') =
    concat
      ( hom A x z)
      ( comp-is-segal A is-segal-A x y z f1 h1)
      ( comp-is-segal A is-segal-A x y z f2 h2)
      ( comp-is-segal A is-segal-A x y z f3 h3)
      ( congruence-homotopy-is-segal A is-segal-A x y z f1 f2 h1 h2 p p')
      ( congruence-homotopy-is-segal A is-segal-A x y z f2 f3 h2 h3 q q')
```

```rzk title="RS17, Proposition 5.15"
#def homotopy-interchange-law
  ( f1 f2 f3 : hom A x y)
  ( h1 h2 h3 : hom A y z)
  ( p : f1 = f2)
  ( q : f2 = f3)
  ( p' : h1 = h2)
  ( q' : h2 = h3)
  : statement-homotopy-interchange-law f1 f2 f3 h1 h2 h3 p q p' q'
  := ind-path
    ( hom A x y)
    ( f2)
    ( \ f3 q -> statement-homotopy-interchange-law f1 f2 f3 h1 h2 h3 p q p' q')
    ( ind-path
      ( hom A x y)
      ( f1)
      ( \ f2 p -> statement-homotopy-interchange-law f1 f2 f2 h1 h2 h3
          p refl p' q')
      ( ind-path
        ( hom A y z)
        ( h2)
        ( \ h3 q' -> statement-homotopy-interchange-law f1 f1 f1 h1 h2 h3
            refl refl p' q')
        ( ind-path
          ( hom A y z)
          ( h1)
          ( \ h2 p' -> statement-homotopy-interchange-law f1 f1 f1 h1 h2 h2
              refl refl p' refl)
          ( refl)
          ( h2)
          ( p'))
        ( h3)
        ( q'))
      ( f2)
      ( p))
    ( f3)
    ( q)

#end homotopy-interchange-law
```

## Inner anodyne shape inclusions

An **inner fibration** is a map `α : A' → A` which is right orthogonal to
`Λ ⊂ Δ²`. This is the relative notion of a Segal type.

```rzk
#def is-inner-fibration
  ( A' A : U)
  ( α : A' → A)
  : U
  := is-right-orthogonal-to-shape (2 × 2) Δ² (\ t → Λ t) A' A α
```

We say that a shape inclusion `ϕ ⊂ ψ` is **inner anodyne** if it is anodyne for
`Λ ⊂ Δ²`, i.e., if every inner fibration `A' → A` is right orthogonal to
`ϕ ⊂ ψ`.

```rzk
#def is-inner-anodyne
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  : U
  := is-anodyne-for-shape (2 × 2) (Δ²) (\ t → Λ t) I ψ ϕ

#def unpack-is-inner-anodyne
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  : is-inner-anodyne I ψ ϕ
  = ( (A' : U) → (A : U) → (α : A' → A)
    → is-inner-fibration A' A α
    → is-right-orthogonal-to-shape I ψ ϕ A' A α)
  := refl

```

## Weak inner anodyne shape inclusions

We say that a shape inclusion `ϕ ⊂ ψ` is **weak inner anodyne** if every Segal
type `A` has unique extensions with respect to `ϕ ⊂ ψ`.

This notion was just called "anodyne" in RS17.

```rzk title="RS17, Definition 5.19"
#def is-weak-inner-anodyne
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( Φ : ψ → TOPE)
  : U
  := (A : U) → is-segal A → (h : Φ → A) → is-contr ((t : ψ) → A[ Φ t ↦ h t ])
```

Since Segal types are exactly those that have unique extensions with respect to
`Λ ⊂ Δ²`, we see that weak inner anodyne is a special case of the general notion
of weak anodyne introduced earlier.

```rzk
#def is-weak-inner-anodyne-is-weak-anodyne-for-Λ-Δ²
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( is-wa-Λ-Δ² : is-weak-anodyne-for-shape (2 × 2) Δ² (\ t → Λ t) I ψ ϕ)
  : is-weak-inner-anodyne I ψ ϕ
  :=
    \ A is-segal-A →
      ( is-wa-Λ-Δ² A (has-unique-inner-extensions-is-segal A is-segal-A))

#def is-weak-anodyne-for-Λ-Δ²-is-weak-inner-anodyne
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( is-wia : is-weak-inner-anodyne I ψ ϕ)
  : is-weak-anodyne-for-shape (2 × 2) Δ² (\ t → Λ t) I ψ ϕ
  :=
    \ A has-uie-A →
      ( is-wia A (is-segal-has-unique-inner-extensions A has-uie-A))
```

The shape inclusion `Λ ⊂ Δ²` is tautologically inner anodyne

```rzk
#def is-weak-inner-anodyne-Λ²₁
  : is-weak-inner-anodyne (2 × 2) Δ² Λ²₁
  :=
    is-weak-inner-anodyne-is-weak-anodyne-for-Λ-Δ² (2 × 2) Δ² (\ t → Λ t)
    ( is-weak-anodyne-for-self (2 × 2) Δ² (\ t → Λ t))
```

Weak inner anodyne shape inclusions are preserved under pushout product. This is
the direct proof from RS17. One could also deduce it from the corresponding
general statements about weak anodyne shape inclusions.

```rzk title="RS17, lemma 5.20"
#def is-weak-inner-anodyne-pushout-product-left-is-weak-inner-anodyne uses (weakextext)
  ( I J : CUBE)
  ( ψ : I → TOPE)
  ( Φ : ψ → TOPE)
  ( is-weak-inner-anodyne-ψ-Φ : is-weak-inner-anodyne I ψ Φ)
  ( ζ : J → TOPE)
  ( χ : ζ → TOPE)
  : is-weak-inner-anodyne (I × J)
      (\ (t,s) → ψ t ∧ ζ s)
      (\ (t,s) → (Φ t ∧ ζ s) ∨ (ψ t ∧ χ s))
  := \ A is-segal-A h →
    is-contr-equiv-is-contr'
      (((t,s) : I × J | ψ t ∧ ζ s) → A[(Φ t ∧ ζ s) ∨ (ψ t ∧ χ s) ↦ h (t,s)])
      ( (s : ζ) → ((t : ψ) → A[ Φ t ↦ h (t,s)])[ χ s ↦ \ t → h (t, s)])
      (uncurry-opcurry I J ψ Φ ζ χ (\ s t → A) h)
      (weakextext
        ( J)
        ( ζ)
        ( χ)
        ( \ s → (t : ψ) → A[ Φ t ↦ h (t,s)])
        ( \ s → is-weak-inner-anodyne-ψ-Φ A is-segal-A (\ t → h (t,s)))
        ( \ s t → h (t,s)))

#def is-weak-inner-anodyne-pushout-product-right-is-weak-inner-anodyne uses (weakextext)
  ( I J : CUBE)
  ( ψ : I → TOPE)
  ( Φ : ψ → TOPE)
  ( ζ : J → TOPE)
  ( χ : ζ → TOPE)
  (is-weak-inner-anodyne-ζ-χ : is-weak-inner-anodyne J ζ χ)
  : is-weak-inner-anodyne (I × J)
      (\ (t,s) → ψ t ∧ ζ s)
      (\ (t,s) → (Φ t ∧ ζ s) ∨ (ψ t ∧ χ s))
  := \ A is-segal-A h →
    is-contr-equiv-is-contr
      ( (t : ψ) → ((s : ζ) → A[ χ s ↦ h (t,s)])[ Φ t ↦ \ s → h (t, s)])
      (((t,s) : I × J | ψ t ∧ ζ s) → A[(Φ t ∧ ζ s) ∨ (ψ t ∧ χ s) ↦ h (t,s)])
      (curry-uncurry I J ψ Φ ζ χ (\ s t → A) h)
      (weakextext
        ( I)
        ( ψ)
        ( Φ)
        ( \ t → (s : ζ) → A[ χ s ↦ h (t,s)])
        ( \ t → is-weak-inner-anodyne-ζ-χ A is-segal-A (\ s → h (t,s)))
        ( \ s t → h (s,t)))
```

The following argument from RS17 proves that `Λ³₂ ⊂ Δ³` is weakly inner anodyne.
It should be easy to adapt it to prove that it is actually inner anodyne.

```rzk title="RS17, lemma 5.21"
#section retraction-Λ³₂-Δ³-pushout-product-Λ²₁-Δ²

-- Δ³×Λ²₁ ∪_{Λ³₂×Λ²₁} Λ³₂×Δ²
#def pushout-prod-Λ³₂-Λ²₁
  : (Δ³×Δ²) → TOPE
  := shape-pushout-prod (2 × 2 × 2) (2 × 2) Δ³ Λ³₂ Δ² Λ²₁


#variable A : U
#variable h : Λ³₂ → A

#def h^
  : pushout-prod-Λ³₂-Λ²₁ → A
  := \ ( ((t1, t2), t3), (s1, s2) ) →
    recOR
      ( s1 ≤ t1 ∧ t2 ≤ s2 ↦ h ((t1, t2), t3),
        t1 ≤ s1 ∧ t2 ≤ s2 ↦ h ((s1, t2), t3),
        s1 ≤ t1 ∧ t3 ≤ s2 ∧ s2 ≤ t2 ↦ h ((t1, s2), t3),
        t1 ≤ s1 ∧ t3 ≤ s2 ∧ s2 ≤ t2 ↦ h ((s1, s2), t3),
        s1 ≤ t1 ∧ s2 ≤ t3 ↦ h ((t1, s2), s2),
        t1 ≤ s1 ∧ s2 ≤ t3 ↦ h ((s1, s2), s2))


#def extend-against-Λ³₂-Δ³
  : U
  := (t : Δ³) → A[ Λ³₂ t ↦ h t ]

#def extend-against-pushout-prod-Λ³₂-Λ²₁-Δ³×Δ² uses (h)
  : U
  := (x : Δ³×Δ²) → A[ pushout-prod-Λ³₂-Λ²₁ x ↦ h^ x]

#def retract-pushout-prod-Λ³₂-Λ²₁-Δ³×Δ² uses (A h)
  (f : extend-against-pushout-prod-Λ³₂-Λ²₁-Δ³×Δ²)
  : extend-against-Λ³₂-Δ³
  := \ ((t1, t2), t3) → f ( ((t1, t2), t3), (t1, t2) )

#def section-pushout-prod-Λ³₂-Λ²₁-Δ³×Δ² uses (A h)
  (g : (t : Δ³) → A[ Λ³₂ t ↦ h t ])
  : (x : Δ³×Δ²) → A[ pushout-prod-Λ³₂-Λ²₁ x ↦ h^ x]
  :=
    \ ( ((t1, t2), t3), (s1, s2) ) →
    recOR
      ( s1 ≤ t1 ∧ t2 ≤ s2 ↦ g ((t1, t2), t3),
        t1 ≤ s1 ∧ t2 ≤ s2 ↦ g ((s1, t2), t3),
        s1 ≤ t1 ∧ t3 ≤ s2 ∧ s2 ≤ t2 ↦ g ((t1, s2), t3),
        t1 ≤ s1 ∧ t3 ≤ s2 ∧ s2 ≤ t2 ↦ g ((s1, s2), t3),
        s1 ≤ t1 ∧ s2 ≤ t3 ↦ g ((t1, s2), s2),
        t1 ≤ s1 ∧ s2 ≤ t3 ↦ g ((s1, s2), s2))

#def homotopy-retraction-section-id-pushout-prod-Λ³₂-Λ²₁-Δ³×Δ² uses (A h)
  : homotopy extend-against-Λ³₂-Δ³ extend-against-Λ³₂-Δ³
    ( comp
      ( extend-against-Λ³₂-Δ³)
      ( extend-against-pushout-prod-Λ³₂-Λ²₁-Δ³×Δ²)
      ( extend-against-Λ³₂-Δ³)
      ( retract-pushout-prod-Λ³₂-Λ²₁-Δ³×Δ²)
      ( section-pushout-prod-Λ³₂-Λ²₁-Δ³×Δ²))
    ( identity extend-against-Λ³₂-Δ³)
  := \ t → refl

#def is-retract-of-Δ³-Δ³×Δ² uses (A h)
  : is-retract-of
      extend-against-Λ³₂-Δ³
      extend-against-pushout-prod-Λ³₂-Λ²₁-Δ³×Δ²
  :=
    ( section-pushout-prod-Λ³₂-Λ²₁-Δ³×Δ² ,
      ( retract-pushout-prod-Λ³₂-Λ²₁-Δ³×Δ² ,
        homotopy-retraction-section-id-pushout-prod-Λ³₂-Λ²₁-Δ³×Δ²))

#end retraction-Λ³₂-Δ³-pushout-product-Λ²₁-Δ²

#def is-weak-inner-anodyne-Δ³-Λ³₂ uses (weakextext)
  : is-weak-inner-anodyne (2 × 2 × 2) Δ³ Λ³₂
  :=
    \ A is-segal-A h →
    is-contr-is-retract-of-is-contr
      (extend-against-Λ³₂-Δ³ A h)
      (extend-against-pushout-prod-Λ³₂-Λ²₁-Δ³×Δ² A h)
      (is-retract-of-Δ³-Δ³×Δ² A h)
      (is-weak-inner-anodyne-pushout-product-right-is-weak-inner-anodyne
        ( 2 × 2 × 2)
        ( 2 × 2)
        ( Δ³)
        ( Λ³₂)
        ( Δ²)
        ( Λ²₁)
        ( is-weak-inner-anodyne-Λ²₁)
        ( A)
        ( is-segal-A)
        ( h^ A h))
```

## Products of Segal types

This is an additional section which describes morphisms in products of types as
products of morphisms. It is implicitly stated in Proposition 8.21.

```rzk
#section morphisms-of-products-is-products-of-morphisms
#variables A B : U
#variable p : ( product A B )
#variable p' : ( product A B )

#def morphism-in-product-to-product-of-morphism
  : hom ( product A B ) p p' →
    product ( hom A ( first p ) ( first p' ) ) ( hom B ( second p ) ( second p' ) )
  :=  \ f → ( \ ( t : Δ¹ ) → first ( f t ) , \ ( t : Δ¹ ) → second ( f t ) )

#def product-of-morphism-to-morphism-in-product
  : product ( hom A ( first p ) ( first p' ) ) ( hom B ( second p ) ( second p' ) ) →
    hom ( product A B ) p p'
  := \ ( f , g ) ( t : Δ¹ ) → ( f t , g t )

#def morphisms-in-product-to-product-of-morphism-to-morphism-in-product-is-id
  : ( f :  product ( hom A ( first p ) ( first p' ) ) ( hom B ( second p ) ( second p' ) ) ) →
    ( morphism-in-product-to-product-of-morphism )
    ( ( product-of-morphism-to-morphism-in-product )
      f ) = f
  := \ f → refl

#def product-of-morphism-to-morphisms-in-product-to-product-of-morphism-is-id
  : ( f :  hom ( product A B ) p p' ) →
    ( product-of-morphism-to-morphism-in-product )
    ( ( morphism-in-product-to-product-of-morphism )
      f ) = f
  := \ f → refl

#def morphism-in-product-equiv-product-of-morphism
  : Equiv
    ( hom ( product A B ) p p' )
    ( product ( hom A ( first p ) ( first p' ) ) ( hom B ( second p ) ( second p' ) ) )
  :=
    ( ( morphism-in-product-to-product-of-morphism ) ,
      ( ( ( product-of-morphism-to-morphism-in-product ) ,
          ( product-of-morphism-to-morphisms-in-product-to-product-of-morphism-is-id ) ) ,
        ( ( product-of-morphism-to-morphism-in-product ) ,
          ( morphisms-in-product-to-product-of-morphism-to-morphism-in-product-is-id ) ) ) )

#end morphisms-of-products-is-products-of-morphisms
```

## Fibers of maps between Segal types

For any map `f : A → B` between Segal types, each fiber `fib A B f b` is again a
Segal type. This is an instance of a general statement about types with unique
extensions for the shape inclusion `Λ ⊂ Δ²`.

```rzk
#def is-fiberwise-segal-are-segal uses (extext)
  ( A B : U)
  ( f : A → B)
  ( is-segal-A : is-segal A)
  ( is-segal-B : is-segal B)
  ( b : B)
  : is-segal (fib A B f b)
  :=
    is-segal-has-unique-inner-extensions (fib A B f b)
    ( has-fiberwise-unique-extensions-have-unique-extensions extext
      ( 2 × 2) (Δ²) (\ t → Λ t) A B f
      ( has-unique-inner-extensions-is-segal A is-segal-A)
      ( has-unique-inner-extensions-is-segal B is-segal-B)
      ( b))
```
