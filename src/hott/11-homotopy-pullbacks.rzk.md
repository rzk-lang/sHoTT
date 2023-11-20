# 11. Homotopy cartesian squares

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Homotopy cartesian squares

We start by fixing the data of a map between two type families `A' → U` and
`A → U`, which we think of as a commutative square

```
Σ A' → Σ A
 ↓      ↓
 A'  →  A
```

```rzk
#section homotopy-cartesian
-- We prepend all local names in this section
-- with the random identifier temp-uBDx
-- to avoid cluttering the global name space.
-- Once rzk supports local variables, these should be renamed.

#variable A' : U
#variable C' : A' → U
#variable A : U
#variable C : A → U
#variable α : A' → A
#variable γ : (a' : A') → C' a' → C (α a')

#def temp-uBDx-Σαγ
  : total-type A' C' → total-type A C
  := \ (a', c') → (α a', γ a' c')
```

We say that such a square is homotopy cartesian just if it induces an
equivalence componentwise.

```rzk
#def is-homotopy-cartesian uses (A)
  : U
  :=
    ( a' : A') → is-equiv (C' a') (C (α a')) (γ a')
```

### Interaction with horizontal equivalences

We implement various ways homotopy-cartesian squares interact with horizontal
equivalences.

For example, if the lower map `α : A' → A` is an equivalence in a homotopy
cartesian square, then so is the upper one `Σαγ : Σ C' → Σ C`.

```rzk
#def temp-uBDx-comp
  : (total-type A' C') → (total-type A C)
  := comp
      ( total-type A' C')
      ( Σ (a' : A'), C (α a'))
      ( total-type A C)
      ( \ (a', c) → (α a', c) )
      ( total-map A' C' (\ a' → C (α a')) γ)


#def pull-up-equiv-is-homotopy-cartesian
  ( is-hc-α-γ : is-homotopy-cartesian)
  ( is-equiv-α : is-equiv A' A α)
  : is-equiv (total-type A' C') (total-type A C) (\ (a', c') → (α a', γ a' c'))
  :=
    is-equiv-homotopy
      ( total-type A' C')
      ( total-type A C)
      ( temp-uBDx-Σαγ )
      ( temp-uBDx-comp )
      (\ _ → refl)
      ( is-equiv-comp
        ( total-type A' C')
        ( Σ (a' : A'), C (α a'))
        ( total-type A C)
        ( total-map A' C' (\ a' → C (α a')) γ)
        ( is-equiv-total-is-equiv-fiberwise A' C'
          ( \ a' → C (α a') )
          ( γ)
          ( \ a' → is-hc-α-γ a'))
        ( \ (a', c) → (α a', c) )
        ( second
          ( equiv-total-pullback-is-equiv A' A α
            ( is-equiv-α )
            ( C ))))
```

Conversely, if both the upper and the lower maps are equivalences, then the
square is homotopy-cartesian.

```rzk
#def is-homotopy-cartesian-is-horizontal-equiv
  ( is-equiv-α : is-equiv A' A α)
  ( is-equiv-Σαγ : is-equiv
      (total-type A' C') (total-type A C) (\ (a', c') → (α a', γ a' c'))
  )
  : is-homotopy-cartesian
  :=
    is-equiv-fiberwise-is-equiv-total
        A' C' ( \ x → C (α x) ) γ
        ( is-equiv-right-factor
            ( total-type A' C')
            ( Σ (x : A'), C (α x))
            ( total-type A C)
            ( total-map A' C' (\ x → C (α x)) γ)
            ( \ (x, c) → (α x, c) )
            ( second ( equiv-total-pullback-is-equiv A' A α is-equiv-α C))
            ( is-equiv-homotopy
                ( total-type A' C')
                ( total-type A C )
                ( temp-uBDx-comp )
                ( temp-uBDx-Σαγ )
                ( \ _ → refl)
                ( is-equiv-Σαγ)))
```

In a general homotopy-cartesian square we cannot deduce `is-equiv α` from
`is-equiv (Σγ)`. However, if the square has a vertical section then we can
always do this (whether the square is homotopy-cartesian or not).

```rzk
#def has-section-family-over-map
  : U
  :=
    Σ ( ( s', s) : product ((a' : A') → C' a') ((a : A) → C a) ),
      ( (a' : A') → γ a' (s' a') = s (α a'))

#def induced-map-on-fibers-Σ uses (γ)
  ( ĉ : total-type A C)
  ( (ĉ', q̂) : fib
                (total-type A' C') (total-type A C)
                (\ (a', c') → (α a', γ a' c'))
                ĉ)
  : fib A' A α (first ĉ)
  :=
    (first ĉ', first-path-Σ A C (temp-uBDx-Σαγ ĉ') ĉ q̂)

#def temp-uBDx-helper-type uses (γ C')
  ( ((s', s) , η) : has-section-family-over-map)
  ( a : A )
  ( (a', p) : fib A' A α a )
  : U
  :=
    Σ ( q̂ : temp-uBDx-Σαγ (a', s' a') = (a, s a)),
        ( induced-map-on-fibers-Σ (a, s a) ((a', s' a'), q̂) = (a', p))

#def temp-uBDx-helper uses (γ C')
  ( ((s', s) , η) : has-section-family-over-map)
  : ( a : A) →
    ( (a', p) : fib A' A α a ) →
    temp-uBDx-helper-type ((s',s), η) a (a', p)
  :=
    ind-fib A' A α
    ( temp-uBDx-helper-type ((s',s), η))
    ( \ a' →
      ( eq-pair A C (α a', γ a' (s' a')) (α a', s (α a')) ( refl, η a' ) ,
        eq-pair
        ( A')
        ( \ x → α x = α a')
        ( a' ,
          first-path-Σ A C
          ( α a', γ a' (s' a'))
          ( α a', s (α a'))
          ( eq-pair A C (α a', γ a' (s' a')) (α a', s (α a')) ( refl, η a' )))
        ( a' , refl)
        ( refl ,
          first-path-Σ-eq-pair
            A C (α a', γ a' (s' a')) (α a', s (α a')) ( refl, η a' ))))


#def induced-retraction-on-fibers-with-section uses (γ)
  ( ((s',s),η) : has-section-family-over-map)
  ( a : A )
  : ( is-retract-of
      ( fib A' A α a )
      ( fib
        ( total-type A' C') (total-type A C)
        ( \ (a', c') → (α a', γ a' c'))
        ( a, s a)))
  :=
    ( \ (a', p) → ( (a', s' a'), first (temp-uBDx-helper ((s',s),η) a (a',p))),
      ( induced-map-on-fibers-Σ (a, s a) ,
        \ (a', p) → second (temp-uBDx-helper ((s',s),η) a (a',p))))

#def push-down-equiv-with-section uses (γ)
  ( ((s',s),η) : has-section-family-over-map)
  ( is-equiv-Σαγ : is-equiv
      (total-type A' C') (total-type A C) temp-uBDx-Σαγ)
  : is-equiv A' A α
  :=
    is-equiv-is-contr-map A' A α
    ( \ a →
      is-contr-is-retract-of-is-contr
      ( fib A' A α a)
      ( fib (total-type A' C') (total-type A C) (temp-uBDx-Σαγ) (a, s a))
      ( induced-retraction-on-fibers-with-section ((s',s),η) a)
      ( is-contr-map-is-equiv
        ( total-type A' C') (total-type A C)
        (temp-uBDx-Σαγ)
        ( is-equiv-Σαγ )
        (a, s a)))

#end homotopy-cartesian
```

### Invariance under pullbacks

We can pullback a homotopy cartesian square over `α : A' → A` along any map of
maps `β → α` and obtain another homotopy cartesian square.

```rzk
#def is-homotopy-cartesian-pullback
  ( A' : U)
  ( C' : A' → U)
  ( A : U)
  ( C : A → U)
  ( α : A' → A)
  ( γ : ( a' : A') → C' a' → C (α a'))
  ( B' B : U)
  ( β : B' → B)
  ( ((s', s), η) : map-of-maps B' B β A' A α)
  ( is-hc-α : is-homotopy-cartesian A' C' A C α γ)
  : is-homotopy-cartesian
      B' ( \ b' → C' (s' b'))
      B  ( \ b → C (s b))
      β  ( \ b' c' → transport A C (α (s' b')) (s (β b')) (η b') (γ (s' b') c'))
  :=
    \ b' →
      is-equiv-comp (C' (s' b')) (C (α (s' b'))) (C (s (β b')))
        ( γ (s' b'))
        ( is-hc-α (s' b'))
        ( transport A C (α (s' b')) (s (β b')) (η b'))
        ( is-equiv-transport A C (α (s' b')) (s (β b')) (η b'))
```

## Pasting calculus for homotopy cartesian squares

Currently our notion of squares is not symmetric, since the vertical maps are
given by type families, i.e. they are _display maps_, while the horizontal maps
are arbitrary. Therefore we distinquish between the vertical and the horizontal
pasting calculus.

### Vertical calculus

The following vertical composition and cancellation laws follow easily from the
corresponding statements about equivalences established above.

```rzk
#section homotopy-cartesian-vertical-calculus

#variable A' : U
#variable C' : A' → U
#variable D' : ( a' : A') → C' a' → U
#variable A : U
#variable C : A → U
#variable D : (a : A) → C a → U
#variable α : A' → A
#variable γ : (a' : A') → C' a' → C (α a')
#variable δ : (a' : A') → (c' : C' a') → D' a' c' → D (α a') (γ a' c')

#def is-homotopy-cartesian-upper
  : U
  := ( is-homotopy-cartesian
       ( total-type A' C')
       ( \ (a', c') → D' a' c')
       ( total-type A C)
       ( \ (a, c) → D a c)
       ( \ (a', c') → (α a', γ a' c'))
       ( \ (a', c') → δ a' c'))

#def is-homotopy-cartesian-upper-to-fibers uses (A)
  ( is-hc-γ-δ : is-homotopy-cartesian-upper)
  ( a' : A')
  : is-homotopy-cartesian (C' a') (D' a') (C (α a')) (D (α a')) (γ a') (δ a')
  :=
    \ c' → is-hc-γ-δ (a', c')

#def is-homotopy-cartesian-upper-from-fibers uses (A)
  ( is-fiberwise-hc-γ-δ
    : ( a' : A') →
      is-homotopy-cartesian (C' a') (D' a') (C (α a')) (D (α a')) (γ a') (δ a'))
  : is-homotopy-cartesian-upper
  :=
    \ (a', c') → is-fiberwise-hc-γ-δ a' c'

#def is-homotopy-cartesian-vertical-pasted
  : U
  :=
    is-homotopy-cartesian
      A' (\ a' → total-type (C' a') (D' a'))
      A (\ a → total-type (C a) (D a))
      α (\ a' (c', d') → (γ a' c', δ a' c' d'))

#def is-homotopy-cartesian-vertical-pasting
  ( is-hc-α-γ : is-homotopy-cartesian A' C' A C α γ )
  ( is-hc-γ-δ : is-homotopy-cartesian-upper)
  : is-homotopy-cartesian-vertical-pasted
  :=
    \ a' →
      pull-up-equiv-is-homotopy-cartesian
        (C' a') (D' a') (C (α a')) (D (α a')) (γ a') (δ a')
        ( is-homotopy-cartesian-upper-to-fibers is-hc-γ-δ a')
        ( is-hc-α-γ a' )

#def is-homotopy-cartesian-vertical-pasting-from-fibers
  ( is-hc-α-γ : is-homotopy-cartesian A' C' A C α γ )
  ( is-fiberwise-hc-γ-δ
    : ( a' : A') →
      is-homotopy-cartesian (C' a') (D' a') (C (α a')) (D (α a')) (γ a') (δ a'))
  : is-homotopy-cartesian-vertical-pasted
  :=
    is-homotopy-cartesian-vertical-pasting
      is-hc-α-γ
      ( is-homotopy-cartesian-upper-from-fibers is-fiberwise-hc-γ-δ)

#def is-homotopy-cartesian-lower-cancel-to-fibers
  ( is-hc-α-γ : is-homotopy-cartesian A' C' A C α γ )
  ( is-hc-α-δ : is-homotopy-cartesian-vertical-pasted)
  ( a' : A')
  : is-homotopy-cartesian (C' a') (D' a') (C (α a')) (D (α a')) (γ a') (δ a')
  :=
    is-homotopy-cartesian-is-horizontal-equiv
      ( C' a') (D' a') (C (α a')) (D (α a')) (γ a') (δ a')
      ( is-hc-α-γ a')
      ( is-hc-α-δ a')

#def is-homotopy-cartesian-lower-cancel uses (D D' δ)
  ( is-hc-α-γ : is-homotopy-cartesian A' C' A C α γ )
  ( is-hc-α-δ : is-homotopy-cartesian-vertical-pasted
  )
  : is-homotopy-cartesian-upper
  :=
    is-homotopy-cartesian-upper-from-fibers
      (is-homotopy-cartesian-lower-cancel-to-fibers is-hc-α-γ is-hc-α-δ)

#def is-homotopy-cartesian-upper-cancel-with-section
  ( has-sec-γ-δ : (a' : A') →
      has-section-family-over-map
        (C' a') (D' a') (C (α a')) (D (α a')) (γ a') (δ a'))
  ( is-hc-α-δ : is-homotopy-cartesian-vertical-pasted)
  : is-homotopy-cartesian A' C' A C α γ
  :=
    \ a' →
      push-down-equiv-with-section
      ( C' a') (D' a') (C (α a')) (D (α a')) (γ a') (δ a')
      ( has-sec-γ-δ a')
      ( is-hc-α-δ a')

#end homotopy-cartesian-vertical-calculus
```

### Horizontal calculus

We also have the horizontal version of pasting and cancellation which follows
from composition and cancelling laws for equivalences.

```rzk
#section homotopy-cartesian-horizontal-calculus

#variable A'' : U
#variable C'' : A'' → U
#variable A' : U
#variable C' : A' → U
#variable A : U
#variable C : A → U
#variable f' : A'' → A'
#variable F' : (a'' : A'') → C'' a'' → C' (f' a'')
#variable f : A' → A
#variable F : (a' : A') → C' a' → C (f a')

#def is-homotopy-cartesian-horizontal-pasting
  ( ihc : is-homotopy-cartesian A' C' A C f F)
  ( ihc' : is-homotopy-cartesian A'' C'' A' C' f' F')
  : is-homotopy-cartesian A'' C'' A C
    ( comp A'' A' A f f')
    ( \ a'' →
        comp (C'' a'') (C' (f' a'')) (C (f (f' a'')))
         (F (f' a'')) (F' a''))
  :=
    \ a'' →
    is-equiv-comp (C'' a'') (C' (f' a'')) (C (f (f' a'')))
      (F' a'') (ihc' a'')
      (F (f' a'')) (ihc (f' a''))

#def is-homotopy-cartesian-right-cancel
  ( ihc : is-homotopy-cartesian A' C' A C f F)
  ( ihc'' : is-homotopy-cartesian A'' C'' A C
              ( comp A'' A' A f f')
              ( \ a'' →
                comp (C'' a'') (C' (f' a'')) (C (f (f' a'')))
                  (F (f' a'')) (F' a'')))
  : is-homotopy-cartesian A'' C'' A' C' f' F'
  :=
    \ a'' →
    is-equiv-right-factor (C'' a'') (C' (f' a'')) (C (f (f' a'')))
    ( F' a'') (F (f' a''))
    ( ihc (f' a''))
    ( ihc'' a'')

```

We can cancel the left homotopy cartesian square if its lower map
`f' : A'' → A'` has a section.

```rzk
#def is-homotopy-cartesian-left-cancel-with-lower-section
  ( has-section-f' : has-section A'' A' f')
  ( ihc' : is-homotopy-cartesian A'' C'' A' C' f' F')
  ( ihc'' : is-homotopy-cartesian A'' C'' A C
              ( comp A'' A' A f f')
              ( \ a'' →
                comp (C'' a'') (C' (f' a'')) (C (f (f' a'')))
                  (F (f' a'')) (F' a'')))
  : is-homotopy-cartesian A' C' A C f F
  :=
    ind-has-section A'' A' f' has-section-f'
    ( \ a' → is-equiv (C' a') (C (f a')) (F a'))
    ( \ a'' →
      is-equiv-left-factor (C'' a'') (C' (f' a'')) (C (f (f' a'')))
      ( F' a'') (ihc' a'')
      ( F (f' a'')) ( ihc'' a''))
```

In fact, it suffices to assume that the left square has horizontal sections.

```rzk
#def is-homotopy-cartesian-left-cancel-with-section
  ( has-section-f' : has-section A'' A' f')
  ( has-sections-F' : (a'' : A'') → has-section (C'' a'') (C' (f' a'')) (F' a''))
  ( ihc'' : is-homotopy-cartesian A'' C'' A C
              ( comp A'' A' A f f')
              ( \ a'' →
                comp (C'' a'') (C' (f' a'')) (C (f (f' a'')))
                  (F (f' a'')) (F' a'')))
  : is-homotopy-cartesian A' C' A C f F
  :=
    ind-has-section A'' A' f' has-section-f'
    ( \ a' → is-equiv (C' a') (C (f a')) (F a'))
    ( \ a'' →
      is-equiv-left-cancel (C'' a'') (C' (f' a'')) (C (f (f' a'')))
      ( F' a'') ( has-sections-F' a'')
      ( F (f' a'')) ( ihc'' a''))

#def is-homotopy-cartesian-left-cancel-with-section'
  ( (sec-f' , ε-f') : has-section A'' A' f')
  ( has-sections-F'
    : (a' : A')
    → has-section (C'' (sec-f' a')) (C' (f' (sec-f' a'))) (F' (sec-f' a')))
  ( ihc''
    : is-homotopy-cartesian A'' C'' A C
      ( comp A'' A' A f f')
      ( \ a'' →
        comp (C'' a'') (C' (f' a'')) (C (f (f' a'')))
        ( F (f' a'')) (F' a'')))
  : is-homotopy-cartesian A' C' A C f F
  :=
    ind-has-section' A'' A' f' (sec-f', ε-f')
    ( \ a' → is-equiv (C' a') (C (f a')) (F a'))
    ( \ a' →
      is-equiv-left-cancel
      ( C'' (sec-f' a')) (C' (f' (sec-f' a'))) (C (f (f' (sec-f' a'))))
      ( F' (sec-f' a')) ( has-sections-F' a')
      ( F (f' (sec-f' a'))) ( ihc'' (sec-f' a')))

#end homotopy-cartesian-horizontal-calculus
```

### Homotopy cartesian faces of a cube

Consider two squares induced by type families as follows

```rzk
#section is-homotopy-cartesian-in-cube

#variable A' : U
#variable C' : A' → U
#variable A : U
#variable C : A → U
#variable α : A' → A
#variable γ : (a' : A') → C' a' → C (α a')

#variable B' : U
#variable D' : B' → U
#variable B : U
#variable D : B → U
#variable β : B' → B
#variable δ : (b' : B') → D' b' → D (β b')
```

and a map between them in the following strict sense

```rzk
#variable f' : A' → B'
#variable f : A → B
#variable h : (a' : A') → β (f' a') = f (α a')

#variable F' : (a' : A') → C' a' → D' (f' a')
#variable F : (a : A) → C a → D (f a)
#variable H
  : (a' : A')
  → (c' : C' a')
  → ( transport B D (β (f' a')) (f (α a')) (h a')
      ( δ (f' a') (F' a' c'))
    = F (α a') (γ a' c'))
```

We view this as a cube

```
      Σ D'      Σ D

Σ C'      Σ C

       B'        B

 A'        A
```

with display maps going down and ordinary maps going to the right and up-right.

Assume furthermore that the two squares on the left and right are themselves
homotopy cartesian.

```rzk
#variable is-hc-CD' : is-homotopy-cartesian A' C' B' D' f' F'
#variable is-hc-CD : is-homotopy-cartesian A C B D f F
```

If the square `B' D' B D` is homotopy cartesian, then so is `A' C' A C`.

```rzk
#def is-homotopy-cartesian-in-cube
  : is-homotopy-cartesian B' D' B D β δ
  → is-homotopy-cartesian A' C' A C α γ
  :=
  \ is-hc-BD a' →
    is-equiv-equiv-is-equiv
    ( C' a') (C (α a')) (γ a')
    ( D' (f' a')) (D (f (α a')))
    (\ d' → transport B D (β (f' a')) (f (α a')) (h a') (δ (f' a') d'))
    ( ( F' a' ,  F (α a')) , H a')
    ( is-hc-CD' a')
    ( is-hc-CD (α a'))
    ( is-equiv-comp
      ( D' (f' a')) (D (β (f' a'))) (D (f (α a')))
      ( δ (f' a')) (is-hc-BD (f' a'))
      ( transport B D (β (f' a')) (f (α a')) (h a'))
      ( is-equiv-transport B D (β (f' a')) (f (α a')) (h a')))
```

The converse holds provided that the map `f' : A' → B'` has a section.

```rzk
#def is-homotopy-cartesian-in-cube'
  ( has-sec-f' : has-section A' B' f')
  : is-homotopy-cartesian A' C' A C α γ
  → is-homotopy-cartesian B' D' B D β δ
  :=
  \ is-hc-AC →
    ind-has-section A' B' f' has-sec-f'
    ( \ b' → is-equiv (D' b') (D (β b')) (δ b'))
    ( \ a' →
      ( is-equiv-right-factor
        ( D' (f' a')) (D (β (f' a'))) (D (f (α a')))
        ( δ (f' a'))
        ( transport B D (β (f' a')) (f (α a')) (h a'))
        ( is-equiv-transport B D (β (f' a')) (f (α a')) (h a'))
        ( is-equiv-equiv-is-equiv'
          ( C' a') (C (α a')) (γ a')
          ( D' (f' a')) (D (f (α a')))
          (\ d' → transport B D (β (f' a')) (f (α a')) (h a') (δ (f' a') d'))
          ( ( F' a' ,  F (α a')) , H a')
          ( is-hc-CD' a')
          ( is-hc-CD (α a'))
          ( is-hc-AC a'))))

#end is-homotopy-cartesian-in-cube
```

## Fiber products

Given two type families `B C : A → U`, we can form their **fiberwise product**.

```rzk
#def fiberwise-product
  ( A : U)
  ( B C : A → U)
  : A → U
  :=
    \ a → product (B a) (C a)

#def first-fiberwise-product
  ( A : U)
  ( B C : A → U)
  ( a : A)
  : fiberwise-product A B C a → B a
  := \ (b,_) → b

#def second-fiberwise-product
  ( A : U)
  ( B C : A → U)
  ( a : A)
  : fiberwise-product A B C a → C a
  := \ (_,c) → c
```

Given two maps `B → A` and `C → A`, we can form the **relative product** over
`A`.

```rzk
#section relative-product

#variable A : U
#variable B : U
#variable β : B → A
#variable C : U
#variable γ : C → A

#def relative-product
  : U
  := Σ ( (b, c) : product B C) , (β b = γ c)

#def first-relative-product uses (A B β C γ)
  : relative-product → B
  := \ ((b , _), _) → b

#def second-relative-product uses (A B β C γ)
  : relative-product → C
  := \ ((_ , c), _) → c

#def projection-relative-product uses (A B β C)
  : relative-product → A
  := \ ((_ , c) , _) → γ c

#def homotopy-relative-product uses (A B C)
  ( (bc, p) : relative-product )
  : β (first-relative-product (bc,p)) = γ (second-relative-product (bc,p))
  := p
```

This relative product agrees with the fiber product obtained by summing over the
product of all fibers.

```rzk
#def fiber-product
  : U
  := total-type A (fiberwise-product A (fib B A β) (fib C A γ))

#def unpack-fiber-product
  : fiber-product
  = ( Σ (a : A), (product (fib B A β a) (fib C A γ a)))
  := refl

#def first-fiber-product uses (A B β C γ)
  : fiber-product → B
  := \ (_, ((b, _), _ )) → b

#def second-fiber-product uses (A B β C γ)
  : fiber-product → C
  := \ (_, (_, (c, _))) → c

#def projection-fiber-product uses (A B β C γ)
  : fiber-product → A
  := \ (a, (_, (_, _))) → a

#def homotopy-fiber-product uses (A B C)
  : ( abpcq : fiber-product )
  → β (first-fiber-product abpcq) = γ (second-fiber-product abpcq)
  :=
    \ ( a, ((b, p), (c,q))) →
      zig-zag-concat A (β b) a (γ c) p q

#def relative-fiber-product uses (B C)
  ( (a, ((b, p), (c,q))) : fiber-product )
  : relative-product
  := ( ( b , c) , zig-zag-concat A (β b) a (γ c) p q)

#def fiber-relative-product uses ( A B β C)
  ( ((b,c), e) : relative-product)
  : fiber-product
  := ( γ c , ( (b , e) , (c , refl)))

#def compatible-projection-fiber-relative-product uses (A B β C γ)
  ( x : relative-product)
  : projection-relative-product x = projection-fiber-product (fiber-relative-product x)
  := refl

#def compatible-projection-relative-fiber-product uses (A B β C γ)
  ( abpcq : fiber-product)
  : ( projection-relative-product (relative-fiber-product abpcq)
    = projection-fiber-product abpcq)
  := second (second (second abpcq)) -- evaluates to q

#def is-id-relative-fiber-relative-product
  ( bce : relative-product)
  : relative-fiber-product (fiber-relative-product bce) = bce
  := refl

#def is-id-fiber-relative-fiber-product
  : ( abpcq : fiber-product)
  → ( fiber-relative-product (relative-fiber-product abpcq)) = abpcq
  :=
  \ (a', (bq', cq')) →
    ind-fib C A γ
    ( \ a cq →
      ( ( bq : fib B A β a)
      → ( fiber-relative-product (relative-fiber-product (a, (bq, cq)))
        = ( a, (bq, cq)))))
    ( \ c bq → refl)
    ( a')
    ( cq')
    ( bq')

#def is-equiv-relative-fiber-product uses (A B β C γ)
  : is-equiv fiber-product relative-product relative-fiber-product
  :=
    ( ( fiber-relative-product
      , is-id-fiber-relative-fiber-product)
    , ( fiber-relative-product
      , is-id-relative-fiber-relative-product))

#def equiv-relative-product-fiber-product uses (A B β C γ)
  : Equiv fiber-product relative-product
  :=
    ( relative-fiber-product
    , is-equiv-relative-fiber-product)

#end relative-product
```

### Fiber product with singleton type

The relative product of `f : B → A` with a map `Unit → A` corresponding to
`a : A` is nothing but the fiber `fib B A f a`.

```rzk
#def compute-pullback-to-Unit
  ( B A : U)
  ( f : B → A)
  ( a : A)
  : Equiv (fib B A f a) (relative-product A B f Unit (\ unit → a))
  :=
    ( ( \ (b , p) → ((b , unit) , p))
    , ( ( ( ( \ ((b , unit) , p) → (b, p))
          , ( \ _ → refl))
        , ( ( \ ((b , unit) , p) → (b, p))
          , ( \ _ → refl)))))

#def compute-map-pullback-to-Unit
  ( B A : U)
  ( f : B → A)
  ( a : A)
  : Equiv-of-maps
    ( fib B A f a) (Unit) (\ _ → unit)
    ( relative-product A B f Unit (\ unit → a))
    ( Unit) ( second-relative-product A B f Unit (\ unit → a))
  :=
    ( ( ( ( \ (b , p) → ((b , unit) , p))
        , ( identity Unit))
      , \ _ → refl)
    , ( second (compute-pullback-to-Unit B A f a)
      , is-equiv-identity Unit))
```

### Total fibers of a square

We consider a commutative square

```
T → B
↓   ↓
C → A
```

given by the following data:

```rzk
#section fibers-comm-square

-- the data of a comm square
#variable A : U
#variable B : U
#variable β : B → A
#variable C : U
#variable γ : C → A
#variable T : U
#variable β' : T → B
#variable γ' : T → C
#variable η : (t : T) → β (β' t) = γ (γ' t)
```

We define the canonical **gap map** from `T` to the relative product over `A`.
The fibers of this gap map are called the **total-fibers** of the commutative
square.

```rzk
#def gap-map-comm-square
  : T → relative-product A B β C γ
  := \ t → ((β' t , γ' t) , η t)

#def tot-fib-comm-square uses (β' γ' η)
  ( bcp : relative-product A B β C γ)
  : U
  := fib T (relative-product A B β C γ) gap-map-comm-square bcp
-- t , ((β' t , γ' t) , η t) = ((b , c) , p)
```

We aim to show that one can compute these total fibers of the commutative square
in two steps: first, one takes the fibers in the vertical direction and obtains
an induced map `fib T C γ c → fib B A β (γ c)`; second, one takes the fibers of
these maps.

We define the induced maps on fibers the resulting fibers between fibers.

```rzk
#def map-vertical-fibs-comm-square
  ( c : C)
  : fib T C γ' c → fib B A β (γ c)
  := \ (t , q) →
     ( (β' t)
     , ( concat A (β (β' t)) (γ (γ' t)) (γ c)
         (η t) (ap C A (γ' t) c γ q)))

#def fib-vertical-fibs-comm-square uses (β' γ' η)
  ( c : C)
  ( bp : fib B A β (γ c))
  : U
  := fib (fib T C γ' c) (fib B A β (γ c))
     ( map-vertical-fibs-comm-square c)
     ( bp)
-- (t, q : γ' t = c) , (β' t, concat (η t) (ap γ q)) = (b, p : β b = γ c)
```

Then we use a helper term to construct a comparison map from the total fibers to
the fiber fibers.

```rzk
-- We append the random suffix IkCK to terms
-- that are only meant to be used locally in this section

#def helper-IkCK uses (β' η)
  ( ((b , c) , p) : relative-product A B β C γ)
  ( t : T)
  : U
  := Σ ( q : γ' t = c) , map-vertical-fibs-comm-square c (t , q) = (b , p)

#def fib-vertical-fibs-helper-IkCK uses (β' γ' η)
  ( ((b , c) , p) : relative-product A B β C γ)
  ( t : T)
  ( (q , e) : helper-IkCK ((b,c),p) t)
  : fib-vertical-fibs-comm-square c (b,p)
  := ((t , q) , e)

#def fib-vertical-fibs-tot-fib-comm-square uses (η β' γ')
  ( ((b,c),p) : relative-product A B β C γ)
  ( (t , h) : tot-fib-comm-square ((b,c),p))
  : fib-vertical-fibs-comm-square c (b,p)
  :=
    ( fib-vertical-fibs-helper-IkCK ((b,c),p) t)
    ( ind-fib T (relative-product A B β C γ)
      ( gap-map-comm-square)
      ( \ bcp' (t, h') → helper-IkCK bcp' t)
      ( \ t → (refl, refl))
      ( ((b,c),p))
      ( t , h))
```

We could have defined this comparison map without the helper by a direct fiber
induction, but in this case it would not commute definitionally with the
canonical projection to `T`.

```rzk
#def compute-fib-vertical-fibs-tot-fib-comm-square uses (η β' γ')
  ( bcp : relative-product A B β C γ)
  ( (t , h) : tot-fib-comm-square bcp)
  :
  ( first (first (fib-vertical-fibs-tot-fib-comm-square bcp (t , h)))
  = t)
  := refl
```

Finally, we show that these comparison maps are equivalences by summing over all
of them. Indeed, by applications of `is-equiv-domain-sum-of-fibers`, the total
type on each side is just equivalent to `T`.

```rzk
#def is-equiv-projection-fib-vertical-fibs-comm-square uses (η β')
  : is-equiv
    ( Σ (((b,c),p) : relative-product A B β C γ)
      , fib-vertical-fibs-comm-square c (b,p))
    ( T)
    ( \ (_ , ((t , _) , _)) → t)
  :=
    is-equiv-triple-comp
    ( Σ (((b,c),p) : relative-product A B β C γ)
      , fib-vertical-fibs-comm-square c (b,p))
    ( Σ ( c : C)
      , ( Σ (bp : fib B A β (γ c))
          , fib-vertical-fibs-comm-square c bp))
    ( Σ (c : C) , fib T C γ' c)
    ( T)
    ( \ (((b , c) , p) , tqe) → (c , ((b , p) , tqe)))
    ( ( \ (c , ((b , p) , tqe)) → (((b , c) , p) , tqe) , \ _ → refl)
    , ( \ (c , ((b , p) , tqe)) → (((b , c) , p) , tqe) , \ _ → refl))
    ( \ (c , (_ , (tq , _))) → (c , tq))
    ( is-equiv-total-is-equiv-fiberwise C
      ( \ c → Σ (bp : fib B A β (γ c)) , fib-vertical-fibs-comm-square c bp)
      ( \ c → fib T C γ' c)
      ( \ c (_ , (tq , _)) → tq)
      ( \ c →
        is-equiv-domain-sum-of-fibers
        ( fib T C γ' c) (fib B A β (γ c))
        ( map-vertical-fibs-comm-square c)))
    ( \ (_ , (t , _)) → t)
    ( is-equiv-domain-sum-of-fibers T C γ')

#def is-equiv-fib-vertical-fibs-tot-fib-comm-square uses (η β' γ')
  : (((b,c),p) : relative-product A B β C γ)
  → is-equiv
    ( tot-fib-comm-square ((b,c),p))
    ( fib-vertical-fibs-comm-square c (b,p))
    ( fib-vertical-fibs-tot-fib-comm-square ((b,c),p))
  :=
    is-equiv-fiberwise-is-equiv-total
    ( relative-product A B β C γ)
    ( \ bcp → tot-fib-comm-square bcp)
    ( \ ((b,c),p) → fib-vertical-fibs-comm-square c (b,p))
    ( \ bcp → fib-vertical-fibs-tot-fib-comm-square bcp)
    ( is-equiv-right-factor
      ( Σ (bcp : relative-product A B β C γ)
        , tot-fib-comm-square bcp)
      ( Σ (((b,c),p) : relative-product A B β C γ)
        , fib-vertical-fibs-comm-square c (b,p))
      ( T)
      ( total-map
        ( relative-product A B β C γ)
        ( \ bcp → tot-fib-comm-square bcp)
        ( \ ((b,c),p) → fib-vertical-fibs-comm-square c (b,p))
        ( \ bcp → fib-vertical-fibs-tot-fib-comm-square bcp))
      ( \ (_ , ((t , _) , _)) → t)
      ( is-equiv-projection-fib-vertical-fibs-comm-square)
      ( is-equiv-domain-sum-of-fibers
        ( T) ( relative-product A B β C γ)
        ( gap-map-comm-square)))
```

We summarize the result as the following equivalence:

```rzk
#def equiv-fib-vertical-fibs-tot-fib-comm-square uses (A B C β γ T β' γ' η)
  ( b : B)
  ( c : C)
  ( p : β b = γ c)
  : Equiv
    ( tot-fib-comm-square ((b , c) , p))
    ( fib-vertical-fibs-comm-square c (b , p))
  :=
    ( fib-vertical-fibs-tot-fib-comm-square ((b , c) , p)
    , is-equiv-fib-vertical-fibs-tot-fib-comm-square ((b , c) , p))

#end fibers-comm-square
```

## Functoriality of fibers

We have an assignment that to each `α : A' → A` and each `a : A` assigns the
fiber `fib A' A α a`. We now investigate the functoriality properties of this
assignment.

Every map of maps induces a map of fibers.

```rzk
#section is-equiv-map-of-fibers-is-equiv-map-of-maps
#variables A' A : U
#variable α : A' → A
#variables B' B : U
#variable β : B' → B
#variable map-of-maps-α-β : map-of-maps A' A α B' B β

-- To avoid polluting the global namespace, we add a random suffix to
-- identifiers that are only supposed to be used in this section.
#def s'-c4XT uses (A α B β) : A' → B' := first (first map-of-maps-α-β)
#def s-c4XT uses (A' α B' β) : A → B := second (first map-of-maps-α-β)

#def map-of-fibers-map-of-maps
  ( a : A)
  ( (a', p) : fib A' A α a)
  : fib B' B β (s-c4XT a)
  :=
  ( s'-c4XT a'
  , ( concat B (β (s'-c4XT a')) (s-c4XT (α a')) (s-c4XT a))
    ( second  map-of-maps-α-β a')
    ( ap A B (α a') a s-c4XT p))
```

### Equivalences induce equivalences on fibers

As an application of `#!rzk is-homotopy-cartesian-is-horizontal-equiv`, we show
that an equivalence of maps induces an equivalence of fibers at each base point.

```rzk
#def map-of-sums-of-fibers-map-of-maps uses (map-of-maps-α-β)
  ( (a, u) : Σ (a : A), fib A' A α a)
  : Σ (b : B), fib B' B β b
  := (s-c4XT a, map-of-fibers-map-of-maps a u)

#def sums-of-fibers-to-domains-map-of-maps uses (map-of-maps-α-β)
  : map-of-maps
    ( Σ (a : A), fib A' A α a)
    ( Σ (b : B), fib B' B β b)
    ( map-of-sums-of-fibers-map-of-maps)
    ( A')
    ( B')
    ( s'-c4XT)
  :=
  ((( \ (_, (a', _)) → a'), ( \ (_, (b', _)) → b')), \ (a, u) → refl)

#variable is-equiv-s' : is-equiv A' B' s'-c4XT

#def is-equiv-map-of-sums-of-fibers-is-equiv-map-of-domains
  uses (map-of-maps-α-β is-equiv-s')
  : is-equiv
    ( Σ (a : A), fib A' A α a)
    ( Σ (b : B), fib B' B β b)
    ( map-of-sums-of-fibers-map-of-maps)
  :=
  is-equiv-equiv-is-equiv
  ( Σ (a : A), fib A' A α a)
  ( Σ (b : B), fib B' B β b)
  ( map-of-sums-of-fibers-map-of-maps)
  ( A')
  ( B')
  ( s'-c4XT)
  ( sums-of-fibers-to-domains-map-of-maps)
  ( second
    ( ( inv-equiv A' (Σ (a : A), fib A' A α a))
      ( equiv-sum-of-fibers-domain A' A α)))
  ( second
    ( ( inv-equiv B' (Σ (b : B), fib B' B β b))
      ( equiv-sum-of-fibers-domain B' B β)))
  ( is-equiv-s')

#variable is-equiv-s : is-equiv A B s-c4XT

#def is-equiv-map-of-fibers-is-equiv-map-of-maps
  uses (map-of-maps-α-β  is-equiv-s is-equiv-s')
  : (a : A)
  → is-equiv
    ( fib A' A α a)
    ( fib B' B β (s-c4XT a))
    ( map-of-fibers-map-of-maps a)
  :=
  is-homotopy-cartesian-is-horizontal-equiv
  ( A)
  ( fib A' A α)
  ( B)
  ( fib B' B β)
  ( s-c4XT)
  ( map-of-fibers-map-of-maps)
  ( is-equiv-s)
  ( is-equiv-map-of-sums-of-fibers-is-equiv-map-of-domains)

#end is-equiv-map-of-fibers-is-equiv-map-of-maps

#def Equiv-of-fibers-Equiv-of-maps
  ( A' A : U)
  ( α : A' → A)
  ( B' B : U)
  ( β : B' → B)
  ( (((s', s), η), (is-equiv-s, is-equiv-s')) : Equiv-of-maps A' A α B' B β)
  (a : A)
  : Equiv (fib A' A α a) (fib B' B β (s a))
  :=
  ( map-of-fibers-map-of-maps A' A α B' B β ((s', s), η) a
  , ( is-equiv-map-of-fibers-is-equiv-map-of-maps A' A α B' B β ((s', s), η))
    ( is-equiv-s)
    ( is-equiv-s')
    ( a))
```

### Composition induces composition on fibers

The map induced on fibers respects composition up to homotopy.

```rzk
#def comp-map-of-maps
  ( A' A : U)
  ( α : A' → A)
  ( B' B : U)
  ( β : B' → B)
  ( C' C : U)
  ( γ : C' → C)
  ( ((t',t),ηt) : map-of-maps B' B β C' C γ)
  ( ((s',s),ηs) : map-of-maps A' A α B' B β)
  : map-of-maps A' A α C' C γ
  :=
  ( ( comp A' B' C' t' s'
    , comp A B C t s)
  , ( \ a' →
      concat C (γ (t' (s' a'))) (t (β (s' a'))) (t (s (α a')))
      ( ηt (s' a'))
      ( ap B C (β (s' a')) (s (α a')) t (ηs a'))))

#def comp-map-of-fibers-comp-map-of-maps
  ( A' A : U)
  ( α : A' → A)
  ( B' B : U)
  ( β : B' → B)
  ( C' C : U)
  ( γ : C' → C)
  ( ((t',t),ηt) : map-of-maps B' B β C' C γ)
  ( ((s',s),ηs) : map-of-maps A' A α B' B β)
  : ( a : A)
  → homotopy (fib A' A α a) (fib C' C γ (t (s a)))
    ( comp ( fib A' A α a) (fib B' B β (s a)) (fib C' C γ (t (s a)))
      ( map-of-fibers-map-of-maps B' B β C' C γ ((t',t),ηt) ( s a))
      ( map-of-fibers-map-of-maps A' A α B' B β ((s',s),ηs) ( a)))
    ( map-of-fibers-map-of-maps A' A α C' C γ
      ( comp-map-of-maps A' A α B' B β C' C γ
        ((t',t),ηt) ((s',s),ηs))
      (a))
  :=
    ind-fib A' A α
    ( \ a a'p →
      ( ( map-of-fibers-map-of-maps B' B β C' C γ ((t',t),ηt) (s a))
        ( map-of-fibers-map-of-maps A' A α B' B β ((s',s),ηs) a
          ( a'p))
      =_{ fib C' C γ (t (s a))}
        ( map-of-fibers-map-of-maps A' A α C' C γ
          ( comp-map-of-maps A' A α B' B β C' C γ
            ((t',t),ηt) ((s',s),ηs))
          ( a) (a'p))))
    ( \ a' → refl)
```

### Retracts induce retracts on fibers

Every retract of types induces a retract on fibers.

```rzk
#def is-section-retraction-pair-Map
  ( ((A',A),α) : Map)
  ( ((B',B),β) : Map)
  ( ((C',C),γ) : Map)
  ( ((s',s),_) : map-Map ((A',A),α) ((B',B),β))
  ( ((t',t),_) : map-Map ((B',B),β) ((C',C),γ))
  : U
  :=
    product
    ( is-section-retraction-pair A' B' C' s' t')
    ( is-section-retraction-pair A B C s t)

#def has-external-retract-Map
  ( α β : Map)
  ( S : map-Map α β)
  : U
  :=
    Σ ((γ , T) : ( Σ (γ : Map) , (map-Map β γ)))
    , ( is-section-retraction-pair-Map α β γ S T)

#def is-external-retract-of-Map
  ( α β : Map)
  : U
  :=
    Σ (S : map-Map α β)
    , has-external-retract-Map α β S

#def is-retract-of-fibers-is-external-retract-of-Map
  ( A' A : U)
  ( α : A' → A)
  ( B' B : U)
  ( β : B' → B)
  ( ( ((s',s),ηs) , ( ( ((C',C),γ) , ((r',r),ηr)) , ( is-s-r' , is-s-r)))
    : is-external-retract-of-Map ((A',A),α) ((B',B),β))
  ( a : A)
  : is-retract-of (fib A' A α a) (fib B' B β (s a))
  :=
    ( ( map-of-fibers-map-of-maps A' A α B' B β ((s',s),ηs) a)
    , ( has-retraction-internalize
        ( fib A' A α a) (fib B' B β (s a))
        ( map-of-fibers-map-of-maps A' A α B' B β ((s',s),ηs) a)
        ( ( fib C' C γ (r (s a))
          , map-of-fibers-map-of-maps B' B β C' C γ ((r',r),ηr) (s a))
        , ( is-equiv-homotopy (fib A' A α a) (fib C' C γ (r (s a)))
                ( comp ( fib A' A α a) (fib B' B β (s a)) (fib C' C γ (r (s a)))
                  ( map-of-fibers-map-of-maps B' B β C' C γ ((r',r),ηr) ( s a))
                  ( map-of-fibers-map-of-maps A' A α B' B β ((s',s),ηs) ( a)))
                ( map-of-fibers-map-of-maps A' A α C' C γ
                  ( comp-map-of-maps A' A α B' B β C' C γ
                    ( (r',r),ηr) ((s',s),ηs))
                  (a))
            ( comp-map-of-fibers-comp-map-of-maps A' A α B' B β C' C γ
              ( (r',r),ηr) ((s',s),ηs)
              ( a))
            ( is-equiv-map-of-fibers-is-equiv-map-of-maps A' A α C' C γ
              ( comp-map-of-maps A' A α B' B β C' C γ ((r',r),ηr) ((s',s),ηs))
              ( is-s-r')
              ( is-s-r)
              ( a))))))
```

### Equivalences are closed under retracts

As an immediate corollary we obtain that equivalences are closed under retracts.

```rzk
#def is-equiv-is-retract-of-is-equiv
  ( A' A : U)
  ( α : A' → A)
  ( B' B : U)
  ( β : B' → B)
  ( (((s',s),ηs) , has-ext-retr-S)
    : is-external-retract-of-Map ((A',A),α) ((B',B),β))
  ( is-equiv-β : is-equiv B' B β)
  : is-equiv A' A α
  :=
  is-equiv-is-contr-map A' A α
  ( \ a →
    is-contr-is-retract-of-is-contr
    ( fib A' A α a) (fib B' B β (s a))
    ( is-retract-of-fibers-is-external-retract-of-Map A' A α B' B β
      ( ((s',s),ηs) , has-ext-retr-S)
      ( a))
    ( is-contr-map-is-equiv B' B β is-equiv-β (s a)))
```
