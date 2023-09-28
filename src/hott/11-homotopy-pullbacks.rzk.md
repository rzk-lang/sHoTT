# 11. Homotopy pullbacks

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Homotopy cartesian squares

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

#def is-homotopy-cartesian uses (A)
  : U
  :=
    ( a' : A') → is-equiv (C' a') (C (α a')) (γ a')
```

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
        ( family-of-equiv-total-equiv
          ( A' )
          ( C' )
          ( \ a' → C (α a') )
          ( γ)
          ( \ a' → is-hc-α-γ a'))
        ( \ (a', c) → (α a', c) )
        ( second
          ( total-equiv-pullback-is-equiv
            ( A')
            ( A )
            ( α )
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
    total-equiv-family-of-equiv
        A' C' ( \ x → C (α x) ) γ    -- use x instead of a' to avoid shadowing
        ( is-equiv-right-factor
            ( total-type A' C')
            ( Σ (x : A'), C (α x))
            ( total-type A C)
            ( total-map A' C' (\ x → C (α x)) γ)
            ( \ (x, c) → (α x, c) )
            ( second ( total-equiv-pullback-is-equiv A' A α is-equiv-α C))
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

Form this interaction with equivalences we deduce corresponding facts about
vertical pasting and cancellation of homotopy cartesian squares.

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

#def is-homotopy-cartesian-lower-cancellation
  ( is-hc-α-γ : is-homotopy-cartesian A' C' A C α γ )
  ( is-hc-α-δ : is-homotopy-cartesian-vertical-pasted
  )
  : is-homotopy-cartesian-upper
  :=
    is-homotopy-cartesian-upper-from-fibers
    ( \ a' →
        is-homotopy-cartesian-is-horizontal-equiv
        ( C' a') (D' a') (C (α a')) (D (α a')) (γ a') (δ a')
        ( is-hc-α-γ a')
        ( is-hc-α-δ a'))

#def is-homotopy-cartesian-upper-cancellation-with-section
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

#def is-homotopy-cartesian-right-cancellation
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

#end homotopy-cartesian-horizontal-calculus
```
