# 3. Equivalences

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Sections, retractions, and equivalences

```rzk
#section is-equiv

#variables A B : U

#def has-section
  ( f : A → B)
  : U
  := Σ (s : B → A) , (homotopy B B (comp B A B f s) (identity B))

#def has-retraction
  ( f : A → B)
  : U
  := Σ (r : B → A) , (homotopy A A (comp A B A r f) (identity A))
```

We define equivalences to be bi-invertible maps.

```rzk
#def is-equiv
  ( f : A → B)
  : U
  := product (has-retraction f) (has-section f)

#end is-equiv
```

### The identity is an equivalence

```rzk
#def is-equiv-identity
  ( A : U)
  : is-equiv A A (\ a → a)
  :=
    ( ( \ a → a , \ _ → refl) , (\ a → a , \ _ → refl))
```

## Equivalence data

```rzk
#section equivalence-data

#variables A B : U
#variable f : A → B
#variable is-equiv-f : is-equiv A B f

#def section-is-equiv uses (f)
  : B → A
  := first (second is-equiv-f)

#def has-section-is-equiv
  : has-section A B f
  := second is-equiv-f

#def retraction-is-equiv uses (f)
  : B → A
  := first (first is-equiv-f)

#def has-retraction-is-equiv
  : has-retraction A B f
  := first is-equiv-f
```

```rzk title="The homotopy between the section and retraction of an equivalence"
#def homotopy-section-retraction-is-equiv uses (f)
  : homotopy B A section-is-equiv retraction-is-equiv
  :=
    concat-homotopy B A
      ( section-is-equiv)
      ( triple-comp B A B A retraction-is-equiv f section-is-equiv)
      ( retraction-is-equiv)
      ( rev-homotopy B A
        ( triple-comp B A B A retraction-is-equiv f section-is-equiv)
        ( section-is-equiv)
        ( prewhisker-homotopy B A A
          ( comp A B A retraction-is-equiv f)
          ( identity A)
          ( second (first is-equiv-f))
          ( section-is-equiv)))
      ( postwhisker-homotopy B B A
        ( comp B A B f section-is-equiv)
        ( identity B)
        ( second (second is-equiv-f))
        ( retraction-is-equiv))

#end equivalence-data
```

## Invertible maps

The following type of more coherent equivalences is not a proposition.

```rzk
#def has-inverse
  ( A B : U)
  ( f : A → B)
  : U
  :=
    Σ ( g : B → A)
    , ( product
        ( homotopy A A (comp A B A g f) (identity A))
        ( homotopy B B (comp B A B f g) (identity B)))
```

## Equivalences are invertible maps

```rzk title="Invertible maps are equivalences"
#def is-equiv-has-inverse
  ( A B : U)
  ( f : A → B)
  ( has-inverse-f : has-inverse A B f)
  : is-equiv A B f
  :=
    ( ( first has-inverse-f , first (second has-inverse-f))
    , ( first has-inverse-f , second (second has-inverse-f)))
```

```rzk title="Equivalences are invertible"
#def has-inverse-is-equiv
  ( A B : U)
  ( f : A → B)
  ( is-equiv-f : is-equiv A B f)
  : has-inverse A B f
  :=
    ( section-is-equiv A B f is-equiv-f
    , ( concat-homotopy A A
        ( comp A B A (section-is-equiv A B f is-equiv-f) f)
        ( comp A B A (retraction-is-equiv A B f is-equiv-f) f)
        ( identity A)
        ( prewhisker-homotopy A B A
          ( section-is-equiv A B f is-equiv-f)
          ( retraction-is-equiv A B f is-equiv-f)
          ( homotopy-section-retraction-is-equiv A B f is-equiv-f)
          ( f))
        ( second (first is-equiv-f))
    , ( second (second is-equiv-f))))
```

## Invertible map data

```rzk
#section has-inverse-data

#variables A B : U
#variable f : A → B
#variable has-inverse-f : has-inverse A B f
```

```rzk title="The inverse of a map with an inverse"
#def map-inverse-has-inverse uses (f)
  : B → A
  := first (has-inverse-f)
```

The following are some iterated composites associated to a pair of invertible
maps.

```rzk
#def retraction-composite-has-inverse uses (B has-inverse-f)
  : A → A
  := comp A B A map-inverse-has-inverse f

#def section-composite-has-inverse uses (A has-inverse-f)
  : B → B
  := comp B A B f map-inverse-has-inverse
```

This composite is parallel to `#!rzk f`; we won't need the dual notion.

```rzk
#def triple-composite-has-inverse uses (has-inverse-f)
  : A → B
  := triple-comp A B A B f map-inverse-has-inverse f
```

This composite is also parallel to `#!rzk f`; again we won't need the dual
notion.

```rzk
#def quintuple-composite-has-inverse uses (has-inverse-f)
  : A → B
  := \ a → f (map-inverse-has-inverse (f (map-inverse-has-inverse (f a))))

#end has-inverse-data
```

## Symmetry of having an inverse

The inverse of an invertible map has an inverse.

```rzk
#def has-inverse-map-inverse-has-inverse
  ( A B : U)
  ( f : A → B)
  ( has-inverse-f : has-inverse A B f)
  : has-inverse B A (map-inverse-has-inverse A B f has-inverse-f)
  :=
    ( f
    , ( second (second has-inverse-f)
      , first (second has-inverse-f)))
```

## The type of equivalences

The type of equivalences between types uses `#!rzk is-equiv` rather than
`#!rzk has-inverse`.

```rzk
#def Equiv
  ( A B : U)
  : U
  := Σ (f : A → B) , (is-equiv A B f)
```

## Induction with section

We have two variants of induction with section that say that if `f : A → B` has
a section, it suffices to prove statements about `b : B` by doing so terms of
the form `f a`.

```rzk
#def ind-has-section
  ( A B : U)
  ( f : A → B)
  ( ( sec-f , ε-f) : has-section A B f)
  ( C : B → U)
  ( s : (a : A) → C (f a))
  ( b : B)
  : C b
  := transport B C (f (sec-f b)) b (ε-f b) (s (sec-f b))

#def ind-has-section'
  ( A B : U)
  ( f : A → B)
  ( ( sec-f , ε-f) : has-section A B f)
  ( C : B → U)
  ( c' : (b : B) → C (f (sec-f b)))
  ( b : B)
  : C b
  := transport B C (f (sec-f b)) b (ε-f b) (c' b)
```

It is convenient to have available the special case where `f` is an equivalence.

```rzk
#def ind-has-section-equiv
  ( A B : U)
  ( ( f , is-equiv-f) : Equiv A B)
  : ( C : B → U) → ((a : A) → C (f a)) → (b : B) → C b
  := ind-has-section A B f (second is-equiv-f)
```

## Composing equivalences

The data of an equivalence is not symmetric so we promote an equivalence to an
invertible map to prove symmetry:

```rzk
#def inv-equiv
  ( A B : U)
  ( e : Equiv A B)
  : Equiv B A
  :=
    ( first (has-inverse-is-equiv A B (first e) (second e))
    , ( ( first e
        , second (second (has-inverse-is-equiv A B (first e) (second e))))
      , ( first e
      , first (second (has-inverse-is-equiv A B (first e) (second e))))))
```

```rzk title="Composition of equivalences in diagrammatic order"
#def equiv-comp
  ( A B C : U)
  ( A≃B : Equiv A B)
  ( B≃C : Equiv B C)
  : Equiv A C
  :=
    ( ( \ a → first B≃C (first A≃B a))
    , ( ( ( \ c → first (first (second A≃B)) (first (first (second (B≃C))) c))
        , ( \ a →
            concat A
              ( first
                ( first (second A≃B))
                ( first
                  ( first (second B≃C))
                  ( first B≃C (first A≃B a))))
              ( first (first (second A≃B)) (first A≃B a))
              ( a)
              ( ap B A
                ( first (first (second B≃C)) (first B≃C (first A≃B a)))
                ( first A≃B a)
                ( first (first (second A≃B)))
                ( second (first (second B≃C)) (first A≃B a)))
              ( second (first (second A≃B)) a)))
      , ( ( \ c →
          first
            ( second (second A≃B))
            ( first (second (second (B≃C))) c))
        , ( \ c →
            concat C
              ( first B≃C
                ( first A≃B
                  ( first
                    ( second (second A≃B))
                    ( first (second (second B≃C)) c))))
              ( first B≃C (first (second (second B≃C)) c))
              ( c)
              ( ap B C
                ( first A≃B
                  ( first
                    ( second (second A≃B))
                    ( first (second (second B≃C)) c)))
                ( first (second (second B≃C)) c)
                ( first B≃C)
                ( second
                  ( second (second A≃B))
                  ( first (second (second B≃C)) c)))
              ( second (second (second B≃C)) c)))))
```

Now we compose the functions that are equivalences.

```rzk
#def is-equiv-comp
  ( A B C : U)
  ( f : A → B)
  ( is-equiv-f : is-equiv A B f)
  ( g : B → C)
  ( is-equiv-g : is-equiv B C g)
  : is-equiv A C (comp A B C g f)
  :=
    ( ( comp C B A
        ( retraction-is-equiv A B f is-equiv-f)
        ( retraction-is-equiv B C g is-equiv-g)
      , ( \ a →
          concat A
            ( retraction-is-equiv A B f is-equiv-f
              ( retraction-is-equiv B C g is-equiv-g (g (f a))))
            ( retraction-is-equiv A B f is-equiv-f (f a))
            ( a)
            ( ap B A
              ( retraction-is-equiv B C g is-equiv-g (g (f a)))
              ( f a)
              ( retraction-is-equiv A B f is-equiv-f)
              ( second (first is-equiv-g) (f a)))
            ( second (first is-equiv-f) a)))
    , ( comp C B A
        ( section-is-equiv A B f is-equiv-f)
        ( section-is-equiv B C g is-equiv-g)
      , ( \ c →
          concat C
            ( g (f (first (second is-equiv-f) (first (second is-equiv-g) c))))
            ( g (first (second is-equiv-g) c))
            ( c)
            ( ap B C
              ( f (first (second is-equiv-f) (first (second is-equiv-g) c)))
              ( first (second is-equiv-g) c)
              ( g)
              ( second (second is-equiv-f) (first (second is-equiv-g) c)))
            ( second (second is-equiv-g) c))))
```

```rzk title="Right cancellation of equivalences in diagrammatic order"
#def equiv-right-cancel
  ( A B C : U)
  ( A≃C : Equiv A C)
  ( B≃C : Equiv B C)
  : Equiv A B
  := equiv-comp A C B (A≃C) (inv-equiv B C B≃C)
```

```rzk title="Left cancellation of equivalences in diagrammatic order"
#def equiv-left-cancel
  ( A B C : U)
  ( A≃B : Equiv A B)
  ( A≃C : Equiv A C)
  : Equiv B C
  := equiv-comp B A C (inv-equiv A B A≃B) (A≃C)
```

The following functions refine `equiv-right-cancel` and `equiv-left-cancel` by
providing control over the underlying maps of the equivalence. They also weaken
the hypotheses: if a composite is an equivalence and the second map has a
retraction the first map is an equivalence, and dually.

```rzk
#def ap-cancel-has-retraction
  ( B C : U)
  ( g : B → C)
  ( ( retr-g , η-g) : has-retraction B C g)
  ( b b' : B)
  : ( g b = g b') → (b = b')
  :=
    \ gp →
      triple-concat B b (retr-g (g b)) (retr-g (g b')) b'
        ( rev B (retr-g (g b)) b
          ( η-g b))
        ( ap C B (g b) (g b') retr-g gp)
        ( η-g b')
```

```rzk title="Right cancellation of equivalence property in diagrammatic order"
#def is-equiv-right-cancel
  ( A B C : U)
  ( f : A → B)
  ( g : B → C)
  ( has-retraction-g : has-retraction B C g)
  ( ( ( retr-gf , η-gf) , (sec-gf , ε-gf)) : is-equiv A C (comp A B C g f))
  : is-equiv A B f
  :=
    ( ( comp B C A retr-gf g , η-gf)
    , ( comp B C A sec-gf g
      , \ b →
            ap-cancel-has-retraction B C g
            has-retraction-g (f (sec-gf (g b))) b
            ( ε-gf (g b))))
```

```rzk title="Left cancellation of equivalence property in diagrammatic order"
#def is-equiv-left-cancel
  ( A B C : U)
  ( f : A → B)
  ( has-section-f : has-section A B f)
  ( g : B → C)
  ( ( ( retr-gf , η-gf) , (sec-gf , ε-gf)) : is-equiv A C (comp A B C g f))
  : is-equiv B C g
  :=
    ( ( comp C A B f retr-gf
      , ind-has-section A B f has-section-f
          ( \ b → f (retr-gf (g b)) = b)
          ( \ a → ap A B (retr-gf (g (f a))) a f (η-gf a)))
    , ( comp C A B f sec-gf , ε-gf))
```

We typically apply the cancelation property in a setting where the composite and
one map are known to be equivalences, so we define versions of the above
functions with these stronger hypotheses.

```rzk
#def is-equiv-right-factor
  ( A B C : U)
  ( f : A → B)
  ( g : B → C)
  ( is-equiv-g : is-equiv B C g)
  ( is-equiv-gf : is-equiv A C (comp A B C g f))
  : is-equiv A B f
  :=
    is-equiv-right-cancel A B C f g (first is-equiv-g) is-equiv-gf

#def is-equiv-left-factor
  ( A B C : U)
  ( f : A → B)
  ( is-equiv-f : is-equiv A B f)
  ( g : B → C)
  ( is-equiv-gf : is-equiv A C (comp A B C g f))
  : is-equiv B C g
  :=
    is-equiv-left-cancel A B C f (second is-equiv-f) g is-equiv-gf
```

```rzk title="A composition of three equivalences"
#def equiv-triple-comp
  ( A B C D : U)
  ( A≃B : Equiv A B)
  ( B≃C : Equiv B C)
  ( C≃D : Equiv C D)
  : Equiv A D
  := equiv-comp A B D (A≃B) (equiv-comp B C D B≃C C≃D)

#def is-equiv-triple-comp
  ( A B C D : U)
  ( f : A → B)
  ( is-equiv-f : is-equiv A B f)
  ( g : B → C)
  ( is-equiv-g : is-equiv B C g)
  ( h : C → D)
  ( is-equiv-h : is-equiv C D h)
  : is-equiv A D (triple-comp A B C D h g f)
  :=
    is-equiv-comp A B D
      ( f)
      ( is-equiv-f)
      ( comp B C D h g)
      ( is-equiv-comp B C D g is-equiv-g h is-equiv-h)
```

## Equivalences and homotopy

If a map is homotopic to an equivalence it is an equivalence.

```rzk
#def is-equiv-homotopy
  ( A B : U)
  ( f g : A → B)
  ( H : homotopy A B f g)
  ( is-equiv-g : is-equiv A B g)
  : is-equiv A B f
  :=
    ( ( ( first (first is-equiv-g))
      , ( \ a →
          concat A
            ( first (first is-equiv-g) (f a))
            ( first (first is-equiv-g) (g a))
            ( a)
            ( ap B A (f a) (g a) (first (first is-equiv-g)) (H a))
            ( second (first is-equiv-g) a)))
    , ( ( first (second is-equiv-g))
      , ( \ b →
          concat B
            ( f (first (second is-equiv-g) b))
            ( g (first (second is-equiv-g) b))
            ( b)
            ( H (first (second is-equiv-g) b))
            ( second (second is-equiv-g) b))))

#def is-equiv-rev-homotopy
  ( A B : U)
  ( f g : A → B)
  ( H : homotopy A B f g)
  ( is-equiv-f : is-equiv A B f)
  : is-equiv A B g
  := is-equiv-homotopy A B g f (rev-homotopy A B f g H) is-equiv-f
```

## Reversing equivalences

The section associated with an equivalence is an equivalence.

```rzk
#def is-equiv-section-is-equiv
  ( A B : U)
  ( f : A → B)
  ( is-equiv-f : is-equiv A B f)
  : is-equiv B A (section-is-equiv A B f is-equiv-f)
  :=
    is-equiv-has-inverse B A
      ( section-is-equiv A B f is-equiv-f)
      ( has-inverse-map-inverse-has-inverse A B f
        ( has-inverse-is-equiv A B f is-equiv-f))
```

The retraction associated with an equivalence is an equivalence.

```rzk
#def is-equiv-retraction-is-equiv
  ( A B : U)
  ( f : A → B)
  ( is-equiv-f : is-equiv A B f)
  : is-equiv B A (retraction-is-equiv A B f is-equiv-f)
  :=
    is-equiv-rev-homotopy B A
      ( section-is-equiv A B f is-equiv-f)
      ( retraction-is-equiv A B f is-equiv-f)
      ( homotopy-section-retraction-is-equiv A B f is-equiv-f)
      ( is-equiv-section-is-equiv A B f is-equiv-f)
```

## Section-retraction pairs

A pair of maps `s : A → B` and `r : B → A'` is a **section-retraction pair** if
the composite `A → A'` is an equivalence.

```rzk
#def is-section-retraction-pair
  ( A B A' : U)
  ( s : A → B)
  ( r : B → A')
  : U
  := is-equiv A A' (comp A B A' r s)
```

When we have such a section-retraction pair `(s, r)`, we say that `r` is an
**external retraction** of `s` and `s` is an **external section** of `r`.

```rzk
#def has-external-retraction
  ( A B : U)
  ( s : A → B)
  : U
  :=
    Σ ( ( A' , r) : (Σ (A' : U) , B → A'))
    , ( is-section-retraction-pair A B A' s r)

#def has-external-section
  ( B A' : U)
  ( r : B → A')
  : U
  :=
    Σ ( ( A , s) : (Σ (A : U) , A → B))
    , ( is-section-retraction-pair A B A' s r)
```

Note that exactly like `has-section` and `has-retraction` these are not
_properties_ of `s` or `r`, but structure.

Without univalence, we cannot yet show that the types `has-external-retraction`
and `has-retraction` (and their section counterparts, respectively) are
equivalent, so we content ourselves in showing that there is a logical
biimplication between them.

```rzk
#def is-equiv-retraction-section
  ( A B : U)
  ( s : A → B)
  ( r : B → A)
  ( η : (a : A) → r (s a) = a)
  : is-equiv A A (\ a → r (s a))
  :=
    is-equiv-homotopy A A (\ a → r (s (a))) (identity A)
      ( η) (is-equiv-identity A)

#def has-retraction-externalize
  ( A B : U)
  ( s : A → B)
  ( ( r , η) : has-retraction A B s)
  : has-external-retraction A B s
  :=
    ( ( A , r)
    , is-equiv-retraction-section A B s r η)

#def has-section-externalize
  ( B A' : U)
  ( r : B → A')
  ( ( s , ε) : has-section B A' r)
  : has-external-section B A' r
  :=
    ( ( A' , s)
    , is-equiv-retraction-section A' B s r ε)

#def has-retraction-internalize
  ( A B : U)
  ( s : A → B)
  ( ( ( A' , r) , ((rec-rs , η-rs) , _))
 : has-external-retraction A B s)
  : has-retraction A B s
  := (comp B A' A rec-rs r , η-rs)

#def has-section-internalize
  ( B A' : U)
  ( r : B → A')
  ( ( ( A , s) , (_ , (sec-rs , ε-rs)))
 : has-external-section B A' r)
  : has-section B A' r
  := (comp A' A B s sec-rs , ε-rs)
```

A consequence of the above is that in a section-retraction pair `(s, r)`, the
map `s` is a section and the map `r` is a retraction. Note that not every
composable pair `(s, r)` of such maps is a section-retraction pair; they have to
(up to composition with an equivalence) be section and retraction _of each
other_.

In a section-retraction pair, if one of `s : A → B` and `r : B → A'` is an
equivalence, then so is the other.

This is just a rephrasing of `is-equiv-left-factor` and `is-equiv-right-factor`.

```rzk
#section is-equiv-is-section-retraction-pair

#variables A B A' : U
#variable s : A → B
#variable r : B → A'

#variable is-sec-rec-pair : is-section-retraction-pair A B A' s r

#def is-equiv-section-is-equiv-retraction-is-section-retraction-pair
  ( is-equiv-r : is-equiv B A' r)
  : is-equiv A B s
  :=
    is-equiv-right-factor A B A' s r
    ( is-equiv-r) (is-sec-rec-pair)

#def is-equiv-retraction-is-equiv-section-is-section-retraction-pair
  ( is-equiv-s : is-equiv A B s)
  : is-equiv B A' r
  :=
    is-equiv-left-factor A B A'
    ( s) (is-equiv-s)
    ( r) (is-sec-rec-pair)

#end is-equiv-is-section-retraction-pair
```

## Retracts

We say that a type `A` is a retract of a type `B` if we have a map `s : A → B`
which has a retraction.

```rzk title="The type of proofs that A is a retract of B"
#def is-retract-of
  ( A B : U)
  : U
  := Σ (s : A → B) , has-retraction A B s

#def section-is-retract-of
  ( A B : U)
  ( ( s , (_ , _)) : is-retract-of A B)
  : A → B
  := s

#def retraction-is-retract-of
  ( A B : U)
  ( ( _ , (r , _)) : is-retract-of A B)
  : B → A
  := r

#def homotopy-is-retract-of
  ( A B : U)
  ( ( s , (r , η)) : is-retract-of A B)
  : homotopy A A (\ a → r (s a)) (identity A)
  := η
```

Section-retraction pairs `A → B → A'` are a convenient way to exhibit both `A`
and `A'` as retracts of `B`.

```rzk
#def is-retract-of-left-section-retraction-pair
  ( A B A' : U)
  ( s : A → B)
  ( r : B → A')
  ( is-sr-pair-sr : is-section-retraction-pair A B A' s r)
  : is-retract-of A B
  :=
    ( ( s)
    , ( has-retraction-internalize A B s ((A' , r) , is-sr-pair-sr)))

#def is-retract-of-right-section-retraction-pair
  ( A B A' : U)
  ( s : A → B)
  ( r : B → A')
  ( is-sr-pair-sr : is-section-retraction-pair A B A' s r)
  : is-retract-of A' B
  :=
    ( first (has-section-internalize B A' r ((A , s) , is-sr-pair-sr))
    , ( r
      , second (has-section-internalize B A' r ((A , s) , is-sr-pair-sr))))
```

## Function extensionality

By path induction, an identification between functions defines a homotopy.

```rzk
#def htpy-eq
  ( X : U)
  ( A : X → U)
  ( f g : (x : X) → A x)
  ( p : f = g)
  : ( x : X) → (f x = g x)
  :=
    ind-path
      ( ( x : X) → A x)
      ( f)
      ( \ g' p' → (x : X) → (f x = g' x))
      ( \ x → refl)
      ( g)
      ( p)
```

The function extensionality axiom asserts that this map defines a family of
equivalences.

```rzk title="The type that encodes the function extensionality axiom"
#def FunExt
  : U
  :=
    ( X : U)
  → ( A : X → U)
  → ( f : (x : X) → A x)
  → ( g : (x : X) → A x)
  → is-equiv (f = g) ((x : X) → f x = g x) (htpy-eq X A f g)
```

In the formalisations below, some definitions will assume function
extensionality:

```rzk
#assume funext : FunExt
```

Whenever a definition (implicitly) uses function extensionality, we write
`#!rzk uses (funext)`. In particular, the following definitions rely on function
extensionality:

```rzk title="The equivalence provided by function extensionality"
#def equiv-FunExt uses (funext)
  ( X : U)
  ( A : X → U)
  ( f g : (x : X) → A x)
  : Equiv (f = g) ((x : X) → f x = g x)
  := (htpy-eq X A f g , funext X A f g)
```

In particular, function extensionality implies that homotopies give rise to
identifications. This defines `#!rzk eq-htpy` to be the retraction to
`#!rzk htpy-eq`.

```rzk
#def eq-htpy uses (funext)
  ( X : U)
  ( A : X → U)
  ( f g : (x : X) → A x)
  : ( ( x : X) → f x = g x) → (f = g)
  := first (first (funext X A f g))

#def left-cancel-is-equiv uses (funext)
  ( A B : U)
  ( f : A → B)
  ( is-equiv-f : is-equiv A B f)
  : ( comp A B A (π₁ (π₁ is-equiv-f)) f) = (identity A)
  :=
    eq-htpy A (\ x' → A)
    ( comp A B A (π₁ (π₁ is-equiv-f)) f)
    ( identity A)
    ( π₂ (π₁ is-equiv-f))

#def right-cancel-is-equiv uses (funext)
  ( A B : U)
  ( f : A → B)
  ( is-equiv-f : is-equiv A B f)
  : ( comp B A B f (π₁ (π₂ is-equiv-f))) = (identity B)
  :=
    eq-htpy B (\ x' → B)
    ( comp B A B f (π₁ (π₂ is-equiv-f)))
    ( identity B)
    ( π₂ (π₂ is-equiv-f))
```

Using function extensionality, a fiberwise equivalence defines an equivalence of
dependent function types.

```rzk
#def is-equiv-function-is-equiv-family uses (funext)
  ( X : U)
  ( A B : X → U)
  ( f : (x : X) → (A x) → (B x))
  ( famisequiv : (x : X) → is-equiv (A x) (B x) (f x))
  : is-equiv ((x : X) → A x) ((x : X) → B x) (\ a x → f x (a x))
  :=
    ( ( ( \ b x → first (first (famisequiv x)) (b x))
      , ( \ a →
           eq-htpy
            X A
           ( \ x →
              first
                ( first (famisequiv x))
                ( f x (a x)))
            ( a)
            ( \ x → second (first (famisequiv x)) (a x))))
    , ( ( \ b x → first (second (famisequiv x)) (b x))
      , ( \ b →
            eq-htpy
            X B
            ( \ x → f x (first (second (famisequiv x)) (b x)))
            ( b)
            ( \ x → second (second (famisequiv x)) (b x)))))
```

```rzk
#def equiv-function-equiv-family uses (funext)
  ( X : U)
  ( A B : X → U)
  ( famequiv : (x : X) → Equiv (A x) (B x))
  : Equiv ((x : X) → A x) ((x : X) → B x)
  :=
    ( ( \ a x → (first (famequiv x)) (a x))
    , ( is-equiv-function-is-equiv-family
        ( X)
        ( A)
        ( B)
        ( \ x ax → first (famequiv x) (ax))
        ( \ x → second (famequiv x))))
```

## Embeddings

```rzk
#def is-emb
  ( A B : U)
  ( f : A → B)
  : U
  := (x : A) → (y : A) → is-equiv (x = y) (f x = f y) (ap A B x y f)

#def Emb
  ( A B : U)
  : U
  := (Σ (f : A → B) , is-emb A B f)

#def is-emb-is-inhabited-emb
  ( A B : U)
  ( f : A → B)
  ( e : A → is-emb A B f)
  : is-emb A B f
  := \ x y → e x x y

#def inv-ap-is-emb
  ( A B : U)
  ( f : A → B)
  ( is-emb-f : is-emb A B f)
  ( x y : A)
  ( p : f x = f y)
  : ( x = y)
  := first (first (is-emb-f x y)) p
```

## Reversal is an equivalence

```rzk
#def equiv-rev
  ( A : U)
  ( x y : A)
  : Equiv (x = y) (y = x)
  := (rev A x y , ((rev A y x , rev-rev A x y) , (rev A y x , rev-rev A y x)))
```

```rzk
#def ind-rev
  ( A : U)
  ( x y : A)
  ( B : (x = y) → U)
  : ( ( p : y = x) → B (rev A y x p)) → (q : x = y) → B q
  :=
    ind-has-section-equiv (y = x) (x = y) (equiv-rev A y x) (B)
```

## Concatenation with a fixed path is an equivalence

```rzk
#def equiv-preconcat
  ( A : U)
  ( x y z : A)
  ( p : x = y)
  : Equiv (y = z) (x = z)
  :=
    ( concat A x y z p
    , ( ( concat A y x z (rev A x y p) , retraction-preconcat A x y z p)
      , ( concat A y x z (rev A x y p) , section-preconcat A x y z p)))

#def equiv-postconcat
  ( A : U)
  ( x y z : A)
  ( q : y = z)
  : Equiv (x = y) (x = z)
  :=
    ( \ p → concat A x y z p q
    , ( ( \ r → concat A x z y r (rev A y z q)
        , retraction-postconcat A x y z q)
      , ( \ r → concat A x z y r (rev A y z q)
        , section-postconcat A x y z q)))
```

## Transport along a path is an equivalence

```rzk
#def is-equiv-transport
  ( A : U)
  ( C : A → U)
  ( x : A)
  : ( y : A) → (p : x = y) → is-equiv (C x) (C y) (transport A C x y p)
  := ind-path A x
       ( \ y p → is-equiv (C x) (C y) (transport A C x y p))
       ( is-equiv-identity (C x))

#def equiv-transport
  ( A : U)
  ( C : A → U)
  ( x y : A)
  ( p : x = y)
  : Equiv (C x) (C y)
  := (transport A C x y p , is-equiv-transport A C x y p)
```

## Equivalence is equivalence invariant

```rzk
#def map-of-maps
  ( A' A : U)
  ( α : A' → A)
  ( B' B : U)
  ( β : B' → B)
  : U
  :=
    Σ ( ( s' , s) : product (A' → B') (A → B))
    , ( ( a' : A') → β (s' a') = s (α a'))

#def map-Map
  ( ( ( A' , A) , α) : Map)
  ( ( ( B' , B) , β) : Map)
  : U
  := map-of-maps A' A α B' B β

#def Equiv-of-maps
  ( A' A : U)
  ( α : A' → A)
  ( B' B : U)
  ( β : B' → B)
  : U
  :=
    Σ ( ( ( s' , s) , _) : map-of-maps A' A α B' B β)
    , ( product
        ( is-equiv A' B' s')
        ( is-equiv A B s))

#def is-equiv-equiv-is-equiv
  ( A' A : U)
  ( α : A' → A)
  ( B' B : U)
  ( β : B' → B)
  ( ( ( s' , s) , η) : map-of-maps A' A α B' B β)
  ( is-equiv-s' : is-equiv A' B' s')
  ( is-equiv-s : is-equiv A B s)
  ( is-equiv-β : is-equiv B' B β)
  : is-equiv A' A α
  :=
    is-equiv-right-factor A' A B α s is-equiv-s
      ( is-equiv-rev-homotopy A' B
        ( comp A' B' B β s')
        ( comp A' A B s α)
        ( η)
        ( is-equiv-comp A' B' B s' is-equiv-s' β is-equiv-β))

#def is-equiv-Equiv-is-equiv
  ( A' A : U)
  ( α : A' → A)
  ( B' B : U)
  ( β : B' → B)
  ( ( S , (is-equiv-s' , is-equiv-s)) : Equiv-of-maps A' A α B' B β)
  : is-equiv B' B β → is-equiv A' A α
  := is-equiv-equiv-is-equiv A' A α B' B β S is-equiv-s' is-equiv-s

#def is-equiv-equiv-is-equiv'
  ( A' A : U)
  ( α : A' → A)
  ( B' B : U)
  ( β : B' → B)
  ( ( ( s' , s) , η) : map-of-maps A' A α B' B β)
  ( is-equiv-s' : is-equiv A' B' s')
  ( is-equiv-s : is-equiv A B s)
  ( is-equiv-α : is-equiv A' A α)
  : is-equiv B' B β
  :=
    is-equiv-left-factor A' B' B s' is-equiv-s' β
      ( is-equiv-homotopy A' B
        ( comp A' B' B β s')
        ( comp A' A B s α)
        ( η)
        ( is-equiv-comp A' A B α is-equiv-α s is-equiv-s))

#def is-equiv-Equiv-is-equiv'
  ( A' A : U)
  ( α : A' → A)
  ( B' B : U)
  ( β : B' → B)
  ( ( S , (is-equiv-s' , is-equiv-s)) : Equiv-of-maps A' A α B' B β)
  : is-equiv A' A α → is-equiv B' B β
  := is-equiv-equiv-is-equiv' A' A α B' B β S is-equiv-s' is-equiv-s
```
