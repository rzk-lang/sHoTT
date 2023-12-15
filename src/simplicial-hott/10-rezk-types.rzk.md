# Rezk types

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

Some of the definitions in this file rely on function extensionality, extension
extensionality and weak function extensionality:

```rzk
#assume funext : FunExt
#assume extext : ExtExt
#assume weakfunext : WeakFunExt
```

## Isomorphisms

```rzk
#def has-retraction-arrow
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  ( f : hom A x y)
  ( g : hom A y x)
  : U
  := (comp-is-segal A is-segal-A x y x f g) =_{hom A x x} (id-hom A x)

#def Retraction-arrow
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  ( f : hom A x y)
  : U
  := Σ (g : hom A y x) , (has-retraction-arrow A is-segal-A x y f g)

#def has-section-arrow
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  ( f : hom A x y)
  ( h : hom A y x)
  : U
  := (comp-is-segal A is-segal-A y x y h f) =_{hom A y y} (id-hom A y)

#def Section-arrow
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  ( f : hom A x y)
  : U
  := Σ (h : hom A y x) , (has-section-arrow A is-segal-A x y f h)

#def is-iso-arrow
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  ( f : hom A x y)
  : U
  :=
    product
    ( Retraction-arrow A is-segal-A x y f)
    ( Section-arrow A is-segal-A x y f)

#def Iso
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  : U
  := Σ (f : hom A x y) , is-iso-arrow A is-segal-A x y f
```

## Invertible arrows

We now show that `#!rzk f : hom A a x` is an isomorphism if and only if it is
invertible, meaning `#!rzk f` has a two-sided composition inverse
`#!rzk g : hom A x a`.

```rzk
#def has-inverse-arrow
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  ( f : hom A x y)
  : U
  :=
    Σ ( g : hom A y x)
    , product
      ( has-retraction-arrow A is-segal-A x y f g)
      ( has-section-arrow A is-segal-A x y f g)

#def is-iso-arrow-has-inverse-arrow
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  ( f : hom A x y)
  : ( has-inverse-arrow A is-segal-A x y f) → (is-iso-arrow A is-segal-A x y f)
  :=
    ( \ (g , (p , q)) → ((g , p) , (g , q)))

#def has-inverse-arrow-is-iso-arrow uses (extext)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  ( f : hom A x y)
  : ( is-iso-arrow A is-segal-A x y f) → (has-inverse-arrow A is-segal-A x y f)
  :=
    ( \ ((g , p) , (h , q)) →
      ( g
      , ( p
        , ( concat
            ( hom A y y)
            ( comp-is-segal A is-segal-A y x y g f)
            ( comp-is-segal A is-segal-A y x y h f)
            ( id-hom A y)
            ( postwhisker-homotopy-is-segal A is-segal-A y x y g h f
              ( alternating-quintuple-concat
                ( hom A y x)
                ( g)
                ( comp-is-segal A is-segal-A y y x (id-hom A y) g)
                ( rev
                  ( hom A y x)
                  ( comp-is-segal A is-segal-A y y x (id-hom A y) g)
                  ( g)
                  ( id-comp-is-segal A is-segal-A y x g))
                ( comp-is-segal A is-segal-A y y x
                  ( comp-is-segal A is-segal-A y x y h f) (g))
                ( postwhisker-homotopy-is-segal A is-segal-A y y x
                  ( id-hom A y)
                  ( comp-is-segal A is-segal-A y x y h f)
                  ( g)
                  ( rev
                    ( hom A y y)
                    ( comp-is-segal A is-segal-A y x y h f)
                    ( id-hom A y)
                    ( q)))
                ( comp-is-segal A is-segal-A y x x
                  ( h)
                  ( comp-is-segal A is-segal-A x y x f g))
                ( associative-is-segal extext A is-segal-A y x y x h f g)
                ( comp-is-segal A is-segal-A y x x h (id-hom A x))
                ( prewhisker-homotopy-is-segal A is-segal-A y x x h
                  ( comp-is-segal A is-segal-A x y x f g)
                  ( id-hom A x) p)
                ( h)
                ( comp-id-is-segal A is-segal-A y x h)))
            ( q)))))
```

```rzk title="RS17, Proposition 10.1"
#def inverse-iff-iso-arrow uses (extext)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  ( f : hom A x y)
  : iff (has-inverse-arrow A is-segal-A x y f) (is-iso-arrow A is-segal-A x y f)
  :=
    ( is-iso-arrow-has-inverse-arrow A is-segal-A x y f
    , has-inverse-arrow-is-iso-arrow A is-segal-A x y f)
```

## Being an isomorphism is a proposition

The predicate `#!rzk is-iso-arrow` is a proposition.

```rzk
#def has-retraction-postcomp-has-retraction uses (extext)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  ( f : hom A x y)
  ( g : hom A y x)
  ( gg : has-retraction-arrow A is-segal-A x y f g)
  : ( z : A)
  → has-retraction (hom A z x) (hom A z y)
      ( postcomp-is-segal A is-segal-A x y f z)
  :=
    \ z →
    ( ( postcomp-is-segal A is-segal-A y x g z)
      , \ k →
      ( triple-concat
        ( hom A z x)
        ( comp-is-segal A is-segal-A z y x
          ( comp-is-segal A is-segal-A z x y k f) g)
        ( comp-is-segal A is-segal-A z x x
          k (comp-is-segal A is-segal-A x y x f g))
        ( comp-is-segal A is-segal-A z x x k (id-hom A x))
        ( k)
        ( associative-is-segal extext A is-segal-A z x y x k f g)
        ( prewhisker-homotopy-is-segal A is-segal-A z x x k
          ( comp-is-segal A is-segal-A x y x f g) (id-hom A x) gg)
        ( comp-id-is-segal A is-segal-A z x k)))

#def has-section-postcomp-has-section uses (extext)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  ( f : hom A x y)
  ( h : hom A y x)
  ( hh : has-section-arrow A is-segal-A x y f h)
  : ( z : A)
  → has-section (hom A z x) (hom A z y) (postcomp-is-segal A is-segal-A x y f z)
  :=
    \ z →
    ( ( postcomp-is-segal A is-segal-A y x h z)
      , \ k →
        ( triple-concat
          ( hom A z y)
          ( comp-is-segal A is-segal-A z x y
            ( comp-is-segal A is-segal-A z y x k h) f)
          ( comp-is-segal A is-segal-A z y y
            k (comp-is-segal A is-segal-A y x y h f))
          ( comp-is-segal A is-segal-A z y y k (id-hom A y))
          ( k)
          ( associative-is-segal extext A is-segal-A z y x y k h f)
          ( prewhisker-homotopy-is-segal A is-segal-A z y y k
            ( comp-is-segal A is-segal-A y x y h f) (id-hom A y) hh)
          ( comp-id-is-segal A is-segal-A z y k)))

#def is-equiv-postcomp-is-iso uses (extext)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  ( f : hom A x y)
  ( g : hom A y x)
  ( gg : has-retraction-arrow A is-segal-A x y f g)
  ( h : hom A y x)
  ( hh : has-section-arrow A is-segal-A x y f h)
  : ( z : A)
  → is-equiv (hom A z x) (hom A z y) (postcomp-is-segal A is-segal-A x y f z)
  :=
    \ z →
    ( ( has-retraction-postcomp-has-retraction A is-segal-A x y f g gg z)
    , ( has-section-postcomp-has-section A is-segal-A x y f h hh z))

#def has-retraction-precomp-has-section uses (extext)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  ( f : hom A x y)
  ( h : hom A y x)
  ( hh : has-section-arrow A is-segal-A x y f h)
  : ( z : A)
  → has-retraction (hom A y z) (hom A x z)
      ( precomp-is-segal A is-segal-A x y f z)
  :=
    \ z →
    ( ( precomp-is-segal A is-segal-A y x h z)
      , \ k →
        ( triple-concat
          ( hom A y z)
          ( comp-is-segal A is-segal-A y x z
            h (comp-is-segal A is-segal-A x y z f k))
          ( comp-is-segal A is-segal-A y y z
            ( comp-is-segal A is-segal-A y x y h f) k)
          ( comp-is-segal A is-segal-A y y z (id-hom A y) k)
          ( k)
          ( rev
            ( hom A y z)
            ( comp-is-segal A is-segal-A y y z
              ( comp-is-segal A is-segal-A y x y h f) k)
            ( comp-is-segal A is-segal-A y x z
              h (comp-is-segal A is-segal-A x y z f k))
            ( associative-is-segal extext A is-segal-A y x y z h f k))
          ( postwhisker-homotopy-is-segal A is-segal-A y y z
            ( comp-is-segal A is-segal-A y x y h f)
            ( id-hom A y) k hh)
          ( id-comp-is-segal A is-segal-A y z k)
        )
    )

#def has-section-precomp-has-retraction uses (extext)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  ( f : hom A x y)
  ( g : hom A y x)
  ( gg : has-retraction-arrow A is-segal-A x y f g)
  : ( z : A)
  → has-section (hom A y z) (hom A x z) (precomp-is-segal A is-segal-A x y f z)
  :=
    \ z →
    ( ( precomp-is-segal A is-segal-A y x g z)
      , \ k →
        ( triple-concat
          ( hom A x z)
          ( comp-is-segal A is-segal-A x y z
            f (comp-is-segal A is-segal-A y x z g k))
          ( comp-is-segal A is-segal-A x x z
            ( comp-is-segal A is-segal-A x y x f g) k)
          ( comp-is-segal A is-segal-A x x z
            ( id-hom A x) k)
          ( k)
          ( rev
            ( hom A x z)
            ( comp-is-segal A is-segal-A x x z
              ( comp-is-segal A is-segal-A x y x f g) k)
            ( comp-is-segal A is-segal-A x y z
              f (comp-is-segal A is-segal-A y x z g k))
            ( associative-is-segal extext A is-segal-A x y x z f g k))
          ( postwhisker-homotopy-is-segal A is-segal-A x x z
            ( comp-is-segal A is-segal-A x y x f g)
            ( id-hom A x)
            ( k)
            ( gg))
          ( id-comp-is-segal A is-segal-A x z k)))

#def is-equiv-precomp-is-iso uses (extext)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  ( f : hom A x y)
  ( g : hom A y x)
  ( gg : has-retraction-arrow A is-segal-A x y f g)
  ( h : hom A y x)
  ( hh : has-section-arrow A is-segal-A x y f h)
  : ( z : A)
  → is-equiv (hom A y z) (hom A x z) (precomp-is-segal A is-segal-A x y f z)
  :=
    \ z →
      ( ( has-retraction-precomp-has-section A is-segal-A x y f h hh z)
      , ( has-section-precomp-has-retraction A is-segal-A x y f g gg z))

#def is-contr-Retraction-arrow-is-iso uses (extext)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  ( f : hom A x y)
  ( g : hom A y x)
  ( gg : has-retraction-arrow A is-segal-A x y f g)
  ( h : hom A y x)
  ( hh : has-section-arrow A is-segal-A x y f h)
  : is-contr (Retraction-arrow A is-segal-A x y f)
  :=
    ( is-contr-map-is-equiv
      ( hom A y x)
      ( hom A x x)
      ( precomp-is-segal A is-segal-A x y f x)
      ( is-equiv-precomp-is-iso A is-segal-A x y f g gg h hh x))
    ( id-hom A x)

#def is-contr-Section-arrow-is-iso uses (extext)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  ( f : hom A x y)
  ( g : hom A y x)
  ( gg : has-retraction-arrow A is-segal-A x y f g)
  ( h : hom A y x)
  ( hh : has-section-arrow A is-segal-A x y f h)
  : is-contr (Section-arrow A is-segal-A x y f)
  :=
    ( is-contr-map-is-equiv
      ( hom A y x)
      ( hom A y y)
      ( postcomp-is-segal A is-segal-A x y f y)
      ( is-equiv-postcomp-is-iso A is-segal-A x y f g gg h hh y))
    ( id-hom A y)

#def is-contr-is-iso-arrow-is-iso uses (extext)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  ( f : hom A x y)
  ( g : hom A y x)
  ( gg : has-retraction-arrow A is-segal-A x y f g)
  ( h : hom A y x)
  ( hh : has-section-arrow A is-segal-A x y f h)
  : is-contr (is-iso-arrow A is-segal-A x y f)
  :=
    ( is-contr-product
      ( Retraction-arrow A is-segal-A x y f)
      ( Section-arrow A is-segal-A x y f)
      ( is-contr-Retraction-arrow-is-iso A is-segal-A x y f g gg h hh)
      ( is-contr-Section-arrow-is-iso A is-segal-A x y f g gg h hh))
```

```rzk title="RS17, Proposition 10.2"
#def is-prop-is-iso-arrow uses (extext)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  ( f : hom A x y)
  : ( is-prop (is-iso-arrow A is-segal-A x y f))
  :=
    ( is-prop-is-contr-is-inhabited
      ( is-iso-arrow A is-segal-A x y f)
      ( \ is-isof →
        ( is-contr-is-iso-arrow-is-iso A is-segal-A x y f
          ( first (first is-isof))
          ( second (first is-isof))
          ( first (second is-isof))
          ( second (second is-isof)))))
```

## Isomorphism extensionality

```rzk title="RS17, Proposition 10.3"
#def ev-components-nat-trans-preserves-iso uses (funext)
  ( X : U)
  ( A : X → U)
  ( is-segal-A : (x : X) → is-segal (A x))
  ( f g : (x : X) → A x)
  ( α : nat-trans X A f g)
  : ( is-iso-arrow
      ( ( x : X) → A x)
      ( is-segal-function-type funext X A is-segal-A) f g α)
  → ( x : X)
  → ( is-iso-arrow (A x) (is-segal-A x) (f x) (g x)
      ( ev-components-nat-trans X A f g α x))
  :=
    \ ((β , p) , (γ , q)) →
    \ x →
    ( ( ( ev-components-nat-trans X A g f β x)
      , ( triple-concat
          ( hom (A x) (f x) (f x))
          ( comp-is-segal (A x) (is-segal-A x) (f x) (g x) (f x)
            ( ev-components-nat-trans X A f g α x)
            ( ev-components-nat-trans X A g f β x))
          ( ev-components-nat-trans X A f f
            ( comp-is-segal
              ( ( x' : X) → (A x'))
              ( is-segal-function-type funext X A is-segal-A) f g f α β)
            ( x))
          ( ev-components-nat-trans X A f f (id-hom ((x' : X) → (A x')) f) x)
          ( id-hom (A x) (f x))
          ( comp-components-comp-nat-trans-is-segal
            funext X A is-segal-A f g f α β x)
          ( ap
            ( nat-trans X A f f)
            ( hom (A x) (f x) (f x))
            ( comp-is-segal
              ( ( x' : X) → (A x'))
              ( is-segal-function-type funext X A is-segal-A) f g f α β)
            ( id-hom ((x' : X) → (A x')) f)
            ( \ α' → ev-components-nat-trans X A f f α' x)
            ( p))
          ( id-arr-components-id-nat-trans X A f x)))
    , ( ( ev-components-nat-trans X A g f γ x)
      , ( triple-concat
          ( hom (A x) (g x) (g x))
          ( comp-is-segal (A x) (is-segal-A x) (g x) (f x) (g x)
            ( ev-components-nat-trans X A g f γ x)
            ( ev-components-nat-trans X A f g α x))
          ( ev-components-nat-trans X A g g
            ( comp-is-segal
              ( ( x' : X) → (A x'))
              ( is-segal-function-type funext X A is-segal-A) g f g γ α)
            ( x))
          ( ev-components-nat-trans X A g g (id-hom ((x' : X) → (A x')) g) x)
          ( id-hom (A x) (g x))
          ( comp-components-comp-nat-trans-is-segal
            funext X A is-segal-A g f g γ α x)
          ( ap
            ( nat-trans X A g g)
            ( hom (A x) (g x) (g x))
            ( comp-is-segal
              ( ( x' : X) → (A x'))
              ( is-segal-function-type funext X A is-segal-A) g f g γ α)
            ( id-hom ((x' : X) → (A x')) g)
            ( \ α' → ev-components-nat-trans X A g g α' x)
            ( q))
          ( id-arr-components-id-nat-trans X A g x))))

#def nat-trans-nat-trans-components-preserves-iso-helper uses (funext)
  ( X : U)
  ( A : X → U)
  ( is-segal-A : (x : X) → is-segal (A x))
  ( f g : (x : X) → A x)
  ( α : nat-trans X A f g)
  ( β : nat-trans X A g f)
  : ( ( x : X)
    → ( comp-is-segal (A x) (is-segal-A x) (f x) (g x) (f x)
        ( ev-components-nat-trans X A f g α x)
        ( ev-components-nat-trans X A g f β x))
    = ( id-hom (A x) (f x)))
  → ( comp-is-segal
      ( ( x' : X) → A x')
      ( is-segal-function-type funext X A is-segal-A)
      f g f α β)
  = ( id-hom ((x' : X) → A x') f)
  :=
    \ H →
    ap
      ( nat-trans-components X A f f)
      ( nat-trans X A f f)
      ( \ x →
        ev-components-nat-trans X A f f
          ( comp-is-segal
            ( ( x' : X) → A x')
            ( is-segal-function-type funext X A is-segal-A)
            f g f α β)
          ( x))
      ( \ x → ev-components-nat-trans X A f f (id-hom ((x' : X) → A x') f) x)
      ( first
        ( has-inverse-is-equiv
          ( hom ((x' : X) → A x') f f)
          ( ( x : X) → hom (A x) (f x) (f x))
          ( ev-components-nat-trans X A f f)
          ( is-equiv-ev-components-nat-trans X A f f)))
      ( eq-htpy funext X
        ( \ x → (hom (A x) (f x) (f x)))
        ( \ x →
          ( ev-components-nat-trans X A f f
            ( comp-is-segal
              ( ( x' : X) → A x')
              ( is-segal-function-type funext X A is-segal-A)
              f g f α β)
            ( x)))
        ( \ x → (id-hom (A x) (f x)))
        ( \ x →
          ( triple-concat
            ( hom (A x) (f x) (f x))
            ( ev-components-nat-trans X A f f
              ( comp-is-segal
                ( ( x' : X) → A x')
                ( is-segal-function-type funext X A is-segal-A)
                f g f α β)
              ( x))
            ( comp-is-segal (A x) (is-segal-A x) (f x) (g x) (f x)
              ( ev-components-nat-trans X A f g α x)
              ( ev-components-nat-trans X A g f β x))
            ( id-hom (A x) (f x))
            ( ev-components-nat-trans X A f f (id-hom ((x' : X) → A x') f) x)
            ( rev
              ( hom (A x) (f x) (f x))
              ( comp-is-segal (A x) (is-segal-A x) (f x) (g x) (f x)
                ( ev-components-nat-trans X A f g α x)
                ( ev-components-nat-trans X A g f β x))
              ( ev-components-nat-trans X A f f
                ( comp-is-segal
                  ( ( x' : X) → A x')
                  ( is-segal-function-type funext X A is-segal-A)
                  f g f α β)
                ( x))
              ( comp-components-comp-nat-trans-is-segal
                funext X A is-segal-A f g f α β x))
            ( H x)
            ( rev
              ( hom (A x) (f x) (f x))
              ( ev-components-nat-trans X A f f (id-hom ((x' : X) → A x') f) x)
              ( id-hom (A x) (f x))
              ( id-arr-components-id-nat-trans X A f x)))))

#def nat-trans-nat-trans-components-preserves-iso uses (funext)
  ( X : U)
  ( A : X → U)
  ( is-segal-A : (x : X) → is-segal (A x))
  ( f g : (x : X) → A x)
  ( α : nat-trans X A f g)
  : ( ( x : X)
    → ( is-iso-arrow (A x) (is-segal-A x) (f x) (g x)
        ( ev-components-nat-trans X A f g α x)))
  → ( is-iso-arrow
      ( ( x' : X) → A x')
      ( is-segal-function-type funext X A is-segal-A) f g α)
  :=
    \ H →
    ( ( \ t x → (first (first (H x))) t
      , nat-trans-nat-trans-components-preserves-iso-helper X A is-segal-A f g
          ( α)
          ( \ t x → (first (first (H x))) t)
          ( \ x → (second (first (H x)))))
    , ( \ t x → (first (second (H x))) t
      , nat-trans-nat-trans-components-preserves-iso-helper X A is-segal-A g f
          ( \ t x → (first (second (H x))) t)
          ( α)
          ( \ x → (second (second (H x))))))

#def iff-is-iso-pointwise-is-iso uses (funext)
  ( X : U)
  ( A : X → U)
  ( is-segal-A : (x : X) → is-segal (A x))
  ( f g : (x : X) → A x)
  ( α : nat-trans X A f g)
  : iff
    ( is-iso-arrow
      ( ( x : X) → A x)
      ( is-segal-function-type funext X A is-segal-A) f g α)
    ( ( x : X)
      → ( is-iso-arrow
          ( A x)
          ( is-segal-A x)
          ( f x)
          ( g x)
          ( ev-components-nat-trans X A f g α x)))
  :=
    ( ev-components-nat-trans-preserves-iso X A is-segal-A f g α
    , nat-trans-nat-trans-components-preserves-iso X A is-segal-A f g α)

#def equiv-is-iso-pointwise-is-iso uses (extext funext weakfunext)
  ( X : U)
  ( A : X → U)
  ( is-segal-A : (x : X) → is-segal (A x))
  ( f g : (x : X) → A x)
  ( α : nat-trans X A f g)
  : Equiv
    ( is-iso-arrow
      ( ( x : X) → A x)
      ( is-segal-function-type funext X A is-segal-A) f g α)
    ( ( x : X)
      → ( is-iso-arrow
          ( A x)
          ( is-segal-A x)
          ( f x)
          ( g x)
          ( ev-components-nat-trans X A f g α x)))
  :=
    equiv-iff-is-prop-is-prop
      ( is-iso-arrow
        ( ( x : X) → A x)
        ( is-segal-function-type funext X A is-segal-A) f g α)
      ( ( x : X)
      → ( is-iso-arrow
          ( A x)
          ( is-segal-A x)
          ( f x)
          ( g x)
          ( ev-components-nat-trans X A f g α x)))
      ( is-prop-is-iso-arrow
        ( ( x : X) → A x)
        ( is-segal-function-type funext X A is-segal-A)
        ( f)
        ( g)
        ( α))
      ( is-prop-fiberwise-prop funext weakfunext
        ( X)
        ( \ x →
          ( is-iso-arrow
            ( A x)
            ( is-segal-A x)
            ( f x)
            ( g x)
            ( ev-components-nat-trans X A f g α x)))
        ( \ x →
          is-prop-is-iso-arrow
            ( A x)
            ( is-segal-A x)
            ( f x)
            ( g x)
            ( ev-components-nat-trans X A f g α x)))
      ( iff-is-iso-pointwise-is-iso X A is-segal-A f g α)
```

```rzk title="RS17, Corollary 10.4"
#def iso-extensionality uses (extext funext weakfunext)
  ( X : U)
  ( A : X → U)
  ( is-segal-A : (x : X) → is-segal (A x))
  ( f g : (x : X) → A x)
  : Equiv
      ( Iso ((x : X) → A x) (is-segal-function-type funext X A is-segal-A) f g)
      ( ( x : X) → Iso (A x) (is-segal-A x) (f x) (g x))
  :=
    equiv-triple-comp
      ( Iso ((x : X) → A x) (is-segal-function-type funext X A is-segal-A) f g)
      ( Σ ( α : nat-trans X A f g)
      , ( x : X)
      → ( is-iso-arrow (A x) (is-segal-A x) (f x) (g x)
          ( ev-components-nat-trans X A f g α x)))
      ( Σ ( α' : nat-trans-components X A f g)
      , ( x : X) → is-iso-arrow (A x) (is-segal-A x) (f x) (g x) (α' x))
      ( ( x : X) → Iso (A x) (is-segal-A x) (f x) (g x))
      ( total-equiv-family-of-equiv
        ( nat-trans X A f g)
        ( \ α →
          ( is-iso-arrow
            ( ( x : X) → A x)
            ( is-segal-function-type funext X A is-segal-A)
            f g α))
        ( \ α →
          ( x : X)
        → ( is-iso-arrow (A x) (is-segal-A x) (f x) (g x)
            ( ev-components-nat-trans X A f g α x)))
        ( \ α → equiv-is-iso-pointwise-is-iso X A is-segal-A f g α))
      ( equiv-total-pullback-is-equiv
        ( nat-trans X A f g)
        ( nat-trans-components X A f g)
        ( ev-components-nat-trans X A f g)
        ( is-equiv-ev-components-nat-trans X A f g)
        ( \ α' →
          ( x : X) → is-iso-arrow (A x) (is-segal-A x) (f x) (g x) (α' x)))
      ( inv-equiv
        ( ( x : X) → Iso (A x) (is-segal-A x) (f x) (g x))
        ( Σ ( α' : nat-trans-components X A f g)
        , ( x : X) → is-iso-arrow (A x) (is-segal-A x) (f x) (g x) (α' x))
        ( equiv-choice X
          ( \ x → hom (A x) (f x) (g x))
          ( \ x αₓ → is-iso-arrow (A x) (is-segal-A x) (f x) (g x) αₓ)))
```

## Rezk types

For every `x : A`, the identity arrow `id-hom A x : hom A x x` is an
isomorphism.

```rzk
#def is-iso-arrow-id-hom
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x : A)
  : is-iso-arrow A is-segal-A x x (id-hom A x)
  :=
    ( ( id-hom A x , comp-id-is-segal A is-segal-A x x (id-hom A x))
    , ( id-hom A x , comp-id-is-segal A is-segal-A x x (id-hom A x)))

#def iso-id-arrow
  ( A : U)
  ( is-segal-A : is-segal A)
  : ( x : A) → Iso A is-segal-A x x
  := \ x → (id-hom A x , is-iso-arrow-id-hom A is-segal-A x)
```

More generally, every path induces an isomorphism.

```rzk
#def is-iso-arrow-hom-eq
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  : ( p : x = y)
  → is-iso-arrow A is-segal-A x y (hom-eq A x y p)
  :=
    ind-path A x
    ( \ y' p' → is-iso-arrow A is-segal-A x y' (hom-eq A x y' p'))
    ( is-iso-arrow-id-hom A is-segal-A x)
    ( y)

#def iso-eq
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  : ( x = y) → Iso A is-segal-A x y
  := \ p → (hom-eq A x y p , is-iso-arrow-hom-eq A is-segal-A x y p)
```

A Segal type `A` is a Rezk type just when, for all `#!rzk x y : A`, this natural
map from `#!rzk x = y` to `#!rzk Iso A is-segal-A x y` is an equivalence.

```rzk title="RS17, Definition 10.6"
#def is-rezk
  ( A : U)
  : U
  :=
    Σ ( is-segal-A : is-segal A)
    , ( ( x : A)
      → ( y : A)
      → is-equiv (x = y) (Iso A is-segal-A x y) (iso-eq A is-segal-A x y))
```

The inverse to `#!rzk iso-eq` for a Rezk type.

```rzk
#def eq-iso-is-rezk
  ( A : U)
  ( is-rezk-A : is-rezk A)
  ( x y : A)
  : Iso A (first is-rezk-A) x y → x = y
  :=
    section-is-equiv (x = y) (Iso A (first is-rezk-A) x y)
    ( iso-eq A (first is-rezk-A) x y)
    ( ( second is-rezk-A) x y)

#def iso-eq-iso-is-rezk
  ( A : U)
  ( is-rezk-A : is-rezk A)
  ( x y : A)
  ( ( e , is-iso-e) : Iso A (first is-rezk-A) x y)
  : first (iso-eq A (first is-rezk-A) x y (eq-iso-is-rezk A is-rezk-A x y (e , is-iso-e))) = e
  :=
    first-path-Σ
    ( hom A x y)
    ( is-iso-arrow A (first is-rezk-A) x y)
    ( iso-eq A (first is-rezk-A) x y
      ( eq-iso-is-rezk A is-rezk-A x y (e , is-iso-e)))
    ( ( e , is-iso-e))
    ( ( second
      ( has-section-is-equiv (x = y) (Iso A (first is-rezk-A) x y)
        ( iso-eq A (first is-rezk-A) x y)
        ( ( second is-rezk-A) x y))) (e , is-iso-e))
```

The following results show how `#!rzk iso-eq` mediates between the
type-theoretic operations on paths and the category-theoretic operations on
arrows.

```rzk title="RS17, Lemma 10.7"
#def compute-covariant-transport-of-hom-family-iso-eq-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( C : A → U)
  ( is-covariant-C : is-covariant A C)
  ( x y : A)
  ( e : x = y)
  ( u : C x)
  : covariant-transport
      ( A)
      ( x)
      ( y)
      ( first (iso-eq A is-segal-A x y e))
      ( C)
      ( is-covariant-C)
      ( u)
    = transport A C x y e u
  :=
    ind-path
      ( A)
      ( x)
      ( \ y' e' →
        covariant-transport
          ( A)
          ( x)
          ( y')
          ( first (iso-eq A is-segal-A x y' e'))
          ( C)
          ( is-covariant-C)
          ( u)
        = transport A C x y' e' u)
      ( id-arr-covariant-transport A x C is-covariant-C u)
      ( y)
      ( e)
```

```rzk title="RS17, Lemma 10.8"
#def compute-ap-hom-of-iso-eq
  ( A B : U)
  ( is-segal-A : is-segal A)
  ( is-segal-B : is-segal B)
  ( f : A → B)
  ( x y : A)
  ( e : x = y)
  : ( ap-hom A B f x y (first (iso-eq A is-segal-A x y e)))
  = ( first (iso-eq B is-segal-B (f x) (f y) (ap A B x y f e)))
  :=
    ind-path
      ( A)
      ( x)
      ( \ y' e' →
        ( ap-hom A B f x y' (first (iso-eq A is-segal-A x y' e')))
      = ( first (iso-eq B is-segal-B (f x) (f y') (ap A B x y' f e'))))
      ( refl)
      ( y)
      ( e)
```

## Isomorphisms in discrete types

In a discrete type every arrow is an isomorphisms. This is a straightforward
path induction since every identity arrow is an isomorphism. Note that with
extension extensionality, `is-discrete A` implies `is-segal A` but we state the
first statement in a way that works without it.

```rzk
#def has-iso-arrows-is-segal-is-discrete
  ( A : U)
  ( is-discrete-A : is-discrete A)
  ( is-segal-A : is-segal A)
  ( x y : A)
  : ( f : hom A x y)
  → ( is-iso-arrow A is-segal-A x y f)
  :=
    ind-has-section-equiv (x =_{A} y) (hom A x y)
    ( hom-eq A x y , is-discrete-A x y)
    ( \ f → is-iso-arrow A is-segal-A x y f)
    ( ind-path A x
      ( \ y' p → is-iso-arrow A is-segal-A x y' (hom-eq A x y' p))
      ( is-iso-arrow-id-hom A is-segal-A x)
      ( y))

#def has-iso-arrows-is-discrete uses (extext)
  ( A : U)
  ( is-discrete-A : is-discrete A)
  ( x y : A)
  ( f : hom A x y)
  : ( is-iso-arrow A (is-segal-is-discrete extext A is-discrete-A)
      x y f)
  :=
    has-iso-arrows-is-segal-is-discrete A
    is-discrete-A
    ( is-segal-is-discrete extext A is-discrete-A)
    ( x) (y) (f)

#def is-equiv-hom-iso-is-discrete uses (extext)
  ( A : U)
  ( is-discrete-A : is-discrete A)
  ( x y : A)
  : is-equiv
    ( Iso A (is-segal-is-discrete extext A is-discrete-A)
      x y)
    ( hom A x y)
    ( \ (f , _) → f)
  :=
    is-equiv-projection-contractible-fibers
    ( hom A x y) (is-iso-arrow A (is-segal-is-discrete extext A is-discrete-A) x y)
    ( \ f →
      is-contr-is-inhabited-is-prop
      ( is-iso-arrow A (is-segal-is-discrete extext A is-discrete-A) x y f)
      ( is-prop-is-iso-arrow A
        ( is-segal-is-discrete extext A is-discrete-A)
        ( x) (y) (f))
      ( has-iso-arrows-is-discrete A is-discrete-A x y f))
```

### Discrete types are Rezk

As a corollary we obtain that every discrete type is Rezk.

```rzk
#def is-rezk-is-discrete uses (extext)
  ( A : U)
  : is-discrete A → is-rezk A
  :=
  \ is-discrete-A →
  ( is-segal-is-discrete extext A is-discrete-A
  , ( \ x y →
      is-equiv-right-factor
      ( x = y)
      ( Iso A (is-segal-is-discrete extext A is-discrete-A)
        x y)
      ( hom A x y)
      ( iso-eq A (is-segal-is-discrete extext A is-discrete-A)
        x y)
      ( \ (f , _) → f)
      ( is-equiv-hom-iso-is-discrete A is-discrete-A x y)
      ( is-discrete-A x y)))
```

In particular, every contractible type is Rezk

```rzk
#def is-rezk-is-contr uses (extext)
  ( A : U)
  : is-contr A → is-rezk A
  :=
  \ is-contr-A →
    ( is-rezk-is-discrete A
      ( is-discrete-is-contr extext A is-contr-A))

#def is-rezk-Unit uses (extext)
  : is-rezk Unit
  := is-rezk-is-contr Unit (is-contr-Unit)
```

## Representable isomorphisms.

We prove [RS17, Proposition 10.11]. We first need to access the fiberwise
equivalence with no extra data, and then define some helpers.

```rzk
#section representable-isomorphisms

#variable A : U
#variable is-segal-A : is-segal A
#variables a a' : A
#variable ψ : (x : A) → (Equiv (hom A a x) (hom A a' x))

#def map-representable-equiv
  : ( x : A) → (hom A a x) → (hom A a' x)
  := \ x → first (ψ x)

#def inverse-representable-equiv
  : ( x : A) → (has-inverse (hom A a x) (hom A a' x) (first (ψ x)))
  :=
  \ x →
  has-inverse-is-equiv
    ( hom A a x)
    ( hom A a' x)
    ( first (ψ x))
    ( second (ψ x))

#def inv-map-representable-equiv uses (A a a' ψ)
  : ( x : A) → (hom A a' x) → (hom A a x)
  := \ x → first (inverse-representable-equiv x)

#def arr-map-representable-equiv
  : hom A a' a
  := evid A a (hom A a') (map-representable-equiv)

#def arr-inv-map-representable-equiv
  : hom A a a'
  := evid A a' (hom A a) (inv-map-representable-equiv)
```

We now show that `#!rzk arrow-map-representable-equiv` has section
`#!rzk arrow-inv-map-representable-equiv`.

```rzk
#def htpy-inv-map-fib-equiv-map-fib-equiv-id uses (A a a' ψ)
  : ( x : A)
  → ( homotopy
      ( hom A a x)
      ( hom A a x)
      ( comp
        ( hom A a x)
        ( hom A a' x)
        ( hom A a x)
        ( inv-map-representable-equiv x)
        ( map-representable-equiv x))
      ( identity (hom A a x)))
  := \ x → first (second (inverse-representable-equiv x))
```

We compute the required paths for the section of
`#!rzk arrow-map-representable-equiv`.

```rzk
#def rev-comp-id-comp-arr-inv-map-arr-map-id-a uses (A is-segal-A a a' ψ)
  : comp-is-segal A is-segal-A a a' a
      arr-inv-map-representable-equiv
      arr-map-representable-equiv
  =_{ hom A a a}
    comp-is-segal A is-segal-A a a a
      ( comp-is-segal A is-segal-A a a' a
          arr-inv-map-representable-equiv
          arr-map-representable-equiv)
      ( id-hom A a)
  :=
  rev
    ( hom A a a)
    ( comp-is-segal A is-segal-A a a a
      ( comp-is-segal A is-segal-A a a' a
          arr-inv-map-representable-equiv
          arr-map-representable-equiv)
      ( id-hom A a))
    ( comp-is-segal A is-segal-A a a' a
        arr-inv-map-representable-equiv
        arr-map-representable-equiv)
    ( comp-id-is-segal A is-segal-A a a
      ( comp-is-segal A is-segal-A a a' a
          arr-inv-map-representable-equiv
          arr-map-representable-equiv))

#def assoc-is-segal-comp-comp-arr-inv-equiv-arr-map-idhom-a
  uses (A is-segal-A a a' ψ)
  : comp-is-segal A is-segal-A a a a
      ( comp-is-segal A is-segal-A a a' a
         arr-inv-map-representable-equiv
         arr-map-representable-equiv)
      ( id-hom A a)
  =_{ hom A a a}
    comp-is-segal A is-segal-A a a' a
      ( arr-inv-map-representable-equiv)
      ( comp-is-segal A is-segal-A a' a a
        ( arr-map-representable-equiv)
        ( id-hom A a))
  :=
  associative-is-segal extext A is-segal-A a a' a a
  ( arr-inv-map-representable-equiv)
  ( arr-map-representable-equiv)
  ( id-hom A a)

#def rev-eq-compute-precomposition-evid-arr-inv-map-representable-equiv
  uses (A is-segal-A a a' ψ)
  : comp-is-segal A is-segal-A a a' a
      ( arr-inv-map-representable-equiv)
      ( comp-is-segal A is-segal-A a' a a
        ( arr-map-representable-equiv)
        ( id-hom A a))
  =_{ hom A a a}
    inv-map-representable-equiv a
    ( comp-is-segal A is-segal-A a' a a
      ( arr-map-representable-equiv)
      ( id-hom A a))
  :=
  rev
  ( hom A a a)
  ( inv-map-representable-equiv a
    ( comp-is-segal A is-segal-A a' a a arr-map-representable-equiv (id-hom A a)))
  ( comp-is-segal A is-segal-A a a' a
    ( arr-inv-map-representable-equiv)
    ( comp-is-segal A is-segal-A a' a a arr-map-representable-equiv (id-hom A a)))
  ( eq-compute-precomposition-evid funext A is-segal-A a' a
    ( inv-map-representable-equiv)
    ( a)
    ( comp-is-segal A is-segal-A a' a a
      ( arr-map-representable-equiv)
      ( id-hom A a)))

#def rev-ap-inv-map-representable-equiv uses (A is-segal-A a a' ψ)
  : inv-map-representable-equiv a
    ( comp-is-segal A is-segal-A a' a a
      ( arr-map-representable-equiv)
      ( id-hom A a))
  =_{ hom A a a}
    inv-map-representable-equiv a (map-representable-equiv a (id-hom A a))
  :=
  ap
  ( hom A a' a)
  ( hom A a a)
  ( comp-is-segal A is-segal-A a' a a
        ( arr-map-representable-equiv)
        ( id-hom A a))
  ( map-representable-equiv a (id-hom A a))
  ( inv-map-representable-equiv a)
  ( rev (hom A a' a)
    ( map-representable-equiv a (id-hom A a))
    ( comp-is-segal A is-segal-A a' a a
        ( arr-map-representable-equiv)
        ( id-hom A a))
    ( eq-compute-precomposition-evid funext A is-segal-A a a'
        ( map-representable-equiv)
        ( a)
        ( id-hom A a)))

#def compute-htpy-inv-map-fib-equiv-map-fib-equiv-id
  : inv-map-representable-equiv a (map-representable-equiv a (id-hom A a))
  =_{ hom A a a}
    id-hom A a
  := htpy-inv-map-fib-equiv-map-fib-equiv-id a (id-hom A a)
```

Concatenate all the paths above.

```rzk
#def eq-comp-arrow-inv-map-arrow-map-equiv-id-a
  uses (extext funext A is-segal-A a a' ψ)
  : comp-is-segal A is-segal-A a a' a
      arr-inv-map-representable-equiv
      arr-map-representable-equiv
  =_{ hom A a a}
    id-hom A a
  :=
  quintuple-concat
  ( hom A a a)
  ( comp-is-segal A is-segal-A a a' a
      arr-inv-map-representable-equiv
      arr-map-representable-equiv)
  ( comp-is-segal A is-segal-A a a a
    ( comp-is-segal A is-segal-A a a' a
        arr-inv-map-representable-equiv
        arr-map-representable-equiv)
    ( id-hom A a))
  ( comp-is-segal A is-segal-A a a' a
    ( arr-inv-map-representable-equiv)
    ( comp-is-segal A is-segal-A a' a a arr-map-representable-equiv (id-hom A a)))
  ( inv-map-representable-equiv a
    ( comp-is-segal A is-segal-A a' a a arr-map-representable-equiv (id-hom A a)))
  ( inv-map-representable-equiv a (map-representable-equiv a (id-hom A a)))
  ( id-hom A a)
  ( rev-comp-id-comp-arr-inv-map-arr-map-id-a)
  ( assoc-is-segal-comp-comp-arr-inv-equiv-arr-map-idhom-a)
  ( rev-eq-compute-precomposition-evid-arr-inv-map-representable-equiv)
  ( rev-ap-inv-map-representable-equiv)
  ( compute-htpy-inv-map-fib-equiv-map-fib-equiv-id)
```

Now we give the section of `#!rzk arrow-map-representable-equiv`.

```rzk
#def section-arrow-map-representable-equiv uses (extext funext A is-segal-A a a' ψ)
  : Section-arrow A is-segal-A a' a arr-map-representable-equiv
  :=
  ( arr-inv-map-representable-equiv , eq-comp-arrow-inv-map-arrow-map-equiv-id-a)
```

We see that `#!rzk arrow-map-representable-equiv` has retraction
`#!rzk arrow-inv-map-representable-equiv`.

```rzk
#def htpy-comp-map-fib-equiv-inv-map-fib-equiv uses (A a a' ψ)
  : ( x : A)
  → ( homotopy
      ( hom A a' x)
      ( hom A a' x)
      ( comp
        ( hom A a' x)
        ( hom A a x)
        ( hom A a' x)
        ( map-representable-equiv x)
        ( inv-map-representable-equiv x))
      ( identity (hom A a' x)))
  := \ x → second (second (inverse-representable-equiv x))
```

We compute the required paths for the retraction of
`#!rzk arrow-map-iso-representable`.

```rzk
#def rev-eq-compute-precomposition-evid-map-representable-equiv
  uses (A is-segal-A a a' ψ)
  : comp-is-segal A is-segal-A a' a a'
      arr-map-representable-equiv
      arr-inv-map-representable-equiv
  =_{ hom A a' a'}
    map-representable-equiv a' arr-inv-map-representable-equiv
  :=
  rev
  ( hom A a' a')
  ( map-representable-equiv a' arr-inv-map-representable-equiv)
  ( comp-is-segal A is-segal-A a' a a'
      arr-map-representable-equiv
      arr-inv-map-representable-equiv)
  ( eq-compute-precomposition-evid funext A is-segal-A a a'
      map-representable-equiv
      a'
      arr-inv-map-representable-equiv)

#def rev-ap-map-representable-equiv-eq-arr-inv-map-id-a'-arr-inv-map
  uses (A is-segal-A a a' ψ)
  : map-representable-equiv a' arr-inv-map-representable-equiv
  =_{ hom A a' a'}
    map-representable-equiv a'
    ( comp-is-segal A is-segal-A a a' a'
      ( arr-inv-map-representable-equiv)
      ( id-hom A a'))
  :=
  ap
  ( hom A a a')
  ( hom A a' a')
  ( arr-inv-map-representable-equiv)
  ( comp-is-segal A is-segal-A a a' a'
    ( arr-inv-map-representable-equiv)
    ( id-hom A a'))
  ( map-representable-equiv a')
  ( rev
    ( hom A a a')
    ( comp-is-segal A is-segal-A a a' a'
      ( arr-inv-map-representable-equiv)
      ( id-hom A a'))
    ( arr-inv-map-representable-equiv)
    ( comp-id-is-segal A is-segal-A a a' arr-inv-map-representable-equiv))

#def rev-ap-map-representable-equiv uses (A is-segal-A a a' ψ)
  : map-representable-equiv a'
    ( comp-is-segal A is-segal-A a a' a'
      ( arr-inv-map-representable-equiv)
      ( id-hom A a'))
  =_{ hom A a' a'}
    map-representable-equiv a' (inv-map-representable-equiv a' (id-hom A a'))
  :=
  ap
  ( hom A a a')
  ( hom A a' a')
  ( comp-is-segal A is-segal-A a a' a'
    ( arr-inv-map-representable-equiv)
    ( id-hom A a'))
  ( inv-map-representable-equiv a' (id-hom A a'))
  ( map-representable-equiv a')
  ( rev
    ( hom A a a')
    ( inv-map-representable-equiv a' (id-hom A a'))
    ( comp-is-segal A is-segal-A a a' a'
      ( arr-inv-map-representable-equiv)
      ( id-hom A a'))
    ( eq-compute-precomposition-evid funext A is-segal-A a' a
      ( inv-map-representable-equiv)
      ( a')
      ( id-hom A a')))

#def compute-htpy-comp-map-fib-equiv-inv-map-fib-equiv uses (A a a' ψ)
  : map-representable-equiv a' (inv-map-representable-equiv a' (id-hom A a'))
  =_{ hom A a' a'}
    id-hom A a'
  := htpy-comp-map-fib-equiv-inv-map-fib-equiv a' (id-hom A a')
```

Concatenate all the paths above.

```rzk
#def eq-comp-arr-map-representable-arr-inv-map-representable-id-a'
  uses (funext A is-segal-A a a' ψ)
  : comp-is-segal A is-segal-A a' a a'
      arr-map-representable-equiv
      arr-inv-map-representable-equiv
  =_{ hom A a' a'}
    id-hom A a'
  :=
  quadruple-concat
  ( hom A a' a')
  ( comp-is-segal A is-segal-A a' a a'
      arr-map-representable-equiv
      arr-inv-map-representable-equiv)
  ( map-representable-equiv a' arr-inv-map-representable-equiv)
  ( map-representable-equiv a'
    ( comp-is-segal A is-segal-A a a' a'
      ( arr-inv-map-representable-equiv)
      ( id-hom A a')))
  ( map-representable-equiv a' (inv-map-representable-equiv a' (id-hom A a')))
  ( id-hom A a')
  ( rev-eq-compute-precomposition-evid-map-representable-equiv)
  ( rev-ap-map-representable-equiv-eq-arr-inv-map-id-a'-arr-inv-map)
  ( rev-ap-map-representable-equiv)
  ( compute-htpy-comp-map-fib-equiv-inv-map-fib-equiv)
```

Now we give the retraction of `#!rzk arrow-map-representable-equiv`.

```rzk
#def retraction-arrow-map-representable-equiv uses (funext A is-segal-A a a' ψ)
  : Retraction-arrow A is-segal-A a' a arr-map-representable-equiv
  :=
  ( arr-inv-map-representable-equiv
  , eq-comp-arr-map-representable-arr-inv-map-representable-id-a')
```

We show that arrows from representable equivalences are isomorphisms, i.e. that
`#!rzk arr-map-representable-equiv` is an isomorphism.

```rzk title="RS17, Proposition 10.11 (i)"
#def representable-isomorphism uses (extext funext A is-segal-A a a' ψ)
  : is-iso-arrow A is-segal-A a' a arr-map-representable-equiv
  :=
  ( retraction-arrow-map-representable-equiv
  , section-arrow-map-representable-equiv)

#end representable-isomorphisms
```

The second part of Proposition 10.11.

```rzk title="RS17, Proposition 10.11 (ii)"
#def eq-representable-isomorphism uses (extext funext)
  ( A : U)
  ( is-rezk-A : is-rezk A)
  ( a a' : A)
  ( ψ : (x : A) → (Equiv (hom A a x) (hom A a' x)))
  : a' = a
  :=
  eq-iso-is-rezk A is-rezk-A a' a
  ( arr-map-representable-equiv A a a' ψ
  , representable-isomorphism A (first is-rezk-A) a a' ψ)
```
