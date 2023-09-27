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
  := ( comp-is-segal A is-segal-A x y x f g) =_{hom A x x} (id-hom A x)

#def Retraction-arrow
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  ( f : hom A x y)
  : U
  := Σ ( g : hom A y x) , ( has-retraction-arrow A is-segal-A x y f g)

#def has-section-arrow
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  ( f : hom A x y)
  ( h : hom A y x)
  : U
  := ( comp-is-segal A is-segal-A y x y h f) =_{hom A y y} (id-hom A y)

#def Section-arrow
  (A : U)
  (is-segal-A : is-segal A)
  (x y : A)
  (f : hom A x y)
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
  := Σ ( f : hom A x y) , is-iso-arrow A is-segal-A x y f
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
    Σ ( g : hom A y x) ,
      product
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
  : (is-iso-arrow A is-segal-A x y f) → (has-inverse-arrow A is-segal-A x y f)
  :=
    ( \ ((g , p) , (h , q)) →
      ( g ,
        ( p ,
          ( concat
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
                  ( comp-is-segal A is-segal-A y x y h f) ( g))
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
    ( is-iso-arrow-has-inverse-arrow A is-segal-A x y f ,
      has-inverse-arrow-is-iso-arrow A is-segal-A x y f)
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
  : ( z : A) →
    has-retraction (hom A z x) (hom A z y)
      ( postcomp-is-segal A is-segal-A x y f z)
  :=
    \ z →
    ( ( postcomp-is-segal A is-segal-A y x g z) ,
        \ k →
      ( triple-concat
        ( hom A z x)
        ( comp-is-segal A is-segal-A z y x
          ( comp-is-segal A is-segal-A z x y k f) g)
        ( comp-is-segal A is-segal-A z x x
          k ( comp-is-segal A is-segal-A x y x f g))
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
  : ( z : A) →
    has-section (hom A z x) (hom A z y) (postcomp-is-segal A is-segal-A x y f z)
  :=
    \ z →
    ( ( postcomp-is-segal A is-segal-A y x h z) ,
        \ k →
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
  : (z : A) →
    is-equiv (hom A z x) (hom A z y) (postcomp-is-segal A is-segal-A x y f z)
  :=
    \ z →
    ( ( has-retraction-postcomp-has-retraction A is-segal-A x y f g gg z) ,
      ( has-section-postcomp-has-section A is-segal-A x y f h hh z))

#def has-retraction-precomp-has-section uses (extext)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  ( f : hom A x y)
  ( h : hom A y x)
  ( hh : has-section-arrow A is-segal-A x y f h)
  : (z : A) →
    has-retraction (hom A y z) (hom A x z)
      ( precomp-is-segal A is-segal-A x y f z)
  :=
    \ z →
    ( ( precomp-is-segal A is-segal-A y x h z) ,
        \ k →
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
  : (z : A) →
    has-section (hom A y z) (hom A x z) (precomp-is-segal A is-segal-A x y f z)
  :=
    \ z →
    ( ( precomp-is-segal A is-segal-A y x g z) ,
        \ k →
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
  : (z : A) →
    is-equiv (hom A y z) (hom A x z) (precomp-is-segal A is-segal-A x y f z)
  :=
    \ z →
      ( ( has-retraction-precomp-has-section A is-segal-A x y f h hh z) ,
        ( has-section-precomp-has-retraction A is-segal-A x y f g gg z))

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
  : (is-prop (is-iso-arrow A is-segal-A x y f))
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
      ( (x : X) → A x)
      ( is-segal-function-type funext X A is-segal-A) f g α) →
    ( x : X) →
    ( is-iso-arrow (A x) (is-segal-A x) (f x) (g x)
      ( ev-components-nat-trans X A f g α x))
  :=
    \ ((β , p) , (γ , q)) →
    \ x →
    ( ( ( ev-components-nat-trans X A g f β x) ,
        ( triple-concat
          (hom (A x) (f x) (f x))
          ( comp-is-segal (A x) (is-segal-A x) (f x) (g x) (f x)
            ( ev-components-nat-trans X A f g α x)
            ( ev-components-nat-trans X A g f β x))
          ( ev-components-nat-trans X A f f
            ( comp-is-segal
              ( (x' : X) → (A x'))
              ( is-segal-function-type funext X A is-segal-A) f g f α β)
            ( x))
          ( ev-components-nat-trans X A f f (id-hom ((x' : X) → (A x')) f) x)
          ( id-hom (A x) (f x))
          ( comp-components-comp-nat-trans-is-segal
            funext X A is-segal-A f g f α β x)
          ( ap
            ( hom ((x' : X) → (A x')) f f)
            ( hom (A x) (f x) (f x))
            ( comp-is-segal
              ( (x' : X) → (A x'))
              ( is-segal-function-type funext X A is-segal-A) f g f α β)
            ( id-hom ((x' : X) → (A x')) f)
            (\ α' → ev-components-nat-trans X A f f α' x)
            ( p))
          ( id-arr-components-id-nat-trans X A f x))) ,
      ( ( ev-components-nat-trans X A g f γ x) ,
        ( triple-concat
          (hom (A x) (g x) (g x))
          ( comp-is-segal (A x) (is-segal-A x) (g x) (f x) (g x)
            ( ev-components-nat-trans X A g f γ x)
            ( ev-components-nat-trans X A f g α x))
          ( ev-components-nat-trans X A g g
            ( comp-is-segal
              ( (x' : X) → (A x'))
              ( is-segal-function-type funext X A is-segal-A) g f g γ α)
            ( x))
          ( ev-components-nat-trans X A g g (id-hom ((x' : X) → (A x')) g) x)
          ( id-hom (A x) (g x))
          ( comp-components-comp-nat-trans-is-segal
            funext X A is-segal-A g f g γ α x)
          ( ap
            ( hom ((x' : X) → (A x')) g g)
            ( hom (A x) (g x) (g x))
            ( comp-is-segal
              ( (x' : X) → (A x'))
              ( is-segal-function-type funext X A is-segal-A) g f g γ α)
            ( id-hom ((x' : X) → (A x')) g)
            ( \ α' → ev-components-nat-trans X A g g α' x)
            ( q))
          ( id-arr-components-id-nat-trans X A g x))))

#def nat-trans-nat-trans-components-preserves-iso uses (funext)
  ( X : U)
  ( A : X → U)
  ( is-segal-A : (x : X) → is-segal (A x))
  ( f g : (x : X) → A x)
  ( α : nat-trans X A f g)
  : ( ( x : X) →
      ( is-iso-arrow (A x) (is-segal-A x) (f x) (g x)
        ( ev-components-nat-trans X A f g α x))) →
    ( is-iso-arrow
      ( (x' : X) → A x')
      ( is-segal-function-type funext X A is-segal-A) f g α)
  :=
    \ H →
    ( ( \ t x → (first (first (H x))) t ,
        ( ap
          ( (x : X) → hom (A x) (f x) (f x))
          ( hom ((x' : X) → (A x')) f f)
          ( \ x → ev-components-nat-trans X A f f
              ( comp-is-segal
                ( (x' : X) → (A x'))
                ( is-segal-function-type funext X A is-segal-A) f g f α (\ t x' → (first (first (H x'))) t))
              ( x))
          ( \ x → ev-components-nat-trans X A f f (id-hom ((x' : X) → (A x')) f) x)
          ( first
            ( has-inverse-is-equiv
              ( hom ((x' : X) → (A x')) f f)
              ( (x : X) → hom (A x) (f x) (f x))
              ( ev-components-nat-trans X A f f)
              ( is-equiv-ev-components-nat-trans X A f f)))
          ( eq-htpy funext X
            ( \ x → (hom (A x) (f x) (f x)))
            ( \ x →
              ( ev-components-nat-trans X A f f
                ( comp-is-segal
                  ( (x' : X) → A x')
                  ( is-segal-function-type funext X A is-segal-A)
                  f g f α (\ t x' → (first (first (H x'))) t))
                ( x)))
            ( \ x → ( id-hom (A x) (f x)))
            ( \ x →
              ( triple-concat
                ( hom (A x) (f x) (f x))
                ( ev-components-nat-trans X A f f
                  ( comp-is-segal
                    ( (x' : X) → (A x'))
                    ( is-segal-function-type funext X A is-segal-A) f g f α (\ t x' → (first (first (H x'))) t))
                  ( x))
                ( comp-is-segal (A x) (is-segal-A x) (f x) (g x) (f x)
                  ( ev-components-nat-trans X A f g α x)
                  ( ev-components-nat-trans X A g f (\ t x' → (first (first (H x'))) t) x))
                ( id-hom (A x) (f x))
                ( ev-components-nat-trans X A f f (id-hom ((x' : X) → (A x')) f) x)
                ( rev
                  (hom (A x) (f x) (f x))
                  ( comp-is-segal (A x) (is-segal-A x) (f x) (g x) (f x)
                    ( ev-components-nat-trans X A f g α x)
                    ( ev-components-nat-trans X A g f (\ t x' → (first (first (H x'))) t) x))
                  ( ev-components-nat-trans X A f f
                    ( comp-is-segal
                      ( (x' : X) → (A x'))
                      ( is-segal-function-type funext X A is-segal-A) f g f α (\ t x' → (first (first (H x'))) t))
                    ( x))
                  ( comp-components-comp-nat-trans-is-segal
                    funext X A is-segal-A f g f α (\ t x' → (first (first (H x'))) t) x))
                ( second (first (H x)))
                ( rev
                  ( hom (A x) (f x) (f x))
                  ( ev-components-nat-trans X A f f (id-hom ((x' : X) → (A x')) f) x)
                  ( id-hom (A x) (f x))
                  ( id-arr-components-id-nat-trans X A f x))))))) ,
        ( \ t x → (first (second (H x))) t ,
          ( ap
          ( (x : X) → hom (A x) (g x) (g x))
          ( hom ((x' : X) → (A x')) g g)
          ( \ x → ev-components-nat-trans X A g g
              ( comp-is-segal
                ( (x' : X) → (A x'))
                ( is-segal-function-type funext X A is-segal-A) g f g (\ t x' → (first (second (H x'))) t) α)
              ( x))
          ( \ x → ev-components-nat-trans X A g g (id-hom ((x' : X) → (A x')) g) x)
          ( first
            ( has-inverse-is-equiv
              ( hom ((x' : X) → (A x')) g g)
              ( (x : X) → hom (A x) (g x) (g x))
              ( ev-components-nat-trans X A g g)
              ( is-equiv-ev-components-nat-trans X A g g)))
          ( eq-htpy funext X
            ( \ x → (hom (A x) (g x) (g x)))
            ( \ x →
              ( ev-components-nat-trans X A g g
                ( comp-is-segal
                  ( (x' : X) → A x')
                  ( is-segal-function-type funext X A is-segal-A)
                  g f g (\ t x' → (first (second (H x'))) t) α)
                ( x)))
            ( \ x → ( id-hom (A x) (g x)))
            ( \ x →
              ( triple-concat
                ( hom (A x) (g x) (g x))
                ( ev-components-nat-trans X A g g
                  ( comp-is-segal
                    ( (x' : X) → (A x'))
                    ( is-segal-function-type funext X A is-segal-A) g f g (\ t x' → (first (second (H x'))) t) α)
                  ( x))
                ( comp-is-segal (A x) (is-segal-A x) (g x) (f x) (g x)
                  ( ev-components-nat-trans X A g f (\ t x' → (first (second (H x'))) t) x)
                  ( ev-components-nat-trans X A f g α x))
                ( id-hom (A x) (g x))
                ( ev-components-nat-trans X A g g (id-hom ((x' : X) → (A x')) g) x)
                ( rev
                  (hom (A x) (g x) (g x))
                  ( comp-is-segal (A x) (is-segal-A x) (g x) (f x) (g x)
                    ( ev-components-nat-trans X A g f (\ t x' → (first (second (H x'))) t) x)
                    ( ev-components-nat-trans X A f g α x))
                  ( ev-components-nat-trans X A g g
                    ( comp-is-segal
                      ( (x' : X) → (A x'))
                      ( is-segal-function-type funext X A is-segal-A) g f g (\ t x' → (first (second (H x'))) t) α)
                    ( x))
                  ( comp-components-comp-nat-trans-is-segal
                    funext X A is-segal-A g f g (\ t x' → (first (second (H x'))) t) α x))
                ( second (second (H x)))
                ( rev
                  ( hom (A x) (g x) (g x))
                  ( ev-components-nat-trans X A g g (id-hom ((x' : X) → (A x')) g) x)
                  ( id-hom (A x) (g x))
                  ( id-arr-components-id-nat-trans X A g x))))))))


#def TODO uses (funext extext weakfunext)
  ( X : U)
  ( A : X → U)
  ( is-segal-A : (x : X) → is-segal (A x))
  ( f g : (x : X) → A x)
  ( α : nat-trans X A f g)
  : is-equiv
      ( is-iso-arrow ((x : X) → A x) (is-segal-function-type funext X A is-segal-A) f g α)
      ( ( x : X) →
        ( is-iso-arrow
          ( A x)
          ( is-segal-A x)
          ( f x)
          ( g x)
          ( ev-components-nat-trans X A f g α x)))
      ( ev-components-nat-trans-preserves-iso X A is-segal-A f g α)
  :=
    bijective-props-are-equiv
      ( is-iso-arrow ((x : X) → A x) (is-segal-function-type funext X A is-segal-A) f g α)
      ( ( x : X) →
        ( is-iso-arrow
          ( A x)
          ( is-segal-A x)
          ( f x)
          ( g x)
          ( ev-components-nat-trans X A f g α x)))
      ( is-prop-is-iso-arrow
        ( (x : X) → A x)
        ( is-segal-function-type funext X A is-segal-A)
        ( f)
        ( g)
        ( α))
      ( fiberwise-prop-is-prop funext weakfunext
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
      ( ev-components-nat-trans-preserves-iso X A is-segal-A f g α)
      ( nat-trans-nat-trans-components-preserves-iso X A is-segal-A f g α)
```

## Rezk types

A Segal type $A$ is a Rezk type just when, for all `#!rzk x y : A`, the natural
map from `#!rzk x = y` to `#!rzk Iso A is-segal-A x y` is an equivalence.

```rzk
#def iso-id-arrow
  (A : U)
  (is-segal-A : is-segal A)
  : (x : A) → Iso A is-segal-A x x
  :=
    \ x →
    (
    (id-hom A x) ,
    (
    (
      (id-hom A x) ,
      (id-comp-is-segal A is-segal-A x x (id-hom A x))
    ) ,
    (
      (id-hom A x) ,
      (id-comp-is-segal A is-segal-A x x (id-hom A x))
    )
      )
  )

#def iso-eq
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  : (x = y) → Iso A is-segal-A x y
  :=
    \ p →
    ind-path
      ( A)
      ( x)
      ( \ y' p' → Iso A is-segal-A x y')
      ( iso-id-arrow A is-segal-A x)
      ( y)
      ( p)
```

```rzk title="RS17, Definition 10.6"
#def is-rezk
  ( A : U)
  : U
  :=
    Σ ( is-segal-A : is-segal A) ,
      (x : A) → (y : A) →
        is-equiv (x = y) (Iso A is-segal-A x y) (iso-eq A is-segal-A x y)
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
  : ( ap-hom A B f x y (first (iso-eq A is-segal-A x y e))) =
    ( first ( iso-eq B is-segal-B (f x) (f y) (ap A B x y f e)))
  :=
    ind-path
      ( A)
      ( x)
      ( \ y' e' →
        ( ap-hom A B f x y' (first (iso-eq A is-segal-A x y' e'))) =
        ( first (iso-eq B is-segal-B (f x) (f y') (ap A B x y' f e'))))
      ( refl)
      ( y)
      ( e)
```
