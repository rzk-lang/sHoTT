# Cocartesian Fibrations

These formalizations capture cocartesian families as treated in
[Buchholtz and Weinberger (2023), Higher Structures 7](https://doi.org/10.21136/HS.2023.04)
and [Weinberger (2024), Arxiv](https://arxiv.org/abs/2403.08190).

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Prerequisites

- `hott/*` - We require various prerequisites from homotopy type theory, for
  instance the axiom of function extensionality.
- `03-simplicial-type-theory.rzk.md` — We rely on definitions of simplicies and
  their subshapes.
- `04-extension-types.rzk.md` — We use extension extensionality.
- `12-orthogonal-families.rzk.md` - We make use of inner families.
- `20-lari-families.rzk.md` - We make use of LARI families.

```rzk
#assume funext : FunExt
#assume extext : ExtExt
```

## Naive Cocartesian Families

First we will define cocartesian families in the obvious way. Showing their
closure properties using this definition is very elaborate, which is why we
instead show an equivalence to $i_0$-LARI families for which we already
established the desired closure properties.

### Cocartesian arrows

Here we define the proposition that a dependent arrow in a family is
cocartesian. This is an alternative version using unpacked extension types, as
this is preferred for usage.

```rzk title="BW23, Definition 5.1.1"
#def is-cocartesian-arrow
  ( B : U)
  ( b b' : B)
  ( u : hom B b b')
  ( P : B → U)
  ( e : P b)
  ( e' : P b')
  ( f : dhom B b b' u P e e')
  : U
  :=
    ( b'' : B) → (v : hom B b' b'') → (w : hom B b b'')
    → ( sigma : hom2 B b b' b'' u v w) → (e'' : P b'')
    → ( h : dhom B b b'' w P e e'')
    → is-contr
        ( Σ ( g : dhom B b' b'' v P e' e'')
        , ( dhom2 B b b' b'' u v w sigma P e e' e'' f g h))
```

Since this definition only uses function types and as the final codomain a
proposition, the entire definition also is a proposition, which we will need
later.

```rzk
#def is-prop-is-cocartesian-arrow
  ( B : U)
  ( b b' : B)
  ( u : hom B b b')
  ( P : B → U)
  ( e : P b)
  ( e' : P b')
  ( f : dhom B b b' u P e e')
  : is-prop (is-cocartesian-arrow B b b' u P e e' f)
  :=
  is-prop-fiberwise-prop6 funext
  ( B)
  ( \ b'' → hom B b' b'')
  ( \ b'' v → hom B b b'')
  ( \ b'' v w → hom2 B b b' b'' u v w)
  ( \ b'' v w sigma → P b'')
  ( \ b'' v w sigma e'' → dhom B b b'' w P e e'')
  ( \ b'' v w sigma e'' h →
    is-contr
    ( Σ ( g : dhom B b' b'' v P e' e'')
      , ( dhom2 B b b' b'' u v w sigma P e e' e'' f g h)))
  ( \ b'' v w sigma e'' h →
    is-prop-is-contr-itself (weakfunext-funext funext)
    ( Σ ( g : dhom B b' b'' v P e' e'')
    , ( dhom2 B b b' b'' u v w sigma P e e' e'' f g h)))
```

### Cocartesian lifts

The following is the type of cocartesian lifts of a fixed arrow in the base with
a given starting point in the fiber.

```rzk title="BW23, Definition 5.1.2"
#def cocartesian-lift
  ( B : U)
  ( b b' : B)
  ( u : hom B b b')
  ( P : B → U)
  ( e : P b)
  : U
  :=
    Σ ( e' : P b')
    , Σ ( f : dhom B b b' u P e e') , is-cocartesian-arrow B b b' u P e e' f
```

### Cocartesian family

A family is cocartesian if it is isoinner and any arrow in the has a cocartesian
lift, given a point in the fiber over the domain.

```rzk title="BW23, Definition 5.2.1"
#def has-cocartesian-lifts
  ( B : U)
  ( P : B → U)
  : U
  :=
    ( b : B) → (b' : B) → (u : hom B b b')
    → ( e : P b) → (Σ (e' : P b')
      , ( Σ ( f : dhom B b b' u P e e') , is-cocartesian-arrow B b b' u P e e' f))
```

```rzk title="BW23, Definition 5.2.2"
#def is-naive-cocartesian-family
  ( B : U)
  ( P : B → U)
  : U
  := product (is-inner-family B P) (has-cocartesian-lifts B P)
```

## Definition via LARI Families

By using this definition, we obtain the closure properties "for free" from our
work on LARI families.

```rzk
#def is-cocartesian-family
  ( B : U)
  ( P : B → U)
  : U
  := is-LARI-family 2 Δ¹ (\ t → t ≡ 0₂) B P
```

### Cocartesian Families are LARI Families

In order to show that cocartesian families and $i_0$-LARI families are the same,
we show that being a cocartesian arrow is the same as being a dependent initial
object in a certain type family. While challenging in a technical and formal
sense, this proof is just repackaging the data from one form into another.

We want to apply `#!rzk equiv-family-of-props` to the two properties that we
want to show equivalence for. Thus we give several local definitions (marked
with the prefix `temp-96cf`) to give meaning to the terms and avoid repeating
big expressions.

```rzk
#section is-cocartesian-arrow-equiv-is-dependent-initial

#variable B : U
#variable P : B → U
#variable is-inner-family-P : is-inner-family B P

#def temp-96cf-G
  : U
  := Σ (f : Δ¹ → B) , P (f 0₂)

#def temp-96cf-Q uses (B)
  ( ( f , e) : temp-96cf-G)
  : U
  := (t : Δ¹) → P (f t) [t ≡ 0₂ ↦ e]

#variable f : Δ¹ → B
#variable e : P (f 0₂)
#variable F : temp-96cf-Q (f , e)

#def temp-96cf-A
  : U
  :=
  ( Σ ( b'' : B)
    , Σ ( g : hom B (f 1₂) b'')
      , Σ ( h : hom B (f 0₂) b'')
        , Σ ( τ : hom2 B (f 0₂) (f 1₂) b'' f g h)
          , Σ ( e'' : P b'')
            , dhom B (f 0₂) b'' (\ t → τ (t , t)) P e e'')

#def temp-96cf-A'
  : U
  :=
  ( Σ ( f' : Δ¹ → B)
    , Σ ( e' : P(f' 0₂))
      , Σ ( m : hom temp-96cf-G (f , e) (f' , e'))
        , ( t : Δ¹) → P (f' t) [t ≡ 0₂ ↦ e'])

#def temp-96cf-R
  ( ( b'' , (g , (h , (τ , (e'' , F'))))) : temp-96cf-A)
  : U
  :=
  ( Σ ( G : dhom B (f 1₂) b'' g P (F 1₂) e'')
    , dhom2 B (f 0₂) (f 1₂) b'' f g h τ P e (F 1₂) e'' (\ t → F t) G F')

#def temp-96cf-R' uses (P B)
  ( ( f' , (e' , (m , F'))) : temp-96cf-A')
  : U
  := dhom temp-96cf-G (f , e) (f' , e') m (temp-96cf-Q) F F'

#def temp-96cf-alpha₁ uses (f P B)
  ( ( b'' , (g , (h , (τ , (e'' , F'))))) : temp-96cf-A)
  : temp-96cf-A'
  :=
  ( \ t → τ (t , t)
    , ( e
      , ( \ s → (\ t → recOR(Δ² (t , s) ↦ τ (t , s) , t ≤ s ↦ h t) , e)
        , F')))

#def temp-96cf-A'-inner-filler uses (e f B)
  ( ( f' , (e' , (m , F'))) : temp-96cf-A')
  : ( ( t , s) : Δ²) → P (first (m t) s) [t ≡ 1₂ ↦ F' s , s ≡ 0₂ ↦ second (m t)]
  :=
  center-contraction
  ( ( ( t , s) : Δ²) → P (first (m t) s) [t ≡ 1₂ ↦ F' s , s ≡ 0₂ ↦ second (m t)])
  ( is-inner-family-P
    ( \ (t , s) → first (m t) s)
    ( \ (t , s) → recOR(t ≡ 1₂ ↦ F' s , s ≡ 0₂ ↦ second (m t))))

#def temp-96cf-A'-diag uses (is-inner-family-P)
  ( ( f' , (e' , (m , F'))) : temp-96cf-A')
  : dhom B (f 0₂) (f' 1₂) (\ t → first (m t) t) P e (F' 1₂)
  :=
  \ t → temp-96cf-A'-inner-filler (f' , (e' , (m , F'))) (t , t)

#def temp-96cf-alpha₂ uses (e f is-inner-family-P P B)
  ( ( f' , (e' , (m , F'))) : temp-96cf-A')
  : temp-96cf-A
  :=
  ( f' 1₂
  , ( \ t → first (m t) 1₂
    , ( \ t → first (m t) t
      , ( \ (t , s) → first (m s) t
        , ( F' 1₂
          , temp-96cf-A'-diag (f' , (e' , (m , F'))))))))
```

With those defined, we can give a visual overview of what the proof is doing:

<?xml version='1.0' encoding='UTF-8'?>
<svg class="typst-doc" viewBox="0 0 340.15748031496065 113.38582677165354" width="340.15748031496065pt" height="113.38582677165354pt" xmlns="http://www.w3.org/2000/svg" xmlns:xlink="http://www.w3.org/1999/xlink" xmlns:h5="http://www.w3.org/1999/xhtml">
    <g>
        <g class="typst-group" transform="matrix(1 0 0 1 7.08661417322835 10.980946850393703)">
            <g>
                <path class="typst-shape" fill="none" transform="matrix(1 0 0 1 7.469149168853895 0)" d="M 0 0h 109.78611 v 10.241 h -109.78611 v -10.241 Z "/>
                <g class="typst-group">
                    <g>
                        <g class="typst-group" transform="matrix(1 0 0 1 7.469149039370083 -0.00000011023622198446514)">
                            <g>
                                <g class="typst-group">
                                    <g>
                                        <g class="typst-text" transform="matrix(1 0 0 -1 0 7.513000000000001)">
                                            <use xlink:href="#g29E4975B78418E20032E60ADA841E98B" x="0" y="0" fill="#000000" fill-rule="nonzero"/>
                                        </g>
                                        <g class="typst-text" transform="matrix(1 0 0 -1 4.279 7.513000000000001)">
                                            <use xlink:href="#gD69327CDAE318D679FC4BE63780CFA81" x="0" y="0" fill="#000000" fill-rule="nonzero"/>
                                        </g>
                                        <g class="typst-text" transform="matrix(1 0 0 -1 13.153555555555556 7.513000000000001)">
                                            <use xlink:href="#gB03DAE7C80C63AB83560DB0A4C93A908" x="0" y="0" fill="#000000" fill-rule="nonzero"/>
                                        </g>
                                        <g class="typst-text" transform="matrix(1 0 0 -1 19.267111111111113 7.513000000000001)">
                                            <use xlink:href="#g81F644AAE7026A7100D6F1A653A1600C" x="0" y="0" fill="#000000" fill-rule="nonzero"/>
                                        </g>
                                        <g class="typst-text" transform="matrix(1 0 0 -1 27.517111111111113 7.513000000000001)">
                                            <use xlink:href="#g60C750E8AE5C5F8085F1D771DD05A377" x="0" y="0" fill="#000000" fill-rule="nonzero"/>
                                        </g>
                                        <g class="typst-text" transform="matrix(1 0 0 -1 53.79611111111111 7.513000000000001)">
                                            <use xlink:href="#g148E85FBC232B2FC8B39CE10C8EF8377" x="0" y="0" fill="#000000" fill-rule="nonzero"/>
                                        </g>
                                        <g class="typst-text" transform="matrix(1 0 0 -1 86.79611111111112 7.513000000000001)">
                                            <use xlink:href="#g8624EA81C777B56B83FDCB4123F06042" x="0" y="0" fill="#000000" fill-rule="nonzero"/>
                                        </g>
                                        <g class="typst-text" transform="matrix(1 0 0 -1 95.40911111111113 7.513000000000001)">
                                            <use xlink:href="#g29E4975B78418E20032E60ADA841E98B" x="0" y="0" fill="#000000" fill-rule="nonzero"/>
                                        </g>
                                        <g class="typst-text" transform="matrix(1 0 0 -1 99.68811111111111 7.513000000000001)">
                                            <use xlink:href="#gD69327CDAE318D679FC4BE63780CFA81" x="0" y="0" fill="#000000" fill-rule="nonzero"/>
                                        </g>
                                        <g class="typst-text" transform="matrix(1 0 0 -1 105.50711111111113 7.513000000000001)">
                                            <use xlink:href="#g60C750E8AE5C5F8085F1D771DD05A377" x="0" y="0" fill="#000000" fill-rule="nonzero"/>
                                        </g>
                                    </g>
                                </g>
                            </g>
                        </g>
                    </g>
                </g>
                <path class="typst-shape" fill="none" transform="matrix(1 0 0 1 211.7854437007874 75.98664173228346)" d="M 0 0h 15.799191 v 15.437291 h -15.799191 v -15.437291 Z "/>
                <g class="typst-group">
                    <g>
                        <g class="typst-group" transform="matrix(1 0 0 1 211.78544357480317 75.98664163779527)">
                            <g>
                                <g class="typst-text" transform="matrix(1 0 0 -1 2.8346456692913384 10.347645669291339)">
                                    <use xlink:href="#gB7169A9D177B95183E8B87B52F2B966B" x="0" y="0" fill="#000000" fill-rule="nonzero"/>
                                </g>
                                <g class="typst-text" transform="matrix(1 0 0 -1 9.214645669291338 6.354645669291339)">
                                    <use xlink:href="#g443B124EC01EAB2F98238ACC3BEE70A6" x="0" y="0" fill="#000000" fill-rule="nonzero"/>
                                </g>
                            </g>
                        </g>
                    </g>
                </g>
                <path class="typst-shape" fill="none" transform="matrix(1 0 0 1 213.66039370078738 18.029665354330707)" d="M 0 0h 12.049292 v 15.437291 h -12.049292 v -15.437291 Z "/>
                <g class="typst-group">
                    <g>
                        <g class="typst-group" transform="matrix(1 0 0 1 213.6603935905512 18.02966525984252)">
                            <g>
                                <g class="typst-text" transform="matrix(1 0 0 -1 2.8346456692913384 10.347645669291339)">
                                    <use xlink:href="#gB7169A9D177B95183E8B87B52F2B966B" x="0" y="0" fill="#000000" fill-rule="nonzero"/>
                                </g>
                            </g>
                        </g>
                    </g>
                </g>
                <path class="typst-shape" fill="none" transform="matrix(1 0 0 1 271.7540212598425 75.98664173228346)" d="M 0 0h 11.710546 v 10.468646 h -11.710546 v -10.468646 Z "/>
                <g class="typst-group">
                    <g>
                        <g class="typst-group" transform="matrix(1 0 0 1 271.75402122834646 75.98664166929133)">
                            <g>
                                <g class="typst-text" transform="matrix(1 0 0 -1 1.4173228346456692 8.93032283464567)">
                                    <use xlink:href="#g273CACE7470199A800B4A0FC82A0051F" x="0" y="0" fill="#000000" fill-rule="nonzero"/>
                                </g>
                                <g class="typst-text" transform="matrix(1 0 0 -1 6.54332283464567 4.93732283464567)">
                                    <use xlink:href="#g443B124EC01EAB2F98238ACC3BEE70A6" x="0" y="0" fill="#000000" fill-rule="nonzero"/>
                                </g>
                            </g>
                        </g>
                    </g>
                </g>
                <path class="typst-shape" fill="none" transform="matrix(1 0 0 1 275.5039212598425 22.99831102362205)" d="M 0 0h 7.9606457 v 10.468646 h -7.9606457 v -10.468646 Z "/>
                <g class="typst-group">
                    <g>
                        <g class="typst-group" transform="matrix(1 0 0 1 275.5039212440945 22.998310960629926)">
                            <g>
                                <g class="typst-text" transform="matrix(1 0 0 -1 1.4173228346456692 8.93032283464567)">
                                    <use xlink:href="#g273CACE7470199A800B4A0FC82A0051F" x="0" y="0" fill="#000000" fill-rule="nonzero"/>
                                </g>
                            </g>
                        </g>
                    </g>
                </g>
                <path class="typst-shape" fill="none" transform="matrix(1 0 0 1 251.14662125984256 48.188976377952756)" d="M 0 0h 32.317947 v 13.075645 h -32.317947 v -13.075645 Z "/>
                <g class="typst-group">
                    <g>
                        <g class="typst-group" transform="matrix(1 0 0 1 251.14662119685045 48.188976267716534)">
                            <g>
                                <g class="typst-text" transform="matrix(1 0 0 -1 1.4173228346456692 8.93032283464567)">
                                    <use xlink:href="#g293C2D96009CA7436726DF2682208263" x="0" y="0" fill="#000000" fill-rule="nonzero"/>
                                </g>
                                <g class="typst-text" transform="matrix(1 0 0 -1 7.687322834645669 11.647322834645669)">
                                    <use xlink:href="#g584B0F370842A356700A11AD73C4E2E5" x="0" y="0" fill="#000000" fill-rule="nonzero"/>
                                </g>
                                <g class="typst-text" transform="matrix(1 0 0 -1 12.684622834645669 8.93032283464567)">
                                    <use xlink:href="#g29E4975B78418E20032E60ADA841E98B" x="0" y="0" fill="#000000" fill-rule="nonzero"/>
                                </g>
                                <g class="typst-text" transform="matrix(1 0 0 -1 16.96362283464567 8.93032283464567)">
                                    <use xlink:href="#gAEBF7686F00B20CFC7D43C5EA9E9C44F" x="0" y="0" fill="#000000" fill-rule="nonzero"/>
                                </g>
                                <g class="typst-text" transform="matrix(1 0 0 -1 26.62162283464567 8.93032283464567)">
                                    <use xlink:href="#g60C750E8AE5C5F8085F1D771DD05A377" x="0" y="0" fill="#000000" fill-rule="nonzero"/>
                                </g>
                            </g>
                        </g>
                    </g>
                </g>
                <path class="typst-shape" fill="none" transform="matrix(1 0 0 1 204.9433893700787 49.60629921259842)" d="M 0 0h 29.4833 v 10.241 h -29.4833 v -10.241 Z "/>
                <g class="typst-group">
                    <g>
                        <g class="typst-group" transform="matrix(1 0 0 1 204.94338930708662 49.6062991023622)">
                            <g>
                                <g class="typst-text" transform="matrix(1 0 0 -1 0 7.513000000000001)">
                                    <use xlink:href="#g293C2D96009CA7436726DF2682208263" x="0" y="0" fill="#000000" fill-rule="nonzero"/>
                                </g>
                                <g class="typst-text" transform="matrix(1 0 0 -1 6.27 10.23)">
                                    <use xlink:href="#gA37D944EE46D6D738F17A6506485E6D7" x="0" y="0" fill="#000000" fill-rule="nonzero"/>
                                </g>
                                <g class="typst-text" transform="matrix(1 0 0 -1 11.267299999999999 7.513000000000001)">
                                    <use xlink:href="#g29E4975B78418E20032E60ADA841E98B" x="0" y="0" fill="#000000" fill-rule="nonzero"/>
                                </g>
                                <g class="typst-text" transform="matrix(1 0 0 -1 15.546299999999999 7.513000000000001)">
                                    <use xlink:href="#gAEBF7686F00B20CFC7D43C5EA9E9C44F" x="0" y="0" fill="#000000" fill-rule="nonzero"/>
                                </g>
                                <g class="typst-text" transform="matrix(1 0 0 -1 25.2043 7.513000000000001)">
                                    <use xlink:href="#g60C750E8AE5C5F8085F1D771DD05A377" x="0" y="0" fill="#000000" fill-rule="nonzero"/>
                                </g>
                            </g>
                        </g>
                    </g>
                </g>
                <path class="typst-shape" fill="none" stroke="#000000" stroke-width="1" stroke-linecap="butt" stroke-linejoin="miter" stroke-miterlimit="4" transform="matrix(1 0 0 1 198.4251968503937 33.466956692913385)" d="M 0 0m 42.519684 42.519684 h -42.519684 v -42.519684 h 42.519684 v 42.519684 "/>
                <path class="typst-shape" fill="url(#pAAB50FF8EB52344855BB1D98541890EC)" fill-rule="nonzero" stroke="#000000" stroke-width="1" stroke-linecap="butt" stroke-linejoin="miter" stroke-miterlimit="4" transform="matrix(1 0 0 1 283.46456692913387 33.466956692913385)" d="M 0 0m 42.519684 42.519684 h -42.519684 v -42.519684 h 42.519684 "/>
                <path class="typst-shape" fill="none" stroke="#0065bd" stroke-width="1" stroke-linecap="butt" stroke-linejoin="miter" stroke-miterlimit="4" stroke-dashoffset="0" stroke-dasharray="1 1" transform="matrix(1 0 0 1 325.98425196850394 33.466956692913385)" d="M 0 0v 42.519684 "/>
                <path class="typst-shape" fill="none" transform="matrix(1 0 0 1 295.74131377952756 75.98664173228346)" d="M 0 0h 17.966192 v 13.182291 h -17.966192 v -13.182291 Z "/>
                <g class="typst-group">
                    <g>
                        <g class="typst-group" transform="matrix(1 0 0 1 295.74131371653544 75.98664165354332)">
                            <g>
                                <g class="typst-text" transform="matrix(1 0 0 -1 2.8346456692913384 10.347645669291339)">
                                    <use xlink:href="#gCB84B0639382626A1305E08391B56DBF" x="0" y="0" fill="#000000" fill-rule="nonzero"/>
                                </g>
                                <g class="typst-text" transform="matrix(1 0 0 -1 11.38164566929134 6.354645669291339)">
                                    <use xlink:href="#g443B124EC01EAB2F98238ACC3BEE70A6" x="0" y="0" fill="#000000" fill-rule="nonzero"/>
                                </g>
                            </g>
                        </g>
                    </g>
                </g>
                <path class="typst-shape" fill="none" transform="matrix(1 0 0 1 297.6162637795275 20.2846653543307)" d="M 0 0h 14.216291 v 13.182291 h -14.216291 v -13.182291 Z "/>
                <g class="typst-group">
                    <g>
                        <g class="typst-group" transform="matrix(1 0 0 1 297.61626373228347 20.284665275590548)">
                            <g>
                                <g class="typst-text" transform="matrix(1 0 0 -1 2.8346456692913384 10.347645669291339)">
                                    <use xlink:href="#gCB84B0639382626A1305E08391B56DBF" x="0" y="0" fill="#000000" fill-rule="nonzero"/>
                                </g>
                            </g>
                        </g>
                    </g>
                </g>
                <path class="typst-shape" fill="none" transform="matrix(1 0 0 1 199.72722318460194 0)" d="M 0 0h 119.28571 v 10.241 h -119.28571 v -10.241 Z "/>
                <g class="typst-group">
                    <g>
                        <g class="typst-group" transform="matrix(1 0 0 1 199.72722316535433 -0.00000011023622198446514)">
                            <g>
                                <g class="typst-group">
                                    <g>
                                        <g class="typst-text" transform="matrix(1 0 0 -1 0 7.513000000000001)">
                                            <use xlink:href="#g29E4975B78418E20032E60ADA841E98B" x="0" y="0" fill="#000000" fill-rule="nonzero"/>
                                        </g>
                                        <g class="typst-text" transform="matrix(1 0 0 -1 4.279 7.513000000000001)">
                                            <use xlink:href="#gD69327CDAE318D679FC4BE63780CFA81" x="0" y="0" fill="#000000" fill-rule="nonzero"/>
                                        </g>
                                        <g class="typst-text" transform="matrix(1 0 0 -1 10.097999999999999 3.5200000000000005)">
                                            <use xlink:href="#g443B124EC01EAB2F98238ACC3BEE70A6" x="0" y="0" fill="#000000" fill-rule="nonzero"/>
                                        </g>
                                        <g class="typst-text" transform="matrix(1 0 0 -1 16.903455555555556 7.513000000000001)">
                                            <use xlink:href="#gB03DAE7C80C63AB83560DB0A4C93A908" x="0" y="0" fill="#000000" fill-rule="nonzero"/>
                                        </g>
                                        <g class="typst-text" transform="matrix(1 0 0 -1 23.017011111111113 7.513000000000001)">
                                            <use xlink:href="#g81F644AAE7026A7100D6F1A653A1600C" x="0" y="0" fill="#000000" fill-rule="nonzero"/>
                                        </g>
                                        <g class="typst-text" transform="matrix(1 0 0 -1 31.267011111111113 3.5200000000000005)">
                                            <use xlink:href="#g443B124EC01EAB2F98238ACC3BEE70A6" x="0" y="0" fill="#000000" fill-rule="nonzero"/>
                                        </g>
                                        <g class="typst-text" transform="matrix(1 0 0 -1 35.01691111111111 7.513000000000001)">
                                            <use xlink:href="#g60C750E8AE5C5F8085F1D771DD05A377" x="0" y="0" fill="#000000" fill-rule="nonzero"/>
                                        </g>
                                        <g class="typst-text" transform="matrix(1 0 0 -1 55.79591111111112 7.513000000000001)">
                                            <use xlink:href="#g148E85FBC232B2FC8B39CE10C8EF8377" x="0" y="0" fill="#000000" fill-rule="nonzero"/>
                                        </g>
                                        <g class="typst-group">
                                            <g>
                                                <g class="typst-text" transform="matrix(1 0 0 -1 88.79591111111111 7.513000000000001)">
                                                    <use xlink:href="#g8624EA81C777B56B83FDCB4123F06042" x="0" y="0" fill="#000000" fill-rule="nonzero"/>
                                                </g>
                                                <g class="typst-text" transform="matrix(1 0 0 -1 97.40891111111112 3.5200000000000005)">
                                                    <use xlink:href="#g443B124EC01EAB2F98238ACC3BEE70A6" x="0" y="0" fill="#000000" fill-rule="nonzero"/>
                                                </g>
                                                <g class="typst-text" transform="matrix(1 0 0 -1 101.1588111111111 7.513000000000001)">
                                                    <use xlink:href="#g29E4975B78418E20032E60ADA841E98B" x="0" y="0" fill="#000000" fill-rule="nonzero"/>
                                                </g>
                                                <g class="typst-text" transform="matrix(1 0 0 -1 105.43781111111112 7.513000000000001)">
                                                    <use xlink:href="#gD69327CDAE318D679FC4BE63780CFA81" x="0" y="0" fill="#000000" fill-rule="nonzero"/>
                                                </g>
                                                <g class="typst-text" transform="matrix(1 0 0 -1 111.25681111111112 3.5200000000000005)">
                                                    <use xlink:href="#g443B124EC01EAB2F98238ACC3BEE70A6" x="0" y="0" fill="#000000" fill-rule="nonzero"/>
                                                </g>
                                                <g class="typst-text" transform="matrix(1 0 0 -1 115.00671111111112 7.513000000000001)">
                                                    <use xlink:href="#g60C750E8AE5C5F8085F1D771DD05A377" x="0" y="0" fill="#000000" fill-rule="nonzero"/>
                                                </g>
                                            </g>
                                        </g>
                                    </g>
                                </g>
                            </g>
                        </g>
                    </g>
                </g>
                <path class="typst-shape" fill="none" transform="matrix(1 0 0 1 5.4606511811023655 54.72679921259842)" d="M 0 0h 15.799191 v 15.437291 h -15.799191 v -15.437291 Z "/>
                <g class="typst-group">
                    <g>
                        <g class="typst-group" transform="matrix(1 0 0 1 5.460651055118113 54.726799118110236)">
                            <g>
                                <g class="typst-text" transform="matrix(1 0 0 -1 2.8346456692913384 10.347645669291339)">
                                    <use xlink:href="#gB7169A9D177B95183E8B87B52F2B966B" x="0" y="0" fill="#000000" fill-rule="nonzero"/>
                                </g>
                                <g class="typst-text" transform="matrix(1 0 0 -1 9.214645669291338 6.354645669291339)">
                                    <use xlink:href="#g443B124EC01EAB2F98238ACC3BEE70A6" x="0" y="0" fill="#000000" fill-rule="nonzero"/>
                                </g>
                            </g>
                        </g>
                    </g>
                </g>
                <path class="typst-shape" fill="none" transform="matrix(1 0 0 1 15.2351968503937 18.029665354330707)" d="M 0 0h 12.049292 v 15.437291 h -12.049292 l -0.0000000000000031470889 -15.437291 Z "/>
                <g class="typst-group">
                    <g>
                        <g class="typst-group" transform="matrix(1 0 0 1 15.235196740157482 18.02966525984252)">
                            <g>
                                <g class="typst-text" transform="matrix(1 0 0 -1 2.8346456692913384 10.347645669291339)">
                                    <use xlink:href="#gB7169A9D177B95183E8B87B52F2B966B" x="0" y="0" fill="#000000" fill-rule="nonzero"/>
                                </g>
                            </g>
                        </g>
                    </g>
                </g>
                <path class="typst-shape" fill="none" transform="matrix(1 0 0 1 127.55905511811024 75.98664173228346)" d="M 0 0h 13.558546 v 10.468646 h -13.558546 v -10.468646 Z "/>
                <g class="typst-group">
                    <g>
                        <g class="typst-group" transform="matrix(1 0 0 1 127.55905499212597 75.98664166929133)">
                            <g>
                                <g class="typst-text" transform="matrix(1 0 0 -1 1.4173228346456692 8.93032283464567)">
                                    <use xlink:href="#g273CACE7470199A800B4A0FC82A0051F" x="0" y="0" fill="#000000" fill-rule="nonzero"/>
                                </g>
                                <g class="typst-text" transform="matrix(1 0 0 -1 6.54332283464567 4.93732283464567)">
                                    <use xlink:href="#g4BA1FCBFDAC4BA99FE2255AD6CF5831E" x="0" y="0" fill="#000000" fill-rule="nonzero"/>
                                </g>
                            </g>
                        </g>
                    </g>
                </g>
                <path class="typst-shape" fill="none" transform="matrix(1 0 0 1 77.07872440944881 22.99831102362205)" d="M 0 0h 7.9606457 v 10.468646 h -7.9606457 v -10.468646 Z "/>
                <g class="typst-group">
                    <g>
                        <g class="typst-group" transform="matrix(1 0 0 1 77.07872439370078 22.998310960629926)">
                            <g>
                                <g class="typst-text" transform="matrix(1 0 0 -1 1.4173228346456692 8.93032283464567)">
                                    <use xlink:href="#g273CACE7470199A800B4A0FC82A0051F" x="0" y="0" fill="#000000" fill-rule="nonzero"/>
                                </g>
                            </g>
                        </g>
                    </g>
                </g>
                <path class="typst-shape" fill="none" transform="matrix(1 0 0 1 25.381956692913384 43.817685039370076)" d="M 0 0h 5.929 v 7.645 h -5.929 l -0.0000000000000031470889 -7.645 Z "/>
                <g class="typst-group">
                    <g>
                        <g class="typst-group" transform="matrix(1 0 0 1 25.38195661417323 43.817684913385825)">
                            <g>
                                <g class="typst-text" transform="matrix(1 0 0 -1 0 7.513000000000001)">
                                    <use xlink:href="#g6D95EB440369500A57EF39BB7350EBFC" x="0" y="0" fill="#000000" fill-rule="nonzero"/>
                                </g>
                            </g>
                        </g>
                    </g>
                </g>
                <path class="typst-shape" fill="none" stroke="#000000" stroke-width="1" stroke-linecap="butt" stroke-linejoin="miter" stroke-miterlimit="4" transform="matrix(1 0 0 1 0 33.466956692913385)" d="M 0 0m 42.519684 42.519684 l -42.519684 -42.519684 h 42.519684 v 42.519684 "/>
                <path class="typst-shape" fill="url(#pAAB50FF8EB52344855BB1D98541890EC)" fill-rule="nonzero" stroke="#000000" stroke-width="1" stroke-linecap="butt" stroke-linejoin="miter" stroke-miterlimit="4" transform="matrix(1 0 0 1 85.03937007874016 33.466956692913385)" d="M 0 0m 42.519684 42.519684 l -42.519684 -42.519684 h 42.519684 "/>
                <path class="typst-shape" fill="none" stroke="#0065bd" stroke-width="1" stroke-linecap="butt" stroke-linejoin="miter" stroke-miterlimit="4" stroke-dashoffset="0" stroke-dasharray="1 1" transform="matrix(1 0 0 1 127.55905511811024 33.466956692913385)" d="M 0 0m 0 42.519684 v -42.519684 "/>
                <path class="typst-shape" fill="none" transform="matrix(1 0 0 1 88.33302125984254 54.72679921259842)" d="M 0 0h 17.966192 v 13.182291 h -17.966192 v -13.182291 Z "/>
                <g class="typst-group">
                    <g>
                        <g class="typst-group" transform="matrix(1 0 0 1 88.3330211968504 54.72679913385827)">
                            <g>
                                <g class="typst-text" transform="matrix(1 0 0 -1 2.8346456692913384 10.347645669291339)">
                                    <use xlink:href="#gCB84B0639382626A1305E08391B56DBF" x="0" y="0" fill="#000000" fill-rule="nonzero"/>
                                </g>
                                <g class="typst-text" transform="matrix(1 0 0 -1 11.38164566929134 6.354645669291339)">
                                    <use xlink:href="#g443B124EC01EAB2F98238ACC3BEE70A6" x="0" y="0" fill="#000000" fill-rule="nonzero"/>
                                </g>
                            </g>
                        </g>
                    </g>
                </g>
                <path class="typst-shape" fill="none" transform="matrix(1 0 0 1 99.19106692913387 20.2846653543307)" d="M 0 0h 14.216291 v 13.182291 h -14.216291 v -13.182291 Z "/>
                <g class="typst-group">
                    <g>
                        <g class="typst-group" transform="matrix(1 0 0 1 99.19106688188975 20.284665275590548)">
                            <g>
                                <g class="typst-text" transform="matrix(1 0 0 -1 2.8346456692913384 10.347645669291339)">
                                    <use xlink:href="#gCB84B0639382626A1305E08391B56DBF" x="0" y="0" fill="#000000" fill-rule="nonzero"/>
                                </g>
                            </g>
                        </g>
                    </g>
                </g>
            </g>
        </g>
    </g>
    <defs id="glyph">
        <symbol id="g29E4975B78418E20032E60ADA841E98B" overflow="visible">
            <path d="M 0 0m 3.498 -2.728 c 0.09899998 0 0.15400004 0.05499983 0.15400004 0.15400004 c 0 0.032999992 -0.022000074 0.0769999 -0.055000067 0.12099981 c -0.5719998 0.44000006 -1.0339999 1.1660001 -1.375 2.167 c -0.29699993 0.869 -0.45099986 1.727 -0.45099986 2.5740001 v 0.9239998 c 0 0.8470001 0.15399992 1.7049999 0.45099986 2.574 c 0.34100008 1.0010004 0.8030002 1.7270002 1.375 2.1670003 c 0.032999992 0.032999992 0.055000067 0.076999664 0.055000067 0.12100029 c 0 0.09899998 -0.055000067 0.15399933 -0.15400004 0.15399933 c -0.010999918 0 -0.04399991 -0.01099968 -0.0769999 -0.032999992 c -0.6600001 -0.50599957 -1.21 -1.2539997 -1.661 -2.2549996 c -0.42900002 -0.95700026 -0.64900005 -1.8590002 -0.64900005 -2.7280002 v -0.9239998 c 0 -0.8690001 0.22000003 -1.7710001 0.64900005 -2.7280002 c 0.45099998 -1.0009999 1.0009999 -1.7489998 1.661 -2.2549999 c 0.032999992 -0.022000074 0.065999985 -0.032999992 0.0769999 -0.032999992 Z "/>
        </symbol>
        <symbol id="gD69327CDAE318D679FC4BE63780CFA81" overflow="visible">
            <path d="M 0 0m 5.478 1.584 c 0 0.09899998 -0.055000305 0.15400004 -0.17600012 0.15400004 c -0.0880003 0 -0.15400028 -0.07700002 -0.18700027 -0.23100007 c -0.21999979 -0.86899996 -0.48399973 -1.309 -0.78099966 -1.309 c -0.18700027 0 -0.28600025 0.154 -0.28600025 0.46199995 c 0 0.143 0.04400015 0.40700006 0.14300013 0.79200006 l 0.62699986 2.475 c 0.055000305 0.20900011 0.07700014 0.32999992 0.07700014 0.38499975 c 0 0.22000027 -0.12099981 0.3300004 -0.36299992 0.3300004 c -0.23099995 0 -0.38500023 -0.13200045 -0.4619999 -0.38500023 c -0.23100019 0.40700006 -0.5610001 0.605 -0.9790001 0.605 c -0.71500015 0 -1.3420001 -0.36299992 -1.8920001 -1.089 c -0.506 -0.6819999 -0.759 -1.3859999 -0.759 -2.1230001 c 0 -0.95699996 0.56100005 -1.771 1.4849999 -1.771 c 0.47300005 0 0.93499994 0.253 1.375 0.759 c 0.12100005 -0.418 0.49500012 -0.759 1.0119998 -0.759 c 0.7590003 0 0.99000025 0.891 1.1660004 1.705 Z m -1.7270002 2.5299997 c 0.09899998 -0.23099995 0.15400004 -0.38499975 0.15400004 -0.48399997 c 0 -0.04399991 -0.010999918 -0.09899998 -0.022000074 -0.17599988 l -0.53900003 -2.112 c -0.032999992 -0.12100005 -0.109999895 -0.25300002 -0.20899987 -0.385 c -0.40700006 -0.50600004 -0.803 -0.759 -1.188 -0.759 c -0.42900002 0 -0.64900005 0.32999998 -0.64900005 0.97900003 c 0 0.26399994 0.065999985 0.65999997 0.19800007 1.188 c 0.23099995 0.93499994 0.5609999 1.562 0.96799994 1.9030001 c 0.22000003 0.1869998 0.4289999 0.27499962 0.638 0.27499962 c 0.29699993 0 0.51699996 -0.14299965 0.6489999 -0.4289999 Z "/>
        </symbol>
        <symbol id="gB03DAE7C80C63AB83560DB0A4C93A908" overflow="visible">
            <path d="M 0 0m 2.112 4.125 c 0 0.32999992 -0.25300002 0.6160002 -0.58299994 0.6160002 c -0.33000004 0 -0.58300006 -0.28600025 -0.58300006 -0.6160002 c 0 -0.32999992 0.25300002 -0.61599994 0.58300006 -0.61599994 c 0.32999992 0 0.58299994 0.286 0.58299994 0.61599994 Z m 0 -3.509 c 0 0.32999998 -0.25300002 0.616 -0.58299994 0.616 c -0.33000004 0 -0.58300006 -0.286 -0.58300006 -0.616 c 0 -0.32999998 0.25300002 -0.616 0.58300006 -0.616 c 0.32999992 0 0.58299994 0.286 0.58299994 0.616 Z "/>
        </symbol>
        <symbol id="g81F644AAE7026A7100D6F1A653A1600C" overflow="visible">
            <path d="M 0 0m 1.507 0.033 c 0.19800007 0 0.8800001 -0.033 1.089 -0.033 c 0.16499996 0 0.2420001 0.088 0.2420001 0.253 c 0 0.09900001 -0.065999985 0.16499999 -0.20900011 0.176 c -0.319 0.011000007 -0.47300005 0.12100002 -0.47300005 0.33 c 0 0.09899998 0.09899998 0.31899995 0.3080001 0.649 c 0.29699993 0.495 0.50600004 0.85800004 0.6489999 1.0999999 h 2.6729999 c 0 -0.0769999 0.011000156 -0.23099995 0.04400015 -0.4729998 c 0.07700014 -0.8030001 0.12099981 -1.243 0.12099981 -1.2980001 c 0 -0.20899999 -0.24199963 -0.308 -0.737 -0.308 c -0.20899963 0 -0.3079996 -0.088 -0.3079996 -0.264 c 0 -0.10999999 0.065999985 -0.16499999 0.19799995 -0.16499999 c 0.26399994 0 1.0999999 0.033 1.3639998 0.033 c 0.21999979 0 1.0009999 -0.033 1.2210002 -0.033 c 0.16499996 0 0.24199963 0.088 0.24199963 0.264 c 0 0.110000014 -0.09899998 0.16499999 -0.29699993 0.16499999 c -0.3080001 0 -0.4949999 0.022000015 -0.5499997 0.055000007 c -0.055000305 0.033000022 -0.09899998 0.132 -0.11000013 0.29700002 l -0.65999985 6.798 c -0.032999992 0.20900011 -0.022000313 0.29699993 -0.25300026 0.29699993 c -0.13199997 0 -0.2420001 -0.065999985 -0.31899977 -0.20900011 l -3.7840002 -6.347 c -0.32999992 -0.54999995 -0.77 -0.84699994 -1.309 -0.8909999 c -0.176 -0.011000007 -0.264 -0.09900001 -0.264 -0.264 c 0 -0.10999999 0.066000015 -0.16499999 0.18700004 -0.16499999 c 0.176 0 0.75899994 0.033 0.93499994 0.033 Z m 3.9050002 6.314 l 0.32999992 -3.41 h -2.365 Z "/>
        </symbol>
        <symbol id="g60C750E8AE5C5F8085F1D771DD05A377" overflow="visible">
            <path d="M 0 0m 0.858 -2.695 c 0.66 0.50600004 1.21 1.254 1.661 2.2549999 c 0.4289999 0.957 0.6489999 1.859 0.6489999 2.7280002 v 0.9239998 c 0 0.86899996 -0.22000003 1.7709999 -0.6489999 2.7280002 c -0.45099998 1.0009999 -1.001 1.7490001 -1.661 2.2549996 c -0.032999992 0.022000313 -0.065999985 0.032999992 -0.07699996 0.032999992 c -0.09900004 0 -0.15400004 -0.05499935 -0.15400004 -0.15399933 c 0 -0.044000626 0.022000015 -0.0880003 0.055000007 -0.12100029 c 0.57199997 -0.44000006 1.0339999 -1.1659999 1.375 -2.1670003 c 0.29700017 -0.86899996 0.45099998 -1.7269998 0.45099998 -2.574 v -0.9239998 c 0 -0.8470001 -0.1539998 -1.7050002 -0.45099998 -2.5740001 c -0.34099996 -1.0009999 -0.803 -1.727 -1.375 -2.167 c -0.032999992 -0.04399991 -0.055000007 -0.08799982 -0.055000007 -0.12099981 c 0 -0.099000216 0.055000007 -0.15400004 0.15400004 -0.15400004 c 0.010999978 0 0.04399997 0.010999918 0.07699996 0.032999992 Z "/>
        </symbol>
        <symbol id="g148E85FBC232B2FC8B39CE10C8EF8377" overflow="visible">
            <path d="M 0 0m 10.252 2.574 c 0.076999664 0.032999992 0.12100029 0.099000216 0.12100029 0.17600012 c 0 0.0769999 -0.044000626 0.14299989 -0.12100029 0.17599988 c -0.5279999 0.17600012 -1.0229998 0.5500002 -1.4849997 1.122 c -0.30800056 0.38500023 -0.5170002 0.83599997 -0.6160002 1.3530002 c -0.032999992 0.14300013 -0.12100029 0.20900011 -0.26399994 0.20900011 c -0.17600012 0 -0.26399994 -0.0880003 -0.26399994 -0.2750001 l 0.01099968 -0.021999836 v -0.011000156 c 0.18700027 -0.95700026 0.6710005 -1.7160001 1.474 -2.288 h -8.205999 c -0.176 0 -0.264 -0.08800006 -0.264 -0.26399994 c 0 -0.17600012 0.088 -0.26399994 0.264 -0.26399994 h 8.205999 c -0.8029995 -0.572 -1.2869997 -1.3310001 -1.474 -2.288 v -0.0109999925 l -0.01099968 -0.022000015 c 0 -0.18699999 0.08799982 -0.27499998 0.26399994 -0.27499998 c 0.14299965 0 0.23099995 0.066 0.26399994 0.20899999 c 0.09899998 0.517 0.3079996 0.96800005 0.6160002 1.353 c 0.4619999 0.5719999 0.9569998 0.946 1.4849997 1.1219999 Z "/>
        </symbol>
        <symbol id="g8624EA81C777B56B83FDCB4123F06042" overflow="visible">
            <path d="M 0 0m 8.129 5.841 c 0 0.5609999 -0.28599977 0.9899998 -0.84699965 1.2979999 c -0.4510002 0.25300026 -0.99000025 0.37400007 -1.5950003 0.37400007 h -3.1019998 c -0.25300002 0 -0.36300015 -0.011000156 -0.36300015 -0.26399994 c 0 -0.07700014 0.032999992 -0.13199997 0.099000216 -0.14300013 c 0.109999895 -0.011000156 0.19799995 -0.021999836 0.25299978 -0.021999836 c 0.33000016 -0.011000156 0.5170002 -0.032999992 0.572 -0.04400015 c 0.055000067 -0.011000156 0.08800006 -0.04400015 0.08800006 -0.09899998 c 0 -0.021999836 -0.010999918 -0.08799982 -0.04399991 -0.19799995 l -1.452 -5.841 c -0.055000067 -0.24200004 -0.16500008 -0.39600003 -0.33000004 -0.451 c -0.07700002 -0.022000015 -0.27499998 -0.033000022 -0.616 -0.033000022 c -0.24199998 0 -0.341 -0.010999978 -0.341 -0.253 c 0 -0.12099999 0.066000015 -0.176 0.19799998 -0.16499999 l 1.3640001 0.033 l 1.3859999 -0.033 c 0.17600012 -0.011 0.26399994 0.088 0.26399994 0.253 c 0 0.110000014 -0.12099981 0.16499999 -0.352 0.16499999 c -0.43999982 0 -0.65999985 0.055000007 -0.65999985 0.15400004 c 0 0 0.010999918 0.021999955 0.032999992 0.176 l 0.704 2.849 h 1.2649999 c 0.7590003 0 1.144 -0.319 1.144 -0.94599986 c 0 -0.09899998 -0.05499983 -0.34100008 -0.1539998 -0.737 c -0.12100029 -0.462 -0.17600012 -0.77 -0.17600012 -0.93500006 c 0 -0.83599997 0.64900017 -1.221 1.4850001 -1.221 c 0.3079996 0 0.605 0.143 0.90199995 0.41799998 c 0.29699993 0.275 0.4510002 0.572 0.4510002 0.88 c 0 0.110000014 -0.055000305 0.16499996 -0.1760006 0.16499996 c -0.076999664 0 -0.14299965 -0.054999948 -0.17599964 -0.176 c -0.12100029 -0.34099996 -0.2750001 -0.594 -0.4510002 -0.737 c -0.17600012 -0.143 -0.34100008 -0.22 -0.50600004 -0.22 c -0.25299978 0 -0.38499975 0.20899999 -0.38499975 0.616 c 0 0.264 0.032999992 0.671 0.11000013 1.232 c 0.032999992 0.23100007 0.043999672 0.39600003 0.043999672 0.5170001 c 0 0.58299994 -0.3080001 1.0119998 -0.9239998 1.276 c 1.0339999 0.25299978 2.2879996 0.9899998 2.2879996 2.112 Z m -1.4299998 0.93499994 c 0.22000027 -0.14300013 0.32999992 -0.38500023 0.32999992 -0.72599983 c 0 -0.22000027 -0.043999672 -0.47300005 -0.14299965 -0.77000046 c -0.2970004 -0.90199995 -1.0450001 -1.3529997 -2.244 -1.3529997 h -1.1660001 l 0.6930001 2.783 c 0.05499983 0.23099995 0.14299965 0.35199976 0.26399994 0.36299992 c 0.05499983 0.011000156 0.2750001 0.011000156 0.65999985 0.011000156 c 0.71500015 0 1.1329999 -0.022000313 1.606 -0.3080001 Z "/>
        </symbol>
        <symbol id="gB7169A9D177B95183E8B87B52F2B966B" overflow="visible">
            <path d="M 0 0m 6.072 6.963 c 0 0.4840002 -0.47300005 0.7920003 -0.99000025 0.7920003 c -0.6819997 0 -1.1549997 -0.44000006 -1.4079998 -1.309 c -0.055000067 -0.19799995 -0.17600012 -0.7590003 -0.352 -1.6830001 h -0.71500015 c -0.24199986 0 -0.36299992 -0.011000156 -0.36299992 -0.2420001 c 0 -0.12099981 0.11000013 -0.17600012 0.34100008 -0.17600012 h 0.65999985 l -0.803 -4.257 c -0.12099981 -0.627 -0.23099995 -1.089 -0.32999992 -1.3970001 c -0.13199997 -0.40699995 -0.319 -0.61599994 -0.561 -0.61599994 c -0.16499996 0 -0.29700005 0.04399991 -0.41799998 0.12099993 c 0.352 0.055000067 0.528 0.26400006 0.528 0.61600006 c 0 0.28599995 -0.143 0.42899996 -0.44000006 0.42899996 c -0.37399995 0 -0.63799995 -0.32999998 -0.63799995 -0.70399994 c 0 -0.4840001 0.45100003 -0.79199994 0.968 -0.79199994 c 0.27499998 0 0.528 0.109999895 0.7370001 0.34099984 c 0.35199976 0.36300004 0.62699986 0.88 0.8249998 1.5730001 c 0.12100005 0.429 0.23099995 0.847 0.3080001 1.265 l 0.638 3.4209998 h 0.90199995 c 0.25299978 0 0.36299992 0.011000156 0.36299992 0.26400042 c 0 0.09899998 -0.11000013 0.1539998 -0.32999992 0.1539998 h -0.8470001 c 0.065999985 0.45099974 0.37400007 2.112 0.47300005 2.321 c 0.11000013 0.23099995 0.26399994 0.34100008 0.4619999 0.34100008 c 0.16499996 0 0.3080001 -0.04400015 0.42900038 -0.12100029 c -0.34100008 -0.07700014 -0.5170002 -0.2750001 -0.5170002 -0.6160002 c 0 -0.28599977 0.14300013 -0.4289999 0.44000006 -0.4289999 c 0.37400007 0 0.638 0.32999992 0.638 0.704 Z "/>
        </symbol>
        <symbol id="g443B124EC01EAB2F98238ACC3BEE70A6" overflow="visible">
            <path d="M 0 0m 2.1868 4.2273 c -0.1925 0 -0.32340002 -0.07700014 -0.39269996 -0.23870015 l -1.2936001 -3.2494001 h 0.34649998 l 1.7094 2.8259 c 0.038499832 0.06929994 0.06159997 0.14630008 0.06159997 0.23099995 c 0 0.23100019 -0.20020008 0.43120027 -0.43120003 0.43120027 Z "/>
        </symbol>
        <symbol id="g273CACE7470199A800B4A0FC82A0051F" overflow="visible">
            <path d="M 0 0m 1.364 1.419 c 0 0.26399994 0.055000067 0.627 0.16500008 1.078 h 0.53900003 c 0.7149999 0 1.2649999 0.08800006 1.661 0.25300002 c 0.36299992 0.15400004 0.605 0.37400007 0.72599983 0.6489999 c 0.07700014 0.18700004 0.11000013 0.36300015 0.11000013 0.50600004 c 0 0.6049998 -0.572 0.957 -1.188 0.957 c -0.42900014 0 -0.85800004 -0.11000013 -1.2870002 -0.32999992 c -0.8469999 -0.44000006 -1.5839999 -1.441 -1.5839999 -2.651 c 0 -1.122 0.649 -2.002 1.7379999 -2.002 c 0.58299994 0 1.0999999 0.143 1.5510001 0.41799998 c 0.37400007 0.231 0.6489997 0.462 0.8249998 0.693 c 0.07700014 0.09899998 0.11000013 0.176 0.11000013 0.20899999 c 0 0.12099993 -0.05499983 0.18700004 -0.17600012 0.18700004 c -0.05499983 0 -0.11000013 -0.04400003 -0.17600012 -0.13200009 c -0.36299992 -0.48399997 -0.8139999 -0.79199994 -1.3309999 -0.92399997 c -0.34099984 -0.087999985 -0.59399986 -0.13199998 -0.7809999 -0.13199998 c -0.6270001 0 -0.90200007 0.594 -0.90200007 1.2210001 Z m 2.7610002 2.486 c 0 -0.7260001 -0.704 -1.089 -2.123 -1.089 h -0.3850001 c 0.20899999 0.7260001 0.5170001 1.21 0.93500006 1.441 c 0.32999992 0.1869998 0.605 0.28599977 0.82500005 0.28599977 c 0.3959999 0 0.7479999 -0.24199963 0.7479999 -0.6379998 Z "/>
        </symbol>
        <symbol id="g293C2D96009CA7436726DF2682208263" overflow="visible">
            <path d="M 0 0m 5.764 4.741 h -3.6299999 c -0.4510001 0 -0.8470001 -0.17600012 -1.1660001 -0.5170002 c -0.15399998 -0.16499996 -0.671 -0.86899996 -0.671 -1.0120001 c 0.044 -0.0769999 0.044 -0.14299989 0.176 -0.14299989 c 0.07700002 0 0.143 0.04399991 0.20899999 0.14299989 c 0.35200006 0.53900003 0.80300003 0.8140001 1.342 0.8140001 h 0.5610001 c -0.25300002 -0.957 -0.71500003 -2.134 -1.375 -3.5310001 c -0.055000067 -0.132 -0.08800006 -0.231 -0.08800006 -0.286 c 0 -0.22 0.12100005 -0.32999998 0.352 -0.32999998 c 0.20899999 0 0.36300004 0.121 0.462 0.352 c 0.19800007 0.627 0.34099996 1.1110001 0.4180001 1.441 l 0.6049998 2.354 h 1.1330001 c -0.29699993 -1.309 -0.45099998 -2.2220001 -0.45099998 -2.739 c 0 -0.5389999 0.12100005 -1.408 0.5280001 -1.408 c 0.23099995 0 0.48399973 0.22 0.48399973 0.45099998 c 0 0.055000007 -0.021999836 0.143 -0.065999985 0.25300002 c -0.20900011 0.517 -0.3080001 1.0999999 -0.3080001 1.7710001 c 0 0.51699996 0.065999985 1.0779998 0.18700027 1.6719999 h 1.1989999 c 0.38500023 0 0.572 0.13199997 0.572 0.40700006 c 0 0.25299978 -0.19799995 0.3080001 -0.47300005 0.3080001 Z "/>
        </symbol>
        <symbol id="g584B0F370842A356700A11AD73C4E2E5" overflow="visible">
            <path d="M 0 0m 0.9163 3.2648 c 0.24639994 0 0.43119997 0.18479991 0.43119997 0.43120003 c 0 0.27719998 -0.14629996 0.42350006 -0.43119997 0.43120003 c 0.16940004 0.36189985 0.5544 0.6545 1.0548999 0.6545 c 0.6775999 0 1.1242001 -0.50820017 1.1242001 -1.1858001 c 0 -0.36960006 -0.13090014 -0.7238002 -0.40040016 -1.0703001 c -0.1308999 -0.17709994 -0.23099995 -0.30029988 -0.30029988 -0.36960006 l -1.8249 -1.8094999 c -0.10010001 -0.092400014 -0.08470002 -0.1155 -0.08470002 -0.3465 h 3.1724 l 0.23869991 1.4476 h -0.32340002 c -0.053900003 -0.4081 -0.11549997 -0.64680004 -0.18479991 -0.7007 c -0.03850007 -0.023100019 -0.27719998 -0.03850001 -0.7314999 -0.03850001 h -1.3090001 c 0.5159 0.45429993 0.9933001 0.86239994 1.4476 1.2243 c 0.34649992 0.2694999 0.59290004 0.50820005 0.7469001 0.71609986 c 0.23099995 0.30030012 0.34649992 0.6160002 0.34649992 0.94710016 c 0 0.47739983 -0.18479991 0.8547001 -0.56209993 1.1318998 c -0.3311 0.25409985 -0.7469001 0.38500023 -1.2397001 0.38500023 c -0.42349994 0 -0.7853999 -0.12319994 -1.1011 -0.3696003 c -0.3311 -0.26949978 -0.50049996 -0.60829973 -0.50049996 -1.0240998 c 0 -0.26180005 0.19250003 -0.45429993 0.4312 -0.45429993 Z "/>
        </symbol>
        <symbol id="gAEBF7686F00B20CFC7D43C5EA9E9C44F" overflow="visible">
            <path d="M 0 0m 7.2269998 4.862 c -0.671 0 -1.2539997 -0.32999992 -1.7489996 -0.9790001 c -0.09899998 0.64900017 -0.5170002 0.9790001 -1.2650003 0.9790001 c -0.6489999 0 -1.2099998 -0.28599977 -1.6719999 -0.86899996 c -0.08799982 0.48399973 -0.4729998 0.86899996 -1.0339999 0.86899996 c -0.45099998 0 -0.78099996 -0.36299992 -1.012 -1.0780001 c -0.12099999 -0.352 -0.176 -0.5609999 -0.176 -0.62699986 c 0 -0.09899998 0.055000007 -0.15400004 0.176 -0.15400004 c 0.055000007 0 0.088 0.010999918 0.12099999 0.032999992 c 0.055000007 0.09899998 0.088 0.17599988 0.110000014 0.25300002 c 0.19800001 0.83599997 0.45100003 1.2539997 0.74799997 1.2539997 c 0.19799995 0 0.29700005 -0.1539998 0.29700005 -0.4619999 c 0 -0.14299989 -0.055000067 -0.43999982 -0.176 -0.8909998 l -0.62700003 -2.497 c -0.04399997 -0.13200003 -0.09899998 -0.418 -0.09899998 -0.48400003 c 0 -0.22 0.12099999 -0.32999998 0.35199994 -0.32999998 c 0.22000003 0 0.37400007 0.11 0.45099998 0.32999998 c 0.011000037 0.055000007 0.08800006 0.32999998 0.20900011 0.803 l 0.23099995 0.979 l 0.32999992 1.254 c 0.12100005 0.25300002 0.3080001 0.50600004 0.5500002 0.77 c 0.31899977 0.35200024 0.7149999 0.5279999 1.1879997 0.5279999 c 0.36299992 0 0.53900003 -0.24199963 0.53900003 -0.7149997 c 0 -0.14300013 -0.05499983 -0.44000006 -0.16499996 -0.89100003 l -0.29699993 -1.2540001 c -0.07700014 -0.319 -0.25299978 -0.979 -0.34100008 -1.331 c -0.010999918 -0.07699999 -0.021999836 -0.12099999 -0.021999836 -0.143 c 0 -0.22 0.12099981 -0.32999998 0.36299992 -0.32999998 c 0.12099981 0 0.20900011 0.033 0.28599977 0.11 c 0.16500044 0.16499999 0.17600012 0.24200001 0.2420001 0.539 l 0.64900017 2.6069999 c 0.032999992 0.14299989 0.1869998 0.3959999 0.45099974 0.7479999 c 0.3300004 0.44000006 0.77 0.65999985 1.309 0.65999985 c 0.3630004 0 0.53900003 -0.24199963 0.53900003 -0.7149997 c 0 -0.42900014 -0.21999979 -1.2320001 -0.671 -2.409 c -0.09899998 -0.25300002 -0.14299965 -0.462 -0.14299965 -0.605 c 0 -0.53900003 0.4069996 -0.935 0.93499994 -0.935 c 0.4949999 0 0.8689995 0.275 1.144 0.825 c 0.22000027 0.44000006 0.32999992 0.737 0.32999992 0.88 c 0 0.09899998 -0.055000305 0.15400004 -0.17599964 0.15400004 c -0.07700062 -0.011000037 -0.15400028 -0.110000014 -0.20900059 -0.23100007 c -0.24199963 -0.86899996 -0.59399986 -1.309 -1.0669999 -1.309 c -0.14300013 0 -0.21999979 0.11 -0.21999979 0.319 c 0 0.16499996 0.065999985 0.407 0.19799995 0.74799997 c 0.4510002 1.1769999 0.6709995 1.9799999 0.6709995 2.3979998 c 0 0.7809999 -0.51699924 1.1990001 -1.2979999 1.1990001 Z "/>
        </symbol>
        <symbol id="gA37D944EE46D6D738F17A6506485E6D7" overflow="visible">
            <path d="M 0 0m 2.3331 5.1128 c -0.3311 -0.32340002 -0.8239001 -0.48510027 -1.4938002 -0.48510027 v -0.33879995 c 0.4543 0 0.81619996 0.069300175 1.0934 0.20020008 v -3.8346 c 0 -0.10010004 -0.0077000856 -0.16170001 -0.030800104 -0.1925 c -0.03849995 -0.08470002 -0.2694999 -0.13090003 -0.69299996 -0.13090003 h -0.3157 v -0.3311 l 1.3706 0.0308 l 1.3783002 -0.0308 v 0.3311 h -0.31570005 c -0.42350006 0 -0.6545 0.046200007 -0.70070004 0.13090003 c -0.015399933 0.030799985 -0.0230999 0.092399955 -0.0230999 0.1925 v 4.2118998 c 0 0.20790005 -0.030800104 0.24640036 -0.26950002 0.24640036 Z "/>
        </symbol>
        <symbol id="gCB84B0639382626A1305E08391B56DBF" overflow="visible">
            <path d="M 0 0m 2.189 7.216 c 0 -0.11000013 0.12100005 -0.16499996 0.352 -0.16499996 c 0.44000006 0 0.6600001 -0.04400015 0.6600001 -0.14300013 c 0 -0.032999992 -0.022000074 -0.11000013 -0.055000067 -0.25300026 l -1.43 -5.753 c -0.065999985 -0.24200004 -0.176 -0.385 -0.32999992 -0.44 c -0.07700002 -0.022000015 -0.2750001 -0.033000022 -0.61600006 -0.033000022 c -0.24199998 0 -0.352 -0.021999985 -0.352 -0.253 c 0 -0.121 0.066000015 -0.176 0.20899999 -0.176 l 1.43 0.033 l 1.628 -0.033 c 0.17600012 0 0.26399994 0.088 0.26399994 0.253 c 0 0.187 -0.12099981 0.176 -0.40699983 0.176 c -0.48399997 0 -0.75900006 0.022000015 -0.82500005 0.07699999 c -0.032999992 0.011000037 -0.04399991 0.055000007 -0.04399991 0.110000014 l 0.704 2.915 h 1.023 c 0.50600004 0 0.8579998 -0.021999836 0.8579998 -0.43999982 c 0 -0.14300013 -0.021999836 -0.319 -0.07700014 -0.5280001 c -0.01099968 -0.032999992 -0.021999836 -0.0769999 -0.032999992 -0.12100005 c 0 -0.12099981 0.055000305 -0.17599988 0.17600012 -0.17599988 c 0.055000305 0.010999918 0.13199997 0.08800006 0.20900011 0.25300002 l 0.59399986 2.3649998 c 0.022000313 0.0880003 0.032999992 0.15400028 0.032999992 0.18700027 c -0.032999992 0.09899998 -0.09899998 0.1539998 -0.17599964 0.1539998 c -0.0880003 0 -0.15400028 -0.08799982 -0.19800043 -0.25299978 c -0.10999966 -0.41800022 -0.26399994 -0.68200016 -0.43999958 -0.8140001 c -0.17600012 -0.13199997 -0.4840002 -0.19799995 -0.92400026 -0.19799995 h -0.93499994 l 0.68200016 2.7059999 c 0.08799982 0.37400007 0.08799982 0.38500023 0.5499997 0.38500023 h 1.4300003 c 1.0669999 0 1.5509996 -0.16499996 1.5509996 -1.144 c 0 -0.22000027 -0.01099968 -0.41800022 -0.032999992 -0.5830002 c -0.01099968 -0.12099981 -0.021999836 -0.1869998 -0.021999836 -0.19799995 c 0 -0.12099981 0.05499983 -0.17600012 0.16499996 -0.17600012 c 0.11000013 0 0.17600012 0.09899998 0.19800043 0.3080001 l 0.21999931 1.881 c 0.032999992 0.3080001 -0.043999672 0.34100008 -0.3409996 0.34100008 h -5.3240004 c -0.25300002 0 -0.37400007 -0.011000156 -0.37400007 -0.26399994 Z "/>
        </symbol>
        <symbol id="g4BA1FCBFDAC4BA99FE2255AD6CF5831E" overflow="visible">
            <path d="M 0 0m 4.0271 4.2273 c -0.20020008 0 -0.3311 -0.07700014 -0.3927002 -0.23870015 l -1.3167 -3.2494001 h 0.35420012 l 1.7324998 2.8259 c 0.03850031 0.06929994 0.06160021 0.14630008 0.06160021 0.23099995 c 0 0.23100019 -0.20790005 0.43120027 -0.4389 0.43120027 Z m -1.8172002 0 c -0.20019984 0 -0.33109987 -0.07700014 -0.39269996 -0.23870015 l -1.3167 -3.2494001 h 0.35419995 l 1.7248 2.8259 c 0.046200037 0.06929994 0.06929994 0.14630008 0.06929994 0.23099995 c 0 0.23100019 -0.20789981 0.43120027 -0.4389 0.43120027 Z "/>
        </symbol>
        <symbol id="g6D95EB440369500A57EF39BB7350EBFC" overflow="visible">
            <path d="M 0 0m 5.148 4.741 h -3.0359998 c -0.58299994 0 -1.111 -0.37400007 -1.595 -1.1110003 c -0.143 -0.21999979 -0.22000003 -0.36299992 -0.22000003 -0.41799998 c 0.032999992 -0.08799982 0.044 -0.14299989 0.176 -0.14299989 c 0.07700002 0 0.143 0.04399991 0.20899999 0.14299989 c 0.35200006 0.53900003 0.792 0.8140001 1.3310001 0.8140001 h 0.8469999 l -1.045 -3.41 c -0.0769999 -0.24199998 -0.109999895 -0.385 -0.109999895 -0.41799998 c 0 -0.22 0.12099993 -0.32999998 0.35199988 -0.32999998 c 0.12100005 0 0.23100019 0.033 0.29700017 0.099 c 0.14299989 0.132 0.1539998 0.16499999 0.19799995 0.396 l 0.7149999 3.663 h 1.7819998 c 0.38500023 0 0.572 0.13199997 0.572 0.40700006 c 0 0.25299978 -0.19799995 0.3080001 -0.47300005 0.3080001 Z "/>
        </symbol>
    </defs>
    <defs id="tilings">
        <pattern id="t93A20E0C741343932DA0B73A17338770" width="12" height="12" patternUnits="userSpaceOnUse" viewBox="0 0 12.000 12.000">
            <g>
                <path class="typst-shape" fill="none" stroke="#0065bd" stroke-width="2.5" stroke-linecap="butt" stroke-linejoin="miter" stroke-miterlimit="4" transform="matrix(1 0 0 1 0 12)" d="M 0 0l 12 -12 "/>
                <path class="typst-shape" fill="none" stroke="#0065bd" stroke-width="2.5" stroke-linecap="butt" stroke-linejoin="miter" stroke-miterlimit="4" transform="matrix(1 0 0 1 12 12)" d="M 0 0l -0.9 -0.9 "/>
                <path class="typst-shape" fill="none" stroke="#0065bd" stroke-width="2.5" stroke-linecap="butt" stroke-linejoin="miter" stroke-miterlimit="4" d="M 0 0l 0.9 0.9 "/>
            </g>
        </pattern>
    </defs>
    <defs id="tilings-refs">
        <pattern patternTransform="matrix(1 0 0 1 0 0)" id="pAAB50FF8EB52344855BB1D98541890EC" href="#t93A20E0C741343932DA0B73A17338770" xlink:href="#t93A20E0C741343932DA0B73A17338770"/>
    </defs>
</svg>

The left side expresses the data of
`#!rzk is-cocartesian-arrow B (f 0₂) (f 1₂) f P e (F 1₂) (\ t → F t)` and the
right shows that of
`#!rzk is-dependent-initial temp-96cf-G temp-96cf-Q (f , e) F`. The blue area
corresponds to the type that is required to be contractible while the black
parts correspond to the inputs of the function types.

What we're about to show now, is that the triangle is "effectively" equivalent
to the square. It's not truly equivalent, since the inputs are different and
they thus don't live over the same base. However, that's what the
`#!rzk equiv-family-of-props` lemma takes care of: with different bases we need
translation functions $\alpha_1: A \to A'$ and $\alpha_2: A' \to A$ that allow
transforming the triangle to the square and vice versa.

Before giving those functions, we record two auxiliary lemmas.

```rzk
#def temp-96cf-equiv-cocartesian-arrow
  : Equiv
    ( is-cocartesian-arrow B (f 0₂) (f 1₂) f P e (F 1₂) (\ t → F t))
    ( ( a : temp-96cf-A) → is-contr (temp-96cf-R a))
  :=
  equiv-has-inverse
  ( is-cocartesian-arrow B (f 0₂) (f 1₂) f P e (F 1₂) (\ t → F t))
  ( ( a : temp-96cf-A) → is-contr (temp-96cf-R a))
  ( \ is-cocartesian-arrow-F (b'' , (g , (h , (τ , (e'' , F'))))) →
    is-cocartesian-arrow-F b'' g h τ e'' (\ t → F' t))
  ( \ a-is-contr-R-a b'' v w sigma e'' h → a-is-contr-R-a (b'' , (v , (w , (sigma , (e'' , h))))))
  ( \ _ → refl)
  ( \ _ → refl)

#def temp-96cf-equiv-dependent-initial uses (P B)
  : Equiv
    ( ( a' : temp-96cf-A') → is-contr (temp-96cf-R' a'))
    ( is-dependent-initial temp-96cf-G temp-96cf-Q (f , e) F)
  :=
  equiv-has-inverse
  ( ( a' : temp-96cf-A') → is-contr (temp-96cf-R' a'))
  ( is-dependent-initial temp-96cf-G temp-96cf-Q (f , e) F)
  ( \ a'-is-contr-R'-a' (f' , e') F' m → a'-is-contr-R'-a' (f' , (e' , (m , F'))))
  ( \ is-dependent-initial-F (f' , (e' , (m , F'))) →
    is-dependent-initial-F (f' , e') F' m)
  ( \ _ → refl)
  ( \ _ → refl)
```

Now we can show that the two transformation functions satisfy the required
property of lifting to the triangle and square. These proofs are very elaborate
and technical.

```rzk
#def temp-96cf-is-contr-R-a-is-contr-R'-alpha₁-a
  ( ( b'' , (g , (h , (τ , (e'' , F'))))) : temp-96cf-A)
  : is-contr (temp-96cf-R' (temp-96cf-alpha₁ (b'' , (g , (h , (τ , (e'' , F')))))))
    → is-contr (temp-96cf-R (b'' , (g , (h , (τ , (e'' , F'))))))
  :=
  is-contr-equiv-is-contr
  ( temp-96cf-R' (temp-96cf-alpha₁ (b'' , (g , (h , (τ , (e'' , F')))))))
  ( temp-96cf-R (b'' , (g , (h , (τ , (e'' , F'))))))
  ( equiv-comp
    ( temp-96cf-R' (temp-96cf-alpha₁ (b'' , (g , (h , (τ , (e'' , F')))))))
    ( Σ ( G : dhom B (f 1₂) b'' g P (F 1₂) e'')
      , dependent-square B (f 0₂) (f 1₂) (f 0₂) b''
        ( f) (id-hom B (f 0₂)) h g
        ( \ (t , s) → recOR(Δ² (t , s) ↦ τ (t , s) , t ≤ s ↦ h t))
        ( P) e (F 1₂) e e''
        ( \ t → F t) (id-dhom B (f 0₂) P e) F' G)
    ( temp-96cf-R (b'' , (g , (h , (τ , (e'' , F'))))))
    ( equiv-has-inverse
      ( temp-96cf-R' (temp-96cf-alpha₁ (b'' , (g , (h , (τ , (e'' , F')))))))
      ( Σ ( G : dhom B (f 1₂) b'' g P (F 1₂) e'')
        , dependent-square B (f 0₂) (f 1₂) (f 0₂) b''
          ( f) (id-hom B (f 0₂)) h g
          ( \ (t , s) → recOR(Δ² (t , s) ↦ τ (t , s) , t ≤ s ↦ h t))
          ( P) e (F 1₂) e e''
          ( \ t → F t) (id-dhom B (f 0₂) P e) F' G)
      ( \ M → (\ t → M t 1₂ , \ (t , s) → M s t))
      ( \ (G , σ) t s → σ (s , t))
      ( \ _ → refl)
      ( \ _ → refl))
    ( total-equiv-family-of-equiv
      ( dhom B (f 1₂) b'' g P (F 1₂) e'')
      ( \ G →
        dependent-square B (f 0₂) (f 1₂) (f 0₂) b''
        ( f) (id-hom B (f 0₂)) h g
        ( \ (t , s) → recOR(Δ² (t , s) ↦ τ (t , s) , t ≤ s ↦ h t))
        ( P) e (F 1₂) e e''
        ( \ t → F t) (id-dhom B (f 0₂) P e) F' G)
      ( \ G → dhom2 B (f 0₂) (f 1₂) b'' f g h τ P e (F 1₂) e'' (\ t → F t) G F')
      ( equiv-dependent-square-left-id-dhom2-is-inner-family B
        ( f 0₂) (f 1₂) b''
        ( f) h g
        ( τ)
        ( P) is-inner-family-P
        ( e) (F 1₂) e''
        ( \ t → F t) F')))

#def temp-96cf-is-contr-R'-a'-is-contr-R-alpha₂-a'
  ( ( f' , (e' , (m , F'))) : temp-96cf-A')
  : is-contr (temp-96cf-R (temp-96cf-alpha₂ (f' , (e' , (m , F')))))
    → is-contr (temp-96cf-R' (f' , (e' , (m , F'))))
  :=
  is-contr-equiv-is-contr'
  ( temp-96cf-R' (f' , (e' , (m , F'))))
  ( temp-96cf-R (temp-96cf-alpha₂ (f' , (e' , (m , F')))))
  ( equiv-quadruple-comp
    ( temp-96cf-R' (f' , (e' , (m , F'))))
    ( Σ ( G : dhom B (f 1₂) (f' 1₂) (\ t → first (m t) 1₂) P (F 1₂) (F' 1₂))
      , dependent-square B (f 0₂) (f 1₂) (f' 0₂) (f' 1₂)
        ( f) (\ t → first (m t) 0₂) f' (\ t → first (m t) 1₂)
        ( \ (t , s) → first (m s) t)
        ( P) e (F 1₂) e' (F' 1₂)
        ( \ t → F t) (\ t → second (m t)) (\ t → F' t) G)
    ( Σ ( G : dhom B (f 1₂) (f' 1₂) (\ t → first (m t) 1₂) P (F 1₂) (F' 1₂))
      , Σ ( D : dhom B (f 0₂) (f' 1₂) (\ t → first (m t) t) P e (F' 1₂))
        , product
          ( dhom2 B (f 0₂) (f 1₂) (f' 1₂)
            ( f) (\ t → first (m t) 1₂) (\ t → first (m t) t)
            ( \ (t , s) → first (m s) t)
            ( P) e (F 1₂) (F' 1₂)
            ( \ t → F t) G D)
          ( dhom2 B (f 0₂) (f' 0₂) (f' 1₂)
            ( \ t → first (m t) 0₂) (f') (\ t → first (m t) t)
            ( \ (t , s) → first (m t) s)
            ( P) e (F' 0₂) (F' 1₂)
            ( \ t → second (m t)) (\ t → F' t) D))
    ( Σ ( G : dhom B (f 1₂) (f' 1₂) (\ t → first (m t) 1₂) P (F 1₂) (F' 1₂))
      , Σ ( Dτ : Σ (D : dhom B (f 0₂) (f' 1₂) (\ t → first (m t) t) P e (F' 1₂))
                , dhom2 B (f 0₂) (f' 0₂) (f' 1₂)
                  ( \ t → first (m t) 0₂) (f') (\ t → first (m t) t)
                  ( \ (t , s) → first (m t) s)
                  ( P) e (F' 0₂) (F' 1₂)
                  ( \ t → second (m t)) (\ t → F' t) D)
        , dhom2 B (f 0₂) (f 1₂) (f' 1₂)
          ( f) (\ t → first (m t) 1₂) (\ t → first (m t) t)
          ( \ (t , s) → first (m s) t)
          ( P) e (F 1₂) (F' 1₂)
          ( \ t → F t) G (first Dτ))
    ( temp-96cf-R (temp-96cf-alpha₂ (f' , (e' , (m , F')))))
    ( equiv-has-inverse
      ( temp-96cf-R' (f' , (e' , (m , F'))))
      ( Σ ( G : dhom B (f 1₂) (f' 1₂) (\ t → first (m t) 1₂) P (F 1₂) (F' 1₂))
        , dependent-square B (f 0₂) (f 1₂) (f' 0₂) (f' 1₂)
          ( f) (\ t → first (m t) 0₂) f' (\ t → first (m t) 1₂)
          ( \ (t , s) → first (m s) t)
          ( P) e (F 1₂) e' (F' 1₂)
          ( \ t → F t) (\ t → second (m t)) (\ t → F' t) G)
      ( \ M → (\ t → M t 1₂ , \ (t , s) → M s t))
      ( \ (G , σ) t s → σ (s , t))
      ( \ _ → refl)
      ( \ _ → refl))
    ( total-equiv-family-of-equiv
      ( dhom B (f 1₂) (f' 1₂) (\ t → first (m t) 1₂) P (F 1₂) (F' 1₂))
      ( \ G →
        dependent-square B (f 0₂) (f 1₂) (f' 0₂) (f' 1₂)
        ( f) (\ t → first (m t) 0₂) f' (\ t → first (m t) 1₂)
        ( \ (t , s) → first (m s) t)
        ( P) e (F 1₂) e' (F' 1₂)
        ( \ t → F t) (\ t → second (m t)) (\ t → F' t) G)
      ( \ G →
        Σ ( D : dhom B (f 0₂) (f' 1₂) (\ t → first (m t) t) P e (F' 1₂))
        , product
          ( dhom2 B (f 0₂) (f 1₂) (f' 1₂)
            ( f) (\ t → first (m t) 1₂) (\ t → first (m t) t)
            ( \ (t , s) → first (m s) t)
            ( P) e (F 1₂) (F' 1₂)
            ( \ t → F t) G D)
          ( dhom2 B (f 0₂) (f' 0₂) (f' 1₂)
            ( \ t → first (m t) 0₂) (f') (\ t → first (m t) t)
            ( \ (t , s) → first (m t) s)
            ( P) e (F' 0₂) (F' 1₂)
            ( \ t → second (m t)) (\ t → F' t) D))
      ( equiv-dependent-square-glued-dhom2 B (f 0₂) (f 1₂) (f' 0₂) (f' 1₂)
        ( f) (\ t → first (m t) 0₂) f' (\ t → first (m t) 1₂)
        ( \ (t , s) → first (m s) t)
        ( P) e (F 1₂) e' (F' 1₂)
        ( \ t → F t) (\ t → second (m t)) (\ t → F' t)))
    ( equiv-has-inverse
      ( Σ ( G : dhom B (f 1₂) (f' 1₂) (\ t → first (m t) 1₂) P (F 1₂) (F' 1₂))
        , Σ ( D : dhom B (f 0₂) (f' 1₂) (\ t → first (m t) t) P e (F' 1₂))
          , product
            ( dhom2 B (f 0₂) (f 1₂) (f' 1₂)
              ( f) (\ t → first (m t) 1₂) (\ t → first (m t) t)
              ( \ (t , s) → first (m s) t)
              ( P) e (F 1₂) (F' 1₂)
              ( \ t → F t) G D)
            ( dhom2 B (f 0₂) (f' 0₂) (f' 1₂)
              ( \ t → first (m t) 0₂) (f') (\ t → first (m t) t)
              ( \ (t , s) → first (m t) s)
              ( P) e (F' 0₂) (F' 1₂)
              ( \ t → second (m t)) (\ t → F' t) D))
      ( Σ ( G : dhom B (f 1₂) (f' 1₂) (\ t → first (m t) 1₂) P (F 1₂) (F' 1₂))
        , Σ ( Dτ : Σ (D : dhom B (f 0₂) (f' 1₂) (\ t → first (m t) t) P e (F' 1₂))
                  , dhom2 B (f 0₂) (f' 0₂) (f' 1₂)
                    ( \ t → first (m t) 0₂) (f') (\ t → first (m t) t)
                    ( \ (t , s) → first (m t) s)
                    ( P) e (F' 0₂) (F' 1₂)
                    ( \ t → second (m t)) (\ t → F' t) D)
          , dhom2 B (f 0₂) (f 1₂) (f' 1₂)
            ( f) (\ t → first (m t) 1₂) (\ t → first (m t) t)
            ( \ (t , s) → first (m s) t)
            ( P) e (F 1₂) (F' 1₂)
            ( \ t → F t) G (first Dτ))
      ( \ (G , (D , (τ' , τ))) → (G , ((D , τ) , τ')))
      ( \ (G , ((D , τ) , τ')) → (G , (D , (τ' , τ))))
      ( \ _ → refl)
      ( \ _ → refl))
    ( total-equiv-family-of-equiv
      ( dhom B (f 1₂) (f' 1₂) (\ t → first (m t) 1₂) P (F 1₂) (F' 1₂))
      ( \ G →
        Σ ( Dτ : Σ (D : dhom B (f 0₂) (f' 1₂) (\ t → first (m t) t) P e (F' 1₂))
                , dhom2 B (f 0₂) (f' 0₂) (f' 1₂)
                  ( \ t → first (m t) 0₂) (f') (\ t → first (m t) t)
                  ( \ (t , s) → first (m t) s)
                  ( P) e (F' 0₂) (F' 1₂)
                  ( \ t → second (m t)) (\ t → F' t) D)
        , dhom2 B (f 0₂) (f 1₂) (f' 1₂)
          ( f) (\ t → first (m t) 1₂) (\ t → first (m t) t)
          ( \ (t , s) → first (m s) t)
          ( P) e (F 1₂) (F' 1₂)
          ( \ t → F t) G (first Dτ))
      ( \ G →
        dhom2 B (f 0₂) (f 1₂) (f' 1₂)
        ( f) (\ t → first (m t) 1₂) (\ t → first (m t) t)
        ( \ (t , s) → first (m s) t)
        ( P) e (F 1₂) (F' 1₂)
        ( \ t → F t) G (temp-96cf-A'-diag (f' , (e' , (m , F')))))
      ( \ G →
        transport-equiv-center-fiber-total-type-is-contr-base
        ( Σ ( D : dhom B (f 0₂) (f' 1₂) (\ t → first (m t) t) P e (F' 1₂))
          , dhom2 B (f 0₂) (f' 0₂) (f' 1₂)
            ( \ t → first (m t) 0₂) (f') (\ t → first (m t) t)
            ( \ (t , s) → first (m t) s)
            ( P) e (F' 0₂) (F' 1₂)
            ( \ t → second (m t)) (\ t → F' t) D)
        ( is-contr-equiv-is-contr'
          ( Σ ( D : dhom B (f 0₂) (f' 1₂) (\ t → first (m t) t) P e (F' 1₂))
            , dhom2 B (f 0₂) (f' 0₂) (f' 1₂)
              ( \ t → first (m t) 0₂) (f') (\ t → first (m t) t)
              ( \ (t , s) → first (m t) s)
              ( P) e (F' 0₂) (F' 1₂)
              ( \ t → second (m t)) (\ t → F' t) D)
          ( ( ( t , s) : Δ²) → P (first (m t) s) [s ≡ 0₂ ↦ second (m t) , t ≡ 1₂ ↦ F' s])
          ( equiv-has-inverse
            ( Σ ( D : dhom B (f 0₂) (f' 1₂) (\ t → first (m t) t) P e (F' 1₂))
              , dhom2 B (f 0₂) (f' 0₂) (f' 1₂)
                ( \ t → first (m t) 0₂) (f') (\ t → first (m t) t)
                ( \ (t , s) → first (m t) s)
                ( P) e (F' 0₂) (F' 1₂)
                ( \ t → second (m t)) (\ t → F' t) D)
            ( ( ( t , s) : Δ²) → P (first (m t) s) [s ≡ 0₂ ↦ second (m t) , t ≡ 1₂ ↦ F' s])
            ( \ (D , τ) (t , s) → τ (t , s))
            ( \ τ → (\ t → τ (t , t) , \ (t , s) → τ (t , s)))
            ( \ _ → refl)
            ( \ _ → refl))
          ( is-inner-family-P
            ( \ (t , s) → first (m t) s)
            ( \ (t , s) → recOR(s ≡ 0₂ ↦ second (m t) , t ≡ 1₂ ↦ F' s))))
        ( \ Dτ →
          dhom2 B (f 0₂) (f 1₂) (f' 1₂)
          ( f) (\ t → first (m t) 1₂) (\ t → first (m t) t)
          ( \ (t , s) → first (m s) t)
          ( P) e (F 1₂) (F' 1₂)
          ( \ t → F t) G (first Dτ))
        ( temp-96cf-A'-diag (f' , (e' , (m , F')))
        , \ (t , s) → temp-96cf-A'-inner-filler (f' , (e' , (m , F'))) (t , s)))))
```

With those finished, we can finally apply the `#!rzk equiv-family-of-props`
lemma, which yields the desired equivalence.

```rzk
#def is-cocartesian-arrow-equiv-is-dependent-initial uses (is-inner-family-P)
  : Equiv
    ( is-cocartesian-arrow B (f 0₂) (f 1₂) f P e (F 1₂) (\ t → F t))
    ( is-dependent-initial temp-96cf-G temp-96cf-Q (f , e) F)
  :=
  equiv-triple-comp
  ( is-cocartesian-arrow B (f 0₂) (f 1₂) f P e (F 1₂) (\ t → F t))
  ( ( a : temp-96cf-A) → is-contr (temp-96cf-R a))
  ( ( a' : temp-96cf-A') → is-contr (temp-96cf-R' a'))
  ( is-dependent-initial temp-96cf-G temp-96cf-Q (f , e) F)
  ( temp-96cf-equiv-cocartesian-arrow)
  ( equiv-family-of-props funext
    ( temp-96cf-A)
    ( temp-96cf-A')
    ( \ a → is-contr (temp-96cf-R a))
    ( \ a → is-prop-is-contr-itself (weakfunext-funext funext) (temp-96cf-R a))
    ( \ a' → is-contr (temp-96cf-R' a'))
    ( \ a' → is-prop-is-contr-itself (weakfunext-funext funext) (temp-96cf-R' a'))
    ( temp-96cf-alpha₁)
    ( temp-96cf-is-contr-R-a-is-contr-R'-alpha₁-a)
    ( temp-96cf-alpha₂)
    ( temp-96cf-is-contr-R'-a'-is-contr-R-alpha₂-a'))
  ( temp-96cf-equiv-dependent-initial)

#def is-cocartesian-arrow-is-dependent-initial uses (is-inner-family-P funext)
  : is-cocartesian-arrow B (f 0₂) (f 1₂) f P e (F 1₂) (\ t → F t)
    → is-dependent-initial temp-96cf-G temp-96cf-Q (f , e) F
  := first is-cocartesian-arrow-equiv-is-dependent-initial

#def is-dependent-initial-is-cocartesian-arrow uses (is-inner-family-P funext)
  : is-dependent-initial temp-96cf-G temp-96cf-Q (f , e) F
    → is-cocartesian-arrow B (f 0₂) (f 1₂) f P e (F 1₂) (\ t → F t)
  :=
  first
  ( inv-equiv
    ( is-cocartesian-arrow B (f 0₂) (f 1₂) f P e (F 1₂) (\ t → F t))
    ( is-dependent-initial temp-96cf-G temp-96cf-Q (f , e) F)
    ( is-cocartesian-arrow-equiv-is-dependent-initial))

#end is-cocartesian-arrow-equiv-is-dependent-initial
```

Using this equivalence, we can now show the equivalence between
`#!rzk is-naive-cocartesian-family` and `#!rzk is-cocartesian-family`.
Justifying our previous work of LARI families.

```rzk
#def is-cocartesian-family-equiv-has-cocartesian-lifts-is-inner-family
  ( B : U)
  ( P : B → U)
  ( is-inner-family-P : is-inner-family B P)
  : Equiv (is-cocartesian-family B P) (is-naive-cocartesian-family B P)
  :=
  equiv-quadruple-comp
  ( is-cocartesian-family B P)
  ( ( ( g , f₀) : temp-96cf-G B P)
    → Σ ( f : LARI-family-codomain 2 Δ¹ (\ t → t ≡ 0₂) B P (g , \ t → f₀))
      , is-dependent-initial
        ( LARI-family-domain 2 Δ¹ (\ t → t ≡ 0₂) B P)
        ( LARI-family-codomain 2 Δ¹ (\ t → t ≡ 0₂) B P)
        ( g , \ t → f₀)
        ( f))
  ( ( ( f , e) : temp-96cf-G B P)
    → Σ ( e' : P (f 1₂))
      , Σ ( F : dhom B (f 0₂) (f 1₂) f P e e')
        , is-cocartesian-arrow B (f 0₂) (f 1₂) (\ t → f t) P e e' F)
  ( has-cocartesian-lifts B P)
  ( is-naive-cocartesian-family B P)
  ( equiv-has-inverse
    ( is-cocartesian-family B P)
    ( ( ( g , f₀) : temp-96cf-G B P)
      → Σ ( f : LARI-family-codomain 2 Δ¹ (\ t → t ≡ 0₂) B P (g , \ t → f₀))
        , is-dependent-initial
          ( LARI-family-domain 2 Δ¹ (\ t → t ≡ 0₂) B P)
          ( LARI-family-codomain 2 Δ¹ (\ t → t ≡ 0₂) B P)
          ( g , \ t → f₀)
          ( f))
    ( \ is-cocartesian-family-P (g , f₀) → is-cocartesian-family-P g (\ t → f₀))
    ( \ is-cocartesian-family-P' g f₀ → is-cocartesian-family-P' (g , f₀ 0₂))
    ( \ _ → refl)
    ( \ _ → refl))
  ( equiv-function-equiv-family funext
    ( temp-96cf-G B P)
    ( \ (g , f₀) →
      Σ ( f : LARI-family-codomain 2 Δ¹ (\ t → t ≡ 0₂) B P (g , \ t → f₀))
      , is-dependent-initial
        ( LARI-family-domain 2 Δ¹ (\ t → t ≡ 0₂) B P)
        ( LARI-family-codomain 2 Δ¹ (\ t → t ≡ 0₂) B P)
        ( g , \ t → f₀)
        ( f))
    ( \ (f , e) →
      Σ ( e' : P (f 1₂))
      , Σ ( F : dhom B (f 0₂) (f 1₂) f P e e')
        , is-cocartesian-arrow B (f 0₂) (f 1₂) (\ t → f t) P e e' F)
    ( \ (f , e) →
      equiv-comp
      ( Σ ( F : LARI-family-codomain 2 Δ¹ (\ t → t ≡ 0₂) B P (f , \ t → e))
        , is-dependent-initial
          ( LARI-family-domain 2 Δ¹ (\ t → t ≡ 0₂) B P)
          ( LARI-family-codomain 2 Δ¹ (\ t → t ≡ 0₂) B P)
          ( f , \ t → e)
          ( F))
      ( Σ ( F : LARI-family-codomain 2 Δ¹ (\ t → t ≡ 0₂) B P (f , \ t → e))
        , is-cocartesian-arrow B (f 0₂) (f 1₂) (\ t → f t) P e (F 1₂) (\ t → F t))
      ( Σ ( e' : P (f 1₂))
        , Σ ( F : dhom B (f 0₂) (f 1₂) f P e e')
          , is-cocartesian-arrow B (f 0₂) (f 1₂) (\ t → f t) P e e' F)
      ( total-equiv-family-of-equiv
        ( LARI-family-codomain 2 Δ¹ (\ t → t ≡ 0₂) B P (f , \ t → e))
        ( is-dependent-initial
          ( LARI-family-domain 2 Δ¹ (\ t → t ≡ 0₂) B P)
          ( LARI-family-codomain 2 Δ¹ (\ t → t ≡ 0₂) B P)
          ( f , \ t → e))
        ( \ F → is-cocartesian-arrow B (f 0₂) (f 1₂) (\ t → f t) P e (F 1₂) (\ t → F t))
        ( \ F →
          equiv-comp
          ( is-dependent-initial
            ( LARI-family-domain 2 Δ¹ (\ t → t ≡ 0₂) B P)
            ( LARI-family-codomain 2 Δ¹ (\ t → t ≡ 0₂) B P)
            ( f , \ t → e)
            ( F))
          ( is-dependent-initial (temp-96cf-G B P) (temp-96cf-Q B P) (f , e) F)
          ( is-cocartesian-arrow B (f 0₂) (f 1₂) (\ t → f t) P e (F 1₂) (\ t → F t))
          ( equiv-has-inverse
            ( is-dependent-initial
              ( LARI-family-domain 2 Δ¹ (\ t → t ≡ 0₂) B P)
              ( LARI-family-codomain 2 Δ¹ (\ t → t ≡ 0₂) B P)
              ( f , \ t → e)
              ( F))
            ( is-dependent-initial (temp-96cf-G B P) (temp-96cf-Q B P) (f , e) F)
            ( \ is-dependent-initial-F (f' , e') F' m →
              is-dependent-initial-F (f' , \ _ → e') F'
              ( \ t → (first (m t) , \ _ → second (m t))))
            ( \ is-dependent-initial-F (f' , e') F' m →
              is-dependent-initial-F (f' , e' 0₂) F'
              ( \ t → (first (m t) , second (m t) 0₂)))
            ( \ _ → refl)
            ( \ _ → refl))
          ( inv-equiv
            ( is-cocartesian-arrow B (f 0₂) (f 1₂) (\ t → f t) P e (F 1₂) (\ t → F t))
            ( is-dependent-initial (temp-96cf-G B P) (temp-96cf-Q B P) (f , e) F)
            ( is-cocartesian-arrow-equiv-is-dependent-initial B P is-inner-family-P f e F))))
      ( equiv-has-inverse
        ( Σ ( F : LARI-family-codomain 2 Δ¹ (\ t → t ≡ 0₂) B P (f , \ t → e))
          , is-cocartesian-arrow B (f 0₂) (f 1₂) (\ t → f t) P e (F 1₂) (\ t → F t))
        ( Σ ( e' : P (f 1₂))
          , Σ ( F : dhom B (f 0₂) (f 1₂) (\ t → f t) P e e')
            , is-cocartesian-arrow B (f 0₂) (f 1₂) (\ t → f t) P e e' F)
        ( \ (F , prf) → (F 1₂ , (\ t → F t , prf)))
        ( \ (e' , (f , prf)) → (\ t → f t , prf))
        ( \ _ → refl)
        ( \ _ → refl))))
  ( equiv-has-inverse
    ( ( ( f , e) : temp-96cf-G B P)
      → Σ ( e' : P (f 1₂))
        , Σ ( F : dhom B (f 0₂) (f 1₂) (\ t → f t) P e e')
          , is-cocartesian-arrow B (f 0₂) (f 1₂) (\ t → f t) P e e' F)
    ( has-cocartesian-lifts B P)
    ( \ has-cocartesian-lifts-P' b b' u e → has-cocartesian-lifts-P' (u , e))
    ( \ has-cocartesian-lifts-P (f , e) →
      has-cocartesian-lifts-P (f 0₂) (f 1₂) (\ t → f t) e)
    ( \ _ → refl)
    ( \ _ → refl))
  ( equiv-has-inverse
    ( has-cocartesian-lifts B P)
    ( is-naive-cocartesian-family B P)
    ( \ lifts → (is-inner-family-P , lifts))
    ( \ (_ , lifts) → lifts)
    ( \ _ → refl)
    ( \ (is-inner , lifts) → path-product
      ( is-inner-family B P)
      ( has-cocartesian-lifts B P)
      ( is-inner-family-P) (is-inner)
      ( lifts) (lifts)
      ( all-elements-equal-is-prop
        ( is-inner-family B P)
        ( is-inner-family-is-prop funext B P)
        ( is-inner-family-P)
        ( is-inner))
      ( refl)))
```

## Closure Properties

We have now established that cocartesian families and LARI families are
equivalent and we can thus transfer our closure properties of LARI families to
cocartesian families.

```rzk
#def is-cocartesian-family-product-is-cocartesian-family
  ( I : U)
  ( B : I → U)
  ( P : (i : I) → (b : B i) → U)
  ( is-cocartesian-family-P : (i : I) → is-cocartesian-family (B i) (P i))
  : is-cocartesian-family (section I B) (\ b → ((i : I) → P i (b i)))
  :=
  is-LARI-family-product-is-LARI-family funext 2 Δ¹ (\ t → t ≡ 0₂) I B P
  ( is-cocartesian-family-P)

#def is-cocartesian-family-pullback-is-cocartesian-family
  ( A B : U)
  ( P : B → U)
  ( k : A → B)
  ( is-cocartesian-family-P : is-cocartesian-family B P)
  : is-cocartesian-family A (\ a → P (k a))
  :=
  is-LARI-family-pullback-is-LARI-family 2 Δ¹ (\ t → t ≡ 0₂) A B P k
  ( is-cocartesian-family-P)

#def is-cocartesian-family-comp-is-cocartesian-family
  ( B : U)
  ( P : B → U)
  ( is-cocartesian-family-P : is-cocartesian-family B P)
  ( R : (total-type B P) → U)
  ( is-cocartesian-family-R : is-cocartesian-family (total-type B P) R)
  : is-cocartesian-family B (type-family-comp B P R)
  :=
  is-LARI-family-comp-is-LARI-family extext 2 Δ¹ (\ t → t ≡ 0₂) B
  ( P) is-cocartesian-family-P
  ( R) is-cocartesian-family-R
```
