# 4. Equivalences involving extension types

These formalisations correspond to Section 3 of the RS17 paper.

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

## Prerequisites

- `hott/4-equivalences.rzk` — contains the definitions of `#!rzk Equiv` and
  `#!rzk comp-equiv`
- the file `hott/4-equivalences.rzk` relies in turn on the previous files in
  `hott/`

## Commutation of arguments and currying

```rzk title="RS17, Theorem 4.1"
#def flip-ext-fun
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( X : U)
  ( Y : ψ → X → U)
  ( f : (t : ϕ) → (x : X) → Y t x)
  : Equiv
      ( (t : ψ) → ((x : X) → Y t x) [ϕ t ↦ f t])
      ( (x : X) → (t : ψ) → Y t x [ϕ t ↦ f t x])
  :=
    ( \ g x t → g t x ,
      ( ( \ h t x → (h x) t ,
          \ g → refl) ,
        ( \ h t x → (h x) t ,
          \ h → refl)))

#def flip-ext-fun-inv
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( X : U)
  ( Y : ψ → X → U)
  ( f : (t : ϕ) → (x : X) → Y t x)
  : Equiv
    ( (x : X) → (t : ψ) → Y t x [ϕ t ↦ f t x])
    ( (t : ψ) → ((x : X) → Y t x) [ϕ t ↦ f t])
  :=
    ( \ h t x → (h x) t ,
      ( ( \ g x t → g t x ,
          \ h → refl) ,
        ( \ g x t → g t x ,
          \ g → refl)))
```

```rzk title="RS17, Theorem 4.2"
#def curry-uncurry
  ( I J : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( ζ : J → TOPE)
  ( χ : ζ → TOPE)
  ( X : ψ → ζ → U)
  ( f : ((t , s) : I × J | (ϕ t ∧ ζ s) ∨ (ψ t ∧ χ s)) → X t s)
  : Equiv
    ( (t : ψ) →
      ( (s : ζ) → X t s [χ s ↦ f (t , s)]) [ϕ t ↦ \ s → f (t , s)])
    ( ((t , s) : I × J | ψ t ∧ ζ s) →
      X t s [(ϕ t ∧ ζ s) ∨ (ψ t ∧ χ s) ↦ f (t , s)])
  :=
    ( \ g (t , s) → (g t) s ,
      ( ( \ h t s → h (t , s) ,
          \ g → refl) ,
        ( \ h t s → h (t , s) ,
          \ h → refl)))

#def uncurry-opcurry
  ( I J : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( ζ : J → TOPE)
  ( χ : ζ → TOPE)
  ( X : ψ → ζ → U)
  ( f : ((t , s) : I × J | (ϕ t ∧ ζ s) ∨ (ψ t ∧ χ s)) → X t s)
  : Equiv
    ( ((t , s) : I × J | ψ t ∧ ζ s) →
      X t s [(ϕ t ∧ ζ s) ∨ (ψ t ∧ χ s) ↦ f (t , s)])
    ( ( s : ζ) →
      ( (t : ψ) → X t s [ϕ t ↦ f (t , s)]) [χ s ↦ \ t → f (t , s)])
  :=
    ( \ h s t → h (t , s) ,
      ( ( \ g (t , s) → (g s) t ,
          \ h → refl) ,
        ( \ g (t , s) → (g s) t ,
          \ g → refl)))

#def fubini
  ( I J : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( ζ : J → TOPE)
  ( χ : ζ → TOPE)
  ( X : ψ → ζ → U)
  ( f : ((t , s) : I × J | (ϕ t ∧ ζ s) ∨ (ψ t ∧ χ s)) → X t s)
  : Equiv
    ( ( t : ψ) →
      ( (s : ζ) → X t s [χ s ↦ f (t , s)]) [ϕ t ↦ \ s → f (t , s)])
    ( ( s : ζ) →
      ( (t : ψ) → X t s [ϕ t ↦ f (t , s)]) [χ s ↦ \ t → f (t , s)])
  :=
    equiv-comp
      ( ( t : ψ) →
        ( (s : ζ) → X t s [χ s ↦ f (t , s)]) [ϕ t ↦ \ s → f (t , s)])
      ( ( (t , s) : I × J | ψ t ∧ ζ s) →
        X t s [(ϕ t ∧ ζ s) ∨ (ψ t ∧ χ s) ↦ f (t , s)])
      ( ( s : ζ) →
        ( (t : ψ) → X t s [ϕ t ↦ f (t , s)]) [χ s ↦ \ t → f (t , s)])
      ( curry-uncurry I J ψ ϕ ζ χ X f)
      ( uncurry-opcurry I J ψ ϕ ζ χ X f)
```

## Extending into Σ-types (the non-axiom of choice)

```rzk title="RS17, Theorem 4.3"
#def axiom-choice
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( X : ψ → U)
  ( Y : (t : ψ) → (x : X t) → U)
  ( a : (t : ϕ) → X t)
  ( b : (t : ϕ) → Y t (a t))
  : Equiv
    ( (t : ψ) → (Σ (x : X t) , Y t x) [ϕ t ↦ (a t , b t)])
    ( Σ ( f : ((t : ψ) → X t [ϕ t ↦ a t])) ,
        ( (t : ψ) → Y t (f t) [ϕ t ↦ b t]))
    :=
      ( \ g → (\ t → (first (g t)) , \ t → second (g t)) ,
        ( ( \ (f , h) t → (f t , h t) ,
            \ _ → refl) ,
          ( \ (f , h) t → (f t , h t) ,
            \ _ → refl)))
```

## Composites and unions of cofibrations

The original form.

```rzk title="RS17, Theorem 4.4"
#def cofibration-composition
  ( I : CUBE)
  ( χ : I → TOPE)
  ( ψ : χ → TOPE)
  ( ϕ : ψ → TOPE)
  ( X : χ → U)
  ( a : (t : ϕ) → X t)
  : Equiv
    ( (t : χ) → X t [ϕ t ↦ a t])
    ( Σ ( f : (t : ψ) → X t [ϕ t ↦ a t]) ,
        ( (t : χ) → X t [ψ t ↦ f t]))
  :=
    ( \ h → (\ t → h t , \ t → h t) ,
      ( ( \ (_f , g) t → g t , \ h → refl) ,
        ( ( \ (_f , g) t → g t , \ h → refl))))

#def cofibration-composition-functorial
  ( I : CUBE)
  ( χ : I → TOPE)
  ( ψ : χ → TOPE)
  ( ϕ : ψ → TOPE)
  ( A' A : χ → U)
  ( α : (t : χ) → A' t → A t)
  ( σ' : (t : ϕ) → A' t)
  : Equiv-of-maps
     ( (t : χ) → A' t [ϕ t ↦ σ' t])
     ( (t : χ) → A t [ϕ t ↦ α t (σ' t)])
     ( \ τ' t → α t (τ' t))
     ( Σ ( τ' : (t : ψ) → A' t [ϕ t ↦ σ' t]) ,
        ( (t : χ) → A' t [ψ t ↦ τ' t]))
     ( Σ ( τ : (t : ψ) → A t [ϕ t ↦ α t (σ' t)]) ,
        ( (t : χ) → A t [ψ t ↦ τ t]))
     ( \ (τ', υ') → ( \ t → α t (τ' t), \t → α t (υ' t)))
  :=
    ( ( ( \ h → (\ t → h t , \ t → h t) , \ h → (\ t → h t , \ t → h t)),
        \ _ → refl),
      ( ( ( \ (_f , g) t → g t , \ h → refl) ,
          ( ( \ (_f , g) t → g t , \ h → refl))),
        ( ( \ (_f , g) t → g t , \ h → refl) ,
          ( ( \ (_f , g) t → g t , \ h → refl)))))
```

A reformulated version via tope disjunction instead of inclusion (see
<https://github.com/rzk-lang/rzk/issues/8>).

```rzk title="RS17, Theorem 4.4"
#def cofibration-composition'
  ( I : CUBE)
  ( χ ψ ϕ : I → TOPE)
  ( X : χ → U)
  ( a : (t : I | χ t ∧ ψ t ∧ ϕ t) → X t)
  : Equiv
      ( (t : χ) → X t [χ t ∧ ψ t ∧ ϕ t ↦ a t])
      ( Σ ( f : (t : I | χ t ∧ ψ t) → X t [χ t ∧ ψ t ∧ ϕ t ↦ a t]) ,
          ( (t : χ) → X t [χ t ∧ ψ t ↦ f t]))
  :=
    ( \ h → (\ t → h t , \ t → h t) ,
      ( ( \ (_f , g) t → g t , \ h → refl) ,
        ( \ (_f , g) t → g t , \ h → refl)))
```

```rzk title="RS17, Theorem 4.5"
#def cofibration-union
  ( I : CUBE)
  ( ϕ ψ : I → TOPE)
  ( X : (t : I | ϕ t ∨ ψ t) → U)
  ( a : (t : ψ) → X t)
  : Equiv
      ( (t : I | ϕ t ∨ ψ t) → X t [ψ t ↦ a t])
      ( (t : ϕ) → X t [ϕ t ∧ ψ t ↦ a t])
  :=
    (\ h t → h t ,
      ( ( \ g t → recOR (ϕ t ↦ g t , ψ t ↦ a t) , \ _ → refl) ,
        ( \ g t → recOR (ϕ t ↦ g t , ψ t ↦ a t) , \ _ → refl)))

#def cofibration-union-functorial
  ( I : CUBE)
  ( ϕ ψ : I → TOPE)
  ( A' A : (t : I | ϕ t ∨ ψ t) → U)
  ( α : (t : I | ϕ t ∨ ψ t) → A' t → A t)
  ( τ' : (t : ψ) → A' t)
  : Equiv-of-maps
      ( (t : I | ϕ t ∨ ψ t) → A' t [ψ t ↦ τ' t])
      ( (t : I | ϕ t ∨ ψ t) → A t [ψ t ↦ α t (τ' t)])
      ( \ υ' t → α t (υ' t))
      ( (t : ϕ) → A' t [ϕ t ∧ ψ t ↦ τ' t])
      ( (t : ϕ) → A t [ϕ t ∧ ψ t ↦ α t (τ' t)])
      ( \ ν' t → α t (ν' t))
  :=
     ( ( ( \ υ' t → υ' t
         , \ υ t → υ t
         )
       , \ _ → refl
       )
     , ( second (cofibration-union I ϕ ψ A' τ')
       ,
         second (cofibration-union I ϕ ψ A ( \ t → α t (τ' t)))
       )
     )
```

## Extension extensionality

There are various equivalent forms of the relative function extensionality axiom
for extension types. One form corresponds to the standard weak function
extensionality. As suggested by footnote 8, we refer to this as a "weak
extension extensionality" axiom.

```rzk title="RS17, Axiom 4.6, Weak extension extensionality"
#define WeakExtExt
  : U
  := ( I : CUBE) → (ψ : I → TOPE) → (ϕ : ψ → TOPE) → (A : ψ → U) →
     ( is-locally-contr-A : (t : ψ) → is-contr (A t)) →
     ( a : (t : ϕ) → A t) → is-contr ((t : ψ) → A t [ϕ t ↦ a t])
```

We refer to another form as an "extension extensionality" axiom.

```rzk
#def ext-htpy-eq
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( A : ψ → U)
  ( a : (t : ϕ) → A t)
  ( f g : (t : ψ) → A t [ϕ t ↦ a t])
  ( p : f = g)
  : (t : ψ) → (f t = g t) [ϕ t ↦ refl]
  :=
    ind-path
      ( (t : ψ) → A t [ϕ t ↦ a t])
      ( f)
      ( \ g' p' → (t : ψ) → (f t = g' t) [ϕ t ↦ refl])
      ( \ t → refl)
      ( g)
      ( p)
```

```rzk title="RS17, Proposition 4.8(ii)"
#def ExtExt
  : U
  :=
    ( I : CUBE) →
    ( ψ : I → TOPE) →
    ( ϕ : ψ → TOPE) →
    ( A : ψ → U) →
    ( a : (t : ϕ) → A t) →
    ( f  : (t : ψ) → A t [ϕ t ↦ a t]) →
    ( g : (t : ψ ) → A t [ϕ t ↦ a t]) →
    is-equiv
      ( f = g)
      ( (t : ψ) → (f t = g t) [ϕ t ↦ refl])
      ( ext-htpy-eq I ψ ϕ A a f g)
```

```rzk title="The equivalence provided by extension extensionality"
#def equiv-ExtExt
  ( extext : ExtExt)
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( A : ψ → U)
  ( a : (t : ϕ) → A t)
  ( f g : (t : ψ) → A t [ϕ t ↦ a t])
  : Equiv (f = g) ((t : ψ) → (f t = g t) [ϕ t ↦ refl])
  := (ext-htpy-eq I ψ ϕ A a f g , extext I ψ ϕ A a f g)
```

For readability of code, it is useful to the function that supplies an equality
between terms of an extension type from a pointwise equality extending refl. In
fact, sometimes only this weaker form of the axiom is needed.

```rzk
#def NaiveExtExt
  : U
  :=
    ( I : CUBE) →
    ( ψ : I → TOPE) →
    ( ϕ : ψ → TOPE) →
    ( A : ψ → U) →
    ( a : (t : ϕ) → A t) →
    ( f : (t : ψ) → A t [ϕ t ↦ a t]) →
    ( g : (t : ψ) → A t [ϕ t ↦ a t]) →
    ( (t : ψ) → (f t = g t) [ϕ t ↦ refl]) →
    ( f = g)

#def naiveextext-extext
  ( extext : ExtExt)
  : NaiveExtExt
  :=
    \ I ψ ϕ A a f g →
      ( first (first (extext I ψ ϕ A a f g)))
```

Weak extension extensionality implies extension extensionality; this is the
context of RS17 Proposition 4.8 (i). We prove this in a series of lemmas. The
`ext-projection-temp` function is a (hopefully temporary) helper that explicitly
cases an extension type to a function type.

```rzk
#section rs-4-8

#variable  weakextext : WeakExtExt
#variable  I : CUBE
#variable  ψ : I → TOPE
#variable  ϕ : ψ → TOPE
#variable  A : ψ → U
#variable  a : (t : ϕ ) → A t
#variable  f : (t : ψ ) → A t [ϕ t ↦ a t]

#define ext-projection-temp uses (I ψ ϕ A a f)
  : ((t : ψ ) → A t)
  := f

#define is-contr-ext-based-paths uses (weakextext f)
  : is-contr ((t : ψ ) → (Σ (y : A t) ,
              ((ext-projection-temp) t = y))[ϕ t ↦ (a t , refl)])
  :=
    weakextext
    ( I )
    ( ψ )
    ( ϕ )
    ( \ t → (Σ (y : A t) , ((ext-projection-temp) t = y)))
    ( \ t →
      is-contr-based-paths (A t ) ((ext-projection-temp) t))
    ( \ t → (a t , refl) )

#define is-contr-ext-endpoint-based-paths uses (weakextext f)
  : is-contr
    ( ( t : ψ) →
      ( Σ (y : A t) , (y = ext-projection-temp t)) [ ϕ t ↦ (a t , refl)])
  :=
    weakextext
    ( I)
    ( ψ)
    ( ϕ)
    ( \ t → (Σ (y : A t) , y = ext-projection-temp t))
    ( \ t → is-contr-endpoint-based-paths (A t) (ext-projection-temp t))
    ( \ t → (a t , refl))

#define is-contr-based-paths-ext uses (weakextext)
  : is-contr (Σ (g : (t : ψ ) → A t [ϕ t ↦ a t]) ,
              (t : ψ ) → (f t = g t) [ϕ t ↦ refl])
  :=
    is-contr-equiv-is-contr
    ( (t : ψ ) → (Σ (y : A t),
                     ((ext-projection-temp ) t = y)) [ϕ t ↦ (a t , refl)] )
    ( Σ (g : (t : ψ ) → A t [ϕ t ↦ a t]) ,
                (t : ψ ) → (f t = g t) [ϕ t ↦ refl] )
    ( axiom-choice
      ( I )
      ( ψ )
      ( ϕ )
      ( A )
      ( \ t y → (ext-projection-temp) t = y)
      ( a )
      ( \t → refl ))
    ( is-contr-ext-based-paths)

#end rs-4-8
```

The map that defines extension extensionality

```rzk title="RS17 4.7"
#define extext-weakextext-map
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( A : ψ → U)
  ( a : (t : ϕ ) → A t)
  ( f : (t : ψ ) → A t [ϕ t ↦ a t])
  : ((Σ (g : (t : ψ ) → A t [ϕ t ↦ a t]), (f = g)) →
      Σ (g : (t : ψ ) → A t [ϕ t ↦ a t]) ,
        ((t : ψ ) → (f t = g t) [ϕ t ↦ refl]))
  :=
    total-map
    ( (t : ψ ) → A t [ϕ t ↦ a t])
    ( \ g → (f = g))
    ( \ g → (t : ψ ) → (f t = g t) [ϕ t ↦ refl])
    ( ext-htpy-eq I ψ ϕ A a f)
```

The total bundle version of extension extensionality

```rzk
#define extext-weakextext-bundle-version
  ( weakextext : WeakExtExt)
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( A : ψ → U)
  ( a : (t : ϕ ) → A t)
  ( f : (t : ψ ) → A t [ϕ t ↦ a t])
  : is-equiv ((Σ (g : (t : ψ ) → A t [ϕ t ↦ a t]), (f = g)))
               (Σ (g : (t : ψ ) → A t [ϕ t ↦ a t]) ,
                  ((t : ψ ) → (f t = g t) [ϕ t ↦ refl]))
               (extext-weakextext-map I ψ ϕ A a f)
  :=
    is-equiv-are-contr
    ( Σ (g : (t : ψ ) → A t [ϕ t ↦ a t]), (f = g)  )
    ( Σ (g : (t : ψ ) → A t [ϕ t ↦ a t]) ,
      ((t : ψ ) → (f t = g t) [ϕ t ↦ refl]))
    ( is-contr-based-paths
      ( (t : ψ ) → A t [ϕ t ↦ a t])
      ( f ))
    ( is-contr-based-paths-ext weakextext I ψ ϕ A a f)
    ( extext-weakextext-map I ψ ϕ A a f)
```

Finally, using equivalences between families of equivalences and bundles of
equivalences we have that weak extension extensionality implies extension
extensionality. The following is statement the as proved in RS17.

```rzk title="RS17 Prop 4.8(i) as proved"
#define extext-weakextext'
  ( weakextext : WeakExtExt)
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( A : ψ → U)
  ( a : (t : ϕ ) → A t)
  ( f : (t : ψ ) → A t [ϕ t ↦ a t])
  : (g : (t : ψ ) → A t [ϕ t ↦ a t]) →
      is-equiv
        ( f = g)
        ( (t : ψ ) → (f t = g t) [ϕ t ↦ refl])
        ( ext-htpy-eq I ψ ϕ A a f g)
  := total-equiv-family-of-equiv
      ( (t : ψ ) → A t [ϕ t ↦ a t] )
      ( \ g → (f = g) )
      ( \ g → (t : ψ ) → (f t = g t) [ϕ t ↦ refl])
      ( ext-htpy-eq I ψ ϕ A a f)
      ( extext-weakextext-bundle-version weakextext I ψ ϕ A a f)
```

The following is the literal statement of weak extension extensionality implying
extension extensionality that we get by extraccting the fiberwise equivalence.

```rzk title="RS17 Proposition 4.8(i)"
#define extext-weakextext
  (weakextext : WeakExtExt)
  :  ExtExt
  := \ I ψ ϕ A a f g →
      extext-weakextext' weakextext I ψ ϕ A a f g
```

## Applications of extension extensionality

We now assume extension extensionality and derive a few consequences.

```rzk
#assume extext : ExtExt
```

In particular, extension extensionality implies that homotopies give rise to
identifications. This definition defines `#!rzk eq-ext-htpy` to be the
retraction to `#!rzk ext-htpy-eq`.

```rzk
#def eq-ext-htpy uses (extext)
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( A : ψ → U)
  ( a : (t : ϕ) → A t)
  ( f g : (t : ψ) → A t [ϕ t ↦ a t])
  : ((t : ψ) → (f t = g t) [ϕ t ↦ refl]) → (f = g)
  := first (first (extext I ψ ϕ A a f g))
```

By extension extensionality, fiberwise equivalences of extension types define
equivalences of extension types. For simplicity, we extend from `#!rzk BOT`.

```rzk
#def equiv-extension-equiv-family uses (extext)
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( A B : ψ → U)
  ( famequiv : (t : ψ) → (Equiv (A t) (B t)))
  : Equiv ((t : ψ) → A t) ((t : ψ) → B t)
  :=
    ( ( \ a t → (first (famequiv t)) (a t)) ,
      ( ( ( \ b t → (first (first (second (famequiv t)))) (b t)) ,
          ( \ a →
            eq-ext-htpy
              ( I)
              ( ψ)
              ( \ t → BOT)
              ( A)
              ( \ u → recBOT)
              ( \ t →
                first (first (second (famequiv t))) (first (famequiv t) (a t)))
              ( a)
              ( \ t → second (first (second (famequiv t))) (a t)))) ,
        ( ( \ b t → first (second (second (famequiv t))) (b t)) ,
          ( \ b →
            eq-ext-htpy
              ( I)
              ( ψ)
              ( \ t → BOT)
              ( B)
              ( \ u → recBOT)
              ( \ t →
                first (famequiv t) (first (second (second (famequiv t))) (b t)))
              ( b)
              ( \ t → second (second (second (famequiv t))) (b t))))))
```

We have a homotopy extension property.

The following code is another instantiation of casting, necessary for some
arguments below.

```rzk
#define restrict
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( A : ψ → U)
  ( a : (t : ϕ) → A t)
  ( f : (t : ψ) → A t [ϕ t ↦ a t])
  : (t : ψ ) → A t
  := f

```

The homotopy extension property has the following signature. We state this
separately since below we will will both show that this follows from extension
extensionality, but we will also show that extension extensionality follows from
the homotopy extension property together with extra hypotheses.

```rzk
#define HtpyExtProperty
  : U
  :=
    ( I : CUBE) →
    ( ψ : I → TOPE) →
    ( ϕ : ψ → TOPE) →
    ( A : ψ → U) →
    ( b : (t : ψ) → A t) →
    ( a : (t : ϕ) → A t) →
    ( e : (t : ϕ) → a t = b t) →
      Σ (a' : (t : ψ) → A t [ϕ t ↦ a t]) ,
      ((t : ψ) → (restrict I ψ ϕ A a a' t = b t) [ϕ t ↦ e t])

```

If we assume weak extension extensionality, then then homotopy extension
property follows from a straightforward application of the axiom of choice to
the point of contraction for weak extension extensionality.

```rzk title="RS17 Proposition 4.10"
#define htpy-ext-property-weakextext
  ( weakextext : WeakExtExt)
  : HtpyExtProperty
  :=
    \ I ψ ϕ A b a e →
    first
    ( axiom-choice
      ( I)
      ( ψ)
      ( ϕ)
      ( A)
      ( \ t y → y = b t)
      ( a)
      ( e))
    ( first
      ( weakextext
        ( I)
        ( ψ)
        ( ϕ)
        ( \ t → (Σ (y : A t) , y = b t))
        ( \ t → is-contr-endpoint-based-paths
                ( A t)
                ( b t))
        ( \ t → ( a t , e t) )))

```

```rzk title="RS17 Proposition 4.10"
#define htpy-ext-prop-weakextext
  ( weakextext : WeakExtExt)
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( A : ψ → U)
  ( b : (t : ψ) → A t)
  ( a : (t : ϕ) → A t)
  ( e : (t : ϕ) → a t = b t)
  : Σ (a' : (t : ψ) → A t [ϕ t ↦ a t]) ,
      ((t : ψ) → (restrict I ψ ϕ A a a' t = b t) [ϕ t ↦ e t])
  :=
    first
    ( axiom-choice
      ( I)
      ( ψ)
      ( ϕ)
      ( A)
      ( \ t y → y = b t)
      ( a)
      ( e))
    ( first
      ( weakextext
        ( I)
        ( ψ)
        ( ϕ)
        ( \ t → (Σ (y : A t) , y = b t))
        ( \ t → is-contr-endpoint-based-paths
                ( A t)
                ( b t))
        ( \ t → ( a t , e t) )))
```

In an extension type of a dependent type that is pointwise contractible, then we
have an inhabitant of the extension type witnessing the contraction, at every
inhabitant of the base, of each point in the fiber to the center of the fiber.
Both directions of this statement will be needed.

```rzk

#def eq-ext-is-contr
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( A : ψ → U)
  ( a : (t : ϕ ) → A t)
  ( is-contr-fiberwise-A : (t : ψ ) → is-contr ( A t))
  : (t : ϕ ) → ((first (is-contr-fiberwise-A t)) = a t)
  :=  \ t → ( second (is-contr-fiberwise-A t) (a t))

#def codomain-eq-ext-is-contr
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( A : ψ → U)
  ( a : (t : ϕ ) → A t)
  ( is-contr-fiberwise-A : (t : ψ ) → is-contr ( A t))
  : (t : ϕ ) → (a t = first (is-contr-fiberwise-A t))
  :=  \ t →
          rev
            ( A t )
            ( first (is-contr-fiberwise-A t) )
            ( a t)
            ( second (is-contr-fiberwise-A t) (a t))

```

The below gives us the inhabitant
$(a', e') : \sum_{\left\langle\prod_{t : I|\psi} A (t) \biggr|^\phi_a\right\rangle} \left\langle \prod_{t: I |\psi} a'(t) = b(t)\biggr|^\phi_e \right\rangle$
from the first part of the proof of RS Prop 4.11. It amounts to the fact that
parameterized contractibility, i.e. `#!rzk A : ψ → U` such that each `A t` is
contractible, implies the hypotheses of the homotopy extension property are
satisfied, and so assuming homotopy extension property, we are entitled to the
conclusion.

```rzk

#define htpy-ext-prop-is-fiberwise-contr
  (htpy-ext-property : HtpyExtProperty)
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( A : ψ → U)
  ( a : (t : ϕ ) → A t)
  (is-contr-fiberwise-A : (t : ψ ) → is-contr (A t))
  : Σ (a' : (t : ψ ) → A t [ϕ t ↦ a t]),
           ((t : ψ ) →
            (restrict I ψ ϕ A a a' t =
              first (is-contr-fiberwise-A t))
              [ϕ t ↦ codomain-eq-ext-is-contr I ψ ϕ A a is-contr-fiberwise-A t] )
  :=
    htpy-ext-property
    ( I )
    ( ψ )
    ( ϕ )
    ( A )
    (\ t →  first (is-contr-fiberwise-A t))
    ( a)
    ( codomain-eq-ext-is-contr I ψ ϕ A a is-contr-fiberwise-A)
```

The expression below give us the inhabitant `#!rzk c : (t : ψ) → f t = a' t`
used in the proof of RS Proposition 4.11. It follows from a more general
statement about the contractibility of identity types, but it is unclear if that
generality is needed.

```rzk
#define RS-4-11-c
  (htpy-ext-prop : HtpyExtProperty)
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( A : ψ → U)
  ( a : (t : ϕ ) → A t)
  ( f : (t : ψ ) → A t [ϕ t ↦ a t])
  (is-contr-fiberwise-A : (t : ψ ) → is-contr (A t))
  : (t : ψ ) → f t = (first (htpy-ext-prop-is-fiberwise-contr htpy-ext-prop I ψ ϕ A a is-contr-fiberwise-A)) t
  := \ t → eq-is-contr
              ( A t)
              ( is-contr-fiberwise-A t)
              ( f t )
              ( restrict I ψ ϕ A a (first (htpy-ext-prop-is-fiberwise-contr htpy-ext-prop I ψ ϕ A a is-contr-fiberwise-A)) t)
```

And below proves that `#!rzk c(t) = refl`. Again, this is a consequence of a
slightly more general statement.

```rzk
#define RS-4-11-c-is-refl
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( A : ψ → U)
  ( is-fiberwise-contr : (t : ψ ) → is-contr (A t))
  ( a : (t : ϕ ) → A t)
  ( f : (t : ψ ) → A t [ϕ t ↦ a t])
  ( a' : (t : ψ ) → A t [ϕ t ↦ a t])
  ( c : (t : ψ ) → (f t = a' t))
  : (t : ϕ ) → (refl =_{f t = a' t} c t)
  :=  \ t →
    all-paths-eq-is-contr
    ( A t)
    ( is-fiberwise-contr t)
    ( f t)
    ( a' t)
    ( refl )
    ( c t )
```

Given the `#!rzk a'` produced above, the following gives an inhabitant of
$\left \langle_{t : I |\psi} f(t) = a'(t) \biggr|^\phi_{\lambda t.refl} \right\rangle$

```rzk
#define is-fiberwise-contr-ext-is-fiberwise-contr
  (htpy-ext-prop : HtpyExtProperty)
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( A : ψ → U)
  ( is-contr-fiberwise-A : (t : ψ ) → is-contr (A t))
 -- ( b : (t : ψ) → A t)
  ( a : (t : ϕ) → A t)
  ( f : (t : ψ ) → A t [ϕ t ↦ a t])
  : (t : ψ ) →
      (f t = (first
              (htpy-ext-prop-is-fiberwise-contr
                htpy-ext-prop I ψ ϕ A a is-contr-fiberwise-A)) t)[ϕ t ↦ refl]
  :=
  first(
    htpy-ext-prop
    ( I )
    ( ψ )
    ( ϕ )
    ( \ t → f t = first
                  (htpy-ext-prop-is-fiberwise-contr
                    htpy-ext-prop I ψ ϕ A a is-contr-fiberwise-A) t)
    ( RS-4-11-c
      htpy-ext-prop I ψ ϕ A a f is-contr-fiberwise-A)
    ( \ t → refl )
    ( RS-4-11-c-is-refl
      ( I)
      ( ψ)
      ( ϕ)
      ( A)
      ( is-contr-fiberwise-A)
      ( a )
      ( f )
      ( first (htpy-ext-prop-is-fiberwise-contr htpy-ext-prop I ψ ϕ A a is-contr-fiberwise-A))
      ( RS-4-11-c
        ( htpy-ext-prop)
        ( I)
        ( ψ)
        ( ϕ)
        ( A)
        ( a)
        ( f)
        ( is-contr-fiberwise-A ))))

#define weak-ext-ext-from-eq-ext-htpy-htpy-ext-property
 (naiveextext : NaiveExtExt)
 (htpy-ext-prop : HtpyExtProperty)
 : WeakExtExt
  := \ I ψ ϕ A is-contr-fiberwise-A a →
    (first (htpy-ext-prop-is-fiberwise-contr htpy-ext-prop I ψ ϕ A a is-contr-fiberwise-A),
     \ f →
      rev
      ( (t : ψ ) → A t [ϕ t ↦ a t])
      ( f )
      ( first (htpy-ext-prop-is-fiberwise-contr
                htpy-ext-prop I ψ ϕ A a is-contr-fiberwise-A))
      (naiveextext
      ( I)
      ( ψ )
      ( ϕ )
      ( A)
      ( a)
      ( f)
      ( first (htpy-ext-prop-is-fiberwise-contr
                htpy-ext-prop I ψ ϕ A a is-contr-fiberwise-A))
      ( is-fiberwise-contr-ext-is-fiberwise-contr
        ( htpy-ext-prop)
        ( I)
        ( ψ )
        ( ϕ )
        ( A)
        ( is-contr-fiberwise-A)
        ( a)
        ( f))))
```

## Proving weak extension extensionality

```rzk
#def equiv-extension-type
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( A : ψ → U)
  : Equiv
    ( (t : ψ) → A t)
    ( Σ ( a : (t : ϕ) → A t) , ( (t : ψ) → A t [ϕ t ↦ a t]))
  :=
    cofibration-composition
      I ψ ϕ (\ t → BOT) A (\ t → recBOT)



```
