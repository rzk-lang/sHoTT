# 2. Internal Universe

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

We formalize the internal universe construction following
Licata, Orton, Pitts, and Spitters' "Internal Universes in Models of Homotopy
Type Theory" (arXiv:1801.07664).
## Prerequisites

- `hott/01-paths.rzk.md` — `ap`, `rev`, `concat`, `transport`.
- `hott/03-equivalences.rzk.md` — `Equiv`, `is-equiv`, `UA`, `ua`, `transport-ua`.
- `hott/05-half-adjoint-equivalences.rzk.md` — `is-emb-is-equiv`.
- `hott/06-sigma.rzk.md` — `eq-pair`.
- `hott/08-fibers.rzk.md` — `fib`.
- `hott/10-propositions.rzk.md` — `Prop`, `Unit-Prop`, `univ-family-Prop`, `ufp-first-eq-const-Unit`.
- `hott/04-modalities.rzk.md` — Modality operations, `Prop-b`, `univ-family-Prop-b`.
- `triangulated/01-tiny.rzk.md` — Right adjoint, transpose adjunction.

## Amazing predicate

Given a propositional predicate `pred : (II → U) → Prop` on arrow types,
the amazing predicate lifts it to a predicate on types
via the right adjoint `rar`.

```rzk

#def univ-family-proj-1_i
  : b-extract U (rar univ-family-Prop-b) → b-extract U (rar Prop-b)
  :=
    b-extract
      ( b-extract U (rar univ-family-Prop-b) → b-extract U (rar Prop-b))
      ( rar-fmap univ-family-Prop Prop (\ x → first x))

#def univ-family-rar
  : ( b-extract U (rar Prop-b)) → U
  :=
  \ b →
    fib
      ( b-extract U (rar univ-family-Prop-b))
      ( b-extract U (rar Prop-b))
      ( univ-family-proj-1_i)
      ( b)

#def amazing-tr
  ( pred :♭ (𝕀 → U) → Prop)
  : U → b-extract U (rar Prop-b)
  := b-extract (U → b-extract U (rar Prop-b)) ((untranspose-ar Prop U) (mod ♭ pred))

#def amazing-predicate
  ( pred :♭ (𝕀 → U) → Prop)
  : U → U
  := \ A → univ-family-rar (amazing-tr pred A)

#def const-Unit-Prop-tr (A :♭ U)
  : A → b-extract U (rar Prop-b)
  :=
    b-extract
      ( A → b-extract U (rar Prop-b))
      ( ( untranspose-ar Prop A) (mod ♭ (\ h → Unit-Prop)))

#def const-Unit-Prop-ufp-tr
  : b-extract U (rar univ-family-Prop-b) → b-extract U (rar Prop-b)
  :=
    b-extract
      ( b-extract U (rar univ-family-Prop-b) → b-extract U (rar Prop-b))
      ( ( untranspose-ar Prop (b-extract U (rar univ-family-Prop-b))) (mod ♭ (\ h → Unit-Prop)))


#def ufp-proj_1-i-eq-const-Unit-tr
  :
    univ-family-proj-1_i
  = b-extract
      ( b-extract U (rar univ-family-Prop-b) → b-extract U (rar Prop-b))
      ( ( untranspose-ar Prop (b-extract U (rar univ-family-Prop-b))) (mod ♭ (\ h → Unit-Prop)))
  :=
    ap
      ( ♭ ( univ-family-Prop → Prop))
      ( b-extract U (rar univ-family-Prop-b) → b-extract U (rar Prop-b))
      ( mod ♭ (\ x → first x))
      ( mod ♭ (\ x → Unit-Prop))
      ( \ f →
        let mod ♭ f0 := f in
        let mod ♭ fmap := rar-fmap univ-family-Prop Prop f0
        in fmap)
      ( b-path-commute-fwd
        ( univ-family-Prop → Prop)
        ( \ x → first x)
        ( \ x → Unit-Prop)
        ( mod ♭ (ufp-first-eq-const-Unit funext weakfunext ua)))

#def pred-tr-eq-ufp-const-Unit
  ( pred :♭ (𝕀 → U) → Prop)
  ( A :♭ U)
  ( h :♭ A → U)
  ( f :♭ (a : A) → amazing-predicate pred (h a))
  ( a : A)
  : amazing-tr pred (h a)
    = ( const-Unit-Prop-ufp-tr (first (f a)))
  :=
    concat
      ( b-extract U (rar Prop-b))
      ( amazing-tr pred (h a))
      ( univ-family-proj-1_i (first (f a)))
      ( const-Unit-Prop-ufp-tr (first (f a)))
      ( rev (b-extract U (rar Prop-b))
        ( univ-family-proj-1_i (first (f a)))
        ( amazing-tr pred (h a))
        ( second (f a)))
      ( htpy-eq
        ( b-extract U (rar univ-family-Prop-b))
        ( \ _ → b-extract U (rar Prop-b))
        ( univ-family-proj-1_i)
        ( const-Unit-Prop-ufp-tr)
        ( ufp-proj_1-i-eq-const-Unit-tr)
        ( first (f a)))

#def ufp-const-Unit-eq-A-const-Unit
  ( pred :♭ (𝕀 → U) → Prop)
  ( A :♭ U)
  ( h :♭ A → U)
  ( f :♭ (a : A) → amazing-predicate pred (h a))
  ( a : A)
  : ( const-Unit-Prop-ufp-tr (first (f a)))
    = ( const-Unit-Prop-tr A a)
  :=
    let F-inner
      := let mod ♭ sec := untranspose-ar Prop (b-extract U (rar univ-family-Prop-b)) (mod ♭ (\ (_ : 𝕀 → b-extract U (rar univ-family-Prop-b)) → Unit-Prop))
         in mod ♭ (\ (x : A) → sec (first (f x))) in
    let V := untranspose-ar Prop A (mod ♭ (\ (_ : 𝕀 → A) → Unit-Prop)) in
    let key
      : F-inner = V
      := untranspose-naturality-left Prop (b-extract U (rar univ-family-Prop-b)) A
           ( \ (x : A) → first (f x))
           ( \ (_ : 𝕀 → b-extract U (rar univ-family-Prop-b)) → Unit-Prop) in
    let B-L
      : ( b-extract (A → b-extract U (rar Prop-b)) F-inner) a = const-Unit-Prop-ufp-tr (first (f a))
      := b-elim
           ( b-extract U (rar univ-family-Prop-b) → b-extract U (rar Prop-b))
           ( \ (z : ♭ (b-extract U (rar univ-family-Prop-b) → b-extract U (rar Prop-b)))
           → ( b-extract (A → b-extract U (rar Prop-b)) (let mod ♭ sec := z in mod ♭ (\ (x : A) → sec (first (f x))))) a
             = ( b-extract (b-extract U (rar univ-family-Prop-b) → b-extract U (rar Prop-b)) z) (first (f a)))
           ( untranspose-ar Prop (b-extract U (rar univ-family-Prop-b)) (mod ♭ (\ (_ : 𝕀 → b-extract U (rar univ-family-Prop-b)) → Unit-Prop)))
           ( \ (w0 :♭ b-extract U (rar univ-family-Prop-b) → b-extract U (rar Prop-b)) → \ (e : mod ♭ w0 =_{♭ (b-extract U (rar univ-family-Prop-b) → b-extract U (rar Prop-b))} untranspose-ar Prop (b-extract U (rar univ-family-Prop-b)) (mod ♭ (\ (_ : 𝕀 → b-extract U (rar univ-family-Prop-b)) → Unit-Prop))) → refl) in
    concat (b-extract U (rar Prop-b))
      ( const-Unit-Prop-ufp-tr (first (f a)))
      ( let mod ♭ g := F-inner in g a)
      ( const-Unit-Prop-tr A a)
      ( rev (b-extract U (rar Prop-b))
        ( let mod ♭ g := F-inner in g a)
        ( const-Unit-Prop-ufp-tr (first (f a)))
        ( concat (b-extract U (rar Prop-b))
          ( let mod ♭ g := F-inner in g a)
          ( ( b-extract (A → b-extract U (rar Prop-b)) F-inner) a)
          ( const-Unit-Prop-ufp-tr (first (f a)))
          ( b-let-commute
            ( A → b-extract U (rar Prop-b)) (b-extract U (rar Prop-b))
            ( \ (g : A → b-extract U (rar Prop-b)) → g a) F-inner)
          ( B-L)))
      ( concat (b-extract U (rar Prop-b))
        ( let mod ♭ g := F-inner in g a)
        ( let mod ♭ g := V in g a)
        ( const-Unit-Prop-tr A a)
        ( ap (♭ (A → b-extract U (rar Prop-b))) (b-extract U (rar Prop-b))
          F-inner V
          ( \ (F : ♭ (A → b-extract U (rar Prop-b))) → let mod ♭ g := F in g a)
          key)
        ( b-let-commute
          ( A → b-extract U (rar Prop-b)) (b-extract U (rar Prop-b))
          ( \ (g : A → b-extract U (rar Prop-b)) → g a) V))

#def pred-tr-eq-A-const-Unit
  ( pred :♭ (𝕀 → U) → Prop)
  ( A :♭ U)
  ( h :♭ A → U)
  ( f :♭ (a : A) → amazing-predicate pred (h a))
  ( a : A)
  : amazing-tr pred (h a)
    = ( const-Unit-Prop-tr A a)
  :=
    concat
      ( b-extract U (rar Prop-b))
      ( amazing-tr pred (h a))
      ( const-Unit-Prop-ufp-tr (first (f a)))
      ( const-Unit-Prop-tr A a)
      ( pred-tr-eq-ufp-const-Unit pred A h f a)
      ( ufp-const-Unit-eq-A-const-Unit pred A h f a)
```

## Transposition

`amazing-transpose` converts a `amazing-predicate` into an
arrow predicate.

```rzk

#def transpose-pred-precomp
  ( pred :♭ (𝕀 → U) → Prop)
  ( A :♭ U)
  ( h :♭ A → U)
  : transpose-ar Prop A (mod ♭ (\ (a : A) → amazing-tr pred (h a)))
  =_{♭ ((ar A) → Prop)}
  (let mod ♭ sec := untranspose-ar Prop U (mod ♭ pred) in transpose-ar Prop A (mod ♭ (\ (x : A) → sec (h x))))
  := b-b-elim
       ( U → b-extract U (rar Prop-b))
       ( \ (z : ♭ (U → b-extract U (rar Prop-b)))
         → transpose-ar Prop A (mod ♭ (\ (a : A) → amazing-tr pred (h a)))
           =_{♭ ((ar A) → Prop)}
  (let mod ♭ sec := z in transpose-ar Prop A (mod ♭ (\ (x : A) → sec (h x)))))
       ( untranspose-ar Prop U (mod ♭ pred))
       ( \ (g :♭ U → b-extract U (rar Prop-b))
           ( e : ♭ (mod ♭ g =_{♭ (U → b-extract U (rar Prop-b))} untranspose-ar Prop U (mod ♭ pred)))
         → ap (♭ (A → b-extract U (rar Prop-b))) (♭ ((ar A) → Prop))
             ( mod ♭ (\ (a : A) → amazing-tr pred (h a)))
             ( mod ♭ (\ (x : A) → g (h x)))
             ( transpose-ar Prop A)
             ( b-path-commute-fwd (A → b-extract U (rar Prop-b))
                 ( \ (a : A) → amazing-tr pred (h a)) (\ (x : A) → g (h x))
                 ( let mod ♭ e0 := e in
                   mod ♭ (rev (A → b-extract U (rar Prop-b))
                            ( \ (a : A) → g (h a))
                            ( \ (a : A) → amazing-tr pred (h a))
                            ( ap (U → b-extract U (rar Prop-b)) (A → b-extract U (rar Prop-b))
                                ( g) (b-extract (U → b-extract U (rar Prop-b)) (untranspose-ar Prop U (mod ♭ pred)))
                                ( \ (f : U → b-extract U (rar Prop-b)) → \ (a : A) → f (h a))
                                ( b-extract-eq (U → b-extract U (rar Prop-b))
                                    ( mod ♭ g) (untranspose-ar Prop U (mod ♭ pred)) e0))))))

#def transpose-const-Unit-eq
  ( A :♭ U)
  : transpose-ar Prop A (mod ♭ (const-Unit-Prop-tr A))
  =_{♭ ((ar A) → Prop)}
  transpose-ar Prop A (untranspose-ar Prop A (mod ♭ (\ (_ : 𝕀 → A) → Unit-Prop)))
  := b-b-elim
       ( A → b-extract U (rar Prop-b))
       ( \ (z : ♭ (A → b-extract U (rar Prop-b)))
         → transpose-ar Prop A (mod ♭ (const-Unit-Prop-tr A)) =_{♭ ((ar A) → Prop)} transpose-ar Prop A z)
       ( untranspose-ar Prop A (mod ♭ (\ (_ : 𝕀 → A) → Unit-Prop)))
       ( \ (g :♭ A → b-extract U (rar Prop-b))
           ( e : ♭ (mod ♭ g =_{♭ (A → b-extract U (rar Prop-b))} untranspose-ar Prop A (mod ♭ (\ (_ : 𝕀 → A) → Unit-Prop))))
         → ap (♭ (A → b-extract U (rar Prop-b))) (♭ ((ar A) → Prop))
             ( mod ♭ (const-Unit-Prop-tr A)) (mod ♭ g)
             ( transpose-ar Prop A)
             ( b-path-commute-fwd (A → b-extract U (rar Prop-b)) (const-Unit-Prop-tr A) g
                 ( let mod ♭ e0 := e in
                   mod ♭ (rev (A → b-extract U (rar Prop-b))
                            ( g) (const-Unit-Prop-tr A)
                            ( b-extract-eq (A → b-extract U (rar Prop-b))
                                ( mod ♭ g) (untranspose-ar Prop A (mod ♭ (\ (_ : 𝕀 → A) → Unit-Prop))) e0)))))

#def amazing-transpose
  ( pred :♭ (𝕀 → U) → Prop)
  ( A :♭ U)
  ( h :♭ A → U)
  ( f :♭ (a : A) → amazing-predicate pred (h a))
  : ( ♭ ( ( g : 𝕀 → A) → first (pred (\ b → h (g b)))))
  :=
    let mod ♭ f0 := mod ♭ (\ (a : A) → amazing-tr pred (h a)) in
    let mod ♭ f1 := mod ♭ (const-Unit-Prop-tr A) in
    let mod ♭ A-is-pullback :=
        mod ♭ (\ (a : A) → pred-tr-eq-A-const-Unit pred A h f a)
    in
    let mod ♭ f0=f1 :=
        mod ♭ (b-path-commute-fwd
          ( A → b-extract U (rar Prop-b))
          ( f0) (f1)
          ( mod ♭ (eq-htpy funext A (\ _ → b-extract U (rar Prop-b)) (f0) (f1) (A-is-pullback))))
    in
    let mod ♭ tr-f0 := (transpose-ar Prop A (mod ♭ f0)) in
    let mod ♭ tr-f1 := (transpose-ar Prop A (mod ♭ f1)) in
    let mod ♭ transpose-eq-is-cov :=
        mod ♭ (b-extract-eq
          ( ( 𝕀 → A) → Prop)
          ( transpose-ar Prop A (mod ♭ f0))
          ( mod ♭ (\ (g : 𝕀 → A) → pred (\ b → h (g b))))
          ( concat (♭ ((𝕀 → A) → Prop))
            ( transpose-ar Prop A (mod ♭ f0))
            ( let mod ♭ sec := untranspose-ar Prop U (mod ♭ pred) in transpose-ar Prop A (mod ♭ (\ (x : A) → sec (h x))))
            ( mod ♭ (\ (g : 𝕀 → A) → pred (\ b → h (g b))))
            ( transpose-pred-precomp pred A h)
            ( transpose-untranspose-comp Prop U A h pred)))
    in
    let mod ♭ transpose-eq-pure :=
        mod ♭ (b-extract-eq
          ( ( 𝕀 → A) → Prop)
          ( transpose-ar Prop A (mod ♭ f1))
          ( mod ♭ (\ (_ : (𝕀 → A)) → Unit-Prop))
          ( concat (♭ ((𝕀 → A) → Prop))
            ( transpose-ar Prop A (mod ♭ f1))
            ( transpose-ar Prop A (untranspose-ar Prop A (mod ♭ (\ (_ : 𝕀 → A) → Unit-Prop))))
            ( mod ♭ (\ (_ : (𝕀 → A)) → Unit-Prop))
            ( transpose-const-Unit-eq A)
            ( transpose-untranspose-ar Prop A (mod ♭ (\ _ → Unit-Prop)))))
    in
    let mod ♭ transposed-eq :=
        mod ♭ (concat
          ( ( 𝕀 → A) → Prop)
          ( \ g → (pred (\ b → h (g b))))
          ( tr-f0)
          ( \ _ → Unit-Prop)
          ( rev
            ( ( 𝕀 → A) → Prop)
            ( tr-f0)
            ( \ g → (pred (\ b → h (g b))))
            transpose-eq-is-cov)
          ( concat
            ( ( 𝕀 → A) → Prop)
            ( tr-f0)
            ( tr-f1)
            ( \ _ → Unit-Prop)
            ( ap
              ( ( ♭ ( A → b-extract U (rar Prop-b))))
              ( ( 𝕀 → A) → Prop)
              ( mod ♭ f0) (mod ♭ f1)
              ( \ x → let mod ♭ tr := (transpose-ar Prop A x) in tr)
              f0=f1)
            transpose-eq-pure))
    in
    mod ♭ (\ f → (transport U (\ B → B)
      Unit (first (pred (\ b → h (f b))))
      ( rev U
        ( first (pred (\ b → h (f b))))
        Unit
        ( ap Prop U
          ( pred (\ b → h (f b)))
          Unit-Prop
          ( \ p → first p)
          ( htpy-eq
            ( 𝕀 → A)
            ( \ _ → Prop)
            ( \ g → (pred (\ b → h (g b))))
            ( \ _ → Unit-Prop)
            transposed-eq
            f))))
      unit)
```

`amazing-untranspose` is the converse: given that every arrow satisfies
`pred`, each fiber carries an `amazing-predicate` witness.

```rzk

#def amazing-untranspose
  ( pred :♭ (𝕀 → U) → Prop)
  ( A :♭ U)
  ( h :♭ A → U)
  ( f :♭ (g : 𝕀 → A) → first (pred (\ b → h (g b))))
  : ( ♭ ( ( a : A) → amazing-predicate pred (h a)))
  :=
    let mod ♭ t : (g : 𝕀 → A) → univ-family-Prop := mod ♭ (\ (g : 𝕀 → A) → (pred (\ b → h (g b)) , f g)) in
    let mod ♭ full-eq :=
        mod ♭ (concat (♭ (A → b-extract U (rar Prop-b)))
          ( let mod ♭ fmap := rar-fmap univ-family-Prop Prop (\ (x : univ-family-Prop) → first x) in
            let mod ♭ k := untranspose-ar univ-family-Prop A (mod ♭ t) in
            mod ♭ (\ (x : A) → fmap (k x)))
          ( untranspose-ar Prop A (let mod ♭ t' := (mod ♭ t) in mod ♭ (\ (p : 𝕀 → A) → first (t' p))))
          ( let mod ♭ sec := untranspose-ar Prop U (mod ♭ pred) in mod ♭ (\ (x : A) → sec (h x)))
          ( untranspose-naturality-right-rev univ-family-Prop Prop A (\ (x : univ-family-Prop) → first x) t)
          ( rev (♭ (A → b-extract U (rar Prop-b)))
            ( let mod ♭ sec := untranspose-ar Prop U (mod ♭ pred) in mod ♭ (\ (x : A) → sec (h x)))
            ( untranspose-ar Prop A (let mod ♭ t' := (mod ♭ t) in mod ♭ (\ (p : 𝕀 → A) → first (t' p))))
            ( untranspose-naturality-left Prop U A h pred)))
    in
    let mod ♭ eq-beta :=
        mod ♭ (\ (a : A) →
          concat (b-extract U (rar Prop-b))
            ( univ-family-proj-1_i (b-extract (A → b-extract U (rar univ-family-Prop-b)) (untranspose-ar univ-family-Prop A (mod ♭ t)) a))
            ( b-extract (A → b-extract U (rar Prop-b))
              ( let mod ♭ fmap := rar-fmap univ-family-Prop Prop (\ (x : univ-family-Prop) → first x) in
                let mod ♭ k := untranspose-ar univ-family-Prop A (mod ♭ t) in
                mod ♭ (\ (x : A) → fmap (k x))) a)
            ( amazing-tr pred (h a))
            ( b-elim
                ( b-extract U (rar univ-family-Prop-b) → b-extract U (rar Prop-b))
                ( \ (z1 : ♭ (b-extract U (rar univ-family-Prop-b) → b-extract U (rar Prop-b)))
                → ( b-extract (b-extract U (rar univ-family-Prop-b) → b-extract U (rar Prop-b)) z1)
                    ( b-extract (A → b-extract U (rar univ-family-Prop-b)) (untranspose-ar univ-family-Prop A (mod ♭ t)) a)
                  =_{ b-extract U (rar Prop-b)}
  b-extract (A → b-extract U (rar Prop-b))
                      ( let mod ♭ fmap := z1 in
                        let mod ♭ k := untranspose-ar univ-family-Prop A (mod ♭ t) in
                        mod ♭ (\ (x : A) → fmap (k x))) a)
                ( rar-fmap univ-family-Prop Prop (\ (x : univ-family-Prop) → first x))
                ( \ (fm0 :♭ b-extract U (rar univ-family-Prop-b) → b-extract U (rar Prop-b))
                → \ (e1 : mod ♭ fm0 =_{♭ (b-extract U (rar univ-family-Prop-b) → b-extract U (rar Prop-b))} rar-fmap univ-family-Prop Prop (\ (x : univ-family-Prop) → first x))
                → b-elim
                    ( A → b-extract U (rar univ-family-Prop-b))
                    ( \ (z2 : ♭ (A → b-extract U (rar univ-family-Prop-b)))
                    → fm0 (b-extract (A → b-extract U (rar univ-family-Prop-b)) z2 a)
                      =_{ b-extract U (rar Prop-b)}
  b-extract (A → b-extract U (rar Prop-b))
                          ( let mod ♭ k := z2 in mod ♭ (\ (x : A) → fm0 (k x))) a)
                    ( untranspose-ar univ-family-Prop A (mod ♭ t))
                    ( \ (k0 :♭ A → b-extract U (rar univ-family-Prop-b))
                    → \ (e2 : mod ♭ k0 =_{♭ (A → b-extract U (rar univ-family-Prop-b))} untranspose-ar univ-family-Prop A (mod ♭ t)) → refl)))
            ( concat (b-extract U (rar Prop-b))
              ( b-extract (A → b-extract U (rar Prop-b))
                ( let mod ♭ fmap := rar-fmap univ-family-Prop Prop (\ (x : univ-family-Prop) → first x) in
                  let mod ♭ k := untranspose-ar univ-family-Prop A (mod ♭ t) in
                  mod ♭ (\ (x : A) → fmap (k x))) a)
              ( b-extract (A → b-extract U (rar Prop-b))
                ( let mod ♭ sec := untranspose-ar Prop U (mod ♭ pred) in mod ♭ (\ (x : A) → sec (h x))) a)
              ( amazing-tr pred (h a))
              ( ap (♭ (A → b-extract U (rar Prop-b))) (b-extract U (rar Prop-b))
                ( let mod ♭ fmap := rar-fmap univ-family-Prop Prop (\ (x : univ-family-Prop) → first x) in
                  let mod ♭ k := untranspose-ar univ-family-Prop A (mod ♭ t) in
                  mod ♭ (\ (x : A) → fmap (k x)))
                ( let mod ♭ sec := untranspose-ar Prop U (mod ♭ pred) in mod ♭ (\ (x : A) → sec (h x)))
                ( \ (F : ♭ (A → b-extract U (rar Prop-b))) → b-extract (A → b-extract U (rar Prop-b)) F a)
                ( full-eq))
              ( b-elim
                  ( U → b-extract U (rar Prop-b))
                  ( \ (z : ♭ (U → b-extract U (rar Prop-b)))
                  → b-extract (A → b-extract U (rar Prop-b)) (let mod ♭ sec := z in mod ♭ (\ (x : A) → sec (h x))) a
                    =_{ b-extract U (rar Prop-b)}
  (b-extract (U → b-extract U (rar Prop-b)) z) (h a))
                  ( untranspose-ar Prop U (mod ♭ pred))
                  ( \ (sec0 :♭ U → b-extract U (rar Prop-b)) → \ (e : mod ♭ sec0 =_{♭ (U → b-extract U (rar Prop-b))} untranspose-ar Prop U (mod ♭ pred)) → refl))))
    in
    mod ♭ (\ a → (b-extract (A → b-extract U (rar univ-family-Prop-b)) (untranspose-ar univ-family-Prop A (mod ♭ t)) a , eq-beta a))
```

## Transposition equivalence

The transpose and untranspose form an equivalence, using
that `amazing-predicate` is a proposition.

```rzk

#postulate is-prop-amazing-predicate
  ( pred :♭ (𝕀 → U) → Prop)
  ( X : U)
  : is-prop (amazing-predicate pred X)

#def amazing-transpose-untranspose-section
  ( pred :♭ (𝕀 → U) → Prop)
  ( A :♭ U)
  ( h :♭ A → U)
  ( f :♭ (a : A) → amazing-predicate pred (h a))
  :
    amazing-untranspose pred A h
      ( b-extract ((g : 𝕀 → A) → first (pred (\ b → h (g b)))) (amazing-transpose pred A h f))
    = ( mod ♭ f)
  :=
    let mod ♭ a-untranspose-transpose :=
      ( amazing-untranspose pred A h
        ( b-extract ((g : 𝕀 → A) → first (pred (\ b → h (g b)))) (amazing-transpose pred A h f)))
    in
    b-path-commute-fwd
      ( ( a : A) → amazing-predicate pred (h a))
      ( a-untranspose-transpose) f
      ( mod ♭ (eq-htpy funext A (\ a → amazing-predicate pred (h a))
          a-untranspose-transpose
          ( f)
          ( \ a →
            first
              ( is-prop-amazing-predicate pred (h a)
                ( a-untranspose-transpose a)
                ( f a)))))

#def amazing-transpose-untranspose-retraction
  ( pred :♭ (𝕀 → U) → Prop)
  ( A :♭ U)
  ( h :♭ A → U)
  ( f :♭ (g : 𝕀 → A) → first (pred (\ b → h (g b))))
  :
    amazing-transpose pred A h
      ( b-extract ((a : A) → amazing-predicate pred (h a)) (amazing-untranspose pred A h f))
    = mod ♭ f
  :=
    let mod ♭ a-transpose-untranspose :=
      ( amazing-transpose pred A h
        ( b-extract ((a : A) → amazing-predicate pred (h a)) (amazing-untranspose pred A h f)))
    in
    b-path-commute-fwd
      ( ( g : 𝕀 → A) → first (pred (\ b → h (g b))))
      ( a-transpose-untranspose) f
      ( mod ♭ (eq-htpy funext (𝕀 → A) (\ g → first (pred (\ b → h (g b))))
        a-transpose-untranspose
        ( f)
        ( \ g →
          first
            ( second (pred (\ b → h (g b)))
              ( a-transpose-untranspose g)
              ( f g)))))

#def amazing-transpose-untranspose-equiv
  ( pred :♭ (𝕀 → U) → Prop)
  ( A :♭ U)
  ( h :♭ A → U)
  : Equiv
    ( ♭ ( ( a : A) → amazing-predicate pred (h a)))
    ( ♭ ( ( g : 𝕀 → A) → first (pred (\ b → h (g b)))))
  :=
    let fwd
      : ♭ ( ( a : A) → amazing-predicate pred (h a)) → ♭ ((g : 𝕀 → A) → first (pred (\ b → h (g b))))
      := \ (x : ♭ ((a : A) → amazing-predicate pred (h a))) → let mod ♭ x0 := x in amazing-transpose pred A h x0 in
    let inv
      : ♭ ( ( g : 𝕀 → A) → first (pred (\ b → h (g b)))) → ♭ ((a : A) → amazing-predicate pred (h a))
      := \ (y : ♭ ((g : 𝕀 → A) → first (pred (\ b → h (g b))))) → let mod ♭ y0 := y in amazing-untranspose pred A h y0 in
    ( fwd
    , (
      ( inv
        , \ (x : ♭ ((a : A) → amazing-predicate pred (h a)))
          → b-elim
              ( ( a : A) → amazing-predicate pred (h a))
              ( \ (z : ♭ ((a : A) → amazing-predicate pred (h a))) → inv (fwd z) = z)
              ( x)
              ( \ (x0 :♭ (a : A) → amazing-predicate pred (h a)) → \ (e : mod ♭ x0 =_{♭ ((a : A) → amazing-predicate pred (h a))} x) → amazing-transpose-untranspose-section pred A h x0))

      , ( inv
        , \ (y : ♭ ((g : 𝕀 → A) → first (pred (\ b → h (g b)))))
          → b-elim
              ( ( g : 𝕀 → A) → first (pred (\ b → h (g b))))
              ( \ (z : ♭ ((g : 𝕀 → A) → first (pred (\ b → h (g b))))) → fwd (inv z) = z)
              ( y)
              ( \ (y0 :♭ (g : 𝕀 → A) → first (pred (\ b → h (g b)))) → \ (e : mod ♭ y0 =_{♭ ((g : 𝕀 → A) → first (pred (\ b → h (g b))))} y) → amazing-transpose-untranspose-retraction pred A h y0))

      ))
```
