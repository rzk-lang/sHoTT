# 10. Trivial fibrations

This is a literate `rzk` file:

```rzk
#lang rzk-1
```

In what follows we show that the projection from the total space of a Sigma type
is an equivalence if and only if its fibers are contractible.

## Contractible fibers

The following type asserts that the fibers of a type family are contractible.

```rzk
#def contractible-fibers
  ( A : U)
  ( B : A → U)
  : U
  := ((x : A) → is-contr (B x))

#section contractible-fibers-data

#variable A : U
#variable B : A → U
#variable contractible-fibers-A-B : contractible-fibers A B
```

```rzk title="The center of contraction in contractible fibers"
#def contractible-fibers-section
  : ( x : A) → B x
  := \ x → center-contraction (B x) (contractible-fibers-A-B x)
```

```rzk title="The section of the total space projection built from the contraction centers"
#def contractible-fibers-actual-section uses (contractible-fibers-A-B)
  : ( a : A) → Σ (x : A) , B x
  := \ a → (a , contractible-fibers-section a)

#def contractible-fibers-section-htpy uses (contractible-fibers-A-B)
  : homotopy A A
    ( comp A (Σ (x : A) , B x) A
      ( projection-total-type A B) (contractible-fibers-actual-section))
    ( identity A)
  := \ x → refl

#def contractible-fibers-section-is-section uses (contractible-fibers-A-B)
  : has-section (Σ (x : A) , B x) A (projection-total-type A B)
  := (contractible-fibers-actual-section , contractible-fibers-section-htpy)
```

This can be used to define the retraction homotopy for the total space
projection, called `#!rzk first` here:

```rzk
#def contractible-fibers-retraction-htpy
  : ( z : Σ (x : A) , B x)
    → ( contractible-fibers-actual-section) (first z) = z
  :=
    \ z →
    eq-eq-fiber-Σ A B
      ( first z)
      ( ( contractible-fibers-section) (first z))
      ( second z)
      ( homotopy-contraction (B (first z)) (contractible-fibers-A-B (first z)) (second z))

#def contractible-fibers-retraction uses (contractible-fibers-A-B)
  : has-retraction (Σ (x : A) , B x) A (projection-total-type A B)
  := (contractible-fibers-actual-section , contractible-fibers-retraction-htpy)
```

The first half of our main result:

```rzk
#def is-equiv-projection-contractible-fibers uses (contractible-fibers-A-B)
  : is-equiv (Σ (x : A) , B x) A (projection-total-type A B)
  := (contractible-fibers-retraction , contractible-fibers-section-is-section)

#def equiv-projection-contractible-fibers uses (contractible-fibers-A-B)
  : Equiv (Σ (x : A) , B x) A
  := (projection-total-type A B , is-equiv-projection-contractible-fibers)

#end contractible-fibers-data
```

## Projection equivalences

From a projection equivalence, it's not hard to inhabit fibers:

```rzk
#def inhabited-fibers-is-equiv-projection
  ( A : U)
  ( B : A → U)
  ( proj-B-to-A-is-equiv : is-equiv (Σ (x : A) , B x) A (projection-total-type A B))
  ( a : A)
  : B a
  :=
    transport A B (first ((first (second proj-B-to-A-is-equiv)) a)) a
      ( ( second (second proj-B-to-A-is-equiv)) a)
      ( second ((first (second proj-B-to-A-is-equiv)) a))
```

This is great but we need more coherence to show that the inhabited fibers are
contractible; the following proof fails:

```text
#def is-equiv-projection-implies-contractible-fibers
  ( A : U)
  ( B : A → U)
  ( proj-B-to-A-is-equiv : is-equiv (Σ (x : A) , B x) A (projection-total-type A B))
  : contractible-fibers A B
  :=
    ( \ x → (second (first (first proj-B-to-A-is-equiv) x) ,
      ( \ u →
        second-path-Σ A B (first (first proj-B-to-A-is-equiv) x) (x , u)
          ( second (first proj-B-to-A-is-equiv) (x , u)))))
```

```rzk
#section projection-hae-data
#variable A : U
#variable B : A → U
#variable proj-B-to-A-is-half-adjoint-equivalence :
  is-half-adjoint-equiv (Σ (x : A) , B x) A (projection-total-type A B)
#variable w : (Σ (x : A) , B x)
```

We start over from a stronger hypothesis of a half adjoint equivalence.

```rzk
#def projection-hae-inverse
  ( a : A)
  : Σ ( x : A) , B x
  := (first (first proj-B-to-A-is-half-adjoint-equivalence)) a

#def projection-hae-base-htpy uses (B)
  ( a : A)
  : ( first (projection-hae-inverse a)) = a
  := (second (second (first proj-B-to-A-is-half-adjoint-equivalence))) a

#def projection-hae-section uses (proj-B-to-A-is-half-adjoint-equivalence)
  ( a : A)
  : B a
  :=
    transport A B (first (projection-hae-inverse a)) a
      ( projection-hae-base-htpy a)
      ( second (projection-hae-inverse a))

#def projection-hae-total-htpy
  : ( projection-hae-inverse (first w)) = w
  := (first (second (first proj-B-to-A-is-half-adjoint-equivalence))) w

#def projection-hae-fibered-htpy
  : ( transport A B (first ((projection-hae-inverse (first w)))) (first w)
    ( first-path-Σ A B
      ( projection-hae-inverse (first w)) w
      ( projection-hae-total-htpy))
    ( second (projection-hae-inverse (first w))))
  = ( second w)
  :=
    second-path-Σ A B (projection-hae-inverse (first w)) w
      ( projection-hae-total-htpy)

#def projection-hae-base-coherence
  : ( projection-hae-base-htpy (first w))
  = ( first-path-Σ A B (projection-hae-inverse (first w)) w
      ( projection-hae-total-htpy))
  := (second proj-B-to-A-is-half-adjoint-equivalence) w

#def projection-hae-transport-coherence
  : ( projection-hae-section (first w))
  = ( transport A B (first ((projection-hae-inverse (first w)))) (first w)
      ( first-path-Σ A B
        ( projection-hae-inverse (first w)) w
        ( projection-hae-total-htpy))
      ( second (projection-hae-inverse (first w))))
  :=
    transport2 A B (first (projection-hae-inverse (first w))) (first w)
    ( projection-hae-base-htpy (first w))
    ( first-path-Σ A B (projection-hae-inverse (first w)) w
      ( projection-hae-total-htpy))
    ( projection-hae-base-coherence)
    ( second (projection-hae-inverse (first w)))

#def projection-hae-fibered-homotopy-contraction
  : ( projection-hae-section (first w)) =_{B (first w)} (second w)
  :=
    concat (B (first w))
      ( projection-hae-section (first w))
      ( transport A B
        ( first ((projection-hae-inverse (first w))))
        ( first w)
        ( first-path-Σ A B (projection-hae-inverse (first w)) w
          ( projection-hae-total-htpy))
        ( second (projection-hae-inverse (first w))))
      ( second w)
      ( projection-hae-transport-coherence)
      ( projection-hae-fibered-htpy)

#end projection-hae-data
```

Finally, we have:

```rzk
#def contractible-fibers-is-half-adjoint-equiv-projection
  ( A : U)
  ( B : A → U)
  ( proj-B-to-A-is-half-adjoint-equivalence
 : is-half-adjoint-equiv (Σ (x : A) , B x) A (projection-total-type A B))
  : contractible-fibers A B
  :=
    \ x →
      ( ( projection-hae-section A B proj-B-to-A-is-half-adjoint-equivalence x)
      , \ u →
          projection-hae-fibered-homotopy-contraction
          A B proj-B-to-A-is-half-adjoint-equivalence (x , u))
```

```rzk title="The converse to our first result"
#def contractible-fibers-is-equiv-projection
  ( A : U)
  ( B : A → U)
  ( proj-B-to-A-is-equiv
 : is-equiv (Σ (x : A) , B x) A (projection-total-type A B))
  : contractible-fibers A B
  :=
    contractible-fibers-is-half-adjoint-equiv-projection A B
      ( is-half-adjoint-equiv-is-equiv (Σ (x : A) , B x) A
        ( projection-total-type A B) proj-B-to-A-is-equiv)
```

```rzk title="The main theorem"
#def projection-theorem
  ( A : U)
  ( B : A → U)
  : iff
    ( is-equiv (Σ (x : A) , B x) A (projection-total-type A B))
    ( contractible-fibers A B)
  :=
    ( \ proj-B-to-A-is-equiv →
      contractible-fibers-is-equiv-projection A B proj-B-to-A-is-equiv
    , \ contractible-fibers-A-B →
      is-equiv-projection-contractible-fibers A B contractible-fibers-A-B)
```

## Equivalence between domain and sum of fibers

For any map `#!rzk f : A → B` the domain `#!rzk A` is equivalent to the sum of
the fibers.

```rzk
#def equiv-sum-of-fibers-domain
  ( A B : U)
  ( f : A → B)
  : Equiv A (Σ (b : B) , fib A B f b)
  :=
    equiv-left-cancel
    ( Σ ( a : A) , Σ (b : B) , f a = b)
    ( A)
    ( Σ ( b : B) , fib A B f b)
    ( equiv-projection-contractible-fibers
      A
      ( \ a → Σ (b : B) , f a = b)
      ( \ a → is-contr-based-paths B (f a)))
    ( fubini-Σ A B (\ a b → f a = b))
```

The inverse map is just the canonical projection to `A`.

```rzk
#def is-equiv-domain-sum-of-fibers
  ( A B : U)
  ( f : A → B)
  : is-equiv (Σ (b : B) , fib A B f b) A (\ (_ , (a , _)) → a)
  :=
    second
    ( inv-equiv A (Σ (b : B) , fib A B f b)
      ( equiv-sum-of-fibers-domain A B f))
```

## Equivalence between fibers in equivalent domains

As an application of the main theorem, we show that precomposing with an
equivalence preserves fibers up to equivalence.

```rzk
#def equiv-fibers-equiv-domains
  ( A B C : U)
  ( f : A → B)
  ( g : B → C)
  ( is-equiv-f : is-equiv A B f)
  ( c : C)
  : Equiv (fib A C (comp A B C g f) c) (fib B C g c)
  :=
  equiv-comp
  ( fib A C (comp A B C g f) c)
  ( Σ ( ( b , _) : fib B C g c) , fib A B f b)
  ( fib B C g c)
  ( equiv-fiber-sum-fiber-comp A B C f g c)
  ( ( projection-total-type (fib B C g c) (\ (b , _) → fib A B f b))
    , second
      ( projection-theorem (fib B C g c) (\ (b , _) → fib A B f b))
      ( \ (b , _) → (is-contr-map-is-equiv A B f is-equiv-f) b))
```
