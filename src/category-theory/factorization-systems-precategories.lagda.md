# Factorization systems in precategories

```agda
module category-theory.factorization-systems-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.algebras-monads-on-precategories
open import category-theory.arrow-precategories
open import category-theory.coalgebras-comonads-on-precategories
open import category-theory.commuting-squares-of-morphisms-in-precategories
open import category-theory.comonads-on-precategories
open import category-theory.functors-precategories
open import category-theory.isomorphisms-in-precategories
open import category-theory.maps-precategories
open import category-theory.monads-on-precategories
open import category-theory.natural-isomorphisms-functors-precategories
open import category-theory.natural-transformations-functors-precategories
open import category-theory.natural-transformations-maps-precategories
open import category-theory.opposite-precategories
open import category-theory.pointed-endofunctors-precategories
open import category-theory.precategories
open import category-theory.representing-arrow-category

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.commuting-squares-of-maps
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.propositions
open import foundation-core.transport-along-identifications
```

</details>

## Idea

We define algebraic weak factorization systems in several steps:

## Definitions

A factorization is for each `f : x → y` a choice of `Zf : Ob C` and morphisms
`Lf : x → Zf` and `Rf : Zf → y` such that `Rf ∘ Lf = f`.

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  (let C1 = arrow-Precategory C)
  (let dom = dom-obj-arrow-Precategory C)
  (let cod = cod-obj-arrow-Precategory C)
  (let mor = mor-obj-arrow-Precategory C)
  (let dom-mor = dom-hom-arrow-Precategory C)
  (let cod-mor = cod-hom-arrow-Precategory C)
  where

  middle-fact-Precategory : UU (l1 ⊔ l2)
  middle-fact-Precategory = obj-Precategory C1 → obj-Precategory C

  left-fact-Precategory : middle-fact-Precategory → UU (l1 ⊔ l2)
  left-fact-Precategory Z =
    (f : obj-Precategory C1) →
    hom-Precategory C (dom f) (Z f)

  right-fact-Precategory : middle-fact-Precategory → UU (l1 ⊔ l2)
  right-fact-Precategory Z =
    (f : obj-Precategory C1) →
    hom-Precategory C (Z f) (cod f)

  is-fact-Precategory :
    (Z : middle-fact-Precategory)
    (L : left-fact-Precategory Z)
    (R : right-fact-Precategory Z) →
    UU (l1 ⊔ l2)
  is-fact-Precategory Z L R =
    (f : obj-Precategory C1) →
    comp-hom-Precategory C (R f) (L f) ＝ mor f
```

Now we extend this to the necessary structure to give three functors:
`Z : C[1] → C`, `L : C[1] → C[1]`, and `R : C[1] → C[1]` with the restrictions
that:

1. `d⁰ ∘ L = Z = d¹ ∘ R` ;
2. `d¹ ∘ L = dom` ; and
3. `d⁰ ∘ R = cod`.

Doing it in steps instead of requiring three functors and equalities (or a
single functor `C[1] → C[2]` with equalities) allows us to ensure that the three
conditions above hold judgementally at each morphism in `C` which simplifies
both statements and proofs significantly.

```agda
  ext-middle-fact-Precategory :
    (Z : middle-fact-Precategory) → UU (l1 ⊔ l2)
  ext-middle-fact-Precategory Z =
    Σ ( {f g : obj-Precategory C1} (u : hom-Precategory C1 f g) →
        hom-Precategory C (Z f) (Z g))
      (λ M → is-functor-map-Precategory C1 C (Z , M))

  hom-ext-middle-fact-Precategory :
    (Z : middle-fact-Precategory)
    (M : ext-middle-fact-Precategory Z)
    {f g : obj-Precategory C1}
    (u : hom-Precategory C1 f g) →
    hom-Precategory C (Z f) (Z g)
  hom-ext-middle-fact-Precategory Z M = pr1 M
```

This data extends `Z` to a functor:

```agda
  functor-ext-middle-fact-Precategory :
    (Z : middle-fact-Precategory)
    (M : ext-middle-fact-Precategory Z) →
    functor-Precategory C1 C
  functor-ext-middle-fact-Precategory Z M = Z , M

  is-ext-left-fact-Precategory :
    (Z : middle-fact-Precategory)
    (M : ext-middle-fact-Precategory Z)
    (L : left-fact-Precategory Z) →
    UU (l1 ⊔ l2)
  is-ext-left-fact-Precategory Z M L =
    {f g : obj-Precategory C1}
    (u : hom-Precategory C1 f g) →
    coherence-square-hom-Precategory C
      ( dom-mor u)
      ( L f)
      ( L g)
      ( (hom-ext-middle-fact-Precategory Z M) u)
```

This property extends `L` to a copointed functor:

```agda
  functor-is-ext-left-fact-Precategory :
    (Z : middle-fact-Precategory)
    (M : ext-middle-fact-Precategory Z)
    (L : left-fact-Precategory Z)
    (N : is-ext-left-fact-Precategory Z M L) →
    functor-Precategory C1 C1
  pr1 (functor-is-ext-left-fact-Precategory Z M L N) f =
    ((dom f) , (Z f)) , (L f)
  pr1 (pr2 (functor-is-ext-left-fact-Precategory Z M L N)) {f} {g} u =
    ((dom-mor u) , (pr1 M) u) , N u
  pr1 (pr2 (pr2 (functor-is-ext-left-fact-Precategory Z M L N))) {f} {g} {h} u v =
    eq-hom-arrow-Precategory C _ _ _ _
      ( refl)
      ( preserves-comp-functor-Precategory C1 C
        ( functor-ext-middle-fact-Precategory Z M)
        ( _)
        ( _))
  pr2 (pr2 (pr2 (functor-is-ext-left-fact-Precategory Z M L N))) f =
    eq-hom-arrow-Precategory C _ _ _ _
      ( refl)
      ( preserves-id-functor-Precategory C1 C
        ( functor-ext-middle-fact-Precategory Z M)
        ( _))

  is-ext-right-fact-Precategory :
    (Z : middle-fact-Precategory)
    (M : ext-middle-fact-Precategory Z)
    (R : right-fact-Precategory Z) →
    UU (l1 ⊔ l2)
  is-ext-right-fact-Precategory Z M R =
    {f g : obj-Precategory C1}
    (u : hom-Precategory C1 f g) →
    coherence-square-hom-Precategory C
      ( (hom-ext-middle-fact-Precategory Z M) u)
      ( R f)
      ( R g)
      ( cod-mor u)
```

This property extends `R` to a functor:

```agda
  functor-is-ext-right-fact-Precategory :
    (Z : middle-fact-Precategory)
    (M : ext-middle-fact-Precategory Z)
    (R : right-fact-Precategory Z)
    (N : is-ext-right-fact-Precategory Z M R) →
    functor-Precategory C1 C1
  pr1 (functor-is-ext-right-fact-Precategory Z M R N) f =
    ((Z f) , (cod f)) , (R f)
  pr1 (pr2 (functor-is-ext-right-fact-Precategory Z M R N)) {f} {g} u =
    ((pr1 M) u , (cod-mor u)) , N u
  pr1 (pr2 (pr2 (functor-is-ext-right-fact-Precategory Z M R N))) {f} {g} {h} u v =
    eq-hom-arrow-Precategory C _ _ _ _
      ( preserves-comp-functor-Precategory C1 C
        ( functor-ext-middle-fact-Precategory Z M)
        ( _)
        ( _))
      ( refl)
  pr2 (pr2 (pr2 (functor-is-ext-right-fact-Precategory Z M R N))) f =
    eq-hom-arrow-Precategory C _ _ _ _
      ( preserves-id-functor-Precategory C1 C
        ( functor-ext-middle-fact-Precategory Z M)
        ( _))
      ( refl)
```

We pack this data into a single type; having both extensions also gives us a
copointing `L ⇒ id` and a pointing `id ⇒ R`.

```
  funct-fact-Precategory : UU (l1 ⊔ l2)
  funct-fact-Precategory =
    Σ ( middle-fact-Precategory)
      ( λ Z →
        Σ ( ( ( left-fact-Precategory Z) × (right-fact-Precategory Z)) ×
            ( ext-middle-fact-Precategory Z))
          ( λ LRE →
            ( is-fact-Precategory Z (pr1 (pr1 LRE)) (pr2 (pr1 LRE))) ×
            ( ( is-ext-left-fact-Precategory Z (pr2 LRE) (pr1 (pr1 LRE))) ×
              ( is-ext-right-fact-Precategory Z (pr2 LRE) (pr2 (pr1 LRE))))))

  middle-funct-fact-Precategory :
    funct-fact-Precategory → middle-fact-Precategory
  middle-funct-fact-Precategory = pr1

  left-funct-fact-Precategory :
    (F : funct-fact-Precategory) →
    left-fact-Precategory (middle-funct-fact-Precategory F)
  left-funct-fact-Precategory = pr1 ∘ pr1 ∘ pr1 ∘ pr2

  right-funct-fact-Precategory :
    (F : funct-fact-Precategory) →
    right-fact-Precategory (middle-funct-fact-Precategory F)
  right-funct-fact-Precategory = pr2 ∘ pr1 ∘ pr1 ∘ pr2

  is-fact-funct-fact-Precategory :
    (F : funct-fact-Precategory) →
    is-fact-Precategory
      (middle-funct-fact-Precategory F)
      (left-funct-fact-Precategory F)
      (right-funct-fact-Precategory F)
  is-fact-funct-fact-Precategory = pr1 ∘ pr2 ∘ pr2

  ext-middle-funct-fact-Precategory :
    (F : funct-fact-Precategory) →
    ext-middle-fact-Precategory (middle-funct-fact-Precategory F)
  ext-middle-funct-fact-Precategory = pr2 ∘ pr1 ∘ pr2

  is-ext-left-funct-fact-Precategory :
    (F : funct-fact-Precategory) →
    is-ext-left-fact-Precategory
      (middle-funct-fact-Precategory F)
      (ext-middle-funct-fact-Precategory F)
      (left-funct-fact-Precategory F)
  is-ext-left-funct-fact-Precategory = pr1 ∘ pr2 ∘ pr2 ∘ pr2

  is-ext-right-funct-fact-Precategory :
    (F : funct-fact-Precategory) →
    is-ext-right-fact-Precategory
      (middle-funct-fact-Precategory F)
      (ext-middle-funct-fact-Precategory F)
      (right-funct-fact-Precategory F)
  is-ext-right-funct-fact-Precategory = pr2 ∘ pr2 ∘ pr2 ∘ pr2

  middle-functor-funct-fact-Precategory :
    (F : funct-fact-Precategory) →
    functor-Precategory C1 C
  middle-functor-funct-fact-Precategory F =
    functor-ext-middle-fact-Precategory
      ( middle-funct-fact-Precategory F)
      ( ext-middle-funct-fact-Precategory F)

  left-functor-funct-fact-Precategory :
    (F : funct-fact-Precategory) →
    functor-Precategory C1 C1
  left-functor-funct-fact-Precategory F =
    functor-is-ext-left-fact-Precategory
      ( middle-funct-fact-Precategory F)
      ( ext-middle-funct-fact-Precategory F)
      ( left-funct-fact-Precategory F)
      ( is-ext-left-funct-fact-Precategory F)

  right-functor-funct-fact-Precategory :
    (F : funct-fact-Precategory) →
    functor-Precategory C1 C1
  right-functor-funct-fact-Precategory F =
    functor-is-ext-right-fact-Precategory
      ( middle-funct-fact-Precategory F)
      ( ext-middle-funct-fact-Precategory F)
      ( right-funct-fact-Precategory F)
      ( is-ext-right-funct-fact-Precategory F)

  counit-funct-fact-Precategory :
    (F : funct-fact-Precategory) →
    natural-transformation-Precategory C1 C1
      ( left-functor-funct-fact-Precategory F)
      ( id-functor-Precategory C1)
  pr1 (pr1 (pr1 (counit-funct-fact-Precategory F) f)) =
    id-hom-Precategory C
  pr2 (pr1 (pr1 (counit-funct-fact-Precategory F) f)) =
    right-funct-fact-Precategory F f
  pr2 (pr1 (counit-funct-fact-Precategory F) f) =
    ( is-fact-funct-fact-Precategory F f) ∙
    ( inv (right-unit-law-comp-hom-Precategory C _))
  pr2 (counit-funct-fact-Precategory F) u =
    eq-hom-arrow-Precategory C _ _ _ _
      ( ( right-unit-law-comp-hom-Precategory C _) ∙
        ( inv (left-unit-law-comp-hom-Precategory C _)))
      ( is-ext-right-funct-fact-Precategory F u)

  unit-funct-fact-Precategory :
    (F : funct-fact-Precategory) →
    natural-transformation-Precategory C1 C1
      ( id-functor-Precategory C1)
      ( right-functor-funct-fact-Precategory F)
  pr1 (pr1 (pr1 (unit-funct-fact-Precategory F) f)) =
    left-funct-fact-Precategory F f
  pr2 (pr1 (pr1 (unit-funct-fact-Precategory F) f)) =
    id-hom-Precategory C
  pr2 (pr1 (unit-funct-fact-Precategory F) f) =
    ( left-unit-law-comp-hom-Precategory C _) ∙
    ( inv (is-fact-funct-fact-Precategory F f))
  pr2 (unit-funct-fact-Precategory F) u =
    eq-hom-arrow-Precategory C _ _ _ _
      ( is-ext-left-funct-fact-Precategory F u)
      ( ( right-unit-law-comp-hom-Precategory C _) ∙
        ( inv (left-unit-law-comp-hom-Precategory C _)))
```

We have a natural weak factorization system if we have a comonad and monad
structure on `L` and `R`, respectively, with the counit and unit given by the
natural copointing and pointing, respectively. In this case, the (retracts of)
`L`-coalgebras lift against the (retracts of) `R`-algebras.

```agda
  is-left-algebraic-funct-fact-Precategory :
    funct-fact-Precategory → UU (l1 ⊔ l2)
  is-left-algebraic-funct-fact-Precategory F =
    structure-comonad-copointed-endofunctor-Precategory C1
      ( ( left-functor-funct-fact-Precategory F) ,
        ( counit-funct-fact-Precategory F))

  is-right-algebraic-funct-fact-Precategory :
    funct-fact-Precategory → UU (l1 ⊔ l2)
  is-right-algebraic-funct-fact-Precategory F =
    structure-monad-pointed-endofunctor-Precategory C1
      ( ( right-functor-funct-fact-Precategory F) ,
        ( unit-funct-fact-Precategory F))
```

Given a left- and right-algebraic functorial factorization, any lifting diagram
of an `L`-coalgebra against an `R`-algebra has a canonical solution.

```agda
  module _
    (F : funct-fact-Precategory)
    (let L = left-functor-funct-fact-Precategory F)
    (let L₀ = obj-functor-Precategory C1 C1 L)
    (let L₁ = hom-functor-Precategory C1 C1 L)
    (let R = right-functor-funct-fact-Precategory F)
    (let R₀ = obj-functor-Precategory C1 C1 R)
    (let R₁ = hom-functor-Precategory C1 C1 R)
    (let ε = counit-funct-fact-Precategory F)
    (let Z = middle-functor-funct-fact-Precategory F)
    (let η = unit-funct-fact-Precategory F)
    (Ln : is-left-algebraic-funct-fact-Precategory F)
    (let Lc : comonad-Precategory C1
         Lc = ((L , ε) , Ln))
    (let ν = pr1 Ln)
    (Rn : is-right-algebraic-funct-fact-Precategory F)
    (let Rm : monad-Precategory C1
         Rm = ((R , η) , Rn))
    (let μ = pr1 Rn)
    (let cha = cod-hom-arrow-Precategory C)
    (let dha = dom-hom-arrow-Precategory C)
    where

    eq-dom-coalgebra-algebraic-funct-fact-Precategory :
      (f : coalgebra-comonad-Precategory C1 Lc) →
      dom-hom-arrow-Precategory C (hom-coalgebra-comonad-Precategory C1 Lc f) ＝
      id-hom-Precategory C
    eq-dom-coalgebra-algebraic-funct-fact-Precategory f =
      ( inv (left-unit-law-comp-hom-Precategory C _)) ∙
      ( ap
        ( dom-hom-arrow-Precategory C)
        ( counit-law-coalgebra-comonad-Precategory C1 Lc f))

    eq-cod-coalgebra-algebraic-funct-fact-Precategory :
      (f : coalgebra-comonad-Precategory C1 Lc) →
      comp-hom-Precategory C
        ( mor-obj-arrow-Precategory C (R₀ (obj-coalgebra-comonad-Precategory C1 Lc f)))
        ( cod-hom-arrow-Precategory C (hom-coalgebra-comonad-Precategory C1 Lc f)) ＝
      id-hom-Precategory C
    eq-cod-coalgebra-algebraic-funct-fact-Precategory f =
      ap
        ( cod-hom-arrow-Precategory C)
        ( counit-law-coalgebra-comonad-Precategory C1 Lc f)

    lift-coalgebra-algebra-algebraic-funct-fact-Precategory :
      (f : coalgebra-comonad-Precategory C1 Lc)
      (g : algebra-monad-Precategory C1 Rm)
      (u : hom-Precategory C
        ( dom-obj-arrow-Precategory C (pr1 f))
        ( dom-obj-arrow-Precategory C (pr1 g)))
      (v : hom-Precategory C
        ( cod-obj-arrow-Precategory C (pr1 f))
        ( cod-obj-arrow-Precategory C (pr1 g)))
      (sq : coherence-square-hom-Precategory C
        ( u)
        ( mor-obj-arrow-Precategory C (pr1 f))
        ( mor-obj-arrow-Precategory C (pr1 g))
        ( v)) →
      has-lift-coherence-square-hom-Precategory C
        ( u)
        ( mor-obj-arrow-Precategory C (pr1 f))
        ( mor-obj-arrow-Precategory C (pr1 g))
        ( v)
        ( sq)
    pr1 (lift-coalgebra-algebra-algebraic-funct-fact-Precategory (((x , y) , f) , (((sd , sc) , ssq) , fa)) (g , (((td , tc) , tsq) , ga)) u v sq) =
      comp-hom-Precategory C
        ( comp-hom-Precategory C
          ( td)
          ( pr1 (ext-middle-funct-fact-Precategory F) ((u , v) , sq)))
        ( sc)
    pr2 (lift-coalgebra-algebra-algebraic-funct-fact-Precategory (((x , y) , f) , (((sd , sc) , ssq) , fa)) (((a , b) , g) , (((td , tc) , tsq) , ga)) u v sq) =
      sol , sol' where

      middle = pr1 (ext-middle-funct-fact-Precategory F) ((u , v) , sq)
      filler = comp-hom-Precategory C
        ( comp-hom-Precategory C
          ( td)
          ( middle))
        ( sc)

      isid : sd ＝ id-hom-Precategory C {x}
      isid =
        ( inv (left-unit-law-comp-hom-Precategory C sd)) ∙
        ( ap dha (counit-law-coalgebra-comonad-Precategory C1 Lc (((x , y) , f) , (((sd , sc) , ssq) , fa))))

      isid' : tc ＝ id-hom-Precategory C {b}
      isid' =
        ( inv (right-unit-law-comp-hom-Precategory C tc)) ∙
        ( ap cha (unit-law-algebra-monad-Precategory C1 Rm (((a , b) , g) , (((td , tc) , tsq) , ga))))

      Lf = mor-obj-arrow-Precategory C (L₀ ((x , y) , f))
      Lg = mor-obj-arrow-Precategory C (L₀ ((a , b) , g))

      Rf = mor-obj-arrow-Precategory C (R₀ ((x , y) , f))
      Rg = mor-obj-arrow-Precategory C (R₀ ((a , b) , g))

      sol : comp-hom-Precategory C filler f ＝ u
      sol =
        ( associative-comp-hom-Precategory C _ _ _) ∙
        ( ap
          ( comp-hom-Precategory C
            ( comp-hom-Precategory C td middle))
          ( ( ssq) ∙
            ( ap (comp-hom-Precategory C _) isid) ∙
            ( right-unit-law-comp-hom-Precategory C _))) ∙
        ( associative-comp-hom-Precategory C td middle Lf) ∙
        ( ap
          ( comp-hom-Precategory C td)
          ( is-ext-left-funct-fact-Precategory F ((u , v) , sq))) ∙
        ( inv (associative-comp-hom-Precategory C td Lg u)) ∙
        ( ap
          ( precomp-hom-Precategory C u _)
          ( ap dha (unit-law-algebra-monad-Precategory C1 Rm ( (((a , b) , g) , (((td , tc) , tsq) , ga)))))) ∙
        ( left-unit-law-comp-hom-Precategory C u)

      sol' : comp-hom-Precategory C g filler ＝ v
      sol' =
        ( inv (associative-comp-hom-Precategory C g _ sc)) ∙
        ( ap
          ( precomp-hom-Precategory C sc _)
          ( ( inv (associative-comp-hom-Precategory C g td middle)) ∙
            ( ap
              ( precomp-hom-Precategory C middle _)
              ( ( inv (square-hom-arrow-Precategory C (((td , tc) , tsq)))) ∙
                ( ap (precomp-hom-Precategory C _ _) isid') ∙
                ( left-unit-law-comp-hom-Precategory C _))) ∙
            ( inv (is-ext-right-funct-fact-Precategory F ((u , v) , sq))))) ∙
        ( associative-comp-hom-Precategory C v Rf sc) ∙
        ( ap
          ( comp-hom-Precategory C v)
          ( ap cha (counit-law-coalgebra-comonad-Precategory C1 Lc ( (((x , y) , f) , (((sd , sc) , ssq) , fa)))))) ∙
        ( right-unit-law-comp-hom-Precategory C v)
```

We have a natural transformation `LR ⇒ RL` induced by the codomain
comultiplication on the domain and the domain multiplication on the codomain
part:

```agda
    dist-morphism-algebraic-funct-fact-Precategory :
      natural-transformation-Precategory C1 C1
        ( comp-functor-Precategory C1 C1 C1 L R)
        ( comp-functor-Precategory C1 C1 C1 R L)
    pr1 (pr1 (pr1 dist-morphism-algebraic-funct-fact-Precategory f)) =
      cha (pr1 ν f)
    pr2 (pr1 (pr1 dist-morphism-algebraic-funct-fact-Precategory f)) =
      dha (pr1 μ f)
    pr2 (pr1 dist-morphism-algebraic-funct-fact-Precategory f) =
      ( ap (λ x → dha (pr1 x f)) (right-unit-law-mul-monad-Precategory C1 Rm)) ∙
      ( inv
        ( ap (λ x → cha (pr1 x f))
          ( right-counit-law-comul-comonad-Precategory C1 Lc)))
    pr2 dist-morphism-algebraic-funct-fact-Precategory u =
      eq-hom-arrow-Precategory C _ _ _ _
        ( pr2
          ( left-whisker-natural-transformation-Precategory C1 C1 C
            ( L)
            ( comp-functor-Precategory C1 C1 C1 L L)
            ( cod-functor-arrow-Precategory C)
            ( ν))
          ( u))
        ( pr2
          ( left-whisker-natural-transformation-Precategory C1 C1 C
            ( comp-functor-Precategory C1 C1 C1 R R)
            ( R)
            ( dom-functor-arrow-Precategory C)
            ( μ))
          ( u))
```

An algebraic functorial factorization system is an algebraic weak factorization
system if the `dist-morphism` above is a distributive law:

```agda
  is-algebraic-wfs-Precategory :
    (F : funct-fact-Precategory)
    (LF : is-left-algebraic-funct-fact-Precategory F)
    (RF : is-right-algebraic-funct-fact-Precategory F) →
    UU (l1 ⊔ l2)
  is-algebraic-wfs-Precategory F LF RF =
    (f : obj-Precategory C1) →
    comp-hom-Precategory C
      ( cod-hom-arrow-Precategory C (pr1 (pr1 LF) f))
      ( dom-hom-arrow-Precategory C (pr1 (pr1 RF) f)) ＝
    comp-hom-Precategory C
      ( comp-hom-Precategory C
        ( dom-hom-arrow-Precategory C
          ( pr1
            ( pr1 RF)
            ( obj-functor-Precategory C1 C1
              ( left-functor-funct-fact-Precategory F)
              ( f))))
        ( hom-functor-Precategory C1 C
          ( middle-functor-funct-fact-Precategory F)
          ( pr1
            ( dist-morphism-algebraic-funct-fact-Precategory F LF RF)
            ( f))))
      ( cod-hom-arrow-Precategory C
        ( pr1
          ( pr1 LF)
          ( obj-functor-Precategory C1 C1
            ( right-functor-funct-fact-Precategory F)
            ( f))))

  algebraic-wfs-Precategory : UU (l1 ⊔ l2)
  algebraic-wfs-Precategory =
    Σ ( funct-fact-Precategory)
      ( λ F →
        Σ ( is-left-algebraic-funct-fact-Precategory F ×
            is-right-algebraic-funct-fact-Precategory F)
          ( λ LR →
            ( is-algebraic-wfs-Precategory F (pr1 LR) (pr2 (LR)))))
```
