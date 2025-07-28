# The one-step factorization system on a precategory

```agda
module category-theory.one-step-factorization-systems-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.arrow-precategories
open import category-theory.categories
open import category-theory.commuting-squares-of-morphisms-in-precategories
open import category-theory.comonads-on-precategories
open import category-theory.copointed-endofunctors-precategories
open import category-theory.density-comonads-on-precategories
open import category-theory.factorization-systems-precategories
open import category-theory.functors-categories
open import category-theory.functors-precategories
open import category-theory.id-dom-comonad-precategories
open import category-theory.isomorphisms-in-categories
open import category-theory.isomorphisms-in-precategories
open import category-theory.left-kan-extensions-precategories
open import category-theory.maps-categories
open import category-theory.maps-precategories
open import category-theory.natural-isomorphisms-functors-categories
open import category-theory.natural-isomorphisms-functors-precategories
open import category-theory.natural-transformations-functors-categories
open import category-theory.natural-transformations-functors-precategories
open import category-theory.natural-transformations-maps-categories
open import category-theory.natural-transformations-maps-precategories
open import category-theory.opposite-precategories
open import category-theory.pointed-endofunctors-categories
open import category-theory.precategories
open import category-theory.pushouts-in-precategories
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

```agda
module _
  {l1 l2 l3 l4 : Level}
  (J : Precategory l1 l2)
  (C : Precategory l1 l2)
  (let C1 = arrow-Precategory C)
  (t : has-all-pushout-obj-Precategory C)
  (F : functor-Precategory J C1)
  (Fk : left-kan-extension-Precategory J C1 C1 F F)
  (let Fc = density-comonad-Precategory J C1 F Fk)
  (let Lc = id-dom-comonad-Precategory C t Fc)
  (let L = endofunctor-comonad-Precategory C1 Lc)
  (let L₀ = obj-functor-Precategory C1 C1 L)
  (let L₁ = hom-functor-Precategory C1 C1 L)
  (let ε = counit-comonad-Precategory C1 Lc)
  (let ν = comul-comonad-Precategory C1 Lc)
  (let cha = cod-hom-arrow-Precategory C)
  where

  middle-fact-one-step-fact-Precategory :
    obj-Precategory C1 → obj-Precategory C
  middle-fact-one-step-fact-Precategory x =
    cod-obj-arrow-Precategory C (L₀ x)

  left-fact-one-step-fact-Precategory :
    left-fact-Precategory C middle-fact-one-step-fact-Precategory
  left-fact-one-step-fact-Precategory f = mor-obj-arrow-Precategory C (L₀ f)

  right-fact-one-step-fact-Precategory :
    right-fact-Precategory C middle-fact-one-step-fact-Precategory
  right-fact-one-step-fact-Precategory f =
    cod-hom-arrow-Precategory C (pr1 ε f)

  is-fact-one-step-fact-Precategory :
    is-fact-Precategory C
      ( middle-fact-one-step-fact-Precategory)
      ( left-fact-one-step-fact-Precategory)
      ( right-fact-one-step-fact-Precategory)
  is-fact-one-step-fact-Precategory f =
    ( square-hom-arrow-Precategory C (pr1 ε f)) ∙
    ( right-unit-law-comp-hom-Precategory C (pr2 f))

  ext-middle-fact-one-step-fact-Precategory :
    ext-middle-fact-Precategory C middle-fact-one-step-fact-Precategory
  pr1 ext-middle-fact-one-step-fact-Precategory u =
    cod-hom-arrow-Precategory C (L₁ u)
  pr2 ext-middle-fact-one-step-fact-Precategory =
    is-functor-functor-Precategory C1 C
      (comp-functor-Precategory C1 C1 C (cod-functor-arrow-Precategory C) L)

  is-ext-left-fact-one-step-fact-Precategory :
    is-ext-left-fact-Precategory C
      ( middle-fact-one-step-fact-Precategory)
      ( ext-middle-fact-one-step-fact-Precategory)
      ( left-fact-one-step-fact-Precategory)
  is-ext-left-fact-one-step-fact-Precategory u =
    square-hom-arrow-Precategory C (L₁ u)

  is-ext-right-fact-one-step-fact-Precategory :
    is-ext-right-fact-Precategory C
      ( middle-fact-one-step-fact-Precategory)
      ( ext-middle-fact-one-step-fact-Precategory)
      ( right-fact-one-step-fact-Precategory)
  is-ext-right-fact-one-step-fact-Precategory u =
    ap cha (pr2 ε u)

  funct-fact-one-step-fact-Precategory :
    funct-fact-Precategory C
  funct-fact-one-step-fact-Precategory =
    middle-fact-one-step-fact-Precategory ,
    ( ( left-fact-one-step-fact-Precategory , right-fact-one-step-fact-Precategory) ,
      ext-middle-fact-one-step-fact-Precategory) ,
    ( is-fact-one-step-fact-Precategory ,
      ( is-ext-left-fact-one-step-fact-Precategory ,
        is-ext-right-fact-one-step-fact-Precategory))

  left-funct-one-step-fact-Precategory :
    functor-Precategory C1 C1
  left-funct-one-step-fact-Precategory =
    functor-is-ext-left-fact-Precategory C
      middle-fact-one-step-fact-Precategory
      ext-middle-fact-one-step-fact-Precategory
      left-fact-one-step-fact-Precategory
      is-ext-left-fact-one-step-fact-Precategory

  eq-left-fact-one-step-fact-Precategory :
    left-funct-one-step-fact-Precategory ＝ L
  eq-left-fact-one-step-fact-Precategory =
    eq-htpy-functor-Precategory C1 C1 left-funct-one-step-fact-Precategory L
      ( refl-htpy ,
        λ u →
          ( right-unit-law-comp-hom-Precategory C1 _) ∙
          ( inv (left-unit-law-comp-hom-Precategory C1 _)))
```
