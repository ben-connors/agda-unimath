# The density factorization system on a category

```agda
module category-theory.density-factorization-systems-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.arrow-precategories
open import category-theory.categories
open import category-theory.precategories
open import category-theory.factorization-systems-categories
open import category-theory.left-kan-extensions-precategories
open import category-theory.density-comonads-on-precategories
open import category-theory.copointed-endofunctors-precategories
open import category-theory.comonads-on-precategories
open import category-theory.density-comonads-on-precategories
open import category-theory.id-dom-comonad-precategories
open import category-theory.opposite-precategories
open import category-theory.commuting-squares-of-morphisms-in-precategories
open import category-theory.functors-categories
open import category-theory.isomorphisms-in-categories
open import category-theory.maps-categories

open import category-theory.functors-precategories
open import category-theory.isomorphisms-in-precategories
open import category-theory.maps-precategories
open import category-theory.natural-isomorphisms-functors-categories
open import category-theory.natural-transformations-functors-categories
open import category-theory.natural-transformations-maps-categories
open import category-theory.pointed-endofunctors-categories
open import category-theory.representing-arrow-category
open import category-theory.natural-isomorphisms-functors-precategories
open import category-theory.natural-transformations-functors-precategories
open import category-theory.natural-transformations-maps-precategories
open import category-theory.pushouts-in-precategories
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

  middle-fact-density-Precategory :
    obj-Precategory C1 → obj-Precategory C
  middle-fact-density-Precategory x =
    cod-obj-arrow-Precategory C (L₀ x)

  left-fact-density-Precategory :
    left-fact-Precategory C middle-fact-density-Precategory
  left-fact-density-Precategory f = mor-obj-arrow-Precategory C (L₀ f)

  right-fact-density-Precategory :
    right-fact-Precategory C middle-fact-density-Precategory
  right-fact-density-Precategory f =
    cod-hom-arrow-Precategory C (pr1 ε f)

  is-fact-density-Precategory :
    is-fact-Precategory C
      ( middle-fact-density-Precategory)
      ( left-fact-density-Precategory)
      ( right-fact-density-Precategory)
  is-fact-density-Precategory f =
    ( square-hom-arrow-Precategory C (pr1 ε f)) ∙
    ( right-unit-law-comp-hom-Precategory C (pr2 f))

  ext-middle-fact-density-Precategory :
    ext-middle-fact-Precategory C middle-fact-density-Precategory
  pr1 ext-middle-fact-density-Precategory u =
    cod-hom-arrow-Precategory C (L₁ u)
  pr2 ext-middle-fact-density-Precategory =
    is-functor-functor-Precategory C1 C
      (comp-functor-Precategory C1 C1 C (cod-functor-arrow-Precategory C) L)

  is-ext-left-fact-density-Precategory :
    is-ext-left-fact-Precategory C
      ( middle-fact-density-Precategory)
      ( ext-middle-fact-density-Precategory)
      ( left-fact-density-Precategory)
  is-ext-left-fact-density-Precategory u =
    square-hom-arrow-Precategory C (L₁ u)

  is-ext-right-fact-density-Precategory :
    is-ext-right-fact-Precategory C
      ( middle-fact-density-Precategory)
      ( ext-middle-fact-density-Precategory)
      ( right-fact-density-Precategory)
  is-ext-right-fact-density-Precategory u =
    ap cha (pr2 ε u)

  funct-fact-density-Precategory :
    funct-fact-Precategory C
  funct-fact-density-Precategory =
    middle-fact-density-Precategory ,
    ( ( left-fact-density-Precategory , right-fact-density-Precategory) ,
      ext-middle-fact-density-Precategory) ,
    ( is-fact-density-Precategory ,
      ( is-ext-left-fact-density-Precategory ,
        is-ext-right-fact-density-Precategory ))

  left-funct-density-Precategory :
    functor-Precategory C1 C1
  left-funct-density-Precategory =
    functor-is-ext-left-fact-Precategory C
      middle-fact-density-Precategory
      ext-middle-fact-density-Precategory
      left-fact-density-Precategory
      is-ext-left-fact-density-Precategory

  eq-left-fact-density-Precategory :
    left-funct-density-Precategory ＝ L
  eq-left-fact-density-Precategory =
    eq-htpy-functor-Precategory C1 C1 left-funct-density-Precategory L
      ( refl-htpy ,
        λ u →
          ( right-unit-law-comp-hom-Precategory C1 _) ∙
          ( inv (left-unit-law-comp-hom-Precategory C1 _)))
```
