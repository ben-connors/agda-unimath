r Factorization systems in categories

```agda
module category-theory.factorization-systems-categories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.commuting-squares-of-morphisms-in-precategories
open import category-theory.functors-categories
open import category-theory.maps-categories
open import category-theory.isomorphisms-in-categories
open import category-theory.representing-arrow-category
open import category-theory.natural-transformations-functors-categories
open import category-theory.natural-transformations-maps-categories
open import category-theory.natural-isomorphisms-functors-categories
open import category-theory.pointed-endofunctors-categories
open import category-theory.categories
open import category-theory.arrow-categories

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
  {l1 l2 : Level} (C : Category l1 l2)
  {x y : obj-Category C} (f : hom-Category C x y)
  where

  is-fact-hom-Category :
    (z : obj-Category C)
    (i : hom-Category C x z) (p : hom-Category C z y)  →
    UU l2
  is-fact-hom-Category z i p =
    comp-hom-Category C p i ＝ f

  fact-hom-Category : UU (l1 ⊔ l2)
  fact-hom-Category =
    Σ ( obj-Category C)
      ( λ z →
        Σ ( (hom-Category C x z) × (hom-Category C z y))
          ( λ ip →
            is-fact-hom-Category z (pr1 ip) (pr2 ip)))

  obj-fact-hom-Category : fact-hom-Category → obj-Category C
  obj-fact-hom-Category = pr1

  left-mor-fact-hom-Category :
    (fact : fact-hom-Category) →
    hom-Category C x (obj-fact-hom-Category fact)
  left-mor-fact-hom-Category fact = pr1 (pr1 (pr2 fact))

  right-mor-fact-hom-Category :
    (fact : fact-hom-Category) →
    hom-Category C (obj-fact-hom-Category fact) y
  right-mor-fact-hom-Category fact = pr2 (pr1 (pr2 fact))

  is-fact-fact-hom-Category :
    (fact : fact-hom-Category) →
    is-fact-hom-Category
      ( obj-fact-hom-Category fact)
      ( left-mor-fact-hom-Category fact)
      ( right-mor-fact-hom-Category fact)
  is-fact-fact-hom-Category fact = pr2 (pr2 fact)

  eq-fact-hom-Category :
    (f1 f2 : fact-hom-Category) →
    (e : iso-Category C (obj-fact-hom-Category f1) (obj-fact-hom-Category f2))
    (G :
      comp-hom-Category C
        ( hom-iso-Category C e) (left-mor-fact-hom-Category f1) ＝
      left-mor-fact-hom-Category f2)
    (H :
      comp-hom-Category C
        ( right-mor-fact-hom-Category f1) (hom-inv-iso-Category C e) ＝
      right-mor-fact-hom-Category f2) →
    f1 ＝ f2
  eq-fact-hom-Category f1 f2 e G H =
    eq-pair-Σ
      ( eq-iso-Category C e)
      ( eq-pair-Σ
        ( eq-pair
          ( ( preserves-tr (λ z x → pr1 (pr1 x)) (eq-iso-Category C e) (pr2 f1)) ∙
            ( compute-left-tr-eq-iso-Category C e _) ∙
            ( G))
          ( ( preserves-tr (λ z x → pr2 (pr1 x)) (eq-iso-Category C e) (pr2 f1)) ∙
            ( compute-right-tr-eq-iso-Category C _ e) ∙
            ( H)))
        ( eq-is-prop (is-set-hom-Category C _ _ _ _)))
```

```agda
module _
  {l1 l2 : Level} (C : Category l1 l2)
  (let C1 = arrow-Category C)
  where

  middle-fact-Category : UU (l1 ⊔ l2)
  middle-fact-Category =
    {x y : obj-Category C} → hom-Category C x y → obj-Category C

  left-fact-Category : middle-fact-Category → UU (l1 ⊔ l2)
  left-fact-Category Z = 
    {x y : obj-Category C} (f : hom-Category C x y) →
    hom-Category C x (Z f)

  right-fact-Category : middle-fact-Category → UU (l1 ⊔ l2)
  right-fact-Category Z =
    {x y : obj-Category C} (f : hom-Category C x y) →
    hom-Category C (Z f) y

  is-fact-Category :
    (Z : middle-fact-Category)
    (L : left-fact-Category Z)
    (R : right-fact-Category Z) →
    UU (l1 ⊔ l2)
  is-fact-Category Z L R =
    {x y : obj-Category C} (f : hom-Category C x y) →
    comp-hom-Category C (R f) (L f) ＝ f

  map-left-fact-Category :
    (Z : middle-fact-Category)
    (L : left-fact-Category Z) →
    map-Category C C1
  pr1 (map-left-fact-Category Z L) x =
    make-arrow-Category C (x , (Z (id-hom-Category C) , L (id-hom-Category C)))
  pr2 (map-left-fact-Category Z L) f = {!!}
