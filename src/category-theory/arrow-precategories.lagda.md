# Arrow precategories

```agda
module category-theory.arrow-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.adjunctions-precategories
open import category-theory.commuting-squares-of-morphisms-in-precategories
open import category-theory.functors-categories
open import category-theory.maps-categories
open import category-theory.natural-transformations-functors-precategories
open import category-theory.natural-transformations-maps-precategories
open import category-theory.pointed-endofunctors-precategories
open import category-theory.categories
open import category-theory.category-of-functors
open import category-theory.representing-arrow-category

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.identity-types
open import foundation.unit-type
open import foundation.sets
open import foundation.booleans
open import foundation.propositions
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

```
module _
  {l1 l2 : Level} (C : Category l1 l2)
  where

  arrow-Category : Category (l1 ⊔ l2) l2
  arrow-Category =
    functor-category-Category representing-arrow-Category C

  dom-arrow-Category : obj-Category arrow-Category → obj-Category C
  dom-arrow-Category f =
    obj-functor-Category representing-arrow-Category C f false

  cod-arrow-Category : obj-Category arrow-Category → obj-Category C
  cod-arrow-Category f =
    obj-functor-Category representing-arrow-Category C f true

  mor-arrow-Category :
    (f : obj-Category arrow-Category) →
    hom-Category C (dom-arrow-Category f) (cod-arrow-Category f)
  mor-arrow-Category f =
    hom-functor-Category representing-arrow-Category C f star

  make-arrow-Category :
    total-hom-Category C →
    obj-Category arrow-Category
  pr1 (make-arrow-Category f) true = pr1 (pr2 f)
  pr1 (make-arrow-Category f) false = pr1 f
  pr1 (pr2 (make-arrow-Category f)) {true} {true} star = id-hom-Category C
  pr1 (pr2 (make-arrow-Category f)) {false} {true} star = pr2 (pr2 f)
  pr1 (pr2 (make-arrow-Category f)) {false} {false} star = id-hom-Category C
  pr1 (pr2 (pr2 (make-arrow-Category f))) {true} {true} {true} star star =
    inv (left-unit-law-comp-hom-Category C _)
  pr1 (pr2 (pr2 (make-arrow-Category f))) {false} {true} {true} star star =
    inv (left-unit-law-comp-hom-Category C _)
  pr1 (pr2 (pr2 (make-arrow-Category f))) {false} {false} {true} star star =
    inv (right-unit-law-comp-hom-Category C _)
  pr1 (pr2 (pr2 (make-arrow-Category f))) {false} {false} {false} star star =
    inv (right-unit-law-comp-hom-Category C _)
  pr2 (pr2 (pr2 (make-arrow-Category f))) true = refl
  pr2 (pr2 (pr2 (make-arrow-Category f))) false = refl

  unmake-arrow-Category :
    obj-Category arrow-Category →
    total-hom-Category C
  unmake-arrow-Category f =
    dom-arrow-Category f ,
    ( cod-arrow-Category f ,
      mor-arrow-Category f)

  first' :
    (f : obj-Category arrow-Category) →
    obj-functor-Category representing-arrow-Category C (make-arrow-Category (unmake-arrow-Category f)) ~ obj-functor-Category representing-arrow-Category C f
  first' f true = refl
  first' f false = refl

  first'' :
    (f : obj-Category arrow-Category) →
    coherence-htpy-map-Category representing-arrow-Category C (map-functor-Category representing-arrow-Category C (make-arrow-Category (unmake-arrow-Category f))) (map-functor-Category representing-arrow-Category C f) (first' f)
  first'' f {true} {true} star = {!!}
  first'' f {false} {true} star = {!!}
  first'' f {false} {false} star = {!!}

  first : make-arrow-Category ∘ unmake-arrow-Category ~ id
  first x =
    eq-htpy-functor-Category representing-arrow-Category C _ _
      ({!!} , {!!})

--  obj-arrow-Precategory : UU (l1 ⊔ l2)
--  obj-arrow-Precategory = total-hom-Precategory C
--
--  cod-arrow-Precategory : obj-arrow-Precategory → obj-Precategory C
--  cod-arrow-Precategory x = pr1 (pr2 x)
--
--  dom-arrow-Precategory : obj-arrow-Precategory → obj-Precategory C
--  dom-arrow-Precategory x = pr1 x
--
--  mor-arrow-Precategory : (f : obj-arrow-Precategory) →
--    hom-Precategory C (dom-arrow-Precategory f) (cod-arrow-Precategory f)
--  mor-arrow-Precategory x = pr2 (pr2 x)
--
--  hom-arrow-Precategory : (f g : obj-arrow-Precategory) → UU l2
--  hom-arrow-Precategory f g =
--    Σ ( ( hom-Precategory C
--          ( dom-total-hom-Precategory C f)
--          ( dom-total-hom-Precategory C g)) ×
--        ( hom-Precategory C
--          ( cod-total-hom-Precategory C f)
--          ( cod-total-hom-Precategory C g)))
--      ( λ uv →
--        coherence-square-hom-Precategory C
--          ( pr1 uv)
--          ( mor-total-hom-Precategory C f)
--          ( mor-total-hom-Precategory C g)
--          ( pr2 uv))
--
--  dom-hom-arrow-Precategory : {f g : obj-arrow-Precategory}
--    (u : hom-arrow-Precategory f g) →
--    hom-Precategory C (dom-arrow-Precategory f) (dom-arrow-Precategory g)
--  dom-hom-arrow-Precategory u = pr1 (pr1 u)
--
--  cod-hom-arrow-Precategory : {f g : obj-arrow-Precategory}
--    (u : hom-arrow-Precategory f g) →
--    hom-Precategory C (cod-arrow-Precategory f) (cod-arrow-Precategory g)
--  cod-hom-arrow-Precategory u = pr2 (pr1 u)
--
--  square-hom-arrow-Precategory : {f g : obj-arrow-Precategory}
--    (u : hom-arrow-Precategory f g) →
--    coherence-square-hom-Precategory C
--      ( dom-hom-arrow-Precategory u)
--      ( mor-total-hom-Precategory C f)
--      ( mor-total-hom-Precategory C g)
--      ( cod-hom-arrow-Precategory u)
--  square-hom-arrow-Precategory u = pr2 u
--
--  hom-set-arrow-Precategory : (f g : obj-arrow-Precategory) → Set l2
--  hom-set-arrow-Precategory f g =
--    Σ-Set
--      ( hom-set-Precategory C
--        ( dom-total-hom-Precategory C f)
--        ( dom-total-hom-Precategory C g))
--      ( λ u →
--        Σ-Set
--          ( hom-set-Precategory C
--            ( cod-total-hom-Precategory C f)
--            ( cod-total-hom-Precategory C g))
--          ( λ v →
--            truncated-type-Prop _
--              ( ( _ ),
--                ( is-prop-coherence-square-hom-Precategory C
--                  ( u)
--                  ( mor-total-hom-Precategory C f)
--                  ( mor-total-hom-Precategory C g)
--                  ( v)))))
--
--  comp-hom-arrow-Precategory :
--    {f g h : obj-arrow-Precategory} →
--    hom-arrow-Precategory g h →
--    hom-arrow-Precategory f g →
--    hom-arrow-Precategory f h
--  comp-hom-arrow-Precategory v u =
--    ( ( comp-hom-Precategory C
--        ( dom-hom-arrow-Precategory v)
--        ( dom-hom-arrow-Precategory u)),
--      ( comp-hom-Precategory C
--        ( cod-hom-arrow-Precategory v)
--        ( cod-hom-arrow-Precategory u))) ,
--    ( comp-coherence-square-hom-Precategory C _ _ _ _ _ _ _
--      ( square-hom-arrow-Precategory u)
--      ( square-hom-arrow-Precategory v))
--
--  id-hom-arrow-Precategory :
--    {f : obj-arrow-Precategory} →
--    hom-arrow-Precategory f f
--  id-hom-arrow-Precategory =
--    ( ( id-hom-Precategory C) ,
--      ( id-hom-Precategory C)) ,
--    ( left-unit-law-comp-hom-Precategory C _) ∙
--    ( inv (right-unit-law-comp-hom-Precategory C _))
--
--  left-unit-law-comp-hom-arrow-Precategory :
--    {f g : obj-arrow-Precategory}
--    (u : hom-arrow-Precategory f g) →
--    comp-hom-arrow-Precategory id-hom-arrow-Precategory u ＝ u
--  left-unit-law-comp-hom-arrow-Precategory u =
--    eq-pair-Σ
--      ( eq-pair
--        ( left-unit-law-comp-hom-Precategory C _)
--        ( left-unit-law-comp-hom-Precategory C _))
--      ( eq-is-prop (is-set-hom-Precategory C _ _ _ _))
--    
--  right-unit-law-comp-hom-arrow-Precategory :
--    {f g : obj-arrow-Precategory}
--    (u : hom-arrow-Precategory f g) →
--    comp-hom-arrow-Precategory u id-hom-arrow-Precategory ＝ u
--  right-unit-law-comp-hom-arrow-Precategory u =
--    eq-pair-Σ
--      ( eq-pair
--        ( right-unit-law-comp-hom-Precategory C _)
--        ( right-unit-law-comp-hom-Precategory C _))
--      ( eq-is-prop (is-set-hom-Precategory C _ _ _ _))
--
--  associative-comp-hom-arrow-Precategory :
--    {x y z w : obj-arrow-Precategory}
--    (h : hom-arrow-Precategory z w)
--    (g : hom-arrow-Precategory y z)
--    (f : hom-arrow-Precategory x y) →
--    ( comp-hom-arrow-Precategory
--      ( comp-hom-arrow-Precategory h g)
--      ( f)) ＝
--    ( comp-hom-arrow-Precategory
--      ( h)
--      ( comp-hom-arrow-Precategory g f))
--  associative-comp-hom-arrow-Precategory h g f =
--    eq-pair-Σ
--      ( eq-pair
--        ( associative-comp-hom-Precategory C _ _ _)
--        ( associative-comp-hom-Precategory C _ _ _))
--      ( eq-is-prop (is-set-hom-Precategory C _ _ _ _))
