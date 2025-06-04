# Arrow categories

```agda
module category-theory.arrow-categories where

open import category-theory.representing-arrow-category public
```

<details><summary>Imports</summary>

```agda
open import category-theory.adjunctions-precategories
open import category-theory.commuting-squares-of-morphisms-in-precategories
open import category-theory.functors-precategories
open import category-theory.maps-precategories
open import category-theory.categories
open import category-theory.isomorphisms-in-precategories
open import category-theory.isomorphisms-in-categories
open import category-theory.natural-transformations-functors-precategories
open import category-theory.natural-transformations-maps-precategories
open import category-theory.pointed-endofunctors-precategories
open import category-theory.precategories
open import category-theory.category-of-functors
open import category-theory.precategory-of-functors

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
  {l1 l2 : Level} (C : Precategory l1 l2)
  (let C1 = functor-precategory-Precategory representing-arrow-Precategory C)
  where

  obj-arrow-Precategory : UU (l1 ⊔ l2)
  obj-arrow-Precategory =
    Σ ( (obj-Precategory C) × (obj-Precategory C))
      ( λ xy → hom-Precategory C (pr1 xy) (pr2 xy))

  dom-obj-arrow-Precategory : obj-arrow-Precategory → obj-Precategory C
  dom-obj-arrow-Precategory = pr1 ∘ pr1

  cod-obj-arrow-Precategory : obj-arrow-Precategory → obj-Precategory C
  cod-obj-arrow-Precategory = pr2 ∘ pr1

  mor-obj-arrow-Precategory : (f : obj-arrow-Precategory) →
    hom-Precategory C
      ( dom-obj-arrow-Precategory f)
      ( cod-obj-arrow-Precategory f)
  mor-obj-arrow-Precategory = pr2

  hom-arrow-Precategory : (f g : obj-arrow-Precategory) → UU l2
  hom-arrow-Precategory f g =
    Σ ( ( hom-Precategory C
          ( dom-obj-arrow-Precategory f)
          ( dom-obj-arrow-Precategory g)) ×
        ( hom-Precategory C
          ( cod-obj-arrow-Precategory f)
          ( cod-obj-arrow-Precategory g)))
      ( λ uv →
        coherence-square-hom-Precategory C
          ( pr1 uv)
          ( mor-obj-arrow-Precategory f)
          ( mor-obj-arrow-Precategory g)
          ( pr2 uv))

  dom-hom-arrow-Precategory : {f g : obj-arrow-Precategory}
    (u : hom-arrow-Precategory f g) →
    hom-Precategory C
      ( dom-obj-arrow-Precategory f)
      ( dom-obj-arrow-Precategory g)
  dom-hom-arrow-Precategory u = pr1 (pr1 u)

  cod-hom-arrow-Precategory : {f g : obj-arrow-Precategory}
    (u : hom-arrow-Precategory f g) →
    hom-Precategory C
      ( cod-obj-arrow-Precategory f)
      ( cod-obj-arrow-Precategory g)
  cod-hom-arrow-Precategory u = pr2 (pr1 u)

  square-hom-arrow-Precategory : {f g : obj-arrow-Precategory}
    (u : hom-arrow-Precategory f g) →
    coherence-square-hom-Precategory C
      ( dom-hom-arrow-Precategory u)
      ( mor-obj-arrow-Precategory f)
      ( mor-obj-arrow-Precategory g)
      ( cod-hom-arrow-Precategory u)
  square-hom-arrow-Precategory u = pr2 u

  is-set-hom-arrow-Precategory :
    (f g : obj-arrow-Precategory) → is-set (hom-arrow-Precategory f g)
  is-set-hom-arrow-Precategory f g =
    is-set-Σ
      (is-set-product
        ( is-set-hom-Precategory C
          ( dom-obj-arrow-Precategory f)
          ( dom-obj-arrow-Precategory g))
        ( is-set-hom-Precategory C
          ( cod-obj-arrow-Precategory f)
          ( cod-obj-arrow-Precategory g)))
      ( λ uv →
        is-trunc-is-prop _
          ( is-prop-coherence-square-hom-Precategory C
            ( pr1 uv)
            ( mor-obj-arrow-Precategory f)
            ( mor-obj-arrow-Precategory g)
            ( pr2 uv)))

  hom-set-arrow-Precategory :
    (f g : obj-arrow-Precategory) → Set l2
  hom-set-arrow-Precategory f g =
    ( hom-arrow-Precategory f g) ,
    ( is-set-hom-arrow-Precategory f g)

  comp-hom-arrow-Precategory :
    {f g h : obj-arrow-Precategory} →
    hom-arrow-Precategory g h →
    hom-arrow-Precategory f g →
    hom-arrow-Precategory f h
  comp-hom-arrow-Precategory v u =
    ( ( comp-hom-Precategory C
        ( dom-hom-arrow-Precategory v)
        ( dom-hom-arrow-Precategory u)),
      ( comp-hom-Precategory C
        ( cod-hom-arrow-Precategory v)
        ( cod-hom-arrow-Precategory u))) ,
    ( pasting-horizontal-coherence-square-hom-Precategory C _ _ _ _ _ _ _
      ( square-hom-arrow-Precategory u)
      ( square-hom-arrow-Precategory v))

  id-hom-arrow-Precategory :
    {f : obj-arrow-Precategory} →
    hom-arrow-Precategory f f
  id-hom-arrow-Precategory =
    ( ( id-hom-Precategory C) ,
      ( id-hom-Precategory C)) ,
    ( left-unit-law-comp-hom-Precategory C _) ∙
    ( inv (right-unit-law-comp-hom-Precategory C _))

  left-unit-law-comp-hom-arrow-Precategory :
    {f g : obj-arrow-Precategory}
    (u : hom-arrow-Precategory f g) →
    comp-hom-arrow-Precategory id-hom-arrow-Precategory u ＝ u
  left-unit-law-comp-hom-arrow-Precategory u =
    eq-pair-Σ
      ( eq-pair
        ( left-unit-law-comp-hom-Precategory C _)
        ( left-unit-law-comp-hom-Precategory C _))
      ( eq-is-prop (is-set-hom-Precategory C _ _ _ _))
    
  right-unit-law-comp-hom-arrow-Precategory :
    {f g : obj-arrow-Precategory}
    (u : hom-arrow-Precategory f g) →
    comp-hom-arrow-Precategory u id-hom-arrow-Precategory ＝ u
  right-unit-law-comp-hom-arrow-Precategory u =
    eq-pair-Σ
      ( eq-pair
        ( right-unit-law-comp-hom-Precategory C _)
        ( right-unit-law-comp-hom-Precategory C _))
      ( eq-is-prop (is-set-hom-Precategory C _ _ _ _))

  associative-comp-hom-arrow-Precategory :
    {x y z w : obj-arrow-Precategory}
    (h : hom-arrow-Precategory z w)
    (g : hom-arrow-Precategory y z)
    (f : hom-arrow-Precategory x y) →
    ( comp-hom-arrow-Precategory
      ( comp-hom-arrow-Precategory h g)
      ( f)) ＝
    ( comp-hom-arrow-Precategory
      ( h)
      ( comp-hom-arrow-Precategory g f))
  associative-comp-hom-arrow-Precategory h g f =
    eq-pair-Σ
      ( eq-pair
        ( associative-comp-hom-Precategory C _ _ _)
        ( associative-comp-hom-Precategory C _ _ _))
      ( eq-is-prop (is-set-hom-Precategory C _ _ _ _))

  arrow-Precategory : Precategory (l1 ⊔ l2) l2
  arrow-Precategory =
    make-Precategory
      ( obj-arrow-Precategory)
      ( hom-set-arrow-Precategory)
      ( comp-hom-arrow-Precategory)
      ( λ x → id-hom-arrow-Precategory)
      ( associative-comp-hom-arrow-Precategory)
      ( left-unit-law-comp-hom-arrow-Precategory)
      ( right-unit-law-comp-hom-arrow-Precategory)
```

```agda
  dom-C1 :
    (f : obj-Precategory C1) →
    obj-Precategory C
  dom-C1 f = obj-functor-Precategory representing-arrow-Precategory C f false

  cod-C1 :
    (f : obj-Precategory C1) →
    obj-Precategory C
  cod-C1 f = obj-functor-Precategory representing-arrow-Precategory C f true

  mor-C1 :
    (f : obj-Precategory C1) →
    hom-Precategory C (dom-C1 f) (cod-C1 f)
  mor-C1 f = hom-functor-Precategory representing-arrow-Precategory C f star

--  make-arrow-Precategory :
--    total-hom-Precategory C →
--    obj-Precategory C1
--  pr1 (make-arrow-Precategory f) true = pr1 (pr2 f)
--  pr1 (make-arrow-Precategory f) false = pr1 f
--  pr1 (pr2 (make-arrow-Precategory f)) {true} {true} star = id-hom-Precategory C
--  pr1 (pr2 (make-arrow-Precategory f)) {false} {true} star = pr2 (pr2 f)
--  pr1 (pr2 (make-arrow-Precategory f)) {false} {false} star = id-hom-Precategory C
--  pr1 (pr2 (pr2 (make-arrow-Precategory f))) {true} {true} {true} star star =
--    inv (left-unit-law-comp-hom-Precategory C _)
--  pr1 (pr2 (pr2 (make-arrow-Precategory f))) {false} {true} {true} star star =
--    inv (left-unit-law-comp-hom-Precategory C _)
--  pr1 (pr2 (pr2 (make-arrow-Precategory f))) {false} {false} {true} star star =
--    inv (right-unit-law-comp-hom-Precategory C _)
--  pr1 (pr2 (pr2 (make-arrow-Precategory f))) {false} {false} {false} star star =
--    inv (right-unit-law-comp-hom-Precategory C _)
--  pr2 (pr2 (pr2 (make-arrow-Precategory f))) true = refl
--  pr2 (pr2 (pr2 (make-arrow-Precategory f))) false = refl
--
--  unmake-arrow-Precategory :
--    obj-Precategory arrow-Precategory →
--    total-hom-Precategory C
--  unmake-arrow-Precategory f =
--    dom-obj-arrow-Precategory f ,
--    ( cod-arrow-Precategory f ,
--      mor-arrow-Precategory f)
--
--  obj-htpy-make-arrow-Precategory :
--    (f : obj-Precategory arrow-Precategory) →
--    obj-functor-Precategory representing-arrow-Precategory C (make-arrow-Precategory (unmake-arrow-Precategory f)) ~ obj-functor-Precategory representing-arrow-Precategory C f
--  obj-htpy-make-arrow-Precategory f true = refl
--  obj-htpy-make-arrow-Precategory f false = refl
--
--  coh-htpy-make-arrow-Precategory :
--    (f : obj-Precategory arrow-Precategory) →
--    coherence-htpy-map-Precategory representing-arrow-Precategory C
--      ( map-functor-Precategory representing-arrow-Precategory C
--        ( make-arrow-Precategory (unmake-arrow-Precategory f)))
--      ( map-functor-Precategory representing-arrow-Precategory C f)
--      ( obj-htpy-make-arrow-Precategory f)
--  coh-htpy-make-arrow-Precategory f {true} {true} star =
--    right-unit-law-comp-hom-Precategory C _ ∙
--    preserves-id-functor-Precategory representing-arrow-Precategory C f _ ∙
--    inv (right-unit-law-comp-hom-Precategory C _)
--  coh-htpy-make-arrow-Precategory f {false} {true} star =
--    right-unit-law-comp-hom-Precategory C _ ∙
--    inv (left-unit-law-comp-hom-Precategory C _)
--  coh-htpy-make-arrow-Precategory f {false} {false} star =
--    right-unit-law-comp-hom-Precategory C _ ∙
--    preserves-id-functor-Precategory representing-arrow-Precategory C f _ ∙
--    inv (right-unit-law-comp-hom-Precategory C _)
--
--  htpy-make-arrow-Precategory : make-arrow-Precategory ∘ unmake-arrow-Precategory ~ id
--  htpy-make-arrow-Precategory x =
--    eq-htpy-functor-Precategory representing-arrow-Precategory C _ _
--      (obj-htpy-make-arrow-Precategory x , coh-htpy-make-arrow-Precategory x)
--
--  htpy-make-arrow-Precategory' : unmake-arrow-Precategory ∘ make-arrow-Precategory ~ id
--  htpy-make-arrow-Precategory' (x , y , f) = refl

  module _
    (is-cat-C : is-category-Precategory C)
    (let CC = (C , is-cat-C))
    where

    dom-iso : (f g : obj-arrow-Precategory) →
      iso-Precategory arrow-Precategory f g →
      iso-Precategory C (dom-obj-arrow-Precategory f) (dom-obj-arrow-Precategory g)
    pr1 (dom-iso f g I) =
      dom-hom-arrow-Precategory (hom-iso-Precategory arrow-Precategory I)
    pr1 (pr2 (dom-iso f g I)) =
      dom-hom-arrow-Precategory (hom-inv-iso-Precategory arrow-Precategory I)
    pr1 (pr2 (pr2 (dom-iso f g I))) =
      ap
        ( dom-hom-arrow-Precategory)
        ( is-section-hom-inv-iso-Precategory arrow-Precategory I)
    pr2 (pr2 (pr2 (dom-iso f g I))) =
      ap
        ( dom-hom-arrow-Precategory)
        ( is-retraction-hom-inv-iso-Precategory arrow-Precategory I)

    cod-iso : (f g : obj-arrow-Precategory) →
      iso-Precategory arrow-Precategory f g →
      iso-Precategory C (cod-obj-arrow-Precategory f) (cod-obj-arrow-Precategory g)
    pr1 (cod-iso f g I) =
      cod-hom-arrow-Precategory (hom-iso-Precategory arrow-Precategory I)
    pr1 (pr2 (cod-iso f g I)) =
      cod-hom-arrow-Precategory (hom-inv-iso-Precategory arrow-Precategory I)
    pr1 (pr2 (pr2 (cod-iso f g I))) =
      ap
        ( cod-hom-arrow-Precategory)
        ( is-section-hom-inv-iso-Precategory arrow-Precategory I)
    pr2 (pr2 (pr2 (cod-iso f g I))) =
      ap
        ( cod-hom-arrow-Precategory)
        ( is-retraction-hom-inv-iso-Precategory arrow-Precategory I)

    is-category-arrow-Precategory : is-category-Precategory arrow-Precategory
    is-category-arrow-Precategory f g = {!!} where
      back : iso-Precategory arrow-Precategory f g → f ＝ g
      back u =
        eq-pair-Σ
          ( eq-pair
            ( eq-iso-Category CC (dom-iso f g u))
            ( eq-iso-Category CC (cod-iso f g u)))
          ( ( tr-eq-pair _
              ( eq-iso-Category CC (dom-iso f g u))
              ( eq-iso-Category CC (cod-iso f g u))
              ( mor-obj-arrow-Precategory f)) ∙
            ( ap
              ( tr
                ( hom-Precategory C (dom-obj-arrow-Precategory g))
                ( eq-iso-Category CC (cod-iso f g u)))
              ( compute-right-tr-eq-iso-Category CC (pr2 f) (dom-iso f g u))) ∙
            ( compute-left-tr-eq-iso-Category CC (cod-iso f g u) _) ∙
            ( {!!}))

--  arrow-Category : Category (l1 ⊔ l2) l2
--  arrow-Category =
--    functor-category-Category representing-arrow-Category C
--
--  dom-obj-arrow-Category : obj-Category arrow-Category → obj-Category C
--  dom-obj-arrow-Category f =
--    obj-functor-Category representing-arrow-Category C f false
--
--  cod-arrow-Category : obj-Category arrow-Category → obj-Category C
--  cod-arrow-Category f =
--    obj-functor-Category representing-arrow-Category C f true
--
--  mor-arrow-Category :
--    (f : obj-Category arrow-Category) →
--    hom-Category C (dom-obj-arrow-Category f) (cod-arrow-Category f)
--  mor-arrow-Category f =
--    hom-functor-Category representing-arrow-Category C f star
--
--  functor-dom-obj-arrow-Category : functor-Category arrow-Category C
--  functor-dom-obj-arrow-Category =
--    ev-functor-Category representing-arrow-Category C false
--
--  functor-cod-arrow-Category : functor-Category arrow-Category C
--  functor-cod-arrow-Category =
--    ev-functor-Category representing-arrow-Category C true
--
--```
