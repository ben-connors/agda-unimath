# Arrow categories

```agda
module category-theory.arrow-precategories where

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
open import foundation.equivalences
open import foundation.embeddings
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
open import foundation-core.subtypes
open import foundation-core.transport-along-identifications
```

</details>

## Idea

The {{#concept "arrow precategory" Disambiguation="of a precategory" Agda=arrow-Precategory}} of a [precategory](category-theory.precategories.md) `C` is the precategory with objects the total hom types of `C` (i.e. triples `(x : C, y : C, f : x → y)`) and morphisms `(x, y, f) → (x', y', g)` pairs of morphisms in `C` `(u : x → x', v : y → y')` giving commutative squares in `C`.

## Definitions

### Direct definition
```
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
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

  eq-hom-arrow-Precategory :
    (f g : obj-arrow-Precategory)
    (u v : hom-arrow-Precategory f g) →
    dom-hom-arrow-Precategory u ＝ dom-hom-arrow-Precategory v →
    cod-hom-arrow-Precategory u ＝ cod-hom-arrow-Precategory v →
    u ＝ v
  eq-hom-arrow-Precategory f g u v p q =
    eq-pair-Σ
      (eq-pair p q)
      (eq-is-prop (is-set-hom-Precategory C _ _ _ _))

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

### As a functor precategory

Alternatively, we can define the arrow precategory to be the [precategory of functors](category-theory.precategory-of-functors.md) from the [representing arrow category](category-theory.representing-arrow-category.md) into `C`.

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  where

  represented-arrow-Precategory : Precategory (l1 ⊔ l2) l2
  represented-arrow-Precategory =
    functor-precategory-Precategory representing-arrow-Precategory C

  dom-represented-arrow-Precategory :
    (f : obj-Precategory represented-arrow-Precategory) →
    obj-Precategory C
  dom-represented-arrow-Precategory f =
    obj-functor-Precategory representing-arrow-Precategory C f false

  cod-represented-arrow-Precategory :
    (f : obj-Precategory represented-arrow-Precategory) →
    obj-Precategory C
  cod-represented-arrow-Precategory f =
    obj-functor-Precategory representing-arrow-Precategory C f true

  mor-represented-arrow-Precategory :
    (f : obj-Precategory represented-arrow-Precategory) →
    hom-Precategory C
      ( dom-represented-arrow-Precategory f)
      ( cod-represented-arrow-Precategory f)
  mor-represented-arrow-Precategory f =
    hom-functor-Precategory representing-arrow-Precategory C f star
```

## Properties

We can go between the two definitions:

TODO: There is most of the data of a pair of functors here.

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  where

  make-represented-arrow-Precategory :
    obj-arrow-Precategory C →
    obj-Precategory (represented-arrow-Precategory C)
  pr1 (make-represented-arrow-Precategory f) true = pr2 (pr1 f)
  pr1 (make-represented-arrow-Precategory f) false = pr1 (pr1 f)
  pr1 (pr2 (make-represented-arrow-Precategory f)) {true} {true} star =
    id-hom-Precategory C
  pr1 (pr2 (make-represented-arrow-Precategory f)) {false} {true} star = pr2 f
  pr1 (pr2 (make-represented-arrow-Precategory f)) {false} {false} star =
    id-hom-Precategory C
  pr1 (pr2 (pr2 (make-represented-arrow-Precategory f)))
    {true} {true} {true} star star =
      inv (left-unit-law-comp-hom-Precategory C _)
  pr1 (pr2 (pr2 (make-represented-arrow-Precategory f)))
    {false} {true} {true} star star =
      inv (left-unit-law-comp-hom-Precategory C _)
  pr1 (pr2 (pr2 (make-represented-arrow-Precategory f)))
    {false} {false} {true} star star =
      inv (right-unit-law-comp-hom-Precategory C _)
  pr1 (pr2 (pr2 (make-represented-arrow-Precategory f)))
    {false} {false} {false} star star =
      inv (right-unit-law-comp-hom-Precategory C _)
  pr2 (pr2 (pr2 (make-represented-arrow-Precategory f))) true = refl
  pr2 (pr2 (pr2 (make-represented-arrow-Precategory f))) false = refl

  unmake-represented-arrow-Precategory :
    obj-Precategory (represented-arrow-Precategory C) →
    obj-arrow-Precategory C
  unmake-represented-arrow-Precategory f =
    ( dom-represented-arrow-Precategory C f ,
      cod-represented-arrow-Precategory C f) ,
    mor-represented-arrow-Precategory C f

  obj-is-retraction-make-represented-arrow-Precategory :
    (f : obj-Precategory (represented-arrow-Precategory C)) →
    obj-functor-Precategory representing-arrow-Precategory C
      ( make-represented-arrow-Precategory
        ( unmake-represented-arrow-Precategory f)) ~
    obj-functor-Precategory representing-arrow-Precategory C f
  obj-is-retraction-make-represented-arrow-Precategory f true = refl
  obj-is-retraction-make-represented-arrow-Precategory f false = refl

  coh-is-retraction-make-represented-arrow-Precategory :
    (f : obj-Precategory (represented-arrow-Precategory C)) →
    coherence-htpy-map-Precategory representing-arrow-Precategory C
      ( map-functor-Precategory representing-arrow-Precategory C
        ( make-represented-arrow-Precategory
          ( unmake-represented-arrow-Precategory f)))
      ( map-functor-Precategory representing-arrow-Precategory C f)
      ( obj-is-retraction-make-represented-arrow-Precategory f)
  coh-is-retraction-make-represented-arrow-Precategory f {true} {true} star =
    right-unit-law-comp-hom-Precategory C _ ∙
    preserves-id-functor-Precategory representing-arrow-Precategory C f _ ∙
    inv (right-unit-law-comp-hom-Precategory C _)
  coh-is-retraction-make-represented-arrow-Precategory f {false} {true} star =
    right-unit-law-comp-hom-Precategory C _ ∙
    inv (left-unit-law-comp-hom-Precategory C _)
  coh-is-retraction-make-represented-arrow-Precategory f {false} {false} star =
    right-unit-law-comp-hom-Precategory C _ ∙
    preserves-id-functor-Precategory representing-arrow-Precategory C f _ ∙
    inv (right-unit-law-comp-hom-Precategory C _)

  is-retraction-make-represented-arrow-Precategory :
    make-represented-arrow-Precategory ∘ unmake-represented-arrow-Precategory ~
    id
  is-retraction-make-represented-arrow-Precategory x =
    eq-htpy-functor-Precategory representing-arrow-Precategory C _ _
      ( obj-is-retraction-make-represented-arrow-Precategory x ,
        coh-is-retraction-make-represented-arrow-Precategory x)

  is-section-make-represented-arrow-Precategory :
    unmake-represented-arrow-Precategory ∘ make-represented-arrow-Precategory ~
    id
  is-section-make-represented-arrow-Precategory ((x , y) , f) = refl

  equiv-make-represented-arrow-Precategory :
    obj-arrow-Precategory C ≃ obj-Precategory (represented-arrow-Precategory C)
  pr1 equiv-make-represented-arrow-Precategory =
    make-represented-arrow-Precategory
  pr2 equiv-make-represented-arrow-Precategory =
    is-equiv-is-invertible
      ( unmake-represented-arrow-Precategory)
      ( is-retraction-make-represented-arrow-Precategory)
      ( is-section-make-represented-arrow-Precategory)

  module _
    (f g : obj-arrow-Precategory C)
    where

    hom-arrow-to-representing-Precategory :
      hom-arrow-Precategory C f g →
      hom-Precategory
        ( represented-arrow-Precategory C)
        ( make-represented-arrow-Precategory f)
        ( make-represented-arrow-Precategory g)
    pr1 (hom-arrow-to-representing-Precategory ((u , v) , H)) true = v
    pr1 (hom-arrow-to-representing-Precategory ((u , v) , H)) false = u
    pr2 (hom-arrow-to-representing-Precategory ((u , v) , H))
      {true} {true} star =
        left-unit-law-comp-hom-Precategory C _ ∙
        inv (right-unit-law-comp-hom-Precategory C _)
    pr2 (hom-arrow-to-representing-Precategory ((u , v) , H))
      {false} {true} star = inv H
    pr2 (hom-arrow-to-representing-Precategory ((u , v) , H))
      {false} {false} star =
        left-unit-law-comp-hom-Precategory C _ ∙
        inv (right-unit-law-comp-hom-Precategory C _)

    hom-representing-to-arrow-Precategory : 
      hom-Precategory
        ( represented-arrow-Precategory C)
        ( make-represented-arrow-Precategory f)
        ( make-represented-arrow-Precategory g) →
      hom-arrow-Precategory C f g
    pr1 (pr1 (hom-representing-to-arrow-Precategory x)) = (pr1 x) false
    pr2 (pr1 (hom-representing-to-arrow-Precategory x)) = (pr1 x) true
    pr2 (hom-representing-to-arrow-Precategory x) =
      inv
        ( naturality-natural-transformation-Precategory
          ( representing-arrow-Precategory)
          ( C)
          (make-represented-arrow-Precategory f)
          (make-represented-arrow-Precategory g)
          ( x)
          ( star))

    is-section-hom-arrow-to-representing-Precategory :
      hom-representing-to-arrow-Precategory ∘
      hom-arrow-to-representing-Precategory ~
      id
    is-section-hom-arrow-to-representing-Precategory ((u , v) , H) =
      eq-pair-Σ
        (eq-pair refl refl)
        (eq-is-prop (is-set-hom-Precategory C _ _ _ _))

    is-retraction-hom-arrow-to-representing-Precategory :
      hom-arrow-to-representing-Precategory ∘
      hom-representing-to-arrow-Precategory ~
      id
    is-retraction-hom-arrow-to-representing-Precategory x =
      eq-htpy-hom-family-natural-transformation-Precategory
        ( representing-arrow-Precategory)
        ( C)
        ( make-represented-arrow-Precategory f)
        ( make-represented-arrow-Precategory g)
        ( _)
        ( _)
        ( λ { true → refl ; false → refl })

  is-iso-arrow-to-representing-Precategory :
    (f g : obj-arrow-Precategory C) (u : hom-arrow-Precategory C f g) →
    is-iso-Precategory (arrow-Precategory C) u →
    is-iso-Precategory (represented-arrow-Precategory C)
      { make-represented-arrow-Precategory f}
      { make-represented-arrow-Precategory g}
      ( hom-arrow-to-representing-Precategory f g u)
  pr1 (is-iso-arrow-to-representing-Precategory f g u (v , H , G)) =
    hom-arrow-to-representing-Precategory g f v
  pr1 (pr2 (is-iso-arrow-to-representing-Precategory f g u (v , H , G))) =
    eq-htpy-hom-family-natural-transformation-Precategory
      ( representing-arrow-Precategory)
      ( C)
      ( make-represented-arrow-Precategory g)
      ( make-represented-arrow-Precategory g)
      ( _)
      ( _)
      ( λ {
        true → ap (cod-hom-arrow-Precategory C) H ;
        false → ap (dom-hom-arrow-Precategory C) H })
  pr2 (pr2 (is-iso-arrow-to-representing-Precategory f g u (v , H , G))) =
    eq-htpy-hom-family-natural-transformation-Precategory
      ( representing-arrow-Precategory)
      ( C)
      ( make-represented-arrow-Precategory f)
      ( make-represented-arrow-Precategory f)
      ( _)
      ( _)
      ( λ {
        true → ap (cod-hom-arrow-Precategory C) G ;
        false → ap (dom-hom-arrow-Precategory C) G })

  is-iso-representing-to-arrow-Precategory :
    (f g : obj-arrow-Precategory C)
    (u :
      hom-Precategory
        ( represented-arrow-Precategory C)
        ( make-represented-arrow-Precategory f)
        ( make-represented-arrow-Precategory g)) →
    is-iso-Precategory (represented-arrow-Precategory C)
      { make-represented-arrow-Precategory f}
      { make-represented-arrow-Precategory g}
      ( hom-arrow-to-representing-Precategory f g
        ( hom-representing-to-arrow-Precategory f g u)) →
    is-iso-Precategory
      ( arrow-Precategory C)
      ( hom-representing-to-arrow-Precategory f g u)
  pr1 (is-iso-representing-to-arrow-Precategory f g u (v , H , G)) =
    hom-representing-to-arrow-Precategory g f v
  pr1 (pr2 (is-iso-representing-to-arrow-Precategory f g u (v , H , G))) =
    eq-hom-arrow-Precategory C g g _ _
      ( ap (λ x → (pr1 x) false) H)
      ( ap (λ x → (pr1 x) true) H)
  pr2 (pr2 (is-iso-representing-to-arrow-Precategory f g u (v , H , G))) =
    eq-hom-arrow-Precategory C f f _ _
      ( ap (λ x → (pr1 x) false) G)
      ( ap (λ x → (pr1 x) true) G)

  iso-arrow-to-representing-Precategory :
    (f g : obj-arrow-Precategory C) →
    iso-Precategory (arrow-Precategory C) f g →
    iso-Precategory
      ( represented-arrow-Precategory C)
      ( make-represented-arrow-Precategory f)
      ( make-represented-arrow-Precategory g)
  iso-arrow-to-representing-Precategory f g (u , I) =
    hom-arrow-to-representing-Precategory f g u ,
    is-iso-arrow-to-representing-Precategory f g u I

  iso-representing-to-arrow-Precategory :
    (f g : obj-arrow-Precategory C) →
    iso-Precategory
      ( represented-arrow-Precategory C)
      ( make-represented-arrow-Precategory f)
      ( make-represented-arrow-Precategory g) →
    iso-Precategory (arrow-Precategory C) f g
  iso-representing-to-arrow-Precategory f g (u , I) =
    hom-representing-to-arrow-Precategory f g u ,
    is-iso-representing-to-arrow-Precategory f g u
      ( tr
        ( λ x →
          is-iso-Precategory (represented-arrow-Precategory C)
            { make-represented-arrow-Precategory f}
            { make-represented-arrow-Precategory g} x)
            ( inv
              ( is-retraction-hom-arrow-to-representing-Precategory f g u)) I)

  equiv-iso-representing-to-arrow-Precategory :
    (f g : obj-arrow-Precategory C) →
    iso-Precategory
      ( represented-arrow-Precategory C)
      ( make-represented-arrow-Precategory f)
      ( make-represented-arrow-Precategory g) ≃
    iso-Precategory (arrow-Precategory C) f g
  pr1 (equiv-iso-representing-to-arrow-Precategory f g) =
    iso-representing-to-arrow-Precategory f g
  pr2 (equiv-iso-representing-to-arrow-Precategory f g) =
    is-equiv-is-invertible
      ( iso-arrow-to-representing-Precategory f g)
      ( λ x →
        eq-pair-Σ
          ( is-section-hom-arrow-to-representing-Precategory f g (pr1 x))
          ( eq-is-prop (is-prop-is-iso-Precategory (arrow-Precategory C) _)))
      ( λ x →
        eq-pair-Σ
          ( is-retraction-hom-arrow-to-representing-Precategory f g (pr1 x))
          ( eq-is-prop
            ( is-prop-is-iso-Precategory (represented-arrow-Precategory C)
              { make-represented-arrow-Precategory f}
              { make-represented-arrow-Precategory g}
              ( _))))

  module _
    (is-cat-C : is-category-Precategory C)
    where

    equiv-iso-eq-arrow-Precategory :
      (f g : obj-arrow-Precategory C) →
      (f ＝ g) ≃ iso-Precategory (arrow-Precategory C) f g
    equiv-iso-eq-arrow-Precategory f g = 
      (equiv-iso-representing-to-arrow-Precategory f g) ∘e
      (extensionality-obj-Category
        ( represented-arrow-Precategory C ,
          is-category-functor-precategory-is-category-Precategory
            ( representing-arrow-Precategory)
            ( C)
            ( is-cat-C))
        ( make-represented-arrow-Precategory f)
        (make-represented-arrow-Precategory g)) ∘e
      (equiv-ap-is-emb (is-emb-equiv equiv-make-represented-arrow-Precategory))

    compute-iso-eq-arrow-Precategory :
      (f g : obj-arrow-Precategory C) →
      iso-eq-Precategory (arrow-Precategory C) f g ~
      map-equiv (equiv-iso-eq-arrow-Precategory f g)
    compute-iso-eq-arrow-Precategory f g refl =
      eq-pair-Σ
        (eq-hom-arrow-Precategory C f g _ _ refl refl)
        (eq-is-prop (is-prop-is-iso-Precategory (arrow-Precategory C) _))

    abstract
      is-category-arrow-precategory-is-category-Precategory :
        is-category-Precategory (arrow-Precategory C)
      is-category-arrow-precategory-is-category-Precategory f g =
        is-equiv-htpy-equiv
          ( equiv-iso-eq-arrow-Precategory f g)
          ( compute-iso-eq-arrow-Precategory f g) 
```

```
module _
  {l1 l2 : Level} (C : Category l1 l2)
  where

  arrow-Category : Category (l1 ⊔ l2) l2
  pr1 arrow-Category = arrow-Precategory (precategory-Category C)
  pr2 arrow-Category =
    is-category-arrow-precategory-is-category-Precategory
      ( precategory-Category C)
      ( is-category-Category C)

  obj-arrow-Category : UU (l1 ⊔ l2)
  obj-arrow-Category = obj-arrow-Precategory (precategory-Category C)

  hom-arrow-Category : (f g : obj-arrow-Category) → UU l2
  hom-arrow-Category = hom-arrow-Precategory (precategory-Category C)

  dom-obj-arrow-Category : obj-arrow-Category → obj-Category C
  dom-obj-arrow-Category = pr1 ∘ pr1

  cod-obj-arrow-Category : obj-arrow-Category → obj-Category C
  cod-obj-arrow-Category = pr2 ∘ pr1

  mor-obj-arrow-Category : (f : obj-arrow-Category) →
    hom-Category C
      ( dom-obj-arrow-Category f)
      ( cod-obj-arrow-Category f)
  mor-obj-arrow-Category = pr2

  dom-hom-arrow-Category : {f g : obj-arrow-Category}
    (u : hom-arrow-Category f g) →
    hom-Category C
      ( dom-obj-arrow-Category f)
      ( dom-obj-arrow-Category g)
  dom-hom-arrow-Category u = pr1 (pr1 u)

  cod-hom-arrow-Category : {f g : obj-arrow-Category}
    (u : hom-arrow-Category f g) →
    hom-Category C
      ( cod-obj-arrow-Category f)
      ( cod-obj-arrow-Category g)
  cod-hom-arrow-Category u = pr2 (pr1 u)

  square-hom-arrow-Category : {f g : obj-arrow-Category}
    (u : hom-arrow-Category f g) →
    coherence-square-hom-Precategory (precategory-Category C)
      ( dom-hom-arrow-Category u)
      ( mor-obj-arrow-Category f)
      ( mor-obj-arrow-Category g)
      ( cod-hom-arrow-Category u)
  square-hom-arrow-Category u = pr2 u

  eq-hom-arrow-Category :
    (f g : obj-arrow-Category)
    (u v : hom-arrow-Category f g) →
    dom-hom-arrow-Category u ＝ dom-hom-arrow-Category v →
    cod-hom-arrow-Category u ＝ cod-hom-arrow-Category v →
    u ＝ v
  eq-hom-arrow-Category = eq-hom-arrow-Precategory (precategory-Category C)
```
