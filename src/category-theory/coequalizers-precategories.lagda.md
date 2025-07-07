# Coequalizers in Precategories

```agda
module category-theory.coequalizers-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.constant-functors
open import category-theory.precategories

open import foundation.action-on-identifications-functions
open import foundation.uniqueness-quantification
open import foundation.set-truncations
open import foundation.sets
open import category-theory.commuting-triangles-of-morphisms-in-precategories
open import foundation.homotopies

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.unit-type
open import foundation.universe-levels
```

</detail>

## Idea

A *coequalizer* of two morphisms `f, g : x → y` in a [precategory](category-theory.precategories.md) consists of:

- an object `w`; and
- a morphism `c : y → w` with `c ∘ f ＝ c ∘ g` such that
  - for any morphism `c' : y → w'` with `c' ∘ f ＝ c' ∘ g` there is a unique morphism `e : w → w'` with `e ∘ c ＝ c'`.

We say that `C` *has all coequalizers* if for every parallel pair of morphisms there is a choice of coequalizer.

## Definitions

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  where

  is-coequalizer-obj-Precategory :
    {x y : obj-Precategory C}
    (f g : hom-Precategory C x y)
    {w : obj-Precategory C}
    (q : hom-Precategory C y w) →
    comp-hom-Precategory C q f ＝ comp-hom-Precategory C q g →
    UU (l1 ⊔ l2)
  is-coequalizer-obj-Precategory {x} {y} f g {w} q α =
    {w' : obj-Precategory C}
    (q' : hom-Precategory C y w') →
    comp-hom-Precategory C q' f ＝ comp-hom-Precategory C q' g →
    uniquely-exists-structure
      ( hom-Precategory C w w')
      ( λ h → comp-hom-Precategory C h q ＝ q')

  coequalizer-obj-Precategory :
    {x y : obj-Precategory C}
    (f g : hom-Precategory C x y) →
    UU (l1 ⊔ l2)
  coequalizer-obj-Precategory {x} {y} f g =
    Σ ( obj-Precategory C)
      ( λ w →
        Σ ( hom-Precategory C y w)
          ( λ q →
            Σ ( comp-hom-Precategory C q f ＝ comp-hom-Precategory C q g)
              ( λ α →
                is-coequalizer-obj-Precategory f g q α)))

  has-all-coequalizer-obj-Precategory : UU (l1 ⊔ l2)
  has-all-coequalizer-obj-Precategory =
    {x y : obj-Precategory C}
    (f g : hom-Precategory C x y) →
    coequalizer-obj-Precategory f g

  module _
    {x y : obj-Precategory C}
    (f g : hom-Precategory C x y)
    (c : coequalizer-obj-Precategory f g)
    where

    obj-coequalizer-obj-Precategory : obj-Precategory C
    obj-coequalizer-obj-Precategory = pr1 c

    mor-coequalizer-obj-Precategory :
      hom-Precategory C y obj-coequalizer-obj-Precategory
    mor-coequalizer-obj-Precategory = pr1 (pr2 c)

    coh-coequalizer-obj-Precategory :
      comp-hom-Precategory C mor-coequalizer-obj-Precategory f ＝
      comp-hom-Precategory C mor-coequalizer-obj-Precategory g
    coh-coequalizer-obj-Precategory = pr1 (pr2 (pr2 c))

    module _
      {w : obj-Precategory C}
      (q : hom-Precategory C y w)
      (α : comp-hom-Precategory C q f ＝ comp-hom-Precategory C q g)
      where

      mor-from-coequalizer-obj-Precategory :
        hom-Precategory C obj-coequalizer-obj-Precategory w
      mor-from-coequalizer-obj-Precategory =
        pr1 (pr1 (pr2 (pr2 (pr2 c)) q α))

      compute-mor-from-coequalizer-obj-Precategory :
        comp-hom-Precategory C
          ( mor-from-coequalizer-obj-Precategory )
          ( mor-coequalizer-obj-Precategory ) ＝
        q
      compute-mor-from-coequalizer-obj-Precategory =
        pr2 (pr1 (pr2 (pr2 (pr2 c)) q α))

      is-unique-mor-from-coequalizer-obj-Precategory :
        (q' : hom-Precategory C obj-coequalizer-obj-Precategory w) →
        (β : comp-hom-Precategory C q' mor-coequalizer-obj-Precategory ＝ q) →
        mor-from-coequalizer-obj-Precategory ＝ q'
      is-unique-mor-from-coequalizer-obj-Precategory q' β =
        ap pr1 (pr2 (pr2 (pr2 (pr2 c)) q α) (q' , β))
```
