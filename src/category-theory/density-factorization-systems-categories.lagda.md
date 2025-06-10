# Density factorization systems in categories

```agda
module category-theory.density-factorization-systems-categories where
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

## Every comonad on an arrow category factors through one which is the identity on the domain

We first show this for copointed functors:

```agda
module _
  {l1 l2 : Level}
  (C : Precategory l1 l2)
  (let C1 = arrow-Precategory C)
  (L : functor-Precategory C1 C1)
  (ε : natural-transformation-Precategory C1 C1 L (id-functor-Precategory C1))
  (t : has-all-pushout-obj-Precategory C)
  (let L₀ = obj-functor-Precategory C1 C1 L)
  (let L₁ = hom-functor-Precategory C1 C1 L)
  (let Ldom = λ f → dom-obj-arrow-Precategory C (L₀ f))
  (let Lcod = λ f → cod-obj-arrow-Precategory C (L₀ f))
  (let Lmor = λ f → mor-obj-arrow-Precategory C (L₀ f))
  (let ε₀ = pr1 ε)
  (let nε = naturality-natural-transformation-Precategory C1 C1 L (id-functor-Precategory C1) ε)
  (let εtop = λ f → dom-hom-arrow-Precategory C (ε₀ f))
  (let εbot = λ f → cod-hom-arrow-Precategory C (ε₀ f))
  (let εcom = λ f → square-hom-arrow-Precategory C (ε₀ f))
  where

  M₀ : obj-Precategory C1 → obj-Precategory C1
  pr1 (pr1 (M₀ f)) = dom-obj-arrow-Precategory C f
  pr2 (pr1 (M₀ f)) = object-pushout-obj-Precategory C t _ _ _ (Lmor f) (εtop f)
  pr2 (M₀ f) = inr-pushout-obj-Precategory C t _ _ _ (Lmor f) (εtop f)

  α₀ : (f : obj-Precategory C1) → hom-Precategory C1 (M₀ f) f
  pr1 (pr1 (α₀ f)) = id-hom-Precategory C
  pr2 (pr1 (α₀ f)) = morphism-from-pushout-obj-Precategory C t _ _ _ (Lmor f) (εtop f) (cod-obj-arrow-Precategory C f)
                      (εbot f) (pr2 f) (εcom f)
  pr2 (α₀ f) =
    comm-morphism-from-inr-pushout-obj-Precategory C t _ _ _ (Lmor f)
     (εtop f) _ _ _ _ ∙
    inv (right-unit-law-comp-hom-Precategory C _)

  b₀ : (f : obj-Precategory C1) → hom-Precategory C1 (L₀ f) (M₀ f)
  pr1 (pr1 (b₀ f)) = εtop f
  pr2 (pr1 (b₀ f)) = inl-pushout-obj-Precategory C t _ _ _ (Lmor f) (εtop f)
  pr2 (b₀ f) = comm-pushout-obj-Precategory C t _ _ _ (Lmor f) (εtop f)

  M₁ : (f g : obj-Precategory C1) → (hom-Precategory C1 f g) →
    hom-Precategory C1 (M₀ f) (M₀ g)
  pr1 (pr1 (M₁ f g u)) = dom-hom-arrow-Precategory C u
  pr2 (pr1 (M₁ f g u)) =
    morphism-from-pushout-obj-Precategory C t _ _ _ (Lmor f) (εtop f)
      ( cod-obj-arrow-Precategory C (M₀ g))
      ( comp-hom-Precategory C
        ( cod-hom-arrow-Precategory C (b₀ g))
        ( cod-hom-arrow-Precategory C (L₁ u)))
      ( comp-hom-Precategory C
        ( mor-obj-arrow-Precategory C (M₀ g))
        ( dom-hom-arrow-Precategory C u))
      ( ( associative-comp-hom-Precategory C _ _ _) ∙
        ( ap
           ( λ x →
             comp-hom-Precategory C (cod-hom-arrow-Precategory C (b₀ g)) x)
          (square-hom-arrow-Precategory C (L₁ u))) ∙
        ( inv (associative-comp-hom-Precategory C _ _ _)) ∙
        ( ap
          ( precomp-hom-Precategory C (dom-hom-arrow-Precategory C (L₁ u)) _)
          ( comm-pushout-obj-Precategory C t _ _ _ (Lmor g) (εtop g))) ∙
        ( associative-comp-hom-Precategory C _ _ _ ) ∙
        ( ap
          ( postcomp-hom-Precategory C (mor-obj-arrow-Precategory C (M₀ g)) _)
          ( ap (dom-hom-arrow-Precategory C)
            ( inv (nε u)))) ∙
        ( inv (associative-comp-hom-Precategory C _ _ _)))
  pr2 (M₁ f g u) =
    comm-morphism-from-inr-pushout-obj-Precategory C t _ _ _ _ _ _ _ _ _

  idM :
    (f : obj-Precategory C1) →
    M₁ f f (id-hom-Precategory C1) ＝ id-hom-Precategory C1
  idM f = eq-hom-arrow-Precategory C (M₀ f) (M₀ f) _ _
    refl
    ( is-unique-morphism-from-pushout-obj-Precategory C t _ _ _ (Lmor f)
      ( εtop f) _ _ _ _ (id-hom-Precategory C)
      ( ( left-unit-law-comp-hom-Precategory C _) ∙
        ( inv
          ( ( ap
              ( λ x → comp-hom-Precategory C _ (cod-hom-arrow-Precategory C x))
              ( preserves-id-functor-Precategory C1 C1 L _)) ∙
            ( right-unit-law-comp-hom-Precategory C _))))
      ( ( left-unit-law-comp-hom-Precategory C _) ∙
        ( inv (right-unit-law-comp-hom-Precategory C _) )))

  compM :
    (f g h : obj-Precategory C1) →
    (v : hom-Precategory C1 g h) →
    (u : hom-Precategory C1 f g) →
    M₁ f h (comp-hom-Precategory C1 v u) ＝
    comp-hom-Precategory C1 (M₁ g h v) (M₁ f g u)
  compM f g h v u =
    eq-hom-arrow-Precategory C (M₀ f) (M₀ h) _ _
      refl
      ( is-unique-morphism-from-pushout-obj-Precategory C t _ _ _ (Lmor f)
        ( εtop f) _ _ _ _
        ( cod-hom-arrow-Precategory C
          ( comp-hom-Precategory C1 (M₁ g h v) (M₁ f g u)))
        ( ( associative-comp-hom-Precategory C _ _ _) ∙
          ( ap
            ( postcomp-hom-Precategory C _ _)
            ( comm-morphism-from-inl-pushout-obj-Precategory
                C t _ _ _ (Lmor f) (εtop f) _ _ _ _)) ∙
          ( inv (associative-comp-hom-Precategory C _ _ _)) ∙
          ( ap
            ( precomp-hom-Precategory C _ _)
            ( comm-morphism-from-inl-pushout-obj-Precategory
                C t _ _ _ (Lmor g) (εtop g) _ _ _ _)) ∙
          ( associative-comp-hom-Precategory C _ _ _) ∙
          ( ap
            ( λ x → comp-hom-Precategory C _ (cod-hom-arrow-Precategory C x))
            ( inv (preserves-comp-functor-Precategory C1 C1 L _ _))))
        ( ( associative-comp-hom-Precategory C _ _ _) ∙
          ( ap
            ( postcomp-hom-Precategory C _ _)
            ( comm-morphism-from-inr-pushout-obj-Precategory
                C t _ _ _ (Lmor f) (εtop f) _ _ _ _)) ∙
          ( inv (associative-comp-hom-Precategory C _ _ _)) ∙
          ( ap
            ( precomp-hom-Precategory C _ _)
            ( comm-morphism-from-inr-pushout-obj-Precategory
                C t _ _ _ (Lmor g) (εtop g) _ _ _ _)) ∙
          ( associative-comp-hom-Precategory C _ _ _)))

  M : functor-Precategory C1 C1
  pr1 M = M₀
  pr1 (pr2 M) {x} {y} = M₁ x y
  pr1 (pr2 (pr2 M)) {x} {y} {z} = compM x y z
  pr2 (pr2 (pr2 M)) = idM 
