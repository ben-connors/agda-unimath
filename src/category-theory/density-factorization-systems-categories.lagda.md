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
open import category-theory.comonads-on-precategories
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

## Every comonad on an arrow category factors through one which is the identity on the domain

We first show this for copointed functors: given an arbitrary copointed functor `(L : C1 → C1, ε : L ⇒ id)`, we get a second copointed functor `(M, α)` and `β : L ⇒ M` such that `ε = α ∘ β`, each component of `β` is a pushout square, and `dom ∘ L = id` judgementally on objects.

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
  (let εtop = λ f → dom-hom-arrow-Precategory C (pr1 ε f))
  (let εbot = λ f → cod-hom-arrow-Precategory C (pr1 ε f))
  (let εcomm = λ f → square-hom-arrow-Precategory C (pr1 ε f))
  (let tp = λ f → t _ _ _ (Lmor f) (εtop f))
  where

  obj-id-dom-comonad-Precategory : obj-Precategory C1 → obj-Precategory C1
  pr1 (pr1 (obj-id-dom-comonad-Precategory f)) =
    dom-obj-arrow-Precategory C f
  pr2 (pr1 (obj-id-dom-comonad-Precategory f)) =
    object-pushout-obj-Precategory C _ _ _ (Lmor f) (εtop f) (tp f)
  pr2 (obj-id-dom-comonad-Precategory f) =
    inr-pushout-obj-Precategory C _ _ _ (Lmor f) (εtop f) (tp f)

  hom-family-right-id-dom-comonad-Precategory :
    (f : obj-Precategory C1) →
    hom-Precategory C1 (obj-id-dom-comonad-Precategory f) f
  pr1 (pr1 (hom-family-right-id-dom-comonad-Precategory f)) =
    id-hom-Precategory C
  pr2 (pr1 (hom-family-right-id-dom-comonad-Precategory f)) =
    morphism-from-pushout-obj-Precategory C _ _ _ (Lmor f) (εtop f) (tp f)
      ( cod-obj-arrow-Precategory C f)
      ( εbot f)
      ( pr2 f)
      ( εcomm f)
  pr2 (hom-family-right-id-dom-comonad-Precategory f) =
    ( comm-morphism-from-inr-pushout-obj-Precategory
        C _ _ _ (Lmor f) (εtop f) (tp f) _ _ _ _) ∙
    ( inv (right-unit-law-comp-hom-Precategory C _))

  hom-family-left-id-dom-comonad-Precategory :
    (f : obj-Precategory C1) →
    hom-Precategory C1 (L₀ f) (obj-id-dom-comonad-Precategory f)
  pr1 (pr1 (hom-family-left-id-dom-comonad-Precategory f)) =
    εtop f
  pr2 (pr1 (hom-family-left-id-dom-comonad-Precategory f)) =
    inl-pushout-obj-Precategory C _ _ _ (Lmor f) (εtop f) (tp f)
  pr2 (hom-family-left-id-dom-comonad-Precategory f) =
    comm-pushout-obj-Precategory C _ _ _ (Lmor f) (εtop f) (tp f)

  private module Dummy6 where
    abstract
      comm-bottom-hom-id-dom-comonad-Precategory :
        (f g : obj-Precategory C1)
        (u : hom-Precategory C1 f g) →
        comp-hom-Precategory C
          ( comp-hom-Precategory C
            ( cod-hom-arrow-Precategory C (hom-family-left-id-dom-comonad-Precategory g))
            ( cod-hom-arrow-Precategory C (L₁ u)))
          ( Lmor f) ＝
        comp-hom-Precategory C
          ( comp-hom-Precategory C
            ( mor-obj-arrow-Precategory C (obj-id-dom-comonad-Precategory g))
            ( dom-hom-arrow-Precategory C u))
          ( εtop f)
      comm-bottom-hom-id-dom-comonad-Precategory f g u =
        ( associative-comp-hom-Precategory C _ _ _) ∙
        ( ap
          ( λ x →
            comp-hom-Precategory C
              ( cod-hom-arrow-Precategory C
                ( hom-family-left-id-dom-comonad-Precategory g))
              ( x))
          ( square-hom-arrow-Precategory C (L₁ u))) ∙
        ( inv (associative-comp-hom-Precategory C _ _ _)) ∙
        ( ap
          ( precomp-hom-Precategory C (dom-hom-arrow-Precategory C (L₁ u)) _)
          ( comm-pushout-obj-Precategory C _ _ _ (Lmor g) (εtop g) (tp g))) ∙
        ( associative-comp-hom-Precategory C _ _ _ ) ∙
        ( ap
          ( postcomp-hom-Precategory C
            ( mor-obj-arrow-Precategory C
              ( obj-id-dom-comonad-Precategory g))
              ( _))
          ( ap (dom-hom-arrow-Precategory C)
            ( inv (pr2 ε u)))) ∙
        ( inv (associative-comp-hom-Precategory C _ _ _))
  open Dummy6 public
    
  -- Agda slows down a lot if `f` and `g` are implicit
  hom-id-dom-comonad-Precategory :
    (f g : obj-Precategory C1) →
    hom-Precategory C1 f g →
    hom-Precategory C1
      ( obj-id-dom-comonad-Precategory f)
      ( obj-id-dom-comonad-Precategory g)
  pr1 (pr1 (hom-id-dom-comonad-Precategory f g u)) =
    dom-hom-arrow-Precategory C u
  pr2 (pr1 (hom-id-dom-comonad-Precategory f g u)) =
    morphism-from-pushout-obj-Precategory C _ _ _ (Lmor f) (εtop f) (tp f)
      ( cod-obj-arrow-Precategory C (obj-id-dom-comonad-Precategory g))
      ( comp-hom-Precategory C
        ( cod-hom-arrow-Precategory C
          ( hom-family-left-id-dom-comonad-Precategory g))
        ( cod-hom-arrow-Precategory C (L₁ u)))
      ( comp-hom-Precategory C
        ( mor-obj-arrow-Precategory C (obj-id-dom-comonad-Precategory g))
        ( dom-hom-arrow-Precategory C u))
      ( comm-bottom-hom-id-dom-comonad-Precategory f g u)
  pr2 (hom-id-dom-comonad-Precategory f g u) =
    comm-morphism-from-inr-pushout-obj-Precategory C _ _ _ _ _ (tp f) _ _ _ _

  private module Dummy1 where
    abstract
      preserves-id-id-dom-comonad-Precategory :
        (f : obj-Precategory C1) →
        hom-id-dom-comonad-Precategory f f (id-hom-Precategory C1) ＝
        id-hom-Precategory C1
      preserves-id-id-dom-comonad-Precategory f =
        eq-hom-arrow-Precategory C _ _ _ _
          refl
          ( is-unique-morphism-from-pushout-obj-Precategory C _ _ _ (Lmor f)
            ( εtop f) (tp f) _ _ _ _ (id-hom-Precategory C)
            ( ( left-unit-law-comp-hom-Precategory C _) ∙
              ( inv
                ( ( ap
                    ( λ x →
                      comp-hom-Precategory C _ (cod-hom-arrow-Precategory C x))
                    ( preserves-id-functor-Precategory C1 C1 L _)) ∙
                  ( right-unit-law-comp-hom-Precategory C _))))
            ( ( left-unit-law-comp-hom-Precategory C _) ∙
              ( inv (right-unit-law-comp-hom-Precategory C _) )))
  
      preserves-comp-id-dom-comonad-Precategory :
        (f g h : obj-Precategory C1) →
        (v : hom-Precategory C1 g h) →
        (u : hom-Precategory C1 f g) →
        hom-id-dom-comonad-Precategory f h (comp-hom-Precategory C1 v u) ＝
        comp-hom-Precategory C1
          ( hom-id-dom-comonad-Precategory g h v)
          ( hom-id-dom-comonad-Precategory f g u)
      preserves-comp-id-dom-comonad-Precategory f g h v u =
        eq-hom-arrow-Precategory C _ _ _ _
          refl
          ( is-unique-morphism-from-pushout-obj-Precategory C _ _ _ (Lmor f)
            ( εtop f) (tp f) _ _ _ _
            ( cod-hom-arrow-Precategory C
              ( comp-hom-Precategory C1
                ( hom-id-dom-comonad-Precategory g h v)
                ( hom-id-dom-comonad-Precategory f g u)))
            ( ( associative-comp-hom-Precategory C _ _ _) ∙
              ( ap
                ( postcomp-hom-Precategory C _ _)
                ( comm-morphism-from-inl-pushout-obj-Precategory
                    C _ _ _ (Lmor f) (εtop f) (tp f) _ _ _ _)) ∙
              ( inv (associative-comp-hom-Precategory C _ _ _)) ∙
              ( ap
                ( precomp-hom-Precategory C _ _)
                ( comm-morphism-from-inl-pushout-obj-Precategory
                    C _ _ _ (Lmor g) (εtop g) (tp g) _ _ _ _)) ∙
              ( associative-comp-hom-Precategory C _ _ _) ∙
              ( ap
                ( λ x → comp-hom-Precategory C _ (cod-hom-arrow-Precategory C x))
                ( inv (preserves-comp-functor-Precategory C1 C1 L _ _))))
            ( ( associative-comp-hom-Precategory C _ _ _) ∙
              ( ap
                ( postcomp-hom-Precategory C _ _)
                ( comm-morphism-from-inr-pushout-obj-Precategory
                    C _ _ _ (Lmor f) (εtop f) (tp f) _ _ _ _)) ∙
              ( inv (associative-comp-hom-Precategory C _ _ _)) ∙
              ( ap
                ( precomp-hom-Precategory C _ _)
                ( comm-morphism-from-inr-pushout-obj-Precategory
                    C _ _ _ (Lmor g) (εtop g) (tp g) _ _ _ _)) ∙
              ( associative-comp-hom-Precategory C _ _ _)))
  open Dummy1 public

  id-dom-comonad-Precategory : functor-Precategory C1 C1
  pr1 id-dom-comonad-Precategory =
    obj-id-dom-comonad-Precategory
  pr1 (pr2 id-dom-comonad-Precategory) {x} {y} =
    hom-id-dom-comonad-Precategory x y
  pr1 (pr2 (pr2 id-dom-comonad-Precategory)) {x} {y} {z} =
    preserves-comp-id-dom-comonad-Precategory x y z
  pr2 (pr2 (pr2 id-dom-comonad-Precategory)) =
    preserves-id-id-dom-comonad-Precategory 

  private module Dummy2 where
    abstract
      naturality-left-id-dom-comonad-Precategory :
        is-natural-transformation-Precategory C1 C1 L id-dom-comonad-Precategory
          hom-family-left-id-dom-comonad-Precategory
      naturality-left-id-dom-comonad-Precategory {f} {g} u =
        eq-hom-arrow-Precategory C _ _ _ _
          ( ap (dom-hom-arrow-Precategory C) ((pr2 ε) u))
          ( comm-morphism-from-inl-pushout-obj-Precategory
              C _ _ _ (Lmor f) (εtop f) (tp f) _ _ _ _)
  
      naturality-right-id-dom-comonad-Precategory :
        is-natural-transformation-Precategory C1 C1
          ( id-dom-comonad-Precategory)
          ( id-functor-Precategory C1)
          ( hom-family-right-id-dom-comonad-Precategory)
      naturality-right-id-dom-comonad-Precategory {f} {g} u =
        eq-hom-arrow-Precategory C _ _ _ _
          ( ( right-unit-law-comp-hom-Precategory C _) ∙
            ( inv (left-unit-law-comp-hom-Precategory C _)))
          ( ( inv left) ∙
            ( right))
          where
    
          pushout-map :
            hom-Precategory C
              ( cod-obj-arrow-Precategory C (obj-id-dom-comonad-Precategory f))
              ( cod-obj-arrow-Precategory C g)
          pushout-map =
            morphism-from-pushout-obj-Precategory C _ _ _ (Lmor f) (εtop f) (tp f)
              ( cod-obj-arrow-Precategory C g)
              ( comp-hom-Precategory C
                ( cod-hom-arrow-Precategory C u)
                ( cod-hom-arrow-Precategory C (pr1 ε f)))
              ( comp-hom-Precategory C
                ( cod-hom-arrow-Precategory C u)
                ( mor-obj-arrow-Precategory C f))
              ( ( associative-comp-hom-Precategory C _ _ _) ∙
                ( ap
                  ( postcomp-hom-Precategory C (cod-hom-arrow-Precategory C u) _)
                  ( pr2 (pr1 ε f))) ∙
                ( inv (associative-comp-hom-Precategory C _ _ _)))
    
          left :
            pushout-map ＝
            comp-hom-Precategory C
              ( cod-hom-arrow-Precategory C u)
              ( cod-hom-arrow-Precategory C
                ( hom-family-right-id-dom-comonad-Precategory f))
          left =
            is-unique-morphism-from-pushout-obj-Precategory
              C _ _ _ (Lmor f) (εtop f) (tp f) _ _ _ _ _
              ( ( associative-comp-hom-Precategory C _ _ _) ∙
                ( ap
                  ( postcomp-hom-Precategory C (cod-hom-arrow-Precategory C u) _)
                  ( comm-morphism-from-inl-pushout-obj-Precategory
                      C _ _ _ (Lmor f) (εtop f) (tp f) _ _ _ _)))
              ( ( associative-comp-hom-Precategory C _ _ _) ∙
                ( ap
                  ( postcomp-hom-Precategory C (cod-hom-arrow-Precategory C u) _)
                  ( comm-morphism-from-inr-pushout-obj-Precategory
                      C _ _ _ (Lmor f) (εtop f) (tp f) _ _ _ _)))
          right :
            pushout-map ＝
            comp-hom-Precategory C
              ( cod-hom-arrow-Precategory C
                ( hom-family-right-id-dom-comonad-Precategory g))
              ( cod-hom-arrow-Precategory C
                ( hom-id-dom-comonad-Precategory f g u))
          right =
            is-unique-morphism-from-pushout-obj-Precategory
              C _ _ _ (Lmor f) (εtop f) (tp f) _ _ _ _ _
              ( ( associative-comp-hom-Precategory C _ _ _) ∙
                ( ap
                  ( postcomp-hom-Precategory C
                    ( cod-hom-arrow-Precategory C
                      ( hom-family-right-id-dom-comonad-Precategory g))
                    ( _))
                  ( comm-morphism-from-inl-pushout-obj-Precategory
                      C _ _ _ _ _ (tp f) _ _ _ _)) ∙
                ( inv ( associative-comp-hom-Precategory C _ _ _)) ∙
                ( ap
                  ( precomp-hom-Precategory C
                    ( cod-hom-arrow-Precategory C (L₁ u))
                    ( _))
                  ( comm-morphism-from-inl-pushout-obj-Precategory
                      C _ _ _ _ _ (tp g)  _ _ _ _)) ∙
                ( inv (ap (cod-hom-arrow-Precategory C) (pr2 ε u))))
              ( ( associative-comp-hom-Precategory C _ _ _) ∙
                ( ap
                  ( postcomp-hom-Precategory C
                    ( cod-hom-arrow-Precategory C
                      ( hom-family-right-id-dom-comonad-Precategory g))
                    ( _))
                  ( comm-morphism-from-inr-pushout-obj-Precategory
                      C _ _ _ _ _ (tp f) _ _ _ _)) ∙
                ( inv (associative-comp-hom-Precategory C _ _ _)) ∙
                ( ap (precomp-hom-Precategory C (dom-hom-arrow-Precategory C u) _)
                  ( comm-morphism-from-inr-pushout-obj-Precategory
                      C _ _ _ _ _ (tp g) _ _ _ _)) ∙
                ( inv (square-hom-arrow-Precategory C u)))
  open Dummy2 public

  left-id-dom-comonad-Precategory :
    natural-transformation-Precategory C1 C1 L id-dom-comonad-Precategory
  pr1 left-id-dom-comonad-Precategory =
    hom-family-left-id-dom-comonad-Precategory
  pr2 left-id-dom-comonad-Precategory =
    naturality-left-id-dom-comonad-Precategory
        
  right-id-dom-comonad-Precategory :
    natural-transformation-Precategory C1 C1
      ( id-dom-comonad-Precategory)
      ( id-functor-Precategory C1)
  pr1 right-id-dom-comonad-Precategory =
    hom-family-right-id-dom-comonad-Precategory
  pr2 right-id-dom-comonad-Precategory =
    naturality-right-id-dom-comonad-Precategory

  factor-id-dom-comonad-Precategory :
    comp-natural-transformation-Precategory C1 C1
      ( L)
      ( id-dom-comonad-Precategory)
      ( id-functor-Precategory C1)
      ( right-id-dom-comonad-Precategory)
      ( left-id-dom-comonad-Precategory) ＝
    ε
  factor-id-dom-comonad-Precategory =
    eq-htpy-hom-family-natural-transformation-Precategory C1 C1
      ( L)
      ( id-functor-Precategory C1)
      ( _)
      ( _)
      ( λ f →
        eq-hom-arrow-Precategory C _ _ _ _
          ( left-unit-law-comp-hom-Precategory C _)
          ( comm-morphism-from-inl-pushout-obj-Precategory
              C _ _ _ (Lmor f) (εtop f) (tp f) _ _ _ _ ))

  module _
    (let LL = comp-functor-Precategory C1 C1 C1 L L)
    (let M = id-dom-comonad-Precategory)
    (let M₀ = obj-id-dom-comonad-Precategory)
    (let M₁ = hom-id-dom-comonad-Precategory)
    (let MM = comp-functor-Precategory C1 C1 C1 M M)
    (let MM₁ = hom-functor-Precategory C1 C1 MM)
    (let α = right-id-dom-comonad-Precategory)
    (let β = left-id-dom-comonad-Precategory)
    (ν : natural-transformation-Precategory C1 C1  L LL)
    (let ν₀ = pr1 ν)
    (Lass : associative-comul-copointed-endofunctor-Precategory C1 (L , ε) ν)
    (Lleft : left-counit-law-comul-copointed-endofunctor-Precategory C1 (L , ε) ν)
    (Lright : right-counit-law-comul-copointed-endofunctor-Precategory C1 (L , ε) ν)
    (let cha = cod-hom-arrow-Precategory C)
    (let dha = dom-hom-arrow-Precategory C)
    (let Mβ = left-whisker-natural-transformation-Precategory C1 C1 C1 L M M β)
    (let βL = right-whisker-natural-transformation-Precategory C1 C1 C1 L M β L)
    where
    
    private module Dummy4 where
      abstract
        δ₀-pushout-comm :
          (f : obj-Precategory C1) →
          comp-hom-Precategory C
            ( comp-hom-Precategory C
              ( cod-hom-arrow-Precategory C (M₁ _ _ (pr1 β f)))
              ( comp-hom-Precategory C
                ( cod-hom-arrow-Precategory C (pr1 β (L₀ f)))
                ( cod-hom-arrow-Precategory C (ν₀ f))))
            ( Lmor f) ＝
          comp-hom-Precategory C
            ( mor-obj-arrow-Precategory C (M₀ (M₀ f)))
            ( εtop f)
        δ₀-pushout-comm f =
          ( pasting-horizontal-coherence-square-hom-Precategory C
            ( _)
            ( dom-hom-arrow-Precategory C (M₁ _ _ (pr1 β f)))
            ( mor-obj-arrow-Precategory C (L₀ f))
            ( mor-obj-arrow-Precategory C (M₀ (L₀ f)))
            ( mor-obj-arrow-Precategory C (M₀ (M₀ f)))
            ( _)
            ( cod-hom-arrow-Precategory C (M₁ _ _ (pr1 β f)))
            ( pasting-horizontal-coherence-square-hom-Precategory C
              ( dom-hom-arrow-Precategory C (pr1 ν f))
              ( dom-hom-arrow-Precategory C (pr1 β (L₀ f)))
              ( mor-obj-arrow-Precategory C (L₀ f))
              ( mor-obj-arrow-Precategory C (L₀ (L₀ f)))
              ( mor-obj-arrow-Precategory C (M₀ (L₀ f)))
              ( cod-hom-arrow-Precategory C (pr1 ν f))
              ( cod-hom-arrow-Precategory C (pr1 β (L₀ f)))
              ( square-hom-arrow-Precategory C (pr1 ν f))
              ( square-hom-arrow-Precategory C (pr1 β (L₀ f))))
            ( square-hom-arrow-Precategory C (M₁ _ _ (pr1 β f)))) ∙
          ( inv (associative-comp-hom-Precategory C _ _ _)) ∙
          ( ap (postcomp-hom-Precategory C _ _)
            ( ap (λ x → dom-hom-arrow-Precategory C (pr1 x f)) Lright)) ∙
          ( right-unit-law-comp-hom-Precategory C _)
    open Dummy4 public

    δ₀ : (f : obj-Precategory C1) →
      hom-Precategory C1 (M₀ f) (M₀ (M₀ f))
    pr1 (pr1 (δ₀ f)) = id-hom-Precategory C
    pr2 (pr1 (δ₀ f)) =
      morphism-from-pushout-obj-Precategory C _ _ _ (Lmor f) (εtop f) (tp f) _
        ( comp-hom-Precategory C
          ( cod-hom-arrow-Precategory C (M₁ _ _ (pr1 β f)))
          ( comp-hom-Precategory C
            ( cod-hom-arrow-Precategory C (pr1 β (L₀ f)))
            ( cod-hom-arrow-Precategory C (ν₀ f))))
        ( mor-obj-arrow-Precategory C (M₀ (M₀ f)))
        ( δ₀-pushout-comm f)
    pr2 (δ₀ f) =
      ( comm-morphism-from-inr-pushout-obj-Precategory C _ _ _ _ _ (tp f) _ _ _ _) ∙
      ( inv (right-unit-law-comp-hom-Precategory C _))

    private module Dummy3 where
      abstract
        δ₀c : (f : obj-Precategory C1) →
          comp-hom-Precategory C1 (δ₀ f) (pr1 β f) ＝
          comp-hom-Precategory C1
            ( comp-hom-Precategory C1
              ( M₁ _ _ (pr1 β f))
              ( pr1 β (L₀ f)))
            ( ν₀ f)
        δ₀c f =
          eq-hom-arrow-Precategory C _ _ _ _
            ( ( left-unit-law-comp-hom-Precategory C _ ) ∙
              ( inv
                ( ( associative-comp-hom-Precategory C _ _ _) ∙
                  ( ap
                    ( λ x → comp-hom-Precategory C (dha (pr1 β f)) (dha (pr1 x f)))
                    ( Lright)) ∙
                  ( right-unit-law-comp-hom-Precategory C _))))
            ( ( comm-morphism-from-inl-pushout-obj-Precategory C _ _ _ _ _ (tp f) _ _ _ (δ₀-pushout-comm f)) ∙
              ( inv (associative-comp-hom-Precategory C _ _ _)))
  
        δ₀c' : (f : obj-Precategory C1) →
          comp-hom-Precategory C (cha (δ₀ f)) (pr2 (M₀ f)) ＝
          pr2 (M₀ (M₀ f))
        δ₀c' f =
          comm-morphism-from-inr-pushout-obj-Precategory C _ _ _ _ _ (tp f) _ _ _ (δ₀-pushout-comm f)
    open Dummy3 public

    private module Dummy5 where
      abstract
        right1b :
          {f g : obj-Precategory C1} (u : hom-Precategory C1 f g) →
          comp-hom-Precategory C1
            ( comp-hom-Precategory C1
              (δ₀ g)
              (M₁ f g u))
            ( pr1 β f) ＝
          comp-hom-Precategory C1
            ( M₁ (M₀ f) (M₀ g) (M₁ f g u))
            ( comp-hom-Precategory C1
              ( M₁ (L₀ f) (M₀ f) (pr1 β f))
              ( comp-hom-Precategory C1
                ( pr1 β (L₀ f))
                ( ν₀ f)))
        right1b {f} {g} u = 
          ( associative-comp-hom-Precategory C1 (δ₀ g) (M₁ f g u) (pr1 β f)) ∙
          ( ap
            ( comp-hom-Precategory C1 (δ₀ g))
            ( pr2 β u)) ∙ 
          ( inv (associative-comp-hom-Precategory C1 (δ₀ g) (pr1 β g) (L₁ u))) ∙
          ( ap
            ( precomp-hom-Precategory C1 (L₁ u) _)
            ( δ₀c g)) ∙
          ( associative-comp-hom-Precategory C1
            ( comp-hom-Precategory C1 (M₁ (L₀ g) (M₀ g) (pr1 β g)) (pr1 β (L₀ g)))
            ( pr1 ν g)
            ( L₁ u)) ∙
          ( ap
            ( comp-hom-Precategory C1
              ( comp-hom-Precategory C1 (pr1 Mβ g) (pr1 βL g)))
            ( inv (pr2 ν u))) ∙
          ( inv
            ( associative-comp-hom-Precategory C1
              ( comp-hom-Precategory C1 (M₁ (L₀ g) (M₀ g) (pr1 β g)) (pr1 β (L₀ g)))
              ( L₁ (L₁ u))
              ( pr1 ν f))) ∙
          ( ap
            ( precomp-hom-Precategory C1 (pr1 ν f) _)
            ( ( associative-comp-hom-Precategory C1
                ( M₁ (L₀ g) (M₀ g) (pr1 β g))
                ( pr1 β (L₀ g))
                ( L₁ (L₁ u))) ∙
              ( ap
                ( comp-hom-Precategory C1 (pr1 Mβ g))
                ( inv (pr2 βL u))) ∙
              ( inv
                ( associative-comp-hom-Precategory C1
                  ( pr1 Mβ g)
                  ( M₁ (L₀ f) (L₀ g) (L₁ u))
                  ( pr1 β (L₀ f)))) ∙
              ( ap
                ( precomp-hom-Precategory C1 (pr1 βL f) _)
                ( inv (pr2 Mβ u))) ∙
              ( associative-comp-hom-Precategory C1
                ( M₁ (M₀ f) (M₀ g) (M₁ f g u))
                ( pr1 Mβ f)
                ( pr1 β (L₀ f))))) ∙
          ( associative-comp-hom-Precategory C1
            ( M₁ (M₀ f) (M₀ g) (M₁ f g u))
            ( comp-hom-Precategory C1 (pr1 Mβ f) (pr1 β (L₀ f)))
            ( pr1 ν f)) ∙ 
          ( ap
            ( comp-hom-Precategory C1 (M₁ (M₀ f) (M₀ g) (M₁ f g u)))
            ( associative-comp-hom-Precategory C1
              ( pr1 Mβ f)
              ( pr1 β (L₀ f))
              ( pr1 ν f)))
    open Dummy5 public

    nδ : 
      is-natural-transformation-Precategory C1 C1 M MM δ₀
    nδ {f} {g} u =
      eq-hom-arrow-Precategory C _ _ _ _
        ( ( right-unit-law-comp-hom-Precategory C _) ∙
          ( inv (left-unit-law-comp-hom-Precategory C _)))
        ( ( preserves-postcomp-morphism-from-pushout-obj-Precategory C _ _ _
             _ _ (tp f) _
             ( comp-hom-Precategory C
               ( cod-hom-arrow-Precategory C (M₁ _ _ (pr1 β f)))
               ( comp-hom-Precategory C
                 ( cod-hom-arrow-Precategory C (pr1 β (L₀ f)))
                 ( cod-hom-arrow-Precategory C (ν₀ f))))
             ( mor-obj-arrow-Precategory C (M₀ (M₀ f)))
             ( δ₀-pushout-comm f)
             ( cod-hom-arrow-Precategory C (M₁ (M₀ f) (M₀ g) (M₁ f g u)))) ∙
          ( right))
      where
        right2 :
          comp-hom-Precategory C
            ( comp-hom-Precategory C (cha (δ₀ g)) (cha (M₁ f g u)))
            ( pr2 (M₀ f))
            ＝
          comp-hom-Precategory C
            ( cha (M₁ (M₀ f) (M₀ g) (M₁ f g u)))
            ( pr2 (M₀ (M₀ f)))
        right2 =
          ( associative-comp-hom-Precategory C _ _ _) ∙
          ( ap (comp-hom-Precategory C (cha (δ₀ g)))
            ( pr2 (M₁ f g u))) ∙
          ( inv (associative-comp-hom-Precategory C _ _ _)) ∙
          ( ap (precomp-hom-Precategory C (dha (M₁ f g u)) _)
            ( δ₀c' g)) ∙
          ( inv (pr2 (M₁ (M₀ f) (M₀ g) (M₁ f g u))))
    
        right = is-unique-morphism-from-pushout-obj-Precategory C _ _ _
          ( Lmor f)
          ( εtop f) (tp f)
          _ _ _ _
          ( comp-hom-Precategory C
            ( cod-hom-arrow-Precategory C (δ₀ g))
            ( cod-hom-arrow-Precategory C (M₁ f g u)))
          ( ap cha (right1b u))
          ( right2)
