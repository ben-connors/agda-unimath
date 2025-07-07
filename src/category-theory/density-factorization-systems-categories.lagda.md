# The identity-on-domain factorization of a comonad

```agda
module category-theory.id-dom-comonad-precategories where
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

## Idea

Every comonad on an arrow category factors through one which is the identity on the domain

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

  private module Dummy1 where
    abstract
      cod-obj-id-dom-comonad-Precategory : obj-Precategory C1 → obj-Precategory C
      cod-obj-id-dom-comonad-Precategory f = 
        object-pushout-obj-Precategory C _ _ _ (Lmor f) (εtop f) (tp f)
  
      mor-obj-id-dom-comonad-Precategory : (f : obj-Precategory C1) →
        hom-Precategory C
          ( dom-obj-arrow-Precategory C f)
          ( cod-obj-id-dom-comonad-Precategory f)
      mor-obj-id-dom-comonad-Precategory f = 
        inr-pushout-obj-Precategory C _ _ _ (Lmor f) (εtop f) (tp f)
  
      bottom-hom-family-left-id-dom-comonad-Precategory :
        (f : obj-Precategory C1) →
        hom-Precategory C
          ( cod-obj-arrow-Precategory C (L₀ f))
          ( cod-obj-id-dom-comonad-Precategory f)
      bottom-hom-family-left-id-dom-comonad-Precategory f =
        inl-pushout-obj-Precategory C _ _ _ (Lmor f) (εtop f) (tp f)
  
      comm-hom-family-left-id-dom-comonad-Precategory :
        (f : obj-Precategory C1) →
        comp-hom-Precategory C
          ( bottom-hom-family-left-id-dom-comonad-Precategory f)
          ( mor-obj-arrow-Precategory C (L₀ f)) ＝
        comp-hom-Precategory C
          ( mor-obj-id-dom-comonad-Precategory f)
          ( εtop f)
      comm-hom-family-left-id-dom-comonad-Precategory f =
        comm-pushout-obj-Precategory C _ _ _ (Lmor f) (εtop f) (tp f)
  
      is-pushout-id-dom-comonad-Precategory :
        (f : obj-Precategory C1) →
        is-pushout-obj-Precategory C _ _ _ (Lmor f) (εtop f)
          ( cod-obj-id-dom-comonad-Precategory f)
          ( bottom-hom-family-left-id-dom-comonad-Precategory f)
          ( mor-obj-id-dom-comonad-Precategory f)
          ( comm-hom-family-left-id-dom-comonad-Precategory f )
      is-pushout-id-dom-comonad-Precategory f =
        pr2 (pr2 (pr2 (pr2 (tp f))))
  open Dummy1 public

  pushout-id-dom-comonad-Precategory :
    (f : obj-Precategory C1) →
    pushout-obj-Precategory C _ _ _ (Lmor f) (εtop f)
  pushout-id-dom-comonad-Precategory f =
    cod-obj-id-dom-comonad-Precategory f ,
    bottom-hom-family-left-id-dom-comonad-Precategory f ,
    mor-obj-id-dom-comonad-Precategory f ,
    comm-hom-family-left-id-dom-comonad-Precategory f ,
    is-pushout-id-dom-comonad-Precategory f 

  obj-id-dom-comonad-Precategory : obj-Precategory C1 → obj-Precategory C1
  pr1 (pr1 (obj-id-dom-comonad-Precategory f)) =
    dom-obj-arrow-Precategory C f
  pr2 (pr1 (obj-id-dom-comonad-Precategory f)) =
    cod-obj-id-dom-comonad-Precategory f
  pr2 (obj-id-dom-comonad-Precategory f) =
    mor-obj-id-dom-comonad-Precategory f

  private module Dummy00 where
    abstract
      comm-bottom-hom-id-dom-comonad-Precategory :
        (f g : obj-Precategory C1)
        (u : hom-Precategory C1 f g) →
        comp-hom-Precategory C
          ( comp-hom-Precategory C
            ( bottom-hom-family-left-id-dom-comonad-Precategory g)
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
              ( bottom-hom-family-left-id-dom-comonad-Precategory g)
              ( x))
          ( square-hom-arrow-Precategory C (L₁ u))) ∙
        ( inv (associative-comp-hom-Precategory C _ _ _)) ∙
        ( ap
          ( precomp-hom-Precategory C (dom-hom-arrow-Precategory C (L₁ u)) _)
          ( comm-pushout-obj-Precategory C _ _ _ (Lmor g) (εtop g) (pushout-id-dom-comonad-Precategory g))) ∙
        ( associative-comp-hom-Precategory C _ _ _ ) ∙
        ( ap
          ( postcomp-hom-Precategory C
            ( mor-obj-arrow-Precategory C
              ( obj-id-dom-comonad-Precategory g))
              ( _))
          ( ap (dom-hom-arrow-Precategory C)
            ( inv (pr2 ε u)))) ∙
        ( inv (associative-comp-hom-Precategory C _ _ _))
  
      bottom-hom-id-dom-comonad-Precategory :
        (f g : obj-Precategory C1)
        (u : hom-Precategory C1 f g) →
        hom-Precategory C
          ( cod-obj-id-dom-comonad-Precategory f)
          ( cod-obj-id-dom-comonad-Precategory g)
      bottom-hom-id-dom-comonad-Precategory f g u =
        morphism-from-pushout-obj-Precategory C _ _ _ (Lmor f) (εtop f)
          ( pushout-id-dom-comonad-Precategory f)
          ( cod-obj-arrow-Precategory C (obj-id-dom-comonad-Precategory g))
          ( comp-hom-Precategory C
            ( bottom-hom-family-left-id-dom-comonad-Precategory g)
            ( cod-hom-arrow-Precategory C (L₁ u)))
          ( comp-hom-Precategory C
            ( mor-obj-arrow-Precategory C (obj-id-dom-comonad-Precategory g))
            ( dom-hom-arrow-Precategory C u))
          ( comm-bottom-hom-id-dom-comonad-Precategory f g u)
  
      eq-bottom-hom-id-dom-comonad-Precategory :
        (f g : obj-Precategory C1)
        (u : hom-Precategory C1 f g) →
        bottom-hom-id-dom-comonad-Precategory f g u ＝
        morphism-from-pushout-obj-Precategory C _ _ _ (Lmor f) (εtop f)
          ( pushout-id-dom-comonad-Precategory f)
          ( cod-obj-arrow-Precategory C (obj-id-dom-comonad-Precategory g))
          ( comp-hom-Precategory C
            ( bottom-hom-family-left-id-dom-comonad-Precategory g)
            ( cod-hom-arrow-Precategory C (L₁ u)))
          ( comp-hom-Precategory C
            ( mor-obj-arrow-Precategory C (obj-id-dom-comonad-Precategory g))
            ( dom-hom-arrow-Precategory C u))
          ( comm-bottom-hom-id-dom-comonad-Precategory f g u)
      eq-bottom-hom-id-dom-comonad-Precategory f g u = refl
  
      comm-hom-id-dom-comonad-Precategory :
        (f g : obj-Precategory C1)
        (u : hom-Precategory C1 f g) →
        comp-hom-Precategory C
          ( bottom-hom-id-dom-comonad-Precategory f g u)
          ( mor-obj-id-dom-comonad-Precategory f) ＝
        comp-hom-Precategory C
          ( mor-obj-arrow-Precategory C (obj-id-dom-comonad-Precategory g))
          ( dom-hom-arrow-Precategory C u)
      comm-hom-id-dom-comonad-Precategory f g u =
        comm-morphism-from-inr-pushout-obj-Precategory
          C _ _ _ _ _ (pushout-id-dom-comonad-Precategory f) _ _ _ _
  
      preserves-id-bottom-hom-id-dom-comonad-Precategory :
        (f : obj-Precategory C1) →
        bottom-hom-id-dom-comonad-Precategory f f (id-hom-Precategory C1) ＝
        id-hom-Precategory C
      preserves-id-bottom-hom-id-dom-comonad-Precategory f =
        is-unique-morphism-from-pushout-obj-Precategory C _ _ _ (Lmor f)
          ( εtop f) (pushout-id-dom-comonad-Precategory f) _ _ _ _ (id-hom-Precategory C)
          ( ( left-unit-law-comp-hom-Precategory C _) ∙
            ( inv
              ( ( ap
                  ( λ x →
                    comp-hom-Precategory C
                      ( bottom-hom-family-left-id-dom-comonad-Precategory f)
                      ( cod-hom-arrow-Precategory C x))
                  ( preserves-id-functor-Precategory C1 C1 L f)) ∙
                ( right-unit-law-comp-hom-Precategory C _))))
          ( ( left-unit-law-comp-hom-Precategory C _) ∙
            ( inv (right-unit-law-comp-hom-Precategory C _) ))
  
      preserves-comp-bottom-hom-id-dom-comonad-Precategory :
        (f g h : obj-Precategory C1) →
        (v : hom-Precategory C1 g h) →
        (u : hom-Precategory C1 f g) →
        bottom-hom-id-dom-comonad-Precategory f h (comp-hom-Precategory C1 v u) ＝
        comp-hom-Precategory C
          ( bottom-hom-id-dom-comonad-Precategory g h v)
          ( bottom-hom-id-dom-comonad-Precategory f g u)
      preserves-comp-bottom-hom-id-dom-comonad-Precategory f g h v u =
        is-unique-morphism-from-pushout-obj-Precategory C _ _ _ (Lmor f)
          ( εtop f) (pushout-id-dom-comonad-Precategory f) _ _ _ _
          ( comp-hom-Precategory C
            ( bottom-hom-id-dom-comonad-Precategory g h v)
            ( bottom-hom-id-dom-comonad-Precategory f g u))
          ( ( associative-comp-hom-Precategory C
              ( bottom-hom-id-dom-comonad-Precategory g h v)
              ( bottom-hom-id-dom-comonad-Precategory f g u)
              ( bottom-hom-family-left-id-dom-comonad-Precategory f)) ∙
            ( ap
              ( postcomp-hom-Precategory C (bottom-hom-id-dom-comonad-Precategory g h v) _)
              ( comm-morphism-from-inl-pushout-obj-Precategory
                  C _ _ _ (Lmor f) (εtop f) (pushout-id-dom-comonad-Precategory f) _ _ _ _)) ∙
            ( inv
              ( associative-comp-hom-Precategory C
                ( bottom-hom-id-dom-comonad-Precategory g h v)
                ( bottom-hom-family-left-id-dom-comonad-Precategory g)
                ( cod-hom-arrow-Precategory C (L₁ u)))) ∙
            ( ap
              ( precomp-hom-Precategory C (cod-hom-arrow-Precategory C (L₁ u)) _)
              ( comm-morphism-from-inl-pushout-obj-Precategory
                  C _ _ _ (Lmor g) (εtop g) (pushout-id-dom-comonad-Precategory g) _ _ _ _)) ∙
            ( associative-comp-hom-Precategory C
              ( (bottom-hom-family-left-id-dom-comonad-Precategory h))
              ( (cod-hom-arrow-Precategory C (L₁ v)))
              ( (cod-hom-arrow-Precategory C (L₁ u)))) ∙
            ( ap
              ( λ x → comp-hom-Precategory C (bottom-hom-family-left-id-dom-comonad-Precategory h) (cod-hom-arrow-Precategory C x))
              ( inv (preserves-comp-functor-Precategory C1 C1 L _ _))))
          ( ( associative-comp-hom-Precategory C _ _ _) ∙
            ( ap
              ( postcomp-hom-Precategory C _ _)
              ( comm-morphism-from-inr-pushout-obj-Precategory
                  C _ _ _ (Lmor f) (εtop f) (pushout-id-dom-comonad-Precategory f) _ _ _ _)) ∙
            ( inv (associative-comp-hom-Precategory C _ _ _)) ∙
            ( ap
              ( precomp-hom-Precategory C _ _)
              ( comm-morphism-from-inr-pushout-obj-Precategory
                  C _ _ _ (Lmor g) (εtop g) (pushout-id-dom-comonad-Precategory g) _ _ _ _)) ∙
            ( associative-comp-hom-Precategory C _ _ _))
  open Dummy00 public

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
    bottom-hom-id-dom-comonad-Precategory f g u
  pr2 (hom-id-dom-comonad-Precategory f g u) =
    comm-hom-id-dom-comonad-Precategory f g u

  abstract
    preserves-id-id-dom-comonad-Precategory :
      (f : obj-Precategory C1) →
      hom-id-dom-comonad-Precategory f f (id-hom-Precategory C1) ＝
      id-hom-Precategory C1
    preserves-id-id-dom-comonad-Precategory f =
      eq-hom-arrow-Precategory C _ _ _ _
        ( refl)
        ( preserves-id-bottom-hom-id-dom-comonad-Precategory f)

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
        ( refl)
        ( preserves-comp-bottom-hom-id-dom-comonad-Precategory f g h v u)

  functor-id-dom-comonad-Precategory : functor-Precategory C1 C1
  pr1 functor-id-dom-comonad-Precategory =
    obj-id-dom-comonad-Precategory
  pr1 (pr2 functor-id-dom-comonad-Precategory) {x} {y} =
    hom-id-dom-comonad-Precategory x y
  pr1 (pr2 (pr2 functor-id-dom-comonad-Precategory)) {x} {y} {z} =
    preserves-comp-id-dom-comonad-Precategory x y z
  pr2 (pr2 (pr2 functor-id-dom-comonad-Precategory)) =
    preserves-id-id-dom-comonad-Precategory 

  hom-family-right-id-dom-comonad-Precategory :
    (f : obj-Precategory C1) →
    hom-Precategory C1 (obj-id-dom-comonad-Precategory f) f
  pr1 (pr1 (hom-family-right-id-dom-comonad-Precategory f)) =
    id-hom-Precategory C
  pr2 (pr1 (hom-family-right-id-dom-comonad-Precategory f)) =
    morphism-from-pushout-obj-Precategory C _ _ _ (Lmor f) (εtop f) (pushout-id-dom-comonad-Precategory f)
      ( cod-obj-arrow-Precategory C f)
      ( εbot f)
      ( pr2 f)
      ( εcomm f)
  pr2 (hom-family-right-id-dom-comonad-Precategory f) =
    ( comm-morphism-from-inr-pushout-obj-Precategory
        C _ _ _ (Lmor f) (εtop f) (pushout-id-dom-comonad-Precategory f) _ _ _ _) ∙
    ( inv (right-unit-law-comp-hom-Precategory C _))

  hom-family-left-id-dom-comonad-Precategory :
    (f : obj-Precategory C1) →
    hom-Precategory C1 (L₀ f) (obj-id-dom-comonad-Precategory f)
  pr1 (pr1 (hom-family-left-id-dom-comonad-Precategory f)) =
    εtop f
  pr2 (pr1 (hom-family-left-id-dom-comonad-Precategory f)) =
    bottom-hom-family-left-id-dom-comonad-Precategory f
  pr2 (hom-family-left-id-dom-comonad-Precategory f) =
    comm-hom-family-left-id-dom-comonad-Precategory f

  private module Dummy001 where
    abstract
      naturality-left-id-dom-comonad-Precategory :
        is-natural-transformation-Precategory C1 C1 L functor-id-dom-comonad-Precategory
          hom-family-left-id-dom-comonad-Precategory
      naturality-left-id-dom-comonad-Precategory {f} {g} u =
        eq-hom-arrow-Precategory C _ _ _ _
          ( ap (dom-hom-arrow-Precategory C) ((pr2 ε) u))
          ( ( ap (precomp-hom-Precategory C _ _)
              ( eq-bottom-hom-id-dom-comonad-Precategory f g u)) ∙
            ( comm-morphism-from-inl-pushout-obj-Precategory
                C _ _ _ (Lmor f) (εtop f)
                ( pushout-id-dom-comonad-Precategory f) _ _ _ _))
  
      naturality-right-id-dom-comonad-Precategory :
        is-natural-transformation-Precategory C1 C1
          ( functor-id-dom-comonad-Precategory)
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
            morphism-from-pushout-obj-Precategory C _ _ _ (Lmor f) (εtop f) (pushout-id-dom-comonad-Precategory f)
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
              C _ _ _ (Lmor f) (εtop f) (pushout-id-dom-comonad-Precategory f) _ _ _ _ _
              ( ( associative-comp-hom-Precategory C _ _ _) ∙
                ( ap
                  ( postcomp-hom-Precategory C (cod-hom-arrow-Precategory C u) _)
                  ( comm-morphism-from-inl-pushout-obj-Precategory
                      C _ _ _ (Lmor f) (εtop f) (pushout-id-dom-comonad-Precategory f) _ _ _ _)))
              ( ( associative-comp-hom-Precategory C _ _ _) ∙
                ( ap
                  ( postcomp-hom-Precategory C (cod-hom-arrow-Precategory C u) _)
                  ( comm-morphism-from-inr-pushout-obj-Precategory
                      C _ _ _ (Lmor f) (εtop f) (pushout-id-dom-comonad-Precategory f) _ _ _ _)))
          right :
            pushout-map ＝
            comp-hom-Precategory C
              ( cod-hom-arrow-Precategory C
                ( hom-family-right-id-dom-comonad-Precategory g))
              ( cod-hom-arrow-Precategory C
                ( hom-id-dom-comonad-Precategory f g u))
          right =
            ( is-unique-morphism-from-pushout-obj-Precategory
              C _ _ _ (Lmor f) (εtop f) (pushout-id-dom-comonad-Precategory f) _ _ _ _ _
              ( ( associative-comp-hom-Precategory C _ _ _) ∙
                ( ap
                  ( postcomp-hom-Precategory C
                    ( cod-hom-arrow-Precategory C
                      ( hom-family-right-id-dom-comonad-Precategory g))
                    ( _))
                  ( comm-morphism-from-inl-pushout-obj-Precategory
                      C _ _ _ _ _ (pushout-id-dom-comonad-Precategory f) _ _ _ _)) ∙
                ( inv ( associative-comp-hom-Precategory C _ _ _)) ∙
                ( ap
                  ( precomp-hom-Precategory C
                    ( cod-hom-arrow-Precategory C (L₁ u))
                    ( _))
                  ( comm-morphism-from-inl-pushout-obj-Precategory
                      C _ _ _ _ _ (pushout-id-dom-comonad-Precategory g) _ _ _ _)) ∙
                ( inv (ap (cod-hom-arrow-Precategory C) (pr2 ε u))))
              ( ( associative-comp-hom-Precategory C _ _ _) ∙
                ( ap
                  ( postcomp-hom-Precategory C
                    ( cod-hom-arrow-Precategory C
                      ( hom-family-right-id-dom-comonad-Precategory g))
                    ( _))
                  ( comm-morphism-from-inr-pushout-obj-Precategory
                      C _ _ _ _ _ (pushout-id-dom-comonad-Precategory f) _ _ _ _)) ∙
                ( inv (associative-comp-hom-Precategory C _ _ _)) ∙
                ( ap (precomp-hom-Precategory C (dom-hom-arrow-Precategory C u) _)
                  ( comm-morphism-from-inr-pushout-obj-Precategory
                      C _ _ _ _ _ (pushout-id-dom-comonad-Precategory g) _ _ _ _)) ∙
                ( inv (square-hom-arrow-Precategory C u)))) ∙
            ( ap
              ( comp-hom-Precategory C
                ( cod-hom-arrow-Precategory C
                  ( hom-family-right-id-dom-comonad-Precategory g)))
              ( inv (eq-bottom-hom-id-dom-comonad-Precategory f g u)))

      factor-hom-family-id-dom-comonad-Precategory :
        (f : obj-Precategory C1) →
        comp-hom-Precategory C1
          ( hom-family-right-id-dom-comonad-Precategory f)
          ( hom-family-left-id-dom-comonad-Precategory f) ＝
        pr1 ε f
      factor-hom-family-id-dom-comonad-Precategory f =
        eq-hom-arrow-Precategory C _ _ _ _
          ( left-unit-law-comp-hom-Precategory C _)
          ( comm-morphism-from-inl-pushout-obj-Precategory
            C _ _ _ (Lmor f) (εtop f) (pushout-id-dom-comonad-Precategory f) _ _ _ _ )
  open Dummy001 public
        
  right-id-dom-comonad-Precategory :
    natural-transformation-Precategory C1 C1
      ( functor-id-dom-comonad-Precategory)
      ( id-functor-Precategory C1)
  pr1 right-id-dom-comonad-Precategory =
    hom-family-right-id-dom-comonad-Precategory
  pr2 right-id-dom-comonad-Precategory =
    naturality-right-id-dom-comonad-Precategory

  left-id-dom-comonad-Precategory :
    natural-transformation-Precategory C1 C1 L functor-id-dom-comonad-Precategory
  pr1 left-id-dom-comonad-Precategory =
    hom-family-left-id-dom-comonad-Precategory
  pr2 left-id-dom-comonad-Precategory =
    naturality-left-id-dom-comonad-Precategory

  factor-id-dom-comonad-Precategory :
    comp-natural-transformation-Precategory C1 C1
      ( L)
      ( functor-id-dom-comonad-Precategory)
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
      ( factor-hom-family-id-dom-comonad-Precategory)

  module _
    (let LL = comp-functor-Precategory C1 C1 C1 L L)
    (let M = functor-id-dom-comonad-Precategory)
    (let M₀ = obj-id-dom-comonad-Precategory)
    (let M₁ = hom-id-dom-comonad-Precategory)
    (let MM = comp-functor-Precategory C1 C1 C1 M M)
    (let MM₁ = hom-functor-Precategory C1 C1 MM)
    (let α = right-id-dom-comonad-Precategory)
    (let MMM = comp-functor-Precategory C1 C1 C1 M MM)
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
    (let Mα = left-whisker-natural-transformation-Precategory C1 C1 C1 M (id-functor-Precategory C1) M α)
    (let αM = right-whisker-natural-transformation-Precategory C1 C1 C1 M (id-functor-Precategory C1) α M)
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
      morphism-from-pushout-obj-Precategory C _ _ _ (Lmor f) (εtop f) (pushout-id-dom-comonad-Precategory f) _
        ( comp-hom-Precategory C
          ( cod-hom-arrow-Precategory C (M₁ _ _ (pr1 β f)))
          ( comp-hom-Precategory C
            ( cod-hom-arrow-Precategory C (pr1 β (L₀ f)))
            ( cod-hom-arrow-Precategory C (ν₀ f))))
        ( mor-obj-arrow-Precategory C (M₀ (M₀ f)))
        ( δ₀-pushout-comm f)
    pr2 (δ₀ f) =
      ( comm-morphism-from-inr-pushout-obj-Precategory C _ _ _ _ _ (pushout-id-dom-comonad-Precategory f) _ _ _ _) ∙
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
            ( ( comm-morphism-from-inl-pushout-obj-Precategory C _ _ _ _ _ (pushout-id-dom-comonad-Precategory f) _ _ _ (δ₀-pushout-comm f)) ∙
              ( inv (associative-comp-hom-Precategory C _ _ _)))
  
        δ₀c' : (f : obj-Precategory C1) →
          comp-hom-Precategory C (cha (δ₀ f)) (pr2 (M₀ f)) ＝
          pr2 (M₀ (M₀ f))
        δ₀c' f =
          comm-morphism-from-inr-pushout-obj-Precategory C _ _ _ _ _ (pushout-id-dom-comonad-Precategory f) _ _ _ (δ₀-pushout-comm f)
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
        nδ : 
          is-natural-transformation-Precategory C1 C1 M MM δ₀
        nδ {f} {g} u =
          eq-hom-arrow-Precategory C _ _ _ _
            ( ( right-unit-law-comp-hom-Precategory C _) ∙
              ( inv (left-unit-law-comp-hom-Precategory C _)))
            ( ( preserves-postcomp-morphism-from-pushout-obj-Precategory C _ _ _
                 _ _ (pushout-id-dom-comonad-Precategory f) _
                 ( comp-hom-Precategory C
                   ( cod-hom-arrow-Precategory C (M₁ _ _ (pr1 β f)))
                   ( comp-hom-Precategory C
                     ( cod-hom-arrow-Precategory C (pr1 β (L₀ f)))
                     ( cod-hom-arrow-Precategory C (ν₀ f))))
                 ( mor-obj-arrow-Precategory C (M₀ (M₀ f)))
                 ( δ₀-pushout-comm f)
                 ( cod-hom-arrow-Precategory C (M₁ (M₀ f) (M₀ g) (M₁ f g u)))) ∙
              ( is-unique-morphism-from-pushout-obj-Precategory C _ _ _
                ( Lmor f)
                ( εtop f) (pushout-id-dom-comonad-Precategory f)
                _ _ _ _
                ( comp-hom-Precategory C
                  ( cod-hom-arrow-Precategory C (δ₀ g))
                  ( cod-hom-arrow-Precategory C (M₁ f g u)))
                ( ap cha (right1b u))
                ( ( associative-comp-hom-Precategory C _ _ _) ∙
                  ( ap (comp-hom-Precategory C (cha (δ₀ g)))
                    ( pr2 (M₁ f g u))) ∙
                  ( inv (associative-comp-hom-Precategory C _ _ _)) ∙
                  ( ap (precomp-hom-Precategory C (dha (M₁ f g u)) _)
                    ( δ₀c' g)) ∙
                  ( inv (pr2 (M₁ (M₀ f) (M₀ g) (M₁ f g u)))))))
    open Dummy5 public

    comul-id-dom-comonad-Precategory : natural-transformation-Precategory C1 C1 M MM
    comul-id-dom-comonad-Precategory = δ₀ , nδ

    private module ComonadLaws where
      abstract
        hom-family-associativity-law-id-dom-comonad-Precategory :
          (f : obj-Precategory C1) →
          comp-hom-Precategory C1
            (M₁ _ _ (δ₀ f))
            (δ₀ f) ＝
          comp-hom-Precategory C1
            (δ₀ (M₀ f))
            (δ₀ f)
        hom-family-associativity-law-id-dom-comonad-Precategory f =
          eq-hom-arrow-Precategory C _ _ _ _
            ( ( right-unit-law-comp-hom-Precategory C _) ∙
              ( ap dha (preserves-id-id-dom-comonad-Precategory f)) ∙
              ( inv (right-unit-law-comp-hom-Precategory C _)))
            (is-unique-pair-morphism-from-pushout-obj-Precategory C _ _ _
              (Lmor f) (εtop f) (pushout-id-dom-comonad-Precategory f) _ _
              (ap cha left)
              right)
          where
    
          right :
            comp-hom-Precategory C
              ( comp-hom-Precategory C
                ( cha (M₁ _ _ (δ₀ f)))
                ( cha (δ₀ f)))
              ( mor-obj-arrow-Precategory C (M₀ f)) ＝
            comp-hom-Precategory C
              ( comp-hom-Precategory C
                ( cha (δ₀ (M₀ f)))
                ( cha (δ₀ f)))
              ( mor-obj-arrow-Precategory C (M₀ f))
          right =
            ( associative-comp-hom-Precategory C _ _ _) ∙
            ( ap (comp-hom-Precategory C (cha (M₁ _ _ (δ₀ f))))
              ( comm-morphism-from-inr-pushout-obj-Precategory C _ _ _ (Lmor f)
                 (εtop f) (pushout-id-dom-comonad-Precategory f) _ _ _ (δ₀-pushout-comm f))) ∙
            ( ap
              ( precomp-hom-Precategory C
                ( mor-obj-arrow-Precategory C (M₀ (M₀ f)))
                ( _))
              ( eq-bottom-hom-id-dom-comonad-Precategory (M₀ f) (M₀ (M₀ f)) (δ₀ f))) ∙
            ( comm-morphism-from-inr-pushout-obj-Precategory C _ _ _ (Lmor (M₀ f)) (εtop (M₀ f)) (pushout-id-dom-comonad-Precategory (M₀ f)) _ _ _ _) ∙
            ( right-unit-law-comp-hom-Precategory C _) ∙
            ( inv
              ( ( associative-comp-hom-Precategory C _ _ _) ∙
                ( ap (comp-hom-Precategory C (cha (δ₀ (M₀ f))))
                  ( comm-morphism-from-inr-pushout-obj-Precategory C _ _ _ (Lmor f)
                    (εtop f) (pushout-id-dom-comonad-Precategory f) _ _ _ (δ₀-pushout-comm f))) ∙
                ( comm-morphism-from-inr-pushout-obj-Precategory C _ _ _
                   (Lmor (M₀ f)) (εtop (M₀ f)) (pushout-id-dom-comonad-Precategory (M₀ f)) _ _ _ _)))
    
          left :
            comp-hom-Precategory C1
              ( comp-hom-Precategory C1
                ( M₁ _ _ (δ₀ f))
                ( δ₀ f))
              (pr1 β f) ＝
            comp-hom-Precategory C1
              ( comp-hom-Precategory C1
                ( δ₀ (M₀ f))
                ( δ₀ f))
              (pr1 β f)
          left =
            ( associative-comp-hom-Precategory C1 _ _ _) ∙
            ( ap (comp-hom-Precategory C1 (M₁ _ _ (δ₀ f)))
              ( ( δ₀c f) ∙
                ( associative-comp-hom-Precategory C1 _ _ _))) ∙
            ( inv (associative-comp-hom-Precategory C1 _ _ _)) ∙
            ( ap
              ( precomp-hom-Precategory C1
                ( comp-hom-Precategory C1 (pr1 β (L₀ f)) (pr1 ν f))
                ( _))
               ( ( inv (preserves-comp-functor-Precategory C1 C1 M (δ₀ f) (pr1 β f))) ∙
                 ( ap (M₁ _ _) (δ₀c f)) ∙
                 ( preserves-comp-functor-Precategory C1 C1 M _ _))) ∙
            ( associative-comp-hom-Precategory C1 _ (M₁ _ _ (pr1 ν f)) _) ∙
            ( ap
              ( comp-hom-Precategory C1
                ( M₁ _ _
                  ( comp-hom-Precategory C1
                    ( M₁ _ _ (pr1 β f))
                    ( pr1 β (L₀ f)))))
              ( ( inv (associative-comp-hom-Precategory C1 (M₁ _ _ (pr1 ν f)) (pr1 β (L₀ f)) (pr1 ν f))) ∙
                ( ap (precomp-hom-Precategory C1 (pr1 ν f) _)
                  ( pr2 β (pr1 ν f))) ∙
                ( associative-comp-hom-Precategory C1 (pr1 β (L₀ (L₀ f))) (L₁ (pr1 ν f)) (pr1 ν f)) ∙
                ( ap (λ x → comp-hom-Precategory C1 (pr1 β (L₀ (L₀ f))) (pr1 x f))
                  ( Lass)))) ∙
            ( inv
              ( ( associative-comp-hom-Precategory C1 _ _ _) ∙
                ( ap (comp-hom-Precategory C1 (δ₀ (M₀ f)))
                  ( ( δ₀c f) ∙
                    ( ap (precomp-hom-Precategory C1 (pr1 ν f) _)
                      ( pr2 β (pr1 β f))) ∙
                    ( associative-comp-hom-Precategory C1 (pr1 β (M₀ f)) (L₁ (pr1 β f)) (pr1 ν f)))) ∙
                ( inv (associative-comp-hom-Precategory C1 (δ₀ (M₀ f)) (pr1 β (M₀ f)) _)) ∙
                ( ap
                  ( precomp-hom-Precategory C1
                    ( comp-hom-Precategory C1 (L₁ (pr1 β f)) (pr1 ν f))
                    ( _))
                  ( δ₀c (M₀ f))) ∙
                ( associative-comp-hom-Precategory C1 _ (pr1 ν (M₀ f)) _) ∙
                ( ap
                  ( comp-hom-Precategory C1
                    ( comp-hom-Precategory C1 (M₁ _ _ (pr1 β (M₀ f))) (pr1 β (L₀ (M₀ f)))))
                  ( ( inv (associative-comp-hom-Precategory C1 (pr1 ν (M₀ f)) (L₁ (pr1 β f)) (pr1 ν f))) ∙
                    ( ap (precomp-hom-Precategory C1 (pr1 ν f) _)
                      ( inv (pr2 ν (pr1 β f)))) ∙
                    ( associative-comp-hom-Precategory C1 (L₁ (L₁ (pr1 β f))) (pr1 ν (L₀ f)) (pr1 ν f)))) ∙
                ( inv (associative-comp-hom-Precategory C1 _ (L₁ (L₁ (pr1 β f))) _)) ∙
                ( ap
                  ( precomp-hom-Precategory C1
                    ( comp-hom-Precategory C1
                      ( pr1 ν (L₀ f))
                      ( pr1 ν f))
                    ( _))
                  ( ( associative-comp-hom-Precategory C1 _ _ _) ∙
                    ( ap (comp-hom-Precategory C1 (M₁ _ _ (pr1 β (M₀ f))))
                      ( inv (pr2 βL (pr1 β f)))) ∙
                    ( inv (associative-comp-hom-Precategory C1 (M₁ _ _ (pr1 β (M₀ f))) (M₁ _ _ (L₁ (pr1 β f))) (pr1 β (L₀ (L₀ f))))) ∙
                    ( ap
                      ( precomp-hom-Precategory C1 (pr1 β (L₀ (L₀ f))) _)
                      ( ( inv (preserves-comp-functor-Precategory C1 C1 M (pr1 β (M₀ f)) (L₁ (pr1 β f)))) ∙
                        ( ap (M₁ _ _) (inv (pr2 β (pr1 β f)))))))) ∙
                ( associative-comp-hom-Precategory C1 _ _ _)))

        associativity-law-id-dom-comonad-Precategory :
          comp-natural-transformation-Precategory C1 C1 M MM MMM
            ( left-whisker-natural-transformation-Precategory C1 C1 C1 M MM M
              comul-id-dom-comonad-Precategory)
            comul-id-dom-comonad-Precategory ＝
          comp-natural-transformation-Precategory C1 C1 M MM MMM
            ( right-whisker-natural-transformation-Precategory C1 C1 C1 M MM comul-id-dom-comonad-Precategory M)
            comul-id-dom-comonad-Precategory
        associativity-law-id-dom-comonad-Precategory =
          eq-htpy-hom-family-natural-transformation-Precategory C1 C1 M MMM _ _
            ( hom-family-associativity-law-id-dom-comonad-Precategory)

        hom-family-left-counit-law-id-dom-comonad-Precategory :
          (f : obj-Precategory C1) →
          comp-hom-Precategory C1
            (M₁ _ _ (pr1 α f))
            (δ₀ f) ＝
          id-hom-Precategory C1
        hom-family-left-counit-law-id-dom-comonad-Precategory f =
          eq-hom-arrow-Precategory C _ _ _ _
            ( right-unit-law-comp-hom-Precategory C _) -- Spice things up a bit
            ( is-id-morphism-from-pushout-obj-Precategory C _ _ _ (Lmor f)
              (εtop f) (pushout-id-dom-comonad-Precategory f) _ (ap cha right) left)
          where
    
          left :
            comp-hom-Precategory C
              ( comp-hom-Precategory C
                ( cod-hom-arrow-Precategory C (M₁ _ _ (pr1 α f)))
                ( cod-hom-arrow-Precategory C (δ₀ f)))
              ( mor-obj-arrow-Precategory C (M₀ f)) ＝
            mor-obj-arrow-Precategory C (M₀ f)
          left =
            ( associative-comp-hom-Precategory C _ _ _) ∙
            ( ap (comp-hom-Precategory C (cod-hom-arrow-Precategory C (M₁ _ _ (pr1 α f))))
              ( comm-morphism-from-inr-pushout-obj-Precategory C _ _ _ (Lmor f)
                 (εtop f) (pushout-id-dom-comonad-Precategory f) _ _ _ _)) ∙
            ( square-hom-arrow-Precategory C (M₁ _ _ (pr1 α f))) ∙
            ( right-unit-law-comp-hom-Precategory C _)
    
          right :
            comp-hom-Precategory C1
              ( comp-hom-Precategory C1
                ( M₁ _ _ (pr1 α f))
                ( δ₀ f))
              ( pr1 β f) ＝
            pr1 β f
          right =
            ( associative-comp-hom-Precategory C1 _ _ _) ∙
            ( ap (comp-hom-Precategory C1 (M₁ _ _ (pr1 α f)))
              ( ( δ₀c f) ∙
                ( associative-comp-hom-Precategory C1 _ _ _))) ∙
            ( inv (associative-comp-hom-Precategory C1 (M₁ _ _ (pr1 α f)) (M₁ _ _ (pr1 β f)) _)) ∙
            ( ap
              ( precomp-hom-Precategory C1 
                ( comp-hom-Precategory C1
                  ( pr1 β (L₀ f))
                  ( pr1 ν f))
                ( _))
              ( ( inv (preserves-comp-functor-Precategory C1 C1 M (pr1 α f) (pr1 β f))) ∙
                ( ap (λ x → (M₁ _ _ (pr1 x f))) factor-id-dom-comonad-Precategory))) ∙
            ( inv (associative-comp-hom-Precategory C1 (M₁ _ _ (pr1 ε f)) _ _)) ∙
            ( ap (precomp-hom-Precategory C1 (pr1 ν f) _)
              ( pr2 β (pr1 ε f))) ∙
            ( associative-comp-hom-Precategory C1 (pr1 β f) (L₁ (pr1 ε f)) (pr1 ν f)) ∙
            ( ap (λ x → comp-hom-Precategory C1 (pr1 β f) (pr1 x f)) Lleft) ∙
            ( right-unit-law-comp-hom-Precategory C1 _)
    
        left-counit-law-id-dom-comonad-Precategory :
          comp-natural-transformation-Precategory C1 C1 M MM M Mα comul-id-dom-comonad-Precategory ＝
          id-natural-transformation-Precategory C1 C1 M
        left-counit-law-id-dom-comonad-Precategory =
          eq-htpy-hom-family-natural-transformation-Precategory C1 C1 M M _ _
            ( hom-family-left-counit-law-id-dom-comonad-Precategory)

        hom-family-right-counit-law-id-dom-comonad-Precategory :
          (f : obj-Precategory C1) →
          comp-hom-Precategory C1
            (pr1 α (M₀ f))
            (δ₀ f) ＝
          id-hom-Precategory C1
        hom-family-right-counit-law-id-dom-comonad-Precategory f =
          eq-hom-arrow-Precategory C _ _ _ _
            ( left-unit-law-comp-hom-Precategory C _)
            ( is-id-morphism-from-pushout-obj-Precategory C _ _ _ (Lmor f)
               (εtop f) (pushout-id-dom-comonad-Precategory f) _ (ap cha right) left)
          where
            left :
              comp-hom-Precategory C
                ( comp-hom-Precategory C
                  ( cod-hom-arrow-Precategory C (pr1 α (M₀ f)))
                  ( cod-hom-arrow-Precategory C (δ₀ f)))
                ( mor-obj-arrow-Precategory C (M₀ f)) ＝
              mor-obj-arrow-Precategory C (M₀ f)
            left =
              ( associative-comp-hom-Precategory C _ _ _) ∙
              ( ap (comp-hom-Precategory C (cod-hom-arrow-Precategory C (pr1 α (M₀ f))))
                ( comm-morphism-from-inr-pushout-obj-Precategory C _ _ _ (Lmor f)
                   (εtop f) (pushout-id-dom-comonad-Precategory f) _ _ _ _)) ∙
              ( comm-morphism-from-inr-pushout-obj-Precategory C _ _ _
                 (Lmor (M₀ f)) (εtop (M₀ f)) (pushout-id-dom-comonad-Precategory (M₀ f)) _ _ _ _)
                
            right :
              comp-hom-Precategory C1
                ( comp-hom-Precategory C1
                  ( pr1 α (M₀ f))
                  ( δ₀ f))
                ( pr1 β f) ＝
              pr1 β f
            right =
              ( associative-comp-hom-Precategory C1 _ _ _) ∙
              ( ap (comp-hom-Precategory C1 (pr1 α (M₀ f)))
                ( ( δ₀c f) ∙
                  ( associative-comp-hom-Precategory C1 _ _ _))) ∙
              ( inv
                ( associative-comp-hom-Precategory C1
                  ( pr1 α (M₀ f))
                  ( M₁ _ _ (pr1 β f))
                  ( comp-hom-Precategory C1 (pr1 β (L₀ f)) (pr1 ν f)))) ∙
              ( ap
                ( precomp-hom-Precategory C1
                  ( comp-hom-Precategory C1
                    ( pr1 β (L₀ f))
                    ( pr1 ν f))
                  ( _))
                ( inv (pr2 α (pr1 β f)))) ∙
              ( associative-comp-hom-Precategory C1 (pr1 β f) (pr1 α (L₀ f)) _) ∙
              ( ap
                ( comp-hom-Precategory C1 (pr1 β f))
                ( ( inv (associative-comp-hom-Precategory C1 (pr1 α (L₀ f)) (pr1 β (L₀ f)) (pr1 ν f))) ∙
                  ( ap
                    ( λ x → comp-hom-Precategory C1 (pr1 x (L₀ f)) (pr1 ν f))
                    ( factor-id-dom-comonad-Precategory)) ∙
                  ( ap
                    ( λ x → pr1 x f)
                    ( Lright)))) ∙
              ( right-unit-law-comp-hom-Precategory C1 _)

        right-counit-law-id-dom-comonad-Precategory :
          comp-natural-transformation-Precategory C1 C1 M MM M
            ( αM)
            ( comul-id-dom-comonad-Precategory) ＝
          id-natural-transformation-Precategory C1 C1 M
        right-counit-law-id-dom-comonad-Precategory =
          eq-htpy-hom-family-natural-transformation-Precategory C1 C1 M M _ _
            ( hom-family-right-counit-law-id-dom-comonad-Precategory)
    open ComonadLaws public

    id-dom-comonad-Precategory : comonad-Precategory C1
    id-dom-comonad-Precategory =
      ( M , right-id-dom-comonad-Precategory) ,
      comul-id-dom-comonad-Precategory ,
      associativity-law-id-dom-comonad-Precategory ,
      left-counit-law-id-dom-comonad-Precategory ,
      right-counit-law-id-dom-comonad-Precategory
