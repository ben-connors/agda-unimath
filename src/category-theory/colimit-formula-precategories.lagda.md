# Colimits from coequalizers and coproducts in precategories

```agda
module category-theory.colimit-formula-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.cocones-precategories
open import category-theory.colimits-precategories
open import category-theory.constant-functors
open import category-theory.coproducts-in-precategories
open import category-theory.functors-precategories
open import category-theory.left-extensions-precategories
open import category-theory.left-kan-extensions-precategories
open import category-theory.natural-transformations-functors-precategories
open import category-theory.precategories
open import category-theory.terminal-category
open import category-theory.coequalizers-precategories

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

</details>

## Idea

We can construct colimits of functors when the codomain category has coproducts and coequalizers. Specifically, we require the existence of two coproducts for a functor `F : J → C`:

1. `⨆_{j : Ob J} Fj`; and
2. `⨆_{f : i → j ∈ J} Fi`.

For simplicity, we ask that `C` is instead closed under set-indexed coproducts, in which case the colimit exists whenever the objects of `J` form a set. In univalent categories this limits us to domains which are [gaunt categories](category-theory.gaunt-categories.md).

```agda
module _
  {l1 l2 l3 l4 : Level} (C : Precategory l1 l2)
  (q : has-all-coequalizer-obj-Precategory C)
  (i1 : has-all-indexed-coproduct-obj-Precategory C l3)
  (i2 : has-all-indexed-coproduct-obj-Precategory C (l3 ⊔ l4))
  (J : Precategory l3 l4)
  (let Js = obj-Precategory J)
  (F : functor-Precategory J C)
  (let F₀ = obj-functor-Precategory J C F)
  (let F₁ = hom-functor-Precategory J C F)
  where

  coproduct-obj-J₀ :
    indexed-coproduct-obj-Precategory C F₀
  coproduct-obj-J₀ =
    i1 Js F₀

  obj-coproduct-obj-J₀ = obj-indexed-coproduct-obj-Precategory C F₀ coproduct-obj-J₀

  J₁ : UU (l3 ⊔ l4)
  J₁ =
    Σ ( Js)
      ( λ x →
        Σ ( Js)
          ( λ y → hom-Precategory J x y))

  J₁m : J₁ → obj-Precategory C
  J₁m (x , (y , m)) = F₀ x

  coproduct-obj-J₁ :
    indexed-coproduct-obj-Precategory C J₁m
  coproduct-obj-J₁ = i2 J₁ J₁m

  obj-coproduct-obj-J₁ = obj-indexed-coproduct-obj-Precategory C J₁m coproduct-obj-J₁

  iota1 :
    (j : J₁) → hom-Precategory C (J₁m j) obj-coproduct-obj-J₁
  iota1 = pr1 (pr2 (i2 J₁ J₁m))

  iota0 :
    (j : obj-Precategory J) → hom-Precategory C (F₀ j) obj-coproduct-obj-J₀
  iota0 = pr1 (pr2 (i1 Js F₀))

  iota :
    (j : J₁) →
    hom-Precategory C (J₁m j) obj-coproduct-obj-J₀
  iota (x , (y , f)) = iota0 x

  iiota : hom-Precategory C obj-coproduct-obj-J₁ obj-coproduct-obj-J₀
  iiota = mor-from-indexed-coproduct-obj-Precategory C J₁m coproduct-obj-J₁ obj-coproduct-obj-J₀ iota

  iota' :
    (j : J₁) →
    hom-Precategory C (J₁m j) obj-coproduct-obj-J₀
  iota' (x , (y , f)) =
    comp-hom-Precategory C
      (iota0 y)
      (F₁ f) 

  iiota' : hom-Precategory C obj-coproduct-obj-J₁ obj-coproduct-obj-J₀
  iiota' = mor-from-indexed-coproduct-obj-Precategory C J₁m coproduct-obj-J₁ obj-coproduct-obj-J₀ iota'

  candidate : coequalizer-obj-Precategory C iiota iiota'
  candidate = q iiota iiota'

  co : obj-Precategory C
  co = pr1 candidate

  cm : hom-Precategory C obj-coproduct-obj-J₀ co
  cm = pr1 (pr2 candidate)

  cocone-hom :
    (j : obj-Precategory J) →
    (hom-Precategory C (F₀ j) co)
  cocone-hom j =
    comp-hom-Precategory C
      cm
      (iota0 j)
        
  abstract
    cocone-coh :
      {j j' : obj-Precategory J} (f : hom-Precategory J j j') →
      comp-hom-Precategory C (cocone-hom j') (F₁ f) ＝
      cocone-hom j
    cocone-coh {j} {j'} f =
      ( inv
        ( ( ap (comp-hom-Precategory C cm) (compute-mor-from-indexed-coproduct-obj-Precategory C J₁m coproduct-obj-J₁ obj-coproduct-obj-J₀ iota' _)) ∙
          ( inv (associative-comp-hom-Precategory C _ _ _)))) ∙
      ( inv
        ( ( inv (associative-comp-hom-Precategory C _ _ _)) ∙
          ( ap
            ( precomp-hom-Precategory C (iota1 (j , j' , f)) _)
            ( coh-coequalizer-obj-Precategory C iiota iiota' candidate)) ∙
          ( associative-comp-hom-Precategory C _ _ _))) ∙
      ( ap (comp-hom-Precategory C cm) (compute-mor-from-indexed-coproduct-obj-Precategory C J₁m coproduct-obj-J₁ obj-coproduct-obj-J₀ iota _))

  cocone-colimit-formula-Precategory : cocone-Precategory J C F
  cocone-colimit-formula-Precategory = make-cocone-Precategory J C F
    co
    cocone-hom
    (λ f → inv (cocone-coh f))

  module _
    (d : cocone-Precategory J C F)
    (let dob = pr1 d)
    (let dh = component-cocone-Precategory J C F d)
    (let dn = naturality-cocone-Precategory J C F d)
    where

    dmor : hom-Precategory C obj-coproduct-obj-J₀ dob
    dmor =
      mor-from-indexed-coproduct-obj-Precategory C F₀ coproduct-obj-J₀ dob dh

    dmor-coeq-pre :
      (f : J₁) →
      comp-hom-Precategory C dmor (iota f) ＝
      comp-hom-Precategory C dmor (iota' f)
    dmor-coeq-pre (j , j' , f) =
      ( compute-mor-from-indexed-coproduct-obj-Precategory C F₀ coproduct-obj-J₀ dob dh j) ∙
      ( dn f) ∙
      ( ap (precomp-hom-Precategory C (F₁ f) _)
        ( inv
          ( compute-mor-from-indexed-coproduct-obj-Precategory C F₀
              coproduct-obj-J₀ dob dh j'))) ∙
      ( associative-comp-hom-Precategory C _ _ _)

    dmor-coeq :
      comp-hom-Precategory C dmor iiota ＝
      comp-hom-Precategory C dmor iiota'
    dmor-coeq =
      ( inv (postcomp-mor-from-indexed-coproduct-obj-Precategory C J₁m
              coproduct-obj-J₁ obj-coproduct-obj-J₀ iota dmor)) ∙
      ( ap (mor-from-indexed-coproduct-obj-Precategory C J₁m coproduct-obj-J₁ dob) (eq-htpy dmor-coeq-pre)) ∙
      ( postcomp-mor-from-indexed-coproduct-obj-Precategory C J₁m coproduct-obj-J₁ obj-coproduct-obj-J₀ iota' dmor)

    themor : hom-Precategory C co dob
    themor = mor-from-coequalizer-obj-Precategory C iiota iiota' candidate dmor dmor-coeq

    abstract
      themor-factor :
        (a : obj-Precategory J) →
        comp-hom-Precategory C themor (cocone-hom a) ＝
        dh a
      themor-factor a =
        ( inv (associative-comp-hom-Precategory C _ _ _)) ∙
        ( ap
          ( precomp-hom-Precategory C (iota0 a) _)
          ( compute-mor-from-coequalizer-obj-Precategory C iiota iiota' candidate dmor dmor-coeq)) ∙
        ( pr2 (pr1 (pr2 (pr2 (i1 Js F₀)) dob dh)) a)

    module _
      (another : hom-Precategory C co dob)
      (anothercoh : (a : obj-Precategory J) →
        comp-hom-Precategory C another (cocone-hom a) ＝
        dh a)
      where

      abstract
        theeq : themor ＝ another
        theeq = is-unique-mor-from-coequalizer-obj-Precategory C iiota iiota'
          candidate dmor dmor-coeq another
          ( inv
            ( is-unique-mor-from-indexed-coproduct-obj-Precategory C F₀
              coproduct-obj-J₀ dob dh _
              ( λ a →
                ( associative-comp-hom-Precategory C _ _ _) ∙
                ( anothercoh a))))

 
  module _
    (d : obj-Precategory C)
    (let themap = cocone-map-Precategory J C F cocone-colimit-formula-Precategory d)
    where
    
    theinverse :
      natural-transformation-Precategory J C
        ( F)
        ( constant-functor-Precategory J C d) →
      hom-Precategory C co d
    theinverse N = themor (d , N)    

    H : theinverse ∘ themap ~ id
    H x = theeq _ x refl-htpy

    G : themap ∘ theinverse ~ id 
    G x = eq-htpy-hom-family-natural-transformation-Precategory J C F
           (constant-functor-Precategory J C d) _ _
      ( themor-factor (d , x))

  is-colimit-cocone-colimit-formula-Precategory : is-colimit-cocone-Precategory J C F cocone-colimit-formula-Precategory
  is-colimit-cocone-colimit-formula-Precategory d = is-equiv-is-invertible (theinverse d) (G d) (H d)

  colimit-formula-Precategory : colimit-Precategory J C F
  pr1 colimit-formula-Precategory =
    cocone-colimit-formula-Precategory
  pr2 colimit-formula-Precategory =
    is-colimit-cocone-colimit-formula-Precategory
```
