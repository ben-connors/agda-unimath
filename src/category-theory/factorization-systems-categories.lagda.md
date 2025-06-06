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
open import category-theory.arrow-precategories

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

We define algebraic weak factorization systems in several steps:

## Definitions

--```agda
--module _
--  {l1 l2 : Level} (C : Category l1 l2)
--  {x y : obj-Category C} (f : hom-Category C x y)
--  where
--
--  is-fact-hom-Category :
--    (z : obj-Category C)
--    (i : hom-Category C x z) (p : hom-Category C z y)  →
--    UU l2
--  is-fact-hom-Category z i p =
--    comp-hom-Category C p i ＝ f
--
--  fact-hom-Category : UU (l1 ⊔ l2)
--  fact-hom-Category =
--    Σ ( obj-Category C)
--      ( λ z →
--        Σ ( (hom-Category C x z) × (hom-Category C z y))
--          ( λ ip →
--            is-fact-hom-Category z (pr1 ip) (pr2 ip)))
--
--  obj-fact-hom-Category : fact-hom-Category → obj-Category C
--  obj-fact-hom-Category = pr1
--
--  left-mor-fact-hom-Category :
--    (fact : fact-hom-Category) →
--    hom-Category C x (obj-fact-hom-Category fact)
--  left-mor-fact-hom-Category fact = pr1 (pr1 (pr2 fact))
--
--  right-mor-fact-hom-Category :
--    (fact : fact-hom-Category) →
--    hom-Category C (obj-fact-hom-Category fact) y
--  right-mor-fact-hom-Category fact = pr2 (pr1 (pr2 fact))
--
--  is-fact-fact-hom-Category :
--    (fact : fact-hom-Category) →
--    is-fact-hom-Category
--      ( obj-fact-hom-Category fact)
--      ( left-mor-fact-hom-Category fact)
--      ( right-mor-fact-hom-Category fact)
--  is-fact-fact-hom-Category fact = pr2 (pr2 fact)
--
--  eq-fact-hom-Category :
--    (f1 f2 : fact-hom-Category) →
--    (e : iso-Category C (obj-fact-hom-Category f1) (obj-fact-hom-Category f2))
--    (G :
--      comp-hom-Category C
--        ( hom-iso-Category C e) (left-mor-fact-hom-Category f1) ＝
--      left-mor-fact-hom-Category f2)
--    (H :
--      comp-hom-Category C
--        ( right-mor-fact-hom-Category f1) (hom-inv-iso-Category C e) ＝
--      right-mor-fact-hom-Category f2) →
--    f1 ＝ f2
--  eq-fact-hom-Category f1 f2 e G H =
--    eq-pair-Σ
--      ( eq-iso-Category C e)
--      ( eq-pair-Σ
--        ( eq-pair
--          ( ( preserves-tr (λ z x → pr1 (pr1 x)) (eq-iso-Category C e) (pr2 f1)) ∙
--            ( compute-left-tr-eq-iso-Category C e _) ∙
--            ( G))
--          ( ( preserves-tr (λ z x → pr2 (pr1 x)) (eq-iso-Category C e) (pr2 f1)) ∙
--            ( compute-right-tr-eq-iso-Category C _ e) ∙
--            ( H)))
--        ( eq-is-prop (is-set-hom-Category C _ _ _ _)))
```

A factorization is for each `f : x → y` a choice of `Zf : Ob C` and morphisms `Lf : x → Zf` and `Rf : Zf → y` such that `Rf ∘ Lf = f`.

```agda
module _
  {l1 l2 : Level} (C : Category l1 l2)
  (let C1 = arrow-Category C)
  (let dom = dom-obj-arrow-Category C)
  (let cod = cod-obj-arrow-Category C)
  (let mor = mor-obj-arrow-Category C)
  (let dom-mor = dom-hom-arrow-Category C)
  (let cod-mor = cod-hom-arrow-Category C)
  where

  middle-fact-Category : UU (l1 ⊔ l2)
  middle-fact-Category = obj-Category C1 → obj-Category C

  left-fact-Category : middle-fact-Category → UU (l1 ⊔ l2)
  left-fact-Category Z =
    (f : obj-Category C1) →
    hom-Category C (dom f) (Z f)

  right-fact-Category : middle-fact-Category → UU (l1 ⊔ l2)
  right-fact-Category Z =
    (f : obj-Category C1) →
    hom-Category C (Z f) (cod f)

  is-fact-Category :
    (Z : middle-fact-Category)
    (L : left-fact-Category Z)
    (R : right-fact-Category Z) →
    UU (l1 ⊔ l2)
  is-fact-Category Z L R =
    (f : obj-Category C1) →
    comp-hom-Category C (R f) (L f) ＝ mor f
```

Now we extend this to the necessary structure to give three functors: `Z : C[1] → C`, `L : C[1] → C[1]`, and `R : C[1] → C[1]` with the restrictions that:

1. `d⁰ ∘ L = Z = d¹ ∘ R`;
2. `d¹ ∘ L = dom`; and
3. `d⁰ ∘ R = cod`.

Doing it in steps instead of requiring three functors and equalities (or a single functor `C[1] → C[2]` with equalities) allows us to ensure that the three conditions above hold judgementally at each morphism in `C` which simplifies both statements and proofs significantly.

```agda
  ext-middle-fact-Category :
    (Z : middle-fact-Category) → UU (l1 ⊔ l2)
  ext-middle-fact-Category Z =
    Σ ( {f g : obj-Category C1} (u : hom-Category C1 f g) →
        hom-Category C (Z f) (Z g))
      (λ M → is-functor-map-Category C1 C (Z , M))

  hom-ext-middle-fact-Category :
    (Z : middle-fact-Category)
    (M : ext-middle-fact-Category Z)
    {f g : obj-Category C1}
    (u : hom-Category C1 f g) →
    hom-Category C (Z f) (Z g)
  hom-ext-middle-fact-Category Z M = pr1 M
```

This data extends `Z` to a functor:

```agda
  functor-ext-middle-fact-Category :
    (Z : middle-fact-Category)
    (M : ext-middle-fact-Category Z) →
    functor-Category C1 C
  functor-ext-middle-fact-Category Z M = Z , M

  is-ext-left-fact-Category :
    (Z : middle-fact-Category)
    (M : ext-middle-fact-Category Z)
    (L : left-fact-Category Z) →
    UU (l1 ⊔ l2)
  is-ext-left-fact-Category Z M L =
    {f g : obj-Category C1}
    (u : hom-Category C1 f g) →
    coherence-square-hom-Precategory (precategory-Category C)
      ( dom-mor u)
      ( L f)
      ( L g)
      ( (hom-ext-middle-fact-Category Z M) u)
```

This property extends `L` to a functor:

```agda
  functor-is-ext-left-fact-Category :
    (Z : middle-fact-Category)
    (M : ext-middle-fact-Category Z)
    (L : left-fact-Category Z)
    (N : is-ext-left-fact-Category Z M L) →
    functor-Category C1 C1
  pr1 (functor-is-ext-left-fact-Category Z M L N) f =
    ((dom f) , (Z f)) , (L f)
  pr1 (pr2 (functor-is-ext-left-fact-Category Z M L N)) {f} {g} u =
    ((dom-mor u) , (pr1 M) u) , N u
  pr1 (pr2 (pr2 (functor-is-ext-left-fact-Category Z M L N))) {f} {g} {h} u v =
    eq-hom-arrow-Category C _ _ _ _
      ( refl)
      ( preserves-comp-functor-Category C1 C
        ( functor-ext-middle-fact-Category Z M)
        ( _)
        ( _))
  pr2 (pr2 (pr2 (functor-is-ext-left-fact-Category Z M L N))) f =
    eq-hom-arrow-Category C _ _ _ _
      ( refl)
      ( preserves-id-functor-Category C1 C
        ( functor-ext-middle-fact-Category Z M)
        ( _))

  is-ext-right-fact-Category :
    (Z : middle-fact-Category)
    (M : ext-middle-fact-Category Z)
    (R : right-fact-Category Z) →
    UU (l1 ⊔ l2)
  is-ext-right-fact-Category Z M R =
    {f g : obj-Category C1}
    (u : hom-Category C1 f g) →
    coherence-square-hom-Precategory (precategory-Category C)
      ( (hom-ext-middle-fact-Category Z M) u)
      ( R f)
      ( R g)
      ( cod-mor u)
```

This property extends `R` to a functor:

```agda
  functor-is-ext-right-fact-Category :
    (Z : middle-fact-Category)
    (M : ext-middle-fact-Category Z)
    (R : right-fact-Category Z)
    (N : is-ext-right-fact-Category Z M R) →
    functor-Category C1 C1
  pr1 (functor-is-ext-right-fact-Category Z M R N) f =
    ((Z f) , (cod f)) , (R f)
  pr1 (pr2 (functor-is-ext-right-fact-Category Z M R N)) {f} {g} u =
    ((pr1 M) u , (cod-mor u)) , N u
  pr1 (pr2 (pr2 (functor-is-ext-right-fact-Category Z M R N))) {f} {g} {h} u v =
    eq-hom-arrow-Category C _ _ _ _
      ( preserves-comp-functor-Category C1 C
        ( functor-ext-middle-fact-Category Z M)
        ( _)
        ( _))
      ( refl)
  pr2 (pr2 (pr2 (functor-is-ext-right-fact-Category Z M R N))) f =
    eq-hom-arrow-Category C _ _ _ _
      ( preserves-id-functor-Category C1 C
        ( functor-ext-middle-fact-Category Z M)
        ( _))
      ( refl)
```

We pack this data into a single type:

```
  funct-fact-Category : UU (l1 ⊔ l2)
  funct-fact-Category =
    Σ ( middle-fact-Category)
      ( λ Z →
        Σ ( ( ( left-fact-Category Z) × (right-fact-Category Z)) ×
            ( ext-middle-fact-Category Z))
          ( λ LRE →
            ( is-fact-Category Z (pr1 (pr1 LRE)) (pr2 (pr1 LRE))) ×
            ( ( is-ext-left-fact-Category Z (pr2 LRE) (pr1 (pr1 LRE))) ×
              ( is-ext-right-fact-Category Z (pr2 LRE) (pr2 (pr1 LRE))))))

  middle-funct-fact-Category :
    funct-fact-Category → middle-fact-Category
  middle-funct-fact-Category = pr1

  left-funct-fact-Category :
    (F : funct-fact-Category) →
    left-fact-Category (middle-funct-fact-Category F)
  left-funct-fact-Category = pr1 ∘ pr1 ∘ pr1 ∘ pr2

  right-funct-fact-Category :
    (F : funct-fact-Category) →
    right-fact-Category (middle-funct-fact-Category F)
  right-funct-fact-Category = pr2 ∘ pr1 ∘ pr1 ∘ pr2

  is-fact-funct-fact-Category :
    (F : funct-fact-Category) →
    is-fact-Category
      (middle-funct-fact-Category F)
      (left-funct-fact-Category F)
      (right-funct-fact-Category F)
  is-fact-funct-fact-Category = pr1 ∘ pr2 ∘ pr2

  ext-middle-funct-fact-Category :
    (F : funct-fact-Category) →
    ext-middle-fact-Category (middle-funct-fact-Category F)
  ext-middle-funct-fact-Category = pr2 ∘ pr1 ∘ pr2

  is-ext-left-funct-fact-Category :
    (F : funct-fact-Category) →
    is-ext-left-fact-Category
      (middle-funct-fact-Category F)
      (ext-middle-funct-fact-Category F)
      (left-funct-fact-Category F)
  is-ext-left-funct-fact-Category = pr1 ∘ pr2 ∘ pr2 ∘ pr2

  is-ext-right-funct-fact-Category :
    (F : funct-fact-Category) →
    is-ext-right-fact-Category
      (middle-funct-fact-Category F)
      (ext-middle-funct-fact-Category F)
      (right-funct-fact-Category F)
  is-ext-right-funct-fact-Category = pr2 ∘ pr2 ∘ pr2 ∘ pr2
```
