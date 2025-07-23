# Colimits in functor precategories

```agda
module category-theory.colimits-precategory-of-functors where
```

<details><summary>Imports</summary>

```agda
open import category-theory.cocones-precategories
open import category-theory.colimits-precategories
open import category-theory.cocomplete-precategories
open import category-theory.constant-functors
open import category-theory.functors-precategories
open import category-theory.natural-transformations-functors-precategories
open import category-theory.precategories
open import category-theory.precategory-of-functors

open import foundation.action-on-identifications-functions
open import foundation.sets
open import foundation.homotopies

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels
```

</details>

## Idea

Given a pair of precategories `I, C` and a functor `F : J → Cᴵ` where `Cᴵ` is the precategory of functors from `I` to `C`, if `C` has all limits of shape `J` then the functor `F` has a colimit in `Cᴵ` which is given at `i : I` by the colimit of the composite

```text
     F      evᵢ
  J --→ Cᴵ ----→ C
```

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (I : Precategory l1 l2)
  (C : Precategory l3 l4)
  (J : Precategory l5 l6)
  (colim : has-all-colimits-of-shape-Precategory C J)
  (let Cᴵ = functor-precategory-Precategory I C)
  (F : functor-Precategory J Cᴵ)
  (let F₀ = obj-functor-Precategory J Cᴵ F)
  (let Fev = λ i → comp-functor-Precategory J Cᴵ C (ev-functor-Precategory I C i) F)
  (let hom-colim = λ i → hom-cocone-colimit-Precategory J C (Fev i) (colim (Fev i)))
  (let component-colim = λ i → component-colimit-Precategory J C (Fev i) (colim (Fev i)))
  (let compute-colim = λ i → compute-hom-cocone-colimit-Precategory J C (Fev i) (colim (Fev i)))
  where

  obj-vertex-colimit-functor-Precategory : obj-Precategory I → obj-Precategory C
  obj-vertex-colimit-functor-Precategory i =
    vertex-colimit-Precategory J C
      ( Fev i)
      ( colim (Fev i))

  hom-vertex-colim-functor-Precategory-cocone : (i j : obj-Precategory I) →
    hom-Precategory I i j →
    cocone-Precategory J C (Fev i)
  pr1 (hom-vertex-colim-functor-Precategory-cocone i j f) =
    obj-vertex-colimit-functor-Precategory j
  pr2 (hom-vertex-colim-functor-Precategory-cocone i j f) =
    comp-natural-transformation-Precategory J C (Fev i) (Fev j)
      ( constant-functor-Precategory J C
        ( obj-vertex-colimit-functor-Precategory j))
      ( natural-transformation-cocone-Precategory J C
        ( Fev j)
        ( cocone-colimit-Precategory J C (Fev j) (colim (Fev j))))
      ( right-whisker-natural-transformation-Precategory Cᴵ C J
        ( ev-functor-Precategory I C i)
        ( ev-functor-Precategory I C j)
        ( ev-trans-Precategory I C i j f) F)

  hom-vertex-colim-functor-Precategory : (i j : obj-Precategory I) →
    hom-Precategory I i j →
    hom-Precategory C
      ( obj-vertex-colimit-functor-Precategory i)
      ( obj-vertex-colimit-functor-Precategory j)
  hom-vertex-colim-functor-Precategory i j f =
    hom-colim i
      ( hom-vertex-colim-functor-Precategory-cocone i j f)

  compute-hom-vertex-colim-functor-Precategory : (i j : obj-Precategory I) →
    (f : hom-Precategory I i j) → (c : obj-Precategory J) →
    comp-hom-Precategory C
      ( hom-vertex-colim-functor-Precategory i j f)
      ( component-colim i c) ＝
    comp-hom-Precategory C
      ( component-colim j c)
      ( hom-functor-Precategory I C (F₀ c) f)
  compute-hom-vertex-colim-functor-Precategory i j f c =
    compute-colim i
     ( hom-vertex-colim-functor-Precategory-cocone i j f)
     ( c)

  preserves-id-hom-vertex-colim-functor-Precategory : (i : obj-Precategory I) →
    hom-vertex-colim-functor-Precategory i i (id-hom-Precategory I) ＝
    id-hom-Precategory C
  preserves-id-hom-vertex-colim-functor-Precategory i =
    eq-htpy-hom-cocone-colimit-Precategory J C (Fev i) (colim (Fev i))
      _
      _
      ( λ c →
        ( compute-colim i _ c) ∙
        ( ap
          ( comp-hom-Precategory C
            ( component-colim i c))
          ( preserves-id-functor-Precategory I C (F₀ c) i)) ∙
        ( right-unit-law-comp-hom-Precategory C _) ∙
        ( inv (left-unit-law-comp-hom-Precategory C _)))

  preserves-comp-hom-vertex-colim-functor-Precategory :
    {i j k : obj-Precategory I} →
    (g : hom-Precategory I j k) (f : hom-Precategory I i j) →
    hom-vertex-colim-functor-Precategory i k (comp-hom-Precategory I g f) ＝
    comp-hom-Precategory C
      ( hom-vertex-colim-functor-Precategory j k g)
      ( hom-vertex-colim-functor-Precategory i j f)
  preserves-comp-hom-vertex-colim-functor-Precategory {i} {j} {k} g f =
    eq-htpy-hom-cocone-colimit-Precategory J C (Fev i) (colim (Fev i)) _ _
      ( λ c →
        ( compute-colim i _ c) ∙
        ( ap
          ( comp-hom-Precategory C
            ( component-colimit-Precategory J C (Fev k) (colim (Fev k)) c))
          ( preserves-comp-functor-Precategory I C (F₀ c) g f)) ∙
        ( inv
          ( associative-comp-hom-Precategory C
            ( component-colimit-Precategory J C (Fev k) (colim (Fev k)) c)
            ( hom-functor-Precategory I C (F₀ c) g)
            ( hom-functor-Precategory I C (F₀ c) f))) ∙
        ( inv
          ( ( associative-comp-hom-Precategory C
              ( hom-vertex-colim-functor-Precategory j k g)
              ( hom-vertex-colim-functor-Precategory i j f)
              ( component-colim i c)) ∙
            ( ap
              ( comp-hom-Precategory C
                ( hom-vertex-colim-functor-Precategory j k g))
              ( compute-colim i _ c)) ∙
            ( inv
              ( associative-comp-hom-Precategory C
                ( hom-vertex-colim-functor-Precategory j k g)
                ( component-colim j c)
                ( hom-functor-Precategory I C (F₀ c) f))) ∙
            ( ap
              ( precomp-hom-Precategory C
                ( hom-functor-Precategory I C (F₀ c) f)
                ( _))
              ( compute-colim j _ c)))))

  vertex-colim-functor-Precategory : functor-Precategory I C
  pr1 vertex-colim-functor-Precategory = obj-vertex-colimit-functor-Precategory
  pr1 (pr2 vertex-colim-functor-Precategory) {x} {y} =
    hom-vertex-colim-functor-Precategory x y
  pr1 (pr2 (pr2 vertex-colim-functor-Precategory)) =
    preserves-comp-hom-vertex-colim-functor-Precategory
  pr2 (pr2 (pr2 vertex-colim-functor-Precategory)) =
    preserves-id-hom-vertex-colim-functor-Precategory

  component-colim-functor-Precategory :
    (c : obj-Precategory J) →
    hom-Precategory Cᴵ (F₀ c) vertex-colim-functor-Precategory
  pr1 (component-colim-functor-Precategory c) i =
    component-colim i c
  pr2 (component-colim-functor-Precategory c) {i} {j} f =
    compute-colim i _ c

  cocone-colim-functor-Precategory :
    cocone-Precategory J Cᴵ F
  cocone-colim-functor-Precategory = make-cocone-Precategory J Cᴵ F
    ( vertex-colim-functor-Precategory)
    ( component-colim-functor-Precategory)
    ( λ {c} {d} f →
      eq-htpy-hom-family-natural-transformation-Precategory I C
        ( F₀ c)
        ( vertex-colim-functor-Precategory)
        ( _)
        ( _)
        ( λ i →
          naturality-cocone-Precategory J C (Fev i)
            ( cocone-colimit-Precategory J C (Fev i) (colim (Fev i)))
            ( f)))

  module _
    (other : cocone-Precategory J Cᴵ F)
    (let otherv = vertex-cocone-Precategory J Cᴵ F other)
    where

    cocone-hom-colim-functor-Precategory : (i : obj-Precategory I) →
      cocone-Precategory J C (Fev i)
    pr1 (cocone-hom-colim-functor-Precategory i) =
      obj-functor-Precategory I C otherv i
    pr2 (cocone-hom-colim-functor-Precategory i) =
      left-whisker-natural-transformation-Precategory J Cᴵ C
        ( F)
        ( constant-functor-Precategory J Cᴵ otherv)
        ( ev-functor-Precategory I C i)
        ( natural-transformation-cocone-Precategory J Cᴵ F other)
    
    hom-colim-functor-Precategory :
      hom-Precategory Cᴵ vertex-colim-functor-Precategory otherv
    pr1 hom-colim-functor-Precategory i =
      hom-colim i (cocone-hom-colim-functor-Precategory i)
    pr2 hom-colim-functor-Precategory {i} {j} f =
      eq-htpy-hom-cocone-colimit-Precategory J C (Fev i) (colim (Fev i)) _ _
        ( λ c →
          ( associative-comp-hom-Precategory C
            ( hom-functor-Precategory I C otherv f)
            ( hom-colim i (cocone-hom-colim-functor-Precategory i))
            ( component-colim i c)) ∙
          ( ap
            ( comp-hom-Precategory C (hom-functor-Precategory I C otherv f))
            ( compute-colim i (cocone-hom-colim-functor-Precategory i) c)) ∙
          ( pr2 (component-cocone-Precategory J Cᴵ F other c) f) ∙
          ( inv
            ( ( associative-comp-hom-Precategory C
                ( hom-colim j (cocone-hom-colim-functor-Precategory j))
                ( hom-vertex-colim-functor-Precategory i j f)
                ( component-colim i c)) ∙
              ( ap
                ( comp-hom-Precategory C
                  ( hom-colim j (cocone-hom-colim-functor-Precategory j)))
                ( compute-hom-vertex-colim-functor-Precategory i j f c)) ∙
              ( inv
                ( associative-comp-hom-Precategory C
                  ( hom-colim j (cocone-hom-colim-functor-Precategory j))
                  ( component-colim j c)
                  ( hom-functor-Precategory I C (F₀ c) f))) ∙
              ( ap
                ( precomp-hom-Precategory C
                  ( hom-functor-Precategory I C (F₀ c) f) _)
                ( compute-colim j
                  ( cocone-hom-colim-functor-Precategory j)
                  ( c))))))

    compute-hom-colim-functor-Precategory : (c : obj-Precategory J) →
      comp-natural-transformation-Precategory I C
        ( F₀ c)
        ( vertex-colim-functor-Precategory)
        ( otherv)
        ( hom-colim-functor-Precategory)
        ( component-colim-functor-Precategory c) ＝
      component-cocone-Precategory J Cᴵ F other c
    compute-hom-colim-functor-Precategory c =
      eq-htpy-hom-family-natural-transformation-Precategory I C (F₀ c) otherv
        ( comp-natural-transformation-Precategory I C
          ( F₀ c)
          ( vertex-colim-functor-Precategory)
          ( otherv)
          ( hom-colim-functor-Precategory)
          ( component-colim-functor-Precategory c))
        ( component-cocone-Precategory J Cᴵ F other c)
        ( λ i → compute-colim i (cocone-hom-colim-functor-Precategory i) c)

    module _
      (othermor : hom-Precategory Cᴵ vertex-colim-functor-Precategory otherv)
      (othermor-comp : (c : obj-Precategory J) →
        comp-natural-transformation-Precategory I C
          ( F₀ c)
          ( vertex-colim-functor-Precategory)
          ( otherv)
          ( othermor)
          ( component-colim-functor-Precategory c) ＝
        component-cocone-Precategory J Cᴵ F other c)
      where

      abstract
        unique-hom-colim-functor-Precategory : 
          hom-colim-functor-Precategory ＝
          othermor
        unique-hom-colim-functor-Precategory =
          eq-htpy-hom-family-natural-transformation-Precategory I C
            ( vertex-colim-functor-Precategory)
            ( otherv)
            ( _)
            ( _)
            ( λ i →
              eq-htpy-hom-cocone-colimit-Precategory J C (Fev i) (colim (Fev i))
                (pr1 hom-colim-functor-Precategory i)
                (pr1 othermor i)
                ( λ c →
                  ( ap (λ x → pr1 x i)
                    ( ( compute-hom-colim-functor-Precategory c) ∙
                      ( inv ( othermor-comp c))))))

  module _
    (other : obj-Precategory Cᴵ)
    where

    cocone-map-colim-functor-Precategory : 
      hom-Precategory Cᴵ vertex-colim-functor-Precategory other →
      natural-transformation-Precategory J Cᴵ
        ( F)
        ( constant-functor-Precategory J Cᴵ other)
    cocone-map-colim-functor-Precategory = 
      cocone-map-Precategory J Cᴵ F cocone-colim-functor-Precategory other

    inv-cocone-map-colim-functor-Precategory :
      natural-transformation-Precategory J Cᴵ
        ( F)
        ( constant-functor-Precategory J Cᴵ other) →
      hom-Precategory Cᴵ vertex-colim-functor-Precategory other
    inv-cocone-map-colim-functor-Precategory othercocone =
      hom-colim-functor-Precategory (other , othercocone)

    is-retraction-cocone-map-colim-functor-Precategory :
      inv-cocone-map-colim-functor-Precategory ∘
      cocone-map-colim-functor-Precategory ~
      id
    is-retraction-cocone-map-colim-functor-Precategory x =
      unique-hom-colim-functor-Precategory
         ( other , (cocone-map-colim-functor-Precategory x))
         ( x)
         ( refl-htpy)

    is-section-cocone-map-colim-functor-Precategory :
      cocone-map-colim-functor-Precategory ∘
      inv-cocone-map-colim-functor-Precategory ~
      id
    is-section-cocone-map-colim-functor-Precategory x =
      eq-htpy-hom-family-natural-transformation-Precategory J Cᴵ
        ( F)
        ( constant-functor-Precategory J Cᴵ other)
        ( _)
        ( _)
        ( compute-hom-colim-functor-Precategory (other , x))

  is-colimit-colim-functor-Precategory :
    is-colimit-cocone-Precategory J Cᴵ F cocone-colim-functor-Precategory
  is-colimit-colim-functor-Precategory othervertex =
    is-equiv-is-invertible
      ( inv-cocone-map-colim-functor-Precategory othervertex)
      ( is-section-cocone-map-colim-functor-Precategory othervertex)
      ( is-retraction-cocone-map-colim-functor-Precategory othervertex)

  colim-functor-Precategory :
    colimit-Precategory J Cᴵ F
  pr1 colim-functor-Precategory = cocone-colim-functor-Precategory
  pr2 colim-functor-Precategory = is-colimit-colim-functor-Precategory
```

### The functor precategory has colimits of all shapes as the codomain

```agda
has-all-colimits-of-shape-functor-precategory-Precategory :
  {l1 l2 l3 l4 l5 l6 : Level}
  (I : Precategory l1 l2)
  (C : Precategory l3 l4)
  (J : Precategory l5 l6)
  (colim : has-all-colimits-of-shape-Precategory C J) →
  has-all-colimits-of-shape-Precategory (functor-precategory-Precategory I C) J
has-all-colimits-of-shape-functor-precategory-Precategory I C J colim F =
  colim-functor-Precategory I C J colim F
```

### The functor precategory is cocomplete if the codomain is

```agda
is-cocomplete-functor-precategory-Precategory :
  {l1 l2 l3 l4 : Level}
  (i j : Level)
  (I : Precategory l1 l2)
  (C : Precategory l3 l4) →
  is-cocomplete-Precategory i j C →
  is-cocomplete-Precategory i j (functor-precategory-Precategory I C)
is-cocomplete-functor-precategory-Precategory i j I C cc J =
  has-all-colimits-of-shape-functor-precategory-Precategory I C J (cc J)
```
