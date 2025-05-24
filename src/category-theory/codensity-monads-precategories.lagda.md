# Codensity monads in precategories

```agda
module category-theory.codensity-monads-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-precategories
open import category-theory.natural-transformations-functors-precategories
open import category-theory.precategories
open import category-theory.right-extensions-precategories
open import category-theory.right-kan-extensions-precategories

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.universe-levels
```

</details>

## Idea

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2) (D : Precategory l3 l4)
  (F : functor-Precategory C D)
  (R : right-kan-extension-Precategory C D D F F)
  where

  private
    Rf = extension-right-kan-extension-Precategory C D D F F R
    Rk = is-right-kan-extension-right-kan-extension-Precategory C D D F F R
    Rn = natural-transformation-right-kan-extension-Precategory C D D F F R
    Rn₀ = pr1 Rn
    cfp = comp-functor-Precategory
    chp = comp-hom-Precategory
    Rf₀ = obj-functor-Precategory D D Rf
    Rf₁ = hom-functor-Precategory D D Rf
    F₀ = obj-functor-Precategory C D F

  id-right-extension-Precategory : right-extension-Precategory C D D F F
  pr1 id-right-extension-Precategory = id-functor-Precategory D
  pr1 (pr2 id-right-extension-Precategory) x = id-hom-Precategory D
  pr2 (pr2 id-right-extension-Precategory) f =
    ( right-unit-law-comp-hom-Precategory D _) ∙
    ( inv (left-unit-law-comp-hom-Precategory D _))

  unit-codensity-monad-Precategory :
    natural-transformation-Precategory D D (id-functor-Precategory D) Rf
  unit-codensity-monad-Precategory =
    map-inv-is-equiv
      (Rk (id-functor-Precategory D))
      (pr2 id-right-extension-Precategory)

  hom-family-unit-codensity-monad-Precategory :
    (x : obj-Precategory D) → hom-Precategory D x (Rf₀ x)
  hom-family-unit-codensity-monad-Precategory =
    pr1 unit-codensity-monad-Precategory

  double-right-extension-Precategory : right-extension-Precategory C D D F F
  pr1 double-right-extension-Precategory =
    ( comp-functor-Precategory D D D Rf Rf)
  pr2 double-right-extension-Precategory =
    comp-natural-transformation-Precategory
      C D
      ( comp-functor-Precategory C D D (comp-functor-Precategory D D D Rf Rf) F)
      ( comp-functor-Precategory C D D Rf (comp-functor-Precategory C D D Rf F))
      ( F)
      ( comp-natural-transformation-Precategory C D
        ( comp-functor-Precategory C D D
          ( Rf)
          ( comp-functor-Precategory C D D Rf F))
        ( comp-functor-Precategory C D D Rf F)
        ( F)
        ( Rn)
        ( left-whisker-natural-transformation-Precategory C D D
          ( comp-functor-Precategory C D D Rf F)
          ( F)
          ( Rf)
          ( Rn)))
      ( associative-natural-transformation-comp-functor-Precategory C D D D
        ( F)
        ( Rf)
        ( Rf))

  mul-codensity-monad-Precategory :
    natural-transformation-Precategory D D
      ( comp-functor-Precategory D D D Rf Rf)
      ( Rf)
  mul-codensity-monad-Precategory =
    map-inv-is-equiv
      ( Rk (comp-functor-Precategory D D D Rf Rf))
      ( pr2 double-right-extension-Precategory)

  hom-family-mul-codensity-monad-Precategory :
    (x : obj-Precategory D) →
    hom-Precategory D (Rf₀ (Rf₀ x)) (Rf₀ x)
  hom-family-mul-codensity-monad-Precategory =
    pr1 mul-codensity-monad-Precategory

  private
    μ₀ = hom-family-mul-codensity-monad-Precategory
    η₀ = hom-family-unit-codensity-monad-Precategory
    RR = cfp D D D Rf Rf
    RF = cfp C D D Rf F
    RR-F = cfp C D D RR F
    R-RF = cfp C D D Rf RF

  -- What we need to be equal to the identity natural transformation on Rf
  first-right-unit-law-codensity-monad-Precategory :
    natural-transformation-Precategory D D Rf Rf
  first-right-unit-law-codensity-monad-Precategory =
    comp-natural-transformation-Precategory
      D D Rf (cfp D D D Rf Rf) Rf
      ( mul-codensity-monad-Precategory)
      ( left-whisker-natural-transformation-Precategory D D D
        ( id-functor-Precategory D)
        ( Rf)
        ( Rf)
        ( unit-codensity-monad-Precategory))

  second-right-unit-law-codensity-monad-Precategory :
    right-extension-map-Precategory C D D F F (Rf , Rn) Rf
      ( first-right-unit-law-codensity-monad-Precategory) ＝
    Rn
  second-right-unit-law-codensity-monad-Precategory =
    first ∙
    second ∙
    third ∙
    fourth ∙
    fifth ∙
    sixth ∙
    seventh ∙
    eighth ∙
    ninth ∙
    tenth where

    G = is-section-map-inv-is-equiv (Rk (cfp D D D Rf Rf))
    G' = is-section-map-inv-is-equiv (Rk (id-functor-Precategory D))

    a = right-extension-map-Precategory C D D F F (Rf , Rn) Rf
      ( first-right-unit-law-codensity-monad-Precategory)

    b : natural-transformation-Precategory C D RF F
    b = comp-natural-transformation-Precategory C D RF RF F
      Rn
      (comp-natural-transformation-Precategory C D RF RR-F RF
        ( right-whisker-natural-transformation-Precategory D D C RR Rf
          ( mul-codensity-monad-Precategory)
          ( F))
        ( right-whisker-natural-transformation-Precategory D D C Rf RR
          ( left-whisker-natural-transformation-Precategory D D D
            ( id-functor-Precategory D)
            ( Rf)
            ( Rf)
            ( unit-codensity-monad-Precategory))
          ( F)))

    first : a ＝ b
    first = refl

    c : natural-transformation-Precategory C D RF F
    c = comp-natural-transformation-Precategory C D RF RR-F F
      (comp-natural-transformation-Precategory C D RR-F RF F
        ( Rn)
        ( right-whisker-natural-transformation-Precategory D D C RR Rf
          ( mul-codensity-monad-Precategory)
          ( F)))
      ( right-whisker-natural-transformation-Precategory D D C Rf RR
        ( left-whisker-natural-transformation-Precategory D D D
          ( id-functor-Precategory D)
          ( Rf)
          ( Rf)
          ( unit-codensity-monad-Precategory))
        ( F))

    second : b ＝ c
    second = inv
      ( associative-comp-natural-transformation-Precategory C D RF RR-F RF F
        ( _)
        ( _)
        ( _))

    d : natural-transformation-Precategory C D RF F
    d = comp-natural-transformation-Precategory C D RF RR-F F
      ( pr2 double-right-extension-Precategory)
      ( right-whisker-natural-transformation-Precategory D D C Rf RR
        ( left-whisker-natural-transformation-Precategory D D D
        ( id-functor-Precategory D) Rf Rf unit-codensity-monad-Precategory)
        ( F))

    third : c ＝ d
    third = ap
      ( λ x →
        comp-natural-transformation-Precategory C D RF RR-F F
          ( x)
          ( right-whisker-natural-transformation-Precategory D D C Rf RR
            ( left-whisker-natural-transformation-Precategory D D D
            ( id-functor-Precategory D) Rf Rf unit-codensity-monad-Precategory)
            ( F)))
      (G _)

    e : natural-transformation-Precategory C D RF F
    e = comp-natural-transformation-Precategory C D RF R-RF F
      ( comp-natural-transformation-Precategory C D R-RF RF F
          ( Rn)
          ( left-whisker-natural-transformation-Precategory C D D RF F
            ( Rf)
            ( Rn)))
      (comp-natural-transformation-Precategory C D RF RR-F R-RF
        ( associative-natural-transformation-comp-functor-Precategory C D D D
          ( F)
          ( Rf)
          ( Rf))
        ( right-whisker-natural-transformation-Precategory D D C Rf RR
          ( left-whisker-natural-transformation-Precategory D D D
            ( id-functor-Precategory D)
            ( Rf)
            ( Rf)
            ( unit-codensity-monad-Precategory))
          ( F)))

    fourth : d ＝ e
    fourth =
      associative-comp-natural-transformation-Precategory C D RF RR-F R-RF F
      ( _)
      ( _)
      ( _)

    f : natural-transformation-Precategory C D RF F
    f = comp-natural-transformation-Precategory C D RF R-RF F
      ( comp-natural-transformation-Precategory C D R-RF RF F
          ( Rn)
          ( left-whisker-natural-transformation-Precategory C D D RF F
            ( Rf)
            ( Rn)))
      (comp-natural-transformation-Precategory C D RF RF R-RF
        (left-whisker-natural-transformation-Precategory C D D F RF Rf
          ( right-whisker-natural-transformation-Precategory D D C
            ( id-functor-Precategory D)
            ( Rf)
            ( unit-codensity-monad-Precategory)
            ( F)))
        ( (associative-natural-transformation-comp-functor-Precategory' C D D
            D F (id-functor-Precategory D) Rf)))

    fifth : e ＝ f
    fifth = ap
      ( λ x →
        comp-natural-transformation-Precategory C D RF R-RF F
          ( comp-natural-transformation-Precategory C D R-RF RF F
              ( Rn)
              ( left-whisker-natural-transformation-Precategory C D D RF F
                ( Rf)
                ( Rn)))
          ( x))
      ( interchange-right-left-whisker-natural-transformation-Precategory
        ( C)
        ( D)
        ( D)
        ( D)
        ( id-functor-Precategory D)
        ( Rf)
        ( Rf)
        ( unit-codensity-monad-Precategory)
        ( F))

    g : natural-transformation-Precategory C D RF F
    g = comp-natural-transformation-Precategory C D RF RF F
      ( comp-natural-transformation-Precategory C D RF R-RF F
        ( comp-natural-transformation-Precategory C D R-RF RF F
            ( Rn)
            ( left-whisker-natural-transformation-Precategory C D D RF F
              ( Rf)
              ( Rn)))
        (left-whisker-natural-transformation-Precategory C D D F RF Rf
          ( right-whisker-natural-transformation-Precategory D D C
            ( id-functor-Precategory D)
            ( Rf)
            ( unit-codensity-monad-Precategory)
            ( F))))
      ( (associative-natural-transformation-comp-functor-Precategory' C D D
          D F (id-functor-Precategory D) Rf))

    sixth : f ＝ g
    sixth =
      inv
        ( associative-comp-natural-transformation-Precategory C D RF RF R-RF F
          ( _)
          ( _)
          ( _))

    h : natural-transformation-Precategory C D RF F
    h = comp-natural-transformation-Precategory C D RF RF F
      ( comp-natural-transformation-Precategory C D RF RF F
        ( Rn)
        ( comp-natural-transformation-Precategory C D RF R-RF RF
          ( left-whisker-natural-transformation-Precategory C D D RF F
            ( Rf)
            ( Rn))
          ( left-whisker-natural-transformation-Precategory C D D F RF Rf
            ( right-whisker-natural-transformation-Precategory D D C
              ( id-functor-Precategory D)
              ( Rf)
              ( unit-codensity-monad-Precategory)
              ( F)))))
      ( (associative-natural-transformation-comp-functor-Precategory' C D D
          D F (id-functor-Precategory D) Rf))

    seventh : g ＝ h
    seventh = ap
      ( λ x →
        comp-natural-transformation-Precategory C D RF RF F
          ( x)
          ( (associative-natural-transformation-comp-functor-Precategory' C D D
              D F (id-functor-Precategory D) Rf)))
      ( associative-comp-natural-transformation-Precategory C D RF R-RF RF F
        ( _)
        ( _)
        ( _))

    i : natural-transformation-Precategory C D RF F
    i = comp-natural-transformation-Precategory C D RF RF F
      ( comp-natural-transformation-Precategory C D RF RF F
        ( Rn)
        ( left-whisker-natural-transformation-Precategory C D D F F
          ( Rf)
          ( comp-natural-transformation-Precategory C D F RF F
            ( Rn)
            ( right-whisker-natural-transformation-Precategory D D C
              ( id-functor-Precategory D)
              ( Rf)
              ( unit-codensity-monad-Precategory)
              ( F)))))
      ( (associative-natural-transformation-comp-functor-Precategory' C D D
          D F (id-functor-Precategory D) Rf))

    eighth : h ＝ i
    eighth = ap
      ( λ x →
        comp-natural-transformation-Precategory C D RF RF F
          ( comp-natural-transformation-Precategory C D RF RF F
            ( Rn)
            x)
          ( (associative-natural-transformation-comp-functor-Precategory' C D D
              D F (id-functor-Precategory D) Rf)))
      ( inv
        ( preserves-comp-left-whisker-natural-transformation-Precategory
          ( C)
          ( D)
          ( D)
          ( F)
          ( RF)
          ( F)
          ( Rf)
          ( Rn)
          ( right-whisker-natural-transformation-Precategory D D C
            ( id-functor-Precategory D)
            ( Rf)
            ( unit-codensity-monad-Precategory)
            ( F))))

    j : natural-transformation-Precategory C D RF F
    j = comp-natural-transformation-Precategory C D RF RF F
      ( comp-natural-transformation-Precategory C D RF RF F
        ( Rn)
        ( left-whisker-natural-transformation-Precategory C D D F F
          ( Rf)
          ( pr2 id-right-extension-Precategory)))
      ( (associative-natural-transformation-comp-functor-Precategory' C D D
          D F (id-functor-Precategory D) Rf))

    ninth : i ＝ j
    ninth = ap
      ( λ x →
        comp-natural-transformation-Precategory C D RF RF F
          ( comp-natural-transformation-Precategory C D RF RF F
            ( Rn)
            ( left-whisker-natural-transformation-Precategory C D D F F
              ( Rf)
              x))
          ( (associative-natural-transformation-comp-functor-Precategory' C D D
              D F (id-functor-Precategory D) Rf)))
      ( G' _)

    k : natural-transformation-Precategory C D RF F
    k = comp-natural-transformation-Precategory C D RF RF F
      ( comp-natural-transformation-Precategory C D RF RF F
        ( Rn)
        ( left-whisker-natural-transformation-Precategory C D D F F
          ( Rf)
          ( pr2 id-right-extension-Precategory)))
      ( (associative-natural-transformation-comp-functor-Precategory' C D D
          D F (id-functor-Precategory D) Rf))

    tenth : j ＝ Rn
    tenth = eq-htpy-hom-family-natural-transformation-Precategory
      ( C)
      ( D)
      ( RF)
      ( F)
      ( _)
      ( _)
      ( λ x →
        ( right-unit-law-comp-hom-Precategory D _) ∙
        ( ap
          ( λ y → comp-hom-Precategory D _ y)
          ( preserves-id-functor-Precategory D D Rf _)) ∙
        ( right-unit-law-comp-hom-Precategory D _))

  third-right-unit-law-codensity-monad-Precategory :
    right-extension-map-Precategory C D D F F (Rf , Rn) Rf
      (id-natural-transformation-Precategory D D Rf) ＝
    Rn
  third-right-unit-law-codensity-monad-Precategory =
    ( right-unit-law-comp-natural-transformation-Precategory C D
      ( RF)
      ( F)
      ( Rn))

  right-unit-law-codensity-monad-Precategory :
    comp-natural-transformation-Precategory
      D D Rf (cfp D D D Rf Rf) Rf
      ( mul-codensity-monad-Precategory)
      ( left-whisker-natural-transformation-Precategory D D D
        ( id-functor-Precategory D)
        ( Rf)
        ( Rf)
        ( unit-codensity-monad-Precategory)) ＝
    id-natural-transformation-Precategory D D Rf
  right-unit-law-codensity-monad-Precategory =
    ( inv (is-retraction-map-inv-is-equiv (Rk Rf) _)) ∙
    ( ap
      ( map-inv-is-equiv (Rk Rf))
      ( ( second-right-unit-law-codensity-monad-Precategory) ∙
        ( inv (third-right-unit-law-codensity-monad-Precategory)))) ∙
    ( is-retraction-map-inv-is-equiv (Rk Rf) _)
```
