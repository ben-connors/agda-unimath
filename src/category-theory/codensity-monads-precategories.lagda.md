# Codensity monads in precategories

```agda
module category-theory.codensity-monads-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.functors-precategories
open import category-theory.monads-on-precategories
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

Given an arbitrary functor `F : C → D`, any [right Kan
extension](category-theory.right-kan-extensions-precategories.md] `R` of `F`
along itself `F` has a canonical
[monad](category-theory.monads-on-precategories.md] structure, called the
{{#concept "codensity monad" Agda=codensity-monad-Precategory}} of `R`.

## Unit and multiplication

The unit and multiplication of the codensity monads follow from the "existence"
part of the universal property of the right Kan extension. We use two right
extensions: the identity map on `D` trivially gives a right extension of `D`
along itself, and `R²` gives an extension by whiskering and composing the
natural transformation. By the universal property of `R`, these give natural
transformations `η : id ⇒ R` and `μ : R² ⇒ R`, respectively.

```agda
module _
  {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2) (D : Precategory l3 l4)
  (F : functor-Precategory C D)
  (Rk : right-kan-extension-Precategory C D D F F)
  where

  private
    R = extension-right-kan-extension-Precategory C D D F F Rk
    is-kan-R =
      is-right-kan-extension-right-kan-extension-Precategory C D D F F Rk
    α = natural-transformation-right-kan-extension-Precategory C D D F F Rk
    RR = comp-functor-Precategory D D D R R
    RF = comp-functor-Precategory C D D R F
    RRF = comp-functor-Precategory C D D RR F
    RRR = comp-functor-Precategory D D D R RR
    RRRF = comp-functor-Precategory C D D RRR F

  unit-codensity-monad-Precategory :
    natural-transformation-Precategory D D (id-functor-Precategory D) R
  unit-codensity-monad-Precategory =
    map-inv-is-equiv
      ( is-kan-R (id-functor-Precategory D))
      ( pr2 (id-right-extension-Precategory C D F))

  abstract
    compute-unit-codensity-monad-Precategory :
      comp-natural-transformation-Precategory C D F RF F
        ( α)
        ( right-whisker-natural-transformation-Precategory D D C
          ( id-functor-Precategory D)
          ( R)
          ( unit-codensity-monad-Precategory)
          ( F)) ＝
      id-natural-transformation-Precategory C D F
    compute-unit-codensity-monad-Precategory =
      is-section-map-inv-is-equiv (is-kan-R _) _

  mul-codensity-monad-Precategory :
    natural-transformation-Precategory D D
      ( comp-functor-Precategory D D D R R)
      ( R)
  mul-codensity-monad-Precategory =
    map-inv-is-equiv
      ( is-kan-R (comp-functor-Precategory D D D R R))
      ( pr2
        ( double-right-extension-Precategory C D F
          ( right-extension-right-kan-extension-Precategory C D D F F Rk)))

  abstract
    compute-mul-codensity-monad-Precategory :
      comp-natural-transformation-Precategory C D RRF RF F
        ( α)
        ( right-whisker-natural-transformation-Precategory D D C
          ( RR)
          ( R)
          ( mul-codensity-monad-Precategory)
          ( F)) ＝
      comp-natural-transformation-Precategory C D RRF RF F
        ( α)
        ( left-whisker-natural-transformation-Precategory C D D
          ( RF)
          ( F)
          ( R)
          ( α))
    compute-mul-codensity-monad-Precategory =
      is-section-map-inv-is-equiv (is-kan-R _) _
```

## Monad laws

Monad laws follow from the "uniqueness" part of the right Kan extension.

For the left unit law, if `α : R∘F ⇒ F` is the right Kan extension natural
transformation, we show that the composite

```text
     (Rμ)F     μF     α
  R∘F  ⇒  R²∘F ⇒  R∘F  ⇒  R
```

is equal to `α`; by uniqueness, `μF ∘ RμF = id`.

```agda
  precomp-left-unit-law-mul-codensity-monad-Precategory :
    right-extension-map-Precategory C D D F F (R , α) R
      ( comp-natural-transformation-Precategory
        D D R RR R
        ( mul-codensity-monad-Precategory)
        ( left-whisker-natural-transformation-Precategory D D D
          ( id-functor-Precategory D)
          ( R)
          ( R)
          ( unit-codensity-monad-Precategory))) ＝
    α
  precomp-left-unit-law-mul-codensity-monad-Precategory =
    ( inv
      ( associative-comp-natural-transformation-Precategory C D RF RRF RF F
        ( _)
        ( _)
        ( _))) ∙
    ( ap
      ( λ x →
        comp-natural-transformation-Precategory C D RF RRF F
          ( x)
          ( right-whisker-natural-transformation-Precategory D D C R RR
            ( left-whisker-natural-transformation-Precategory D D D
            ( id-functor-Precategory D) R R unit-codensity-monad-Precategory)
            ( F)))
      ( compute-mul-codensity-monad-Precategory)) ∙
    ( associative-comp-natural-transformation-Precategory C D RF RRF RF F
      ( _)
      ( _)
      ( _)) ∙
    ( ap
      ( λ x →
        ( comp-natural-transformation-Precategory C D RF RF F
          ( α)
          ( x)))
      ( inv
        ( preserves-comp-left-whisker-natural-transformation-Precategory
          ( C)
          ( D)
          ( D)
          ( F)
          ( RF)
          ( F)
          ( R)
          ( α)
          ( right-whisker-natural-transformation-Precategory D D C
            ( id-functor-Precategory D)
            ( R)
            ( unit-codensity-monad-Precategory)
            ( F))))) ∙
    ( ap
      ( λ x →
        ( comp-natural-transformation-Precategory C D RF RF F
          ( α)
          ( left-whisker-natural-transformation-Precategory C D D F F
            ( R)
            ( x))))
      ( compute-unit-codensity-monad-Precategory)) ∙
    ( ap
      ( λ x →
        ( comp-natural-transformation-Precategory C D RF RF F
          ( α)
          ( x)))
      ( preserves-id-left-whisker-natural-transformation-Precategory C D D
        ( F)
        ( R))) ∙
    ( right-unit-law-comp-natural-transformation-Precategory C D RF F α)

  abstract
    left-unit-law-mul-codensity-monad-Precategory :
      comp-natural-transformation-Precategory
        D D R (comp-functor-Precategory D D D R R) R
        ( mul-codensity-monad-Precategory)
        ( left-whisker-natural-transformation-Precategory D D D
          ( id-functor-Precategory D)
          ( R)
          ( R)
          ( unit-codensity-monad-Precategory)) ＝
      id-natural-transformation-Precategory D D R
    left-unit-law-mul-codensity-monad-Precategory =
      ( inv (is-retraction-map-inv-is-equiv (is-kan-R R) _)) ∙
      ( ap
        ( map-inv-is-equiv (is-kan-R R))
        ( ( precomp-left-unit-law-mul-codensity-monad-Precategory) ∙
          ( inv
            ( right-unit-law-comp-natural-transformation-Precategory C D
              ( RF)
              ( F)
              ( α))))) ∙
      ( is-retraction-map-inv-is-equiv (is-kan-R R) _)
```

The right unit law is similar; we show that the composite is `α` via:

```text
      ηRF     μF      α
   RF  ⇒  R²F  ⇒  RF  ⇒  F
 α ⇓   Rα ⇓              ∥
   F   ⇒  RF      ⇒      F
      ηF          α
```

The right square (triangle) commutes by "uniqueness" of the right Kan UP; the
left square commutes by naturality of `η`. The bottom composite is then `id` by
the UP again.

```agda
  precomp-right-unit-law-mul-codensity-monad-Precategory :
    right-extension-map-Precategory C D D F F (R , α) R
      ( comp-natural-transformation-Precategory
        D D R RR R
        ( mul-codensity-monad-Precategory)
        ( right-whisker-natural-transformation-Precategory D D D
          ( id-functor-Precategory D)
          ( R)
          ( unit-codensity-monad-Precategory)
          ( R))) ＝
    α
  precomp-right-unit-law-mul-codensity-monad-Precategory =
    ( inv
      ( associative-comp-natural-transformation-Precategory C D RF RRF RF F
        ( _)
        ( _)
        ( _))) ∙
    ( ap
      ( λ x →
        ( comp-natural-transformation-Precategory C D RF RRF F
          ( x)
          ( right-whisker-natural-transformation-Precategory D D C R RR
            ( right-whisker-natural-transformation-Precategory D D D
              ( id-functor-Precategory D)
              ( R)
              ( unit-codensity-monad-Precategory)
              ( R))
            ( F))))
      ( is-section-map-inv-is-equiv
        ( is-kan-R (comp-functor-Precategory D D D R R)) _)) ∙
    ( associative-comp-natural-transformation-Precategory C D RF RRF RF F
      ( _)
      ( _)
      ( _)) ∙
    ( ap
      ( λ x → comp-natural-transformation-Precategory C D RF RF F α x)
      ( eq-htpy-hom-family-natural-transformation-Precategory C D RF RF _ _
        ( λ x →
          ( naturality-natural-transformation-Precategory D D
            (id-functor-Precategory D)
            ( R)
            ( unit-codensity-monad-Precategory)
            ( _))))) ∙
    ( inv
      ( associative-comp-natural-transformation-Precategory C D RF F RF F
        ( _)
        ( _)
        ( _))) ∙
    ( ap
      ( λ x →
        ( comp-natural-transformation-Precategory C D RF F F x α))
      ( compute-unit-codensity-monad-Precategory)) ∙
    left-unit-law-comp-natural-transformation-Precategory C D RF F α

  abstract
    right-unit-law-mul-codensity-monad-Precategory :
      comp-natural-transformation-Precategory
        D D R (comp-functor-Precategory D D D R R) R
        ( mul-codensity-monad-Precategory)
        ( right-whisker-natural-transformation-Precategory D D D
          ( id-functor-Precategory D)
          ( R)
          ( unit-codensity-monad-Precategory)
          ( R)) ＝
      id-natural-transformation-Precategory D D R
    right-unit-law-mul-codensity-monad-Precategory =
      ( inv (is-retraction-map-inv-is-equiv (is-kan-R R) _)) ∙
      ( ap
        ( map-inv-is-equiv (is-kan-R R))
        ( ( precomp-right-unit-law-mul-codensity-monad-Precategory) ∙
          ( inv
            ( right-unit-law-comp-natural-transformation-Precategory C D
              ( RF)
              ( F)
              ( α))))) ∙
      ( is-retraction-map-inv-is-equiv (is-kan-R R) _)
```

Showing that multiplication is associative is similar but longer.

```agda
  left-precomp-associative-mul-codensity-monad-Precategory :
    comp-natural-transformation-Precategory C D RRRF RF F
      ( α)
      ( right-whisker-natural-transformation-Precategory D D C
        ( RRR)
        ( R)
        ( comp-natural-transformation-Precategory D D RRR RR R
          ( mul-codensity-monad-Precategory)
          ( left-whisker-natural-transformation-Precategory D D D RR R
            ( R)
            ( mul-codensity-monad-Precategory)))
        ( F)) ＝
    comp-natural-transformation-Precategory C D RRRF RF F
      ( α)
      ( left-whisker-natural-transformation-Precategory C D D
        ( RRF)
        ( F)
        ( R)
        ( comp-natural-transformation-Precategory C D RRF RF F
          ( α)
          ( left-whisker-natural-transformation-Precategory C D D
            ( RF)
            ( F)
            ( R)
            ( α))))
  left-precomp-associative-mul-codensity-monad-Precategory =
    ( ap
      ( λ x → comp-natural-transformation-Precategory C D RRRF RF F α x)
      ( preserves-comp-right-whisker-natural-transformation-Precategory D D C
        ( RRR)
        ( RR)
        ( R)
        ( mul-codensity-monad-Precategory)
        ( left-whisker-natural-transformation-Precategory D D D RR R
          ( R)
          ( mul-codensity-monad-Precategory))
        ( F))) ∙
    ( inv
      ( associative-comp-natural-transformation-Precategory C D RRRF RRF RF F
        ( _)
        ( _)
        ( _))) ∙
    ( ap
      ( λ x →
        ( comp-natural-transformation-Precategory C D RRRF RRF F
          ( x)
          ( right-whisker-natural-transformation-Precategory D D C
            ( RRR)
            ( RR)
            ( left-whisker-natural-transformation-Precategory D D D RR R
              ( R)
              ( mul-codensity-monad-Precategory))
            ( F))))
      ( compute-mul-codensity-monad-Precategory)) ∙
    ( associative-comp-natural-transformation-Precategory C D
      ( RRRF)
      ( RRF)
      ( RF)
      ( F)
      ( _)
      ( _)
      ( _)) ∙
    ( ap
      ( λ x → comp-natural-transformation-Precategory C D RRRF RF F α x)
      ( inv
        ( preserves-comp-left-whisker-natural-transformation-Precategory C D D
          ( RRF)
          ( RF)
          ( F)
          ( R)
          ( α)
          ( right-whisker-natural-transformation-Precategory D D C
            ( RR)
            ( R)
            ( mul-codensity-monad-Precategory)
            ( F))))) ∙
    ( ap
      ( λ x → comp-natural-transformation-Precategory C D RRRF RF F
        ( α)
        ( left-whisker-natural-transformation-Precategory C D D
          ( RRF)
          ( F)
          ( R)
          ( x)))
      ( compute-mul-codensity-monad-Precategory))

  right-precomp-associative-mul-codensity-monad-Precategory :
    comp-natural-transformation-Precategory C D RRRF RF F
      ( α)
      ( right-whisker-natural-transformation-Precategory D D C
        ( RRR)
        ( R)
        ( comp-natural-transformation-Precategory D D RRR RR R
          ( mul-codensity-monad-Precategory)
          ( right-whisker-natural-transformation-Precategory D D D RR R
            ( mul-codensity-monad-Precategory)
            ( R)))
        ( F)) ＝
    comp-natural-transformation-Precategory C D RRRF RF F
      ( α)
      ( left-whisker-natural-transformation-Precategory C D D
        ( RRF)
        ( F)
        ( R)
        ( comp-natural-transformation-Precategory C D RRF RF F
          ( α)
          ( left-whisker-natural-transformation-Precategory C D D
            ( RF)
            ( F)
            ( R)
            ( α))))
  right-precomp-associative-mul-codensity-monad-Precategory =
    ( ap
      ( λ x → comp-natural-transformation-Precategory C D RRRF RF F α x)
      ( preserves-comp-right-whisker-natural-transformation-Precategory D D C
        ( RRR)
        ( RR)
        ( R)
        ( mul-codensity-monad-Precategory)
        ( right-whisker-natural-transformation-Precategory D D D RR R
          ( mul-codensity-monad-Precategory)
          ( R))
        ( F))) ∙
    ( inv
      ( associative-comp-natural-transformation-Precategory C D RRRF RRF RF F
        ( _)
        ( _)
        ( _))) ∙
    ( ap
      ( λ x →
        ( comp-natural-transformation-Precategory C D RRRF RRF F
          ( x)
          ( right-whisker-natural-transformation-Precategory D D C
            ( RRR)
            ( RR)
            ( right-whisker-natural-transformation-Precategory D D D RR R
              ( mul-codensity-monad-Precategory)
              ( R))
            ( F))))
      ( compute-mul-codensity-monad-Precategory)) ∙
    ( associative-comp-natural-transformation-Precategory C D RRRF RRF RF F
        ( _)
        ( _)
        ( _)) ∙
    ( ap
      ( λ x → comp-natural-transformation-Precategory C D RRRF RF F α x)
      ( eq-htpy-hom-family-natural-transformation-Precategory C D RRRF RF
        ( _)
        ( _)
        ( λ x →
          naturality-natural-transformation-Precategory D D RR R
            ( mul-codensity-monad-Precategory)
            ( _)))) ∙
    ( inv
      ( associative-comp-natural-transformation-Precategory C D RRRF RRF RF F
        ( _)
        ( _)
        ( _))) ∙
    ( ap
      ( λ x →
        ( comp-natural-transformation-Precategory C D RRRF RRF F
          ( x)
          ( left-whisker-natural-transformation-Precategory C D D
            ( RRF)
            ( RF)
            ( R)
            ( left-whisker-natural-transformation-Precategory C D D
              ( RF)
              ( F)
              ( R)
              ( α)))))
      ( compute-mul-codensity-monad-Precategory)) ∙
    ( associative-comp-natural-transformation-Precategory C D
      ( RRRF)
      ( RRF)
      ( RF)
      ( F)
      ( _)
      ( _)
      ( _)) ∙
    ( ap
      ( λ x → comp-natural-transformation-Precategory C D RRRF RF F α x)
      ( inv
        ( preserves-comp-left-whisker-natural-transformation-Precategory C D D
          ( RRF)
          ( RF)
          ( F)
          ( R)
          ( α)
          ( left-whisker-natural-transformation-Precategory C D D
            ( RF)
            ( F)
            ( R)
            ( α)))))

  abstract
    associative-mul-codensity-monad-Precategory :
      comp-natural-transformation-Precategory D D RRR RR R
        ( mul-codensity-monad-Precategory)
        ( left-whisker-natural-transformation-Precategory D D D RR R
          ( R)
          ( mul-codensity-monad-Precategory)) ＝
      comp-natural-transformation-Precategory D D RRR RR R
        ( mul-codensity-monad-Precategory)
        ( right-whisker-natural-transformation-Precategory D D D RR R
          ( mul-codensity-monad-Precategory)
          ( R))
    associative-mul-codensity-monad-Precategory =
      ( inv (is-retraction-map-inv-is-equiv (is-kan-R RRR) _)) ∙
      ( ap
        ( map-inv-is-equiv (is-kan-R RRR))
        ( ( left-precomp-associative-mul-codensity-monad-Precategory) ∙
          ( inv right-precomp-associative-mul-codensity-monad-Precategory))) ∙
      ( is-retraction-map-inv-is-equiv (is-kan-R RRR) _)
```

## The codensity monad

```agda
  codensity-monad-Precategory : monad-Precategory D
  codensity-monad-Precategory =
    ( R , unit-codensity-monad-Precategory) ,
    ( mul-codensity-monad-Precategory) ,
    ( ( associative-mul-codensity-monad-Precategory) ,
      ( ( left-unit-law-mul-codensity-monad-Precategory) ,
        ( right-unit-law-mul-codensity-monad-Precategory)))
```
