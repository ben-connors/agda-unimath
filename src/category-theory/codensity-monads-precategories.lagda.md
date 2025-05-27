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
    Rn = natural-transformation-right-kan-extension-Precategory C D D F F Rk
    cfp = comp-functor-Precategory
    chp = comp-hom-Precategory
    cnp = comp-natural-transformation-Precategory
    RR = cfp D D D R R
    RF = cfp C D D R F
    RRF = cfp C D D RR F
    RRR = cfp D D D R RR
    RRRF = cfp C D D RRR F

  id-right-extension-Precategory : right-extension-Precategory C D D F F
  pr1 id-right-extension-Precategory = id-functor-Precategory D
  pr2 id-right-extension-Precategory =
    id-natural-transformation-Precategory C D F

  double-right-extension-Precategory : right-extension-Precategory C D D F F
  pr1 double-right-extension-Precategory =
    ( comp-functor-Precategory D D D R R)
  pr2 double-right-extension-Precategory =
    cnp C D (cfp C D D RR F) (cfp C D D R F) F
      ( Rn)
      ( left-whisker-natural-transformation-Precategory C D D RF F R Rn)

  triple-right-extension-Precategory : right-extension-Precategory C D D F F
  pr1 triple-right-extension-Precategory = RRR
  pr2 triple-right-extension-Precategory =
    cnp C D (cfp C D D RRR F) (cfp C D D RR F) F
      ( pr2 double-right-extension-Precategory)
      ( left-whisker-natural-transformation-Precategory C D D
        ( cfp C D D R F)
        ( F)
        ( RR)
        ( Rn))

  unit-codensity-monad-Precategory :
    natural-transformation-Precategory D D (id-functor-Precategory D) R
  unit-codensity-monad-Precategory =
    map-inv-is-equiv
      (is-kan-R (id-functor-Precategory D))
      (pr2 id-right-extension-Precategory)

  abstract
    compute-unit-codensity-monad-Precategory :
      cnp C D F RF F
        ( Rn)
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
      ( pr2 double-right-extension-Precategory)

  abstract
    compute-mul-codensity-monad-Precategory :
      cnp C D RRF RF F
        ( Rn)
        ( right-whisker-natural-transformation-Precategory D D C
          ( RR)
          ( R)
          ( mul-codensity-monad-Precategory)
          ( F)) ＝
      cnp C D RRF RF F
        ( Rn)
        ( left-whisker-natural-transformation-Precategory C D D
          ( RF)
          ( F)
          ( R)
          ( Rn))
    compute-mul-codensity-monad-Precategory =
      is-section-map-inv-is-equiv (is-kan-R _) _
```

## Monad laws

Monad laws follow from the "uniqueness" part of the right Kan extension.

For the left unit law, if `ε : R∘F ⇒ F` is the right Kan extension natural
transformation, we show that the composite

```text
     (Rμ)F     μF     ε
  R∘F  ⇒  R²∘F ⇒  R∘F  ⇒  R
```

is equal to `ε`; by uniqueness, `μF ∘ RμF = id`.

```agda
  precomp-left-unit-law-mul-codensity-monad-Precategory :
    right-extension-map-Precategory C D D F F (R , Rn) R
      ( comp-natural-transformation-Precategory
        D D R RR R
        ( mul-codensity-monad-Precategory)
        ( left-whisker-natural-transformation-Precategory D D D
          ( id-functor-Precategory D)
          ( R)
          ( R)
          ( unit-codensity-monad-Precategory))) ＝
    Rn
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
          ( Rn)
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
          ( Rn)
          ( right-whisker-natural-transformation-Precategory D D C
            ( id-functor-Precategory D)
            ( R)
            ( unit-codensity-monad-Precategory)
            ( F))))) ∙
    ( ap
      ( λ x →
        ( comp-natural-transformation-Precategory C D RF RF F
          ( Rn)
          ( left-whisker-natural-transformation-Precategory C D D F F
            ( R)
            ( x))))
      ( compute-unit-codensity-monad-Precategory)) ∙
    ( ap
      ( λ x →
        ( comp-natural-transformation-Precategory C D RF RF F
          ( Rn)
          ( x)))
      ( preserves-id-left-whisker-natural-transformation-Precategory C D D
        ( F)
        ( R))) ∙
    ( right-unit-law-comp-natural-transformation-Precategory C D RF F Rn)

  left-unit-law-mul-codensity-monad-Precategory :
    comp-natural-transformation-Precategory
      D D R (cfp D D D R R) R
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
            ( Rn))))) ∙
    ( is-retraction-map-inv-is-equiv (is-kan-R R) _)
```

The right unit law is similar; we show that the composite is `ε` via:

```text
      ηRF     μF      ε
   RF  ⇒  R²F  ⇒  RF  ⇒  F
 ε ⇓   Rε ⇓              ∥
   F   ⇒  RF      ⇒      F
      ηF          ε
```

The right square (triangle) commutes by "uniqueness" of the right Kan UP; the
left square commutes by naturality of `η`. The bottom composite is then `id` by
the UP again.

```agda
  precomp-right-unit-law-mul-codensity-monad-Precategory :
    right-extension-map-Precategory C D D F F (R , Rn) R
      ( comp-natural-transformation-Precategory
        D D R RR R
        ( mul-codensity-monad-Precategory)
        ( right-whisker-natural-transformation-Precategory D D D
          ( id-functor-Precategory D)
          ( R)
          ( unit-codensity-monad-Precategory)
          ( R))) ＝
    Rn
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
      ( is-section-map-inv-is-equiv (is-kan-R (cfp D D D R R)) _)) ∙
    ( associative-comp-natural-transformation-Precategory C D RF RRF RF F
      ( _)
      ( _)
      ( _)) ∙
    ( ap
      ( λ x → cnp C D RF RF F Rn x)
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
        ( cnp C D RF F F x Rn))
      ( compute-unit-codensity-monad-Precategory)) ∙
    left-unit-law-comp-natural-transformation-Precategory C D RF F Rn

  right-unit-law-mul-codensity-monad-Precategory :
    comp-natural-transformation-Precategory
      D D R (cfp D D D R R) R
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
            ( Rn))))) ∙
    ( is-retraction-map-inv-is-equiv (is-kan-R R) _)
```

Showing that multiplication is associative is similar.

```agda
  left-precomp-associative-mul-codensity-monad-Precategory :
    cnp C D RRRF RF F
      ( Rn)
      ( right-whisker-natural-transformation-Precategory D D C
        ( RRR)
        ( R)
        ( cnp D D RRR RR R
          ( mul-codensity-monad-Precategory)
          ( left-whisker-natural-transformation-Precategory D D D RR R
            ( R)
            ( mul-codensity-monad-Precategory)))
        ( F)) ＝
    cnp C D RRRF RF F
      ( Rn)
      ( left-whisker-natural-transformation-Precategory C D D
        ( RRF)
        ( F)
        ( R)
        ( cnp C D RRF RF F
          ( Rn)
          ( left-whisker-natural-transformation-Precategory C D D
            ( RF)
            ( F)
            ( R)
            ( Rn))))
  left-precomp-associative-mul-codensity-monad-Precategory =
    first ∙
    second ∙
    third ∙
    fourth ∙
    fifth ∙
    sixth where

    a : natural-transformation-Precategory C D RRRF F
    a = cnp C D RRRF RF F
      ( Rn)
      ( right-whisker-natural-transformation-Precategory D D C
        ( RRR)
        ( R)
        ( cnp D D RRR RR R
          ( mul-codensity-monad-Precategory)
          ( left-whisker-natural-transformation-Precategory D D D RR R
            ( R)
            ( mul-codensity-monad-Precategory)))
        ( F))

    b : natural-transformation-Precategory C D RRRF F
    b = cnp C D RRRF RF F
      ( Rn)
      ( cnp C D RRRF RRF RF
        ( right-whisker-natural-transformation-Precategory D D C
          ( RR)
          ( R)
          ( mul-codensity-monad-Precategory)
          ( F))
        ( right-whisker-natural-transformation-Precategory D D C
          ( RRR)
          ( RR)
          ( left-whisker-natural-transformation-Precategory D D D RR R
            ( R)
            ( mul-codensity-monad-Precategory))
          ( F)))

    first : a ＝ b
    first = ap
      ( λ x → cnp C D RRRF RF F Rn x)
      ( preserves-comp-right-whisker-natural-transformation-Precategory D D C
        ( RRR)
        ( RR)
        ( R)
        ( mul-codensity-monad-Precategory)
        ( left-whisker-natural-transformation-Precategory D D D RR R
          ( R)
          ( mul-codensity-monad-Precategory))
        ( F))

    c : natural-transformation-Precategory C D RRRF F
    c = cnp C D RRRF RRF F
      ( cnp C D RRF RF F
        ( Rn)
        ( right-whisker-natural-transformation-Precategory D D C
          ( RR)
          ( R)
          ( mul-codensity-monad-Precategory)
          ( F)))
      ( right-whisker-natural-transformation-Precategory D D C
        ( RRR)
        ( RR)
        ( left-whisker-natural-transformation-Precategory D D D RR R
          ( R)
          ( mul-codensity-monad-Precategory))
        ( F))

    second : b ＝ c
    second = inv
      ( associative-comp-natural-transformation-Precategory C D RRRF RRF RF F
        ( _)
        ( _)
        ( _))

    d : natural-transformation-Precategory C D RRRF F
    d = cnp C D RRRF RRF F
      ( cnp C D RRF RF F
        ( Rn)
        ( left-whisker-natural-transformation-Precategory C D D
          ( RF)
          ( F)
          ( R)
          ( Rn)))
      ( right-whisker-natural-transformation-Precategory D D C
        ( RRR)
        ( RR)
        ( left-whisker-natural-transformation-Precategory D D D RR R
          ( R)
          ( mul-codensity-monad-Precategory))
        ( F))

    third : c ＝ d
    third = ap
      ( λ x →
        ( cnp C D RRRF RRF F
          ( x)
          ( right-whisker-natural-transformation-Precategory D D C
            ( RRR)
            ( RR)
            ( left-whisker-natural-transformation-Precategory D D D RR R
              ( R)
              ( mul-codensity-monad-Precategory))
            ( F))))
      ( compute-mul-codensity-monad-Precategory)

    e : natural-transformation-Precategory C D RRRF F
    e = cnp C D RRRF RF F
      ( Rn)
      ( cnp C D RRRF RRF RF
        ( left-whisker-natural-transformation-Precategory C D D
          ( RF)
          ( F)
          ( R)
          ( Rn))
        ( right-whisker-natural-transformation-Precategory D D C
          ( RRR)
          ( RR)
          ( left-whisker-natural-transformation-Precategory D D D RR R
            ( R)
            ( mul-codensity-monad-Precategory))
          ( F)))

    fourth : d ＝ e
    fourth = associative-comp-natural-transformation-Precategory C D
      ( RRRF)
      ( RRF)
      ( RF)
      ( F)
      ( _)
      ( _)
      ( _)

    f : natural-transformation-Precategory C D RRRF F
    f = cnp C D RRRF RF F
      ( Rn)
      ( left-whisker-natural-transformation-Precategory C D D
        ( RRF)
        ( F)
        ( R)
        ( cnp C D RRF RF F
          ( Rn)
          ( right-whisker-natural-transformation-Precategory D D C
            ( RR)
            ( R)
            ( mul-codensity-monad-Precategory)
            ( F))))

    fifth : e ＝ f
    fifth = ap
      ( λ x → cnp C D RRRF RF F Rn x)
      ( inv
        ( preserves-comp-left-whisker-natural-transformation-Precategory C D D
          ( RRF)
          ( RF)
          ( F)
          ( R)
          ( Rn)
          ( right-whisker-natural-transformation-Precategory D D C
            ( RR)
            ( R)
            ( mul-codensity-monad-Precategory)
            ( F))))

    g : natural-transformation-Precategory C D RRRF F
    g = cnp C D RRRF RF F
      ( Rn)
      ( left-whisker-natural-transformation-Precategory C D D
        ( RRF)
        ( F)
        ( R)
        ( cnp C D RRF RF F
          ( Rn)
          ( left-whisker-natural-transformation-Precategory C D D
            ( RF)
            ( F)
            ( R)
            ( Rn))))

    sixth : f ＝ g
    sixth = ap
      ( λ x → cnp C D RRRF RF F
        ( Rn)
        ( left-whisker-natural-transformation-Precategory C D D
          ( RRF)
          ( F)
          ( R)
          ( x)))
      ( compute-mul-codensity-monad-Precategory)

  right-precomp-associative-mul-codensity-monad-Precategory :
    cnp C D RRRF RF F
      ( Rn)
      ( right-whisker-natural-transformation-Precategory D D C
        ( RRR)
        ( R)
        ( cnp D D RRR RR R
          ( mul-codensity-monad-Precategory)
          ( right-whisker-natural-transformation-Precategory D D D RR R
            ( mul-codensity-monad-Precategory)
            ( R)))
        ( F)) ＝
    cnp C D RRRF RF F
      ( Rn)
      ( left-whisker-natural-transformation-Precategory C D D
        ( RRF)
        ( F)
        ( R)
        ( cnp C D RRF RF F
          ( Rn)
          ( left-whisker-natural-transformation-Precategory C D D
            ( RF)
            ( F)
            ( R)
            ( Rn))))
  right-precomp-associative-mul-codensity-monad-Precategory =
    first' ∙
    second' ∙
    third' ∙
    fourth' ∙
    fifth' ∙
    sixth' ∙
    seventh' ∙
    eighth' ∙
    ninth' where

    a' : natural-transformation-Precategory C D RRRF F
    a' = cnp C D RRRF RF F
      ( Rn)
      ( right-whisker-natural-transformation-Precategory D D C
        ( RRR)
        ( R)
        ( cnp D D RRR RR R
          ( mul-codensity-monad-Precategory)
          ( right-whisker-natural-transformation-Precategory D D D RR R
            ( mul-codensity-monad-Precategory)
            ( R)))
        ( F))

    b' : natural-transformation-Precategory C D RRRF F
    b' = cnp C D RRRF RF F
      ( Rn)
      ( cnp C D RRRF RRF RF
        ( right-whisker-natural-transformation-Precategory D D C
          ( RR)
          ( R)
          ( mul-codensity-monad-Precategory)
          ( F))
        ( right-whisker-natural-transformation-Precategory D D C
          ( RRR)
          ( RR)
          ( right-whisker-natural-transformation-Precategory D D D RR R
            ( mul-codensity-monad-Precategory)
            ( R))
          ( F)))

    first' : a' ＝ b'
    first' = ap
      ( λ x → cnp C D RRRF RF F Rn x)
      ( preserves-comp-right-whisker-natural-transformation-Precategory D D C
        ( RRR)
        ( RR)
        ( R)
        ( mul-codensity-monad-Precategory)
        ( right-whisker-natural-transformation-Precategory D D D RR R
          ( mul-codensity-monad-Precategory)
          ( R))
        ( F))

    c' : natural-transformation-Precategory C D RRRF F
    c' = cnp C D RRRF RRF F
      ( cnp C D RRF RF F
        ( Rn)
        ( right-whisker-natural-transformation-Precategory D D C
          ( RR)
          ( R)
          ( mul-codensity-monad-Precategory)
          ( F)))
      ( right-whisker-natural-transformation-Precategory D D C
        ( RRR)
        ( RR)
        ( right-whisker-natural-transformation-Precategory D D D RR R
          ( mul-codensity-monad-Precategory)
          ( R))
        ( F))

    second' : b' ＝ c'
    second' = inv
      ( associative-comp-natural-transformation-Precategory C D RRRF RRF RF F
        ( _)
        ( _)
        ( _))

    d' : natural-transformation-Precategory C D RRRF F
    d' = cnp C D RRRF RRF F
      ( cnp C D RRF RF F
        ( Rn)
        ( left-whisker-natural-transformation-Precategory C D D
          ( RF)
          ( F)
          ( R)
          ( Rn)))
      ( right-whisker-natural-transformation-Precategory D D C
        ( RRR)
        ( RR)
        ( right-whisker-natural-transformation-Precategory D D D RR R
          ( mul-codensity-monad-Precategory)
          ( R))
        ( F))

    third' : c' ＝ d'
    third' = ap
      ( λ x →
        ( cnp C D RRRF RRF F
          ( x)
          ( right-whisker-natural-transformation-Precategory D D C
            ( RRR)
            ( RR)
            ( right-whisker-natural-transformation-Precategory D D D RR R
              ( mul-codensity-monad-Precategory)
              ( R))
            ( F))))
      ( compute-mul-codensity-monad-Precategory)

    e' : natural-transformation-Precategory C D RRRF F
    e' = cnp C D RRRF RF F
      ( Rn)
      ( cnp C D RRRF RRF RF
        ( left-whisker-natural-transformation-Precategory C D D
          ( RF)
          ( F)
          ( R)
          ( Rn))
        ( right-whisker-natural-transformation-Precategory D D C
          ( RRR)
          ( RR)
          ( right-whisker-natural-transformation-Precategory D D D RR R
            ( mul-codensity-monad-Precategory)
            ( R))
          ( F)))

    fourth' : d' ＝ e'
    fourth' =
      associative-comp-natural-transformation-Precategory C D RRRF RRF RF F
        ( _)
        ( _)
        ( _)

    f' : natural-transformation-Precategory C D RRRF F
    f' = cnp C D RRRF RF F
      ( Rn)
      ( cnp C D RRRF RRF RF
        ( right-whisker-natural-transformation-Precategory D D C
          ( RR)
          ( R)
          ( mul-codensity-monad-Precategory)
          ( F))
        ( left-whisker-natural-transformation-Precategory C D D
          ( RRF)
          ( RF)
          ( R)
          ( left-whisker-natural-transformation-Precategory C D D
            ( RF)
            ( F)
            ( R)
            ( Rn))))

    fifth' : e' ＝ f'
    fifth' = ap
      ( λ x → cnp C D RRRF RF F Rn x)
      ( eq-htpy-hom-family-natural-transformation-Precategory C D RRRF RF
        ( _)
        ( _)
        ( λ x →
          naturality-natural-transformation-Precategory D D RR R
            ( mul-codensity-monad-Precategory)
            ( _)))

    g' : natural-transformation-Precategory C D RRRF F
    g' = cnp C D RRRF RRF F
      ( cnp C D RRF RF F
        ( Rn)
        ( right-whisker-natural-transformation-Precategory D D C
          ( RR)
          ( R)
          ( mul-codensity-monad-Precategory)
          ( F)))
      ( left-whisker-natural-transformation-Precategory C D D
        ( RRF)
        ( RF)
        ( R)
        ( left-whisker-natural-transformation-Precategory C D D
          ( RF)
          ( F)
          ( R)
          ( Rn)))

    sixth' : f' ＝ g'
    sixth' = inv
      ( associative-comp-natural-transformation-Precategory C D RRRF RRF RF F
        ( _)
        ( _)
        ( _))

    h' : natural-transformation-Precategory C D RRRF F
    h' = cnp C D RRRF RRF F
      ( cnp C D RRF RF F
        ( Rn)
        ( left-whisker-natural-transformation-Precategory C D D
          ( RF)
          ( F)
          ( R)
          ( Rn)))
      ( left-whisker-natural-transformation-Precategory C D D
        ( RRF)
        ( RF)
        ( R)
        ( left-whisker-natural-transformation-Precategory C D D
          ( RF)
          ( F)
          ( R)
          ( Rn)))

    seventh' : g' ＝ h'
    seventh' = ap
      ( λ x →
        ( cnp C D RRRF RRF F
          ( x)
          ( left-whisker-natural-transformation-Precategory C D D
            ( RRF)
            ( RF)
            ( R)
            ( left-whisker-natural-transformation-Precategory C D D
              ( RF)
              ( F)
              ( R)
              ( Rn)))))
      ( compute-mul-codensity-monad-Precategory)

    i' : natural-transformation-Precategory C D RRRF F
    i' = cnp C D RRRF RF F
      ( Rn)
      ( cnp C D RRRF RRF RF
        ( left-whisker-natural-transformation-Precategory C D D
          ( RF)
          ( F)
          ( R)
          ( Rn))
        ( left-whisker-natural-transformation-Precategory C D D
          ( RRF)
          ( RF)
          ( R)
          ( left-whisker-natural-transformation-Precategory C D D
            ( RF)
            ( F)
            ( R)
            ( Rn))))

    eighth' : h' ＝ i'
    eighth' = associative-comp-natural-transformation-Precategory C D
      ( RRRF)
      ( RRF)
      ( RF)
      ( F)
      ( _)
      ( _)
      ( _)

    j' : natural-transformation-Precategory C D RRRF F
    j' = cnp C D RRRF RF F
      ( Rn)
      ( left-whisker-natural-transformation-Precategory C D D
        ( RRF)
        ( F)
        ( R)
        ( cnp C D RRF RF F
          ( Rn)
          ( left-whisker-natural-transformation-Precategory C D D
            ( RF)
            ( F)
            ( R)
            ( Rn))))

    ninth' : i' ＝ j'
    ninth' = ap
      ( λ x → cnp C D RRRF RF F Rn x)
      ( inv
        ( preserves-comp-left-whisker-natural-transformation-Precategory C D D
          ( RRF)
          ( RF)
          ( F)
          ( R)
          ( Rn)
          ( left-whisker-natural-transformation-Precategory C D D
            ( RF)
            ( F)
            ( R)
            ( Rn))))

  associative-mul-codensity-monad-Precategory :
    cnp D D RRR RR R
      ( mul-codensity-monad-Precategory)
      ( left-whisker-natural-transformation-Precategory D D D RR R
        ( R)
        ( mul-codensity-monad-Precategory)) ＝
    cnp D D RRR RR R
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
