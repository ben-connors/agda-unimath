# Comonads on precategories

```agda
module category-theory.comonads-on-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.adjunctions-precategories
open import category-theory.commuting-squares-of-morphisms-in-precategories
open import category-theory.copointed-endofunctors-precategories
open import category-theory.functors-precategories
open import category-theory.natural-transformations-functors-precategories
open import category-theory.natural-transformations-maps-precategories
open import category-theory.precategories

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

A
{{#concept "comonad" Disambiguation="on a precategory" Agda=comonad-Precategory}}
is the dual concept to a
{{#concept "monad" Disambiguation="on a precategory" Agda=monad=Precategory}};
see there for details.

## Definitions

### Multiplication structure on a copointed endofunctor on a precategory

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  (T : copointed-endofunctor-Precategory C)
  where

  structure-comultiplication-copointed-endofunctor-Precategory : UU (l1 ⊔ l2)
  structure-comultiplication-copointed-endofunctor-Precategory =
    natural-transformation-Precategory C C
      ( functor-copointed-endofunctor-Precategory C T)
      ( comp-functor-Precategory C C C
        ( functor-copointed-endofunctor-Precategory C T)
        ( functor-copointed-endofunctor-Precategory C T))
```

### Associativity of multiplication on a copointed endofunctor on a precategory

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  (T : copointed-endofunctor-Precategory C)
  (μ : structure-comultiplication-copointed-endofunctor-Precategory C T)
  where

  associative-comul-copointed-endofunctor-Precategory : UU (l1 ⊔ l2)
  associative-comul-copointed-endofunctor-Precategory =
    comp-natural-transformation-Precategory C C
      ( functor-copointed-endofunctor-Precategory C T)
      ( comp-functor-Precategory C C C
        ( functor-copointed-endofunctor-Precategory C T)
        ( functor-copointed-endofunctor-Precategory C T))
      ( comp-functor-Precategory C C C
        ( functor-copointed-endofunctor-Precategory C T)
        ( comp-functor-Precategory C C C
          ( functor-copointed-endofunctor-Precategory C T)
          ( functor-copointed-endofunctor-Precategory C T)))
      ( left-whisker-natural-transformation-Precategory C C C
        ( functor-copointed-endofunctor-Precategory C T)
        ( comp-functor-Precategory C C C
          ( functor-copointed-endofunctor-Precategory C T)
          ( functor-copointed-endofunctor-Precategory C T))
        ( functor-copointed-endofunctor-Precategory C T)
        ( μ))
      ( μ) ＝
    comp-natural-transformation-Precategory C C
      ( functor-copointed-endofunctor-Precategory C T)
      ( comp-functor-Precategory C C C
        ( functor-copointed-endofunctor-Precategory C T)
        ( functor-copointed-endofunctor-Precategory C T))
      ( comp-functor-Precategory C C C
        ( functor-copointed-endofunctor-Precategory C T)
        ( comp-functor-Precategory C C C
          ( functor-copointed-endofunctor-Precategory C T)
          ( functor-copointed-endofunctor-Precategory C T)))
      ( right-whisker-natural-transformation-Precategory C C C
        ( functor-copointed-endofunctor-Precategory C T)
        ( comp-functor-Precategory C C C
          ( functor-copointed-endofunctor-Precategory C T)
          ( functor-copointed-endofunctor-Precategory C T))
        ( μ)
        ( functor-copointed-endofunctor-Precategory C T))
      ( μ)

  associative-comul-hom-family-copointed-endofunctor-Precategory : UU (l1 ⊔ l2)
  associative-comul-hom-family-copointed-endofunctor-Precategory =
    (λ x →
      (comp-hom-Precategory C
        (hom-functor-Precategory C C
          (functor-copointed-endofunctor-Precategory C T)
          (hom-family-natural-transformation-Precategory C C
            (functor-copointed-endofunctor-Precategory C T)
            (comp-functor-Precategory C C C
              (functor-copointed-endofunctor-Precategory C T)
              (functor-copointed-endofunctor-Precategory C T))
            μ
            x))
        (hom-family-natural-transformation-Precategory C C
          (functor-copointed-endofunctor-Precategory C T)
          (comp-functor-Precategory C C C
            (functor-copointed-endofunctor-Precategory C T)
            (functor-copointed-endofunctor-Precategory C T))
          μ
          x))) ~
    (λ x →
      (comp-hom-Precategory C
        (hom-family-natural-transformation-Precategory C C
          (functor-copointed-endofunctor-Precategory C T)
          (comp-functor-Precategory C C C
            (functor-copointed-endofunctor-Precategory C T)
            (functor-copointed-endofunctor-Precategory C T))
          μ
          (obj-functor-Precategory C C
            (functor-copointed-endofunctor-Precategory C T)
            x))
        (hom-family-natural-transformation-Precategory C C
          (functor-copointed-endofunctor-Precategory C T)
          (comp-functor-Precategory C C C
            (functor-copointed-endofunctor-Precategory C T)
            (functor-copointed-endofunctor-Precategory C T))
          μ
          x)))
```

### The left counit law on a comultiplication on a copointed endofunctor

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  (T : copointed-endofunctor-Precategory C)
  (μ : structure-comultiplication-copointed-endofunctor-Precategory C T)
  where

  left-counit-law-comul-copointed-endofunctor-Precategory : UU (l1 ⊔ l2)
  left-counit-law-comul-copointed-endofunctor-Precategory =
    comp-natural-transformation-Precategory C C
      ( functor-copointed-endofunctor-Precategory C T)
      ( comp-functor-Precategory C C C
        ( functor-copointed-endofunctor-Precategory C T)
        ( functor-copointed-endofunctor-Precategory C T))
      ( functor-copointed-endofunctor-Precategory C T)
      ( left-whisker-natural-transformation-Precategory C C C
        ( functor-copointed-endofunctor-Precategory C T)
        ( id-functor-Precategory C)
        ( functor-copointed-endofunctor-Precategory C T)
        ( copointing-copointed-endofunctor-Precategory C T))
      ( μ) ＝
    id-natural-transformation-Precategory C C
      ( functor-copointed-endofunctor-Precategory C T)

  left-counit-law-comul-hom-family-copointed-endofunctor-Precategory :
    UU (l1 ⊔ l2)
  left-counit-law-comul-hom-family-copointed-endofunctor-Precategory =
    (λ x →
      comp-hom-Precategory C
        (hom-functor-Precategory C C
          (functor-copointed-endofunctor-Precategory C T)
          (hom-family-natural-transformation-Precategory C C
            (functor-copointed-endofunctor-Precategory C T)
            (id-functor-Precategory C)
            (copointing-copointed-endofunctor-Precategory C T)
            x))
        (hom-family-natural-transformation-Precategory C C
          (functor-copointed-endofunctor-Precategory C T)
          (comp-functor-Precategory C C C
            (functor-copointed-endofunctor-Precategory C T)
            (functor-copointed-endofunctor-Precategory C T))
          μ
          x)) ~
    (λ x → id-hom-Precategory C)
```

### The right counit law on a comultiplication on a copointed endofunctor

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  (T : copointed-endofunctor-Precategory C)
  (μ : structure-comultiplication-copointed-endofunctor-Precategory C T)
  where

  right-counit-law-comul-copointed-endofunctor-Precategory : UU (l1 ⊔ l2)
  right-counit-law-comul-copointed-endofunctor-Precategory =
    comp-natural-transformation-Precategory C C
      ( functor-copointed-endofunctor-Precategory C T)
      ( comp-functor-Precategory C C C
        ( functor-copointed-endofunctor-Precategory C T)
        ( functor-copointed-endofunctor-Precategory C T))
      ( functor-copointed-endofunctor-Precategory C T)
      ( right-whisker-natural-transformation-Precategory C C C
        ( functor-copointed-endofunctor-Precategory C T)
        ( id-functor-Precategory C)
        ( copointing-copointed-endofunctor-Precategory C T)
        ( functor-copointed-endofunctor-Precategory C T))
      ( μ) ＝
    id-natural-transformation-Precategory C C
      ( functor-copointed-endofunctor-Precategory C T)

  right-counit-law-comul-hom-family-copointed-endofunctor-Precategory :
    UU (l1 ⊔ l2)
  right-counit-law-comul-hom-family-copointed-endofunctor-Precategory =
    (λ x →
      comp-hom-Precategory C
        (hom-family-natural-transformation-Precategory C C
          (functor-copointed-endofunctor-Precategory C T)
          (id-functor-Precategory C)
          (copointing-copointed-endofunctor-Precategory C T)
          (obj-functor-Precategory C C
            (functor-copointed-endofunctor-Precategory C T) x))
        (hom-family-natural-transformation-Precategory C C
          (functor-copointed-endofunctor-Precategory C T)
          (comp-functor-Precategory C C C
            (functor-copointed-endofunctor-Precategory C T)
            (functor-copointed-endofunctor-Precategory C T))
          μ
          x)) ~
    (λ x → id-hom-Precategory C)
```

### The structure of a comonad on a copointed endofunctor on a precategory

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  (T : copointed-endofunctor-Precategory C)
  where

  structure-comonad-copointed-endofunctor-Precategory : UU (l1 ⊔ l2)
  structure-comonad-copointed-endofunctor-Precategory =
    Σ ( structure-comultiplication-copointed-endofunctor-Precategory C T)
      ( λ μ →
        associative-comul-copointed-endofunctor-Precategory C T μ ×
        left-counit-law-comul-copointed-endofunctor-Precategory C T μ ×
        right-counit-law-comul-copointed-endofunctor-Precategory C T μ)
```

### The type of comonads on precategories

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  where

  comonad-Precategory : UU (l1 ⊔ l2)
  comonad-Precategory =
    Σ ( copointed-endofunctor-Precategory C)
      ( structure-comonad-copointed-endofunctor-Precategory C)

  module _
    (T : comonad-Precategory)
    where

    copointed-endofunctor-comonad-Precategory :
      copointed-endofunctor-Precategory C
    copointed-endofunctor-comonad-Precategory = pr1 T

    endofunctor-comonad-Precategory :
      functor-Precategory C C
    endofunctor-comonad-Precategory =
      functor-copointed-endofunctor-Precategory C
        ( copointed-endofunctor-comonad-Precategory)

    obj-endofunctor-comonad-Precategory :
      obj-Precategory C → obj-Precategory C
    obj-endofunctor-comonad-Precategory =
      obj-functor-Precategory C C endofunctor-comonad-Precategory

    hom-endofunctor-comonad-Precategory :
      {X Y : obj-Precategory C} →
      hom-Precategory C X Y →
      hom-Precategory C
        ( obj-endofunctor-comonad-Precategory X)
        ( obj-endofunctor-comonad-Precategory Y)
    hom-endofunctor-comonad-Precategory =
      hom-functor-Precategory C C endofunctor-comonad-Precategory

    preserves-id-endofunctor-comonad-Precategory :
      (X : obj-Precategory C) →
      hom-endofunctor-comonad-Precategory (id-hom-Precategory C {X}) ＝
      id-hom-Precategory C
    preserves-id-endofunctor-comonad-Precategory =
      preserves-id-functor-Precategory C C endofunctor-comonad-Precategory

    preserves-comp-endofunctor-comonad-Precategory :
      {X Y Z : obj-Precategory C} →
      (g : hom-Precategory C Y Z) (f : hom-Precategory C X Y) →
      hom-endofunctor-comonad-Precategory (comp-hom-Precategory C g f) ＝
      comp-hom-Precategory C
        ( hom-endofunctor-comonad-Precategory g)
        ( hom-endofunctor-comonad-Precategory f)
    preserves-comp-endofunctor-comonad-Precategory =
      preserves-comp-functor-Precategory C C
        ( endofunctor-comonad-Precategory)

    counit-comonad-Precategory :
      copointing-endofunctor-Precategory C endofunctor-comonad-Precategory
    counit-comonad-Precategory =
      copointing-copointed-endofunctor-Precategory C
        ( copointed-endofunctor-comonad-Precategory)

    hom-counit-comonad-Precategory :
      hom-family-functor-Precategory C C
        ( endofunctor-comonad-Precategory)
        ( id-functor-Precategory C)
    hom-counit-comonad-Precategory =
      hom-family-copointing-copointed-endofunctor-Precategory C
        ( copointed-endofunctor-comonad-Precategory)

    naturality-counit-comonad-Precategory :
      is-natural-transformation-Precategory C C
        ( endofunctor-comonad-Precategory)
        ( id-functor-Precategory C)
        ( hom-counit-comonad-Precategory)
    naturality-counit-comonad-Precategory =
      naturality-copointing-copointed-endofunctor-Precategory C
        ( copointed-endofunctor-comonad-Precategory)

    mul-comonad-Precategory :
      structure-comultiplication-copointed-endofunctor-Precategory C
        ( copointed-endofunctor-comonad-Precategory)
    mul-comonad-Precategory = pr1 (pr2 T)

    hom-comul-comonad-Precategory :
      hom-family-functor-Precategory C C
        ( endofunctor-comonad-Precategory)
        ( comp-functor-Precategory C C C
          ( endofunctor-comonad-Precategory)
          ( endofunctor-comonad-Precategory))
    hom-comul-comonad-Precategory =
      hom-family-natural-transformation-Precategory C C
        ( endofunctor-comonad-Precategory)
        ( comp-functor-Precategory C C C
          ( endofunctor-comonad-Precategory)
          ( endofunctor-comonad-Precategory))
        ( mul-comonad-Precategory)

    naturality-comul-comonad-Precategory :
      is-natural-transformation-Precategory C C
        ( endofunctor-comonad-Precategory)
        ( comp-functor-Precategory C C C
          ( endofunctor-comonad-Precategory)
          ( endofunctor-comonad-Precategory))
        ( hom-comul-comonad-Precategory)
    naturality-comul-comonad-Precategory =
      naturality-natural-transformation-Precategory C C
        ( endofunctor-comonad-Precategory)
        ( comp-functor-Precategory C C C
          ( endofunctor-comonad-Precategory)
          ( endofunctor-comonad-Precategory))
        ( mul-comonad-Precategory)

    associative-comul-comonad-Precategory :
      associative-comul-copointed-endofunctor-Precategory C
        ( copointed-endofunctor-comonad-Precategory)
        ( mul-comonad-Precategory)
    associative-comul-comonad-Precategory =
      pr1 (pr2 (pr2 T))

    associative-comul-hom-family-comonad-Precategory :
      associative-comul-hom-family-copointed-endofunctor-Precategory C
        (copointed-endofunctor-comonad-Precategory)
        (mul-comonad-Precategory)
    associative-comul-hom-family-comonad-Precategory =
      htpy-eq-hom-family-natural-transformation-Precategory C C
        endofunctor-comonad-Precategory
        (comp-functor-Precategory C C C
          endofunctor-comonad-Precategory
          (comp-functor-Precategory C C C
            endofunctor-comonad-Precategory
            endofunctor-comonad-Precategory))
        associative-comul-comonad-Precategory

    left-counit-law-comul-comonad-Precategory :
      left-counit-law-comul-copointed-endofunctor-Precategory C
        ( copointed-endofunctor-comonad-Precategory)
        ( mul-comonad-Precategory)
    left-counit-law-comul-comonad-Precategory =
      pr1 (pr2 (pr2 (pr2 T)))

    left-counit-law-comul-hom-family-comonad-Precategory :
      left-counit-law-comul-hom-family-copointed-endofunctor-Precategory C
        (copointed-endofunctor-comonad-Precategory)
        (mul-comonad-Precategory)
    left-counit-law-comul-hom-family-comonad-Precategory =
      htpy-eq-hom-family-natural-transformation-Precategory C C
        endofunctor-comonad-Precategory endofunctor-comonad-Precategory
        left-counit-law-comul-comonad-Precategory

    right-counit-law-comul-comonad-Precategory :
      right-counit-law-comul-copointed-endofunctor-Precategory C
        ( copointed-endofunctor-comonad-Precategory)
        ( mul-comonad-Precategory)
    right-counit-law-comul-comonad-Precategory =
      pr2 (pr2 (pr2 (pr2 T)))

    right-counit-law-comul-hom-family-comonad-Precategory :
      right-counit-law-comul-hom-family-copointed-endofunctor-Precategory C
        (copointed-endofunctor-comonad-Precategory)
        (mul-comonad-Precategory)
    right-counit-law-comul-hom-family-comonad-Precategory =
      htpy-eq-hom-family-natural-transformation-Precategory C C
        endofunctor-comonad-Precategory endofunctor-comonad-Precategory
        right-counit-law-comul-comonad-Precategory
```

## Coalgebras over a comonad

Note that coalgebra morphisms are in the usual direction, i.e. a coalgebra
morphism `a → b` comes from a morphism `a → b` in the underlying precategory,
not a morphism `b → a`.

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  (T : comonad-Precategory C)
  where

  module _
    {A : obj-Precategory C}
    (a : hom-Precategory C A (obj-endofunctor-comonad-Precategory C T A))
    where

    has-counit-law-comonad-coalgebra-Precategory : UU l2
    has-counit-law-comonad-coalgebra-Precategory =
        comp-hom-Precategory C (hom-counit-comonad-Precategory C T A) a ＝
        id-hom-Precategory C

    has-comul-law-comonad-coalgebra-Precategory : UU l2
    has-comul-law-comonad-coalgebra-Precategory =
        comp-hom-Precategory C (hom-endofunctor-comonad-Precategory C T a) a ＝
        comp-hom-Precategory C (hom-comul-comonad-Precategory C T A) a

    is-comonad-coalgebra-Precategory : UU l2
    is-comonad-coalgebra-Precategory =
        has-counit-law-comonad-coalgebra-Precategory ×
        has-comul-law-comonad-coalgebra-Precategory

  comonad-coalgebra-Precategory : UU (l1 ⊔ l2)
  comonad-coalgebra-Precategory =
    Σ (obj-Precategory C)
      (λ A →
      Σ (hom-Precategory C A (obj-endofunctor-comonad-Precategory C T A))
        (λ a -> is-comonad-coalgebra-Precategory a))

  obj-comonad-coalgebra-Precategory :
    comonad-coalgebra-Precategory → obj-Precategory C
  obj-comonad-coalgebra-Precategory = pr1

  hom-comonad-coalgebra-Precategory : (f : comonad-coalgebra-Precategory) →
    hom-Precategory C
      (obj-comonad-coalgebra-Precategory f)
      (obj-endofunctor-comonad-Precategory C T
        (obj-comonad-coalgebra-Precategory f))
  hom-comonad-coalgebra-Precategory f = pr1 (pr2 f)

  comm-comonad-coalgebra-Precategory : (f : comonad-coalgebra-Precategory) →
    is-comonad-coalgebra-Precategory (hom-comonad-coalgebra-Precategory f)
  comm-comonad-coalgebra-Precategory f = pr2 (pr2 f)

  counit-law-comonad-coalgebra-Precategory :
    (f : comonad-coalgebra-Precategory) →
    has-counit-law-comonad-coalgebra-Precategory
      (hom-comonad-coalgebra-Precategory f)
  counit-law-comonad-coalgebra-Precategory f = pr1 (pr2 (pr2 f))

  comul-law-comonad-coalgebra-Precategory :
    (f : comonad-coalgebra-Precategory) →
    has-comul-law-comonad-coalgebra-Precategory
      (hom-comonad-coalgebra-Precategory f)
  comul-law-comonad-coalgebra-Precategory f = pr2 (pr2 (pr2 f))

  morphism-comonad-coalgebra-Precategory :
    (f g : comonad-coalgebra-Precategory) → UU l2
  morphism-comonad-coalgebra-Precategory f g =
    Σ (hom-Precategory C
        (obj-comonad-coalgebra-Precategory f)
        (obj-comonad-coalgebra-Precategory g))
      (λ h →
        coherence-square-hom-Precategory C
          h
          (hom-comonad-coalgebra-Precategory f)
          (hom-comonad-coalgebra-Precategory g)
          (hom-endofunctor-comonad-Precategory C T h))

  hom-morphism-comonad-coalgebra-Precategory :
    (f g : comonad-coalgebra-Precategory)
    (h : morphism-comonad-coalgebra-Precategory f g) →
    hom-Precategory C
      (obj-comonad-coalgebra-Precategory f)
      (obj-comonad-coalgebra-Precategory g)
  hom-morphism-comonad-coalgebra-Precategory f g h = pr1 h

  bottom-hom-morphism-comonad-coalgebra-Precategory :
    (f g : comonad-coalgebra-Precategory)
    (h : morphism-comonad-coalgebra-Precategory f g) →
    hom-Precategory C
      (obj-endofunctor-comonad-Precategory C T
        (obj-comonad-coalgebra-Precategory f))
      (obj-endofunctor-comonad-Precategory C T
        (obj-comonad-coalgebra-Precategory g))
  bottom-hom-morphism-comonad-coalgebra-Precategory f g h =
    hom-endofunctor-comonad-Precategory C T
      (hom-morphism-comonad-coalgebra-Precategory f g h)

  comm-hom-morphism-comonad-coalgebra-Precategory :
    (f g : comonad-coalgebra-Precategory)
    (h : morphism-comonad-coalgebra-Precategory f g) →
    coherence-square-hom-Precategory C
      (hom-morphism-comonad-coalgebra-Precategory f g h)
      (hom-comonad-coalgebra-Precategory f)
      (hom-comonad-coalgebra-Precategory g)
      (bottom-hom-morphism-comonad-coalgebra-Precategory f g h)
  comm-hom-morphism-comonad-coalgebra-Precategory f g h = pr2 h

  comp-morphism-comonad-coalgebra-Precategory :
    (a b c : comonad-coalgebra-Precategory)
    (g : morphism-comonad-coalgebra-Precategory b c) →
    (f : morphism-comonad-coalgebra-Precategory a b) →
    morphism-comonad-coalgebra-Precategory a c
  comp-morphism-comonad-coalgebra-Precategory a b c g f =
    (comp-hom-Precategory C
      (hom-morphism-comonad-coalgebra-Precategory b c g)
      (hom-morphism-comonad-coalgebra-Precategory a b f)) ,
    (ap
      (precomp-hom-Precategory C (hom-comonad-coalgebra-Precategory a) _)
      (preserves-comp-endofunctor-comonad-Precategory C T _ _)) ∙
    (comp-coherence-square-hom-Precategory C
      (hom-morphism-comonad-coalgebra-Precategory a b f)
      (hom-comonad-coalgebra-Precategory a)
      (hom-comonad-coalgebra-Precategory b)
      (bottom-hom-morphism-comonad-coalgebra-Precategory a b f)
      (hom-morphism-comonad-coalgebra-Precategory b c g)
      (hom-comonad-coalgebra-Precategory c)
      (bottom-hom-morphism-comonad-coalgebra-Precategory b c g)
      (comm-hom-morphism-comonad-coalgebra-Precategory a b f)
      (comm-hom-morphism-comonad-coalgebra-Precategory b c g))

  is-set-morphism-comonad-coalgebra-Precategory :
    (f g : comonad-coalgebra-Precategory) →
    is-set (morphism-comonad-coalgebra-Precategory f g)
  is-set-morphism-comonad-coalgebra-Precategory f g =
    is-set-Σ
      (is-set-hom-Precategory C _ _)
      (λ hk → is-set-is-prop (is-set-hom-Precategory C _ _ _ _))
```

## The Eilenberg-Moore precategory of a comonad

The Eilenberg-Moore category `EM(T)` consists of all `T`-coalgebras and
`T`-coalgebra morphisms. It comes with an adjunction `C : ⇄ EM(T)`.

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  (T : comonad-Precategory C)
  where

  private
    Tf = endofunctor-comonad-Precategory C T
    T₁ = hom-endofunctor-comonad-Precategory C T
    T₀ = obj-endofunctor-comonad-Precategory C T

  em-comonad-Precategory : Precategory (l1 ⊔ l2) l2
  em-comonad-Precategory = make-Precategory
    (comonad-coalgebra-Precategory C T)
    (λ f g →
      (morphism-comonad-coalgebra-Precategory C T f g) ,
      (is-set-morphism-comonad-coalgebra-Precategory C T f g))
    (λ {a} {b} {c} g f →
      comp-morphism-comonad-coalgebra-Precategory C T a b c g f)
    (λ x →
      (id-hom-Precategory C) ,
      (ap
        (precomp-hom-Precategory C _ _)
        (preserves-id-endofunctor-comonad-Precategory C T _)) ∙
      (left-unit-law-comp-hom-Precategory C _) ∙
      (inv (right-unit-law-comp-hom-Precategory C _)))
    (λ h g f →
      eq-pair-Σ
        (associative-comp-hom-Precategory C _ _ _)
        (eq-is-prop (is-set-hom-Precategory C _ _ _ _)))
    (λ {a} {b} f →
      eq-pair-Σ
        (left-unit-law-comp-hom-Precategory C
          (hom-morphism-comonad-coalgebra-Precategory C T a b f))
        (eq-is-prop (is-set-hom-Precategory C _ _ _ _)))
    λ {a} {b} f →
      eq-pair-Σ
        (right-unit-law-comp-hom-Precategory C
          (hom-morphism-comonad-coalgebra-Precategory C T a b f))
        (eq-is-prop (is-set-hom-Precategory C _ _ _ _))

  obj-functor-to-em-comonad-Precategory :
    obj-Precategory C → obj-Precategory em-comonad-Precategory
  obj-functor-to-em-comonad-Precategory x =
    (obj-endofunctor-comonad-Precategory C T x) ,
    ((hom-comul-comonad-Precategory C T x) ,
      right-counit-law-comul-hom-family-comonad-Precategory C T x ,
      associative-comul-hom-family-comonad-Precategory C T x)

  hom-functor-to-em-comonad-Precategory : {x y : obj-Precategory C}
    (f : hom-Precategory C x y) →
    hom-Precategory em-comonad-Precategory
      (obj-functor-to-em-comonad-Precategory x)
      (obj-functor-to-em-comonad-Precategory y)
  hom-functor-to-em-comonad-Precategory f =
    (T₁ f) , naturality-comul-comonad-Precategory C T f

  functor-to-em-comonad-Precategory :
    functor-Precategory C em-comonad-Precategory
  functor-to-em-comonad-Precategory =
    obj-functor-to-em-comonad-Precategory ,
    hom-functor-to-em-comonad-Precategory ,
    (λ g f →
      eq-pair-Σ
        (preserves-comp-endofunctor-comonad-Precategory C T g f)
        (eq-is-prop (is-set-hom-Precategory C _ _ _ _))) ,
    (λ x →
      eq-pair-Σ
        (preserves-id-endofunctor-comonad-Precategory C T x)
        (eq-is-prop (is-set-hom-Precategory C _ _ _ _)))

  functor-from-em-comonad-Precategory :
    functor-Precategory em-comonad-Precategory C
  functor-from-em-comonad-Precategory =
    (obj-comonad-coalgebra-Precategory C T) ,
    (λ {x} {y} f → hom-morphism-comonad-coalgebra-Precategory C T x y f) ,
    (λ g f → refl) ,
    (λ x → refl)

  -- The unit x → Tx is exactly the unit of the comonad
  counit-em-comonad-Precategory :
    natural-transformation-Precategory C C
      (comp-functor-Precategory C em-comonad-Precategory C
        functor-from-em-comonad-Precategory
        functor-to-em-comonad-Precategory)
      (id-functor-Precategory C)
  counit-em-comonad-Precategory = counit-comonad-Precategory C T

  -- The unit is the vertical map given by the structure map of the coalgebra
  --       a
  --    x  →  Tx
  --  a ↓     ↓ μ
  --   Tx  → T²x
  --      Ta
  unit-em-comonad-Precategory :
    natural-transformation-Precategory
      em-comonad-Precategory em-comonad-Precategory
      (id-functor-Precategory em-comonad-Precategory)
      (comp-functor-Precategory em-comonad-Precategory C em-comonad-Precategory
        functor-to-em-comonad-Precategory functor-from-em-comonad-Precategory)
  unit-em-comonad-Precategory =
    (λ x →
      (hom-comonad-coalgebra-Precategory C T x) ,
      (comul-law-comonad-coalgebra-Precategory C T x)) ,
    (λ {x} {y} f → eq-pair-Σ
      (comm-hom-morphism-comonad-coalgebra-Precategory C T x y f)
      (eq-is-prop (is-set-hom-Precategory C _ _ _ _)))

  left-triangle-em-comonad-Precategory :
    has-left-triangle-identity-Precategory em-comonad-Precategory C
      functor-from-em-comonad-Precategory
      functor-to-em-comonad-Precategory
      unit-em-comonad-Precategory
      counit-em-comonad-Precategory
  left-triangle-em-comonad-Precategory x =
    counit-law-comonad-coalgebra-Precategory C T x

  right-triangle-em-comonad-Precategory :
    has-right-triangle-identity-Precategory em-comonad-Precategory C
      functor-from-em-comonad-Precategory
      functor-to-em-comonad-Precategory
      unit-em-comonad-Precategory
      counit-em-comonad-Precategory
  right-triangle-em-comonad-Precategory x =
    eq-pair-Σ
      (left-counit-law-comul-hom-family-comonad-Precategory C T x)
      (eq-is-prop (is-set-hom-Precategory C _ _ _ _))

  adjunction-em-comonad-Precategory :
    Adjunction-Precategory em-comonad-Precategory C
  adjunction-em-comonad-Precategory =
    make-Adjunction-Precategory em-comonad-Precategory C
      functor-from-em-comonad-Precategory
      functor-to-em-comonad-Precategory
      (is-adjoint-pair-unit-counit-Precategory em-comonad-Precategory C
        functor-from-em-comonad-Precategory
        functor-to-em-comonad-Precategory
        unit-em-comonad-Precategory
        counit-em-comonad-Precategory
        left-triangle-em-comonad-Precategory
        right-triangle-em-comonad-Precategory)
```
