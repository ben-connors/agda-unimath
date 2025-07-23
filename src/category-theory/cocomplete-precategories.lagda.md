# Cocomplete precategories

```agda
module category-theory.cocomplete-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.cocones-precategories
open import category-theory.functors-precategories
open import category-theory.colimits-precategories
open import category-theory.precategories
open import category-theory.initial-objects-precategories

open import foundation.universe-levels
```

</details>

## Idea

A {{#concept "cocomplete precategory" Agda=is-cocomplete-Precategory}} is a
[precategory](category-theory.precategories.md) that has all
[colimits](category-theory.colimits-precategories.md) for diagrams from a specified
universe.

More precisely, we say that a precategory `D` is `(l1 , l2)`-cocomplete if for any
`C : Precategory l1 l2` and any
[functor](category-theory.functors-precategories.md) `F : C → D` the type of
colimits of `F` is inhabited.

## Definition

```agda
has-all-colimits-of-shape-Precategory : {l1 l2 l3 l4 : Level}
  (C : Precategory l1 l2)
  (J : Precategory l3 l4) →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
has-all-colimits-of-shape-Precategory C J =
  (F : functor-Precategory J C) → colimit-Precategory J C F

is-cocomplete-Precategory :
  (l1 l2 : Level) {l3 l4 : Level}
  (D : Precategory l3 l4) →
  UU (lsuc l1 ⊔ lsuc l2 ⊔ l3 ⊔ l4)
is-cocomplete-Precategory l1 l2 D =
  (C : Precategory l1 l2) → has-all-colimits-of-shape-Precategory D C
```
