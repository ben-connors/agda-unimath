# Generated equivalence relations

```agda
module foundation.generated-equivalence-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.equivalence-relations
open import foundation.existential-quantification
open import foundation.dependent-pair-types
open import foundation.equivalence-classes
open import foundation.effective-maps-equivalence-relations
open import foundation.fundamental-theorem-of-equivalence-relations
open import foundation.logical-equivalences
open import foundation.partitions
open import foundation.propositional-truncations
open import foundation.reflecting-maps-equivalence-relations
open import foundation.set-quotients
open import foundation.sigma-decompositions
open import foundation.surjective-maps
open import foundation.uniqueness-set-quotients
open import foundation.universal-property-set-quotients
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.sets
open import foundation-core.homotopies
open import foundation-core.coproduct-types
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.addition-natural-numbers
open import foundation.raising-universe-levels
open import foundation-core.cartesian-product-types
open import foundation-core.transport-along-identifications
open import foundation.propositional-truncations
```

</details>

## Idea

Given an arbitrary relation `R`, we construct an equivalence relation using `R`. First, we construct a new reflexive, symmetric, and transitive relation using paths of arbitrary length composed of edges of `R`: an edge from `x` to `y` is a term `R x y + R y x`, i.e. a relation in either direction. A path of length 0 is an identification `x ＝ y` and a path of length `n+1` is a choice of intermediate `x'`, a path from `x` to `x'` of length `n`, and an edge from `x'` to `y`. To construct the resulting equivalence relation we take the propositional truncation of this path relation.

```agda
module _
  {l : Level} {A : UU l} (R : Relation l A)
  where

  edge-Relation : (x y : A) → UU l
  edge-Relation x y = (R x y) + (R y x)

  inv-edge-Relation : (x y : A) (e : edge-Relation x y) → edge-Relation y x
  inv-edge-Relation x y (inl e) = inr e
  inv-edge-Relation x y (inr e) = inl e

  n-path-Relation : (x y : A) (n : ℕ) → UU l
  n-path-Relation x y zero-ℕ = x ＝ y
  n-path-Relation x y (succ-ℕ n) =
    Σ A (λ x' → (n-path-Relation x x' n) × (edge-Relation x' y))

  n-path-edge-Relation :
    (x y : A) (e : edge-Relation x y) → n-path-Relation x y 1
  n-path-edge-Relation x y e = x , (refl , e)

  refl-n-path-Relation : (x : A) → n-path-Relation x x zero-ℕ
  refl-n-path-Relation x = refl

  concat-n-path-Relation : (x y z : A) (n m : ℕ)
    (q : n-path-Relation y z m) (p : n-path-Relation x y n)  →
    n-path-Relation x z (n +ℕ m)
  concat-n-path-Relation x y z n zero-ℕ q p = tr _ q p
  concat-n-path-Relation x y z n (succ-ℕ m) (y' , q , e) p =
    ( y') ,
    ( concat-n-path-Relation x y y' n m q p) , e

  inv-n-path-Relation : (x y : A) (n : ℕ)
    (p : n-path-Relation x y n) →
    n-path-Relation y x n
  inv-n-path-Relation x y zero-ℕ = inv
  inv-n-path-Relation x y (succ-ℕ n) (x' , p , e) =
    tr (λ m → n-path-Relation y x m) (left-one-law-add-ℕ n)
      ( concat-n-path-Relation y x' x 1 n
        ( inv-n-path-Relation x x' n p)
        ( n-path-edge-Relation y x' (inv-edge-Relation x' y e)))

  path-Relation : Relation l A
  path-Relation x y = Σ ℕ (λ n → n-path-Relation x y n)

  is-reflexive-path-Relation : is-reflexive path-Relation
  is-reflexive-path-Relation x = (0 , refl-n-path-Relation x)

  is-symmetric-path-Relation : is-symmetric path-Relation
  is-symmetric-path-Relation x y (n , p) = n , (inv-n-path-Relation x y n p)

  is-transitive-path-Relation : is-transitive path-Relation
  is-transitive-path-Relation x y z (n , q) (m , p) =
    m +ℕ n , concat-n-path-Relation x y z m n q p

  path-Relation-Prop : Relation-Prop l A
  path-Relation-Prop x y = trunc-Prop (path-Relation x y)

  is-reflexive-path-Relation-Prop :
    is-reflexive-Relation-Prop path-Relation-Prop
  is-reflexive-path-Relation-Prop =
    unit-trunc-Prop ∘ is-reflexive-path-Relation

  is-symmetric-path-Relation-Prop :
    is-symmetric-Relation-Prop path-Relation-Prop
  is-symmetric-path-Relation-Prop x y =
    rec-trunc-Prop
      ( path-Relation-Prop y x)
      ( unit-trunc-Prop ∘ (is-symmetric-path-Relation x y))
  is-transitive-path-Relation-Prop :
    is-transitive-Relation-Prop path-Relation-Prop
  is-transitive-path-Relation-Prop x y z =
    rec-trunc-Prop
      ( path-Relation-Prop x y ⇒ path-Relation-Prop x z)
      ( λ q →
        rec-trunc-Prop
          ( path-Relation-Prop x z)
          ( λ p → unit-trunc-Prop (is-transitive-path-Relation x y z q p)))

  is-equivalence-relation-path-Relation-Prop :
    is-equivalence-relation path-Relation-Prop
  is-equivalence-relation-path-Relation-Prop =
    ( is-reflexive-path-Relation-Prop) ,
    ( ( is-symmetric-path-Relation-Prop ,
        is-transitive-path-Relation-Prop))
```

## Set coequalizers

Any pair of maps between sets `f, g : A → B` has a coequalizer given by the quotient of the set `B` by the relation generated by `x ~ y` if there is some `z : A` with `f(z) = x` and `g(z) = y`.

```agda
module _
  {l : Level} (A B : Set l) (f g : type-Set A → type-Set B)
  where

  private
    At = type-Set A
    Bt = type-Set B

  relation-coequalizer-Set : Relation l Bt
  relation-coequalizer-Set x y = Σ (At) (λ z → (f z ＝ x) × (g z ＝ y))

  path-relation-coequalizer-Set : Relation-Prop l Bt
  path-relation-coequalizer-Set = path-Relation-Prop relation-coequalizer-Set

  equivalence-relation-coequalizer-Set : equivalence-relation l (Bt)
  equivalence-relation-coequalizer-Set =
    ( path-relation-coequalizer-Set) ,
    ( is-equivalence-relation-path-Relation-Prop _)

  type-coequalizer-Set = equivalence-class equivalence-relation-coequalizer-Set

  map-coequalizer-Set : Bt → type-coequalizer-Set
  map-coequalizer-Set = class equivalence-relation-coequalizer-Set

  htpy-coequalizer-Set : map-coequalizer-Set ∘ f ~ map-coequalizer-Set ∘ g
  htpy-coequalizer-Set x =
    eq-share-common-element-equivalence-class
      ( equivalence-relation-coequalizer-Set)
      ( map-coequalizer-Set (f x))
      ( map-coequalizer-Set (g x))
      ( intro-exists
        ( g x)
        ( ( unit-trunc-Prop
            ( 1 ,
              ( n-path-edge-Relation relation-coequalizer-Set (f x) (g x)
                ( inl (x , (refl , refl)))))) ,
          ( is-reflexive-path-Relation-Prop _ (g x))))

  module _
    (C : Set l)
    (h : type-Set B → type-Set C)
    (G : h ∘ f ~ h ∘ g)
    where
```
