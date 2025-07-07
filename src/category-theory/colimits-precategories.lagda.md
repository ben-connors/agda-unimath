# Colimits in precategories

```agda
module category-theory.colimits-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.cocones-precategories
open import category-theory.constant-functors
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

A
{{#concept "colimit" Disambiguation="of a functor of precategories" Agda=colimit-Precategory}}
of a [functor](category-theory.functors-precategories.md) `F` between
[precategories](category-theory.precategories.md) is a colimiting
[cocone](category-theory.cocones-precategories.md) under `F`. That is, a cocone
`τ` such that `cocone-map-Precategory C D F τ d` is an equivalence for all
`d : obj-Precategory D`.

Equivalently, the colimit of `F` is a
[left kan extension](category-theory.left-kan-extensions-precategories.md) of
`F` along the terminal functor into the
[terminal precategory](category-theory.terminal-category.md).

We show that both definitions coincide, and we will use the definition using
colimiting cocones as our official one.

If a colimit exists, we call the vertex of the colimiting cocone the **vertex**
of the colimit.

## Definition

### Colimiting cocones

```agda
module _
  {l1 l2 l3 l4 : Level} (C : Precategory l1 l2) (D : Precategory l3 l4)
  (F : functor-Precategory C D)
  where

  is-colimiting-cocone-Precategory :
    cocone-Precategory C D F → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-colimiting-cocone-Precategory τ =
    (d : obj-Precategory D) →
    is-equiv (cocone-map-Precategory C D F τ d)

  colimit-Precategory : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  colimit-Precategory =
    Σ ( cocone-Precategory C D F)
      ( is-colimiting-cocone-Precategory)

  cocone-colimit-Precategory :
    colimit-Precategory →
    cocone-Precategory C D F
  cocone-colimit-Precategory = pr1

  vertex-colimit-Precategory :
    colimit-Precategory →
    obj-Precategory D
  vertex-colimit-Precategory τ =
    vertex-cocone-Precategory C D F (cocone-colimit-Precategory τ)

  is-colimiting-colimit-Precategory :
    (τ : colimit-Precategory) →
    is-colimiting-cocone-Precategory (cocone-colimit-Precategory τ)
  is-colimiting-colimit-Precategory = pr2

  hom-cocone-colimit-Precategory :
    (τ : colimit-Precategory) →
    (φ : cocone-Precategory C D F) →
    hom-Precategory D
      ( vertex-colimit-Precategory τ)
      ( vertex-cocone-Precategory C D F φ)
  hom-cocone-colimit-Precategory τ φ =
    map-inv-is-equiv
      ( is-colimiting-colimit-Precategory τ
        ( vertex-cocone-Precategory C D F φ))
      ( natural-transformation-cocone-Precategory C D F φ)
```

### Colimits through left kan extensions

```agda
module _
  {l1 l2 l3 l4 : Level} (C : Precategory l1 l2) (D : Precategory l3 l4)
  (F : functor-Precategory C D)
  where

  is-colimit-left-extension-Precategory :
    left-extension-Precategory C terminal-Precategory D
      (terminal-functor-Precategory C) F →
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-colimit-left-extension-Precategory =
    is-left-kan-extension-Precategory C terminal-Precategory D
      (terminal-functor-Precategory C) F

  colimit-Precategory' : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  colimit-Precategory' =
    left-kan-extension-Precategory C terminal-Precategory D
      (terminal-functor-Precategory C) F

module _
  {l1 l2 l3 l4 : Level} (C : Precategory l1 l2) (D : Precategory l3 l4)
  (F : functor-Precategory C D) (L : colimit-Precategory' C D F)
  where

  left-extension-colimit-Precategory' :
    left-extension-Precategory C terminal-Precategory D
      (terminal-functor-Precategory C) F
  left-extension-colimit-Precategory' =
    left-extension-left-kan-extension-Precategory
      C terminal-Precategory D (terminal-functor-Precategory C) F L

  extension-colimit-Precategory' :
    functor-Precategory terminal-Precategory D
  extension-colimit-Precategory' =
    extension-left-kan-extension-Precategory
      C terminal-Precategory D (terminal-functor-Precategory C) F L
```

## Properties

### Being a colimit is a property

```agda
module _
  {l1 l2 l3 l4 : Level} (C : Precategory l1 l2) (D : Precategory l3 l4)
  (F : functor-Precategory C D)
  where

  is-prop-is-colimiting-cocone-Precategory :
    (τ : cocone-Precategory C D F) →
    is-prop (is-colimiting-cocone-Precategory C D F τ)
  is-prop-is-colimiting-cocone-Precategory τ =
    is-prop-Π λ φ → is-property-is-equiv _

  is-prop-is-colimit-Precategory' :
    ( R : left-extension-Precategory C terminal-Precategory D
      (terminal-functor-Precategory C) F) →
    is-prop (is-colimit-left-extension-Precategory C D F R)
  is-prop-is-colimit-Precategory' R =
    is-prop-Π λ K → is-property-is-equiv _
```

### Colimiting cocones are equivalent to colimits

```agda
module _
  {l1 l2 l3 l4 : Level} (C : Precategory l1 l2) (D : Precategory l3 l4)
  (F : functor-Precategory C D)
  where

  equiv-is-left-kan-extension-is-colimiting-Precategory :
    (τ : cocone-Precategory C D F) →
    is-colimiting-cocone-Precategory C D F τ ≃
      is-left-kan-extension-Precategory C terminal-Precategory D
      (terminal-functor-Precategory C) F
      (map-equiv (equiv-left-extension-cocone-Precategory C D F) τ)
  equiv-is-left-kan-extension-is-colimiting-Precategory τ =
    equiv-Π _
      ( equiv-point-Precategory D)
      ( λ x →
        equiv-iff-is-prop
          ( is-property-is-equiv _)
          ( is-property-is-equiv _)
          ( λ e →
            is-equiv-left-factor
            ( induced-left-extension-map x)
            ( natural-transformation-constant-functor-Precategory
              terminal-Precategory D)
            ( tr is-equiv (inv (lemma τ x)) e)
            ( is-equiv-natural-transformation-constant-functor-Precategory
              D _ _))
          ( λ e →
            tr is-equiv (lemma τ x)
              ( is-equiv-comp
                ( induced-left-extension-map x)
                ( natural-transformation-constant-functor-Precategory
                  terminal-Precategory D)
                ( is-equiv-natural-transformation-constant-functor-Precategory
                  D _ _)
                ( e))))
    where
      induced-left-extension-map = λ x →
        left-extension-map-Precategory C terminal-Precategory D
          ( terminal-functor-Precategory C) ( F)
          ( map-equiv (equiv-left-extension-cocone-Precategory C D F) τ)
          ( constant-functor-Precategory terminal-Precategory D x)
      lemma :
        ( τ : cocone-Precategory C D F)
        ( x : obj-Precategory D) →
          ( left-extension-map-Precategory C terminal-Precategory D
            ( terminal-functor-Precategory C) F
            ( map-equiv (equiv-left-extension-cocone-Precategory C D F) τ)
            ( constant-functor-Precategory terminal-Precategory D x)) ∘
          ( natural-transformation-constant-functor-Precategory
            terminal-Precategory D) ＝
        ( cocone-map-Precategory C D F τ x)
      lemma τ x =
        eq-htpy λ f →
          eq-htpy-hom-family-natural-transformation-Precategory C D
            ( F)
            ( comp-functor-Precategory C terminal-Precategory D
              ( point-Precategory D x)
              ( terminal-functor-Precategory C))
            ( _)
            ( _)
            ( λ g → refl)

  equiv-colimit-colimit'-Precategory :
    colimit-Precategory C D F ≃ colimit-Precategory' C D F
  equiv-colimit-colimit'-Precategory =
    equiv-Σ
      ( is-left-kan-extension-Precategory C terminal-Precategory D
        ( terminal-functor-Precategory C) F)
      ( equiv-left-extension-cocone-Precategory C D F)
      ( λ τ → equiv-is-left-kan-extension-is-colimiting-Precategory τ)

  colimit-colimit'-Precategory :
    colimit-Precategory C D F → colimit-Precategory' C D F
  colimit-colimit'-Precategory =
    map-equiv equiv-colimit-colimit'-Precategory

  colimit'-colimit-Precategory :
    colimit-Precategory' C D F → colimit-Precategory C D F
  colimit'-colimit-Precategory =
    map-inv-equiv equiv-colimit-colimit'-Precategory
```

## Coproducts (MOVE ME)

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  where

  module _
    {l : Level}
    (A : Set l)
    (let At = type-Set A)
    (f : At → obj-Precategory C)
    where

    is-coproduct-set-obj-Precategory :
      (w : obj-Precategory C)
      (i : (a : At) → hom-Precategory C (f a) w) →
      UU (l1 ⊔ l2 ⊔ l)
    is-coproduct-set-obj-Precategory w i =
      (w' : obj-Precategory C)
      (j : (a : At) → hom-Precategory C (f a) w') →
      uniquely-exists-structure
        ( hom-Precategory C w w')
        ( λ h →
          (a : At) → comp-hom-Precategory C h (i a) ＝ j a)

    coproduct-set-obj-Precategory : UU (l1 ⊔ l2 ⊔ l)
    coproduct-set-obj-Precategory =
      Σ ( obj-Precategory C)
        ( λ w →
          Σ ( (a : At) → hom-Precategory C (f a) w)
            ( λ i →
              is-coproduct-set-obj-Precategory w i))

    module _
      (c : coproduct-set-obj-Precategory)
      where

      obj-coproduct-set-obj-Precategory : obj-Precategory C
      obj-coproduct-set-obj-Precategory = pr1 c

      iota-coproduct-set-obj-Precategory :
        (a : At) → hom-Precategory C (f a) obj-coproduct-set-obj-Precategory
      iota-coproduct-set-obj-Precategory = pr1 (pr2 c)

      module _
        (w' : obj-Precategory C)
        (j : (a : At) → hom-Precategory C (f a) w')
        where

        mor-from-coproduct-set-obj-Precategory :
          hom-Precategory C obj-coproduct-set-obj-Precategory w'
        mor-from-coproduct-set-obj-Precategory =
          pr1 (pr1 (pr2 (pr2 c) w' j))

        compute-mor-from-coproduct-set-obj-Precategory :
          (a : At) →
          comp-hom-Precategory C
            ( mor-from-coproduct-set-obj-Precategory)
            ( iota-coproduct-set-obj-Precategory a) ＝
          j a
        compute-mor-from-coproduct-set-obj-Precategory =
          pr2 (pr1 (pr2 (pr2 c) w' j))

        is-unique-mor-from-coproduct-set-obj-Precategory :
          (j' : hom-Precategory C obj-coproduct-set-obj-Precategory w')
          (α : (a : At) → comp-hom-Precategory C j' (iota-coproduct-set-obj-Precategory a) ＝ j a) →
          mor-from-coproduct-set-obj-Precategory ＝ j'
        is-unique-mor-from-coproduct-set-obj-Precategory j' α =
          ap pr1 (pr2 (pr2 (pr2 c) w' j) (j' , α))

      module _
        (w' : obj-Precategory C)
        (j : (a : At) → hom-Precategory C (f a) w')
        {w'' : obj-Precategory C}
        (h : hom-Precategory C w' w'')
        where

        postcomp-mor-from-coproduct-set-obj-Precategory :
          mor-from-coproduct-set-obj-Precategory
            ( w'')
            ( λ a → comp-hom-Precategory C h (j a)) ＝
          comp-hom-Precategory C
            ( h)
            ( mor-from-coproduct-set-obj-Precategory w' j)
        postcomp-mor-from-coproduct-set-obj-Precategory =
          is-unique-mor-from-coproduct-set-obj-Precategory _ _ _
            ( λ a →
              ( associative-comp-hom-Precategory C _ _ _) ∙
              ( ap (comp-hom-Precategory C h )
                ( compute-mor-from-coproduct-set-obj-Precategory w' j a)))

has-all-coproduct-set-obj-Precategory :
  {l1 l2 : Level} (C : Precategory l1 l2)
  (l : Level) →
  UU (l1 ⊔ l2 ⊔ lsuc l)
has-all-coproduct-set-obj-Precategory C l =
  (A : Set l)
  (f : type-Set A → obj-Precategory C) →
  coproduct-set-obj-Precategory C A f
```

## Colimits from coequalizers and coproducts (MOVE ME)

We can construct colimits of functors when the codomain category has coproducts and coequalizers. Specifically, we require the existence of two coproducts for a functor `F : J → C`:

1. `⨆_{j : Ob J} Fj`; and
2. `⨆_{f : i → j ∈ J} Fi`.

For simplicity, we ask that `C` is instead closed under set-indexed coproducts, in which case the colimit exists whenever the objects of `J` form a set. In univalent categories this limits us to domains which are [gaunt categories](category-theory.gaunt-categories.md).

```agda
module _
  {l1 l2 : Level} (C : Precategory l1 l2)
  (q : has-all-coequalizer-obj-Precategory C)
  {l : Level}
  (i : has-all-coproduct-set-obj-Precategory C l)
  (J : Precategory l l)
  (is-set-J : is-set (obj-Precategory J))
  (let Js = (obj-Precategory J , is-set-J))
  (F : functor-Precategory J C)
  (let F₀ = obj-functor-Precategory J C F)
  (let F₁ = hom-functor-Precategory J C F)
  where

  coproduct-obj-J₀ :
    coproduct-set-obj-Precategory C Js F₀
  coproduct-obj-J₀ =
    i Js F₀

  obj-coproduct-obj-J₀ = obj-coproduct-set-obj-Precategory C Js F₀ coproduct-obj-J₀

  J₁ : Set l
  J₁ =
    Σ-Set
      ( Js)
      ( λ x →
        Σ-Set
          ( Js)
          ( λ y → hom-set-Precategory J x y))

  J₁t = type-Set J₁

  J₁m : J₁t → obj-Precategory C
  J₁m (x , (y , m)) = F₀ x

  coproduct-obj-J₁ :
    coproduct-set-obj-Precategory C J₁ J₁m
  coproduct-obj-J₁ = i J₁ J₁m

  obj-coproduct-obj-J₁ = obj-coproduct-set-obj-Precategory C J₁ J₁m coproduct-obj-J₁

  iota1 :
    (j : J₁t) → hom-Precategory C (J₁m j) obj-coproduct-obj-J₁
  iota1 = pr1 (pr2 (i J₁ J₁m))

  iota0 :
    (j : obj-Precategory J) → hom-Precategory C (F₀ j) obj-coproduct-obj-J₀
  iota0 = pr1 (pr2 (i Js F₀))

  iota :
    (j : J₁t) →
    hom-Precategory C (J₁m j) obj-coproduct-obj-J₀
  iota (x , (y , f)) = iota0 x

  iiota : hom-Precategory C obj-coproduct-obj-J₁ obj-coproduct-obj-J₀
  iiota = mor-from-coproduct-set-obj-Precategory C J₁ J₁m coproduct-obj-J₁ obj-coproduct-obj-J₀ iota

  iota' :
    (j : J₁t) →
    hom-Precategory C (J₁m j) obj-coproduct-obj-J₀
  iota' (x , (y , f)) =
    comp-hom-Precategory C
      (iota0 y)
      (F₁ f) 

  iiota' : hom-Precategory C obj-coproduct-obj-J₁ obj-coproduct-obj-J₀
  iiota' = mor-from-coproduct-set-obj-Precategory C J₁ J₁m coproduct-obj-J₁ obj-coproduct-obj-J₀ iota'

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
        ( ( ap (comp-hom-Precategory C cm) (compute-mor-from-coproduct-set-obj-Precategory C J₁ J₁m coproduct-obj-J₁ obj-coproduct-obj-J₀ iota' _)) ∙
          ( inv (associative-comp-hom-Precategory C _ _ _)))) ∙
      ( inv
        ( ( inv (associative-comp-hom-Precategory C _ _ _)) ∙
          ( ap
            ( precomp-hom-Precategory C (iota1 (j , j' , f)) _)
            ( coh-coequalizer-obj-Precategory C iiota iiota' candidate)) ∙
          ( associative-comp-hom-Precategory C _ _ _))) ∙
      ( ap (comp-hom-Precategory C cm) (compute-mor-from-coproduct-set-obj-Precategory C J₁ J₁m coproduct-obj-J₁ obj-coproduct-obj-J₀ iota _))

  cocone : cocone-Precategory J C F
  cocone = make-cocone-Precategory J C F
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
      mor-from-coproduct-set-obj-Precategory C Js F₀ coproduct-obj-J₀ dob dh

    dmor-coeq-pre :
      (f : J₁t) →
      comp-hom-Precategory C dmor (iota f) ＝
      comp-hom-Precategory C dmor (iota' f)
    dmor-coeq-pre (j , j' , f) =
      ( compute-mor-from-coproduct-set-obj-Precategory C Js F₀ coproduct-obj-J₀ dob dh j) ∙
      ( dn f) ∙
      ( ap (precomp-hom-Precategory C (F₁ f) _)
        ( inv
          ( compute-mor-from-coproduct-set-obj-Precategory C Js F₀
              coproduct-obj-J₀ dob dh j'))) ∙
      ( associative-comp-hom-Precategory C _ _ _)

    dmor-coeq :
      comp-hom-Precategory C dmor iiota ＝
      comp-hom-Precategory C dmor iiota'
    dmor-coeq =
      ( inv (postcomp-mor-from-coproduct-set-obj-Precategory C J₁ J₁m
              coproduct-obj-J₁ obj-coproduct-obj-J₀ iota dmor)) ∙
      ( ap (mor-from-coproduct-set-obj-Precategory C J₁ J₁m coproduct-obj-J₁ dob) (eq-htpy dmor-coeq-pre)) ∙
      ( postcomp-mor-from-coproduct-set-obj-Precategory C J₁ J₁m coproduct-obj-J₁ obj-coproduct-obj-J₀ iota' dmor)

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
        ( pr2 (pr1 (pr2 (pr2 (i Js F₀)) dob dh)) a)

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
            ( is-unique-mor-from-coproduct-set-obj-Precategory C Js F₀
              coproduct-obj-J₀ dob dh _
              ( λ a →
                ( associative-comp-hom-Precategory C _ _ _) ∙
                ( anothercoh a))))

 
  module _
    (d : obj-Precategory C)
    (let themap = cocone-map-Precategory J C F cocone d)
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

  iscolimit : is-colimiting-cocone-Precategory J C F cocone
  iscolimit d = is-equiv-is-invertible (theinverse d) (G d) (H d)
```
