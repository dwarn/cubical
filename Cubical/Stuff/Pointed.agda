{-# OPTIONS --safe #-}

module Cubical.Stuff.Pointed where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma

Pointed : Type1
Pointed = TypeWithStr ℓ-zero λ A → Σ[ B ∈ (A → Type) ] isContr (Σ A B)

triv : (X : Pointed) → typ X → Type
triv (A , B , _) = B

record _→∙_ (X Y : Pointed) : Type where
  field
    map1 : typ X → typ Y
    map2 : {x : typ X} → triv X x → triv Y (map1 x)

open _→∙_

Ω : Pointed → Pointed
Ω (A , B , _) = (Σ[ x ∈ A ] B x × B x) , (λ (x , p , q) → p ≡ q) , {!!}

Ω→ : {X Y : Pointed} → X →∙ Y → Ω X →∙ Ω Y
map1 (Ω→ f) (x , p , q) = map1 f x , map2 f p , map2 f q
map2 (Ω→ f) = cong (map2 f)

_∘∙_ : {X Y Z : Pointed} → Y →∙ Z → X →∙ Y → X →∙ Z
map1 (f ∘∙ g) x1 = map1 f (map1 g x1)
map2 (f ∘∙ g) x2 = map2 f (map2 g x2)

∘∙-assoc : {X Y Z W : Pointed} (f : Z →∙ W) (g : Y →∙ Z) (h : X →∙ Y) →
  (f ∘∙ g) ∘∙ h ≡ f ∘∙ (g ∘∙ h)
∘∙-assoc f g h = refl

Ωcomp : {X Y Z : Pointed} (f : Y →∙ Z) (g : X →∙ Y) →
        Ω→ (f ∘∙ g) ≡ Ω→ f ∘∙ Ω→ g
Ωcomp f g = refl
