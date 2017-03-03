
module Category.Objects where

open import Prelude as P
  hiding
    ( id
    ; _∘_
    ; Functor
    ; [_]
    ; refl
    ; sym
    ; trans
    )

open import Common.Setoid
open import Category

module _ {o m e} (C : Cat o m e) where
  open Cat C

  record Initial (𝟘 : Obj) : Set (o ⊔ m ⊔ e) where
    field
      𝟘! : ∀ {a} → 𝟘 ⟶ a
      initial! : ∀ {a} (f : 𝟘 ⟶ a) → f ∼ 𝟘!
  open Initial public

  Initial! : ∀ {𝟘 𝟘′} (i : Initial 𝟘) (j : Initial 𝟘′) → 𝟘 ≅ 𝟘′
  Initial! i j = 𝟘! i , record
    { inv  = 𝟘! j
    ; iso₁ = initial! i (𝟘! j ∘ 𝟘! i) ▸ sym (initial! i id)
    ; iso₂ = initial! j (𝟘! i ∘ 𝟘! j) ▸ sym (initial! j id)
    }

  record Terminal (𝟙 : Obj) : Set (o ⊔ m ⊔ e) where
    field
      𝟙! : ∀ {a} → a ⟶ 𝟙
      terminal! : ∀ {a} (f : a ⟶ 𝟙) → f ∼ 𝟙!
  open Terminal public

  Terminal! : ∀ {𝟙 𝟙′} (i : Terminal 𝟙) (j : Terminal 𝟙′) → 𝟙 ≅ 𝟙′
  Terminal! i j = 𝟙! j , record
    { inv  = 𝟙! i
    ; iso₁ = terminal! i (𝟙! i ∘ 𝟙! j) ▸ sym (terminal! i id)
    ; iso₂ = terminal! j (𝟙! j ∘ 𝟙! i) ▸ sym (terminal! j id)
    }
