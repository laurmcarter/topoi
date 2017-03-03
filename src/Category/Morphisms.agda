
module Category.Morphisms where

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

  record Monic {a b} (f : a ⟶ b) : Set (o ⊔ m ⊔ e) where
    field
      monic : ∀ {c} (g h : c ⟶ a)
            → f ∘ g ∼ f ∘ h
            → g ∼ h
  open Monic public
  
  record Epic {a b} (f : a ⟶ b) : Set (o ⊔ m ⊔ e) where
    field
      epic : ∀ {c} (g h : b ⟶ c)
           → g ∘ f ∼ h ∘ f
           → g ∼ h
  open Epic public

{-
  record Equalizer {a b} (f g : a ⟶ b) : Set (o ⊔ m ⊔ e) where
    field
      ₀   : Obj
      ₁   : ₀ ⟶ a
      eq  : f ∘ ₁ ∼ g ∘ ₁
      eq! : {!!}
          -- → ∀ {c} {h : c ⟶ a}
          -- → (p : f ∘ h ∼ g ∘ h)
          -- → {!!}
-}
