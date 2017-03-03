
module Category.Adjunction where

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
open CAT-syntax

infix 1 _⊣_
record _⊣_ {o1 m1 e1 o2 m2 e2} {C : Cat o1 m1 e1} {D : Cat o2 m2 e2}
  (L : Functor C D) (R : Functor D C) : Set (o1 ⊔ m1 ⊔ e1 ⊔ o2 ⊔ m2 ⊔ e2) where
  private
    module C = Cat C
    module D = Cat D
    module [C] = Cat [ C , C ]
    module [D] = Cat [ D , D ]
    module L = Functor L
    module R = Functor R
  field
    η : idF ⇒ (R ∘F L)
    ε : (L ∘F R) ⇒ idF
  private
    module η = NatlTrans η
    module ε = NatlTrans ε
  field
    ₗ : ∀ a → ε.₀ (L.₀ a) D.∘ L.₁ (η.₀ a) D.∼ D.id
    ᵣ : ∀ a → R.₁ (ε.₀ a) C.∘ η.₀ (R.₀ a) C.∼ C.id

{-
record Cat o m e : Set (lsuc (o ⊔ m ⊔ e)) where
  infixr 9 _∘_
  field
    Obj : Set o
    _⟶_ : Obj → Obj → Set m
    hom-setoid : ∀ a b → Setoid e (a ⟶ b)
    id  : ∀ {a} → a ⟶ a
    _∘_ : ∀ {a b c} (g : b ⟶ c) (f : a ⟶ b) → a ⟶ c
  id⟨_⟩ : ∀ a → a ⟶ a
  id⟨_⟩ _ = id
  module SetoidHom {a b} = Setoid (hom-setoid a b)
  open SetoidHom public
  field
    ∘λ : ∀ {a b} {f : a ⟶ b} → id ∘ f ∼ f
    ∘ρ : ∀ {a b} {f : a ⟶ b} → f ∘ id ∼ f
    ∘α : ∀ {a b c d} {f : a ⟶ b} {g : b ⟶ c} {h : c ⟶ d} → (h ∘ g) ∘ f ∼ h ∘ (g ∘ f)
    ∘∼ : ∀ {a b c}
       → {h i : b ⟶ c} (q : h ∼ i)
       → {f g : a ⟶ b} (p : f ∼ g)
       → h ∘ f ∼ i ∘ g
  [-∘]∼ : ∀ {a b c}
        → {h : b ⟶ c}
        → {f g : a ⟶ b} (p : f ∼ g)
        → h ∘ f ∼ h ∘ g
  [-∘]∼ = ∘∼ refl 
  [∘-]∼ : ∀ {a b c}
        → {h i : b ⟶ c} (q : h ∼ i)
        → {f : a ⟶ b}
        → h ∘ f ∼ i ∘ f
  [∘-]∼ p = ∘∼ p refl

  record Iso {a b} (f : a ⟶ b) : Set (o ⊔ m ⊔ e) where
    field
      inv  : b ⟶ a
      iso₁ : inv ∘ f ∼ id
      iso₂ : f ∘ inv ∼ id
  open Iso public

  _⁻¹ : ∀ {a b} (f : a ⟶ b) {{_ : Iso f}} → b ⟶ a
  _⁻¹ f {{i}} = inv i

  infix 1 _≅_
  _≅_ : (a b : Obj) → Set _
  _≅_ a b = Σ (a ⟶ b) Iso

  SetoidObj : Setoid _ Obj
  SetoidObj = record
    { _∼_   = _≅_
    ; refl  = refl≅
    ; sym   = sym≅
    ; trans = trans≅
    }
    where
    refl≅ : ∀ {a} → a ≅ a
    refl≅ = id , record
      { inv  = id
      ; iso₁ = ∘λ
      ; iso₂ = ∘ρ
      }
    sym≅ : ∀ {a b} → a ≅ b → b ≅ a
    sym≅ (f , fIso) = f ⁻¹ , record
      { inv = f
      ; iso₁ = fIso.iso₂
      ; iso₂ = fIso.iso₁
      }
      where
      module fIso = Iso fIso
      private
        instance
          Iso-f = fIso
    trans≅ : ∀ {a b c} → a ≅ b → b ≅ c → a ≅ c
    trans≅ (f , fIso) (g , gIso) = g ∘ f , record
      { inv  = f ⁻¹ ∘ g ⁻¹
      ; iso₁ =
        ∘α
        ▸ [-∘]∼
          ( sym ∘α
          ▸ [∘-]∼ (iso₁ gIso)
          ▸ ∘λ
          )
        ▸ iso₁ fIso
      ; iso₂ =
        ∘α
        ▸ [-∘]∼
          ( sym ∘α
          ▸ [∘-]∼ (iso₂ fIso)
          ▸ ∘λ
          )
        ▸ iso₂ gIso
      }
      where
      private
        instance
          Iso-f = fIso
          Iso-g = gIso
  module SetoidObj = Setoid SetoidObj

Cat₀ = Cat lzero lzero lzero

record Functor {o1 m1 e1 o2 m2 e2} (C : Cat o1 m1 e1) (D : Cat o2 m2 e2) : Set (o1 ⊔ m1 ⊔ e1 ⊔ o2 ⊔ m2 ⊔ e2) where
  private
    module C = Cat C
    module D = Cat D
  field
    ₀  : C.Obj → D.Obj
    ₁  : ∀ {a b} (f : a C.⟶ b) → ₀ a D.⟶ ₀ b
    ∼  : ∀ {a b} {f g : a C.⟶ b}
       → (p : f C.∼ g)
       → ₁ f D.∼ ₁ g
    id : ∀ {a} → ₁ C.id⟨ a ⟩ D.∼ D.id
    ∘  : ∀ {a b c} {f : a C.⟶ b} {g : b C.⟶ c}
       → ₁ (g C.∘ f) D.∼ ₁ g D.∘ ₁ f

record NaturalTransformation {o1 m1 e1 o2 m2 e2} {C : Cat o1 m1 e1} {D : Cat o2 m2 e2} (F G : Functor C D) : Set (o1 ⊔ m1 ⊔ e1 ⊔ o2 ⊔ m2 ⊔ e2) where
  private
    module C = Cat C
    module D = Cat D
    module F = Functor F
    module G = Functor G
  field
    ₀    : ∀ a → F.₀ a D.⟶ G.₀ a
    comm : ∀ {a b} {f : a C.⟶ b}
         → G.₁ f D.∘ ₀ a D.∼ ₀ b D.∘ F.₁ f

CAT : ∀ o m e → Cat _ _ _

[_,_] : ∀ {o1 m1 e1 o2 m2 e2} (C : Cat o1 m1 e1) (D : Cat o2 m2 e2) → Cat _ _ _

SetoidFunctor : ∀ {o1 m1 e1 o2 m2 e2} (C : Cat o1 m1 e1) (D : Cat o2 m2 e2) → Setoid _ (Functor C D)

⇑ : ∀ o2 m2 e2 {o1 m1 e1} (C : Cat o1 m1 e1) → Cat _ _ _
⇑ o2 m2 e2 C = record
  { Obj = ↑ o2 Obj
  ; _⟶_ = λ a b → ↑ m2 (lower a ⟶ lower b)
  ; hom-setoid = λ a b → record
    { _∼_   = λ f g → ↑ e2 (lower f ∼ lower g)
    ; refl  = lift refl
    ; sym   = λ p → lift (sym (lower p))
    ; trans = λ p q → lift (trans (lower p) (lower q))
    }
  ; id  = lift id
  ; _∘_ = λ g f → lift (lower g ∘ lower f)
  ; ∘λ  = lift ∘λ
  ; ∘ρ  = lift ∘ρ
  ; ∘α  = lift ∘α
  ; ∘∼  = λ q p → lift (∘∼ (lower q) (lower p))
  }
  where
  open Cat C

[_,_] C D = record
  { Obj = Functor C D
  ; _⟶_ = NaturalTransformation
  -- truncated equivalence
  ; hom-setoid = λ F G →
    let module F = Functor F
        module G = Functor G
    in record
    { _∼_   = λ α β →
      let module α = NaturalTransformation α
          module β = NaturalTransformation β
      in
      {!β.₀!}
    ; refl  = {!!}
    ; sym   = {!!}
    ; trans = {!!}
    }
  ; id  = record
    { ₀    = λ x → D.id
    ; comm =
      D.∘ρ
      D.▸ D.sym D.∘λ
    }
  ; _∘_ = λ β α →
    let module α = NaturalTransformation α
        module β = NaturalTransformation β
    in record
      { ₀    = λ x → β.₀ x D.∘ α.₀ x
      ; comm =
        D.sym D.∘α
        D.▸ D.[∘-]∼ β.comm
        D.▸ D.∘α
        D.▸ D.[-∘]∼ α.comm
        D.▸ D.sym D.∘α
      }
  ; ∘λ  = {!!}
  ; ∘ρ  = {!!}
  ; ∘α  = {!!}
  ; ∘∼  = {!!}
  }
  where
  module C = Cat C
  module D = Cat D

CAT o m e = record
  { Obj = Cat o m e
  ; _⟶_ = Functor
  ; hom-setoid = λ C D → Cat.SetoidObj [ C , D ]
  ; id  = λ {A} →
    let module A = Cat A
    in record
    { ₀  = λ x → x
    ; ₁  = λ f → f
    ; ∼  = λ p → p
    ; id = A.refl
    ; ∘  = A.refl
    }
  ; _∘_ = λ {A} {B} {C} G F →
    let module A = Cat A
        module B = Cat B
        module C = Cat C
        module F = Functor F
        module G = Functor G
    in
    record
      { ₀  = λ x → G.₀ (F.₀ x)
      ; ₁  = λ f → G.₁ (F.₁ f)
      ; ∼  = λ p → G.∼ (F.∼ p)
      ; id = G.∼ F.id C.▸ G.id
      ; ∘  = G.∼ F.∘ C.▸ G.∘
      }
  ; ∘λ  = λ {C} {D} →
    let module C = Cat C
        module D = Cat D
    in record
    { ₀    = λ x → D.id
    ; comm = D.∘ρ D.▸ D.sym D.∘λ
    }
    , record
    { inv = record
      { ₀    = λ x → D.id
      ; comm = D.∘ρ D.▸ D.sym D.∘λ
      }
    ; iso₁ = {!!}
    ; iso₂ = {!!}
    }
  ; ∘ρ  = λ {C} {D} →
    let module C = Cat C
        module D = Cat D
    in record
    { ₀    = λ x → D.id
    ; comm = D.∘ρ D.▸ D.sym D.∘λ
    }
    , record
    { inv = record
      { ₀    = λ x → D.id
      ; comm = D.∘ρ D.▸ D.sym D.∘λ
      }
    ; iso₁ = {!!}
    ; iso₂ = {!!}
    }
  ; ∘α  = λ {A} {B} {C} {D} →
    let module A = Cat A
        module B = Cat B
        module C = Cat C
        module D = Cat D
    in record
    { ₀    = λ x → D.id
    ; comm = D.∘ρ D.▸ D.sym D.∘λ
    }
    , record
    { inv = record
      { ₀    = λ x → D.id
      ; comm = D.∘ρ D.▸ D.sym D.∘λ
      }
    ; iso₁ = {!!}
    ; iso₂ = {!!}
    }
  ; ∘∼  = λ {A} {B} {C} {H} {I} qI {F} {G} pI →
    let module A = Cat A
        module B = Cat B
        module C = Cat C
        module [A,B] = Cat [ A , B ]
        module [B,C] = Cat [ B , C ]
        module F = Functor F
        module G = Functor G
        module H = Functor H
        module I = Functor I
        p = fst pI
        q = fst qI
        private
          instance
            pIso = snd pI
            qIso = snd qI
        module p = NaturalTransformation p
        module q = NaturalTransformation q
        module p⁻¹ = NaturalTransformation (p [A,B].⁻¹)
        module q⁻¹ = NaturalTransformation (q [B,C].⁻¹)
    in
    record
    { ₀    = λ x → I.₁ (p.₀ x) C.∘ q.₀ (F.₀ x)
    ; comm =
      C.sym C.∘α
      C.▸ C.[∘-]∼
        ( C.sym I.∘
          C.▸ I.∼ p.comm
        )
      C.▸ q.comm
      C.▸ C.[-∘]∼ H.∘
      C.▸ C.sym C.∘α
      C.▸ C.[∘-]∼ (C.sym q.comm)
    } , record
    { inv = record
      { ₀    = λ x → H.₁ (p⁻¹.₀ x) C.∘ q⁻¹.₀ (G.₀ x)
      ; comm =
        C.sym C.∘α
        C.▸ C.[∘-]∼
          ( C.sym H.∘
            C.▸ H.∼ p⁻¹.comm
          )
        C.▸ q⁻¹.comm
        C.▸ C.[-∘]∼ I.∘
        C.▸ C.sym C.∘α
        C.▸ C.[∘-]∼ (C.sym q⁻¹.comm)
      }
    ; iso₁ = {!!}
    ; iso₂ = {!!}
    }
  }

SetoidFunctor C D = [C,D].SetoidObj
  where
  module [C,D] = Cat [ C , D ]

CAT₀ = CAT lzero lzero lzero

_ᵒᵖ : ∀ {o m e} (C : Cat o m e) → Cat _ _ _
C ᵒᵖ = record
  { Obj = Obj
  ; _⟶_ = λ a b → b ⟶ a
  ; hom-setoid = λ a b → hom-setoid b a
  ; id  = id
  ; _∘_ = λ g f → f ∘ g
  ; ∘λ  = ∘ρ
  ; ∘ρ  = ∘λ
  ; ∘α  = sym ∘α
  ; ∘∼  = λ q p → ∘∼ p q
  }
  where
  open Cat C

UNIT : Cat _ _ _
UNIT = record
  { Obj = ⊤
  ; _⟶_ = λ _ _ → ⊤
  ; hom-setoid = λ _ _ → UnitSetoid ⊤
  ; id  = tt
  ; _∘_ = λ _ _ → tt
  ; ∘λ  = tt
  ; ∘ρ  = tt
  ; ∘α  = tt
  ; ∘∼  = λ _ _ → tt
  }
module UNIT = Cat UNIT

SET : ∀ a → Cat _ _ _
SET a = record
  { Obj = Set a
  ; _⟶_ = λ A B → A → B
  ; hom-setoid = λ A B → record
    { _∼_   = λ f g → ∀ x → f x ≡ g x
    ; refl  = λ x → P.refl
    ; sym   = λ p x → P.sym (p x)
    ; trans = λ p q x → P.trans (p x) (q x)
    }
  ; id  = λ x → x
  ; _∘_ = λ g f x → g (f x)
  ; ∘λ  = λ x → P.refl
  ; ∘ρ  = λ x → P.refl
  ; ∘α  = λ x → P.refl
  ; ∘∼  = λ {_} {_} {_} {h} {i} q {f} {g} p x → P.trans (q (f x)) (i $≡ p x)
  }
module SET {a} = Cat (SET a)

SET₀ = SET lzero

PSH : ∀ {o m e} (C : Cat o m e) a → Cat _ _ _
PSH C a = [ C ᵒᵖ , SET a ]

PSH₀ : ∀ {o m e} (C : Cat o m e) → Cat _ _ _
PSH₀ C = [ C ᵒᵖ , SET₀ ]

⟨_,_⟩ : ∀ {o1 m1 e1 o2 m2 e2} (C : Cat o1 m1 e1) (D : Cat o2 m2 e2) → Cat _ _ _
⟨ C , D ⟩ = record
  { Obj = C.Obj × D.Obj
  ; _⟶_ = λ a b → (fst a C.⟶ fst b) × (snd a D.⟶ snd b)
  ; hom-setoid = λ a b → record
    { _∼_   = λ f g → (fst f C.∼ fst g) × (snd f D.∼ snd g)
    ; refl  = C.refl , D.refl
    ; sym   = λ p → C.sym (fst p) , D.sym (snd p)
    ; trans = λ p q → C.trans (fst p) (fst q) , D.trans (snd p) (snd q)
    }
  ; id  = C.id , D.id
  ; _∘_ = λ g f → fst g C.∘ fst f , snd g D.∘ snd f
  ; ∘λ  = C.∘λ , D.∘λ
  ; ∘ρ  = C.∘ρ , D.∘ρ
  ; ∘α  = C.∘α , D.∘α
  ; ∘∼  = λ q p → C.∘∼ (fst q) (fst p) , D.∘∼ (snd q) (snd p)
  }
  where
  module C = Cat C
  module D = Cat D

infix 1 _⊣_
record _⊣_ {o1 m1 e1 o2 m2 e2} {C : Cat o1 m1 e1} {D : Cat o2 m2 e2}
  (L : Functor C D) (R : Functor D C) : Set (o1 ⊔ m1 ⊔ e1 ⊔ o2 ⊔ m2 ⊔ e2) where
  private
    module C = Cat C
    module D = Cat D
    module [C] = Cat [ C , C ]
    module [D] = Cat [ D , D ]
    module L = Functor L
    module R = Functor R
  field
    η : {!!} [C].⟶ {!!}
    ε : {!!} [D].⟶ {!!}
  

-- ⅀ : ∀ {o1 m1 e1 o2 m2 e2} (C : Cat o1 m1 e1) (D : ⟦ [ C ᵒᵖ , CAT₀ ]′ ⟧) → {!!}
-- ⅀ = {!!}

{-
FAM : ∀ a b → Cat _ _ _
FAM a b = record
  { Obj = Σ (Set a) λ A → A → Set b
  ; _⟶_ = λ A B → Σ (fst A → fst B) λ f → ∀ x → snd A x → snd B (f x)
  ; hom-setoid = λ A B → record
    { _∼_   = λ f g → Σ (fst f SET.∼ fst g) λ p → ∀ x → transport (λ y → snd A x → snd B y) (p x) (snd f x) SET.∼ snd g x
    ; refl  = (λ x → P.refl) , (λ x y → P.refl)
    ; sym   = λ {f} {g} p → (λ x → P.sym (fst p x)) , (λ x y → {!!})
    ; trans = λ p q → (λ x → P.trans (fst p x) (fst q x)) , (λ x y → {!!})
    }
  ; id  = {!!}
  ; _∘_ = {!!}
  }
module FAM {a b} = Cat (FAM a b)
-}
-}
