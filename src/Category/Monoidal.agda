
module Category.Monoidal where

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

{-
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
-}

[_,_] C D = record
  { Obj = Functor C D
  ; _⟶_ = NaturalTransformation
  ; hom-setoid = λ F G →
    let module F = Functor F
        module G = Functor G
    in record
    { _∼_   = λ α β →
      let module α = NaturalTransformation α
          module β = NaturalTransformation β
      in
      ∀ a → α.₀ a D.∼ β.₀ a
    ; refl  = λ a → D.refl
    ; sym   = λ p a → D.sym (p a)
    ; trans = λ p q a → D.trans (p a) (q a)
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
  ; ∘λ  = λ a → D.∘λ
  ; ∘ρ  = λ a → D.∘ρ
  ; ∘α  = λ a → D.∘α
  ; ∘∼  = λ q p a → D.∘∼ (q a) (p a)
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
        module [C,D] = Cat [ C , D ]
    in record
    { ₀    = λ x → D.id
    ; comm = D.∘ρ D.▸ D.sym D.∘λ
    }
    , record
    { inv = record
      { ₀    = λ x → D.id
      ; comm = D.∘ρ D.▸ D.sym D.∘λ
      }
    ; iso₁ = λ a → D.∘ρ
    ; iso₂ = λ a → D.∘λ
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
    ; iso₁ = λ a → D.∘ρ
    ; iso₂ = λ a → D.∘λ
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
    ; iso₁ = λ a → D.∘ρ
    ; iso₂ = λ a → D.∘λ
    }
  ; ∘∼  = λ {A} {B} {C} {H} {I} qI {F} {G} pI →
    let module A = Cat A
        module B = Cat B
        module C = Cat C
        module [A,B] = Cat [ A , B ]
        module [B,C] = Cat [ B , C ]
        module [A,C] = Cat [ A , C ]
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
    ; iso₁ = λ a →
      C.[∘-]∼ q⁻¹.comm
      C.▸ C.∘α
      C.▸ C.[-∘]∼
        ( C.sym C.∘α
          C.▸ C.[∘-]∼
            ( C.sym I.∘
              C.▸ I.∼ ([A,B].iso₁ pIso a) 
              C.▸ I.id
            )
          C.▸ C.∘λ
        )
      C.▸ [B,C].iso₁ qIso (F.₀ a)
    ; iso₂ = λ a →
      C.[∘-]∼ q.comm
      C.▸ C.∘α
      C.▸ C.[-∘]∼
        ( C.sym C.∘α
          C.▸ C.[∘-]∼
            ( C.sym H.∘
              C.▸ H.∼ ([A,B].iso₂ pIso a)
              C.▸ H.id
            )
          C.▸ C.∘λ
        )
      C.▸ [B,C].iso₂ qIso (G.₀ a)
    }
  }
module CAT {o m e} = Cat (CAT o m e)

SetoidFunctor C D = [C,D].SetoidObj
  where
  module [C,D] = Cat [ C , D ]

CAT₀ = CAT lzero lzero lzero
-}
