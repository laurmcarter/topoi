
module Category.Prelude where

open import Prelude as P public
  hiding
    ( id
    ; _∘_
    ; Functor
    ; [_]
    ; refl
    ; sym
    ; trans
    )

open import Common.Setoid public
open import Category public
open import Category.Adjunction

obj : ∀ {o m e} (C : Cat o m e) → Set o
obj = Cat.Obj

hom : ∀ {o m e} (C : Cat o m e) (a b : obj C) → Set m
hom = Cat._⟶_

eqv : ∀ {o m e} (C : Cat o m e) {a b : obj C} (f g : hom C a b) → Set e
eqv = Cat._∼_

record Lift {b a} (A : Set a) : Set (a ⊔ b) where
  constructor lift
  field
    lower : A
open Lift public

LIFT : ∀ {o2 m2 e2 o1 m1 e1} (C : Cat o1 m1 e1) → Cat _ _ _
LIFT {o2} {m2} {e2} C = record
  { Obj = Lift {o2} Obj
  ; _⟶_ = λ a b → Lift {m2} (lower a ⟶ lower b)
  ; hom-setoid = λ a b → record
    { _∼_   = λ f g → Lift {e2} (lower f ∼ lower g)
    ; refl  = lift refl
    ; sym   = λ p → lift (sym (lower p))
    ; trans = λ p q → lift (trans (lower p) (lower q))
    }
  ; id  = lift id
  ; _∘_ = λ g f → lift (lower g ∘ lower f)
  ; ∘λ  = lift ∘λ
  ; ∘ρ  = lift ∘ρ
  ; ∘α  = λ f g h → lift (∘α (lower f) (lower g) (lower h))
  ; ∘∼  = λ q p → lift (∘∼ (lower q) (lower p))
  }
  where
  open Cat C

{-
record 2Cat o1 m1 e1 m2 e2 : Set {!!} where
  field
    ₀   : Cat o1 m1 e1
  module ₀ = Cat ₀
  infix 1 _⇒_
  infixr 9 _∙_
  field
    _⇒_ : ∀ {a b} (f g : a ₀.⟶ b) → Set m2
    hom₁-setoid : ∀ {a b} (f g : a ₀.⟶ b)
                → Setoid e2 (f ⇒ g)
  module Hom₁Setoid {a b f g} = Setoid (hom₁-setoid {a} {b} f g)
  open Hom₁Setoid public
    renaming
      ( _∼_   to _∼₁_
      ; refl  to refl₁
      ; sym   to sym₁
      ; trans to trans₁
      ; _▸_   to _▸₁_
      )
  field
    Id : ∀ {a b} {f : a ₀.⟶ b}
        → f ⇒ f
    _∙_ : ∀ {a b} {f g h : a ₀.⟶ b}
        → (ψ : g ⇒ h) (φ : f ⇒ g)
        → f ⇒ h
    ∙λ  : ∀ {a b} {f g : a ₀.⟶ b}
        → {φ : f ⇒ g}
        → Id ∙ φ ∼₁ φ
    ∙ρ  : ∀ {a b} {f g : a ₀.⟶ b}
        → {φ : f ⇒ g}
        → φ ∙ Id ∼₁ φ
    ∙α  : ∀ {a b} {f g h i : a ₀.⟶ b}
        → {φ : f ⇒ g} {ψ : g ⇒ h} {χ : h ⇒ i}
        → (χ ∙ ψ) ∙ φ ∼₁ χ ∙ (ψ ∙ φ)
    ∙∼  : ∀ {a b} {f g h : a ₀.⟶ b}
        → {χ ξ : g ⇒ h} (q : χ ∼₁ ξ)
        → {φ ψ : f ⇒ g} (p : φ ∼₁ ψ)
        → χ ∙ φ ∼₁ ξ ∙ ψ
  ₁ : (a b : ₀.Obj) → Cat _ _ _
  ₁ a b = record
    { Obj = a ₀.⟶ b
    ; _⟶_ = _⇒_
    ; hom-setoid = hom₁-setoid
    ; id  = Id
    ; _∘_ = _∙_
    ; ∘λ  = ∙λ
    ; ∘ρ  = ∙ρ
    ; ∘α  = ∙α
    ; ∘∼  = ∙∼
    }
-}

_₀_ = Functor.₀
_₁_ = Functor.₁
infixl 20 _₀_ _₁_

_ᵒᵖ : ∀ {o m e} (C : Cat o m e) → Cat _ _ _
C ᵒᵖ = record
  { Obj = Obj
  ; _⟶_ = λ a b → b ⟶ a
  ; hom-setoid = λ a b → hom-setoid b a
  ; id  = id
  ; _∘_ = λ g f → f ∘ g
  ; ∘λ  = ∘ρ
  ; ∘ρ  = ∘λ
  ; ∘α  = λ f g h → sym (∘α h g f)
  ; ∘∼  = λ q p → ∘∼ p q
  }
  where
  open Cat C

{-
arr : ∀ {o m e} (C : Cat o m e) → Cat _ _ _
arr C = record
  { Obj = Σ Obj λ a → Σ Obj λ b → a ⟶ b
  ; _⟶_ = λ a b → {!!}
  ; hom-setoid = {!!}
  ; id  = {!!}
  ; _∘_ = {!!}
  ; ∘λ  = {!!}
  ; ∘ρ  = {!!}
  ; ∘α  = {!!}
  ; ∘∼  = {!!}
  }
  where
  open Cat C
-}

UNIT : Cat _ _ _
UNIT = record
  { Obj = ⊤
  ; _⟶_ = λ _ _ → ⊤
  ; hom-setoid = λ _ _ → UnitSetoid ⊤
  ; id  = tt
  ; _∘_ = λ _ _ → tt
  ; ∘λ  = tt
  ; ∘ρ  = tt
  ; ∘α  = λ _ _ _ → tt
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
  ; ∘α  = λ f g h x → P.refl
  ; ∘∼  = λ {_} {_} {_} {h} {i} q {f} {g} p x → P.trans (q (f x)) (i $≡ p x)
  }
module SET {a} = Cat (SET a)

SET₀ = SET lzero

Family : ∀ {a} b (A : Set a) → Set _
Family b A = A → Set b

FamilyObj : ∀ a b → Set _
FamilyObj a b = Σ (Set a) (Family b)

infix 1 _fam→_
_fam→_ : ∀ {a1 b1 a2 b2} (A : FamilyObj a1 b1) (B : FamilyObj a2 b2)
       → Set _
A fam→ B =
  Σ (fst A → fst B) λ f →
  ∀ x → snd A x → snd B (f x)

-- infix 1 _fam∼_

FAM : ∀ a b → Cat _ _ _
FAM a b = record
  { Obj = FamilyObj a b
  ; _⟶_ = _fam→_
  ; hom-setoid = λ a b → record
    { _∼_   = λ f g →
      Σ (∀ x → fst f x ≡ fst g x) λ p →
      ∀ x y → transport (snd b) (p x) (snd f x y) ≡ snd g x y
    ; refl  = (λ x → {!refl!}) , {!CAT-syntax._∼_!}
    ; sym   = {!!}
    ; trans = {!!}
    }
  ; id  = {!!}
  ; _∘_ = {!!}
  ; ∘λ  = {!!}
  ; ∘ρ  = {!!}
  ; ∘α  = {!!}
  ; ∘∼  = {!!}
  }

FAM[_] : ∀ {o1 m1 e1} (C : Cat o1 m1 e1) o2 m2 e2 → Cat _ _ _
FAM[ C ] o2 m2 e2 = record
  { Obj =
    Σ (Cat o2 m2 e2) λ D →
    C ⟶ D
  ; _⟶_ = λ D E →
    Σ (fst D ⟶ fst E) λ F →
    {!snd D!}
  ; hom-setoid = {!!}
  ; id = {!!}
  ; _∘_ = {!!}
  ; ∘λ = {!!}
  ; ∘ρ = {!!}
  ; ∘α = {!!}
  ; ∘∼ = {!!}
  }
  where
  open CAT-syntax

SetoidObj : ∀ a b → Set (lsuc (a ⊔ b))
SetoidObj a b = Σ (Set a) (Setoid b)

infix 1 _ext→_
_ext→_ : ∀ {a1 b1 a2 b2} (A : SetoidObj a1 b1) (B : SetoidObj a2 b2)
       → Set (a1 ⊔ b1 ⊔ a2 ⊔ b2)
A ext→ B =
  Σ (fst A → fst B) λ f → (∀ {x y} (p : x A.∼ y) → f x B.∼ f y)
  where
  module A = Setoid (snd A)
  module B = Setoid (snd B)

ext-setoid : ∀ {a1 b1 a2 b2} (A : SetoidObj a1 b1) (B : SetoidObj a2 b2)
     → Setoid (a1 ⊔ b2) (A ext→ B)
ext-setoid A B = record
  { _∼_   = λ f g → ∀ x → fst f x B.∼ fst g x
  ; refl  = λ x → B.refl
  ; sym   = λ p x → B.sym (p x)
  ; trans = λ p q x → B.trans (p x) (q x)
  }
  where
  module A = Setoid (snd A)
  module B = Setoid (snd B)

module ext {a1 b1 a2 b2} {A : SetoidObj a1 b1} {B : SetoidObj a2 b2} = Setoid (ext-setoid A B)

infix 1 _ext∼_
_ext∼_ : ∀ {a1 b1 a2 b2} {A : SetoidObj a1 b1} {B : SetoidObj a2 b2}
       → (f g : A ext→ B)
       → Set (a1 ⊔ b2)
_ext∼_ {A = A} {B} = Setoid._∼_ (ext-setoid A B)

{-
  Obj′ = Σ (Set a) (Setoid b)
  Hom′ : Obj′ → Obj′ → Set (a ⊔ b)
  Hom′ a b =
    Σ (fst a → fst b) λ f → (∀ {x y} (p : x A.∼ y) → f x B.∼ f y)
    where
    module A = Setoid (snd a)
    module B = Setoid (snd b)
  Hom′-setoid : (x y : Obj′) → Setoid (a ⊔ b) (Hom′ x y)
  Hom′-setoid a b = record
    { _∼_   = λ f g → ∀ x → fst f x B.∼ fst g x
    ; refl  = λ x → B.refl
    ; sym   = λ p x → B.sym (p x)
    ; trans = λ p q x → B.trans (p x) (q x)
    }
    where
    module A = Setoid (snd a)
    module B = Setoid (snd b)
-}

SETOID : ∀ a b → Cat _ _ _
SETOID a b = record
  { Obj        = Obj′
  ; _⟶_        = Hom′
  ; hom-setoid = Hom′-setoid
  ; id  = (λ x → x) , (λ p → p)
  ; _∘_ = λ g f → (λ x → fst g (fst f x)) , (λ p → snd g (snd f p))
  ; ∘λ  = λ {a} {b} x → Setoid.refl (snd b)
  ; ∘ρ  = λ {a} {b} x → Setoid.refl (snd b)
  ; ∘α  = λ {a} {b} {c} {d} f g h x → Setoid.refl (snd d)
  ; ∘∼  = λ {a} {b} {c} {h} {i} q {f} {g} p x → Setoid.trans (snd c) (snd h (p x)) (q (fst g x))
  }
  where
  Obj′ = Σ (Set a) (Setoid b)
  Hom′ : Obj′ → Obj′ → Set (a ⊔ b)
  Hom′ a b =
    Σ (fst a → fst b) λ f → (∀ {x y} (p : x A.∼ y) → f x B.∼ f y)
    where
    module A = Setoid (snd a)
    module B = Setoid (snd b)
  Hom′-setoid : (x y : Obj′) → Setoid (a ⊔ b) (Hom′ x y)
  Hom′-setoid a b = record
    { _∼_   = λ f g → ∀ x → fst f x B.∼ fst g x
    ; refl  = λ x → B.refl
    ; sym   = λ p x → B.sym (p x)
    ; trans = λ p q x → B.trans (p x) (q x)
    }
    where
    module A = Setoid (snd a)
    module B = Setoid (snd b)
module SETOID {a b} = Cat (SETOID a b)

PSH : ∀ {o m e} (C : Cat o m e) a → Cat _ _ _
PSH C a = [ C ᵒᵖ , SET a ]

Presheaf : ∀ {o m e} (C : Cat o m e) a → Set _
Presheaf C a = obj (PSH C a)

PSH₀ : ∀ {o m e} (C : Cat o m e) → Cat _ _ _
PSH₀ C = [ C ᵒᵖ , SET₀ ]

⟨_×_⟩ : ∀ {o1 m1 e1 o2 m2 e2} (C : Cat o1 m1 e1) (D : Cat o2 m2 e2) → Cat _ _ _
⟨ C × D ⟩ = record
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
  ; ∘α  = λ f g h → C.∘α′ , D.∘α′
  ; ∘∼  = λ q p → C.∘∼ (fst q) (fst p) , D.∘∼ (snd q) (snd p)
  }
  where
  module C = Cat C
  module D = Cat D

⟨_,_⟩ : ∀ {o1 m1 e1 o2 m2 e2 o3 m3 e3 o4 m4 e4}
      → {A : Cat o1 m1 e1} {B : Cat o2 m2 e2} {C : Cat o3 m3 e3} {D : Cat o4 m4 e4}
      → (F : Functor A B) (G : Functor C D)
      → Functor ⟨ A × C ⟩ ⟨ B × D ⟩
⟨ F , G ⟩ = record
  { ₀  = λ x → F.₀ (fst x) , G.₀ (snd x)
  ; ₁  = λ f → F.₁ (fst f) , G.₁ (snd f)
  ; ∼  = λ p → F.∼ (fst p) , G.∼ (snd p)
  ; id = F.id , G.id
  ; ∘  = F.∘ , G.∘
  }
  where
  module F = Functor F
  module G = Functor G

∘F× : ∀ {o1 m1 e1 o2 m2 e2 o3 m3 e3 o4 m4 e4 o5 m5 e5}
        → {A : Cat o1 m1 e1} {B : Cat o2 m2 e2} {C : Cat o3 m3 e3} {D : Cat o4 m4 e4} {E : Cat o5 m5 e5}
        → (H : Functor ⟨ B × D ⟩ E) (F : Functor A B) (G : Functor C D)
        → Functor ⟨ A × C ⟩ E
∘F× H F G = H ∘F ⟨ F , G ⟩
infix 1 ∘F×
syntax ∘F× H F G = F ×⟨ H ⟩× G

[_]INDEXED : ∀ {o1 m1 e1} (C : Cat o1 m1 e1) o2 m2 e2 → Cat _ _ _
[ C ]INDEXED o m e = [ C ᵒᵖ , CAT o m e ]

[_]IxCat : ∀ {o1 m1 e1} (C : Cat o1 m1 e1) o2 m2 e2 → Set _
[ C ]IxCat o m e = obj ([ C ]INDEXED o m e)

infixl 20 _⟨-,_⟩
_⟨-,_⟩ : ∀ {o1 m1 e1 o2 m2 e2 o3 m3 e3 o4 m4 e4}
       → {A : Cat o1 m1 e1} {B : Cat o2 m2 e2} {C : Cat o3 m3 e3} {D : Cat o4 m4 e4}
       → (G : Functor ⟨ C × B ⟩ D) (F : Functor A B)
       → Functor ⟨ C × A ⟩ D
_⟨-,_⟩ {C = C} G F = G ∘F ⟨ idF⟨ C ⟩ , F ⟩

infixl 20 _⟨_,-⟩
_⟨_,-⟩ : ∀ {o1 m1 e1 o2 m2 e2 o3 m3 e3 o4 m4 e4}
       → {A : Cat o1 m1 e1} {B : Cat o2 m2 e2} {C : Cat o3 m3 e3} {D : Cat o4 m4 e4}
       → (G : Functor ⟨ B × C ⟩ D) (F : Functor A B)
       → Functor ⟨ A × C ⟩ D
_⟨_,-⟩ {C = C} G F = G ∘F ⟨ F , idF⟨ C ⟩ ⟩

ObjF : ∀ o m e → Functor (CAT o m e) (SETOID o (o ⊔ m ⊔ e))
ObjF o m e = record
  { ₀  = obj₀
  ; ₁  = obj₁
  ; ∼  = λ {A} {B} {F} {G} p x →
    let module [A,B] = Cat [ A , B ]
        module B = Cat B
    in
    NatlTrans.₀ (fst p) x
    , record
      { inv  = NatlTrans.₀ ([A,B].inv (snd p)) x
      ; iso₁ = [A,B].iso₁ (snd p) x
      ; iso₂ = [A,B].iso₂ (snd p) x
      }
  ; id = λ {A} a → Cat.refl≅ A
  ; ∘  = λ {A} {B} {C} a → Cat.refl≅ C
  }
  where
  obj₀ : Cat o m e → SetoidObj o (o ⊔ m ⊔ e)
  obj₀ C = Cat.Obj C , Cat.SetoidObj C
  obj₁ : ∀ {A B} (F : Functor A B) → obj₀ A ext→ obj₀ B
  obj₁ F = F.₀ , F.≅
    where
    module F = Functor F

HomF : ∀ {o m e} (C : Cat o m e) → Functor ⟨ C ᵒᵖ × C ⟩ (SETOID m e)
HomF C = record
  { ₀  = λ x → (fst x ⟶ snd x) , hom-setoid (fst x) (snd x)
  ; ₁  = λ {a} {b} f →
    (λ g → snd f ∘ g ∘ fst f)
    , (λ p → [-∘]∼ ([∘-]∼ p))
  ; ∼  = λ p h → ∘∼ (snd p) ([-∘]∼ (fst p))
  ; id = λ h → ∘λ ▸ ∘ρ
  ; ∘  = λ h → ∘α′ ▸ [-∘]∼ ([-∘]∼ (sym ∘α′) ▸ sym ∘α′)
  }
  where
  open Cat C
  module ⟨Cᵒᵖ×C⟩ = Cat ⟨ C ᵒᵖ × C ⟩

{-
HOM : ∀ {o m e} (C : Cat o m e) → Cat _ _ _
HOM C = record
  { Obj = {!!}
  ; _⟶_ = {!!}
  ; hom-setoid = {!!}
  ; id = {!!}
  ; _∘_ = {!!}
  ; ∘λ = {!!}
  ; ∘ρ = {!!}
  ; ∘α = {!!}
  ; ∘∼ = {!!}
  }
-}

-- NaturalIsomorphism : {!!}
-- NaturalIsomorphism = {!!}

-- Curry : ∀ {o1 m1 e1 o2 m2 e2}
--       → {C : Cat o1 m1 e1} {D : Cat o2 m2 e2}
--       → ⟨ {!!} , {!!} ⟩ ⊣ {!!}
-- Curry = {!!}

record Monoidal {o m e} (C : Cat o m e) : Set (o ⊔ m ⊔ e) where
  open Cat C
  field
    𝟙   : Obj
    [⊗] : Functor ⟨ C × C ⟩ C
  module [⊗] = Functor [⊗]
  infixr 3 _⊗_ _⊗₁_ _⊗F_
  _⊗_ : (a b : Obj) → Obj
  _⊗_ a b = [⊗] ₀ (a , b)
  _⊗₁_ : ∀ {a b c d} (f : a ⟶ b) (g : c ⟶ d) → a ⊗ c ⟶ b ⊗ d
  _⊗₁_ f g = [⊗] ₁ (f , g)
  _⊗F_ : ∀ {o1 m1 e1 o2 m2 e2} {A : Cat o1 m1 e1} {B : Cat o2 m2 e2}
       → (F : Functor A C) (G : Functor B C)
       → Functor ⟨ A × B ⟩ C
  _⊗F_ F G = ∘F× [⊗] F G
  field
    ⊗λ : ∀ {a}
       → 𝟙 ⊗ a ≅ a
    ⊗ρ : ∀ {a}
       → a ⊗ 𝟙 ≅ a
    ⊗α : ∀ {a b c}
       → (a ⊗ b) ⊗ c ≅ a ⊗ (b ⊗ c)
  ⊗λ⟨_⟩ : ∀ a → 𝟙 ⊗ a ≅ a
  ⊗λ⟨_⟩ _ = ⊗λ
  ⊗ρ⟨_⟩ : ∀ a
     → a ⊗ 𝟙 ≅ a
  ⊗ρ⟨_⟩ _ = ⊗ρ
  ⊗α⟨_,_,_⟩ : ∀ a b c → (a ⊗ b) ⊗ c ≅ a ⊗ (b ⊗ c)
  ⊗α⟨_,_,_⟩ _ _ _ = ⊗α
  field
    λ⊗ρ : ∀ {a b}
        → (id ⊗₁ fst ⊗λ⟨ b ⟩) ∘ fst ⊗α⟨ a , 𝟙 , b ⟩
        ∼ (fst ⊗ρ⟨ a ⟩ ⊗₁ id)
    ρ⊗λ : ∀ {a b}
        → (id ⊗₁ fst ⊗λ⟨ b ⟩) ∘ fst ⊗α⟨ a , 𝟙 , b ⟩
        ∼ (fst ⊗ρ⟨ a ⟩ ⊗₁ id)
    α⊗α : ∀ {a b c d}
        → fst ⊗α⟨ a , b , c ⊗ d ⟩ ∘ fst ⊗α⟨ a ⊗ b , c , d ⟩
        ∼ (id ⊗₁ fst ⊗α⟨ b , c , d ⟩)
        ∘ fst ⊗α⟨ a , b ⊗ c , d ⟩
        ∘ (fst ⊗α⟨ a , b , c ⟩ ⊗₁ id)

MonCat : ∀ o m e → Set _
MonCat o m e = Σ (Cat o m e) Monoidal

module MonCat {o m e} (M : MonCat o m e) where
  open Cat (fst M) public
  open Monoidal (snd M) public

record Braided {o m e} (C : MonCat o m e) : Set (o ⊔ m ⊔ e) where
  open MonCat C
  field
    ⊗σ : ∀ {a b} → a ⊗ b ≅ b ⊗ a
  ⊗σ⟨_,_⟩ : ∀ a b
          → a ⊗ b ≅ b ⊗ a
  ⊗σ⟨_,_⟩ _ _ = ⊗σ
  field
    σ⊗α   : ∀ {a b c}
          → ⟪ ⊗α⟨ b , c , a ⟩ ⟫ ∘ ⟪ ⊗σ⟨ a , b ⊗ c ⟩ ⟫ ∘ ⟪ ⊗α⟨ a , b , c ⟩ ⟫
          ∼ (id ⊗₁ ⟪ ⊗σ⟨ a , c ⟩ ⟫) ∘ ⟪ ⊗α⟨ b , a , c ⟩ ⟫ ∘ (⟪ ⊗σ⟨ a , b ⟩ ⟫ ⊗₁ id)
    σ⊗α⁻¹ : ∀ {a b c}
          → ⟪ ⊗α⟨ c , a , b ⟩ ⁻¹ ⟫ ∘ ⟪ ⊗σ⟨ a ⊗ b , c ⟩ ⟫ ∘ ⟪ ⊗α⟨ a , b , c ⟩ ⁻¹ ⟫
          ∼ (⟪ ⊗σ⟨ a , c ⟩ ⟫ ⊗₁ id) ∘ ⟪ ⊗α⟨ a , c , b ⟩ ⁻¹ ⟫ ∘ (id ⊗₁ ⟪ ⊗σ⟨ b , c ⟩ ⟫)

BraidCat : ∀ o m e → Set _
BraidCat o m e = Σ (MonCat o m e) Braided

module BraidCat {o m e} (B : BraidCat o m e) where
  open MonCat (fst B) public
  open Braided (snd B) public

record Symmetric {o m e} (B : BraidCat o m e) : Set (o ⊔ m ⊔ e) where
  open BraidCat B
  field
    σ⊗σ : ∀ {a b}
        → fst ⊗σ⟨ b , a ⟩ ∘ fst ⊗σ⟨ a , b ⟩ ∼ id

SymmCat : ∀ o m e → Set _
SymmCat o m e = Σ (BraidCat o m e) Symmetric

module SymmCat {o m e} (S : SymmCat o m e) where
  open BraidCat  (fst S) public
  open Symmetric (snd S) public

MonoidalCAT : ∀ {o m e} → Monoidal (CAT o m e)
MonoidalCAT = record
  { 𝟙   = record
    { Obj = {!!}
    ; _⟶_ = {!!}
    ; hom-setoid = {!!}
    ; id  = {!!}
    ; _∘_ = {!!}
    ; ∘λ  = {!!}
    ; ∘ρ  = {!!}
    ; ∘α  = {!!}
    ; ∘∼  = {!!}
    }
  ; [⊗] = {!!}
  ; ⊗λ  = {!!}
  ; ⊗ρ  = {!!}
  ; ⊗α  = {!!}
  ; λ⊗ρ = {!!}
  ; ρ⊗λ = {!!}
  ; α⊗α = {!!}
  }

record [_]Enriched {o1 m1 e1} (K : MonCat o1 m1 e1) o2 : Set (o1 ⊔ m1 ⊔ e1 ⊔ lsuc o2) where
  private
    module K = MonCat K
  
  infix 2 _⟶_
  field
    Obj : Set o2
    _⟶_ : (a b : Obj) → K.Obj
  field
    id  : ∀ {a}
        → K.𝟙 K.⟶ (a ⟶ a)
    ∘   : ∀ {a b c}
        → (b ⟶ c) K.⊗ (a ⟶ b) K.⟶ (a ⟶ c)
  id⟨_⟩ : ∀ a
        → K.𝟙 K.⟶ (a ⟶ a)
  id⟨_⟩ _ = id
  ∘⟨_,_,_⟩ : ∀ a b c
           → (b ⟶ c) K.⊗ (a ⟶ b) K.⟶ (a ⟶ c)
  ∘⟨_,_,_⟩ _ _ _ = ∘
  field
    ∘λ  : ∀ {a b}
        → ∘⟨ a , a , b ⟩ K.∘ (K.id K.⊗₁ id⟨ a ⟩) K.∼ fst K.⊗ρ
        -- (id ∘ f) ∼ f
    ∘ρ  : ∀ {a b}
        → ∘⟨ a , b , b ⟩ K.∘ (id⟨ b ⟩ K.⊗₁ K.id) K.∼ fst K.⊗λ
        -- (f ∘ id) ∼ f
    ∘α  : ∀ {a b c d}
        → ∘⟨ a , b , d ⟩ K.∘ (∘⟨ b , c , d ⟩ K.⊗₁ K.id)
          K.∼ ∘⟨ a , c , d ⟩ K.∘ (K.id K.⊗₁ ∘⟨ a , b , c ⟩) K.∘ fst K.⊗α
        -- (h ∘ g) ∘ f ∼ h ∘ (g ∘ f)
    -- ∘∼  : ∀ {a b c}
    --     -- f ∼ g
    --     → ∘⟨ {!!} , {!!} , {!!} ⟩ K.∼ ∘⟨ {!!} , {!!} , {!!} ⟩
    --     -- (h ∘ f) ∼ (i ∘ g)

record Groupoid {o m e} (C : Cat o m e) : Set (o ⊔ m ⊔ e) where
  open Cat C
  field
    iso : ∀ {a b} (f : a ⟶ b) → Iso f

Grpd : ∀ o m e → Set _
Grpd o m e = Σ (Cat o m e) Groupoid

module Grpd {o m e} (G : Grpd o m e) where
  open Cat      (fst G) public
  open Groupoid (snd G) public

GRPD : ∀ o m e → Cat _ _ _
GRPD o m e = record
  { Obj = Grpd o m e
  ; _⟶_ = λ A B → fst A ⟶ fst B
  ; hom-setoid = λ A B → CAT.hom-setoid (fst A) (fst B)
  ; id = idF
  ; _∘_ = _∘F_
  ; ∘λ = CAT.∘λ
  ; ∘ρ = CAT.∘ρ
  ; ∘α = CAT.∘α
  ; ∘∼ = CAT.∘∼
  }
  where
  open CAT-syntax

record CwF o1 m1 e1 a b : Set {!!} where
  field
    C : Cat o1 m1 e1
    F : Functor (C ᵒᵖ) (FAM a b)
  open Cat C
    using
      ( _⟶_
      )
    renaming
      ( Obj to Ctx
      )
  private
    module C = Cat C
    module F = Functor F
  Ty : (Γ : Ctx) → Set a
  Ty Γ = fst (F.₀ Γ)
  Tm : (Γ : Ctx) (A : Ty Γ) → Set b
  Tm Γ = snd (F.₀ Γ)
  _[_] : ∀ {Γ Δ} (A : Ty Γ) (σ : Δ ⟶ Γ)
       → Ty Δ
  _[_] A σ = {!F.₁ σ!}
  infixl 2 _·_
  field 
    𝟙   : Ctx
    _·_ : (Γ : Ctx) (A : Ty Γ) → Ctx
    𝕡   : ∀ {Γ A} → Γ · A ⟶ Γ
    𝕢   : ∀ {Γ A} → Tm (Γ · A) {!F.₁ 𝕡!}

-- [_]ENRICHED : ∀ {o1 m1 e1} (C : Cat o1 m1 e1) o2 m2 e2 → Cat _ _ _
-- [ C ]ENRICHED o2 m2 e2 = record
--   { Obj = C.Obj
--   ; _⟶_ = {!!}
--   ; hom-setoid = {!!}
--   ; id  = {!!}
--   ; _∘_ = {!!}
--   ; ∘λ  = {!!}
--   ; ∘ρ  = {!!}
--   ; ∘α  = {!!}
--   ; ∘∼  = {!!}
--   }
--   where
--   module C = Cat C

-- [_]EnrichedCat {o1 m1 e1} (C : Cat o1 m1 e1) o2 m2 e2 : Set ? where
--   private
--     module C = Cat C
--   field
    

{-
Hom : ∀ {o m e} (C : Cat o m e) → Functor ⟨ C ᵒᵖ × C ⟩ (SET m)
Hom {m = m} C = record
  { ₀  = λ x → fst x ⟶ snd x
  ; ₁  = λ f g → snd f ∘ g ∘ fst f
  ; ∼  = λ {a} {b} {f} {g} p h → {!h!}
  ; id = {!!}
  ; ∘  = {!!}
  }
  where
  open Cat C
  module S = Cat (SET m)
-}

{-
⅀ : ∀ {o1 m1 e1 o2 m2 e2} (C : Cat o1 m1 e1) (D : [ C ]IxCat o2 m2 e2) → Cat _ _ _
⅀ C D = record
  { Obj = Σ C.Obj D.Obj
  ; _⟶_ = λ a b → Σ (fst a C.⟶ fst b) λ f → {!snd b!}
  ; hom-setoid = {!!}
  ; id  = {!!}
  ; _∘_ = {!!}
  ; ∘λ  = {!!}
  ; ∘ρ  = {!!}
  ; ∘α  = {!!}
  ; ∘∼  = {!!}
  }
  where
  module C = Cat C
  module 𝓓 = Functor D
  module D a = Cat (𝓓.₀ a)
-}

{-
∫ : ∀ {o m e a} (C : Cat o m e) (Γ : Presheaf C a) → Cat _ _ _
∫ {a = a} C Γ = record
  { Obj = Σ C.Obj Γ.₀
  ; _⟶_ = λ a b →
    Σ (fst a C.⟶ fst b) λ f →
    {!snd a!}
  ; hom-setoid = {!!}
  ; id  = {!!}
  ; _∘_ = {!!}
  ; ∘λ  = {!!}
  ; ∘ρ  = {!!}
  ; ∘α  = {!!}
  ; ∘∼  = {!!}
  }
  where
  module C    = Cat C
  module PshC = Cat (PSH C a)
  module Γ    = Functor Γ
-}

{-
  record
  { Obj = Σ C.Obj Γ.₀
  ; _⟶_ = λ a b →
    let J  = fst a
        I  = fst b
        ρ′ = snd a
        ρ  = snd b
    in
    Σ (J C.⟶ I) λ f →
    ρ′ Γ.₀.∼ Γ.₁ f ρ
  ; hom-setoid = λ a b →
    let J  = fst a
        I  = fst b
        ρ′ = snd a
        ρ  = snd b
    in record
    { _∼_   = λ σ τ → fst σ C.∼ fst τ
    ; refl  = C.refl
    ; sym   = C.sym
    ; trans = C.trans
    }
  ; id  = C.id , {!!}
  ; _∘_ = λ g f → {!!} , {!!}
  ; ∘λ  = λ {a} {b} {f} → C.∘λ {fst a} {fst b} {fst f}
  ; ∘ρ  = λ {a} {b} {f} → C.∘ρ {fst a} {fst b} {fst f}
  ; ∘α  = λ {a} {b} {c} {d} {f} {g} {h} → C.∘α {fst a} {fst b} {fst c} {fst d} {fst f} {fst g} {fst h}
  ; ∘∼  = {!Γ._∼_!}
  }
  where
  module C = Cat C
  module Γ = Presheaf∼ Γ
  open module ₀ {I} = Setoid (Γ.₀-setoid I)
-}


