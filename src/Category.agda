
module Category where

open import Prelude as P
  hiding
    ( id
    ; _∘_
    ; Functor
    ; [_]
    ; refl
    ; sym
    ; trans
    ; transport₂
    )

open import Common.Setoid

record Cat o m e : Set (lsuc (o ⊔ m ⊔ e)) where
  infix  1 _⟶_
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
    ∘α : ∀ {a b c d} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) → (h ∘ g) ∘ f ∼ h ∘ (g ∘ f)
    ∘∼ : ∀ {a b c}
       → {h i : b ⟶ c} (q : h ∼ i)
       → {f g : a ⟶ b} (p : f ∼ g)
       → h ∘ f ∼ i ∘ g
  ∘α′  : ∀ {a b c d} {f : a ⟶ b} {g : b ⟶ c} {h : c ⟶ d} → (h ∘ g) ∘ f ∼ h ∘ (g ∘ f)
  ∘α′ {f = f} {g} {h} = ∘α f g h
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

  infix 1 _≅_
  _≅_ : (a b : Obj) → Set _
  _≅_ a b = Σ (a ⟶ b) Iso

  ⟪_⟫ : ∀ {a b} (f : a ≅ b) → a ⟶ b
  ⟪_⟫ = fst

  refl≅ : ∀ {a} → a ≅ a
  refl≅ = id , record
    { inv  = id
    ; iso₁ = ∘λ
    ; iso₂ = ∘ρ
    }

  sym≅ : ∀ {a b} (f : a ≅ b) → b ≅ a
  sym≅ f = inv (snd f) , record
    { inv = fst f
    ; iso₁ = iso₂ (snd f)
    ; iso₂ = iso₁ (snd f)
    }
  _⁻¹ : ∀ {a b} (f : a ≅ b) → b ≅ a
  _⁻¹ f = sym≅ f

  trans≅ : ∀ {a b c} (f : a ≅ b) (g : b ≅ c) → a ≅ c
  trans≅ f g = fst g ∘ fst f , record
    { inv  = inv (snd f) ∘ inv (snd g)
    ; iso₁ =
      ∘α′
      ▸ [-∘]∼
        ( sym ∘α′
        ▸ [∘-]∼ (iso₁ (snd g))
        ▸ ∘λ
        )
      ▸ iso₁ (snd f)
    ; iso₂ =
      ∘α′
      ▸ [-∘]∼
        ( sym ∘α′
        ▸ [∘-]∼ (iso₂ (snd f))
        ▸ ∘λ
        )
      ▸ iso₂ (snd g)
    }

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

  -- infix 1 _↣_ _↠_

  SetoidObj : Setoid _ Obj
  SetoidObj = record
    { _∼_   = _≅_
    ; refl  = refl≅
    ; sym   = sym≅
    ; trans = trans≅
    }
  module SetoidObj = Setoid SetoidObj

obj[_] : ∀ {o m e} (C : Cat o m e) → Set o
obj[_] = Cat.Obj

hom[_] : ∀ {o m e} (C : Cat o m e) (a b : obj[ C ]) → Set m
hom[_] = Cat._⟶_

eqv[_] : ∀ {o m e} (C : Cat o m e) {a b : obj[ C ]} (f g : hom[ C ] a b) → Set e
eqv[_] = Cat._∼_

id[_] : ∀ {o m e} (C : Cat o m e) {a : obj[ C ]} → hom[ C ] a a
id[_] = Cat.id

∘[_] : ∀ {o m e} (C : Cat o m e) {a b c : obj[ C ]}
      → (g : hom[ C ] b c)
      → (f : hom[ C ] a b)
      → hom[ C ] a c
∘[_] = Cat._∘_
infixr 9 ∘[_]

{-# DISPLAY Cat.Obj C     = obj[ C ] #-}
{-# DISPLAY Cat._⟶_ C a b = hom[ C ] a b #-}
{-# DISPLAY Cat._∼_ C f g = eqv[ C ] f g #-}
{-# DISPLAY Cat.id  C     =  id[ C ] #-}
{-# DISPLAY Cat._∘_ C g f =   ∘[ C ] g f #-}

record Precat o m : Set (lsuc (o ⊔ m)) where
  field
    `obj : Set o
    `hom : (a b : `obj) → Set m
open Precat public

precat : ∀ {o m e} (C : Cat o m e) → Precat o m
precat C = record
  { `obj = obj[ C ]
  ; `hom = hom[ C ]
  }

Cat₀ = Cat lzero lzero lzero

record Functor {o1 m1 e1 o2 m2 e2}
  (C : Cat o1 m1 e1) (D : Cat o2 m2 e2) : Set (o1 ⊔ m1 ⊔ e1 ⊔ o2 ⊔ m2 ⊔ e2) where
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
  ≅ : ∀ {a b} (f : a C.≅ b) → ₀ a D.≅ ₀ b
  ≅ {a} {b} f =
    ₁ (fst f)
    , record
      { inv  = ₁ (C.inv (snd f))
      ; iso₁ = D.sym ∘ D.▸ ∼ (C.iso₁ (snd f)) D.▸ id
      ; iso₂ = D.sym ∘ D.▸ ∼ (C.iso₂ (snd f)) D.▸ id
      }

_₀𝓯_ : ∀ {o1 m1 e1 o2 m2 e2}
     → {C : Cat o1 m1 e1} {D : Cat o2 m2 e2}
     → (F : Functor C D)
     → (a : obj[ C ])
     → obj[ D ]
_₀𝓯_ = Functor.₀

_₁𝓯_ : ∀ {o1 m1 e1 o2 m2 e2}
     → {C : Cat o1 m1 e1} {D : Cat o2 m2 e2}
     → (F : Functor C D)
     → {a b : obj[ C ]}
     → (f : hom[ C ] a b)
     → hom[ D ] (F ₀𝓯 a) (F ₀𝓯 b)
_₁𝓯_ = Functor.₁
infixl 20 _₀𝓯_ _₁𝓯_

{-# DISPLAY Functor.₀ F x = F ₀𝓯 x #-}
{-# DISPLAY Functor.₁ F f = F ₁𝓯 f #-}

record NatlTrans {o1 m1 e1 o2 m2 e2}
  {C : Cat o1 m1 e1} {D : Cat o2 m2 e2}
  (F G : Functor C D) : Set (o1 ⊔ m1 ⊔ e1 ⊔ o2 ⊔ m2 ⊔ e2) where
  private
    module C = Cat C
    module D = Cat D
    module F = Functor F
    module G = Functor G
  field
    ₀ : ∀ x → F.₀ x D.⟶ G.₀ x
    ₁ : ∀ {x y} {f : x C.⟶ y}
      → G.₁ f D.∘ ₀ x D.∼ ₀ y D.∘ F.₁ f

_₀𝓽_ : ∀ {o1 m1 e1 o2 m2 e2}
     → {C : Cat o1 m1 e1} {D : Cat o2 m2 e2}
     → {F G : Functor C D}
     → (α : NatlTrans F G)
     → (x : obj[ C ])
     → hom[ D ] (F ₀𝓯 x) (G ₀𝓯 x)
_₀𝓽_ = NatlTrans.₀

_₁𝓽_ : ∀ {o1 m1 e1 o2 m2 e2}
     → {C : Cat o1 m1 e1} {D : Cat o2 m2 e2}
     → {F G : Functor C D}
     → (α : NatlTrans F G)
     → ∀ {x y} (f : hom[ C ] x y)
     → eqv[ D ] (∘[ D ] (G ₁𝓯 f) (α ₀𝓽 x)) (∘[ D ] (α ₀𝓽 y) (F ₁𝓯 f))
_₁𝓽_ α _ = NatlTrans.₁ α
infixl 20 _₀𝓽_ _₁𝓽_

{-# DISPLAY NatlTrans.₀ α x = α ₀𝓽 x #-}
{-# DISPLAY NatlTrans.₁ α f = α ₁𝓽 f #-}

CAT : ∀ o m e → Cat _ _ _

[_,_] : ∀ {o1 m1 e1 o2 m2 e2} (C : Cat o1 m1 e1) (D : Cat o2 m2 e2) → Cat _ _ _

SetoidFunctor : ∀ {o1 m1 e1 o2 m2 e2} (C : Cat o1 m1 e1) (D : Cat o2 m2 e2) → Setoid _ (Functor C D)

module CAT-syntax where
  infix 1 _⟶_ _⇒_ _∼_
  _⟶_ = Functor
  _⇒_ = NatlTrans
  _∼_ : ∀ {o1 m1 e1 o2 m2 e2} {C : Cat o1 m1 e1} {D : Cat o2 m2 e2}
      → (F G : C ⟶ D)
      → Set _
  _∼_ {C = C} {D} = Setoid._∼_ (SetoidFunctor C D)
  {-# DISPLAY Functor C D = C ⟶ D #-}
  {-# DISPLAY NatlTrans F G = F ⇒ G #-}
  {-# DISPLAY Setoid._∼_ _ a b = a ∼ b #-}
open CAT-syntax

idF : ∀ {o m e} {C : Cat o m e} → C ⟶ C
idF {C = C} = record
  { ₀  = λ x → x
  ; ₁  = λ f → f
  ; ∼  = λ p → p
  ; id = refl
  ; ∘  = refl
  }
  where
  open Cat C

idF⟨_⟩ : ∀ {o m e} (C : Cat o m e) → C ⟶ C
idF⟨ _ ⟩ = idF

infixr 9 _∘F_
_∘F_ : ∀ {o1 m1 e1 o2 m2 e2 o3 m3 e3}
    → {C : Cat o1 m1 e1} {D : Cat o2 m2 e2} {E : Cat o3 m3 e3}
    → (G : D ⟶ E) (F : C ⟶ D)
    → C ⟶ E
_∘F_ {E = E} G F = record
  { ₀  = λ x → G.₀ (F.₀ x)
  ; ₁  = λ f → G.₁ (F.₁ f)
  ; ∼  = λ p → G.∼ (F.∼ p)
  ; id = G.∼ F.id E.▸ G.id
  ; ∘  = G.∼ F.∘ E.▸ G.∘
  }
  where
  module E = Cat E
  module F = Functor F
  module G = Functor G

idT : ∀ {o1 m1 e1 o2 m2 e2}
    → {C : Cat o1 m1 e1} {D : Cat o2 m2 e2}
    → {F : C ⟶ D}
    → F ⇒ F
idT {D = D} = record
  { ₀ = λ x → id
  ; ₁ = ∘ρ ▸ sym ∘λ
  }
  where
  open Cat D

idT⟨_⟩ : ∀ {o1 m1 e1 o2 m2 e2}
    → {C : Cat o1 m1 e1} {D : Cat o2 m2 e2}
    → (F : C ⟶ D)
    → F ⇒ F
idT⟨ _ ⟩ = idT

infixr 9 _∘T_
_∘T_ : ∀ {o1 m1 e1 o2 m2 e2}
    → {C : Cat o1 m1 e1} {D : Cat o2 m2 e2}
    → {F G H : C ⟶ D}
    → (β : G ⇒ H)
    → (α : F ⇒ G)
    → F ⇒ H
_∘T_ {D = D} β α = record
  { ₀    = λ x → β.₀ x ∘ α.₀ x
  ; ₁ =
    sym ∘α′
    ▸ [∘-]∼ β.₁
    ▸ ∘α′
    ▸ [-∘]∼ α.₁
    ▸ sym ∘α′
  }
  where
  open Cat D
  module α = NatlTrans α
  module β = NatlTrans β

[_,_] C D = record
  { Obj = Functor C D
  ; _⟶_ = NatlTrans
  ; hom-setoid = λ F G →
    let module F = Functor F
        module G = Functor G
    in record
    { _∼_   = λ α β →
      let module α = NatlTrans α
          module β = NatlTrans β
      in
      ∀ a → α.₀ a D.∼ β.₀ a
    ; refl  = λ a → D.refl
    ; sym   = λ p a → D.sym (p a)
    ; trans = λ p q a → D.trans (p a) (q a)
    }
  ; id  = idT
  ; _∘_ = _∘T_
  ; ∘λ  = λ a → D.∘λ
  ; ∘ρ  = λ a → D.∘ρ
  ; ∘α  = λ f g h a → D.∘α (NatlTrans.₀ f a) (NatlTrans.₀ g a) (NatlTrans.₀ h a)
  ; ∘∼  = λ q p a → D.∘∼ (q a) (p a)
  }
  where
  module C = Cat C
  module D = Cat D

CAT o m e = record
  { Obj = Cat o m e
  ; _⟶_ = Functor
  ; hom-setoid = λ C D → Cat.SetoidObj [ C , D ]
  ; id  = idF
  ; _∘_ = _∘F_
  ; ∘λ  = λ {C} {D} →
    let module C = Cat C
        module D = Cat D
        module [C,D] = Cat [ C , D ]
    in record
    { ₀ = λ x → D.id
    ; ₁ = D.∘ρ D.▸ D.sym D.∘λ
    }
    , record
    { inv = record
      { ₀ = λ x → D.id
      ; ₁ = D.∘ρ D.▸ D.sym D.∘λ
      }
    ; iso₁ = λ a → D.∘ρ
    ; iso₂ = λ a → D.∘λ
    }
  ; ∘ρ  = λ {C} {D} →
    let module C = Cat C
        module D = Cat D
    in record
    { ₀ = λ x → D.id
    ; ₁ = D.∘ρ D.▸ D.sym D.∘λ
    }
    , record
    { inv = record
      { ₀    = λ x → D.id
      ; ₁ = D.∘ρ D.▸ D.sym D.∘λ
      }
    ; iso₁ = λ a → D.∘ρ
    ; iso₂ = λ a → D.∘λ
    }
  ; ∘α  = λ {A} {B} {C} {D} _ _ _ →
    let module A = Cat A
        module B = Cat B
        module C = Cat C
        module D = Cat D
    in record
    { ₀ = λ x → D.id
    ; ₁ = D.∘ρ D.▸ D.sym D.∘λ
    }
    , record
    { inv = record
      { ₀    = λ x → D.id
      ; ₁ = D.∘ρ D.▸ D.sym D.∘λ
      }
    ; iso₁ = λ a → D.∘ρ
    ; iso₂ = λ a → D.∘λ
    }
  ; ∘∼  = λ {A} {B} {C} {H} {I} q {F} {G} p →
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
        module p = NatlTrans (fst p)
        module q = NatlTrans (fst q)
        module p⁻¹ = NatlTrans ([A,B].inv (snd p))
        module q⁻¹ = NatlTrans ([B,C].inv (snd q))
    in
    record
    { ₀    = λ x → I.₁ (p.₀ x) C.∘ q.₀ (F.₀ x)
    ; ₁ =
      C.sym C.∘α′
      C.▸ C.[∘-]∼
        ( C.sym I.∘
          C.▸ I.∼ p.₁
        )
      C.▸ q.₁
      C.▸ C.[-∘]∼ H.∘
      C.▸ C.sym C.∘α′
      C.▸ C.[∘-]∼ (C.sym q.₁)
    } , record
    { inv = record
      { ₀ = λ x → H.₁ (p⁻¹.₀ x) C.∘ q⁻¹.₀ (G.₀ x)
      ; ₁ =
        C.sym C.∘α′
        C.▸ C.[∘-]∼
          ( C.sym H.∘
            C.▸ H.∼ p⁻¹.₁
          )
        C.▸ q⁻¹.₁
        C.▸ C.[-∘]∼ I.∘
        C.▸ C.sym C.∘α′
        C.▸ C.[∘-]∼ (C.sym q⁻¹.₁)
      }
    ; iso₁ = λ a →
      C.[∘-]∼ q⁻¹.₁
      C.▸ C.∘α′
      C.▸ C.[-∘]∼
        ( C.sym C.∘α′
          C.▸ C.[∘-]∼
            ( C.sym I.∘
              C.▸ I.∼ ([A,B].iso₁ (snd p) a) 
              C.▸ I.id
            )
          C.▸ C.∘λ
        )
      C.▸ [B,C].iso₁ (snd q) (F.₀ a)
    ; iso₂ = λ a →
      C.[∘-]∼ q.₁
      C.▸ C.∘α′
      C.▸ C.[-∘]∼
        ( C.sym C.∘α′
          C.▸ C.[∘-]∼
            ( C.sym H.∘
              C.▸ H.∼ ([A,B].iso₂ (snd p) a)
              C.▸ H.id
            )
          C.▸ C.∘λ
        )
      C.▸ [B,C].iso₂ (snd q) (G.₀ a)
    }
  }
module CAT {o m e} = Cat (CAT o m e)

SetoidFunctor C D = [C,D].SetoidObj
  where
  module [C,D] = Cat [ C , D ]

NatlI : ∀ {o1 m1 e1 o2 m2 e2} {C : Cat o1 m1 e1} {D : Cat o2 m2 e2}
      → (F G : C ⟶ D)
      → Set (o1 ⊔ m1 ⊔ e1 ⊔ o2 ⊔ m2 ⊔ e2)
NatlI {C = C} {D} = Setoid._∼_ (SetoidFunctor C D)

CAT₀ = CAT lzero lzero lzero

{-
PRECAT : ∀ o m → Cat _ _ _
PRECAT o m = record
  { Obj = Precat o m
  ; _⟶_ = λ A B →
    Σ (`obj A → `obj B) λ f →
    ∀ {a b} → `hom A a b → `hom B (f a) (f b)
  ; hom-setoid = λ A B → record
    { _∼_   = λ f g →
      Σ (∀ x → fst f x ≡ fst g x) λ p →
      ∀ {x y} (h : `hom A x y)
        → p y · p x · snd f h
                    ∈ `hom B fx (fst f y) [ fst g x / fx ]
              ∈ `hom B (fst g x) fy [ fst g y / fy ]
        ≡ snd g h
    ; refl  = (λ x → P.refl) , (λ h → P.refl)
    ; sym   = λ {x} {y} p →
      (λ x → P.sym (fst p x))
      , ( λ {x} {y} → {!!}
        )
    ; trans = λ {x} {y} {z} p q → (λ x → P.trans (fst p x) (fst q x))
                    , ( λ {u} {v} h →
                        {!!}
                      )
    }
  ; id  = {!!}
  ; _∘_ = {!!}
  ; ∘λ  = {!!}
  ; ∘ρ  = {!!}
  ; ∘α  = {!!}
  ; ∘∼  = {!!}
  }
-}

{-
DIA : ∀ {o m e} (C : Cat o m e) → Cat _ _ _
DIA C = record
  { Obj = ?
  ; _⟶_ = ?
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
-}

{-

What is the computational content in the act of "collecting"?

-}
