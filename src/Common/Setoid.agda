
module Common.Setoid where

open import Prelude as P
  hiding
    ( refl
    ; sym
    ; trans
    ; transport₂
    )

abs-syntax : ∀ {a b} {A : Set a} {B : A → Set b}
           → (∀ x → B x) → ∀ x → B x
abs-syntax f = f
infixl 2 abs-syntax
syntax abs-syntax (λ x → e) = x ∣ e
{-# DISPLAY abs-syntax f = f #-}

record Setoid {a} b (A : Set a) : Set (a ⊔ lsuc b) where
  infix 1 _∼_
  field
    _∼_ : A → A → Set b
    refl : ∀ {x} → x ∼ x
    sym  : ∀ {x y} (p : x ∼ y) → y ∼ x
    trans  : ∀ {x y z} (p : x ∼ y) (q : y ∼ z) → x ∼ z
  infixr 0 _▸_
  refl[_] : ∀ x → x ∼ x
  refl[_] _ = refl
  _▸_ = trans

  record Unique {p} (P : A → Set p) (x : A) : Set (a ⊔ b ⊔ p) where
    constructor _!_
    field
      prop   : P x
      unique : {y : A} → P y → y ∼ x
  open Unique public

UnitSetoid : ∀ {a} (A : Set a) → Setoid _ A
UnitSetoid A = record
  { _∼_   = λ _ _ → ⊤
  ; refl  = tt
  ; sym   = λ _ → tt
  ; trans = λ _ _ → tt
  }

DiscreteSetoid : ∀ {a} (A : Set a) → Setoid _ A
DiscreteSetoid A = record
  { _∼_   = _≡_
  ; refl  = P.refl
  ; sym   = P.sym
  ; trans = P.trans
  }

{-
Natl : ∀ {a b r} {A : Set a} (B : A → Set b)
     → (R : ∀ x → B x → B x → Set r)
     → (f g : ∀ x → B x)
     → Set (a ⊔ r)
Natl B R f g = ∀ x → R x (f x) (g x)
infix 4 Natl
syntax Natl B R f g = f ∼[ B ∣ R ] g

Natl′ : ∀ {a b r} {A : Set a} (B : Set b)
      → (R : B → B → Set r)
      → (f g : A → B)
      → Set (a ⊔ r)
Natl′ B R f g = ∀ x → R (f x) (g x)
infix 4 Natl′
syntax Natl′ B R f g = f ∼[ B ∣ R ]′ g
-}

-- foo : ∀ {a b c} {A : Set a} (B : A → Set b) (C : ∀ x → B x → Set c)
--     → Set {!!}
-- foo B C = Natl (λ x → C x {!!}) (λ x → {!Natl!}) {!!} {!!}

{-
record [_]IndexedSetoid {a b c} {A : Set a} (A-setoid : Setoid b A) d (C : A → Set c) : Set {!!} where
  private
    module A = Setoid A-setoid
  infix  1  _∼_
  infixr 20 _↑_
  field
    _∼_   : {x : A} (u v : C x) → Set d
    refl  : {x : A} {u : C x} → u ∼ u
    sym   : {x : A} {u v : C x} → u ∼ v → v ∼ u
    trans : {x : A} {u v w : C x} → u ∼ v → v ∼ w → u ∼ w
    _↑_   : {x y : A} (p : x A.∼ y)
          → (u : C x) → C y
    ↑refl : 

Σˢ : ∀ {a b c d} {A : Set a} {B : A → Set b}
   → (𝓐 : Setoid c A)
   → (𝓑 : (x : A) → Setoid d (B x))
   → (_↑_ : {x y : A} (p : Setoid._∼_ 𝓐 x y) → B x → B y)
   -- → (↑refl : {x : A} {u : B x} → A.refl[ x ] ↑ u 
   → Setoid _ (Σ A B)
Σˢ 𝓐 𝓑 _↑_ = record
  { _∼_   = λ a b → Σ (fst a A.∼ fst b) λ p → p ↑ snd a B.∼ snd b
  ; refl  = A.refl , {!!}
  ; sym   = {!!}
  ; trans = {!!}
  }
  where
  module A     = Setoid 𝓐
  module B {x} = Setoid (𝓑 x)
-}

transport-syntax : ∀ {a b} {A : Set a} (B : A → Set b)
                 → {x : A} (y : A) (p : x ≡ y)
                 → B x → B y
transport-syntax B y = transport B
infixl 5 transport-syntax
syntax transport-syntax (λ x → B) y p b = p · b ∈ B [ y / x ]
{-# DISPLAY transport-syntax B _ p b = transport B p b #-}

transport-syntax₂ : ∀ {a b} {A : Set a} {B : A → Set b}
                  → (x y : A) (p : x ≡ y)
                  → B x → B y
transport-syntax₂ x .x P.refl z = z
infixr 5 transport-syntax₂
syntax transport-syntax₂ x y p z = p · z [ y / x ]

ind≡ : ∀ {a c} {A : Set a} (C : (x y : A) → x ≡ y → Set c)
     → {x y : A}
     → (∀ ∙ → C ∙ ∙ P.refl)
     → (p : x ≡ y)
     → C x y p
ind≡ C c P.refl = c _
infixl 1 ind≡
syntax ind≡ C (λ x → e) = x ←[ C ] e

bind≡ : ∀ {a c} {A : Set a} (C : (x y : A) → x ≡ y → Set c)
      → {x y : A}
      → (p : x ≡ y)
      → (∀ x → C x x P.refl)
      → C x y p
bind≡ C P.refl c = c _
infixl 1 bind≡
syntax bind≡ C p (λ x → e) = x ← p [ C ] e

transport₂ : ∀ {a b c} {A : Set a} {B : A → Set b} (C : ∀ x → B x → Set c)
           → {x₁ x₂ : A} (p : x₁ ≡ x₂)
           → {y₁ : B x₁} {y₂ : B x₂} (q : p · y₁ ∈ B x₁ [ x₂ / x₁ ] ≡ y₂)
           → C x₁ y₁ → C x₂ y₂
transport₂ {c = c} {B = B} C =
  x ←[ x₁ ∣ x₂ ∣ p ∣
     ( {y₁ : B x₁} {y₂ : B x₂}
     → (q : p · y₁ ∈ B x₁ [ x₂ / x₁ ] ≡ y₂)
     → C x₁ y₁ → C x₂ y₂
     )]
  y ←[ y₁ ∣ y₂ ∣ q ∣ (C x y₁ → C x y₂) ]
  z  ∣ z

ind≡₂ : ∀ {a b c} {A : Set a} (B : A → Set b)
      → (C : (x y : A) (u : B x) (v : B y) (p : x ≡ y) (q : p · u ∈ B x [ y / x ] ≡ v) → Set c)
      → (∀ x (y : B x) → C x x y y P.refl P.refl)
      → {x y : A} (p : x ≡ y)
      → {u : B x} {v : B y} (q : p · u ∈ B x [ y / x ] ≡ v)
      → C x y u v p q
ind≡₂ B C c =
  x′ ←[ x ∣ y ∣ p ∣
     ( {u : B x} {v : B y}
     → (q : p · u ∈ B x [ y / x ] ≡ v)
     → C x y u v p q
     )]
  y′ ←[ u ∣ v ∣ q ∣ C x′ x′ u v P.refl q ]
  c x′ y′

ind≡₃ : ∀ {a b c d} {A : Set a}
      → (B : A → Set b) (C : ∀ x → B x → Set c)
      → (D : (x y : A) (p : x ≡ y)
           → (u : B x) (v : B y) (q : p · u ∈ B x [ y / x ] ≡ v)
           → (s : C x u) (t : C y v) (r : transport₂ C p q s ≡ t)
           → Set d)
      → ((x : A) (y : B x) (z : C x y) → D x x P.refl y y P.refl z z P.refl)
      → {x y : A} (p : x ≡ y)
      → {u : B x} {v : B y}   (q : p · u ∈ B x [ y / x ] ≡ v)
      → {s : C x u} {t : C y v} (r : transport₂ C p q s ≡ t)
      → D x y p u v q s t r
ind≡₃ B C D d =
  x ←[ x ∣ y ∣ p ∣
     ( {u : B x} {v : B y}
     → (q : p · u ∈ B x [ y / x ] ≡ v)
     → {s : C x u} {t : C y v} (r : transport₂ C p q s ≡ t)
     → D x y p u v q s t r
     )]
  u ←[ u ∣ v ∣ q ∣
     ( {s : C x u} {t : C x v}
     → (r : transport₂ C P.refl q s ≡ t)
     → D x x P.refl u v q s t r
     )]
  s ←[ s ∣ t ∣ r ∣ D x x P.refl u u P.refl s t r ]
  d x u s

transport-const : ∀ {a b} {A : Set a} {B : Set b} {z : B}
                → {x y : A} (p : x ≡ y)
                → transport (λ _ → B) p z ≡ z
transport-const {B = B} {z} =
  x ←[ _ ∣ _ ∣ p ∣ transport (λ _ → B) p z ≡ z ]
  P.refl

transport-sym : ∀ {a b} {A : Set a} (B : A → Set b)
              → {x y : A} (p : x ≡ y)
              → {u : B y} {v : B x} (q : transport B p v ≡ u)
              → transport B (P.sym p) u ≡ v
transport-sym B =
  x ←[ x ∣ y ∣ p ∣
     ( {u : B y} {v : B x} (q : transport B p v ≡ u)
     → transport B (P.sym p) u ≡ v
     )]
  q  ∣ P.sym q

transport-trans : ∀ {a b} {A : Set a} (B : A → Set b)
                → {x y : A} (p : x ≡ y)
                → {z : A} (q : y ≡ z)
                → {u : B x} {w : B z} (r : transport B q (transport B p u) ≡ w)
                → transport B (P.trans p q) u ≡ w
transport-trans {A = A} B =
  x ←[ x ∣ y ∣ p ∣
     ( {z : A} (q : y ≡ z)
     → {u : B x} {w : B z} (r : transport B q (transport B p u) ≡ w)
     → transport B (P.trans p q) u ≡ w
     )]
  x ←[ x ∣ z ∣ q ∣
     ( {u : B x} {w : B z} (r : transport B q u ≡ w)
     → transport B q u ≡ w
     )]
  r  ∣ r
