
module Test where

open import Prelude using (lzero;lsuc;_⊔_)
open import Prelude.Equality

transport-syntax : ∀ {a b} {A : Set a} (B : A → Set b)
                 → {x y : A} (p : x ≡ y)
                 → B x → B y
transport-syntax = transport
infixr 5 transport-syntax
syntax transport-syntax (λ x → B) p b = [ x ∣ B ] p · b

congᵈ : ∀ {a b} {A : Set a} {B : A → Set b}
      → (f : ∀ x → B x)
      → {x y : A} (p : x ≡ y)
      → [ x ∣ B x ] p · f x ≡ f y
congᵈ f refl = refl
infixr 10 congᵈ

syntax congᵈ f p = f $$≡ p

congᵈ₂ : ∀ {a b c} {A : Set a} {B : A → Set b} {C : ∀ x → B x → Set c}
       → (f : (x : A) (y : B x) → C x y)
       → {x y : A} (p : x ≡ y)
       → {u : B x} {v : B y} (q : [ x ∣ B x ] p · u ≡ v)
       → [ u ∣ C y u ] q · ([ x ∣ ((u : B x) → C x u) ] p · f x) ([ x ∣ B x ] p · u) ≡ f y v
congᵈ₂ f refl refl = refl

record _×_ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  field
    ₁ : A
    ₂ : B ₁
open _×_ public
infixr 0 _×_

×-syntax : ∀ {a b} (A : Set a) (B : A → Set b) → Set (a ⊔ b)
×-syntax = _×_
syntax ×-syntax A (λ x → B) = [ x ∈ A ]× B

/-syntax : ∀ {a b} (A : Set a) (B : A → Set b) → Set (a ⊔ b)
/-syntax A B = (x : A) → B x
syntax /-syntax A (λ x → B) = [ x ∈ A ]→ B
infixr 0 ×-syntax /-syntax

data _+_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  ₗ_ : A → A + B
  ᵣ_ : B → A + B

data ⊥ : Set where

data ⊤ : Set where
  ★ : ⊤

record _-_ {a b} (A : Set a) (B : Set b): Set (a ⊔ b) where
  field
    -₁ : A → (B → ⊥) → ⊥
    -₂ : B → (A → ⊥) → ⊥
open _-_ public
infixr 1 _+_ _-_

data U : Set
El : U → Set

data U where
  𝟘 𝟙 : U
  _⊕_ _⊝_ : (A B : U) → U
  ⊗ ⊘ : (A : U) (B : El A → U) → U

syntax ⊗ A (λ x → B) = [ x ∈ A ]⊗ B
syntax ⊘ A (λ x → B) = [ x ∈ A ]⊘ B

infixr 1 _⊕_ _⊝_
infixr 0 ⊗ ⊘

El 𝟘       = ⊥
El 𝟙       = ⊤
El (A ⊕ B) = El A + El B
El (A ⊝ B) = El A - El B
El (⊗ A B) = [ x ∈ El A ]× El (B x)
El (⊘ A B) = [ x ∈ El A ]→ El (B x)

data Ctx : Set
Env : Ctx → Set

Type : Ctx → Set
Type Γ = (γ : Env Γ) → U
Term : (Γ : Ctx) (A : Type Γ) → Set
Term Γ A = (γ : Env Γ) → El (A γ)

infix 1 _⇒_ _⊢U _⊢_
infixl 20 _[_]

data _⇒_ : (Γ Δ : Ctx) → Set
data _⊢U : (Γ : Ctx) → Set
data _⊢_ : (Γ : Ctx) (A : Γ ⊢U) → Set

data Ctx where
  ∙   : Ctx
  _,_ : (Γ : Ctx)
      → (A : Γ ⊢U)
      → Ctx
infixl 3 _,_

_[_] : ∀ {Γ Δ} (A : Γ ⊢U) (σ : Δ ⇒ Γ) → Δ ⊢U
_⟦_⟧ : ∀ {Γ Δ A} (a : Γ ⊢ A) (σ : Δ ⇒ Γ) → Δ ⊢ A [ σ ]
type : ∀ {Γ} (A : Γ ⊢U) → Type Γ
term : ∀ {Γ A} (a : Γ ⊢ A) → Term Γ (type A)

Env ∙       = ⊤
Env (Γ , A) = [ γ ∈ Env Γ ]× El (type A γ)

infix 1 _↦_
_↦_ : ∀ {Γ Δ} (σ : Δ ⇒ Γ) (f : Γ ⊢U → Δ ⊢U) → Set
σ ↦ f = ∀ A → A [ σ ] ≡ f A
↦-syntax : ∀ {Γ Δ} (σ : Δ ⇒ Γ) (f : Γ ⊢U → Δ ⊢U) → Set
↦-syntax = _↦_
infixr 1 ↦-syntax
syntax ↦-syntax σ (λ A → B) = σ ≈[ A ↦ B ]

data _⇒_ where
  id : ∀ {Γ}
     → Γ ⇒ Γ
  ∙  : ∀ {Γ}
     → Γ ⇒ ∙
  𝕡  : ∀ {Γ A}
     → Γ , A ⇒ Γ
  𝕤  : ∀ {Γ Δ A}
     → (σ : Δ ⇒ Γ)
     → Δ , A [ σ ] ⇒ Γ , A
  _,_ : ∀ {Γ Δ A}
      → (σ : Δ ⇒ Γ)
      → (a : Δ ⊢ A [ σ ])
      → Δ ⇒ Γ , A
id[_] : ∀ Γ → Γ ⇒ Γ
id[ _ ] = id

_∘_ : ∀ {Γ Δ Φ}
    → (σ : Δ ⇒ Γ)
    → (τ : Φ ⇒ Δ)
    → Φ ⇒ Γ
id      ∘ τ = τ
∙       ∘ τ = ∙
𝕡       ∘ τ = {!!}
𝕤 σ     ∘ τ = {!!}
_∘_ {Γ , A} {Δ} {Φ} (σ , a) τ = (σ ∘ τ) , ([ A ∣ Φ ⊢ A ] {!!} · {!!})

data _⊢U where
  𝟘 𝟙     : ∀ {Γ} → Γ ⊢U
  𝕤       : ∀ {Γ B}
          → (A : Γ ⊢U)
          → Γ , B ⊢U
  _⊕_ _⊝_ : ∀ {Γ} (A B : Γ ⊢U) → Γ ⊢U
  ⊗ ⊘     : ∀ {Γ} (A : Γ ⊢U) (B : Γ , A ⊢U)
          → Γ ⊢U

data _⊢_ where
  𝕫 : ∀ {Γ A}
    → Γ , A ⊢ A [ {!!} ]
  𝕤 : ∀ {Γ A B}
    → (a : Γ ⊢ B)
    → Γ , A ⊢ B [ {!!} ]

𝟘       [ σ ] = 𝟘
𝟙       [ σ ] = 𝟙
𝕤 A     [ id    ] = 𝕤 A
𝕤 A     [ 𝕡     ] = 𝕤 (𝕤 A)
𝕤 A     [ 𝕤 σ   ] = 𝕤 (A [ σ ])
𝕤 A     [ σ , a ] = A [ σ ]
(A ⊕ B) [ σ ] = A [ σ ] ⊕ B [ σ ]
(A ⊝ B) [ σ ] = A [ σ ] ⊝ B [ σ ]
⊗ A B   [ σ ] = ⊗ (A [ σ ]) (B [ 𝕤 σ ])
⊘ A B   [ σ ] = ⊘ (A [ σ ]) (B [ 𝕤 σ ])

[id] : ∀ {Γ} → id[ Γ ] ≈[ A ↦ A ]
[id] 𝟘       = refl
[id] 𝟙       = refl
[id] (𝕤 A)   = refl
[id] (A ⊕ B) = cong₂ _⊕_ ([id] A) ([id] B)
[id] (A ⊝ B) = cong₂ _⊝_ ([id] A) ([id] B)
[id] {Γ} (⊗ A B) = r
  where
  r : _⊢U.⊗ (A [ id[ Γ ] ]) (B [ 𝕤 id[ Γ ] ]) ≡ ⊗ A B
  r = congᵈ₂ {A = {!!}} {B = {!!}} {C = {!!}} ⊗ p q
    where
    p : A [ id[ Γ ] ] ≡ A
    p = [id] A
    q : [ A ∣ Γ , A ⊢U ] ([id] A) · (B [ 𝕤 id[ Γ ] ]) ≡ B
    q = {!B!}
[id] (⊘ A B) = {!!}

[∘] : ∀ {Γ Δ Φ} (σ : Δ ⇒ Γ) (τ : Φ ⇒ Δ) → σ ∘ τ ≈[ A ↦ A [ σ ] [ τ ] ]
[∘] id      τ A = {![id] A!}
[∘] ∙       τ A = {!!}
[∘] 𝕡       τ A = {!!}
[∘] (𝕤 σ)   τ A = {!!}
[∘] (σ , a) τ A = {!!}

a ⟦ σ ⟧ = {!!}

type A γ = {!!}

term a γ = {!!}
