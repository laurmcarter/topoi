
module Common.Graph where

open import Prelude as P
  hiding
    ( id
    ; _∘_
    ; [_]
    ; refl
    ; sym
    ; trans
    ; Graph
    )

open import Common.Setoid

infix 4 _⊆_
_⊆_ : ∀ {a p q} {A : Set a} (P : A → Set p) (Q : A → Set q) → Set (a ⊔ p ⊔ q)
P ⊆ Q = ∀ {x} → P x → Q x

record Graph {o m} (O : Set o) (M : (x y : O) → Set m) v e : Set (o ⊔ m ⊔ lsuc (v ⊔ e)) where
  field
    ₀ : O → Set v
    ₁ : {x y : O} (vx : ₀ x) (vy : ₀ y)
      → M x y
      → Set e

record GraphMor {o m v1 e1 v2 e2} {O : Set o} {M : (x y : O) → Set m}
  (G1 : Graph O M v1 e1) (G2 : Graph O M v2 e2)
  : Set (o ⊔ m ⊔ v1 ⊔ e1 ⊔ v2 ⊔ e2) where
  private
    module G1 = Graph G1
    module G2 = Graph G2
  field
    ₀ : G1.₀ ⊆ G2.₀
    ₁ : ∀ {x y} (vx : G1.₀ x) (vy : G1.₀ y)
      → G1.₁ vx vy ⊆ G2.₁ (₀ vx) (₀ vy)
    
record GraphEqv {o m v e} {O : Set o}
  {M : (x y : O) → Set m}
  {G1 G2 : Graph O M v e}
  (f g : GraphMor G1 G2) : Set {!!} where
  private
    module G1 = Graph G1
    module G2 = Graph G2
    module f  = GraphMor f
    module g  = GraphMor g
  field
    ₀ : ∀ x → G1.₀ x ≡ G2.₀ x
