namespace modal
  open classical

  universe u

  -- possible world type
  variable {world : Type u}

  -- accessibility relation type
  variable {r : world → world → Prop}

  -- modal proposition type
  def σ : Type u := world → Prop

  -- modal connectives
  def mnot (p : σ) (w : world) : Prop := ¬ (p w)
  def mand (p₁ p₂ : σ) (w : world) : Prop := p₁ w ∧ p₂ w
  def mor (p₁ p₂ : σ) (w : world) : Prop := p₁ w ∨ p₂ w
  def mimplies (p₁ p₂ : σ) (w : world) : Prop := (p₁ w) → (p₂ w)
  def mequiv (p₁ p₂ : σ) (w : world) : Prop := (p₁ w) ↔ (p₂ w)

  -- modal quantifiers
  def mall {α : Type u} (p: α → σ) (w : world) : Prop := ∀ x : α, p x w
  def mexists {α : Type u} (p: α → σ) (w : world) : Prop := ∃ x : α, p x w

  -- modal operators
  def mbox (p : σ) := λ w₁ : world, ∀ w₂ : world, (r w₁ w₂) → (p w₂)
  def mdia (p : σ) := λ w₁ : world, ∃ w₂ : world, (r w₁ w₂) ∧  (p w₂)

  -- validity
  def mvalid (p : σ) := ∀ w : world, p w

  -- notation mirroring standard operators/quantifiers
  notation `m¬` p := mnot p
  infix `m∧`:50 := mand
  infix `m∨`:50 := mor
  infix `m→`:50 := mimplies
  infix `m↔`:50 := mequiv
  notation `m∀` x, p := mall (λ x, p)
  notation `m∃` x, p := mexists (λ x, p)
  notation `□` p := mbox p
  notation `♢` p := mdia p
  notation `[` p `]` := mvalid p

  #check σ
  #check mnot
  #check mand
  #check mor
  #check mimplies
  #check mequiv
  #check mall
  #check mexists
  #check mbox
  #check mdia
  #check mvalid
end modal

namespace test
  open modal
  #check mnot
  #check σ

  universe v
  constants w₁ α : Type v
  constant r₁ : w₁ → w₁ → w₁
  constants p q : w₁ → Prop

  #check m¬ p
  #check p m∧ q
  #check p m→ q
  #check p m↔ q
  #check □  p
  #check ♢ p
  #check ∀ w, p w
  #check ∀ w : w₁, p w
  #check ∃ w, p w
  #check ∃ w : w₁, p w
end test
