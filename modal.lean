import init.logic

namespace modal
  universe u

  -- type of worlds
  constant world : Type u

  -- accessibility relation
  constant r : world → world → Prop

  -- type of modal propositions, lifted over Prop
  definition σ : Type := world → Prop

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
  notation p `m∧` q:= p mand q
  notation p `m∨` q:= p mor q
  notation p `m→` q:= p mimplies q
  notation p `m↔` q:= p mequiv q
  notation `m∀` x, p := mall (λ x, p)
  notation `m∃` x, p := mexists (λ x, p)
  notation `m∃` x, p := mexists (λ x, p)
  notation `□` p := mbox p
  notation `♢` p := mdia p
  notation `[` p `]` := mvalid p

  variables p q : σ
  #check mnot p
  #check mand p q
  #check mor p q
  #check mimplies p q
  #check mequiv p q
  #check □p
  #check ♢p

end modal
