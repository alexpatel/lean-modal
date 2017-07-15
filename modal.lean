import init.logic

namespace modal
  universe u
  variable world : Type u
  variable rel : world → world → Prop

  -- modal connectives
  def mnot (p : world → Prop) (w : world) : Prop := ¬ (p w)
    notation `m¬` p := mnot p

  def mand (p₁ p₂ : world → Prop) (w : world) : Prop := p₁ w ∧ p₂ w
    notation p `m∧` q:= p mand q

  def mor (p₁ p₂ : world → Prop) (w : world) : Prop := p₁ w ∨ p₂ w
    notation p `m∨` q:= p mor q

  def mimplies (p₁ p₂ : world → Prop) (w : world) : Prop := (p₁ w) → (p₂ w)
    notation p `m→` q:= p mimplies q

  def mequiv (p₁ p₂ : world → Prop) (w : world) : Prop := (p₁ w) ↔ (p₂ w)
    notation p `m↔` q:= p mequiv q

  def meq (p₁ p₂ : world → Prop) (w : world) : Prop := (p₁ w) = (p₂ w)
    notation p `m=` q:= p meq q

  -- modal quantifiers
  def mall {α : Type u} (p: α → world → Prop) (w : world) : Prop := ∀ x : α, p x w
    notation `m∀` x, p := mall p x

  def mexists {α : Type u} (p: α → world → Prop) (w : world) : Prop := ∃ x : α, p x w
    notation `m∃` x, p := mexists p x

  notation `□` := nat
  notation `♢` := nat

end modal