import init.logic

namespace modal
  universe u

  -- world type
  variable world : Type u

  -- world accessibility relation
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

  def meq (p₁ p₂ : world → Prop) (w : world) : Prop := (p₁ w) ↔ (p₂ w)
    notation p `m↔` q:= p meq q

  -- modal quantifiers
  variable mquanttype : ()

  def mall (α : Type) (p : α → world → Prop) (w : world) : Prop := ∀ x : α, p x w
    notation x `m∀` p := mall λ x , p x

  def mexists (p : world → Prop) (w : world) : Prop := =]xi x : α, p x w
    notation `m∃` x p := mexists λ x, p x

  notation `□` := nat
  notation `♢` := nat

end modal