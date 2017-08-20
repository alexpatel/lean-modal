namespace modal
  open classical

  universe u

  -- possible world type
  variable {world : Type u}

  -- accessibility relation type
  variable {r : world → world → Prop}

  -- modal proposition type, lifted over Prop
  -- a predicate saying whether a given proposition is true in a particular world
  def σ : Type u := world → Prop

  -- true, false
  def mtop := λ w : world, true
  def mbot := λ w : world, false

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
  constant r₁ : w₁ → w₁ → Prop
  constants p q : w₁ → Prop

  #check m¬ p
  #check p m∧ q
  #check p m→ q
  #check p m↔ q
  #check □ p
  #check ♢ p
  #check m∀ w, p w
  #check ∀ w : w₁, p w
  #check ∃ w, p w
  #check ∃ w : w₁, p w

  axiom r_reflex : ∀ w, r₁ w w
  axiom r_trans : ∀ x y z : w₁, (r₁ x y) → (r₁ y z) → (r₁ x z)
  axiom r_symm : ∀ x y : w₁, (r₁ x y) → (r₁ y x)

  #check r_reflex
  #check r_trans
  #check r_trans
end test

namespace exmp
  open modal
  constants world : Type
  constant M : world → Prop
  constant r : world → world → Prop
  constants p q : world → Prop
  variables x₁ x₂ x₃ x₄ x₅ x₆ : world

  axiom kripe_example :
      (r x₁ x₂) ∧ (r x₁ x₃) ∧ (r x₂ x₃) ∧ (r x₃ x₂)
      ∧ (r x₂ x₃) ∧ (r x₃ x₃) ∧ (r x₂ x₂)
      ∧ (r x₃ x₃) ∧ (r x₅ x₄) ∧ (r x₅ x₆)
      ∧ ¬ (p x₁) ∧ (q x₁)
      ∧ (p x₂) ∧ (q x₂)
      ∧ (p x₃) ∧ ¬ (q x₃)
      ∧ ¬ (p x₄) ∧ (q x₄) 
      ∧ ¬ (p x₅) ∧ ¬ (q x₅) 
      ∧ (p x₆) ∧ ¬ (q x₆)

  #check mdia
  #check (mdia p) x₁ 
  #check (♢ p) x₁ 
  theorem prop_1 : p x₁ := sorry
  theorem forall_1 : ∀ w : world, p w := sorry
  theorem exists_1 : ∃ w : world, p w := sorry

  -- test diamond
  theorem dia_1 : ∃ w₂ : world, (r x₁ w₂) ∧  (p w₂)
  theorem dia_2 : (♢ p) x₁ := sorry  -- why does this not work...

  -- test box
  theorem box_1 : ∀ w₂ : world, (r x₁ w₂) → (p w₂)
  theorem box_1 : (□ p) x₁ := sorry  -- why does this not work...
end exmp