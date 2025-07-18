-- Prove that we can order partitions.

universe u
def Set (α : Type u) := α → Prop

instance { α : Type u }: Membership α (Set α) := ⟨id⟩

def Relation (α β) := Set (α × β)
instance {α β : Type u}: Membership (α × β) (Relation α β) := ⟨id⟩

def surjective {α β : Type u} (f : α → β) : Prop := ∀ b, ∃ a, f a = b

class Surjection (α β : Type u) where
  f : α → β
  hf : surjective f

class Partition (α : Type u) where
  target : β
  f : Surjection α β

instance {α : Type u} : LE (Partition α) where
  le := fun a b => ∃ (f : a.target → b.target), (f ∘ a.f.f) = b.f.f

class Preorder.{u₁} (α : Type u₁) extends LE α where
  refl : ∀ a : α, a ≤ a
  trns : ∀ a b c : α, a ≤ b ∧ b ≤ c → a ≤ c

instance {α : Type u} : Preorder (Partition α) where
  refl := by
    intro
    -- The function to map two identical partitions is id.
    refine ⟨id, ?_⟩
    rfl

  trns := by
    intro p₁ p₂ p₃
    intro hps
    obtain ⟨hp₁p₂, hp₂p₃⟩ := hps
    obtain ⟨fp₁p₂, hfp₁p₂⟩ := hp₁p₂
    obtain ⟨fp₂p₃, hfp₂p₃⟩ := hp₂p₃
    refine ⟨fp₂p₃ ∘ fp₁p₂, ?_⟩
    rw [← hfp₂p₃, ← hfp₁p₂]
    rfl

/-- Join two elements in a preorder by finding their least upper bound. -/
class PreorderJoin (α : Type u) extends Preorder α where
  join : α → α → α
  h : ∀ a b c, join a b = c →
    a ≤ c ∧ b ≤ c ∧ ∀ (c' : α), (b ≤ c' ∧ a ≤ c') → c ≤ c'

/-- Meet two elements in a preorder by finding their greatest lower bound. -/
class PreorderMeet (α : Type u) extends Preorder α where
  meet : α → α → α
  h : ∀ a b c, meet a b = c →
    c ≤ a ∧ c ≤ b ∧ ∀ (c' : α), (c' ≤ a ∧ c' ≤ b) → c' ≤ c

instance : Preorder Bool where
  refl := fun a => congrArg id -- witchcraft

  trns := by
    intro a b c ⟨hab, hbc⟩
    exact fun a => hbc (hab a)


@[simp]
theorem leOrL (a b : Bool) : a ≤ (a || b) := by
  cases a
  . exact Bool.false_le _
  . exact congrFun rfl

@[simp]
theorem leOrR (a b : Bool) : b ≤ (a || b) := by
  cases b
  . exact leOrL false _
  . refine Bool.le_of_eq (Bool.or_true a).symm

theorem leFalse (a : Bool) : (a ≤ false) ↔ (a = false) := by
  exact ⟨Bool.eq_false_of_le_false, Bool.le_of_eq⟩

theorem trueLe (a : Bool) : (true ≤ a) ↔ (a = true) := by
  exact ⟨fun a => a rfl, fun a _ => a⟩

@[simp]
theorem leLAnd (a b : Bool) : (a && b) ≤ a := by
  cases a
  . exact Bool.false_le _
  . exact congrFun rfl

@[simp]
theorem leRAnd (a b : Bool) : (a && b) ≤ b := by
  cases b
  . rw [Bool.and_false, leFalse]
  . exact congrFun rfl

instance : PreorderJoin Bool where
  join := fun a b => decide (a || b)
  h := by simp only [Bool.or_eq_true, Bool.decide_or, Bool.decide_eq_true, and_imp, Bool.forall_bool,
      Bool.le_true, imp_self, and_true, forall_eq', leOrL, leOrR, true_and, Bool.le_refl,
      Bool.or_false, Bool.or_true, forall_const, implies_true, and_self]

instance : PreorderMeet Bool where
  meet := fun a b => decide (a && b)
  h := by simp only [Bool.and_eq_true, Bool.decide_and, Bool.decide_eq_true, and_imp, Bool.forall_bool,
      Bool.false_le, imp_self, true_and, forall_eq', leLAnd, leRAnd, Bool.and_false, implies_true,
      Bool.le_refl, Bool.and_true, forall_const, and_self]
