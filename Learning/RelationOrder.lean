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
def Join {α : Type} [Preorder α] (a b : α) : Type :=
  { c : α // a ≤ c ∧ b ≤ c ∧ ∀ (c' : α), (b ≤ c' ∧ a ≤ c') → c ≤ c'}

/-- Meet two elements in a preorder by finding their greatest lower bound. -/
def Meet {α : Type} [Preorder α] (a b : α) : Type :=
  { c : α // c ≤ a ∧ c ≤ b ∧ ∀ (c' : α), (c' ≤ a ∧ c' ≤ b) → c' ≤ c}

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
  cases a
  . exact congrArg false.or
  . exact congrFun rfl

@[simp]
theorem leLAnd (a b : Bool) : (a && b) ≤ a := by
  cases a
  . exact Bool.false_le _
  . exact congrFun rfl

@[simp]
theorem leRAnd (a b : Bool) : (a && b) ≤ b := by
  cases b
  . rw [Bool.and_false]
    trivial
  . exact congrFun rfl

theorem leFalse (a : Bool) : (a ≤ false) ↔ (a = false) := by
  exact ⟨Bool.eq_false_of_le_false, Bool.le_of_eq⟩

theorem trueLe (a : Bool) : (true ≤ a) ↔ (a = true) := by
  exact ⟨fun a => a rfl, fun a _ => a⟩

def joinBooleans (a b : Bool) : Join a b :=
  { val := decide (a || b)
  , property :=
      by
        simp only [Bool.or_eq_true, Bool.decide_or, Bool.decide_eq_true, leOrL, leOrR, and_imp,
          Bool.forall_bool, Bool.le_true, imp_self, and_true, true_and]
        intro hb ha
        have hb' := (leFalse b).mp hb
        have ha' := (leFalse a).mp ha
        rw [ha', hb']
        trivial
  }

def meetBooleans (a b : Bool) : Meet a b :=
  { val := a ∧ b
  , property :=
      by
        simp only [Bool.decide_and, Bool.decide_eq_true, leLAnd, leRAnd, and_imp, Bool.forall_bool,
          Bool.false_le, imp_self, true_and]
        intro ha hb
        have ha' := (trueLe a).mp ha
        have hb' := (trueLe b).mp hb
        rw [ha', hb']
        trivial
  }
