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

universe u₁
class Preorder (α : Type u₁) extends LE α where
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
