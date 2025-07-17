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

def Reflexive {α : Type (u + 1)} (r : Relation α α) : Prop := ∀ a, (a, a) ∈ r
def Transitive {α : Type (u + 1)} (r : Relation α α) : Prop := ∀ a b c, r (a, b) ∧ r (b, c) → r (a, c)

def Preorder {α : Type (u + 1)} (r : Relation α α) : Prop := Reflexive r ∧ Transitive r

def PartitionPreorder (α : Type u) : Relation (Partition α) (Partition α) :=
  fun (a, b) => ∃ (f : a.target → b.target), (f ∘ a.f.f) = b.f.f

theorem partitionPreorderIsAPreorder { α : Type u} :
    Preorder (PartitionPreorder α) := by
  constructor
  . intro
    unfold PartitionPreorder
    refine ⟨id, ?_⟩
    rfl
  . intro p₁ p₂ p₃
    intro hps
    obtain ⟨hp₁p₂, hp₂p₃⟩ := hps
    obtain ⟨fp₁p₂, hfp₁p₂⟩ := hp₁p₂
    obtain ⟨fp₂p₃, hfp₂p₃⟩ := hp₂p₃
    refine ⟨fp₂p₃ ∘ fp₁p₂, ?_⟩
    rw [← hfp₂p₃, ← hfp₁p₂]
    rfl
