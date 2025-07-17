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
  fun (a, b) => ∃ (f : a.target → b.target), surjective f

theorem surjections_compose
  (f : α → β) (hf : surjective f) (g : β → γ) (hg : surjective g) :
    surjective (g ∘ f) := by
  intro c
  let b := (hg c).choose
  let hb := (hg c).choose_spec
  let a := (hf b).choose
  let ha := (hf b).choose_spec
  refine ⟨a, ?_⟩
  rw [Function.comp_def]
  simp only
  rw [ha, hb]

theorem partitionPreorderIsAPreorder { α : Type u} :
    Preorder (PartitionPreorder α) := by
  constructor
  . intro
    unfold PartitionPreorder
    refine ⟨id, ?_⟩
    exact exists_apply_eq_apply id
  . intro p₁ p₂ p₃
    intro hps
    obtain ⟨hp₁p₂, hp₂p₃⟩ := hps
    let hfp₁p₂ := Classical.indefiniteDescription surjective hp₁p₂
    let hfp₂p₃ := Classical.indefiniteDescription surjective hp₂p₃
    refine ⟨hfp₂p₃.val ∘ hfp₁p₂.val, ?_⟩
    refine surjections_compose
      hfp₁p₂.val hfp₁p₂.property
      hfp₂p₃.val hfp₂p₃.property
