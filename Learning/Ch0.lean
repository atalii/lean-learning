-- Some category theory via Algebra Chapter 0.

def left_inverse (f : α → β) (g : β → α) : Prop :=
  g ∘ f = id

def right_inverse (f : α → β) (g : β → α) : Prop :=
  f ∘ g = id

def injective (f : α → β) : Prop :=
  ∀ ⦃a b : α⦄, (f a = f b) → (a = b)

def surjective (f : α → β) : Prop :=
  ∀ b, ∃ (a : α), f a = b

def bijective (f : α → β) : Prop := injective f ∧ surjective f

def Set α := α → Prop

@[ext]
theorem Set.ext {a b : Set α} (h : ∀ x, a x ↔ b x) : a = b := funext (fun x ↦ propext (h x))
attribute [ext] Set.ext

def graph {α β : Type u} (f : α → β) : Set (α × β) := fun (a, b) => f a = b

def set_is_graph (g : Set (α × β)) : Prop :=
  (∀ a, ∀ b, ∀ b', g (a, b) ∧ g (a, b') → b = b') ∧ (∀ b, ∃ a, g (a, b))

def image (f : α → β) : Set β := fun b => (∃ (a : α), f a = b)

def inverted (A : Set (α × β)) : Set (β × α) := fun (b, a) => A (a, b)

def refl (R : Set (α × α)) : Prop := ∀ a, R (a, a)
def symm (R : Set (α × α)) : Prop := ∀ a a', R (a , a') → R (a', a)
def trans (R : Set (α × α)) : Prop := ∀ a a' a'', R (a, a') ∧ R (a', a'') = R (a, a'')

def equiv (R : Set (α × α)) : Prop := refl R ∧ symm R ∧ trans R

theorem alternate_surjection_def (f : α → β) : surjective f ↔ image f = fun _ => True := by
  rw [Set.ext_iff]
  constructor
  . intro hf x
    exact iff_true_intro (hf x)
  . intro hi x
    let hi' := (hi x).mpr
    exact hi' trivial

theorem left_injective [hα : Nonempty α] (f : α → β) : (∃ g, left_inverse f g) ↔ injective f := by
  constructor
  . intro ⟨g,hgi⟩ a b hfafb
    suffices (g ∘ f) a = (g ∘ f) b by rwa [hgi] at this
    rw [Function.comp_apply, Function.comp_apply, hfafb]
  . intro hif
    classical
    exists (fun b ↦ if h : ∃ (a : α), b = f a then h.choose else Classical.choice hα)
    unfold left_inverse
    rw [@Function.comp_def]
    rw [@funext_iff]
    intro a
    split
    . rename_i hea
      have hhea := hea.choose_spec
      have hc := hea.choose
      obtain ⟨x, hx⟩ := hea
      exact hif (id (Eq.symm hhea))
    . let hc : ∃ a', f a = f a' := Exists.intro a rfl
      contradiction

def composition_is_associative (f : α → β) (g : β → γ) (h : γ → δ) :
    (h ∘ g) ∘ f = h ∘ (g ∘ f) := by
  rw [@Function.comp_def, @Function.comp_def, @Function.comp_def, @Function.comp_def]
