notation "ℕ" => Nat

universe u
def Set (α : Type u) := α → Prop
variable {α : Type u}

def union (lhs rhs : Set α) : Set α :=
  fun a => lhs a ∨ rhs a

def intersect (lhs rhs : Set α) : Set α :=
  fun a => lhs a ∧ rhs a

def complement (s : Set α) : Set α := (¬s ·)

def mem (a : α) (s : Set α) : Prop := s a

def empty : Set α := fun _ => False
notation "∅" => empty

def full : Set α := fun _ => True

infix:60 " ∪ " => union
infix:60 " ∩ " => intersect
postfix:100 "ᶜ" => complement

-- wtf??
instance : Membership α (Set α) := ⟨mem⟩

def subset (s t : Set α) : Prop := ∀ x ∈ s, x ∈ t
infix:60 " ⊆ " => subset

theorem setext (s t : Set α) (hst : ∀ x, x ∈ s ↔ x ∈ t) : s = t := by
  funext x
  rw [eq_iff_iff]
  exact hst x

theorem in_is_mem {a : α} {s : Set α } : (a ∈ s) = s a := by rfl

theorem union_membership (a : α) (s t : Set α) :
  (a ∈ s ∪ t) = (a ∈ s ∨ a ∈ t) := by
  unfold union
  repeat rw [in_is_mem]

theorem intersection_membership (a : α) (s t : Set α) :
  (a ∈ s ∩ t) = (a ∈ s ∧ a ∈ t) := by
  unfold intersect
  repeat rw [in_is_mem]

@[simp]
theorem reductio {a : α} (hae : a ∈ (∅ : Set α)) : False := by
  rw [in_is_mem] at hae
  exact hae

@[simp]
theorem union_idempotency (s : Set α) : s ∪ s = s := by
  funext x
  exact or_self _

@[simp]
theorem intersection_idempotency (s : Set α) : s ∩ s = s := by
  unfold intersect
  funext x
  rw [and_self]

theorem union_commutativity (lhs rhs : Set α) :
    lhs ∪ rhs = rhs ∪ lhs := by
  unfold union
  funext x
  exact propext Or.comm

theorem intersection_commutativity (lhs rhs : Set α) :
    lhs ∩ rhs = rhs ∩ lhs := by
  unfold intersect
  funext x
  exact propext And.comm

theorem union_associativity (s t u : Set α) :
    (s ∪ t) ∪ u = s ∪ (t ∪ u) := by
   unfold union
   funext x
   exact propext or_assoc

theorem intersect_associativity (s t u : Set α) :
    (s ∩ t) ∩ u = s ∩ (t ∩ u) := by
  unfold intersect
  funext x
  exact propext and_assoc

@[simp]
theorem and_absorption (a b : Prop) : (a ∨ a ∧ b) = a := by
  rw [eq_iff_iff]
  constructor
  · intro hab
    cases hab with
    | inl ha => exact ha
    | inr hab => exact hab.left
  · intro ha
    exact Or.inl ha

@[simp]
theorem or_absorption (a b : Prop) : (a ∧ (a ∨ b)) = a := by
  rw [eq_iff_iff]
  constructor
  · intro hab
    exact hab.left
  · intro ha
    have hab := Or.intro_left b ha
    exact ⟨ha, hab⟩

@[simp]
theorem intersect_absorption (s t : Set α) :
    s ∪ (s ∩ t) = s := by
  unfold union
  unfold intersect
  funext x
  exact and_absorption (s x) (t x)

@[simp]
theorem union_absorption (s t : Set α) :
    s ∩ (s ∪ t) = s := by
  unfold intersect union
  funext x
  exact or_absorption (s x) (t x)

theorem intersection_distributivity (s t u : Set α) :
    s ∪ (t ∩ u) = (s ∪ t) ∩ (s ∪ u) := by
  apply setext
  intro a
  constructor
  · intro hstu
    rw [union_membership, intersection_membership] at hstu
    rw [intersection_membership, union_membership, union_membership]
    constructor
    · cases hstu with
      | inl has => exact Or.inl has
      | inr hatau => exact Or.inr hatau.left
    · cases hstu with
      | inl has => exact Or.inl has
      | inr hatau => exact Or.inr hatau.right
  · intro stsu
    rw [intersection_membership, union_membership, union_membership] at stsu
    rw [union_membership, intersection_membership]
    by_cases has : a ∈ s
    · exact Or.inl has
    · right
      obtain ⟨asat, asau⟩ := stsu
      have asat_resolved := Or.resolve_left asat
      have asau_resolved := Or.resolve_left asau
      exact ⟨asat_resolved has, asau_resolved has⟩

theorem union_distributivity (s t u : Set α) :
    s ∩ (t ∪ u) = (s ∩ t) ∪ (s ∩ u) := by
  apply setext
  intro a
  constructor
  · intro stu
    rw [intersection_membership, union_membership] at stu
    rw [union_membership, intersection_membership, intersection_membership]
    obtain ⟨has, hatau⟩ := stu
    cases hatau with
    | inl hat => exact Or.inl ⟨has, hat⟩
    | inr hau => exact Or.inr ⟨has, hau⟩
  · intro astsu
    rw [union_membership, intersection_membership, intersection_membership] at astsu
    rw [intersection_membership, union_membership]
    cases astsu with
    | inl asat => exact ⟨asat.left, Or.inl asat.right⟩
    | inr asau => exact ⟨asau.left, Or.inr asau.right⟩

theorem least_element (s : Set α) : ∅ ⊆ s := by
  unfold subset
  intro
  intro x_in_empty
  exfalso
  exact reductio x_in_empty

theorem greatest_element (s : Set α) : s ⊆ full := by
  unfold subset
  intro x
  intro
  rw [in_is_mem]
  exact trivial

theorem involution (s : Set α) : (sᶜᶜ) = s := by
  apply setext
  intro x
  unfold complement
  rw [in_is_mem, in_is_mem]
  constructor
  · intro hccs
    exact Classical.not_not.mp hccs
  · intro hs
    exact Classical.not_not.mpr hs

theorem union_de_morgan (s t : Set α) : (s ∪ t)ᶜ = (sᶜ ∩ tᶜ) := by
  apply setext
  intro x
  unfold union complement intersect
  rw [in_is_mem]
  constructor
  · intro xstc
    rw [not_or] at xstc
    rw [in_is_mem]
    exact xstc
  · intro nsnt
    rw [not_or]
    rw [in_is_mem] at nsnt
    exact nsnt

theorem intersection_de_morgan (s t : Set α) : (s ∩ t)ᶜ = (sᶜ ∪ tᶜ) := by
  apply setext
  intro x
  unfold union complement intersect
  rw [in_is_mem]
  constructor
  · intro xstc
    rw [not_and] at xstc
    by_cases hsx : s x
    · exact Or.inr (xstc hsx)
    · exact Or.inl hsx
  · intro nsnt
    rw [in_is_mem] at nsnt
    exact not_and_of_not_or_not nsnt

theorem complementation_full (s : Set α) : s ∪ sᶜ = full := by
  apply setext
  intro x
  unfold complement union
  rw [in_is_mem]
  constructor
  · intro
    exact trivial
  · intro hxf
    rw [in_is_mem] at hxf
    by_cases sx : s x
    · exact Or.inl sx
    · exact Or.inr sx

theorem complementation_empty (s : Set α) : s ∩ sᶜ = (∅: Set α) := by
  apply setext
  intro x
  rw [in_is_mem]
  unfold intersect complement
  constructor
  · intro hsxnsx
    exact absurd hsxnsx.left hsxnsx.right
  · intro xine
    exfalso
    exact reductio xine
