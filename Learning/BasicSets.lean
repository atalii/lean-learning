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
instance : EmptyCollection (Set α) := ⟨empty⟩

def full : Set α := fun _ => True

infix:60 " ∪ " => union
infix:60 " ∩ " => intersect
postfix:100 "ᶜ" => complement

-- wtf??
instance : Membership α (Set α) := ⟨mem⟩

def Set.Nonempty (s : Set α) : Prop := ∃ x, x ∈ s

theorem empty_is_empty : (∅ : Set α) = empty := by rfl

def subset (s t : Set α) : Prop := ∀ x ∈ s, x ∈ t
infix:60 " ⊆ " => subset

def characteristic (s : Set α) [DecidablePred (· ∈ s)] : α → ℕ :=
  fun a => if a ∈ s then 1 else 0

theorem setext (s t : Set α) (hst : ∀ x, x ∈ s ↔ x ∈ t) : s = t := by
  funext x
  rw [eq_iff_iff]
  exact hst x

theorem in_is_mem {a : α} {s : Set α } : (a ∈ s) = s a := by rfl

theorem nonempty_is_nonempty {s : Set α} : Set.Nonempty s ↔ s ≠ ∅ := by
  constructor
  · rintro ⟨x, hx⟩ rfl
    exact hx
  · intro h
    rw [ne_eq] at h
    unfold Set.Nonempty
    by_cases hxs : ∃ x, x ∈ s
    · exact hxs
    · exfalso
      rw [not_exists] at hxs
      rw [empty_is_empty] at h
      unfold empty at h
      simp only [in_is_mem] at hxs
      refine absurd h ?_
      rw [@Classical.not_not]
      apply funext
      intro x
      have the_goddamn_answer := hxs x
      rw [eq_iff_iff, iff_false]
      exact the_goddamn_answer

theorem union_membership (a : α) (s t : Set α) :
  (a ∈ s ∪ t) = (a ∈ s ∨ a ∈ t) := by
  unfold union
  repeat rw [in_is_mem]

theorem intersection_membership (a : α) (s t : Set α) :
    (a ∈ s ∩ t) = (a ∈ s ∧ a ∈ t) := by
  unfold intersect
  repeat rw [in_is_mem]

theorem complement_membership {a : α} {s : Set α} :
    ¬ a ∈ sᶜ ↔ a ∈ s := by
  unfold complement
  rw [in_is_mem, Classical.not_not, in_is_mem]

@[simp]
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

instance (s t : Set α) [DecidablePred (· ∈ s)] [DecidablePred (· ∈ t)] :
    DecidablePred (· ∈ s ∪ t) :=
  fun a => if has : a ∈ s ∨ a ∈ t then
    Decidable.isTrue (by simp [union_membership, has])
  else Decidable.isFalse (by simp [union_membership, has])

instance (s t : Set α) [DecidablePred (· ∈ s)] [DecidablePred (· ∈ t)] :
    DecidablePred (· ∈ s ∩ t) :=
  fun a => if has : a ∈ s ∧ a ∈ t then
    Decidable.isTrue (by simp [intersection_membership, has])
  else Decidable.isFalse (by simp [intersection_membership, has])

instance (s : Set α) [DecidablePred (· ∈ s)] :
    DecidablePred (· ∈ sᶜ) :=
  fun a => if has : a ∈ s then
    Decidable.isFalse (by simp [complement_membership, has])
  else Decidable.isTrue (by
    simp only
    rw [complement_membership.symm]
    rw [involution]
    exact has)

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

@[simp]
theorem union_characteristic
  (s t : Set α) (x : α)
  [DecidablePred (· ∈ s)] [DecidablePred (· ∈ t)] :
    characteristic (s ∪ t) x = max
      (characteristic s x) (characteristic t x) := by
  unfold characteristic
  split
  · rename_i h
    rw [union_membership] at h
    rcases h with hs | hs <;> rw [if_pos hs]
    · by_cases hxt : x ∈ t
      · rw [if_pos hxt]
        rfl
      · rw [if_neg hxt]
        rfl
    · by_cases hxs : x ∈ s
      · rw [if_pos hxs]
        rfl
      · rw [if_neg hxs]
        rfl
  · rename_i h
    rw [union_membership, not_or] at h
    obtain ⟨hnxs, hnxt⟩ := h
    rw [if_neg hnxs, if_neg hnxt]
    rfl

@[simp]
theorem intersection_characteristic
  (s t : Set α) (x : α)
  [DecidablePred (· ∈ s)] [DecidablePred (· ∈ t)] :
    characteristic (s ∩ t) x = min
      (characteristic s x) (characteristic t x) := by
  unfold characteristic
  split
  · rename_i h
    rw [intersection_membership] at h
    obtain ⟨hxs, hxt⟩ := h
    rw [if_pos hxs, if_pos hxt]
    rfl
  · rename_i h
    rw [intersection_membership, not_and] at h
    by_cases hxs : x ∈ s
    · have hnxt := h hxs
      rw [if_pos hxs, if_neg hnxt]
      rfl
    · rw [if_neg hxs]
      by_cases hxt : x ∈ t
      · rw [if_pos hxt]
        rfl
      · rw [if_neg hxt]
        rfl

@[simp]
theorem complement_characteristic
  (s : Set α) (x : α) [DecidablePred (· ∈ s)] :
    characteristic (sᶜ) x = 1 - characteristic s x := by
  unfold characteristic complement
  split
  · rename_i hxcs
    rw [in_is_mem] at hxcs
    rw [if_neg]
    exact hxcs
  · rename_i hnxcs
    rw [in_is_mem] at hnxcs
    rw [if_pos]
    rw [Classical.not_not] at hnxcs
    exact hnxcs

def union_all : (x : Set (Set α)) → Set α :=
  fun x ↦ fun a ↦ ∃ y ∈ x, a ∈ y

def intersect_all : (x : Set (Set α)) → Set α :=
  fun x ↦ fun a ↦ ∀ y ∈ x, a ∈ y

def related (r : α → α → Prop) : α → Set α := (r · ·)

def classes (r : α → α → Prop) (s : Set α) : Set (Set α) :=
  fun x ↦ ∃ a ∈ s, x = (related r a)

theorem related_refl {r : α → α → Prop} (hr : Equivalence r) :
    x ∈ related r x := hr.refl x

@[simp]
theorem mem_related {r : α → α → Prop} {x : α} {y : α} :
    (x ∈ related r y) ↔ r y x := ⟨id, id⟩

theorem classes_are_subsets {r : α → α → Prop} {s : Set α} {c : Set α} (h : c ∈ classes r s) (hr₁ : ∀ a b , r a b → a ∈ s ∧ b ∈ s) (hr : Equivalence r):
    c ⊆ s := by
  intro x _
  obtain ⟨a, _, rfl⟩ := h
  have hr₁ := hr₁ x x (hr.refl x)
  exact hr₁.left

theorem union_equiv_classes_partition
    (s : Set α) (r : α → α → Prop) (hr : Equivalence r) (hr₁ : ∀ a b, r a b → a ∈ s ∧ b ∈ s):
    union_all (classes r s) = s := by
  apply setext
  intro x
  constructor
  · intro from_union
    unfold union_all at from_union
    rw [in_is_mem] at from_union
    obtain ⟨rx, hrx⟩ := from_union
    apply classes_are_subsets hrx.left hr₁ hr
    exact hrx.right
  · intro xs
    refine ⟨related r x, ?_, related_refl hr⟩
    exact ⟨x, xs, rfl⟩

theorem equiv_classes_partition (a₁ a₂ : α) (r : α → α → Prop) (hr : Equivalence r) :
    related r a₁ = related r a₂ ∨ (related r a₁ ∩ related r a₂) = ∅ := by
  by_cases h : (related r a₁ ∩ related r a₂) = (∅ : Set α)
  · exact Or.inr h
  · left
    rw [← ne_eq _ _, ← nonempty_is_nonempty] at h
    obtain ⟨x, ⟨ha₁, ha₂⟩⟩ := h
    rw [← @in_is_mem _ x (related r a₁), mem_related] at ha₁
    rw [← @in_is_mem _ x (related r a₂), mem_related] at ha₂
    have ha₂r := hr.symm ha₂
    have ha₁a₂ := hr.trans ha₁ ha₂r
    apply setext
    intro x
    constructor
    · intro hxra₁
      rw [mem_related] at hxra₁
      have rxa₁ := hr.symm hxra₁
      exact hr.symm (hr.trans rxa₁ ha₁a₂)
    · intro hxra₂
      rw [mem_related] at hxra₂
      exact hr.trans ha₁a₂ hxra₂

def image (f : α → β) : Set β := fun b => ∃ a, b = f a
def injective (f : α → β) : Prop := ∀ x y, f x = f y → x = y
def surjective (f : α → β) : Prop := ∀ y, ∃ x, f x = y
def bijective (f : a → β) : Prop := injective f ∧ surjective f

def funext_r (f₁ f₂ : α → β) (a: α) (h : f₁ = f₂) : f₁ a = f₂ a := by rw [h]

def surjection_via_image (f : α → β) : surjective f ↔ image f = full := by
  constructor
  · intro hsf
    apply setext
    intro x
    constructor
    · intro
      trivial
    · intro
      have hsf := hsf x
      obtain ⟨a, ha⟩ := hsf
      exact ⟨a, ha.symm⟩
  · intro hiffs
    intro y
    have hiffs := funext_r (fun b => ∃ a, b = f a) (fun _ => True) y hiffs
    rw [@eq_iff_iff] at hiffs
    have hiffs := hiffs.mpr
    rw [true_implies] at hiffs
    obtain ⟨a, ha⟩ := hiffs
    exact ⟨a, ha.symm⟩

def bin_alg_system (α : Type u) : Type u := List (α × α → α)

-- A little sanity check example from the book.
def nats_alg_system : bin_alg_system ℕ := [fun (a, b) ↦ a + b, fun (a, b) ↦ a - b]

structure Homomorphism (α β : Type) where
  a : bin_alg_system α
  b : bin_alg_system β
  f : α → β
  hab : List.length a = List.length b
  hhomo : ∀ (a₁ a₂ : α),
            ∀ i : Fin a.length,
              have j : Fin b.length := Fin.mk (↑i) (by
                rw [← hab]
                exact Fin.is_lt i)
              (f (a.get i (a₁, a₂))) = (b.get j (f a₁, f a₂))

def epimorphism {α β : Type} (h : Homomorphism α β): Prop := surjective h.f
def isomoprhism {α β : Type} (h : Homomorphism α β): Prop := bijective h.f

def reflexive (f : (α × α) → Prop) : Prop := ∀ a, f (a, a)
def antisymm (f : (α × α) → Prop) : Prop := ∀ a b, a = b ↔ f (a, b) ∧ f (b, a)
def transitive (f : (α × α) → Prop) : Prop := ∀ a b c, f (a, b) ∧ f (b, c) → f (a, c)

def partial_order (f : Set (α × α)) : Prop := reflexive f ∧ antisymm f ∧ transitive f

structure Poset (α : Type) where
  set : Set α
  rel : α × α → Prop
  hrel : partial_order rel
