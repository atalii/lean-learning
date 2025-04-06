theorem modus_ponens
    {p q : Prop} (hp : p) (hpq : p → q) : q
  := hpq hp

theorem p_imp_p_imp_q
    {p q : Prop} (hq : q) : p → q
  := fun _ => hq

theorem imp_trans
    {p q r : Prop} (hpq : p → q) (hqp : q → r) : p → r
  := fun hp => hqp (hpq hp)

theorem modus_tollens
    {p q : Prop} (hnpnq : ¬q → ¬p) : p → q := by
  by_cases hq : q
  · exact fun (_: p) => hq
  · exact fun hp => absurd hp (hnpnq hq)

theorem modus_tollens_d_eq
    {p q : Prop} (hpq : p → q) : ¬q → ¬p := by
  exact modus_tollens fun (hnnp : ¬¬p) => by
    have hp := (@Classical.not_not p).mp hnnp
    have hq := hpq hp
    exact (@Classical.not_not q).mpr hq

theorem or_comm₁
    {p q : Prop} (hpqp : (p → q) → q) : (q → p) → p := by
  intro hqp
  by_cases hp : p
  · exact hp
  · exfalso
    have hnpnq := modus_tollens_d_eq hqp
    have nq := hnpnq hp
    have hnpnq := fun (_ : ¬q) => hp
    have hpq := modus_tollens hnpnq
    have hq := hpqp (hpq)
    exact absurd hq nq
