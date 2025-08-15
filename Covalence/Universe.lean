import Covalence.HasTy

inductive Ctx.MaybeSubsort : Ctx → ℕ → Tm → Prop
  | var {Γ : Ctx} {x : ℕ} {A : Tm} {ℓ : ℕ}
    : Γ.Ok → Γ.At x A → MaybeSubsort Γ (ℓ + 1) A → MaybeSubsort Γ ℓ (.fv x)
  | univ {Γ : Ctx} {ℓ : ℕ} : MaybeSubsort Γ (ℓ + 2) (.univ ℓ)
  | unit {Γ : Ctx} {ℓ : ℕ} : MaybeSubsort Γ (ℓ + 1) (.unit ℓ)
  | nil {Γ : Ctx} {ℓ : ℕ} : MaybeSubsort Γ ℓ (.nil ℓ)
  | empty {Γ : Ctx} {ℓ : ℕ} : MaybeSubsort Γ (ℓ + 1) (.empty ℓ)
  | eqn {Γ : Ctx} {A a b : Tm} {ℓ : ℕ}
    :
    -- MaybeSubsort Γ ℓ a → MaybeSubsort Γ ℓ b →
    MaybeSubsort Γ 1 (.eqn A a b)
  | pi {Γ : Ctx} {A B : Tm} {ℓ m n : ℕ} {L : Finset ℕ}
    : MaybeSubsort Γ (m + 1) A
    → (∀x ∉ L, MaybeSubsort (Γ.cons x A) (n + 1) (B.bs0 (.fv x)))
    → (hℓ : ℓ = m.imax n) → MaybeSubsort Γ (ℓ + 1) (.pi ℓ A B)
  | abs {Γ : Ctx} {A B b : Tm} {ℓ m n : ℕ} {L : Finset ℕ}
    : MaybeSubsort Γ (m + 1) A
    → (∀x ∉ L, MaybeSubsort (Γ.cons x A) (n + 1) (B.bs0 (.fv x)))
    → (hℓ : ℓ = m.imax n)
    → MaybeSubsort Γ ℓ (.abs ℓ A B b)
  | app {Γ : Ctx} {A B f a : Tm} {m n : ℕ} {L : Finset ℕ}
    : MaybeSubsort Γ (m + 1) A
    → (∀x ∉ L, MaybeSubsort (Γ.cons x A) (n + 1) (B.bs0 (.fv x)))
    → MaybeSubsort Γ n (.app A B f a)
  | sigma {Γ : Ctx} {ℓ : ℕ} {A B : Tm} {m n : ℕ} {L : Finset ℕ}
    : MaybeSubsort Γ (m + 1) A
    → (∀x ∉ L, MaybeSubsort (Γ.cons x A) (n + 1) (B.bs0 (.fv x)))
    → (hℓ : ℓ = m ⊔ n)
    → MaybeSubsort Γ (ℓ + 1) (.sigma ℓ A B)
  | pair {Γ : Ctx} {ℓ : ℕ} {A B a b : Tm} {m n : ℕ} {L : Finset ℕ}
    : MaybeSubsort Γ (m + 1) A
    → (∀x ∉ L, MaybeSubsort (Γ.cons x A) (n + 1) (B.bs0 (.fv x)))
    → (hℓ : ℓ = m ⊔ n)
    → MaybeSubsort Γ ℓ (.pair ℓ A B a b)
  | fst {Γ : Ctx} {A B a : Tm} {m : ℕ}
    : MaybeSubsort Γ (m + 1) A → MaybeSubsort Γ m (.fst A B a)
  | snd {Γ : Ctx} {A B a : Tm} {m n : ℕ} {L : Finset ℕ}
    : MaybeSubsort Γ (m + 1) A
    → (∀x ∉ L, MaybeSubsort (Γ.cons x A) (n + 1) (B.bs0 (.fv x)))
    → MaybeSubsort Γ n (.snd A B a)
  | dite {Γ : Ctx} {φ A a b : Tm} {ℓ : ℕ}
    : MaybeSubsort Γ (ℓ + 1) A → MaybeSubsort Γ ℓ (.dite φ A a b)
  | trunc {Γ : Ctx} {A : Tm} : MaybeSubsort Γ 1 (.trunc A)
  | choose {Γ : Ctx} {A φ : Tm} {ℓ : ℕ} : MaybeSubsort Γ (ℓ + 1) A → MaybeSubsort Γ ℓ (.choose A φ)
  | nats {Γ : Ctx} : MaybeSubsort Γ 2 .nats
  | zero {Γ : Ctx} : MaybeSubsort Γ 1 .zero
  | succ {Γ : Ctx} : MaybeSubsort Γ 1 .succ
  | natrec {Γ : Ctx} {C n z s : Tm} {ℓ : ℕ} {L : Finset ℕ}
    : (∀x ∉ L, MaybeSubsort (Γ.cons x .nats) (ℓ + 1) (C.bs0 (.fv x)))
    → MaybeSubsort Γ ℓ (.natrec C n z s)

@[simp]
theorem Ctx.MaybeSubsort.univ_iff {Γ : Ctx} {ℓ ℓ' : ℕ} :
  MaybeSubsort Γ ℓ (.univ ℓ') ↔ ℓ = ℓ' + 2
  := by constructor <;> intro h <;> cases h <;> constructor

@[simp]
theorem Ctx.MaybeSubsort.unit_iff {Γ : Ctx} {ℓ ℓ' : ℕ} :
  MaybeSubsort Γ ℓ (.unit ℓ') ↔ ℓ = ℓ' + 1
  := by constructor <;> intro h <;> cases h <;> constructor

@[simp]
theorem Ctx.MaybeSubsort.nil_iff {Γ : Ctx} {ℓ ℓ' : ℕ} :
  MaybeSubsort Γ ℓ (.nil ℓ') ↔ ℓ = ℓ'
  := by constructor <;> intro h <;> cases h <;> constructor

@[simp]
theorem Ctx.MaybeSubsort.empty_iff {Γ : Ctx} {ℓ ℓ' : ℕ} :
  MaybeSubsort Γ ℓ (.empty ℓ') ↔ ℓ = ℓ' + 1
  := by constructor <;> intro h <;> cases h <;> constructor

@[simp]
theorem Ctx.MaybeSubsort.fst_iff {Γ : Ctx} {A B a : Tm} {m : ℕ} :
  MaybeSubsort Γ m (.fst A B a) ↔ MaybeSubsort Γ (m + 1) A
  := ⟨fun h => by cases h; assumption, fun h => .fst h⟩

@[simp]
theorem Ctx.MaybeSubsort.dite_iff {Γ : Ctx} {φ A a b : Tm} {ℓ : ℕ} :
  MaybeSubsort Γ ℓ (.dite φ A a b) ↔ MaybeSubsort Γ (ℓ + 1) A
  := ⟨fun h => by cases h; assumption, fun h => .dite h⟩

@[simp]
theorem Ctx.MaybeSupport.trunc_iff {Γ : Ctx} {A : Tm} {ℓ : ℕ} :
  MaybeSubsort Γ ℓ (.trunc A) ↔ ℓ = 1
  := by constructor <;> intro h <;> cases h <;> constructor

@[simp]
theorem Ctx.MaybeSubsort.choose_iff {Γ : Ctx} {A φ : Tm} {ℓ : ℕ} :
  MaybeSubsort Γ ℓ (.choose A φ) ↔ MaybeSubsort Γ (ℓ + 1) A
  := ⟨fun h => by cases h; assumption, fun h => .choose h⟩

@[simp]
theorem Ctx.MaybeSubsort.nats_iff {Γ : Ctx} {ℓ : ℕ} :
  MaybeSubsort Γ ℓ .nats ↔ ℓ = 2
  := by constructor <;> intro h <;> cases h <;> constructor

@[simp]
theorem Ctx.MaybeSubsort.zero_iff {Γ : Ctx} {ℓ : ℕ} :
  MaybeSubsort Γ ℓ .zero ↔ ℓ = 1
  := by constructor <;> intro h <;> cases h <;> constructor

@[simp]
theorem Ctx.MaybeSubsort.succ_iff {Γ : Ctx} {ℓ : ℕ} :
  MaybeSubsort Γ ℓ .succ ↔ ℓ = 1
  := by constructor <;> intro h <;> cases h <;> constructor

theorem Ctx.MaybeSubsort.unique {Γ : Ctx} {a : Tm} {m n : ℕ}
  (ha : MaybeSubsort Γ m a) (ha' : MaybeSubsort Γ n a) : m = n := by
  induction ha generalizing n with
  | var hΓ hx hA IA => cases ha' with | var  _ hx' hA' =>
    cases hΓ.at_eq hx hx'; have IA := IA hA'; omega
  | pi hA hB hℓ IA IB =>
    rename Finset ℕ => L
    cases ha' with | pi hA' hB' =>
    rename Finset ℕ => L'
    have ⟨x, hx⟩ := Finset.exists_notMem (L ∪ L');
    have hBx := hB x (by simp at hx; exact hx.left);
    have hBx' := hB' x (by simp at hx; exact hx.right);
    have IBx := IB x (by simp at hx; exact hx.left) hBx'
    cases IBx; rfl
  | app hA hB IA IB =>
    rename Finset ℕ => L
    cases ha' with | app hA' hB' =>
    rename Finset ℕ => L'
    have ⟨x, hx⟩ := Finset.exists_notMem (L ∪ L');
    have hBx := hB x (by simp at hx; exact hx.left);
    have hBx' := hB' x (by simp at hx; exact hx.right);
    have IBx := IB x (by simp at hx; exact hx.left) hBx'
    cases IBx; rfl
  | abs hA hB hℓ IA IB =>
    rename Finset ℕ => L
    cases ha' with | abs hA' hB' =>
    rename Finset ℕ => L'
    have ⟨x, hx⟩ := Finset.exists_notMem (L ∪ L');
    have hBx := hB x (by simp at hx; exact hx.left);
    have hBx' := hB' x (by simp at hx; exact hx.right);
    have IBx := IB x (by simp at hx; exact hx.left) hBx'
    cases IBx; rfl
  | sigma hA hB hℓ IA IB =>
    rename Finset ℕ => L
    cases ha' with | sigma hA' hB' =>
    rename Finset ℕ => L'
    have ⟨x, hx⟩ := Finset.exists_notMem (L ∪ L');
    have hBx := hB x (by simp at hx; exact hx.left);
    have hBx' := hB' x (by simp at hx; exact hx.right);
    have IBx := IB x (by simp at hx; exact hx.left) hBx'
    cases IBx; rfl
  | pair hA hB hℓ IA IB =>
    rename Finset ℕ => L
    cases ha' with | pair hA' hB' =>
    rename Finset ℕ => L'
    have ⟨x, hx⟩ := Finset.exists_notMem (L ∪ L');
    have hBx := hB x (by simp at hx; exact hx.left);
    have hBx' := hB' x (by simp at hx; exact hx.right);
    have IBx := IB x (by simp at hx; exact hx.left) hBx'
    cases IBx; rfl
  | fst hA IA => cases ha' with | fst hA' => cases IA hA'; rfl
  | snd hA hB IA IB =>
    rename Finset ℕ => L
    cases ha' with | snd hA' hB' =>
    rename Finset ℕ => L'
    have ⟨x, hx⟩ := Finset.exists_notMem (L ∪ L');
    have hBx := hB x (by simp at hx; exact hx.left);
    have hBx' := hB' x (by simp at hx; exact hx.right);
    have IBx := IB x (by simp at hx; exact hx.left) hBx'
    cases IBx; rfl
  | dite hA IA => cases ha' with | dite hA' => cases IA hA'; rfl
  | choose hA IA => cases ha' with | choose hA' => cases IA hA'; rfl
  | natrec hC IC =>
    rename Finset ℕ => L
    cases ha' with | natrec hC' =>
    rename Finset ℕ => L'
    have ⟨x, hx⟩ := Finset.exists_notMem (L ∪ L');
    have hCx := hC x (by simp at hx; exact hx.left);
    have hCx' := hC' x (by simp at hx; exact hx.right);
    have ICx := IC x (by simp at hx; exact hx.left) hCx'
    cases ICx; rfl
  | _ => cases ha'; rfl

def Ctx.MaybeSubsortCompat (Γ : Ctx) (ℓ : ℕ) (a b : Tm) : Prop :=
  MaybeSubsort Γ ℓ a ∧ MaybeSubsort Γ ℓ b

-- theorem Ctx.JEq.maybe_subsort_compat_iff {Γ : Ctx} {A a b : Tm} (hab : Γ.JEq A a b) {ℓ : ℕ} :
--   Γ.HasTy (.univ ℓ) A ↔ Ctx.MaybeSubsortCompat Γ ℓ a b := by
--   induction hab generalizing ℓ with
--   | beta_true_cf =>
--     sorry
--   | _ => sorry

-- theorem Ctx.MaybeSubsort.jeq_univ {Γ : Ctx} {A a b : Tm} {ℓ : ℕ}
--   (ha : Γ.MaybeSubsort ℓ a) (hb : Γ.MaybeSubsort ℓ b) (hab : Γ.JEq A a b)
--   : Γ.HasTy (.univ ℓ) A
--   := by induction hab generalizing ℓ with
--   | univ | unit | nil | empty | eqn | explode | eqn_rfl | inhab | nats
--     => cases ha; constructor; apply JEq.ok; assumption
--   | nil_uniq | eqn_ext
--     => apply_assumption <;> assumption
--   | spec_cf =>
--     cases hb; constructor; apply JEq.ok; assumption
--   | beta_true_cf _ hA =>
--     have hA' := hA.ty_lhs
--     sorry
--   | _ => sorry

-- theorem Ctx.JEq.maybe_subsort_iff {Γ : Ctx} {A a b : Tm} {ℓ : ℕ} (hab : Γ.JEq A a b) :
--   MaybeSubsort Γ ℓ a ↔ MaybeSubsort Γ ℓ b := by induction hab generalizing ℓ with
--   | eqn_ext hA ha hb heqn IA Ia Ib Ieqn =>
--     have Ieqn := Ieqn (ℓ := 1)
--     simp only [MaybeSubsort.unit_iff, zero_add, iff_true] at Ieqn
--     cases Ieqn with
--     | eqn ha hb =>

--       sorry
--   | _ => stop simp [*]
