import Covalence.Wk

inductive Ctx.PwEq : Ctx → Ctx → Prop
  | nil : PwEq .nil .nil
  | cons' {Γ Δ : Ctx} {ℓ : ℕ} {A B : Tm} {x : ℕ}
    : Γ.PwEq Δ → (x ∉ Γ.dv)
    → Γ.JEq (.univ ℓ) A B → Δ.JEq (.univ ℓ) A B → (Γ.cons x A).PwEq (Δ.cons x B)

theorem Ctx.PwEq.dv_eq {Γ Δ : Ctx} (h : Γ.PwEq Δ) : Γ.dv = Δ.dv := by induction h <;> simp [dv, *]

theorem Ctx.PwEq.symm {Γ Δ : Ctx} (h : Γ.PwEq Δ) : Δ.PwEq Γ := by
  induction h with
  | nil => exact .nil
  | cons' hΓΔ hx hA hA' IΓΔ => exact IΓΔ.cons' (hΓΔ.dv_eq ▸ hx) hA'.symm hA.symm

theorem Ctx.Ok.pw_eq {Γ : Ctx} (h : Γ.Ok) : Γ.PwEq Γ
  := by induction h <;> constructor <;> assumption

theorem Ctx.PwEq.lhs_ok {Γ Δ : Ctx} (h : Γ.PwEq Δ) : Γ.Ok := by induction h with
  | nil => exact .nil
  | cons' hΓΔ hx hA hA' I => exact .cons I hx hA.lhs

theorem Ctx.PwEq.rhs_ok {Γ Δ : Ctx} (h : Γ.PwEq Δ) : Δ.Ok := h.symm.lhs_ok

theorem Ctx.PwEq.at {Γ Δ : Ctx} (h : Γ.PwEq Δ) {x : ℕ} {A : Tm} (hA : Δ.At x A)
  : ∃B, Γ.At x B ∧ ∃ℓ, Γ.JEq (.univ ℓ) B A
  := by induction h with
  | nil => cases hA
  | cons' hΓΔ hx hA hA' I => cases hA with
    | here => exact ⟨_, .here, ⟨_, hA.wk0 hx hA.lhs⟩⟩
    | there h =>  have ⟨B, hy, ⟨ℓ, hB⟩⟩ := I h; exact ⟨B, hy.there, ⟨ℓ, hB.wk0 hx hA.lhs⟩⟩

theorem Ctx.JEq.pw_eq {Γ Δ : Ctx} {A a b : Tm} (hΓΔ : Γ.PwEq Δ) (h : Δ.JEq A a b) : Γ.JEq A a b
  := by induction h generalizing Γ with
  | univ | unit | nil | empty | eqn | trunc | nats | succ | nil_uniq | explode | eqn_rfl | inhab
  | eqn_ext
    => constructor <;> apply_assumption <;> assumption
  | var hA hx I => have ⟨_, hx', ⟨_, hB⟩⟩ := hΓΔ.at hx; exact hB.cast (.var hΓΔ.lhs_ok.zero hx')
  | pi_cf hA hB hℓ IA IB =>
    have hA' := IA hΓΔ
    rename Finset ℕ => L
    apply JEq.pi_cf (L := L ∪ Γ.dv)
    · exact hA'
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      apply IB x hx.1 (.cons' hΓΔ hx.2 hA'.lhs hA.lhs)
    · exact hℓ
  | app_cf hA hB hf hg he IA IB If Ig =>
    have hA' := IA hΓΔ
    rename Finset ℕ => L
    apply JEq.app_cf (L := L ∪ Γ.dv)
    · exact hA'
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      apply IB x hx.1 (.cons' hΓΔ hx.2 hA'.lhs hA.lhs)
    · exact If hΓΔ
    · exact Ig hΓΔ
    · exact he
  | abs_cf hA hb IA Ib =>
    have hA' := IA hΓΔ
    rename Finset ℕ => L
    apply JEq.abs_cf (L := L ∪ Γ.dv)
    · exact hA'
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      apply Ib x hx.1 (.cons' hΓΔ hx.2 hA'.lhs hA.lhs)
  | sigma_cf hA hB hℓ IA IB =>
    have hA' := IA hΓΔ
    rename Finset ℕ => L
    apply JEq.sigma_cf (L := L ∪ Γ.dv)
    · exact hA'
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      apply IB x hx.1 (.cons' hΓΔ hx.2 hA'.lhs hA.lhs)
    · exact hℓ
  | pair_cf hA hB ha hb IA IB Ia Ib =>
    have hA' := IA hΓΔ
    rename Finset ℕ => L
    apply JEq.pair_cf (L := L ∪ Γ.dv)
    · exact hA'
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      apply IB x hx.1 (.cons' hΓΔ hx.2 hA'.lhs hA.lhs)
    · exact Ia hΓΔ
    · exact Ib hΓΔ
  | fst_cf hA hB he IA IB Ie =>
    have hA' := IA hΓΔ
    rename Finset ℕ => L
    apply JEq.fst_cf (L := L ∪ Γ.dv)
    · exact hA'
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      apply IB x hx.1 (.cons' hΓΔ hx.2 hA'.lhs hA.lhs)
    · exact Ie hΓΔ
  | snd_cf hA hB he hBa IA IB Ie =>
    have hA' := IA hΓΔ
    rename Finset ℕ => L
    apply JEq.snd_cf (L := L ∪ Γ.dv)
    · exact hA'
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      apply IB x hx.1 (.cons' hΓΔ hx.2 hA'.lhs hA.lhs)
    · exact Ie hΓΔ
    · exact hBa
  | dite_cf hφ hA ha hb Iφ IA Ia Ib =>
    have hφ' := Iφ hΓΔ
    rename Finset ℕ => L
    apply JEq.dite_cf (L := L ∪ Γ.dv)
    · exact hφ'
    · exact IA hΓΔ
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      apply Ia x hx.1 (.cons' hΓΔ hx.2 hφ'.lhs hφ.lhs)
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      apply Ib x hx.1 (.cons' hΓΔ hx.2 hφ'.lhs.not hφ.lhs.not)
  | choose_cf hA hiA hφ IA IiA Iφ =>
    have hA' := IA hΓΔ
    rename Finset ℕ => L
    apply JEq.choose_cf (L := L ∪ Γ.dv)
    · exact hA'
    · exact IiA hΓΔ
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      apply Iφ x hx.1 (.cons' hΓΔ hx.2 hA'.lhs hA.lhs)
  | natrec_cf hC hn hz hs hCn IC In Iz Is =>
    rename Finset ℕ => L
    apply JEq.natrec_cf (L := L ∪ Γ.dv)
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      apply IC x hx.1 (.cons' hΓΔ hx.2 hΓΔ.lhs_ok.nats hΓΔ.rhs_ok.nats)
    · exact In hΓΔ
    · exact Iz hΓΔ
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      apply Is x hx.1 (.cons' hΓΔ hx.2 hΓΔ.lhs_ok.nats hΓΔ.rhs_ok.nats)
    · exact hCn
  | beta_abs_cf hA hb ha hBa hba IA Ib Ia =>
    have hA' := IA hΓΔ
    rename Finset ℕ => L
    apply JEq.beta_abs_cf (L := L ∪ Γ.dv)
    · exact hA'
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      apply Ib x hx.1 (.cons' hΓΔ hx.2 hA'.lhs hA.lhs)
    · exact Ia hΓΔ
    · exact hBa
    · exact hba
  | beta_fst_cf hA hB ha hb IA IB Ia Ib =>
    have hA' := IA hΓΔ
    rename Finset ℕ => L
    apply JEq.beta_fst_cf (L := L ∪ Γ.dv)
    · exact hA'
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      apply IB x hx.1 (.cons' hΓΔ hx.2 hA'.lhs hA.lhs)
    · exact Ia hΓΔ
    · exact Ib hΓΔ
  | beta_snd_cf hA hB ha hb hBA IA IB Ia Ib =>
    have hA' := IA hΓΔ
    rename Finset ℕ => L
    apply JEq.beta_snd_cf (L := L ∪ Γ.dv)
    · exact hA'
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      apply IB x hx.1 (.cons' hΓΔ hx.2 hA'.lhs hA.lhs)
    · exact Ia hΓΔ
    · exact Ib hΓΔ
    · exact hBA
  | spec_cf hA hiA hφ hφa IA Iia Iφ =>
    have hA' := IA hΓΔ
    rename Finset ℕ => L
    apply JEq.spec_cf (L := L ∪ Γ.dv)
    · exact hA'
    · exact Iia hΓΔ
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      apply Iφ x hx.1 (.cons' hΓΔ hx.2 hA'.lhs hA.lhs)
    · exact hφa
  | beta_true_cf hφ hA ha hb Iφ IA Ia Ib =>
    have hφ' := Iφ hΓΔ
    rename Finset ℕ => L
    apply JEq.beta_true_cf (L := L ∪ Γ.dv)
    · exact hφ'
    · exact IA hΓΔ
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      apply Ia x hx.1 (.cons' hΓΔ hx.2 hφ'.lhs hφ.lhs)
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      apply Ib x hx.1 (.cons' hΓΔ hx.2 hφ'.lhs.not hφ.lhs.not)
  | beta_false_cf hφ hA ha hb Iφ IA Ia Ib =>
    have hφ' := Iφ hΓΔ
    rename Finset ℕ => L
    apply JEq.beta_false_cf (L := L ∪ Γ.dv)
    · exact hφ'
    · exact IA hΓΔ
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      apply Ia x hx.1 (.cons' hΓΔ hx.2 hφ'.lhs hφ.lhs)
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      apply Ib x hx.1 (.cons' hΓΔ hx.2 hφ'.lhs.not hφ.lhs.not)
  | beta_zero_cf hC hz hs hCn IC Iz Is =>
    rename Finset ℕ => L
    apply JEq.beta_zero_cf (L := L ∪ Γ.dv)
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      apply IC x hx.1 (.cons' hΓΔ hx.2 hΓΔ.lhs_ok.nats hΓΔ.rhs_ok.nats)
    · exact Iz hΓΔ
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      apply Is x hx.1 (.cons' hΓΔ hx.2 hΓΔ.lhs_ok.nats hΓΔ.rhs_ok.nats)
    · exact hCn
  | beta_succ_cf hC hn hz hs hsn hCn hCs IC In Iz Is =>
    rename Finset ℕ => L
    apply JEq.beta_succ_cf (L := L ∪ Γ.dv)
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      apply IC x hx.1 (.cons' hΓΔ hx.2 hΓΔ.lhs_ok.nats hΓΔ.rhs_ok.nats)
    · exact In hΓΔ
    · exact Iz hΓΔ
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      apply Is x hx.1 (.cons' hΓΔ hx.2 hΓΔ.lhs_ok.nats hΓΔ.rhs_ok.nats)
    · exact hsn
    · exact hCn
    · exact hCs
  | nil_ok | cons_ok => exact hΓΔ.lhs_ok.zero
  | pi_ext_cf hA hB hf hg hfg IA IB If Ig Ifg =>
    have hA' := IA hΓΔ
    rename Finset ℕ => L
    apply JEq.pi_ext_cf (L := L ∪ Γ.dv)
    · exact hA'
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      apply IB x hx.1 (.cons' hΓΔ hx.2 hA'.lhs hA.lhs)
    · exact If hΓΔ
    · exact Ig hΓΔ
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      apply Ifg x hx.1 (.cons' hΓΔ hx.2 hA'.lhs hA.lhs)
  | sigma_ext_cf hA hB he IA IB Ie =>
    have hA' := IA hΓΔ
    rename Finset ℕ => L
    apply JEq.sigma_ext_cf (L := L ∪ Γ.dv)
    · exact hA'
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      apply IB x hx.1 (.cons' hΓΔ hx.2 hA'.lhs hA.lhs)
    · exact Ie hΓΔ
  | prop_ext => apply JEq.prop_ext <;> apply_assumption <;> assumption
  | prop_uniq => apply JEq.prop_uniq <;> apply_assumption <;> assumption
  | trans => apply JEq.trans <;> apply_assumption <;> assumption
  | symm => apply JEq.symm; apply_assumption; assumption
  | cast => apply JEq.cast <;> apply_assumption <;> assumption

-- theorem Ctx.PwEq.trans {Γ Δ Θ : Ctx} (hΓΔ : Γ.PwEq Δ) (hΔΘ : Δ.PwEq Θ) : Γ.PwEq Θ := by
--   induction hΓΔ generalizing Θ with
--   | nil => exact hΔΘ
--   | cons' hΓΔ hx hA hA' IΓΔ => cases hΔΘ with
--   | cons' hΓΘ hx' hB hB' => exact (IΓΔ hΓΘ).cons' hx (hA.trans hB) sorry
