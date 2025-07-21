import Covalence.JEq

inductive Ctx.Wk : Ctx → Ctx → Prop
  | nil : Wk .nil .nil
  | lift' {Γ Δ : Ctx} {n m : ℕ} {x : ℕ} {A : Tm}
    : Wk Γ Δ
    → x ∉ Γ.dv
    → x ∉ Δ.dv
    → Γ.JEq (.univ n) A A
    → Δ.JEq (.univ m) A A
    → Wk (Γ.cons x A) (Δ.cons x A)
  | skip {Γ Δ : Ctx} {ℓ : ℕ} {x : ℕ} {A : Tm}
    : Wk Γ Δ
    → x ∉ Γ.dv
    → Γ.JEq (.univ ℓ) A A
    → Wk (Γ.cons x A) Δ

attribute [simp] Ctx.Wk.nil

theorem Ctx.Wk.dv_anti {Γ Δ : Ctx} (h : Ctx.Wk Γ Δ) : Δ.dv ⊆ Γ.dv := by
  induction h with
  | nil => rfl
  | lift' => simp [dv]; apply Finset.union_subset_union_right; assumption
  | skip _ _ _ I => apply Finset.Subset.trans I; simp [dv]

theorem Ctx.Wk.src_ok {Γ Δ : Ctx} (h : Ctx.Wk Γ Δ) : Γ.Ok := by
  induction h <;> constructor <;> assumption

theorem Ctx.Wk.trg_ok {Γ Δ : Ctx} (h : Ctx.Wk Γ Δ) : Δ.Ok := by
  induction h <;> repeat first | assumption | constructor

theorem Ctx.Ok.wk {Γ : Ctx} (h : Γ.Ok) : Ctx.Wk Γ Γ
  := by induction h <;> constructor <;> assumption

theorem Ctx.Wk.trans {Γ Δ Θ : Ctx} (hΓΔ : Ctx.Wk Γ Δ) (hΔΘ : Ctx.Wk Δ Θ) : Ctx.Wk Γ Θ := by
  induction hΓΔ generalizing Θ with
  | nil => exact hΔΘ
  | lift' => cases hΔΘ <;> constructor <;> apply_assumption <;> assumption
  | skip => constructor <;> apply_assumption; assumption

theorem Ctx.Wk.at {Γ Δ : Ctx} (h : Ctx.Wk Γ Δ) {x : ℕ} {A : Tm} (hA : Δ.At x A) : Γ.At x A := by
  induction h with
  | nil => exact hA
  | lift' _ _ _ _ _ I => cases hA with
    | here => apply At.here
    | there => apply At.there; apply I; assumption
  | skip _ _ _ I => apply At.there; exact I hA

theorem Ctx.JEq.wk {Γ Δ : Ctx} (hΓΔ : Ctx.Wk Γ Δ) {A a b : Tm} (h : Δ.JEq A a b) : Γ.JEq A a b := by
  induction h generalizing Γ with
  | univ | unit | nil | empty | nats | succ =>
    constructor
    apply hΓΔ.src_ok.zero
  | var _ hA =>
    constructor
    · apply hΓΔ.src_ok.zero
    · apply hΓΔ.at hA
  | eqn | trunc | nil_uniq | explode | eqn_rfl | inhab =>
    constructor <;> apply_assumption <;> assumption
  | pi_cf hA hB hℓ IA IB =>
    have hA' := IA hΓΔ
    rename Finset ℕ => L
    apply JEq.pi_cf (L := L ∪ Γ.dv)
    · exact hA'
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      apply IB
      · exact hx.1
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2) hA'.lhs hA.lhs
    · exact hℓ
  | app_cf hA hB hf hg he IA IB If Ig =>
    have hA' := IA hΓΔ
    rename Finset ℕ => L
    apply JEq.app_cf (L := L ∪ Γ.dv)
    · exact hA'
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      apply IB
      · exact hx.1
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2) hA'.lhs hA.lhs
    · exact (If hΓΔ)
    · exact (Ig hΓΔ)
    · exact he
  | abs_cf hA hb IA Ib =>
    have hA' := IA hΓΔ
    rename Finset ℕ => L
    apply JEq.abs_cf (L := L ∪ Γ.dv)
    · exact hA'
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      apply_assumption
      · exact hx.1
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2) hA'.lhs hA.lhs
  | sigma_cf hA hB hℓ IA IB =>
    have hA' := IA hΓΔ
    rename Finset ℕ => L
    apply JEq.sigma_cf (L := L ∪ Γ.dv)
    · exact hA'
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      apply IB
      · exact hx.1
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2) hA'.lhs hA.lhs
    · exact hℓ
  | pair_cf hA hB ha hb IA IB Ia Ib =>
    have hA' := IA hΓΔ
    rename Finset ℕ => L
    apply JEq.pair_cf (L := L ∪ Γ.dv)
    · exact hA'
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      apply IB
      · exact hx.1
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2) hA'.lhs hA.lhs
    · exact Ia hΓΔ
    · exact Ib hΓΔ
  | fst_cf hA hB he IA IB Ie =>
    have hA' := IA hΓΔ
    rename Finset ℕ => L
    apply JEq.fst_cf (L := L ∪ Γ.dv)
    · exact hA'
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      apply IB
      · exact hx.1
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2) hA'.lhs hA.lhs
    · exact Ie hΓΔ
  | snd_cf hA hB he hBa IA IB Ie =>
    have hA' := IA hΓΔ
    rename Finset ℕ => L
    apply JEq.snd_cf (L := L ∪ Γ.dv)
    · exact hA'
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      apply IB
      · exact hx.1
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2) hA'.lhs hA.lhs
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
      apply Ia
      · exact hx.1
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2) hφ'.lhs hφ.lhs
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      apply Ib
      · exact hx.1
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2) hφ'.lhs.not hφ.lhs.not
  | choose_cf hA hiA hφ IA IiA Iφ =>
    have hA' := IA hΓΔ
    rename Finset ℕ => L
    apply JEq.choose_cf (L := L ∪ Γ.dv)
    · exact hA'
    · exact IiA hΓΔ
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      apply Iφ
      · exact hx.1
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2) hA'.lhs hA.lhs
  | natrec_cf hC hn hz hs hCn IC In Iz Is =>
    rename Finset ℕ => L
    apply JEq.natrec_cf (L := L ∪ Γ.dv)
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      apply IC
      · exact hx.1
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2) hΓΔ.src_ok.nats hΓΔ.trg_ok.nats
    · exact In hΓΔ
    · exact Iz hΓΔ
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      apply Is
      · exact hx.1
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2) hΓΔ.src_ok.nats hΓΔ.trg_ok.nats
    · exact hCn
  | beta_abs_cf hA hb ha hBa hba IA Ib Ia =>
    have hA' := IA hΓΔ
    rename Finset ℕ => L
    apply JEq.beta_abs_cf (L := L ∪ Γ.dv)
    · exact hA'
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      apply Ib
      · exact hx.1
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2) hA'.lhs hA.lhs
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
      apply IB
      · exact hx.1
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2) hA'.lhs hA.lhs
    · exact Ia hΓΔ
    · exact Ib hΓΔ
  | beta_snd_cf hA hB ha hb hBa IA IB Ia Ib =>
    have hA' := IA hΓΔ
    rename Finset ℕ => L
    apply JEq.beta_snd_cf (L := L ∪ Γ.dv)
    · exact hA'
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      apply IB
      · exact hx.1
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2) hA'.lhs hA.lhs
    · exact Ia hΓΔ
    · exact Ib hΓΔ
    · exact hBa
  | spec_cf hA hiA hφ hφa IA Iia Iφ =>
    have hA' := IA hΓΔ
    rename Finset ℕ => L
    apply JEq.spec_cf (L := L ∪ Γ.dv)
    · exact hA'
    · exact Iia hΓΔ
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      apply Iφ
      · exact hx.1
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2) hA'.lhs hA.lhs
    · exact hφa
  | beta_true_cf hφ hA ha hb Iφ IA Ia Ib =>
    have hφ' := Iφ hΓΔ
    rename Finset ℕ => L
    apply JEq.beta_true_cf (L := L ∪ Γ.dv)
    · exact hφ'
    · exact IA hΓΔ
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      apply Ia
      · exact hx.1
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2) hφ'.lhs hφ.lhs
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      apply Ib
      · exact hx.1
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2) hφ'.lhs.not hφ.lhs.not
  | beta_false_cf hφ hA ha hb Iφ IA Ia Ib =>
    have hφ' := Iφ hΓΔ
    rename Finset ℕ => L
    apply JEq.beta_false_cf (L := L ∪ Γ.dv)
    · exact hφ'
    · exact IA hΓΔ
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      apply Ia
      · exact hx.1
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2) hφ'.lhs hφ.lhs
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      apply Ib
      · exact hx.1
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2) hφ'.lhs.not hφ.lhs.not
  | beta_zero_cf hC hz hs hCn IC Iz Is =>
    rename Finset ℕ => L
    apply JEq.beta_zero_cf (L := L ∪ Γ.dv)
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      apply IC
      · exact hx.1
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2) hΓΔ.src_ok.nats hΓΔ.trg_ok.nats
    · exact Iz hΓΔ
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      apply Is
      · exact hx.1
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2) hΓΔ.src_ok.nats hΓΔ.trg_ok.nats
    · exact hCn
  | beta_succ_cf hC hn hz hs hsn hCn hCs IC In Iz Is =>
    rename Finset ℕ => L
    apply JEq.beta_succ_cf (L := L ∪ Γ.dv)
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      apply IC
      · exact hx.1
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2) hΓΔ.src_ok.nats hΓΔ.trg_ok.nats
    · exact In hΓΔ
    · exact Iz hΓΔ
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      apply Is
      · exact hx.1
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2) hΓΔ.src_ok.nats hΓΔ.trg_ok.nats
    · exact hsn
    · exact hCn
    · exact hCs
  | nil_ok | cons_ok => exact hΓΔ.src_ok.zero
  | eqn_ext => apply JEq.eqn_ext <;> apply_assumption <;> assumption
  | pi_ext_cf hA hB hf hg hfg IA IB If Ig Ifg =>
    have hA' := IA hΓΔ
    rename Finset ℕ => L
    apply JEq.pi_ext_cf (L := L ∪ Γ.dv)
    · exact hA'
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      apply IB
      · exact hx.1
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2) hA'.lhs hA.lhs
    · exact If hΓΔ
    · exact Ig hΓΔ
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      apply Ifg
      · exact hx.1
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2) hA'.lhs hA.lhs
  | sigma_ext_cf hA hB he IA IB Ie =>
    have hA' := IA hΓΔ
    rename Finset ℕ => L
    apply JEq.sigma_ext_cf (L := L ∪ Γ.dv)
    · exact hA'
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      apply IB
      · exact hx.1
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2) hA'.lhs hA.lhs
    · exact Ie hΓΔ
  | prop_ext => apply JEq.prop_ext <;> apply_assumption <;> assumption
  | prop_uniq => apply JEq.prop_uniq <;> apply_assumption <;> assumption
  | trans => apply JEq.trans <;> apply_assumption <;> assumption
  | symm => apply JEq.symm; apply_assumption; assumption
  | cast => apply JEq.cast <;> apply_assumption <;> assumption

theorem Ctx.JEq.wk0
  {Γ : Ctx} {A a b : Tm} (h : Γ.JEq A a b)
  {ℓ : ℕ} {x : ℕ} {B : Tm} (hx : x ∉ Γ.dv) (hB : Γ.JEq (.univ ℓ) B B) : (Γ.cons x B).JEq A a b
  := h.wk (h.ok.wk.skip hx hB)
