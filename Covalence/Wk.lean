import Covalence.JEq

inductive Ctx.PureWk : Ctx → Ctx → Prop
  | nil : PureWk .nil .nil
  | lift' {Γ Δ : Ctx} {x : ℕ} {A : Tm}
    : PureWk Γ Δ
    → x ∉ Γ.dv
    → x ∉ Δ.dv
    → Γ.TyEq A A
    → Δ.TyEq A A
    → PureWk (Γ.cons x A) (Δ.cons x A)
  | skip {Γ Δ : Ctx} {x : ℕ} {A : Tm}
    : PureWk Γ Δ
    → x ∉ Γ.dv
    → Γ.TyEq A A
    → PureWk (Γ.cons x A) Δ

attribute [simp] Ctx.PureWk.nil

theorem Ctx.PureWk.dv_anti {Γ Δ : Ctx} (h : Ctx.PureWk Γ Δ) : Δ.dv ⊆ Γ.dv := by
  induction h with
  | nil => rfl
  | lift' => simp [dv]; apply Finset.union_subset_union_right; assumption
  | skip _ _ _ I => apply Finset.Subset.trans I; simp [dv]

theorem Ctx.PureWk.src_ok {Γ Δ : Ctx} (h : Ctx.PureWk Γ Δ) : Γ.Ok := by
  induction h <;> constructor <;> assumption

theorem Ctx.PureWk.trg_ok {Γ Δ : Ctx} (h : Ctx.PureWk Γ Δ) : Δ.Ok := by
  induction h <;> repeat first | assumption | constructor

theorem Ctx.Ok.pure_drop {Γ : Ctx} (h : Γ.Ok) : Ctx.PureWk Γ .nil
  := by induction h <;> constructor <;> assumption

theorem Ctx.Ok.pure_wk {Γ : Ctx} (h : Γ.Ok) : Ctx.PureWk Γ Γ
  := by induction h <;> constructor <;> assumption

theorem Ctx.pure_wk_self_iff {Γ : Ctx} : Ctx.PureWk Γ Γ ↔ Γ.Ok := ⟨PureWk.src_ok, Ok.pure_wk⟩

theorem Ctx.pure_wk_nil_iff {Γ : Ctx} : Ctx.PureWk Γ .nil ↔ Γ.Ok := ⟨PureWk.src_ok, Ok.pure_drop⟩

theorem Ctx.PureWk.at {Γ Δ : Ctx} (h : Ctx.PureWk Γ Δ) {x : ℕ} {A : Tm} (hA : Δ.At x A) : Γ.At x A
  := by induction h with
  | nil => exact hA
  | lift' _ _ _ _ _ I => cases hA with
    | here => apply At.here
    | there => apply At.there; apply I; assumption
  | skip _ _ _ I => apply At.there; exact I hA

theorem Ctx.JEq.pure_wk {Γ Δ : Ctx} (hΓΔ : Ctx.PureWk Γ Δ) {A a b : Tm} (h : Δ.JEq A a b)
  : Γ.JEq A a b := by induction h generalizing Γ with
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
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2) hA'.lhs_ty hA.lhs_ty
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
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2) hA'.lhs_ty hA.lhs_ty
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
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2) hA'.lhs_ty hA.lhs_ty
  | sigma_cf hA hB hℓ IA IB =>
    have hA' := IA hΓΔ
    rename Finset ℕ => L
    apply JEq.sigma_cf (L := L ∪ Γ.dv)
    · exact hA'
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      apply IB
      · exact hx.1
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2) hA'.lhs_ty hA.lhs_ty
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
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2) hA'.lhs_ty hA.lhs_ty
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
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2) hA'.lhs_ty hA.lhs_ty
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
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2) hA'.lhs_ty hA.lhs_ty
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
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2) hφ'.lhs_ty hφ.lhs_ty
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      apply Ib
      · exact hx.1
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2) hφ'.lhs_ty.not_ty hφ.lhs_ty.not_ty
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
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2) hA'.lhs_ty hA.lhs_ty
  | natrec_cf hC hn hz hs hCn IC In Iz Is =>
    rename Finset ℕ => L
    apply JEq.natrec_cf (L := L ∪ Γ.dv)
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      apply IC
      · exact hx.1
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2)
          hΓΔ.src_ok.nats.lhs_ty hΓΔ.trg_ok.nats.lhs_ty
    · exact In hΓΔ
    · exact Iz hΓΔ
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      apply Is
      · exact hx.1
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2)
          hΓΔ.src_ok.nats.lhs_ty hΓΔ.trg_ok.nats.lhs_ty
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
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2) hA'.lhs_ty hA.lhs_ty
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
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2) hA'.lhs_ty hA.lhs_ty
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
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2) hA'.lhs_ty hA.lhs_ty
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
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2) hA'.lhs_ty hA.lhs_ty
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
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2) hφ'.lhs_ty hφ.lhs_ty
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      apply Ib
      · exact hx.1
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2) hφ'.lhs_ty.not_ty hφ.lhs_ty.not_ty
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
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2) hφ'.lhs_ty hφ.lhs_ty
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      apply Ib
      · exact hx.1
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2) hφ'.lhs_ty.not_ty hφ.lhs_ty.not_ty
  | beta_zero_cf hC hz hs hCn IC Iz Is =>
    rename Finset ℕ => L
    apply JEq.beta_zero_cf (L := L ∪ Γ.dv)
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      apply IC
      · exact hx.1
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2)
          hΓΔ.src_ok.nats.lhs_ty hΓΔ.trg_ok.nats.lhs_ty
    · exact Iz hΓΔ
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      apply Is
      · exact hx.1
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2)
          hΓΔ.src_ok.nats.lhs_ty hΓΔ.trg_ok.nats.lhs_ty
    · exact hCn
  | beta_succ_cf hC hn hz hs hsn hCn hCs IC In Iz Is =>
    rename Finset ℕ => L
    apply JEq.beta_succ_cf (L := L ∪ Γ.dv)
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      apply IC
      · exact hx.1
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2)
          hΓΔ.src_ok.nats.lhs_ty hΓΔ.trg_ok.nats.lhs_ty
    · exact In hΓΔ
    · exact Iz hΓΔ
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      apply Is
      · exact hx.1
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2)
          hΓΔ.src_ok.nats.lhs_ty hΓΔ.trg_ok.nats.lhs_ty
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
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2) hA'.lhs_ty hA.lhs_ty
    · exact If hΓΔ
    · exact Ig hΓΔ
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      apply Ifg
      · exact hx.1
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2) hA'.lhs_ty hA.lhs_ty
  | sigma_ext_cf hA hB he IA IB Ie =>
    have hA' := IA hΓΔ
    rename Finset ℕ => L
    apply JEq.sigma_ext_cf (L := L ∪ Γ.dv)
    · exact hA'
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      apply IB
      · exact hx.1
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2) hA'.lhs_ty hA.lhs_ty
    · exact Ie hΓΔ
  | prop_ext => apply JEq.prop_ext <;> apply_assumption <;> assumption
  | prop_uniq => apply JEq.prop_uniq <;> apply_assumption <;> assumption
  | trans => apply JEq.trans <;> apply_assumption <;> assumption
  | symm => apply JEq.symm; apply_assumption; assumption
  | cast => apply JEq.cast <;> apply_assumption <;> assumption

theorem Ctx.TyEq.pure_wk {Γ Δ : Ctx} (hΓΔ : Ctx.PureWk Γ Δ) {A B : Tm} (h : Δ.TyEq A B)
  : Γ.TyEq A B := have ⟨ℓ, h⟩ := h; ⟨ℓ, h.pure_wk hΓΔ⟩

theorem Ctx.PureWk.lift {Γ Δ : Ctx} {x : ℕ} {A : Tm}
  (h : PureWk Γ Δ) (hx : x ∉ Γ.dv) (hΔ : Δ.TyEq A A) : PureWk (Γ.cons x A) (Δ.cons x A)
  := h.lift' hx (Finset.not_mem_subset h.dv_anti hx) (hΔ.pure_wk h) hΔ

theorem Ctx.PureWk.trans {Γ Δ Θ : Ctx} (hΓΔ : Ctx.PureWk Γ Δ) (hΔΘ : Ctx.PureWk Δ Θ)
  : Ctx.PureWk Γ Θ := by induction hΓΔ generalizing Θ with
  | nil => exact hΔΘ
  | lift' => cases hΔΘ with
    | lift' => apply lift <;> apply_assumption; assumption
    | skip => constructor <;> apply_assumption; assumption
  | skip => constructor <;> apply_assumption; assumption

theorem Ctx.JEq.lhs_pure_wk0
  {Γ : Ctx} {ℓ : ℕ} {A B : Tm} (h : Γ.JEq (.univ ℓ) A B) {x : ℕ} (hx : x ∉ Γ.dv)
  : (Γ.cons x A).PureWk Γ := h.ok.pure_wk.skip hx h.lhs_ty

theorem Ctx.TyEq.lhs_pure_wk0
  {Γ : Ctx} {A B : Tm} (h : Γ.TyEq A B) {x : ℕ} (hx : x ∉ Γ.dv)
  : (Γ.cons x A).PureWk Γ := have ⟨_, h⟩ := h; h.lhs_pure_wk0 hx

theorem Ctx.JEq.wk0
  {Γ : Ctx} {A a b : Tm} (h : Γ.JEq A a b)
  {x : ℕ} {B C : Tm} (hx : x ∉ Γ.dv) (hB : Γ.TyEq B C) : (Γ.cons x B).JEq A a b
  := h.pure_wk (hB.lhs_pure_wk0 hx)

theorem Ctx.TyEq.wk0
  {Γ : Ctx} {A B : Tm} (h : Γ.TyEq A B)
  {x : ℕ} {C D : Tm} (hx : x ∉ Γ.dv) (hB : Γ.TyEq C D) : (Γ.cons x C).TyEq A B
  := have ⟨ℓ, h⟩ := h; ⟨ℓ, h.wk0 hx hB⟩

theorem Ctx.JEq.lhs_cons {Γ : Ctx} {ℓ : ℕ} {A B : Tm}
  (h : Γ.JEq (.univ ℓ) A B) {x : ℕ} (hx : x ∉ Γ.dv) : (Γ.cons x A).JEq (.univ ℓ) A B
  := h.wk0 hx h.ty_eq

theorem Ctx.TyEq.lhs_cons {Γ : Ctx} {A B : Tm}
  (h : Γ.TyEq A B) {x : ℕ} (hx : x ∉ Γ.dv) : (Γ.cons x A).TyEq A B
  := have ⟨ℓ, h⟩ := h; ⟨ℓ, h.lhs_cons hx⟩

theorem Ctx.JEq.rhs_cons {Γ : Ctx} {ℓ : ℕ} {A B : Tm}
  (h : Γ.JEq (.univ ℓ) A B) {x : ℕ} (hx : x ∉ Γ.dv) : (Γ.cons x B).JEq (.univ ℓ) A B
  := h.wk0 hx h.ty_eq.symm

inductive Ctx.Wk : Ctx → Ctx → Prop
  | nil : Wk .nil .nil
  | lift' {Γ Δ : Ctx} {x : ℕ} {A B : Tm}
    : Wk Γ Δ
    → x ∉ Γ.dv
    → x ∉ Δ.dv
    → Γ.TyEq A B
    → Δ.IsTy B
    → Wk (Γ.cons x A) (Δ.cons x B)
  | skip {Γ Δ : Ctx} {x : ℕ} {A : Tm}
    : Wk Γ Δ
    → x ∉ Γ.dv
    → Γ.TyEq A A
    → Wk (Γ.cons x A) Δ

theorem Ctx.Wk.dv_anti {Γ Δ : Ctx} (h : Ctx.Wk Γ Δ) : Δ.dv ⊆ Γ.dv := by
  induction h with
  | nil => rfl
  | lift' => simp [dv]; apply Finset.union_subset_union_right; assumption
  | skip _ _ _ I => apply Finset.Subset.trans I; simp [dv]

theorem Ctx.Wk.src_ok {Γ Δ : Ctx} (h : Ctx.Wk Γ Δ) : Γ.Ok := by
  induction h <;> constructor <;> repeat first | assumption | apply TyEq.lhs

theorem Ctx.Wk.trg_ok {Γ Δ : Ctx} (h : Ctx.Wk Γ Δ) : Δ.Ok := by
  induction h with
  | nil => constructor
  | lift' _ _ hx _ hΔ I => exact I.cons hx hΔ.rhs
  | skip => assumption

def Ctx.Var (Γ : Ctx) (x : ℕ) (A : Tm) := ∃X, Ctx.At Γ x X ∧ Γ.TyEq X A

theorem Ctx.Var.jeq {Γ : Ctx} {x : ℕ} {A : Tm} (h : Ctx.Var Γ x A) : Γ.JEq A (.fv x) (.fv x)
  := have ⟨_, hΓ, hX⟩ := h; hX.cast (.var hX.ok.zero hΓ)

theorem Ctx.Var.here {Γ : Ctx}
  {x : ℕ} (hx : x ∉ Γ.dv) {A B : Tm} (hA : Γ.TyEq A B)
  : Ctx.Var (Γ.cons x A) x B := ⟨A, .here, hA.lhs_cons hx⟩

theorem Ctx.Var.there
  {Γ : Ctx} {x : ℕ} {A : Tm} (h : Γ.Var x A) {y : ℕ} (hy : y ∉ Γ.dv) {B C : Tm}
  (hA : Γ.TyEq B C) : Ctx.Var (Γ.cons y B) x A
  := have ⟨X, hΓ, hX⟩ := h; ⟨X, hΓ.there, hX.wk0 hy hA⟩

theorem Ctx.Var.ok {Γ : Ctx} {x : ℕ} {A : Tm} (h : Ctx.Var Γ x A) : Γ.Ok := h.jeq.ok

theorem Ctx.Wk.at {Γ Δ : Ctx} (h : Ctx.Wk Γ Δ) {x : ℕ} {A : Tm} (hA : Δ.At x A) : Γ.Var x A
  := by induction h with
  | nil => cases hA
  | lift' _ _ _ _ _ I => cases hA with
    | here => apply Var.here <;> assumption
    | there => apply Var.there <;> apply_assumption; assumption
  | skip _ _ _ I => apply Var.there <;> apply_assumption; assumption

theorem Ctx.JEq.wk {Γ Δ : Ctx} (hΓΔ : Ctx.Wk Γ Δ) {A a b : Tm} (h : Δ.JEq A a b)
  : Γ.JEq A a b := by induction h generalizing Γ with
  | univ | unit | nil | empty | nats | succ =>
    constructor
    apply hΓΔ.src_ok.zero
  | var _ hA => exact (hΓΔ.at hA).jeq
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
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2) hA'.lhs_ty hA.lhs_ty
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
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2) hA'.lhs_ty hA.lhs_ty
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
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2) hA'.lhs_ty hA.lhs_ty
  | sigma_cf hA hB hℓ IA IB =>
    have hA' := IA hΓΔ
    rename Finset ℕ => L
    apply JEq.sigma_cf (L := L ∪ Γ.dv)
    · exact hA'
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      apply IB
      · exact hx.1
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2) hA'.lhs_ty hA.lhs_ty
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
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2) hA'.lhs_ty hA.lhs_ty
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
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2) hA'.lhs_ty hA.lhs_ty
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
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2) hA'.lhs_ty hA.lhs_ty
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
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2) hφ'.lhs_ty hφ.lhs_ty
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      apply Ib
      · exact hx.1
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2) hφ'.lhs_ty.not_ty hφ.lhs_ty.not_ty
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
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2) hA'.lhs_ty hA.lhs_ty
  | natrec_cf hC hn hz hs hCn IC In Iz Is =>
    rename Finset ℕ => L
    apply JEq.natrec_cf (L := L ∪ Γ.dv)
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      apply IC
      · exact hx.1
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2)
          hΓΔ.src_ok.nats.ty_eq hΓΔ.trg_ok.nats.ty_eq
    · exact In hΓΔ
    · exact Iz hΓΔ
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      apply Is
      · exact hx.1
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2)
          hΓΔ.src_ok.nats.ty_eq hΓΔ.trg_ok.nats.ty_eq
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
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2) hA'.lhs_ty hA.lhs_ty
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
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2) hA'.lhs_ty hA.lhs_ty
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
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2) hA'.lhs_ty hA.lhs_ty
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
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2) hA'.lhs_ty hA.lhs_ty
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
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2) hφ'.lhs_ty hφ.lhs_ty
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      apply Ib
      · exact hx.1
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2) hφ'.lhs_ty.not_ty hφ.lhs_ty.not_ty
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
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2) hφ'.lhs_ty hφ.lhs_ty
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      apply Ib
      · exact hx.1
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2) hφ'.lhs_ty.not_ty hφ.lhs_ty.not_ty
  | beta_zero_cf hC hz hs hCn IC Iz Is =>
    rename Finset ℕ => L
    apply JEq.beta_zero_cf (L := L ∪ Γ.dv)
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      apply IC
      · exact hx.1
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2)
          hΓΔ.src_ok.nats.ty_eq hΓΔ.trg_ok.nats.ty_eq
    · exact Iz hΓΔ
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      apply Is
      · exact hx.1
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2)
          hΓΔ.src_ok.nats.ty_eq hΓΔ.trg_ok.nats.ty_eq
    · exact hCn
  | beta_succ_cf hC hn hz hs hsn hCn hCs IC In Iz Is =>
    rename Finset ℕ => L
    apply JEq.beta_succ_cf (L := L ∪ Γ.dv)
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      apply IC
      · exact hx.1
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2)
          hΓΔ.src_ok.nats.ty_eq hΓΔ.trg_ok.nats.ty_eq
    · exact In hΓΔ
    · exact Iz hΓΔ
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      apply Is
      · exact hx.1
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2)
          hΓΔ.src_ok.nats.ty_eq hΓΔ.trg_ok.nats.ty_eq
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
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2) hA'.lhs_ty hA.lhs_ty
    · exact If hΓΔ
    · exact Ig hΓΔ
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      apply Ifg
      · exact hx.1
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2) hA'.lhs_ty hA.lhs_ty
  | sigma_ext_cf hA hB he IA IB Ie =>
    have hA' := IA hΓΔ
    rename Finset ℕ => L
    apply JEq.sigma_ext_cf (L := L ∪ Γ.dv)
    · exact hA'
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      apply IB
      · exact hx.1
      · exact hΓΔ.lift' hx.2 (Set.notMem_subset hΓΔ.dv_anti hx.2) hA'.lhs_ty hA.lhs_ty
    · exact Ie hΓΔ
  | prop_ext => apply JEq.prop_ext <;> apply_assumption <;> assumption
  | prop_uniq => apply JEq.prop_uniq <;> apply_assumption <;> assumption
  | trans => apply JEq.trans <;> apply_assumption <;> assumption
  | symm => apply JEq.symm; apply_assumption; assumption
  | cast => apply JEq.cast <;> apply_assumption <;> assumption

theorem Ctx.TyEq.wk {Γ Δ : Ctx} (hΓΔ : Ctx.Wk Γ Δ) {A B : Tm} (h : Δ.TyEq A B)
  : Γ.TyEq A B := have ⟨ℓ, h⟩ := h; ⟨ℓ, h.wk hΓΔ⟩

theorem Ctx.Wk.lift {Γ Δ : Ctx} {x : ℕ} {A B : Tm}
  (h : Wk Γ Δ) (hx : x ∉ Γ.dv) (hΔ : Δ.TyEq A B) : Wk (Γ.cons x A) (Δ.cons x B)
  := h.lift' hx (Finset.not_mem_subset h.dv_anti hx) (hΔ.wk h) hΔ.rhs

-- TODO: we need TyEq to be transitive, so we need uniqueness of typing!
-- but otherwise this works, unlike before...
-- theorem Ctx.Wk.trans {Γ Δ Θ : Ctx} (hΓΔ : Ctx.Wk Γ Δ) (hΔΘ : Ctx.Wk Δ Θ)
--   : Ctx.Wk Γ Θ := by induction hΓΔ generalizing Θ with
--   | nil => exact hΔΘ
--   | lift' hΓΔ hxΓ hxΔ hΓ hΔ I => cases hΔΘ with
--     | lift' hΔΘ _ hxΘ => exact (I hΔΘ).lift' hxΓ hxΘ (hΓ.trans sorry) sorry
--     | skip hΔΘ => sorry
--   | skip => constructor <;> apply_assumption; assumption

theorem Ctx.PureWk.wk {Γ Δ : Ctx} (h : PureWk Γ Δ) : Wk Γ Δ
  := by induction h <;> constructor <;> assumption

theorem Ctx.Ok.drop {Γ : Ctx} (h : Γ.Ok) : Wk Γ .nil := h.pure_drop.wk

theorem Ctx.Ok.wk {Γ : Ctx} (h : Γ.Ok) : Wk Γ Γ := h.pure_wk.wk

theorem Ctx.wk_self_iff {Γ : Ctx} : Ctx.Wk Γ Γ ↔ Γ.Ok := ⟨Wk.src_ok, Ok.wk⟩

theorem Ctx.wk_nil_iff {Γ : Ctx} : Ctx.Wk Γ .nil ↔ Γ.Ok := ⟨Wk.src_ok, Ok.drop⟩

theorem Ctx.JEq.lhs_wk0
  {Γ : Ctx} {ℓ : ℕ} {A B : Tm} (h : Γ.JEq (.univ ℓ) A B) {x : ℕ} (hx : x ∉ Γ.dv)
  : (Γ.cons x A).Wk Γ := (h.lhs_pure_wk0 hx).wk

theorem Ctx.JEq.cast0
  {Γ : Ctx} {x : ℕ} {B C a b : Tm} (h : (Γ.cons x B).JEq C a b)
  {A : Tm} (hB : Γ.TyEq A B) : (Γ.cons x A).JEq C a b
  := h.wk (hB.ok.wk.lift h.ok.var hB)
