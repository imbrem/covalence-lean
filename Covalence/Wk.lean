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
  | univ_succ _ Is => exact JEq.univ_succ (Is hΓΔ)
  | univ_max _ _ hℓ hℓ' Im In => exact JEq.univ_max (Im hΓΔ) (In hΓΔ) hℓ hℓ'
  | univ_imax _ _ hℓ hℓ' Im In => exact JEq.univ_imax (Im hΓΔ) (In hΓΔ) hℓ hℓ'
  | trans => apply JEq.trans <;> apply_assumption <;> assumption
  | symm => apply JEq.symm; apply_assumption; assumption
  | cast => apply JEq.cast <;> apply_assumption <;> assumption
  | _ =>
    constructor <;> first | (apply_assumption <;> assumption) | {
      rename Finset ℕ => L
      intro x hx
      have ⟨hΓ, hL⟩ : x ∉ Γ.dv ∧ x ∉ L := by simp only [<-Finset.notMem_union]; exact hx
      simp only [Finset.mem_union, not_or] at hx
      apply_assumption
      · exact hL
      · apply hΓΔ.lift' hΓ (Set.notMem_subset hΓΔ.dv_anti hΓ)
        <;> (try exact hΓΔ.src_ok.nats.lhs_ty)
        <;> (try exact hΓΔ.trg_ok.nats.lhs_ty)
        <;> apply lhs_ty
        <;> (try apply JEq.not)
        <;> apply_assumption
        <;> assumption
    }

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

theorem Ctx.IsTy.wk0
  {Γ : Ctx} {A : Tm} (h : Γ.IsTy A)
  {x : ℕ} {B C : Tm} (hx : x ∉ Γ.dv) (hB : Γ.TyEq B C) : (Γ.cons x B).IsTy A
  := TyEq.wk0 h hx hB

theorem Ctx.JEq.to_cf_dv {Γ : Ctx} {A B a b : Tm} (h : Γ.JEq A a b) (hB : Γ.IsTy B)
  : ∀x ∉ Γ.dv, (Γ.cons x B).JEq (A.bs0 (.fv x)) (a.bs0 (.fv x)) (b.bs0 (.fv x))
  := fun x hx => by
    convert h.wk0 hx hB using 1
    · rw [Tm.bs0, Tm.bsubst_lc]; exact h.lc_ty
    · rw [Tm.bs0, Tm.bsubst_lc]; exact h.lc_lhs
    · rw [Tm.bs0, Tm.bsubst_lc]; exact h.lc_rhs

theorem Ctx.JEq.to_cf_dv' {Γ : Ctx} {A B a b : Tm} (h : Γ.JEq A a b) (hB : Γ.IsTy B) {L : Finset ℕ}
  (hL : Γ.dv ⊆ L) : ∀x ∉ L, (Γ.cons x B).JEq (A.bs0 (.fv x)) (a.bs0 (.fv x)) (b.bs0 (.fv x))
  := fun x hx => h.to_cf_dv hB x (Finset.not_mem_subset hL hx)

theorem Ctx.JEq.pi_k {Γ : Ctx} {m n : ℕ} {A A' B B' : Tm}
  (hA : Γ.JEq (.univ m) A A') (hB : Γ.JEq (.univ n) B B')
  : Γ.JEq (.univ (Nat.imax m n)) (.pi A B) (.pi A' B')
  := .pi_cf hA (hB.to_cf_dv hA.lhs_ty) rfl

theorem Ctx.JEq.app_k {Γ : Ctx} {m n : ℕ} {A A' B B' f f' a a' : Tm}
  (hA : Γ.JEq (.univ m) A A') (hB : Γ.JEq (.univ n) B B')
  (hf : Γ.JEq (.pi A B) f f') (ha : Γ.JEq A a a')
  : Γ.JEq B (.app A B f a) (.app A' B' f' a')
  := .app_cf hA (hB.to_cf_dv hA.lhs_ty) hf ha
      (by convert hB.lhs; rw [Tm.bs0, Tm.bsubst_lc]; exact hB.lc_lhs)

theorem Ctx.JEq.lhs_pure_wk1
  {Γ : Ctx} {ℓ : ℕ} {A B : Tm}
    (h : Γ.JEq (.univ ℓ) A B)
    {x : ℕ} (hx : x ∉ Γ.dv)
    {y : ℕ} (hy : y ∉ {x} ∪ Γ.dv)
    {Y : Tm} (hY : Γ.IsTy Y)
  : ((Γ.cons x A).cons y Y).PureWk (Γ.cons y Y) := (h.ok.pure_wk.skip hx h.lhs_ty).lift hy hY

theorem Ctx.TyEq.lhs_pure_wk1
  {Γ : Ctx} {A B : Tm}
    (h : Γ.TyEq A B)
    {x : ℕ} (hx : x ∉ Γ.dv)
    {y : ℕ} (hy : y ∉ {x} ∪ Γ.dv)
    {Y : Tm} (hY : Γ.IsTy Y)
  : ((Γ.cons x A).cons y Y).PureWk (Γ.cons y Y) := have ⟨_, h⟩ := h; h.lhs_pure_wk1 hx hy hY

theorem Ctx.JEq.wk1
  {Γ : Ctx} {y : ℕ} {Y A a b : Tm} (h : (Γ.cons y Y).JEq A a b)
  {x : ℕ} {B C : Tm} (hx : x ∉ {y} ∪ Γ.dv) (hB : Γ.TyEq B C) : ((Γ.cons x B).cons y Y).JEq A a b
  := h.pure_wk (hB.lhs_pure_wk1
    (by simp at hx; exact hx.2)
    (by simp at hx; simp [h.ok.var, Ne.symm hx.1]) h.ok.ty)

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
  | univ_succ _ Is => exact JEq.univ_succ (Is hΓΔ)
  | univ_max _ _ hℓ hℓ' Im In => exact JEq.univ_max (Im hΓΔ) (In hΓΔ) hℓ hℓ'
  | univ_imax _ _ hℓ hℓ' Im In => exact JEq.univ_imax (Im hΓΔ) (In hΓΔ) hℓ hℓ'
  | trans => apply JEq.trans <;> apply_assumption <;> assumption
  | symm => apply JEq.symm; apply_assumption; assumption
  | cast => apply JEq.cast <;> apply_assumption <;> assumption
  | _ =>
    constructor <;> first | (apply_assumption <;> assumption) | {
      rename Finset ℕ => L
      intro x hx
      have ⟨hΓ, hL⟩ : x ∉ Γ.dv ∧ x ∉ L := by simp only [<-Finset.notMem_union]; exact hx
      simp only [Finset.mem_union, not_or] at hx
      apply_assumption
      · exact hL
      · apply hΓΔ.lift' hΓ (Set.notMem_subset hΓΔ.dv_anti hΓ)
        <;> (try exact hΓΔ.src_ok.nats.lhs_ty)
        <;> (try exact hΓΔ.trg_ok.nats.lhs_ty)
        <;> apply lhs_ty
        <;> (try apply JEq.not)
        <;> apply_assumption
        <;> assumption
    }

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

theorem Ctx.Ok.var_regular {Γ : Ctx} {x : ℕ} {A : Tm} (h : Γ.Ok) (ha : Γ.At x A) :
  Γ.IsTy A := by
  induction ha with
  | here => cases h; apply Ctx.IsTy.wk0 <;> assumption
  | there _ I => cases h; apply Ctx.IsTy.wk0 <;> apply_assumption; assumption

theorem Ctx.JEq.regular {Γ : Ctx} {A a b : Tm} (h : Ctx.JEq Γ A a b) : Γ.IsTy A := by
  induction h with
  | var hΓ hA => exact hΓ.ok.var_regular hA
  | nil_ok => exact Ok.nil.nats_ty
  | cons_ok _ hA hx => exact (hA.lhs_ty.cons hx).nats_ty
  | succ hΓ I => exact ⟨1, .pi_cf hΓ.ok.nats (fun x hx => (I.cons hx).nats) rfl⟩
  | symm => assumption
  | trans => assumption
  | _ =>
    first | apply JEq.lhs_ty; assumption
          | apply JEq.rhs_ty; assumption
          | (constructor; constructor
            <;> first | rfl | assumption
                      | apply JEq.lhs; assumption
                      | intros; apply JEq.lhs; apply_assumption; assumption
                      | apply Ok.zero; apply JEq.ok ; assumption)

theorem Ctx.JEq.abs_k {Γ : Ctx} {m : ℕ} {A A' B b b' : Tm}
  (hA : Γ.JEq (.univ m) A A') (hb : Γ.JEq B b b')
  : Γ.JEq (.pi A B) (.abs A b) (.abs A' b')
  :=
  have ⟨_, hB⟩ := hb.regular;
  .abs_cf hA (hB.to_cf_dv hA.lhs_ty) (hb.to_cf_dv hA.lhs_ty)

theorem Ctx.JEq.prop_ext_true {Γ : Ctx} {A a : Tm}
  (hA : Γ.JEq (.univ 0) A A) (ha : Γ.JEq A a a) : Γ.JEq (.univ 0) A (.unit 0)
  := .prop_ext hA hA.ok.unit (.abs_k hA hA.ok.nil') (.abs_k hA.ok.unit ha)

theorem Ctx.JEq.dite_k {Γ : Ctx} {ℓ : ℕ} {φ φ' A A' a a' b b' : Tm}
  (hφ : Γ.JEq (.univ 0) φ φ') (hA : Γ.JEq (.univ ℓ) A A') (ha : Γ.JEq A a a') (hb : Γ.JEq A b b')
  : Γ.JEq A (.dite φ A a b) (.dite φ' A' a' b')
  := .dite_cf hφ hA (fun _ hx => ha.wk0 hx hφ.lhs_ty) (fun _ hx => hb.wk0 hx hφ.not.lhs_ty)

theorem Ctx.JEq.beta_true_k {Γ : Ctx} {ℓ : ℕ} {φ A a b : Tm}
  (hφ : Γ.JEq (.univ 0) φ (.unit 0)) (hA : Γ.JEq (.univ ℓ) A A)
  (ha : Γ.JEq A a a) (hb : Γ.JEq A b b) : Γ.JEq A (.dite φ A a b) a
  := .beta_true_cf hφ hA (fun _ hx => ha.wk0 hx hφ.lhs_ty) (fun _ hx => hb.wk0 hx hφ.not.lhs_ty)

theorem Ctx.JEq.beta_false_k {Γ : Ctx} {ℓ : ℕ} {φ A a b : Tm}
  (hφ : Γ.JEq (.univ 0) φ (.empty 0)) (hA : Γ.JEq (.univ ℓ) A A)
  (ha : Γ.JEq A a a) (hb : Γ.JEq A b b) : Γ.JEq A (.dite φ A a b) b
  := .beta_false_cf hφ hA (fun _ hx => ha.wk0 hx hφ.lhs_ty) (fun _ hx => hb.wk0 hx hφ.not.lhs_ty)

theorem Ctx.JEq.beta_true_kk {Γ : Ctx} {ℓ : ℕ} {A a b : Tm}
  (hA : Γ.JEq (.univ ℓ) A A)
  (ha : Γ.JEq A a a) (hb : Γ.JEq A b b) : Γ.JEq A (.dite (.unit 0) A a b) a
  := .beta_true_cf hA.ok.unit hA (fun _ hx => ha.wk0 hx hA.ok.unit_ty)
                                  (fun _ hx => hb.wk0 hx hA.ok.unit.not.lhs_ty)

theorem Ctx.JEq.beta_false_kk {Γ : Ctx} {ℓ : ℕ} {A a b : Tm}
  (hA : Γ.JEq (.univ ℓ) A A)
  (ha : Γ.JEq A a a) (hb : Γ.JEq A b b) : Γ.JEq A (.dite (.empty 0) A a b) b
  := .beta_false_cf hA.ok.empty hA (fun _ hx => ha.wk0 hx hA.ok.empty_ty)
                                    (fun _ hx => hb.wk0 hx hA.ok.empty.not.lhs_ty)

theorem Ctx.JEq.explode' {Γ : Ctx} {ℓ : ℕ} {A e a b : Tm}
  (he : Γ.JEq (.empty ℓ) e e) (ha : Γ.JEq A a a) (hb : Γ.JEq A b b)
  : Γ.JEq A a b :=
  have ⟨_, hA⟩ := ha.regular
  (hA.beta_true_kk ha hb).symm.trans ((he.explode.dite_k hA ha hb).trans (hA.beta_false_kk ha hb))

theorem Ctx.JEq.from_empty {Γ : Ctx} {m n : ℕ} {A : Tm}
  (hA : Γ.JEq (.univ m) A A)
  : Γ.JEq (.pi (.empty n) A) (.abs (.empty n) (.nil m)) (.abs (.empty n) (.nil m))
  := .abs_cf hA.ok.empty (hA.to_cf_dv hA.ok.empty_ty) (by
    intro x hx
    have hA' := hA.wk0 hx (hA.ok.empty_ty (ℓ := n));
    simp only [Tm.bs0, Tm.bsubst, A.bsubst_lc hA.lc_lhs]
    exact cast (.explode' (.var hA'.ok.zero .here) hA'.ok.unit hA') hA'.ok.nil'
  )

theorem Ctx.Ok.not_empty {ℓ : ℕ} {Γ : Ctx} (hΓ : Γ.Ok)
  : Γ.JEq (.univ 0) (.not (.empty ℓ)) (.unit 0)
  := .prop_ext_true (.not hΓ.empty) (.from_empty hΓ.empty)

theorem Ctx.JEq.not_empty {Γ : Ctx} {φ : Tm}
  (hφ : Γ.JEq (.univ 0) φ (.empty 0)) : Ctx.JEq Γ (.univ 0) (.not φ) (.unit 0)
  := hφ.not.trans hφ.ok.not_empty
