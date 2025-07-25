import Covalence.Wk

inductive Ctx.Subst : Ctx → Ctx → Tm.MSubst → Tm.MSubst → Prop
  | nil {Γ : Ctx} {σ τ : Tm.MSubst} : Γ.Ok → Subst Γ .nil σ τ
  | cons' {Γ Δ : Ctx} {σ τ : Tm.MSubst} {x : ℕ} {A : Tm}
    : Γ.Subst Δ σ τ
    → x ∉ Δ.dv
    → Δ.IsTy A
    → Γ.JEq (A.msubst σ) (σ.get x) (τ.get x)
    → Γ.JEq (A.msubst τ) (σ.get x) (τ.get x)
    → Γ.Subst (Δ.cons x A) σ τ

theorem Ctx.Subst.src_ok {Γ Δ : Ctx} {σ τ : Tm.MSubst} (h : Γ.Subst Δ σ τ) : Γ.Ok := by
  induction h <;> assumption

theorem Ctx.Subst.trg_ok {Γ Δ : Ctx} {σ τ : Tm.MSubst} (h : Γ.Subst Δ σ τ) : Δ.Ok := by
  induction h <;> constructor <;> assumption

theorem Ctx.Subst.symm {Γ Δ : Ctx} {σ τ : Tm.MSubst} (h : Γ.Subst Δ σ τ) : Γ.Subst Δ τ σ := by
  induction h with
  | nil hΓ => exact .nil hΓ
  | cons' hΓΔ hx hΔ hσ hτ IΓΔ => exact IΓΔ.cons' hx hΔ hτ.symm hσ.symm

theorem Ctx.Subst.at {Γ Δ : Ctx} {σ τ : Tm.MSubst} (h : Γ.Subst Δ σ τ)
  {x : ℕ} {A : Tm} (hA : Δ.At x A) : Γ.JEq (A.msubst σ) (σ x) (τ x) := by
  induction hA <;> cases h <;> apply_assumption; assumption

theorem Ctx.Subst.lc_both {Γ Δ : Ctx} {σ τ : Tm.MSubst} (h : Γ.Subst Δ σ τ) : σ.Lc Δ.dv ∧ τ.Lc Δ.dv
  := by induction h with
  | nil => simp [dv]
  | cons' _ _ _ h => simp [dv, Tm.MSubst.Lc.union_iff, h.lc_lhs, h.lc_rhs, *]

theorem Ctx.Subst.lc_lhs {Γ Δ : Ctx} {σ τ : Tm.MSubst} (h : Γ.Subst Δ σ τ) : σ.Lc Δ.dv
  := h.lc_both.1

theorem Ctx.Subst.lc_rhs {Γ Δ : Ctx} {σ τ : Tm.MSubst} (h : Γ.Subst Δ σ τ) : τ.Lc Δ.dv
  := h.lc_both.2

theorem Ctx.Subst.wkIn {Γ Δ Θ : Ctx} {σ τ : Tm.MSubst} (hΓΔ : Γ.Wk Δ) (hΔΘ : Δ.Subst Θ σ τ)
  : Γ.Subst Θ σ τ := by
  induction hΔΘ with
  | nil _ => exact .nil hΓΔ.src_ok
  | cons' hΔΘ hx hΘ hσ hτ I => exact I.cons' hx hΘ (hσ.wk hΓΔ) (hτ.wk hΓΔ)

theorem Ctx.Subst.wk0In {Γ Δ : Ctx} {σ τ : Tm.MSubst}
  (h : Γ.Subst Δ σ τ) {x} (hx : x ∉ Γ.dv) {A : Tm} (hA : Γ.IsTy A)
  : (Γ.cons x A).Subst Δ σ τ := h.wkIn (hA.lhs_pure_wk0 hx).wk

theorem Ctx.Subst.lift' {Γ Δ : Ctx} {σ τ : Tm.MSubst}
  (h : Γ.Subst Δ σ τ) {x : ℕ} (hxΓ : x ∉ Γ.dv) (hxΔ : x ∉ Δ.dv) {A : Tm}
  (hΔ : Δ.IsTy A) (hΓ : Γ.IsTy (A.msubst σ))
  : (Γ.cons x (A.msubst σ)).Subst (Δ.cons x A) (σ.lift x) (τ.lift x)
  := sorry--(h.wk0In hxΓ hΓ).cons' sorry sorry sorry sorry

def Ctx.Subst.src {Γ Δ : Ctx} {σ τ : Tm.MSubst} (_ : Γ.Subst Δ σ τ) : Ctx := Γ

def Ctx.Subst.trg {Γ Δ : Ctx} {σ τ : Tm.MSubst} (_ : Γ.Subst Δ σ τ) : Ctx := Δ

theorem Ctx.JEq.subst_one {Γ Δ : Ctx} {σ : Tm.MSubst} {A a b : Tm}
  (hΓΔ : Γ.Subst Δ σ σ) (h : Δ.JEq A a b)
  : Γ.JEq (A.msubst σ) (a.msubst σ) (b.msubst σ)
  := by induction h generalizing Γ σ with
  | univ | unit | nil | empty | nats | succ => constructor; apply hΓΔ.src_ok.zero
  | dite_cf hφ hA ha hb Iφ IA Ia Ib =>
    apply JEq.dite_cf
    · exact Iφ hΓΔ
    · exact IA hΓΔ
    · intro x hx
      rename Finset ℕ => L
      have ⟨hΓ, hΔ, hL⟩ : x ∉ Γ.dv ∧ x ∉ hΓΔ.trg.dv ∧ x ∉ L
          := by simp only [<-Finset.notMem_union]; exact hx
      conv =>
        arg 2
        rw [<-Tm.msubst_lift_eq σ (x := x) (hx := by
          apply Finset.notMem_mono _ hΔ
          apply JEq.scoped_lhs
          assumption)]
        skip
      conv =>
        arg 3
        rw [<-Tm.msubst_lift_eq σ (x := x) (hx := by
          apply Finset.notMem_mono _ hΔ
          apply JEq.scoped_cf_lhs'
          assumption)]
        skip
      conv =>
        arg 4
        rw [<-Tm.msubst_lift_eq σ (x := x) (hx := by
          apply Finset.notMem_mono _ hΔ
          apply JEq.scoped_cf_rhs'
          assumption)]
        skip
      apply_assumption
      · exact hL
      · apply hΓΔ.lift' hΓ hΔ <;> apply JEq.lhs_ty <;> apply_assumption; assumption
    · intro x hx
      rename Finset ℕ => L
      have ⟨hΓ, hΔ, hL⟩ : x ∉ Γ.dv ∧ x ∉ hΓΔ.trg.dv ∧ x ∉ L
          := by simp only [<-Finset.notMem_union]; exact hx
      conv =>
        arg 2
        rw [<-Tm.msubst_lift_eq σ (x := x) (hx := by
          apply Finset.notMem_mono _ hΔ
          apply JEq.scoped_lhs
          assumption)]
        skip
      conv =>
        arg 3
        rw [<-Tm.msubst_lift_eq σ (x := x) (hx := by
          apply Finset.notMem_mono _ hΔ
          apply JEq.scoped_cf_lhs'
          assumption)]
        skip
      conv =>
        arg 4
        rw [<-Tm.msubst_lift_eq σ (x := x) (hx := by
          apply Finset.notMem_mono _ hΔ
          apply JEq.scoped_cf_rhs'
          assumption)]
        skip
      apply_assumption
      · exact hL
      · apply hΓΔ.lift' (A := Tm.not _) hΓ hΔ
        <;> apply TyEq.not_ty <;> apply JEq.lhs_ty <;> apply_assumption; assumption
  | natrec_cf => sorry
  | beta_abs_cf => sorry
  | spec_cf => sorry
  | beta_true_cf => sorry
  | beta_false_cf => sorry
  | beta_zero_cf => sorry
  | beta_succ_cf => sorry
  | nil_ok | cons_ok => exact hΓΔ.src_ok.zero
  | eqn_ext hA ha hb he IA Ia Ib Ie => exact .eqn_ext (IA hΓΔ) (Ia hΓΔ) (Ib hΓΔ) (Ie hΓΔ)
  | pi_ext_cf => sorry
  | sigma_ext_cf =>
    stop
    apply JEq.sigma_ext_cf <;>
    (first
    | apply_assumption
    | {
        intro x hx
        rename Finset ℕ => L
        have ⟨hΓ, hΔ, hL⟩ : x ∉ Γ.dv ∧ x ∉ hΓΔ.trg.dv ∧ x ∉ L
          := by simp only [<-Finset.notMem_union]; exact hx
        repeat rw [Tm.MSubst.Lc.bs0_var (hσ := hΓΔ.lc_rhs.anti (by {
          apply JEq.scoped_cf_rhs; assumption
        }))]
        · apply_assumption
          · exact hL
          · apply hΓΔ.lift' hΓ hΔ <;> apply JEq.lhs_ty <;> apply_assumption; assumption
        all_goals {
          apply Finset.notMem_mono _ hΔ
          apply JEq.scoped_cf_rhs; assumption
        }
      })
    <;> assumption
  | prop_ext hA hB hmp hmpr IA IB Imp Impr => exact .prop_ext (IA hΓΔ) (IB hΓΔ) (Imp hΓΔ) (Impr hΓΔ)
  | var _ hA => exact hΓΔ.at hA
  | trans _ _ Ia Ib => exact (Ia hΓΔ).trans (Ib hΓΔ)
  | symm _ Ia => exact (Ia hΓΔ).symm
  | cast _ _ IA Ia => exact (IA hΓΔ).cast (Ia hΓΔ)
  | _ =>
    stop
    constructor <;>
    (first
    | apply_assumption
    | {
        intro x hx
        rename Finset ℕ => L
        have ⟨hΓ, hΔ, hL⟩ : x ∉ Γ.dv ∧ x ∉ hΓΔ.trg.dv ∧ x ∉ L
          := by simp only [<-Finset.notMem_union]; exact hx
        repeat rw [Tm.MSubst.Lc.bs0_var (hσ := hΓΔ.lc_rhs.anti (by {
          first | (apply JEq.scoped_cf_ty; assumption)
                | (apply JEq.scoped_cf_rhs; assumption)
                | (apply JEq.scoped_cf_lhs; assumption)
        }))]
        · apply_assumption
          · exact hL
          · apply hΓΔ.lift' hΓ hΔ <;> apply JEq.lhs_ty <;> apply_assumption; assumption
        all_goals {
          apply Finset.notMem_mono _ hΔ
          first | (apply JEq.scoped_cf_ty; assumption)
                | (apply JEq.scoped_cf_rhs; assumption)
                | (apply JEq.scoped_cf_lhs; assumption)
        }
      }
    | {
      (try simp only [<-Tm.msubst_fst])
      rw [<-Tm.MSubst.Lc.bs0]
      apply_assumption; assumption
      all_goals {
        apply Tm.MSubst.Lc.anti
        · (try simp only [Tm.fvs, Finset.union_subset_iff])
          (try constructorm* _ ∧ _) <;>
          first | (apply JEq.scoped_lhs; assumption)
                -- | (apply JEq.scoped_rhs; assumption)
                | (apply JEq.scoped_cf_lhs ; assumption)
                -- | (apply JEq.scoped_cf_rhs ; assumption)
        · first | apply Ctx.Subst.lc_lhs -- | apply Ctx.Subst.lc_rhs
          assumption
      }
      })
    <;> assumption

-- theorem Ctx.JEq.subst_both {Γ Δ : Ctx} {σ τ : Tm.MSubst} {A a b : Tm}
--   (hΓΔ : Γ.Subst Δ σ τ) (h : Δ.JEq A a b)
--   : Γ.JEq (A.msubst σ) (a.msubst σ) (b.msubst τ) ∧ Γ.JEq (A.msubst τ) (a.msubst σ) (b.msubst τ)
--   := by induction h generalizing Γ σ τ with
--   | univ | unit | nil | empty | nats | succ =>
--     constructor <;> constructor <;> apply hΓΔ.src_ok.zero
--   | var _ hA => exact ⟨hΓΔ.at hA, (hΓΔ.symm.at hA).symm⟩
--   | symm ha Ia =>sorry
--   | _ => sorry

-- TODO: need substitution to cast stuff
-- theorem Ctx.Subst.symm {Γ Δ : Ctx} {σ τ : Tm.MSubst} (h : Γ.Subst Δ σ τ) : Γ.Subst Δ τ σ := by
--   induction h with
--   | nil hΓ => exact .nil hΓ
--   | cons' hΓΔ hx hΔ hΓ IΓΔ => exact IΓΔ.cons' hx hΔ hΓ.symm
