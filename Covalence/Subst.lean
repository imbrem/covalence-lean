import Covalence.Wk

inductive Ctx.Subst : Ctx → Ctx → Tm.MSubst → Tm.MSubst → Prop
  | nil {Γ : Ctx} {σ τ : Tm.MSubst} : Γ.Ok → Subst Γ .nil σ τ
  | cons' {Γ Δ : Ctx} {σ τ : Tm.MSubst} {ℓ : ℕ} {x : ℕ} {A : Tm}
    : Γ.Subst Δ σ τ
    → x ∉ Δ.dv
    → Δ.JEq (.univ ℓ) A A
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

-- theorem Ctx?.Subst.trans {Γ Δ : Ctx} {σ τ ρ : Tm.MSubst}
--   (hστ : Γ.Subst Δ σ τ) (hτρ : Γ.Subst Δ τ ρ) : Γ.Subst Δ σ ρ := by
--   induction hστ with
--   | nil hΓ => exact .nil hΓ
--   | cons' hΓΔ hx hΔ hσ hτ IΓΔ => cases hτρ with
--   | cons' hΓΔ' hx' hΔ' hτ' hρ => exact (IΓΔ hΓΔ').cons' hx hΔ (hσ.trans hτ) sorry

theorem Ctx.Subst.at {Γ Δ : Ctx} {σ τ : Tm.MSubst} (h : Γ.Subst Δ σ τ)
  {x : ℕ} {A : Tm} (hA : Δ.At x A) : Γ.JEq (A.msubst σ) (σ x) (τ x) := by
  induction hA <;> cases h <;> apply_assumption; assumption

-- theorem Ctx.JEq.subst_both {Γ Δ : Ctx} {σ τ : Tm.MSubst} {A a b : Tm}
--   (hΓΔ : Γ.Subst Δ σ τ) (h : Δ.JEq A a b)
--   : Γ.JEq (A.msubst σ) (a.msubst σ) (b.msubst τ) ∧ Γ.JEq (A.msubst τ) (a.msubst σ) (b.msubst τ)
--   := by induction h generalizing Γ σ τ with
--   | univ | unit | nil | empty | nats | succ =>
--     constructor <;> constructor <;> apply hΓΔ.src_ok.zero
--   | var _ hA => exact ⟨hΓΔ.at hA, (hΓΔ.symm.at hA).symm⟩
--   | symm ha Ia => sorry
--   | _ => sorry

-- TODO: need substitution to cast stuff
-- theorem Ctx.Subst.symm {Γ Δ : Ctx} {σ τ : Tm.MSubst} (h : Γ.Subst Δ σ τ) : Γ.Subst Δ τ σ := by
--   induction h with
--   | nil hΓ => exact .nil hΓ
--   | cons' hΓΔ hx hΔ hΓ IΓΔ => exact IΓΔ.cons' hx hΔ hΓ.symm
