import Covalence.Regularity

--TODO: SubstEq lore...

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

theorem Ctx.Subst.refl {Γ : Ctx} (h : Γ.Ok) : Γ.Subst Γ 1 1 := by induction h with
  | nil => exact .nil .nil
  | cons hΓΔ hx hA I =>
    have h' := hΓΔ.cons hx hA;
    exact .cons' (I.wk0In hx hA) hx hA
      (.var h'.zero (by simp; constructor))
      (.var h'.zero (by simp; constructor))

theorem Ctx.Subst.to_eqOn {Γ Δ : Ctx}
   {σ τ σ' τ' : Tm.MSubst} (h : Γ.Subst Δ σ τ)
   (hσ : σ.EqOn Δ.dv σ') (hτ : τ.EqOn Δ.dv τ') : Γ.Subst Δ σ' τ'
  := by induction h with
  | nil hΓ => exact .nil hΓ
  | cons' hΓΔ hx hΔ hσ' hτ' IΓΔ =>
    simp only [Tm.MSubst.EqOn.union_iff, Tm.MSubst.EqOn.singleton_iff, Ctx.dv] at *
    apply (IΓΔ hσ.2 hτ.2).cons' hx hΔ
    · convert hσ' using 1
      · rw [Tm.msubst_eqOn_subset (h := hσ.2.symm)]
        exact hΔ.scoped
      · exact hσ.1.symm
      · exact hτ.1.symm
    · convert hτ' using 1
      · rw [Tm.msubst_eqOn_subset (h := hτ.2.symm)]
        exact hΔ.scoped
      · exact hσ.1.symm
      · exact hτ.1.symm

theorem Ctx.Subst.of_wk {Γ Δ : Ctx} (h : Γ.Wk Δ) : Γ.Subst Δ 1 1 := (refl h.trg_ok).wkIn h

theorem Ctx.Subst.lift_one' {Γ Δ : Ctx} {σ : Tm.MSubst}
  (h : Γ.Subst Δ σ σ) {x : ℕ} (hxΓ : x ∉ Γ.dv) (hxΔ : x ∉ Δ.dv) {A : Tm}
  (hΔ : Δ.IsTy A) (hΓ : Γ.IsTy (A.msubst σ))
  : (Γ.cons x (A.msubst σ)).Subst (Δ.cons x A) (σ.lift x) (σ.lift x)
  := by
    apply ((h.wk0In hxΓ hΓ).to_eqOn
      (σ.lift_eqOn_of_notMem _ _ hxΔ)
      (σ.lift_eqOn_of_notMem _ _ hxΔ)
    ).cons' hxΔ hΔ
    · simp only [Tm.MSubst.get_lift_self]
      apply JEq.var
      · apply (hΓ.cons hxΓ).zero
      · rw [Tm.msubst_lift_eq (hx := Finset.not_mem_subset hΔ.scoped hxΔ)]
        constructor
    · simp only [Tm.MSubst.get_lift_self]
      apply JEq.var
      · apply (hΓ.cons hxΓ).zero
      · rw [Tm.msubst_lift_eq (hx := Finset.not_mem_subset hΔ.scoped hxΔ)]
        constructor

def Ctx.Subst.src {Γ Δ : Ctx} {σ τ : Tm.MSubst} (_ : Γ.Subst Δ σ τ) : Ctx := Γ

def Ctx.Subst.trg {Γ Δ : Ctx} {σ τ : Tm.MSubst} (_ : Γ.Subst Δ σ τ) : Ctx := Δ

theorem Ctx.JEq.subst_one {Γ Δ : Ctx} {σ : Tm.MSubst} {A a b : Tm}
  (hΓΔ : Γ.Subst Δ σ σ) (h : Δ.JEq A a b)
  : Γ.JEq (A.msubst σ) (a.msubst σ) (b.msubst σ)
  := by induction h generalizing Γ σ with
  | univ | unit | nil | empty | nats | succ => constructor; apply hΓΔ.src_ok.zero
  | dite_cf hφ hA ha hb Iφ IA Ia Ib
  | beta_true_cf hφ hA ha hb Iφ IA Ia Ib
  | beta_false_cf hφ hA ha hb Iφ IA Ia Ib =>
    constructor <;> first
    | (apply_assumption ; assumption)
    | {
      intro x hx
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
      · (first | apply hΓΔ.lift_one' hΓ hΔ | apply hΓΔ.lift_one' (A := Tm.not _) hΓ hΔ)
        <;> apply JEq.lhs_ty <;> (try apply JEq.not) <;> apply_assumption; assumption
    }
  | nil_ok | cons_ok => exact hΓΔ.src_ok.zero
  | eqn_ext hA ha hb he IA Ia Ib Ie => exact .eqn_ext (IA hΓΔ) (Ia hΓΔ) (Ib hΓΔ) (Ie hΓΔ)
  | pi_ext_cf hA hB hf hg hfg IA IB If Ig Ifg =>
    rename Finset ℕ => L
    rename_i A B f g
    apply JEq.pi_ext_cf
    · exact IA hΓΔ
    · {
        intro x hx
        have ⟨hΓ, hΔ, hL⟩ : x ∉ Γ.dv ∧ x ∉ hΓΔ.trg.dv ∧ x ∉ L
          := by simp only [<-Finset.notMem_union]; exact hx
        rw [Tm.MSubst.Lc.bs0_var (hσ := hΓΔ.lc_rhs.anti (by {
          apply JEq.scoped_cf_ty; assumption
        }))]
        · apply_assumption
          · exact hL
          · apply hΓΔ.lift_one' hΓ hΔ <;> apply JEq.lhs_ty <;> apply_assumption; assumption
        all_goals {
          apply Finset.notMem_mono _ hΔ
          apply JEq.scoped_cf_ty; assumption
        }
      }
    · exact If hΓΔ
    · exact Ig hΓΔ
    · {
        intro x hx
        have ⟨hΓ, hΔ, hL⟩ : x ∉ Γ.dv ∧ x ∉ hΓΔ.trg.dv ∧ x ∉ L
          := by simp only [<-Finset.notMem_union]; exact hx
        have hABf : (Tm.app (A.msubst σ) (B.msubst σ) (f.msubst σ) (.fv x))
                  = (Tm.app A B f (.fv x)).msubst (σ.lift x) := by
                  simp; constructorm* _ ∧ _
                  <;> rw [Tm.msubst_lift_eq]
                  <;> apply Finset.notMem_mono _ hΔ
                  <;> first
                  | (apply JEq.scoped_cf_ty; assumption)
                  | (apply JEq.scoped_rhs; assumption)
        have hABg : (Tm.app (A.msubst σ) (B.msubst σ) (g.msubst σ) (.fv x))
                  = (Tm.app A B g (.fv x)).msubst (σ.lift x) := by
                  simp; constructorm* _ ∧ _
                  <;> rw [Tm.msubst_lift_eq]
                  <;> apply Finset.notMem_mono _ hΔ
                  <;> first
                  | (apply JEq.scoped_cf_ty; assumption)
                  | (apply JEq.scoped_rhs; assumption)
        rw [hABf, hABg]
        rw [Tm.MSubst.Lc.bs0_fvs_singleton (x := x) (hσ := hΓΔ.lc_rhs.anti (by {
          apply JEq.scoped_cf_ty; assumption
        })) (ha := by simp)]
        · apply Ifg
          · exact hL
          · apply hΓΔ.lift_one' hΓ hΔ <;> apply JEq.lhs_ty <;> apply_assumption; assumption
        · apply Finset.notMem_mono _ hΔ
          apply JEq.scoped_cf_ty; assumption
      }
  | sigma_ext_cf =>
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
          · apply hΓΔ.lift_one' hΓ hΔ <;> apply JEq.lhs_ty <;> apply_assumption; assumption
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
    constructor <;>
    (first
    | apply_assumption
    | {
        intro x hx
        rename Finset ℕ => L
        have ⟨hΓ, hΔ, hL⟩ : x ∉ Γ.dv ∧ x ∉ hΓΔ.trg.dv ∧ x ∉ L
          := by simp only [<-Finset.notMem_union]; exact hx
        repeat rw [Tm.MSubst.Lc.bs0_fvs_singleton (x := x) (hσ := hΓΔ.lc_rhs.anti (by {
          first | (apply JEq.scoped_cf_ty; assumption)
                | (apply JEq.scoped_cf_rhs; assumption)
                | (apply JEq.scoped_cf_lhs; assumption)
        })) (ha := by simp)]
        · apply_assumption
          · exact hL
          · first | apply hΓΔ.lift_one' hΓ hΔ <;> apply JEq.lhs_ty <;> apply_assumption; assumption
                  | exact hΓΔ.lift_one' (A := .nats) hΓ hΔ ⟨1, hΓΔ.trg_ok.nats⟩ ⟨1, hΓΔ.src_ok.nats⟩
        all_goals {
          apply Finset.notMem_mono _ hΔ
          first | (apply JEq.scoped_cf_ty; assumption)
                | (apply JEq.scoped_cf_rhs; assumption)
                | (apply JEq.scoped_cf_lhs; assumption)
        }
      }
    | {
      (try simp only [<-Tm.msubst_fst, <-Tm.msubst_choose, <-Tm.msubst_app_succ])
      repeat first | rw [<-Tm.MSubst.Lc.bs0] | rw [<-Tm.MSubst.Lc.bs0_fvs_empty (ha := by simp)]
      apply_assumption; assumption
      all_goals {
        apply Tm.MSubst.Lc.anti
        · (try simp only [Tm.fvs, Finset.union_subset_iff])
          (try constructorm* _ ∧ _) <;>
          first | (apply JEq.scoped_lhs; assumption)
                -- | (apply JEq.scoped_rhs; assumption)
                | (apply JEq.scoped_cf_lhs ; assumption)
                | (apply JEq.scoped_cf_ty ; assumption)
                -- | (apply JEq.scoped_cf_rhs ; assumption)
                | simp
        · first | apply Ctx.Subst.lc_lhs -- | apply Ctx.Subst.lc_rhs
          assumption
      }
      })
    <;> assumption

theorem Ctx.TyEq.subst_one {Γ Δ : Ctx} {σ : Tm.MSubst} {A B : Tm}
  (hΓΔ : Γ.Subst Δ σ σ) (h : Δ.TyEq A B) : Γ.TyEq (A.msubst σ) (B.msubst σ)
  := have ⟨ℓ, h⟩ := h; ⟨ℓ, h.subst_one hΓΔ⟩

theorem Ctx.IsTy.subst_one {Γ Δ : Ctx} {σ : Tm.MSubst} {A : Tm}
  (hΓΔ : Γ.Subst Δ σ σ) (h : Δ.IsTy A) : Γ.IsTy (A.msubst σ)
  := TyEq.subst_one hΓΔ h

theorem Ctx.Subst.lift_one {Γ Δ : Ctx} {σ : Tm.MSubst}
  (h : Γ.Subst Δ σ σ) {x : ℕ} (hxΓ : x ∉ Γ.dv) (hxΔ : x ∉ Δ.dv) {A : Tm}
  (hΔ : Δ.IsTy A) : (Γ.cons x (A.msubst σ)).Subst (Δ.cons x A) (σ.lift x) (σ.lift x)
  := h.lift_one' hxΓ hxΔ hΔ (hΔ.subst_one h)

theorem Ctx.Subst.set' {Γ Δ : Ctx} {σ τ : Tm.MSubst} {x : ℕ} {A : Tm} {a b : Tm}
  (h : Γ.Subst Δ σ τ) (hxΔ : x ∉ Δ.dv) (hΔ : Δ.IsTy A)
  (hσ : Γ.JEq (A.msubst σ) a b) (hτ : Γ.JEq (A.msubst τ) a b)
  : Γ.Subst (Δ.cons x A) (σ.set x a) (τ.set x b)
  := (h.to_eqOn
      (fun x hx => by simp [Tm.MSubst.get_set]; intro hx'; cases hx'; contradiction)
      (fun x hx => by simp [Tm.MSubst.get_set]; intro hx'; cases hx'; contradiction)).cons' hxΔ hΔ
    (by rw [Tm.msubst_set_eq (hx := Finset.not_mem_subset hΔ.scoped hxΔ)]; simp [hσ])
    (by rw [Tm.msubst_set_eq (hx := Finset.not_mem_subset hΔ.scoped hxΔ)]; simp [hτ])

theorem Ctx.JEq.m0 {Γ : Ctx} {A a b : Tm} (h : Ctx.JEq Γ A a b) {x : ℕ} (hx : x ∉ Γ.dv)
  : Γ.Subst (Γ.cons x A) (a.m0 x) (b.m0 x)
  := (Subst.refl h.ok).set' hx h.regular (by simp [h]) (by simp [h])
