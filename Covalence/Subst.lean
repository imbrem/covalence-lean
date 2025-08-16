import Covalence.Wk
import Covalence.Syntax.Close

--TODO: SubstEq lore...

inductive Ctx.SubstEq : Ctx → Ctx → Tm.MSubst → Tm.MSubst → Prop
  | nil {Γ : Ctx} {σ τ : Tm.MSubst} : Γ.Ok → SubstEq Γ .nil σ τ
  | cons' {Γ Δ : Ctx} {σ τ : Tm.MSubst} {x : ℕ} {A : Tm}
    : Γ.SubstEq Δ σ τ
    → x ∉ Δ.dv
    → Δ.IsTy A
    → Γ.JEq (A.msubst σ) (σ.get x) (τ.get x)
    → Γ.JEq (A.msubst τ) (σ.get x) (τ.get x)
    → Γ.SubstEq (Δ.cons x A) σ τ

theorem Ctx.SubstEq.src_ok {Γ Δ : Ctx} {σ τ : Tm.MSubst} (h : Γ.SubstEq Δ σ τ) : Γ.Ok := by
  induction h <;> assumption

theorem Ctx.SubstEq.trg_ok {Γ Δ : Ctx} {σ τ : Tm.MSubst} (h : Γ.SubstEq Δ σ τ) : Δ.Ok := by
  induction h <;> constructor <;> assumption

theorem Ctx.SubstEq.symm {Γ Δ : Ctx} {σ τ : Tm.MSubst} (h : Γ.SubstEq Δ σ τ) : Γ.SubstEq Δ τ σ := by
  induction h with
  | nil hΓ => exact .nil hΓ
  | cons' hΓΔ hx hΔ hσ hτ IΓΔ => exact IΓΔ.cons' hx hΔ hτ.symm hσ.symm

theorem Ctx.SubstEq.at {Γ Δ : Ctx} {σ τ : Tm.MSubst} (h : Γ.SubstEq Δ σ τ)
  {x : ℕ} {A : Tm} (hA : Δ.At x A) : Γ.JEq (A.msubst σ) (σ x) (τ x) := by
  induction hA <;> cases h <;> apply_assumption; assumption

theorem Ctx.SubstEq.lc_both {Γ Δ : Ctx} {σ τ : Tm.MSubst} (h : Γ.SubstEq Δ σ τ)
  : σ.Lc Δ.dv ∧ τ.Lc Δ.dv := by induction h with
  | nil => simp [dv]
  | cons' _ _ _ h => simp [dv, Tm.MSubst.Lc.union_iff, h.lc_lhs, h.lc_rhs, *]

theorem Ctx.SubstEq.lc_lhs {Γ Δ : Ctx} {σ τ : Tm.MSubst} (h : Γ.SubstEq Δ σ τ) : σ.Lc Δ.dv
  := h.lc_both.1

theorem Ctx.SubstEq.lc_rhs {Γ Δ : Ctx} {σ τ : Tm.MSubst} (h : Γ.SubstEq Δ σ τ) : τ.Lc Δ.dv
  := h.lc_both.2

theorem Ctx.SubstEq.wkIn {Γ Δ Θ : Ctx} {σ τ : Tm.MSubst} (hΓΔ : Γ.Wk Δ) (hΔΘ : Δ.SubstEq Θ σ τ)
  : Γ.SubstEq Θ σ τ := by
  induction hΔΘ with
  | nil _ => exact .nil hΓΔ.src_ok
  | cons' hΔΘ hx hΘ hσ hτ I => exact I.cons' hx hΘ (hσ.wk hΓΔ) (hτ.wk hΓΔ)

theorem Ctx.SubstEq.wk0In {Γ Δ : Ctx} {σ τ : Tm.MSubst}
  (h : Γ.SubstEq Δ σ τ) {x} (hx : x ∉ Γ.dv) {A : Tm} (hA : Γ.IsTy A)
  : (Γ.cons x A).SubstEq Δ σ τ := h.wkIn (hA.lhs_pure_wk0 hx).wk

theorem Ctx.SubstEq.refl {Γ : Ctx} (h : Γ.Ok) : Γ.SubstEq Γ 1 1 := by induction h with
  | nil => exact .nil .nil
  | cons hΓΔ hx hA I =>
    have h' := hΓΔ.cons hx hA;
    exact .cons' (I.wk0In hx hA) hx hA
      (.var h'.zero (by simp; constructor))
      (.var h'.zero (by simp; constructor))

theorem Ctx.SubstEq.to_eqOn {Γ Δ : Ctx}
   {σ τ σ' τ' : Tm.MSubst} (h : Γ.SubstEq Δ σ τ)
   (hσ : σ.EqOn Δ.dv σ') (hτ : τ.EqOn Δ.dv τ') : Γ.SubstEq Δ σ' τ'
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

theorem Ctx.SubstEq.of_wk {Γ Δ : Ctx} (h : Γ.Wk Δ) : Γ.SubstEq Δ 1 1 := (refl h.trg_ok).wkIn h

theorem Ctx.SubstEq.lift_one' {Γ Δ : Ctx} {σ : Tm.MSubst}
  (h : Γ.SubstEq Δ σ σ) {x : ℕ} (hxΓ : x ∉ Γ.dv) (hxΔ : x ∉ Δ.dv) {A : Tm}
  (hΔ : Δ.IsTy A) (hΓ : Γ.IsTy (A.msubst σ))
  : (Γ.cons x (A.msubst σ)).SubstEq (Δ.cons x A) (σ.lift x) (σ.lift x)
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

def Ctx.SubstEq.src {Γ Δ : Ctx} {σ τ : Tm.MSubst} (_ : Γ.SubstEq Δ σ τ) : Ctx := Γ

def Ctx.SubstEq.trg {Γ Δ : Ctx} {σ τ : Tm.MSubst} (_ : Γ.SubstEq Δ σ τ) : Ctx := Δ

theorem Ctx.JEq.subst_one {Γ Δ : Ctx} {σ : Tm.MSubst} {A a b : Tm}
  (hΓΔ : Γ.SubstEq Δ σ σ) (h : Δ.JEq A a b)
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
  | pi_ext_cf hA hB hℓ hf hg hfg IA IB If Ig Ifg =>
    rename Finset ℕ => L
    rename_i ℓ m n A B f g
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
    · exact hℓ
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
  | univ_succ _ Is => exact JEq.univ_succ (Is hΓΔ)
  | univ_max _ _ hℓ hℓ' Im In => exact JEq.univ_max (Im hΓΔ) (In hΓΔ) hℓ hℓ'
  | univ_imax _ _ hℓ hℓ' Im In => exact JEq.univ_imax (Im hΓΔ) (In hΓΔ) hℓ hℓ'
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
                -- | (apply JEq.scoped_cf_ty ; assumption)
                -- | (apply JEq.scoped_cf_rhs ; assumption)
                | simp
        · first | apply Ctx.SubstEq.lc_lhs -- | apply Ctx.SubstEq.lc_rhs
          assumption
      }
      })
    <;> assumption

theorem Ctx.JEq.subst_one_univ {Γ Δ : Ctx} {σ : Tm.MSubst} {ℓ : ℕ} {A B : Tm}
  (hΓΔ : Γ.SubstEq Δ σ σ) (h : Δ.JEq (.univ ℓ) A B)
  : Γ.JEq (.univ ℓ) (A.msubst σ) (B.msubst σ)
  := h.subst_one hΓΔ

theorem Ctx.TyEq.subst_one {Γ Δ : Ctx} {σ : Tm.MSubst} {A B : Tm}
  (hΓΔ : Γ.SubstEq Δ σ σ) (h : Δ.TyEq A B) : Γ.TyEq (A.msubst σ) (B.msubst σ)
  := have ⟨ℓ, h⟩ := h; ⟨ℓ, h.subst_one hΓΔ⟩

theorem Ctx.IsTy.subst_one {Γ Δ : Ctx} {σ : Tm.MSubst} {A : Tm}
  (hΓΔ : Γ.SubstEq Δ σ σ) (h : Δ.IsTy A) : Γ.IsTy (A.msubst σ)
  := TyEq.subst_one hΓΔ h

theorem Ctx.SubstEq.lift_one {Γ Δ : Ctx} {σ : Tm.MSubst}
  (h : Γ.SubstEq Δ σ σ) {x : ℕ} (hxΓ : x ∉ Γ.dv) (hxΔ : x ∉ Δ.dv) {A : Tm}
  (hΔ : Δ.IsTy A) : (Γ.cons x (A.msubst σ)).SubstEq (Δ.cons x A) (σ.lift x) (σ.lift x)
  := h.lift_one' hxΓ hxΔ hΔ (hΔ.subst_one h)

theorem Ctx.SubstEq.set' {Γ Δ : Ctx} {σ τ : Tm.MSubst} {x : ℕ} {A : Tm} {a b : Tm}
  (h : Γ.SubstEq Δ σ τ) (hxΔ : x ∉ Δ.dv) (hΔ : Δ.IsTy A)
  (hσ : Γ.JEq (A.msubst σ) a b) (hτ : Γ.JEq (A.msubst τ) a b)
  : Γ.SubstEq (Δ.cons x A) (σ.set x a) (τ.set x b)
  := (h.to_eqOn
      (fun x hx => by simp [Tm.MSubst.get_set]; intro hx'; cases hx'; contradiction)
      (fun x hx => by simp [Tm.MSubst.get_set]; intro hx'; cases hx'; contradiction)).cons' hxΔ hΔ
    (by rw [Tm.msubst_set_eq (hx := Finset.not_mem_subset hΔ.scoped hxΔ)]; simp [hσ])
    (by rw [Tm.msubst_set_eq (hx := Finset.not_mem_subset hΔ.scoped hxΔ)]; simp [hτ])

theorem Ctx.JEq.m0 {Γ : Ctx} {A a b : Tm} (h : Ctx.JEq Γ A a b) {x : ℕ} (hx : x ∉ Γ.dv)
  : Γ.SubstEq (Γ.cons x A) (a.m0 x) (b.m0 x)
  := (SubstEq.refl h.ok).set' hx h.regular (by simp [h]) (by simp [h])

theorem Ctx.JEq.ms0_one {Γ : Ctx} {A B a b b' : Tm} {x : ℕ}
  (hb : Ctx.JEq (Γ.cons x A) B b b') (ha : Ctx.JEq Γ A a a)
  : Γ.JEq (B.ms0 x a) (b.ms0 x a) (b'.ms0 x a)
  := hb.subst_one (ha.m0 hb.ok.var)

theorem Ctx.JEq.bs0_one {Γ : Ctx} {A B a b b' : Tm} {x : ℕ} (hx : x ∉ B.fvs ∪ b.fvs ∪ b'.fvs)
  (hb : Ctx.JEq (Γ.cons x A) (B.bs0 (.fv x)) (b.bs0 (.fv x)) (b'.bs0 (.fv x)))
  (ha : Ctx.JEq Γ A a a) : Γ.JEq (B.bs0 a) (b.bs0 a) (b'.bs0 a) := by
  simp at hx
  convert hb.ms0_one ha using 1 <;> rw [Tm.ms0_bs0_var_notMem (ha := ha.lc_lhs)] <;> simp [*]

theorem Ctx.JEq.bs0_one_cf {Γ : Ctx} {A B a b b' : Tm} {L : Finset ℕ}
  (hb : ∀ x ∉ L, Ctx.JEq (Γ.cons x A) (B.bs0 (.fv x)) (b.bs0 (.fv x)) (b'.bs0 (.fv x)))
  (ha : Ctx.JEq Γ A a a) : Γ.JEq (B.bs0 a) (b.bs0 a) (b'.bs0 a) := by
  have ⟨x, hx⟩ := Finset.exists_notMem (L ∪ (B.fvs ∪ b.fvs ∪ b'.fvs))
  rw [Finset.notMem_union] at hx
  exact (hb x hx.1).bs0_one hx.2 ha

theorem Ctx.TyEq.bs0_one {Γ : Ctx} {A B B' a : Tm} {x : ℕ} (hx : x ∉ B.fvs ∪ B'.fvs)
  (hb : Ctx.TyEq (Γ.cons x A) (B.bs0 (.fv x)) (B'.bs0 (.fv x)))
  (ha : Ctx.JEq Γ A a a) : Γ.TyEq (B.bs0 a) (B'.bs0 a) := by
  have ⟨ℓ, hb⟩ := hb;
  exact ⟨ℓ, hb.bs0_one (B := .univ ℓ) (by simp [hx]) ha⟩

theorem Ctx.TyEq.bs0_one_cf {Γ : Ctx} {A B a b b' : Tm} {L : Finset ℕ}
  (hb : ∀ x ∉ L, Ctx.JEq (Γ.cons x A) (B.bs0 (.fv x)) (b.bs0 (.fv x)) (b'.bs0 (.fv x)))
  (ha : Ctx.JEq Γ A a a) : Γ.JEq (B.bs0 a) (b.bs0 a) (b'.bs0 a) := by
  have ⟨x, hx⟩ := Finset.exists_notMem (L ∪ (B.fvs ∪ b.fvs ∪ b'.fvs))
  rw [Finset.notMem_union] at hx
  exact (hb x hx.1).bs0_one hx.2 ha

theorem Ctx.JEq.bs0_cf_univ {Γ : Ctx} {n : ℕ} {A B B' a a' : Tm} {L : Finset ℕ}
  (hB : ∀ x ∉ L, Ctx.JEq (Γ.cons x A) (.univ n) (B.bs0 (.fv x)) (B'.bs0 (.fv x)))
  (ha : Ctx.JEq Γ A a a') : Γ.JEq (.univ n) (B.bs0 a) (B'.bs0 a') :=
  have ⟨m, hA⟩ := ha.regular;
  have app_eq
    : Ctx.JEq Γ (.univ n)
      (.app A (.univ n) (.abs (m.imax (n + 1)) A (.univ n) B) a)
      (.app A (.univ n) (.abs (m.imax (n + 1)) A (.univ n) B') a')
    := .app_cf hA (fun x hx => (hB x hx).ok.univ) rfl
                  (.abs_cf hA (fun x hx => (hB x hx).ok.univ) rfl hB) ha hA.ok.univ
  have hba : Ctx.JEq Γ (.univ n)
              (.app A (.univ n) (.abs (m.imax (n + 1)) A (.univ n) B) a) (B.bs0 a)
    := .beta_abs_cf (L := L ∪ Γ.dv) hA
        (fun x hx => by simp at hx; exact (hA.lhs_cons hx.2).ok.univ)
        rfl
        (fun x hx => by simp at hx; exact (hB x hx.1).lhs) ha.lhs hA.ok.univ
        (ha.lhs.bs0_one_cf (B := .univ n) (fun x hx => (hB x hx).lhs))
  have hba' : Ctx.JEq Γ (.univ n)
                (.app A (.univ n)
                      (.abs (m.imax (n + 1)) A (.univ n) B') a') (B'.bs0 a')
    := .beta_abs_cf (L := L ∪ Γ.dv) hA
        (fun x hx => by simp at hx; exact (hA.lhs_cons hx.2).ok.univ)
        rfl
        (fun x hx => by simp at hx; exact (hB x hx.1).rhs) ha.rhs hA.ok.univ
        (ha.rhs.bs0_one_cf (B := .univ n) (fun x hx => (hB x hx).rhs))
  hba.symm.trans (app_eq.trans hba')

def Ctx.Ok.fromName0 {Γ : Ctx} {x : ℕ} {A : Tm} (hΓ : (Γ.cons x A).Ok) (y : ℕ) (hy : y ∉ Γ.dv)
  : (Γ.cons x A).SubstEq (Γ.cons y A) ((Tm.fv x).m0 y) ((Tm.fv x).m0 y) :=
  have hset : Tm.MSubst.EqOn Γ.dv 1 (.set 1 y (.fv x)) := fun z hz => by
    simp [Tm.MSubst.get_set]; intro hz; cases hz; exact (hy hz).elim
  have hA : (Γ.cons x A).JEq
              (Tm.msubst (Tm.MSubst.set 1 y (Tm.fv x)) A)
              ((Tm.MSubst.set 1 y (Tm.fv x)).get y)
              ((Tm.MSubst.set 1 y (Tm.fv x)).get y) := by
    simp only [Tm.MSubst.get_set_self]
    rw [Tm.msubst_eqOn_subset_one hset.symm _ hΓ.ty.scoped]
    exact .var hΓ.zero .here
  .cons' (.wk0In (.to_eqOn (.refl hΓ.tail) hset hset) hΓ.var hΓ.ty) hy hΓ.ty hA hA

def Ctx.Ok.toName0 {Γ : Ctx} {x : ℕ} {A : Tm} (hΓ : (Γ.cons x A).Ok) (y : ℕ) (hy : y ∉ Γ.dv)
  : (Γ.cons y A).SubstEq (Γ.cons x A) ((Tm.fv y).m0 x) ((Tm.fv y).m0 x) :=
  fromName0 (hΓ.tail.cons hy hΓ.ty) x hΓ.var

theorem Ctx.JEq.rename0' {Γ : Ctx} {x : ℕ} {A B a b : Tm}
  (h : Ctx.JEq (Γ.cons x A) B a b)
  : ∀y ∉ Γ.dv, Ctx.JEq (Γ.cons y A) (B.ms0 x (.fv y)) (a.ms0 x (.fv y)) (b.ms0 x (.fv y)) := by
  intro y hy
  exact h.subst_one (h.ok.toName0 y hy)

theorem Ctx.JEq.rename0 {Γ : Ctx} {x : ℕ} {A B a b : Tm}
  (h : Ctx.JEq (Γ.cons x A) (B.bs0 (.fv x)) (a.bs0 (.fv x)) (b.bs0 (.fv x)))
  (hB : x ∉ B.fvs) (ha : x ∉ a.fvs) (hb : x ∉ b.fvs)
  : ∀y ∉ Γ.dv, Ctx.JEq (Γ.cons y A) (B.bs0 (.fv y)) (a.bs0 (.fv y)) (b.bs0 (.fv y)) := by
  intro y hy
  convert h.rename0' y hy using 1
  <;> exact (Tm.ms0_bs0_var_notMem _ _ (by simp [Tm.bvi]) x (by assumption)).symm

theorem Ctx.TyEq.rename0 {Γ : Ctx} {x : ℕ} {A B B' : Tm}
  (h : Ctx.TyEq (Γ.cons x A) (B.bs0 (.fv x)) (B'.bs0 (.fv x)))
  (hB : x ∉ B.fvs) (hB' : x ∉ B'.fvs)
  : ∀y ∉ Γ.dv, Ctx.TyEq (Γ.cons y A) (B.bs0 (.fv y)) (B'.bs0 (.fv y)) := by
  intro y hy
  convert h.subst_one (h.ok.toName0 y hy) using 1
  <;> exact (Tm.ms0_bs0_var_notMem _ _ (by simp [Tm.bvi]) x (by assumption)).symm

theorem Ctx.JEq.univ_of_cf {Γ : Ctx} {A B C : Tm} {L : Finset ℕ}
  (h : ∀ x ∉ L, Ctx.TyEq (Γ.cons x A) (B.bs0 (.fv x)) (C.bs0 (.fv x)))
  : ∃ℓ, ∀ x ∉ Γ.dv, Ctx.JEq (Γ.cons x A) (.univ ℓ) (B.bs0 (.fv x)) (C.bs0 (.fv x)) :=
  have ⟨x, hx⟩ := Finset.exists_notMem (L ∪ Γ.dv ∪ B.fvs ∪ C.fvs)
  have ⟨hL, hΓ, hB, hC⟩ : x ∉ L ∧ x ∉ Γ.dv ∧ x ∉ B.fvs ∧ x ∉ C.fvs
    := by simp only [Finset.notMem_union] at hx; simp only [not_false_eq_true, and_self, hx]
  have ⟨ℓ, h'⟩ := h x hL;
  ⟨ℓ, h'.rename0 (B := .univ ℓ) (by simp) hB hC⟩

theorem Ctx.JEq.univ_cf_iff {Γ : Ctx} {A B C : Tm}
  : (∀ x ∉ Γ.dv, Ctx.TyEq (Γ.cons x A) (B.bs0 (.fv x)) (C.bs0 (.fv x)))
  ↔ ∃ℓ, ∀ x ∉ Γ.dv, Ctx.JEq (Γ.cons x A) (.univ ℓ) (B.bs0 (.fv x)) (C.bs0 (.fv x)) :=
  ⟨JEq.univ_of_cf, fun ⟨ℓ, h⟩ x hx => ⟨ℓ, h x hx⟩⟩

theorem Ctx.TyEq.bs0_cf {Γ : Ctx} {A B B' a a' : Tm} {L : Finset ℕ}
  (hB : ∀ x ∉ L, Ctx.TyEq (Γ.cons x A) (B.bs0 (.fv x)) (B'.bs0 (.fv x)))
  (ha : Ctx.JEq Γ A a a') : Γ.TyEq (B.bs0 a) (B'.bs0 a') :=
  have ⟨ℓ, hB⟩ := JEq.univ_of_cf hB; ⟨ℓ, Ctx.JEq.bs0_cf_univ hB ha⟩

theorem Ctx.JEq.bs0_cf {Γ : Ctx} {A B a a' b b' : Tm} {L : Finset ℕ}
  (hb : ∀ x ∉ L, Ctx.JEq (Γ.cons x A) (B.bs0 (.fv x)) (b.bs0 (.fv x)) (b'.bs0 (.fv x)))
  (ha : Ctx.JEq Γ A a a') : Γ.JEq (B.bs0 a) (b.bs0 a) (b'.bs0 a') := by
  have ⟨m, hA⟩ := ha.regular;
  have ⟨n, hB⟩ := JEq.univ_of_cf (fun x hx => (hb x hx).regular)
  have hB' := JEq.bs0_cf_univ hB ha
  have hB : ∀x ∉ L ∪ Γ.dv, Ctx.JEq (Γ.cons x A) (.univ n) (B.bs0 (.fv x)) (B.bs0 (.fv x))
    := fun x hx => by simp at hx; exact hB x hx.2
  have hb : ∀x ∉ L ∪ Γ.dv, Ctx.JEq (Γ.cons x A) (B.bs0 (.fv x)) (b.bs0 (.fv x)) (b'.bs0 (.fv x))
    := fun x hx => by simp at hx; exact hb x hx.1
  have app_eq
    : Ctx.JEq Γ (B.bs0 a) (.app A B (.abs (m.imax n) A B b) a)
                          (.app A B (.abs (m.imax n) A B b') a')
    := .app_cf hA hB rfl (.abs_cf hA hB rfl hb) ha hB'.lhs
  have hba : Ctx.JEq Γ (B.bs0 a) (.app A B (.abs (m.imax n) A B b) a) (b.bs0 a)
    := .beta_abs_cf hA hB rfl
        (fun x hx => (hb x hx).lhs) ha.lhs (ha.lhs.bs0_one_cf (B := .univ n) hB)
        (ha.lhs.bs0_one_cf (fun x hx => (hb x hx).lhs))
  have hba' : Ctx.JEq Γ (B.bs0 a') (.app A B (.abs (m.imax n) A B b') a') (b'.bs0 a')
    := .beta_abs_cf hA hB rfl
        (fun x hx => (hb x hx).rhs) ha.rhs (ha.rhs.bs0_one_cf (B := .univ n) hB)
        (ha.rhs.bs0_one_cf (fun x hx => (hb x hx).rhs))
  exact hba.symm.trans (app_eq.trans (hB'.symm.cast hba'))
