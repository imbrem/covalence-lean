import Covalence.Subst

inductive Ctx.HasTy : Ctx → Tm → Tm → Prop
  | univ {Γ : Ctx} {ℓ : ℕ} : Γ.Ok → HasTy Γ (.univ (ℓ + 1)) (.univ ℓ)
  | var {Γ : Ctx} {x : ℕ} {A : Tm} : Γ.Ok → Γ.At x A → HasTy Γ A (.fv x)
  | unit {Γ : Ctx} {ℓ : ℕ} : Γ.Ok → HasTy Γ (.univ ℓ) (.unit ℓ)
  | nil {Γ : Ctx} {ℓ : ℕ} : Γ.Ok → HasTy Γ (.unit ℓ) (.nil ℓ)
  | empty {Γ : Ctx} {ℓ : ℕ} : Γ.Ok → HasTy Γ (.univ ℓ) (.empty ℓ)
  | eqn {Γ : Ctx} {ℓ : ℕ} {A a b : Tm}
    : HasTy Γ (.univ ℓ) A
    → HasTy Γ A a
    → HasTy Γ A b
    → HasTy Γ (.univ 0) (.eqn A a b)
  | pi_cf {Γ : Ctx} {ℓ m n : ℕ} {A B : Tm} {L : Finset ℕ}
    : HasTy Γ (.univ m) A
    → (∀ x ∉ L, HasTy (Γ.cons x A) (.univ n) (B.bs0 (.fv x)))
    → (ℓ = m.imax n)
    → HasTy Γ (.univ ℓ) (.pi A B)
  | app_cf {Γ : Ctx} {m n : ℕ} {A B Ba f a : Tm} {L : Finset ℕ}
    : HasTy Γ (.univ m) A
    → (∀ x ∉ L, HasTy (Γ.cons x A) (.univ n) (B.bs0 (.fv x)))
    → HasTy Γ (.pi A B) f
    → HasTy Γ A a
    → JEq Γ (.univ n) (B.bs0 a) Ba
    → HasTy Γ Ba (.app A B f a)
  | abs_cf {Γ : Ctx} {m n : ℕ} {A B b : Tm} {L : Finset ℕ}
    : HasTy Γ (.univ m) A
    → (∀ x ∉ L, HasTy (Γ.cons x A) (.univ n) (B.bs0 (.fv x)))
    → (∀ x ∉ L, HasTy (Γ.cons x A) (B.bs0 (.fv x)) (b.bs0 (.fv x)))
    → HasTy Γ (.pi A B) (.abs A B b)
  | sigma_cf {Γ : Ctx} {ℓ m n : ℕ} {A B : Tm} {L : Finset ℕ}
    : HasTy Γ (.univ m) A
    → (∀ x ∉ L, HasTy (Γ.cons x A) (.univ n) (B.bs0 (.fv x)))
    → (ℓ = m ⊔ n)
    → HasTy Γ (.univ ℓ) (.sigma A B)
  | pair_cf {Γ : Ctx} {m n : ℕ} {A B a b : Tm} {L : Finset ℕ}
    : HasTy Γ (.univ m) A
    → (∀ x ∉ L, HasTy (Γ.cons x A) (.univ n) (B.bs0 (.fv x)))
    → HasTy Γ A a
    → HasTy Γ (B.bs0 a) b
    → HasTy Γ (.sigma A B) (.pair A B a b)
  | fst_cf {Γ : Ctx} {m n : ℕ} {A B e : Tm} {L : Finset ℕ}
    : HasTy Γ (.univ m) A
    → (∀ x ∉ L, HasTy (Γ.cons x A) (.univ n) (B.bs0 (.fv x)))
    → HasTy Γ (.sigma A B) e
    → HasTy Γ A (.fst A B e)
  | snd_cf {Γ : Ctx} {m n : ℕ} {A B Ba e : Tm} {L : Finset ℕ}
    : HasTy Γ (.univ m) A
    → (∀ x ∉ L, HasTy (Γ.cons x A) (.univ n) (B.bs0 (.fv x)))
    → HasTy Γ (.sigma A B) e
    → JEq Γ (.univ n) (B.bs0 (.fst A B e)) Ba
    → HasTy Γ Ba (.snd A B e)
  | dite_cf {Γ : Ctx} {ℓ : ℕ} {φ A a b : Tm} {L : Finset ℕ}
    : HasTy Γ (.univ 0) φ
    → HasTy Γ (.univ ℓ) A
    → (∀ x ∉ L, HasTy (Γ.cons x φ) A a)
    → (∀ x ∉ L, HasTy (Γ.cons x (.not φ)) A b)
    → HasTy Γ A (.dite φ A a b)
  | trunc {Γ : Ctx} {ℓ : ℕ} {A : Tm}
    : HasTy Γ (.univ ℓ) A
    → HasTy Γ (.univ 0) (.trunc A)
  | choose_cf {Γ : Ctx} {ℓ} {A φ : Tm} {L : Finset ℕ}
    : HasTy Γ (.univ ℓ) A
    → JEq Γ (.univ 0) (.trunc A) (.unit 0)
    → (∀ x ∉ L, HasTy (Γ.cons x A) (.univ 0) (φ.bs0 (.fv x)))
    → HasTy Γ A (.choose A φ)
  | nats {Γ : Ctx} : Γ.Ok → HasTy Γ (.univ 1) .nats
  | zero {Γ : Ctx} : Γ.Ok → HasTy Γ .nats .zero
  | succ {Γ : Ctx} : Γ.Ok → HasTy Γ (.pi .nats .nats) .succ
  | natrec_cf {Γ : Ctx} {ℓ : ℕ} {C n z s Cn : Tm} {L : Finset ℕ}
    : (∀ x ∉ L, HasTy (Γ.cons x .nats) (.univ ℓ) (C.bs0 (.fv x)))
    → HasTy Γ .nats n
    → HasTy Γ (C.bs0 .zero) z
    → (∀ x ∉ L,
        HasTy (Γ.cons x .nats) (.pi (C.bs0 (.fv x))
              (C.bs0 (.app .nats .nats .succ (.fv x)))) (s.bs0 (.fv x)))
    → JEq Γ (.univ ℓ) (C.bs0 n) Cn
    → HasTy Γ Cn (.natrec C n z s)
  | cast {Γ : Ctx} {A B a : Tm}
    : TyEq Γ A B
    → HasTy Γ A a
    → HasTy Γ B a

-- `has_ty(Γ, a, A) -> bool`
notation Γ " ⊢ " a " : " A => Ctx.HasTy Γ A a

theorem Ctx.HasTy.refl {Γ : Ctx} {A a : Tm} (h : Ctx.HasTy Γ A a) : Γ.JEq A a a
  := by induction h with
  | cast hA ha Ia => exact hA.cast Ia
  | zero => rw [<-ok_iff_zero] ; assumption
  | _ =>
    constructor <;>
    (try simp only [<-ok_iff_zero]) <;>
    assumption

theorem Ctx.HasTy.is_ty {Γ : Ctx} {ℓ : ℕ} {A : Tm} (h : Ctx.HasTy Γ (.univ ℓ) A) : Γ.IsTy A
  := ⟨_, h.refl⟩

theorem Ctx.HasTy.ok {Γ : Ctx} {A a : Tm} (h : Ctx.HasTy Γ A a) : Γ.Ok := h.refl.ok

theorem Ctx.HasTy.lc_ty {Γ : Ctx} {A a : Tm} (h : Ctx.HasTy Γ A a) : A.bvi = 0
  := h.refl.lc_ty

theorem Ctx.HasTy.lc_tm {Γ : Ctx} {A a : Tm} (h : Ctx.HasTy Γ A a) : a.bvi = 0
  := h.refl.lc_lhs

theorem Ctx.HasTy.not {Γ : Ctx} {ℓ : ℕ} {φ : Tm} (h : Ctx.HasTy Γ (.univ ℓ) φ)
  : Γ.HasTy (.univ 0) φ.not
  :=  .pi_cf (L := Γ.dv) h (fun _ hx => .empty (h.ok.cons hx h.is_ty)) rfl

theorem Ctx.Var.ty {Γ : Ctx} {x : ℕ} {A : Tm} (h : Γ.Var x A) : Γ.HasTy A (.fv x)
  := have ⟨_, hΓ, hX⟩ := h; (HasTy.var hX.ok hΓ).cast hX

theorem Ctx.HasTy.wk {Γ Δ : Ctx} (h : Γ.Wk Δ) {a A : Tm} (h : Δ.HasTy a A) : Γ.HasTy a A
  := by induction h generalizing Γ with
  | cast hA ha I => exact (I h).cast (hA.wk h)
  | var hΓ hA => exact (h.at hA).ty
  | _ =>
    constructor <;> (first | exact h.src_ok | (try apply JEq.wk) <;> apply_assumption | {
      rename Finset ℕ => L
      intro x hx
      have ⟨hL, hΓ⟩ : x ∉ L ∧ x ∉ Γ.dv := by rw [<-Finset.notMem_union]; exact hx
      apply_assumption <;> (first | assumption | apply Wk.lift) <;> first
        | assumption | (apply HasTy.is_ty; (try apply not) <;> first | assumption | constructor)
      <;> exact h.trg_ok
    }) <;> assumption

theorem Ctx.HasTy.wk0
  {Γ : Ctx} {A a : Tm} (h : Γ.HasTy A a)
  {x : ℕ} {B C : Tm} (hx : x ∉ Γ.dv) (hB : Γ.TyEq B C) : (Γ.cons x B).HasTy A a
  := h.wk (hB.lhs_pure_wk0 hx).wk

theorem Ctx.HasTy.wk0'
  {Γ : Ctx} {A a : Tm} (h : Γ.HasTy A a)
  {x : ℕ} {B C : Tm} (hx : x ∉ Γ.dv) (hB : Γ.TyEq B C) : (Γ.cons x B).HasTy A (a.bs0 (.fv x))
  := by convert h.wk0 hx hB using 1; rw [Tm.bs0, Tm.bsubst_lc]; exact h.refl.lc_lhs

theorem Ctx.HasTy.wk1
  {Γ : Ctx} {y : ℕ} {Y A a : Tm} (h : (Γ.cons y Y).HasTy A a)
  {x : ℕ} {B C : Tm} (hx : x ∉ {y} ∪ Γ.dv) (hB : Γ.TyEq B C) : ((Γ.cons x B).cons y Y).HasTy A a
  := h.wk (hB.lhs_pure_wk1
    (by simp at hx; exact hx.2)
    (by simp at hx; simp [h.ok.var, Ne.symm hx.1]) h.ok.ty).wk

theorem Ctx.HasTy.to_cf_dv {Γ : Ctx} {A B a : Tm} (h : Γ.HasTy A a) (hB : Γ.IsTy B)
  : ∀x ∉ Γ.dv, (Γ.cons x B).HasTy (A.bs0 (.fv x)) (a.bs0 (.fv x))
  := fun x hx => by
    convert h.wk0 hx hB using 1
    · rw [Tm.bs0, Tm.bsubst_lc]; exact h.refl.lc_ty
    · rw [Tm.bs0, Tm.bsubst_lc]; exact h.refl.lc_lhs

theorem Ctx.HasTy.to_cf_dv' {Γ : Ctx} {A B a : Tm} (h : Γ.HasTy A a) (hB : Γ.IsTy B)
  : ∀x ∉ Γ.dv, (Γ.cons x B).HasTy A a
  := fun _ hx => h.wk0 hx hB

theorem Ctx.HasTy.cast0
  {Γ : Ctx} {x : ℕ} {B C a : Tm} (h : (Γ.cons x B).HasTy C a)
  {A : Tm} (hB : Γ.TyEq A B) : (Γ.cons x A).HasTy C a
  := h.wk (hB.ok.wk.lift h.ok.var hB)

theorem Ctx.HasTy.pi_k {Γ : Ctx} {ℓ m n : ℕ} {A B : Tm}
  (hA : Γ.HasTy (.univ m) A) (hB : Γ.HasTy (.univ n) B) (hℓ : ℓ = m.imax n)
  : Γ.HasTy (.univ ℓ) (.pi A B)
  := .pi_cf hA (hB.to_cf_dv hA.refl.ty_eq) hℓ

theorem Ctx.HasTy.app_k {Γ : Ctx} {m n : ℕ} {A B f a : Tm}
  (hA : Γ.HasTy (.univ m) A) (hB : Γ.HasTy (.univ n) B)
  (hf : Γ.HasTy (.pi A B) f) (ha : Γ.HasTy A a)
  : Γ.HasTy B (.app A B f a)
  := .app_cf hA (hB.to_cf_dv hA.refl.ty_eq) hf ha (by
    convert hB.refl; rw [Tm.bs0, Tm.bsubst_lc]; exact hB.refl.lc_lhs)

theorem Ctx.HasTy.abs_k {Γ : Ctx} {m n : ℕ} {A B b : Tm}
  (hA : Γ.HasTy (.univ m) A) (hB : Γ.HasTy (.univ n) B) (hb : Γ.HasTy B b)
  : Γ.HasTy (.pi A B) (.abs A B b)
  := .abs_cf hA (hB.to_cf_dv hA.refl.ty_eq) (hb.to_cf_dv hA.refl.ty_eq)

inductive Ctx.Subst : Ctx → Ctx → Tm.MSubst → Prop
  | nil {Γ : Ctx} {σ : Tm.MSubst} : Γ.Ok → Subst Γ .nil σ
  | cons' {Γ Δ : Ctx} {σ : Tm.MSubst} {x : ℕ} {A : Tm}
    : Γ.Subst Δ σ
    → x ∉ Δ.dv
    → Δ.IsTy A
    → Γ.HasTy (A.msubst σ) (σ.get x)
    → Γ.Subst (Δ.cons x A) σ

theorem Ctx.Subst.at {Γ Δ : Ctx} {σ : Tm.MSubst} (h : Γ.Subst Δ σ)
  {x : ℕ} {A : Tm} (hA : Δ.At x A) : Γ.HasTy (A.msubst σ) (σ x) := by
  induction hA <;> cases h <;> apply_assumption; assumption

theorem Ctx.Subst.refl {Γ Δ : Ctx} {σ : Tm.MSubst} (h : Γ.Subst Δ σ) : Γ.SubstEq Δ σ σ
  := by induction h <;> constructor <;> (first | apply HasTy.refl | apply_assumption) <;> assumption

def Ctx.Subst.src {Γ Δ : Ctx} {σ : Tm.MSubst} (_ : Γ.Subst Δ σ) : Ctx := Γ

def Ctx.Subst.trg {Γ Δ : Ctx} {σ : Tm.MSubst} (_ : Γ.Subst Δ σ) : Ctx := Δ

theorem Ctx.Subst.src_ok {Γ Δ : Ctx} {σ : Tm.MSubst} (h : Γ.Subst Δ σ) : Γ.Ok := by
  induction h <;> assumption

theorem Ctx.Subst.trg_ok {Γ Δ : Ctx} {σ : Tm.MSubst} (h : Γ.Subst Δ σ) : Δ.Ok := by
  induction h <;> constructor <;> assumption

theorem Ctx.JEq.subst {Γ Δ : Ctx} {σ : Tm.MSubst} {A a b : Tm}
  (hΓΔ : Γ.Subst Δ σ) (h : Δ.JEq A a b) : Γ.JEq (A.msubst σ) (a.msubst σ) (b.msubst σ)
  := h.subst_one hΓΔ.refl

theorem Ctx.JEq.subst_univ {Γ Δ : Ctx} {σ : Tm.MSubst} {ℓ : ℕ} {A B : Tm}
  (hΓΔ : Γ.Subst Δ σ) (h : Δ.JEq (.univ ℓ) A B)
  : Γ.JEq (.univ ℓ) (A.msubst σ) (B.msubst σ)
  := h.subst hΓΔ

theorem Ctx.JEq.subst_level {Γ Δ : Ctx} {σ : Tm.MSubst} {ℓ m n : ℕ}
  (hΓΔ : Γ.Subst Δ σ) (h : Δ.JEq (.univ ℓ) (.univ m) (.univ n))
  : Γ.JEq (.univ ℓ) (.univ m) (.univ n)
  := h.subst hΓΔ

theorem Ctx.TyEq.subst {Γ Δ : Ctx} {σ : Tm.MSubst} {A B : Tm}
  (hΓΔ : Γ.Subst Δ σ) (h : Δ.TyEq A B) : Γ.TyEq (A.msubst σ) (B.msubst σ)
  := have ⟨ℓ, h⟩ := h; ⟨ℓ, h.subst hΓΔ⟩

theorem Ctx.IsTy.subst {Γ Δ : Ctx} {σ : Tm.MSubst} {A : Tm}
  (hΓΔ : Γ.Subst Δ σ) (h : Δ.IsTy A) : Γ.IsTy (A.msubst σ)
  := TyEq.subst hΓΔ h

theorem Ctx.Subst.lc {Γ Δ : Ctx} {σ : Tm.MSubst} (h : Γ.Subst Δ σ)
  : σ.Lc Δ.dv := h.refl.lc_lhs

theorem Ctx.Subst.wkIn {Γ Δ Θ : Ctx} {σ : Tm.MSubst} (hΓΔ : Γ.Wk Δ) (hΔΘ : Δ.Subst Θ σ)
  : Γ.Subst Θ σ := by
  induction hΔΘ with
  | nil _ => exact .nil hΓΔ.src_ok
  | cons' hΔΘ hx hΘ hσ I => exact I.cons' hx hΘ (hσ.wk hΓΔ)

theorem Ctx.Subst.wk0In {Γ Δ : Ctx} {σ : Tm.MSubst}
  (h : Γ.Subst Δ σ) {x} (hx : x ∉ Γ.dv) {A : Tm} (hA : Γ.IsTy A)
  : (Γ.cons x A).Subst Δ σ := h.wkIn (hA.lhs_pure_wk0 hx).wk

theorem Ctx.Subst.one {Γ : Ctx} (h : Γ.Ok) : Γ.Subst Γ 1 := by induction h with
  | nil => exact .nil .nil
  | cons hΓΔ hx hA I =>
    have h' := hΓΔ.cons hx hA;
    exact .cons' (I.wk0In hx hA) hx hA
      (.var h' (by simp; constructor))

theorem Ctx.Subst.to_eqOn {Γ Δ : Ctx}
   {σ σ' : Tm.MSubst} (h : Γ.Subst Δ σ)
   (hσ : σ.EqOn Δ.dv σ') : Γ.Subst Δ σ'
  := by induction h with
  | nil hΓ => exact .nil hΓ
  | cons' hΓΔ hx hΔ hσ' IΓΔ =>
    simp only [Tm.MSubst.EqOn.union_iff, Tm.MSubst.EqOn.singleton_iff, Ctx.dv] at *
    apply (IΓΔ hσ.2).cons' hx hΔ
    · convert hσ' using 1
      · rw [Tm.msubst_eqOn_subset (h := hσ.2.symm)]
        exact hΔ.scoped
      · exact hσ.1.symm

theorem Ctx.Subst.of_wk {Γ Δ : Ctx} (h : Γ.Wk Δ) : Γ.Subst Δ 1 := (one h.trg_ok).wkIn h

theorem Ctx.Subst.lift' {Γ Δ : Ctx} {σ : Tm.MSubst}
  (h : Γ.Subst Δ σ) {x : ℕ} (hxΓ : x ∉ Γ.dv) (hxΔ : x ∉ Δ.dv) {A : Tm}
  (hΔ : Δ.IsTy A) (hΓ : Γ.IsTy (A.msubst σ))
  : (Γ.cons x (A.msubst σ)).Subst (Δ.cons x A) (σ.lift x)
  := by
    apply ((h.wk0In hxΓ hΓ).to_eqOn (σ.lift_eqOn_of_notMem _ _ hxΔ)).cons' hxΔ hΔ
    · simp only [Tm.MSubst.get_lift_self]
      apply HasTy.var
      · exact (hΓ.cons hxΓ)
      · rw [Tm.msubst_lift_eq (hx := Finset.not_mem_subset hΔ.scoped hxΔ)]
        constructor

theorem Ctx.HasTy.subst {Γ Δ : Ctx} {σ} (hΓΔ : Γ.Subst Δ σ) {A a : Tm} (h : Δ.HasTy A a)
  : Γ.HasTy (A.msubst σ) (a.msubst σ) := by
  induction h generalizing Γ σ with
  | var hΓ hA => exact hΓΔ.at hA
  | dite_cf hφ hA ha hb Iφ IA Ia Ib =>
    rename Finset ℕ => L
    apply (Iφ hΓΔ).dite_cf (IA hΓΔ)
    all_goals {
      intro x hx
      have ⟨hΓ, hΔ, hL⟩ : x ∉ Γ.dv ∧ x ∉ hΓΔ.trg.dv ∧ x ∉ L
          := by simp only [<-Finset.notMem_union]; exact hx
      conv =>
        arg 2
        rw [<-Tm.msubst_lift_eq σ (x := x) (hx := by
          apply Finset.notMem_mono _ hΔ
          apply JEq.scoped_lhs
          apply HasTy.refl
          assumption)]
        skip
      conv =>
        arg 3
        rw [<-Tm.msubst_lift_eq σ (x := x) (hx := by
          apply Finset.notMem_mono _ hΔ
          apply JEq.scoped_cf_lhs'
          intros
          apply HasTy.refl
          apply_assumption
          assumption)]
        skip
      apply_assumption
      · exact hL
      · (first | apply hΓΔ.lift' hΓ hΔ | apply hΓΔ.lift' (A := Tm.not _) hΓ hΔ)
        <;> apply JEq.lhs_ty <;> ((try apply JEq.not); apply HasTy.refl; apply_assumption)
            ; assumption
    }
  | choose_cf hA ht hφ Ia Iφ => exact (Ia hΓΔ).choose_cf (ht.subst hΓΔ) (fun x hx => by
        rename Finset ℕ => L
        have ⟨hΓ, hΔ, hL⟩ : x ∉ Γ.dv ∧ x ∉ hΓΔ.trg.dv ∧ x ∉ L
          := by simp only [<-Finset.notMem_union]; exact hx
        repeat rw [Tm.MSubst.Lc.bs0_fvs_singleton (x := x) (hσ := hΓΔ.lc.anti (by {
          (apply JEq.scoped_cf_lhs; intros; apply HasTy.refl; apply_assumption; assumption)
        })) (ha := by simp)]
        · apply_assumption
          · exact hL
          · first | apply hΓΔ.lift' hΓ hΔ
                    <;> (apply JEq.lhs_ty <;> (try apply HasTy.refl) <;> apply_assumption)
                    ; assumption
        all_goals {
          apply Finset.notMem_mono _ hΔ
          apply JEq.scoped_cf_lhs; intros; apply HasTy.refl; apply_assumption; assumption
        }
    )
  | cast hA ha Ia => exact (Ia hΓΔ).cast (hA.subst hΓΔ)
  | _ =>
    constructor <;> first
    | exact hΓΔ.src_ok
    | apply_assumption <;> assumption
    | {
        intro x hx
        rename Finset ℕ => L
        have ⟨hΓ, hΔ, hL⟩ : x ∉ Γ.dv ∧ x ∉ hΓΔ.trg.dv ∧ x ∉ L
          := by simp only [<-Finset.notMem_union]; exact hx
        repeat rw [Tm.MSubst.Lc.bs0_fvs_singleton (x := x) (hσ := hΓΔ.lc.anti (by {
          first | (apply JEq.scoped_cf_ty; intros;
                    apply HasTy.refl; apply_assumption; assumption)
                | (apply JEq.scoped_cf_lhs; intros;
                    apply HasTy.refl; apply_assumption; assumption)
        })) (ha := by simp)]
        · apply_assumption
          · exact hL
          · first | apply hΓΔ.lift' hΓ hΔ
                    <;> (apply JEq.lhs_ty <;> (try apply HasTy.refl) <;> apply_assumption)
                    ; assumption
                  | exact hΓΔ.lift' (A := .nats) hΓ hΔ ⟨1, hΓΔ.trg_ok.nats⟩ ⟨1, hΓΔ.src_ok.nats⟩
        all_goals {
          apply Finset.notMem_mono _ hΔ
          first | (apply JEq.scoped_cf_ty; intros; apply HasTy.refl; apply_assumption; assumption)
                | (apply JEq.scoped_cf_lhs; intros; apply HasTy.refl; apply_assumption; assumption)
        }
      }
    | {
      (try simp only [<-Tm.msubst_fst])
      repeat first | rw [<-Tm.MSubst.Lc.bs0] | rw [<-Tm.MSubst.Lc.bs0_fvs_empty (ha := by simp)]
      (first | apply JEq.subst_univ | apply_assumption) <;> assumption
      all_goals {
        apply Tm.MSubst.Lc.anti
        · (try simp only [Tm.fvs, Finset.union_subset_iff])
          (try constructorm* _ ∧ _) <;>
          first | (apply JEq.scoped_cf_lhs; intros; apply HasTy.refl; apply_assumption; assumption)
                | (apply JEq.scoped_lhs; apply HasTy.refl; apply_assumption; try assumption)
        · first | apply Ctx.Subst.lc
          assumption
      }
    }

theorem Ctx.Subst.set' {Γ Δ : Ctx} {σ : Tm.MSubst} {x : ℕ} {A : Tm} {a : Tm}
  (h : Γ.Subst Δ σ) (hxΔ : x ∉ Δ.dv) (hΔ : Δ.IsTy A)
  (hσ : Γ.HasTy (A.msubst σ) a)
  : Γ.Subst (Δ.cons x A) (σ.set x a)
  := (h.to_eqOn
      (fun x hx => by simp [Tm.MSubst.get_set]; intro hx'; cases hx'; contradiction)
      ).cons' hxΔ hΔ
    (by rw [Tm.msubst_set_eq (hx := Finset.not_mem_subset hΔ.scoped hxΔ)]; simp [hσ])

theorem Ctx.HasTy.regular {Γ : Ctx} {A a : Tm} (h : Ctx.HasTy Γ A a) : Γ.IsTy A
  := h.refl.regular

theorem Ctx.HasTy.m0 {Γ : Ctx} {A a : Tm} (h : Ctx.HasTy Γ A a) {x : ℕ} (hx : x ∉ Γ.dv)
  : Γ.Subst (Γ.cons x A) (a.m0 x)
  := (Subst.one h.ok).set' hx h.regular (by simp [h])

theorem Ctx.HasTy.ms0_one {Γ : Ctx} {A B a b : Tm} {x : ℕ}
  (hb : Ctx.HasTy (Γ.cons x A) B b) (ha : Ctx.HasTy Γ A a)
  : Γ.HasTy (B.ms0 x a) (b.ms0 x a)
  := hb.subst (ha.m0 hb.ok.var)

theorem Ctx.HasTy.bs0 {Γ : Ctx} {A B a b : Tm} {x : ℕ} (hx : x ∉ B.fvs ∪ b.fvs)
  (hb : Ctx.HasTy (Γ.cons x A) (B.bs0 (.fv x)) (b.bs0 (.fv x)))
  (ha : Ctx.HasTy Γ A a) : Γ.HasTy (B.bs0 a) (b.bs0 a) := by
  simp at hx
  convert hb.ms0_one ha using 1 <;> rw [Tm.ms0_bs0_var_notMem (ha := ha.lc_tm)] <;> simp [*]

theorem Ctx.HasTy.bs0_cf {Γ : Ctx} {A B a b : Tm} {L : Finset ℕ}
  (hb : ∀ x ∉ L, Ctx.HasTy (Γ.cons x A) (B.bs0 (.fv x)) (b.bs0 (.fv x)))
  (ha : Ctx.HasTy Γ A a) : Γ.HasTy (B.bs0 a) (b.bs0 a) := by
  have ⟨x, hx⟩ := Finset.exists_notMem (L ∪ (B.fvs ∪ b.fvs))
  rw [Finset.notMem_union] at hx
  exact (hb x hx.1).bs0 hx.2 ha

theorem Ctx.HasTy.strengthen_inhab_cf {Γ : Ctx} {A B a b : Tm} {L : Finset ℕ}
  (hb : ∀ x ∉ L, Ctx.HasTy (Γ.cons x A) B b)
  (ha : Ctx.HasTy Γ A a)
  : Γ.HasTy B b := by
  have ⟨x, hx⟩ := Finset.exists_notMem (L ∪ B.fvs ∪ b.fvs ∪ Γ.dv);
  simp only [Finset.union_assoc, Finset.mem_union, not_or] at hx
  convert bs0_cf (L := L ∪ B.fvs ∪ b.fvs ∪ Γ.dv) (B := B) (b := b) _ ha using 1
  · rw [Tm.bs0, Tm.bsubst_lc]; exact (hb x hx.1).lc_ty
  · rw [Tm.bs0, Tm.bsubst_lc]; exact (hb x hx.1).lc_tm
  intro y hy
  simp only [Finset.union_assoc, Finset.mem_union, not_or] at hy
  convert hb y hy.1
  · rw [Tm.bs0, Tm.bsubst_lc]; exact (hb x hx.1).lc_ty
  · rw [Tm.bs0, Tm.bsubst_lc]; exact (hb x hx.1).lc_tm

theorem Ctx.HasTy.strengthen_unit {ℓ : ℕ} {Γ : Ctx} {A B b : Tm} {L : Finset ℕ}
  (hb : ∀ x ∉ L, Ctx.HasTy (Γ.cons x A) B b)
  (ha : Ctx.TyEq Γ A (.unit ℓ))
  : Γ.HasTy B b := .strengthen_inhab_cf hb (.cast ha.symm (.nil ha.ok))

def Ctx.Cmp (Γ : Ctx) (A a b : Tm) : Prop := Γ.HasTy A a ∧ Γ.HasTy A b

theorem Ctx.Cmp.lhs_ty {Γ : Ctx} {A a b : Tm} (h : Γ.Cmp A a b) : Γ.HasTy A a := h.1

theorem Ctx.Cmp.rhs_ty {Γ : Ctx} {A a b : Tm} (h : Γ.Cmp A a b) : Γ.HasTy A b := h.2

theorem Ctx.HasTy.cmp {Γ : Ctx} {A a : Tm} (h : Γ.HasTy A a) : Γ.Cmp A a a := ⟨h, h⟩

theorem Ctx.Cmp.symm {Γ : Ctx} {A a b : Tm} (h : Γ.Cmp A a b) : Γ.Cmp A b a := ⟨h.2, h.1⟩

theorem Ctx.Cmp.trans {Γ : Ctx} {A a b c : Tm} (hab : Γ.Cmp A a b) (hbc : Γ.Cmp A b c)
  : Γ.Cmp A a c := ⟨hab.1, hbc.2⟩

theorem Ctx.Cmp.cast {Γ : Ctx} {A B a b : Tm} (h : Γ.Cmp A a b) (hAB : Γ.TyEq A B)
  : Γ.Cmp B a b := ⟨h.1.cast hAB, h.2.cast hAB⟩

theorem Ctx.Cmp.ok {Γ : Ctx} {A a b : Tm} (h : Γ.Cmp A a b) : Γ.Ok := h.lhs_ty.ok

theorem Ctx.Cmp.regular {Γ : Ctx} {A a b : Tm} (h : Γ.Cmp A a b) : Γ.IsTy A := h.lhs_ty.regular

theorem Ctx.JEq.cmp {Γ : Ctx} {A a b : Tm} (h : Ctx.JEq Γ A a b)
  : Γ.Cmp A a b
  := by induction h with
  | nil_ok => apply HasTy.cmp; apply HasTy.zero; constructor
  | cons_ok hΓ =>
    apply HasTy.cmp; apply HasTy.zero; constructor
    · exact hΓ.ok
    · assumption
    · apply JEq.lhs_ty; assumption
  | univ | var | unit | nil | empty | nats | succ | explode =>
    constructor <;> constructor <;> (try apply ok) <;> assumption
  | eqn hA ha hb IA Ia Ib
    => exact ⟨IA.1.eqn Ia.1 Ib.1, IA.2.eqn (Ia.2.cast hA.ty_eq) (Ib.2.cast hA.ty_eq)⟩
  | pi_cf hA hB hℓ IA IB => exact ⟨
      IA.1.pi_cf (fun x hx => (IB x hx).1) hℓ,
      IA.2.pi_cf (fun x hx => (IB x hx).2.cast0 hA.ty_eq.symm) hℓ
    ⟩
  | app_cf hA hB hf ha hBa IA IB If Ia IBa => exact ⟨
      IA.1.app_cf (fun x hx => (IB x hx).1) If.1 Ia.1 hBa,
      IA.2.app_cf
        (fun x hx => (IB x hx).2.cast0 hA.ty_eq.symm)
        (If.2.cast ⟨_, hA.pi_cf hB rfl⟩)
        (Ia.2.cast ⟨_, hA⟩)
        (.trans (.symm (.bs0_cf_univ hB ha)) hBa)
    ⟩
  | abs_cf hA hB hb IA IB Ib => exact ⟨
      IA.1.abs_cf (fun x hx => (IB x hx).1) (fun x hx => (Ib x hx).1),
      (IA.2.abs_cf
        (fun x hx => (IB x hx).2.cast0 hA.ty_eq.symm)
        (fun x hx =>
          ((Ib x hx).2.cast0 hA.ty_eq.symm).cast ((hB x hx).cast0 hA.ty_eq.symm).ty_eq)).cast
        ⟨_, .symm (.pi_cf hA hB rfl)⟩
    ⟩
  | sigma_cf hA hB hℓ IA IB => exact ⟨
      IA.1.sigma_cf (fun x hx => (IB x hx).1) hℓ,
      IA.2.sigma_cf (fun x hx => (IB x hx).2.cast0 hA.ty_eq.symm) hℓ
    ⟩
  | pair_cf hA hB ha hb IA IB Ia Ib => exact ⟨
      IA.1.pair_cf (fun x hx => (IB x hx).1) Ia.1 Ib.1,
      (IA.2.pair_cf
        (fun x hx => (IB x hx).2.cast0 hA.ty_eq.symm)
        (Ia.2.cast hA.ty_eq)
        (Ib.2.cast ⟨_, ha.bs0_cf_univ hB⟩)
        ).cast ⟨_, .symm (.sigma_cf hA hB rfl)⟩
      ⟩
  | fst_cf hA hB he IA IB Ie => exact ⟨
      IA.1.fst_cf (fun x hx => (IB x hx).1) Ie.1,
      (IA.2.fst_cf
        (fun x hx => (IB x hx).2.cast0 hA.ty_eq.symm)
        (Ie.2.cast ⟨_, .sigma_cf hA hB rfl⟩)).cast ⟨_, hA.symm⟩
    ⟩
  | snd_cf hA hB he hBa IA IB Ie IBa => exact ⟨
      IA.1.snd_cf (fun x hx => (IB x hx).1) Ie.1 hBa,
      (IA.2.snd_cf
        (fun x hx => (IB x hx).2.cast0 hA.ty_eq.symm)
        (Ie.2.cast ⟨_, .sigma_cf hA hB rfl⟩)
        (.trans (.symm (.bs0_cf_univ hB (.fst_cf hA hB he))) hBa))
      ⟩
  | dite_cf hφ hA ha hb Iφ IA Ia Ib => exact ⟨
      Iφ.1.dite_cf IA.1 (fun x hx => (Ia x hx).1) (fun x hx => (Ib x hx).1),
      (Iφ.2.dite_cf (L := _ ∪ _) IA.2
        (fun x hx => by
        simp at hx
        exact ((Ia x hx.1).2.cast0 ⟨_, hφ.symm⟩).cast ⟨_, hA.wk0 hx.2 ⟨_, hφ.symm⟩⟩)
        (fun x hx => by
        simp at hx
        exact ((Ib x hx.1).2.cast0 ⟨_, hφ.symm.not⟩).cast ⟨_, hA.wk0 hx.2 ⟨_, hφ.symm.not⟩⟩)
      ).cast ⟨_, hA.symm⟩
    ⟩
  | trunc hA IA => exact ⟨IA.1.trunc, IA.2.trunc⟩
  | choose_cf hA ht hφ IA It Iφ => exact ⟨
      IA.1.choose_cf ht (fun x hx => (Iφ x hx).1),
      (IA.2.choose_cf (hA.trunc.symm.trans ht)
        (fun x hx => (Iφ x hx).2.cast0 ⟨_, hA.symm⟩)).cast ⟨_, hA.symm⟩
    ⟩
  | natrec_cf hC hn hz hs hCn IC In Iz Is ICn =>
    rename Finset ℕ => L
    exact ⟨
    .natrec_cf (fun x hx => (IC x hx).1) In.1 Iz.1 (fun x hx => (Is x hx).1) hCn,
    .natrec_cf (L := L ∪ _)
      (fun x hx => by simp at hx; exact (IC x hx.1).2)
      In.2
      (Iz.2.cast ⟨_, hz.ok.zero.bs0_cf_univ hC⟩)
      (fun x hx => by
        simp at hx
        exact (Is x hx.1).2.cast ⟨_,
          .pi_k
            (hC x hx.1)
            (.bs0_cf_univ (L := {x} ∪ L)
              (fun y hy => by
                simp at hy
                apply (hC y hy.2).wk1 _ hCn.ok.nats_ty
                simp [Ne.symm hy.1]
                exact hx.2
                )
              (.app_k
                (hC x hx.1).ok.nats (hC x hx.1).ok.nats
                (.succ (hC x hx.1).ok.zero)
                (.var (hC x hx.1).ok.zero .here)
              ))
            rfl
        ⟩)
      (.trans (.symm (.bs0_cf_univ hC hn)) hCn)
  ⟩
  | nil_uniq ha Ia => exact ⟨Ia.lhs_ty, .nil ha.ok⟩
  | eqn_rfl hA hab IA Iab => exact ⟨.eqn IA.1 Iab.1 Iab.2, .unit hab.ok⟩
  | beta_abs_cf _ _ _ _ hBa hba IA IB Ib Ia _ Iba =>
    exact ⟨.app_cf IA.1 (fun x hx => (IB x hx).1)
            (.abs_cf IA.1 (fun x hx => (IB x hx).1) (fun x hx => (Ib x hx).1)) Ia.1 hBa, Iba.2⟩
  | beta_fst_cf hA hB ha hb IA IB Ia Ib =>
    exact ⟨IA.1.fst_cf (fun x hx => (IB x hx).1)
            (.pair_cf IA.1 (fun x hx => (IB x hx).1) Ia.1 Ib.1), Ia.2
          ⟩
  | beta_snd_cf hA hB ha hb hBa IA IB Ia Ib Iba =>
    exact ⟨IA.1.snd_cf (fun x hx => (IB x hx).1)
            (.pair_cf IA.1 (fun x hx => (IB x hx).1) Ia.1 Ib.1)
            (.trans (.bs0_cf_univ hB (.beta_fst_cf hA hB ha hb)) hBa),
            Ib.1.cast hBa.ty_eq⟩
  | inhab hA ha IA Ia => exact ⟨.trunc IA.1, .unit hA.ok⟩
  | spec_cf hA ht hφ hφa IA It Iφ Iφa =>
    exact ⟨Iφa.2, .trunc (.sigma_cf IA.1 (fun x hx => (Iφ x hx).1) rfl)⟩
  | beta_true_cf hφ hA ha hb Iφ IA Ia Ib => exact ⟨
    Iφ.1.dite_cf IA.1 (fun x hx => (Ia x hx).1) (fun x hx => (Ib x hx).1),
    .strengthen_unit (fun x hx => (Ia x hx).1) hφ.ty_eq⟩
  | beta_false_cf hφ hA ha hb Iφ IA Ia Ib => exact ⟨
    Iφ.1.dite_cf IA.1 (fun x hx => (Ia x hx).1) (fun x hx => (Ib x hx).1),
    .strengthen_unit (ℓ := 0) (fun x hx => (Ib x hx).1) ⟨_, hφ.not_empty⟩⟩
  | beta_zero_cf hC hz hs hC0 IC Iz Is IC0 => exact ⟨
      .natrec_cf (fun x hx => (IC x hx).1) (.zero hz.ok) Iz.1 (fun x hx => (Is x hx).1) hC0,
      Iz.1.cast ⟨_, hC0⟩
    ⟩
  | beta_succ_cf hC hn hz hs hsn hCn hCs IC In Iz Is Isn ICn ICs => exact ⟨
      .natrec_cf  (fun x hx => (IC x hx).1)
                  (.app_k (.nats hz.ok) (.nats hz.ok) (.succ hz.ok) In.1) Iz.1
                  (fun x hx => (Is x hx).1) hCs,
      .app_k ICn.2 ICs.2 (Isn.2.cast ⟨_, .pi_k hCn hCs rfl⟩)
        (.natrec_cf (fun x hx => (IC x hx).1) In.1 Iz.1 (fun x hx => (Is x hx).1) hCn)
    ⟩
  | unit_uniq hφ ha Iφ Ia => exact ⟨Iφ.lhs_ty, .unit hφ.ok⟩
  | empty_uniq hφ ha Iφ Ia => exact ⟨Iφ.lhs_ty, .empty hφ.ok⟩
  | eqn_ext hA ha hb he IA Ia Ib Ie => exact ⟨Ia.1, Ib.1⟩
  | pi_ext_cf hA hB hf hg hfg IA IB If Ig Ifg => exact ⟨If.1, Ig.1⟩
  | sigma_ext_cf hA hB he IA IB Ie => exact ⟨
      Ie.1, .pair_cf IA.1 (fun x hx => (IB x hx).1)
              (.fst_cf IA.1 (fun x hx => (IB x hx).1) Ie.1)
              (.snd_cf IA.1 (fun x hx => (IB x hx).1) Ie.1
              (.bs0_cf_univ hB (.fst_cf hA hB he)))⟩
  | univ_succ hs Is =>
   exact ⟨.univ hs.ok, .cast (.symm ⟨_, hs.univ_succ.univ_succ⟩) (.univ hs.ok)⟩
  | univ_max hm hn hℓ hℓ' _ _ => exact ⟨
    .univ hm.ok,
    .cast (.symm ⟨_, .univ_succ (.univ_max hm hn hℓ hℓ')⟩) (.univ hm.ok)
  ⟩
  | univ_imax hm hn hℓ hℓ' Im In => exact ⟨
    .univ hm.ok,
    .cast (.symm ⟨_, .univ_succ (.univ_imax hm hn hℓ hℓ')⟩) (.univ hm.ok)
  ⟩
  | symm => apply Ctx.Cmp.symm; assumption
  | trans => apply Ctx.Cmp.trans <;> assumption
  | cast hA ha IA Ia => exact Ia.cast ⟨_, hA⟩

theorem Ctx.JEq.ty_lhs {Γ : Ctx} {A a b : Tm} (h : Ctx.JEq Γ A a b) : Γ.HasTy A a
  := h.cmp.1

theorem Ctx.JEq.ty_rhs {Γ : Ctx} {A a b : Tm} (h : Ctx.JEq Γ A a b) : Γ.HasTy A b
  := h.cmp.2

theorem Ctx.JEq.refl_iff (Γ : Ctx) (A a : Tm) : Γ.JEq A a a ↔ Γ.HasTy A a
  := ⟨Ctx.JEq.ty_lhs, Ctx.HasTy.refl⟩

theorem Ctx.HasTy.rename0 {Γ : Ctx} {x : ℕ} {A B a : Tm}
  (h : Ctx.HasTy (Γ.cons x A) (B.bs0 (.fv x)) (a.bs0 (.fv x)))
  (hB : x ∉ B.fvs) (ha : x ∉ a.fvs)
  : ∀y ∉ Γ.dv, Ctx.HasTy (Γ.cons y A) (B.bs0 (.fv y)) (a.bs0 (.fv y)) := by
  intro y hy
  rw [<-Ctx.JEq.refl_iff]
  apply Ctx.JEq.rename0 _ hB ha ha y hy
  rw [Ctx.JEq.refl_iff]
  exact h

theorem Ctx.HasTy.rename0' {Γ : Ctx} {x : ℕ} {A B a : Tm}
  (h : Ctx.HasTy (Γ.cons x A) B a)
  : ∀y ∉ Γ.dv, Ctx.HasTy (Γ.cons y A) (B.ms0 x (.fv y)) (a.ms0 x (.fv y)) := by
  intro y hy
  rw [<-Ctx.JEq.refl_iff]
  apply Ctx.JEq.rename0' _ y hy
  rw [Ctx.JEq.refl_iff]
  exact h

theorem Ctx.HasTy.close {Γ : Ctx} {x : ℕ} {A B a : Tm}
  (h : Ctx.HasTy (Γ.cons x A) B a)
  : ∀y ∉ Γ.dv, Ctx.HasTy (Γ.cons y A) ((B.close x).bs0 (.fv y)) ((a.close x).bs0 (.fv y)) := by
  intro y hy
  convert h.rename0' y hy using 1 <;> rw [Tm.rename_close]

theorem Ctx.HasTy.cf_to_dv {Γ : Ctx} {A B a : Tm} {L : Finset ℕ}
  (h : ∀ x ∉ L, Ctx.HasTy (Γ.cons x A) (B.bs0 (.fv x)) (a.bs0 (.fv x)))
  : ∀ x ∉ Γ.dv, Ctx.HasTy (Γ.cons x A) (B.bs0 (.fv x)) (a.bs0 (.fv x)) := by
  intro x hx
  have ⟨y, hy⟩ := Finset.exists_notMem (L ∪ B.fvs ∪ a.fvs)
  simp only [Finset.mem_union, not_or] at hy
  exact (h y hy.1.1).rename0 hy.1.2 hy.2 x hx

theorem Ctx.HasTy.cf_ty_to_dv {Γ : Ctx} {A B a : Tm} {L : Finset ℕ}
  (h : ∀ x ∉ L, Ctx.HasTy (Γ.cons x A) B (a.bs0 (.fv x)))
  : ∀ x ∉ Γ.dv, Ctx.HasTy (Γ.cons x A) B (a.bs0 (.fv x)) := by
  have hB : B.bvi = 0 := have ⟨x, hx⟩ := L.exists_notMem; (h x hx).lc_ty
  convert Ctx.HasTy.cf_to_dv (L := L) _
  · rw [Tm.bs0, Tm.bsubst_lc _ hB]
  convert h
  rw [Tm.bs0, Tm.bsubst_lc _ hB]

theorem Ctx.HasTy.cf_k_to_dv {Γ : Ctx} {A B a : Tm} {L : Finset ℕ}
  (h : ∀ x ∉ L, Ctx.HasTy (Γ.cons x A) B a)
  : ∀ x ∉ Γ.dv, Ctx.HasTy (Γ.cons x A) B a := by
  have ha : a.bvi = 0 := have ⟨x, hx⟩ := L.exists_notMem; (h x hx).lc_tm
  convert Ctx.HasTy.cf_ty_to_dv (L := L) _
  · rw [Tm.bs0, Tm.bsubst_lc _ ha]
  convert h
  rw [Tm.bs0, Tm.bsubst_lc _ ha]

theorem Ctx.HasTy.abs_ty_cf {Γ : Ctx} {m n : ℕ} {A B b : Tm}
  (hA : Γ.HasTy (.univ m) A) (hB : Γ.HasTy (.univ n) B) {L : Finset ℕ}
  (hb : ∀ x ∉ L, (Γ.cons x A).HasTy B (b.bs0 (.fv x)))
  : Γ.HasTy (.pi A B) (.abs A B b)
  := .abs_cf hA (hB.to_cf_dv hA.refl.ty_eq) (by
    convert HasTy.cf_ty_to_dv hb
    rw [Tm.bs0, Tm.bsubst_lc _ hB.lc_tm]
  )

theorem Ctx.HasTy.id_abs {Γ : Ctx} {ℓ : ℕ} {A : Tm}
  (hA : Γ.HasTy (.univ ℓ) A) : Γ.HasTy (.pi A A) (.abs A A (.bv 0))
  := .abs_ty_cf (b := .bv 0) (L := Γ.dv) hA hA
        (fun _ hx => .var (hA.ok.cons hx hA.is_ty) .here)
