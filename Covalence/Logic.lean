import Covalence.Factor

def Ctx.Inhab (Γ : Ctx) (A : Tm) : Prop := ∃a, Γ.HasTy A a

theorem Ctx.Inhab.ok {Γ : Ctx} {A : Tm} (h : Γ.Inhab A) : Γ.Ok
  := let ⟨_, ha⟩ := h; ha.ok

theorem Ctx.Inhab.regular {Γ : Ctx} {A : Tm} (h : Γ.Inhab A) : Γ.IsTy A
  := let ⟨_, ha⟩ := h; ha.regular

theorem Ctx.Inhab.cast {Γ : Ctx} {A B : Tm} (hAB : Γ.TyEq A B) (h : Γ.Inhab A) : Γ.Inhab B
  := let ⟨_, ha⟩ := h; ⟨_, ha.cast hAB⟩

theorem Ctx.Inhab.explode' {Γ : Ctx} {ℓ : ℕ} (h : Γ.Inhab (.empty ℓ)) {A a b : Tm}
  (ha : Γ.JEq A a a) (hb : Γ.JEq A b b) : Γ.JEq A a b
  := have ⟨_, h⟩ := h; h.refl.explode' ha hb

theorem Ctx.Inhab.all {Γ : Ctx} {ℓ : ℕ} (h : Γ.Inhab (.empty ℓ))
  {A : Tm} (hA : Γ.IsTy A) : Γ.Inhab A :=
  have ⟨ℓA, hA⟩ := hA;
  have hA' : Γ.JEq (.univ ℓA) (.unit ℓA) A := h.explode' hA.ok.unit hA;
  ⟨.nil ℓA, .cast ⟨_, hA'⟩ (.nil hA.ok)⟩

def Ctx.Contra (Γ : Ctx) := Γ.Inhab (.empty 0)

def Ctx.IsProp (Γ : Ctx) (φ : Tm) := Γ.HasTy (.univ 0) φ

theorem Ctx.IsProp.not {Γ : Ctx} {φ : Tm} (h : Γ.IsProp φ) : Γ.IsProp φ.not
  := HasTy.not h

theorem Ctx.IsProp.imp {Γ : Ctx} {φ ψ : Tm} (hφ : Γ.IsProp φ) (hψ : Γ.IsProp ψ)
  : Γ.IsProp (φ.pi 0 ψ) := HasTy.pi_k hφ hψ rfl

theorem Ctx.IsProp.cf_to_dv {Γ : Ctx} {A φ : Tm} {L : Finset ℕ}
  (h : ∀ x ∉ L, (Γ.cons x A).IsProp (φ.bs0 (.fv x)))
  : ∀ x ∉ Γ.dv, (Γ.cons x A).IsProp (φ.bs0 (.fv x)) := HasTy.cf_ty_to_dv h

def Ctx.IsTrue (Γ : Ctx) (φ : Tm) := Γ.JEq (.univ 0) φ (.unit 0)

theorem Ctx.Ok.tt {Γ : Ctx} (h : Γ.Ok) : Γ.IsTrue (.unit 0) := h.unit

theorem Ctx.IsTrue.is_prop {Γ : Ctx} {φ : Tm} (h : Γ.IsTrue φ) : Γ.IsProp φ := h.ty_lhs

theorem Ctx.IsTrue.ty_eq_unit {Γ : Ctx} {φ : Tm} (h : Γ.IsTrue φ) : Γ.TyEq φ (.unit 0)
  := ⟨_, h⟩

theorem Ctx.IsTrue.inhab {Γ : Ctx} {φ : Tm} (h : Γ.IsTrue φ) : Γ.Inhab φ
  := ⟨.nil 0, .cast h.ty_eq_unit.symm (.nil h.ok)⟩

theorem Ctx.HasTy.is_true {Γ : Ctx} {φ a : Tm} (h : Γ.HasTy φ a) (hp : Γ.IsProp φ) : Γ.IsTrue φ
  := .unit_uniq hp.refl h.refl

theorem Ctx.Inhab.is_true {Γ : Ctx} {φ : Tm} (h : Γ.Inhab φ) (hp : Γ.IsProp φ) : Γ.IsTrue φ
  := have ⟨_, ha⟩ := h; ha.is_true hp

theorem Ctx.IsTrue.iff_inhab_prop {Γ : Ctx} {φ : Tm}
  : Γ.IsTrue φ ↔ Γ.Inhab φ ∧ Γ.IsProp φ
  := ⟨fun h => ⟨h.inhab, h.is_prop⟩, fun ⟨h, hp⟩ => h.is_true hp⟩

theorem Ctx.Ok.var0 {Γ : Ctx} {x : ℕ} {A : Tm} (h : (Γ.cons x A).Ok) : (Γ.cons x A).Inhab A
  := ⟨.fv x, .var h .here⟩

theorem Ctx.IsProp.var0 {Γ : Ctx} {x : ℕ} {φ : Tm}
  (h : (Γ.cons x φ).IsProp φ) : (Γ.cons x φ).IsTrue φ
  := h.ok.var0.is_true h

theorem Ctx.Ok.var1 {Γ : Ctx} {x y : ℕ} {A B : Tm}
  (h : ((Γ.cons x A).cons y B).Ok) : ((Γ.cons x A).cons y B).Inhab A
  := ⟨.fv x, .var h (.there .here)⟩

theorem Ctx.IsProp.var1 {Γ : Ctx} {x y : ℕ} {φ A : Tm}
  (h : ((Γ.cons x φ).cons y A).IsProp φ) : ((Γ.cons x φ).cons y A).IsTrue φ
  := h.ok.var1.is_true h

theorem Ctx.IsProp.wk0 {Γ : Ctx} {A φ : Tm} (h : Γ.IsProp φ) {x} (hx : x ∉ Γ.dv) (hA : Γ.IsTy A)
  : (Γ.cons x A).IsProp φ := HasTy.wk0 h hx hA

theorem Ctx.IsProp.wk1
  {Γ : Ctx} {y : ℕ} {Y φ : Tm} (h : (Γ.cons y Y).IsProp φ)
  {x : ℕ} {B C : Tm} (hx : x ∉ {y} ∪ Γ.dv) (hB : Γ.TyEq B C) : ((Γ.cons x B).cons y Y).IsProp φ
  := HasTy.wk1 h hx hB

theorem Ctx.IsProp.wk0_var0 {Γ : Ctx} {x : ℕ} {A : Tm}
  (h : Γ.IsProp A) (hx : x ∉ Γ.dv) : (Γ.cons x A).IsTrue A
  := (h.wk0 hx h.is_ty).var0

theorem Ctx.IsTrue.nil_ty {Γ : Ctx} {φ : Tm} (hA : Γ.IsTrue φ) : Γ.HasTy φ (.nil 0)
  := .cast ⟨_, .symm hA⟩ (.nil hA.ok)

def Ctx.IsFalse (Γ : Ctx) (φ : Tm) := Γ.JEq (.univ 0) φ (.empty 0)

theorem Ctx.Ok.ff {Γ : Ctx} (h : Γ.Ok) : Γ.IsFalse (.empty 0) := h.empty

theorem Ctx.IsFalse.is_prop {Γ : Ctx} {φ : Tm} (h : Γ.IsFalse φ) : Γ.IsProp φ := h.ty_lhs

theorem Ctx.IsFalse.is_ty {Γ : Ctx} {φ : Tm} (h : Γ.IsFalse φ) : Γ.IsTy φ := h.is_prop.is_ty

theorem Ctx.IsFalse.ty_eq_empty {Γ : Ctx} {φ : Tm} (h : Γ.IsFalse φ) : Γ.TyEq φ (.empty 0)
  := ⟨_, h⟩

theorem Ctx.IsTrue.contra {Γ : Ctx} {φ : Tm} (h : Γ.IsTrue φ) (h' : Γ.IsFalse φ) : Γ.Contra
  := h.inhab.cast ⟨_, h'⟩

def Ctx.IsEmpty (Γ : Ctx) (A : Tm) := Γ.Inhab A.not

theorem Ctx.IsEmpty.inhab {Γ : Ctx} {A : Tm} (h : Γ.IsEmpty A) : Γ.Inhab A.not
  := h

theorem Ctx.IsTy.not_prop {Γ : Ctx} {A : Tm} (h : Γ.IsTy A) : Γ.IsProp A.not
  := have ⟨_, ha⟩ := h; .pi_k ha.ty_lhs (.empty h.ok) rfl

theorem Ctx.IsTy.pi_src {Γ : Ctx} {ℓ : ℕ} {A B : Tm} (h : Γ.IsTy (A.pi ℓ B)) : Γ.IsTy A := by
  have ⟨_, h⟩ := h
  rw [Ctx.JEq.refl_iff, <-Ctx.OuterTy.has_ty_iff] at h
  have ⟨_, hA, hC⟩ := h
  cases hA with | pi_cf hA _ => exact ⟨_, hA.refl⟩

theorem Ctx.IsTy.of_not {Γ : Ctx} {A : Tm} (h : Γ.IsTy A.not) : Γ.IsTy A := h.pi_src

theorem Ctx.IsTy.pi_trg {Γ : Ctx} {ℓ : ℕ} {A B : Tm} (h : Γ.IsTy (A.pi ℓ B))
  : (∀x ∉ Γ.dv, (Γ.cons x A).IsTy (B.bs0 (.fv x))) := by
  have ⟨_, h⟩ := h
  rw [Ctx.JEq.refl_iff, <-Ctx.OuterTy.has_ty_iff] at h
  have ⟨_, hA, hC⟩ := h
  cases hA with | pi_cf hA hB hℓ => intro x hx; exact ⟨_, (HasTy.cf_ty_to_dv hB x hx).refl⟩

theorem Ctx.IsTy.pi_trg_prop {Γ : Ctx} {A B : Tm} (h : Γ.IsTy (A.pi 0 B))
  : (∀x ∉ Γ.dv, (Γ.cons x A).IsProp (B.bs0 (.fv x))) := by
  have ⟨_, h⟩ := h
  rw [Ctx.JEq.refl_iff, <-Ctx.OuterTy.has_ty_iff] at h
  have ⟨_, hA, hC⟩ := h
  cases hA with | pi_cf hA hB hℓ =>
    rename_i m n L
    cases n with
    | zero => exact IsProp.cf_to_dv hB
    | succ => cases m <;> simp [Nat.imax] at hℓ

theorem Ctx.IsEmpty.is_prop {Γ : Ctx} {A : Tm} (h : Γ.IsEmpty A) : Γ.IsProp A.not
  := h.regular.pi_src.not_prop

theorem Ctx.IsEmpty.is_true {Γ : Ctx} {A : Tm} (h : Γ.IsEmpty A) : Γ.IsTrue A.not
  := h.inhab.is_true h.is_prop

theorem Ctx.IsEmpty.is_false {Γ : Ctx} {φ : Tm} (h : Γ.IsEmpty φ) (hp : Γ.IsProp φ) : Γ.IsFalse φ
  := have ⟨_, h⟩ := h; .empty_uniq hp.refl h.refl

theorem Ctx.HasTy.is_false {Γ : Ctx} {φ a : Tm} (h : Γ.HasTy φ.not a) (hp : Γ.IsProp φ)
  : Γ.IsFalse φ := IsEmpty.is_false ⟨a, h⟩ hp

theorem Ctx.Contra.all_true {Γ : Ctx} (h : Γ.Contra) : ∀ {φ}, Γ.IsProp φ → Γ.IsTrue φ
  := fun hφ => (h.all hφ.is_ty).is_true hφ

theorem Ctx.Contra.all_false {Γ : Ctx} (h : Γ.Contra) : ∀ {φ}, Γ.IsProp φ → Γ.IsFalse φ
  := fun hφ => IsEmpty.is_false (h.all hφ.not.is_ty) hφ

theorem Ctx.IsFalse.is_empty {Γ : Ctx} {φ : Tm} (h : Γ.IsFalse φ) : Γ.IsEmpty φ :=
  ⟨
    Tm.abs 0 φ (.empty 0) (.bv 0),
    .abs_cf h.is_prop
      (fun _ hx => .empty (h.ok.cons hx h.is_ty)) rfl
      (fun _ hx => .cast ⟨0, h.wk0 hx ⟨_, h⟩⟩ (.var (h.ok.cons hx h.is_ty) .here))
  ⟩

theorem Ctx.IsFalse.not_true {Γ : Ctx} {φ : Tm} (h : Γ.IsFalse φ) : Γ.IsTrue φ.not
  := h.is_empty.is_true

theorem Ctx.IsFalse.inhab {Γ : Ctx} {φ : Tm} (h : Γ.IsFalse φ) : Γ.Inhab φ.not
  := h.is_empty.inhab

theorem Ctx.IsFalse.iff_empty_prop {Γ : Ctx} {φ : Tm}
  : Γ.IsFalse φ ↔ Γ.IsEmpty φ ∧ Γ.IsProp φ
  := ⟨fun h => ⟨h.is_empty, h.is_prop⟩, fun ⟨h, hp⟩ => h.is_false hp⟩

theorem Ctx.IsTrue.to_false {Γ : Ctx} {φ : Tm} (hφ : Γ.IsProp φ) (h : Γ.IsTrue φ.not)
  : Γ.IsFalse φ := IsEmpty.is_false h.inhab hφ

theorem Ctx.IsProp.not_var0 {Γ : Ctx} {x : ℕ} {φ : Tm}
  (h : (Γ.cons x φ.not).IsProp φ) : (Γ.cons x φ.not).IsFalse φ
  := h.not.var0.to_false h

theorem Ctx.IsProp.not_var1 {Γ : Ctx} {x y : ℕ} {φ A : Tm}
  (h : ((Γ.cons x φ.not).cons y A).IsProp φ) : ((Γ.cons x φ.not).cons y A).IsFalse φ
  := h.not.var1.to_false h

theorem Ctx.IsProp.wk0_not_var0 {Γ : Ctx} {x : ℕ} {φ : Tm}
  (h : Γ.IsProp φ) (hx : x ∉ Γ.dv) : (Γ.cons x φ.not).IsFalse φ
  := (h.wk0 hx h.not.is_ty).not_var0

theorem Ctx.Contra.close_emp {Γ : Ctx} {x : ℕ} {A : Tm}
(h : (Γ.cons x A).Contra) : Γ.IsEmpty A  :=
  have ⟨c, hc⟩ := h;
  have ⟨_, hA⟩ := h.ok.ty;
  ⟨.abs 0 A (.empty 0) (c.close x), .abs_cf hA.ty_lhs
    (fun _ hx => (h.ok.tail.cons hx h.ok.ty).empty.ty_lhs) rfl
    hc.close
  ⟩

theorem Ctx.Contra.close_not_tt {Γ : Ctx} {x : ℕ} {A : Tm}
  (h : (Γ.cons x A).Contra) : Γ.IsTrue A.not :=
  h.close_emp.is_true

theorem Ctx.Contra.close_ff {Γ : Ctx} {x : ℕ} {φ : Tm}
  (hφ : Γ.IsProp φ) (h : (Γ.cons x φ).Contra) : Γ.IsFalse φ :=
  h.close_emp.is_false hφ

def Ctx.Implies (Γ : Ctx) (φ ψ : Tm) := Γ.IsProp φ ∧ Γ.IsProp ψ ∧ Γ.IsTrue (.pi 0 φ ψ)

theorem Ctx.Implies.src_prop {Γ : Ctx} {φ ψ : Tm} (h : Γ.Implies φ ψ) : Γ.IsProp φ := h.1

theorem Ctx.Implies.trg_prop {Γ : Ctx} {φ ψ : Tm} (h : Γ.Implies φ ψ) : Γ.IsProp ψ := h.2.1

theorem Ctx.Implies.is_true {Γ : Ctx} {φ ψ : Tm} (h : Γ.Implies φ ψ) : Γ.IsTrue (.pi 0 φ ψ) := h.2.2

theorem Ctx.Implies.src_ty {Γ : Ctx} {φ ψ : Tm} (h : Γ.Implies φ ψ) : Γ.IsTy φ := h.src_prop.is_ty

theorem Ctx.Implies.trg_ty {Γ : Ctx} {φ ψ : Tm} (h : Γ.Implies φ ψ) : Γ.IsTy ψ := h.trg_prop.is_ty

theorem Ctx.Implies.inhab {Γ : Ctx} {φ ψ : Tm} (h : Γ.Implies φ ψ) : Γ.Inhab (.pi 0 φ ψ)
  := h.2.2.inhab

theorem Ctx.IsTrue.to_imp {Γ : Ctx} {φ : Tm} (hφ : Γ.IsTrue φ) : Γ.Implies (.unit 0) φ := ⟨
    .unit hφ.ok, hφ.is_prop,
    have ⟨_, hp⟩ := hφ.inhab;
    Inhab.is_true ⟨_, .abs_k (.unit hφ.ok) hφ.is_prop rfl hp⟩ (.pi_k (.unit hφ.ok) hφ.is_prop rfl)
  ⟩

theorem Ctx.Implies.true_imp {Γ : Ctx} {φ : Tm} (hφ : Γ.Implies (.unit 0) φ) : Γ.IsTrue φ :=
  have ⟨_, hf⟩ := hφ.inhab;
  Inhab.is_true ⟨_, .app_k hφ.src_prop hφ.trg_prop rfl hf (.nil hf.ok)⟩ hφ.trg_prop

theorem Ctx.Implies.true_imp_iff {Γ : Ctx} {φ : Tm} : Γ.Implies (.unit 0) φ ↔ Γ.IsTrue φ
  := ⟨Ctx.Implies.true_imp, Ctx.IsTrue.to_imp⟩

theorem Ctx.IsFalse.to_imp {Γ : Ctx} {φ : Tm} (hφ : Γ.IsFalse φ) : Γ.Implies φ (.empty 0)
  := ⟨hφ.is_prop, .empty hφ.ok, hφ.not_true⟩

theorem Ctx.Implies.false_imp {Γ : Ctx} {φ : Tm} (hφ : Γ.Implies φ (.empty 0)) : Γ.IsFalse φ :=
  IsEmpty.is_false hφ.is_true.inhab hφ.src_prop

theorem Ctx.Implies.false_imp_iff {Γ : Ctx} {φ : Tm} : Γ.Implies φ (.empty 0) ↔ Γ.IsFalse φ
  := ⟨Ctx.Implies.false_imp, Ctx.IsFalse.to_imp⟩

theorem Ctx.Implies.refl {Γ : Ctx} {φ : Tm} (hφ : Γ.IsProp φ) : Γ.Implies φ φ
  := ⟨hφ, hφ, Inhab.is_true ⟨_, hφ.id_abs⟩ (.pi_k hφ hφ rfl)⟩

theorem Ctx.Implies.trans {Γ : Ctx} {φ ψ θ : Tm} (h : Γ.Implies φ ψ) (h' : Γ.Implies ψ θ)
  : Γ.Implies φ θ := ⟨h.src_prop, h'.trg_prop,
    have ⟨f, hf⟩ := h.inhab; have ⟨g, hg⟩ := h'.inhab;
    Inhab.is_true
    ⟨.abs 0 φ θ (.app ψ θ g (.app φ ψ f (.bv 0))),
      (.abs_ty_cf (L := Γ.dv) h.src_prop h'.trg_prop rfl (fun x hx => by
        have hφ' := h.src_prop.wk0 hx h.src_prop.is_ty;
        have hψ' := h.trg_prop.wk0 hx h.src_prop.is_ty
        have hθ' := h'.trg_prop.wk0 hx h.src_prop.is_ty;
        have hf' := hf.wk0 hx h.src_prop.is_ty;
        have hg' := hg.wk0 hx h.src_prop.is_ty;
        convert HasTy.app_k hψ' hθ' rfl hg' (.app_k hφ' hψ' rfl hf' (.var hf'.ok .here)) using 1
        simp [Tm.bs0, Tm.bsubst_lc, hφ'.lc_tm, hψ'.lc_tm, hθ'.lc_tm, hg'.lc_tm, hf'.lc_tm]
      ))
    ⟩
    (.pi_k h.src_prop h'.trg_prop rfl)
  ⟩

theorem Ctx.Implies.mp {Γ : Ctx} {φ ψ : Tm} (h : Γ.Implies φ ψ) (hφ : Γ.IsTrue φ) : Γ.IsTrue ψ
  := true_imp (hφ.to_imp.trans h)

theorem Ctx.Implies.mt {Γ : Ctx} {φ ψ : Tm} (h : Γ.Implies φ ψ) (hψ : Γ.IsFalse ψ) : Γ.IsFalse φ
  := false_imp (h.trans hψ.to_imp)

theorem Ctx.Implies.wk0 {Γ : Ctx} {x : ℕ} {A : Tm} (hx : x ∉ Γ.dv) (hA : Γ.IsTy A)
  {φ ψ : Tm} (h : Γ.Implies φ ψ) : (Γ.cons x A).Implies φ ψ
  := ⟨h.src_prop.wk0 hx hA, h.trg_prop.wk0 hx hA, h.is_true.wk0 hx hA⟩

theorem Ctx.IsTrue.close {Γ : Ctx} {x : ℕ} {φ ψ : Tm}
  (hφ : Γ.IsProp φ) (hψ : Γ.IsProp ψ) (h : (Γ.cons x φ).IsTrue ψ) : Γ.Implies φ ψ
  := ⟨hφ, hψ, Inhab.is_true ⟨_, .abs_ty_cf (b := .nil 0) hφ hψ rfl (fun y hy => by
    convert h.nil_ty.rename0' y hy
    rw [Tm.ms0, Tm.msubst_eqOn_one]
    intro z hz
    simp [Tm.get_m0]
    intro hy'; cases hy'; exact (h.ok.var (hψ.refl.scoped_lhs hz)).elim
  )⟩ (hφ.imp hψ)⟩

theorem Ctx.Implies.open {Γ : Ctx} {φ ψ : Tm} (h : Γ.Implies φ ψ)
  : ∀x ∉ Γ.dv, (Γ.cons x φ).IsTrue ψ := fun _ hx => (h.wk0 hx h.src_ty).mp (h.src_prop.wk0_var0 hx)

theorem Ctx.Implies.open_iff {Γ : Ctx} {φ ψ : Tm}
  : Γ.Implies φ ψ ↔ Γ.IsProp φ ∧ Γ.IsProp ψ ∧ ∀x ∉ Γ.dv, (Γ.cons x φ).IsTrue ψ := ⟨
    fun h => ⟨h.src_prop, h.trg_prop, h.open⟩,
    fun ⟨hφ, hψ, h⟩ => have ⟨x, hx⟩ := Γ.dv.exists_notMem; (h x hx).close hφ hψ⟩

def Ctx.Iff (Γ : Ctx) (φ ψ : Tm) := Γ.Implies φ ψ ∧ Γ.Implies ψ φ

theorem Ctx.Iff.refl {Γ : Ctx} {φ : Tm} (hφ : Γ.IsProp φ) : Γ.Iff φ φ
  := ⟨Ctx.Implies.refl hφ, Ctx.Implies.refl hφ⟩

theorem Ctx.Iff.symm {Γ : Ctx} {φ ψ : Tm} (h : Γ.Iff φ ψ) : Γ.Iff ψ φ
  := ⟨h.2, h.1⟩

theorem Ctx.Iff.trans {Γ : Ctx} {φ ψ θ : Tm} (h : Γ.Iff φ ψ) (h' : Γ.Iff ψ θ)
  : Γ.Iff φ θ := ⟨h.1.trans h'.1, h'.2.trans h.2⟩

theorem Ctx.Iff.tt {Γ : Ctx} {φ ψ : Tm} (h : Γ.Iff φ ψ) : Γ.IsTrue φ ↔ Γ.IsTrue ψ
  := ⟨h.1.mp, h.2.mp⟩

theorem Ctx.Iff.ff {Γ : Ctx} {φ ψ : Tm} (h : Γ.Iff φ ψ) : Γ.IsFalse φ ↔ Γ.IsFalse ψ
  := ⟨h.2.mt, h.1.mt⟩

theorem Ctx.JEq.eqn_prop {Γ : Ctx} {A a b : Tm} (h : Γ.JEq A a b) : Γ.IsProp (.eqn A a b)
  := have ⟨_, hA⟩ := h.regular; .eqn hA.ty_lhs h.ty_lhs h.ty_rhs

theorem Ctx.JEq.eqn_tt {Γ : Ctx} {A a b : Tm} (h : Γ.JEq A a b) : Γ.IsTrue (.eqn A a b)
  := have ⟨_, hA⟩ := h.regular; .eqn_rfl hA h

theorem Ctx.IsProp.eqn_ty {Γ : Ctx} {A a b : Tm} (h : Γ.IsProp (.eqn A a b)) : Γ.IsTy A
  := by
  rw [IsProp, <-Ctx.OuterTy.has_ty_iff] at h
  have ⟨_, hA, hC⟩ := h
  cases hA; apply HasTy.is_ty; assumption

theorem Ctx.IsProp.eqn_lhs {Γ : Ctx} {A a b : Tm} (h : Γ.IsProp (.eqn A a b)) : Γ.HasTy A a
  := by
  rw [IsProp, <-Ctx.OuterTy.has_ty_iff] at h
  have ⟨_, hA, hC⟩ := h
  cases hA; assumption

theorem Ctx.IsProp.eqn_rhs {Γ : Ctx} {A a b : Tm} (h : Γ.IsProp (.eqn A a b)) : Γ.HasTy A b
  := by
  rw [IsProp, <-Ctx.OuterTy.has_ty_iff] at h
  have ⟨_, hA, hC⟩ := h
  cases hA; assumption

theorem Ctx.IsTrue.eqn_ty {Γ : Ctx} {A a b : Tm} (h : Γ.IsTrue (.eqn A a b)) : Γ.IsTy A
  := h.is_prop.eqn_ty

theorem Ctx.IsTrue.eqn_lhs {Γ : Ctx} {A a b : Tm} (h : Γ.IsTrue (.eqn A a b)) : Γ.HasTy A a
  := h.is_prop.eqn_lhs

theorem Ctx.IsTrue.eqn_rhs {Γ : Ctx} {A a b : Tm} (h : Γ.IsTrue (.eqn A a b)) : Γ.HasTy A b
  := h.is_prop.eqn_rhs

theorem Ctx.IsTrue.ext {Γ : Ctx} {A a b : Tm} (h : Γ.IsTrue (.eqn A a b))
  : Γ.JEq A a b := have ⟨_, hA⟩ := h.eqn_ty; .eqn_ext hA h.eqn_lhs.refl h.eqn_rhs.refl h

theorem Ctx.IsTrue.eqn_iff {Γ : Ctx} {A a b : Tm}
  : Γ.IsTrue (.eqn A a b) ↔ Γ.JEq A a b := ⟨Ctx.IsTrue.ext, JEq.eqn_tt⟩

theorem Ctx.IsTrue.eqn_bool {Γ : Ctx} {φ : Tm} (h : Γ.IsTrue φ)
  : Γ.IsTrue (.eqn (.univ 0) φ (.unit 0)) := JEq.eqn_tt h

theorem Ctx.IsFalse.eqn_bool {Γ : Ctx} {φ : Tm} (h : Γ.IsFalse φ)
  : Γ.IsTrue (.eqn (.univ 0) φ (.empty 0)) := JEq.eqn_tt h

theorem Ctx.IsTrue.eqn_symm {Γ : Ctx} {A a b : Tm} (h : Γ.IsTrue (.eqn A a b))
  : Γ.IsTrue (.eqn A b a) := by
  simp only [Ctx.IsTrue.eqn_iff] at *
  exact JEq.symm h

theorem Ctx.IsTrue.eqn_trans {Γ : Ctx} {A a b c : Tm}
  (h : Γ.IsTrue (.eqn A a b)) (h' : Γ.IsTrue (.eqn A b c))
  : Γ.IsTrue (.eqn A a c) := by
  simp only [Ctx.IsTrue.eqn_iff] at *
  exact JEq.trans h h'

theorem Ctx.HasTy.close_prop {Γ : Ctx} {x : ℕ} {φ A a : Tm}
  (hφ : Γ.IsProp φ) (h : Ctx.HasTy (Γ.cons x φ) A a)
  : ∀y ∉ Γ.dv, Ctx.HasTy (Γ.cons y φ) ((A.close x).bs0 (.nil 0)) ((a.close x).bs0 (.nil 0)) := by
  apply HasTy.cf_k_to_dv (L := (A.close x).fvs ∪ (a.close x).fvs ∪ Γ.dv)
  intro y hy
  simp at hy
  have ⟨x, hx⟩ := Finset.exists_notMem ({y} ∪ Γ.dv)
  have hc := HasTy.bs0 (by simp [*])
    ((h.close y (by simp [*])).wk1 (x := x) hx hφ.is_ty)
    (hφ.wk0_var0 (x := x) (by simp only [Finset.mem_union, not_or] at hx; exact hx.2)).nil_ty
  convert hc.rename0' y (by simp [*]) using 1
  <;> {
    rw [Tm.ms0, Tm.msubst_eqOn_subset_one (X := Γ.dv)]
    · intro z hz; simp [Tm.get_m0]; intro hz'; cases hz'; simp at hx; exact (hx.2 hz).elim
    · have hA := h.refl.scoped_ty;
      have ha := h.refl.scoped_lhs;
      simp only [Ctx.dv, <-Finset.insert_eq, Finset.subset_insert_iff] at *
      exact Tm.bs0_fv_sub (by simp only [Tm.fvs_close, *])
                          (by simp only [Tm.fvs, Finset.empty_subset])
  }

theorem Ctx.HasTy.close_prop_ty {Γ : Ctx} {x : ℕ} {φ A a : Tm}
  (hφ : Γ.IsProp φ) (hA : Γ.IsTy A) (h : Ctx.HasTy (Γ.cons x φ) A a)
  : ∀y ∉ Γ.dv, Ctx.HasTy (Γ.cons y φ) A ((a.close x).bs0 (.nil 0)) := by
  convert h.close_prop hφ
  rw [Tm.close_notMem (h := h.lc_ty), Tm.bs0, Tm.bsubst_lc (h := h.lc_ty)]
  apply Finset.not_mem_subset hA.scoped h.ok.var

theorem Ctx.Inhab.close_lem {Γ : Ctx} {φ A : Tm}
  (hφ : Γ.IsProp φ) (hA : Γ.IsTy A)
  {x : ℕ} (htt : (Γ.cons x φ).Inhab A) {y : ℕ} (hff : (Γ.cons y φ.not).Inhab A)
  : Γ.Inhab A :=
  have ⟨_, hA⟩ := hA; have ⟨_, htt⟩ := htt; have ⟨_, hff⟩ := hff;
  ⟨_, .dite_cf hφ hA.ty_lhs (htt.close_prop_ty hφ hA.lhs_ty) (hff.close_prop_ty hφ.not hA.lhs_ty)⟩

theorem Ctx.IsTrue.close_lem {Γ : Ctx} {φ ψ : Tm}
  (hφ : Γ.IsProp φ) (hψ : Γ.IsProp ψ)
  {x : ℕ} (htt : (Γ.cons x φ).IsTrue ψ) {y : ℕ} (hff : (Γ.cons y φ.not).IsTrue ψ)
  : Γ.IsTrue ψ := (htt.inhab.close_lem hφ hψ.is_ty hff.inhab).is_true hψ

theorem Ctx.Implies.lem {Γ : Ctx} {φ ψ : Tm} (htt : Γ.Implies φ ψ) (hff : Γ.Implies φ.not ψ)
  : Γ.IsTrue ψ :=
  have ⟨x, hx⟩ := Γ.dv.exists_notMem;
  (htt.open x hx).close_lem htt.src_prop htt.trg_prop (hff.open x hx)

theorem Ctx.IsEmpty.close_lem {Γ : Ctx} {φ A : Tm}
  (hφ : Γ.IsProp φ) (hA : Γ.IsTy A)
  {x : ℕ} (htt : (Γ.cons x φ).IsEmpty A) {y : ℕ} (hff : (Γ.cons y φ.not).IsEmpty A)
  : Γ.IsEmpty A := htt.inhab.close_lem hφ ⟨_, hA.not⟩ (hff.inhab)

theorem Ctx.IsFalse.close_lem {Γ : Ctx} {φ ψ : Tm}
  (hφ : Γ.IsProp φ) (hψ : Γ.IsProp ψ)
  {x : ℕ} (htt : (Γ.cons x φ).IsFalse ψ) {y : ℕ} (hff : (Γ.cons y φ.not).IsFalse ψ)
  : Γ.IsFalse ψ := (htt.is_empty.close_lem hφ hψ.is_ty hff.is_empty).is_false hψ

theorem Ctx.Inhab.lem_cf {Γ : Ctx} {φ A : Tm}
  (hφ : Γ.IsProp φ) (hA : Γ.IsTy A) {L : Finset ℕ}
  (htt : ∀ x ∉ L, (Γ.cons x φ).Inhab A) (hff : ∀ x ∉ L, (Γ.cons x φ.not).Inhab A)
  : Γ.Inhab A := have ⟨x, hx⟩ := L.exists_notMem; (htt x hx).close_lem hφ hA (hff x hx)

theorem Ctx.IsTrue.lem_cf {Γ : Ctx} {φ ψ : Tm}
  (hφ : Γ.IsProp φ) (hψ : Γ.IsProp ψ) {L : Finset ℕ}
  (htt : ∀ x ∉ L, (Γ.cons x φ).IsTrue ψ) (hff : ∀ x ∉ L, (Γ.cons x φ.not).IsTrue ψ)
  : Γ.IsTrue ψ := have ⟨x, hx⟩ := L.exists_notMem; (htt x hx).close_lem hφ hψ (hff x hx)

theorem Ctx.Implies.ok {Γ : Ctx} {φ ψ : Tm} (h : Γ.Implies φ ψ) : Γ.Ok := h.2.2.ok

theorem Ctx.Iff.ok {Γ : Ctx} {φ ψ : Tm} (h : Γ.Iff φ ψ) : Γ.Ok := h.1.ok

theorem Ctx.Iff.lhs_prop {Γ : Ctx} {φ ψ : Tm} (h : Γ.Iff φ ψ) : Γ.IsProp φ := h.1.src_prop

theorem Ctx.Iff.rhs_prop {Γ : Ctx} {φ ψ : Tm} (h : Γ.Iff φ ψ) : Γ.IsProp ψ := h.2.src_prop

theorem Ctx.Iff.eqn_prop {Γ : Ctx} {φ ψ : Tm} (h : Γ.Iff φ ψ)
  : Γ.IsProp (.eqn (.univ 0) φ ψ) := .eqn (.univ h.ok) h.lhs_prop h.rhs_prop

theorem Ctx.Iff.wk0 {Γ : Ctx} {x : ℕ} {A : Tm} (hx : x ∉ Γ.dv) (hA : Γ.IsTy A)
  {φ ψ : Tm} (h : Γ.Iff φ ψ) : (Γ.cons x A).Iff φ ψ
  := ⟨h.1.wk0 hx hA, h.2.wk0 hx hA⟩

theorem Ctx.Iff.propext {Γ : Ctx} {φ ψ : Tm} (h : Γ.Iff φ ψ)
  : Γ.JEq (.univ 0) φ ψ := (IsTrue.lem_cf (L := Γ.dv) h.lhs_prop h.eqn_prop
    (fun x hx =>
    have h' := h.wk0 hx h.lhs_prop.is_ty;
    have hψ' := h'.rhs_prop;
    IsTrue.lem_cf (L := {x} ∪ Γ.dv)
        hψ' h'.eqn_prop
        (fun _ hy =>
          (h'.lhs_prop.wk0 hy hψ'.is_ty).var1.eqn_bool.eqn_trans
          (hψ'.wk0_var0 hy).eqn_bool.eqn_symm)
        (fun _ hy =>
          have h'' := h'.wk0 hy hψ'.not.is_ty;
          Contra.all_true
          (IsTrue.contra h''.lhs_prop.var1 (h''.1.mt h''.rhs_prop.not_var0))
          h''.eqn_prop
        )
    )
    (fun x hx =>
      have h' := h.wk0 hx h.lhs_prop.not.is_ty;
      have hψ' := h'.rhs_prop;
      IsTrue.lem_cf (L := {x} ∪ Γ.dv) hψ' h'.eqn_prop
        (fun _ hy =>
          have h'' := h'.wk0 hy hψ'.is_ty;
          Contra.all_true
          (IsTrue.contra (h''.2.mp h''.rhs_prop.var0) h''.lhs_prop.not_var1)
          h''.eqn_prop)
        (fun _ hy =>
          (h'.lhs_prop.wk0 hy hψ'.not.is_ty).not_var1.eqn_bool.eqn_trans
          (hψ'.wk0_not_var0 hy).eqn_bool.eqn_symm)
  )
  ).ext
