import Covalence.Unique

def Ctx.Inhab (Γ : Ctx) (A : Tm) : Prop := ∃a, Γ.HasTy A a

theorem Ctx.Inhab.ok {Γ : Ctx} {A : Tm} (h : Γ.Inhab A) : Γ.Ok
  := let ⟨_, ha⟩ := h; ha.ok

theorem Ctx.Inhab.regular {Γ : Ctx} {A : Tm} (h : Γ.Inhab A) : Γ.IsTy A
  := let ⟨_, ha⟩ := h; ha.regular

theorem Ctx.Inhab.explode' {Γ : Ctx} {ℓ : ℕ} (h : Γ.Inhab (.empty ℓ)) {A a b : Tm}
  (ha : Γ.JEq A a a) (hb : Γ.JEq A b b) : Γ.JEq A a b
  := have ⟨_, h⟩ := h; h.refl.explode' ha hb

theorem Ctx.Inhab.all {Γ : Ctx} {ℓ : ℕ} (h : Γ.Inhab (.empty ℓ))
  {A : Tm} (hA : Γ.IsTy A) : Γ.Inhab A :=
  have ⟨ℓA, hA⟩ := hA;
  have hA' : Γ.JEq (.univ ℓA) (.unit ℓA) A := h.explode' hA.ok.unit hA;
  ⟨.nil ℓA, .cast ⟨_, hA'⟩ (.nil hA.ok)⟩

def Ctx.Contradiction (Γ : Ctx) := Γ.Inhab (.empty 0)

def Ctx.IsProp (Γ : Ctx) (φ : Tm) := Γ.HasTy (.univ 0) φ

theorem Ctx.IsProp.not {Γ : Ctx} {φ : Tm} (h : Γ.IsProp φ) : Γ.IsProp φ.not
  := HasTy.not h

def Ctx.IsTrue (Γ : Ctx) (φ : Tm) := Γ.JEq (.univ 0) φ (.unit 0)

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

def Ctx.IsFalse (Γ : Ctx) (φ : Tm) := Γ.JEq (.univ 0) φ (.empty 0)

theorem Ctx.IsFalse.is_prop {Γ : Ctx} {φ : Tm} (h : Γ.IsFalse φ) : Γ.IsProp φ := h.ty_lhs

theorem Ctx.IsFalse.is_ty {Γ : Ctx} {φ : Tm} (h : Γ.IsFalse φ) : Γ.IsTy φ := h.is_prop.is_ty

theorem Ctx.IsFalse.ty_eq_empty {Γ : Ctx} {φ : Tm} (h : Γ.IsFalse φ) : Γ.TyEq φ (.empty 0)
  := ⟨_, h⟩

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

theorem Ctx.IsEmpty.is_prop {Γ : Ctx} {A : Tm} (h : Γ.IsEmpty A) : Γ.IsProp A.not
  := h.regular.pi_src.not_prop

theorem Ctx.IsEmpty.is_true {Γ : Ctx} {A : Tm} (h : Γ.IsEmpty A) : Γ.IsTrue A.not
  := h.inhab.is_true h.is_prop

theorem Ctx.IsEmpty.is_false {Γ : Ctx} {φ : Tm} (h : Γ.IsEmpty φ) (hp : Γ.IsProp φ) : Γ.IsFalse φ
  := have ⟨_, h⟩ := h; .empty_uniq hp.refl h.refl

theorem Ctx.HasTy.is_false {Γ : Ctx} {φ a : Tm} (h : Γ.HasTy φ.not a) (hp : Γ.IsProp φ)
  : Γ.IsFalse φ := IsEmpty.is_false ⟨a, h⟩ hp

theorem Ctx.IsFalse.is_empty {Γ : Ctx} {φ : Tm} (h : Γ.IsFalse φ) : Γ.IsEmpty φ :=
  ⟨
    Tm.abs 0 φ (.empty 0) (.bv 0),
    .abs_cf h.is_prop
      (fun _ hx => .empty (h.ok.cons hx h.is_ty)) rfl
      (fun _ hx => .cast ⟨0, h.wk0 hx ⟨_, h⟩⟩ (.var (h.ok.cons hx h.is_ty) .here))
  ⟩

theorem Ctx.IsFalse.inhab {Γ : Ctx} {φ : Tm} (h : Γ.IsFalse φ) : Γ.Inhab φ.not
  := h.is_empty.inhab

theorem Ctx.IsFalse.iff_empty_prop {Γ : Ctx} {φ : Tm}
  : Γ.IsFalse φ ↔ Γ.IsEmpty φ ∧ Γ.IsProp φ
  := ⟨fun h => ⟨h.is_empty, h.is_prop⟩, fun ⟨h, hp⟩ => h.is_false hp⟩

-- theorem Ctx.Contradiction.empty0 {Γ : Ctx} {x : ℕ} {A : Tm} {ℓ : ℕ}
-- (h : (Γ.cons x A).Contradiction)
--   : Γ.IsEmpty A  :=
--   have ⟨c, hc⟩ := h;
--   have ⟨_, hA⟩ := h.ok.ty;
--   ⟨.abs 0 A (.empty 0) c, .abs_cf hA.ty_lhs
--     (fun x hx => (h.ok.tail.cons hx h.ok.ty).empty.ty_lhs) rfl
--     sorry
--   ⟩

def Ctx.Implies (Γ : Ctx) (φ ψ : Tm) := Γ.IsProp φ ∧ Γ.IsProp ψ ∧ Γ.IsTrue (.pi 0 φ ψ)

theorem Ctx.Implies.src_prop {Γ : Ctx} {φ ψ : Tm} (h : Γ.Implies φ ψ) : Γ.IsProp φ
  := h.1

theorem Ctx.Implies.trg_prop {Γ : Ctx} {φ ψ : Tm} (h : Γ.Implies φ ψ) : Γ.IsProp ψ
  := h.2.1

theorem Ctx.Implies.src_ty {Γ : Ctx} {φ ψ : Tm} (h : Γ.Implies φ ψ) : Γ.IsTy φ := h.src_prop.is_ty

theorem Ctx.Implies.trg_ty {Γ : Ctx} {φ ψ : Tm} (h : Γ.Implies φ ψ) : Γ.IsTy ψ := h.trg_prop.is_ty

theorem Ctx.Implies.inhab {Γ : Ctx} {φ ψ : Tm} (h : Γ.Implies φ ψ) : Γ.Inhab (.pi 0 φ ψ)
  := h.2.2.inhab

theorem Ctx.Implies.mp {Γ : Ctx} {φ ψ : Tm} (h : Γ.Implies φ ψ) (hφ : Γ.IsTrue φ) : Γ.IsTrue ψ :=
  have ⟨_, hf⟩ := h.inhab; have ⟨_, hp⟩ := hφ.inhab;
  (HasTy.app_k h.src_prop h.trg_prop rfl hf hp).is_true h.trg_prop

-- theorem Ctx.Implies.mt {Γ : Ctx} {φ ψ : Tm} (h : Γ.Implies φ ψ) (hψ : Γ.IsFalse ψ) : Γ.IsFalse φ
-- :=
--   have ⟨_, hf⟩ := h.inhab; have ⟨_, hp⟩ := hψ.inhab;
--   sorry
  -- (HasTy.app_k h.src_prop h.trg_prop rfl hf hp).is_true h.trg_prop

-- theorem Ctx.IsProp.abs {Γ : Ctx} {φ ψ : Tm}
--   (hφ : Γ.IsProp φ) (hψ : Γ.IsProp ψ) {x : ℕ} (h : (Γ.cons x φ).IsTrue ψ)
--   : Γ.Implies φ ψ := sorry

-- theorem Ctx.Implies.lem {Γ : Ctx} {φ ψ : Tm} (h : Γ.Implies φ ψ) (h' : Γ.Implies φ.not ψ)
--   : Γ.IsTrue ψ :=
--   have ⟨_, hf⟩ := h.inhab; have ⟨_, hg⟩ := h'.inhab;
--   sorry

-- def Ctx.Implies.propext {Γ : Ctx} {φ ψ : Tm} (h : Γ.Implies φ ψ) (h' : Γ.Implies ψ φ)
--   : Γ.JEq (.univ 0) φ ψ
--   := sorry
