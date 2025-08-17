import Covalence.HasTy
import Mathlib.Data.Set.Lattice.Image

def Tm.BSubst.cvar (σ : Tm.BSubst) (x : ℕ) : Tm.BSubst
  | 0 => .fv x
  | x + 1 => σ.get x

@[simp]
theorem Tm.BSubst.cvar_get_zero (σ : Tm.BSubst) (x : ℕ) : (σ.cvar x).get 0 = .fv x := rfl

@[simp]
theorem Tm.BSubst.cvar_get_succ (σ : Tm.BSubst) (x i : ℕ) : (σ.cvar x).get (i + 1) = σ.get i := rfl

theorem Tm.BSubst.cvar_mul_lift (σ τ : Tm.BSubst) (x : ℕ) : (σ.cvar x) * ↑s τ = (σ * τ).cvar x := by
  ext i
  cases i with
  | zero => rfl
  | succ i =>
    simp only [get_mul, get_succ_lift, ← bsubst_wkIn, cvar_get_succ]
    rfl

def Ctx.closeSubtermsOver (Γ : Ctx) (σ : Tm.BSubst) : Tm → Set Tm
  | .eqn A a b =>
    { .bsubst σ (.eqn A a b) }
    ∪ Γ.closeSubtermsOver σ A ∪ Γ.closeSubtermsOver σ a ∪ Γ.closeSubtermsOver σ b
  | .pi A B =>
    { .bsubst σ (.pi A B) }
    ∪ Γ.closeSubtermsOver σ A ∪ ⋃x ∉ Γ.dv, (Γ.cons x A).closeSubtermsOver (σ.cvar x) B
  | .abs A B b =>
    { .bsubst σ (.abs A B b) }
    ∪ Γ.closeSubtermsOver σ A
    ∪ (⋃x ∉ Γ.dv, (Γ.cons x A).closeSubtermsOver (σ.cvar x) B)
    ∪ (⋃x ∉ Γ.dv, (Γ.cons x A).closeSubtermsOver (σ.cvar x) b)
  | .app A B f a =>
    { .bsubst σ (.app A B f a) }
    ∪ Γ.closeSubtermsOver σ A
    ∪ (⋃x ∉ Γ.dv, (Γ.cons x A).closeSubtermsOver (σ.cvar x) B)
    ∪ Γ.closeSubtermsOver σ f
    ∪ Γ.closeSubtermsOver σ a
  | .sigma A B =>
    { .bsubst σ (.sigma A B) }
    ∪ Γ.closeSubtermsOver σ A ∪
    (⋃x ∉ Γ.dv, (Γ.cons x A).closeSubtermsOver (σ.cvar x) B)
  | .pair A B a b =>
    { .bsubst σ (.pair A B a b) }
    ∪ Γ.closeSubtermsOver σ A
    ∪ (⋃x ∉ Γ.dv, (Γ.cons x A).closeSubtermsOver (σ.cvar x) B)
    ∪ Γ.closeSubtermsOver σ a
    ∪ Γ.closeSubtermsOver σ b
  | .fst A B a =>
    { .bsubst σ (.fst A B a) }
    ∪ Γ.closeSubtermsOver σ A
    ∪ (⋃x ∉ Γ.dv, (Γ.cons x A).closeSubtermsOver (σ.cvar x) B)
    ∪ Γ.closeSubtermsOver σ a
  | .snd A B a =>
    { .bsubst σ (.snd A B a) }
    ∪ Γ.closeSubtermsOver σ A
    ∪ (⋃x ∉ Γ.dv, (Γ.cons x A).closeSubtermsOver (σ.cvar x) B)
    ∪ Γ.closeSubtermsOver σ a
  | .dite φ A a b =>
    { .bsubst σ (.dite φ A a b) }
    ∪ Γ.closeSubtermsOver σ φ
    ∪ Γ.closeSubtermsOver σ A
    ∪ Γ.closeSubtermsOver σ A
    ∪ (⋃x ∉ Γ.dv, (Γ.cons x φ).closeSubtermsOver σ a)
    ∪ (⋃x ∉ Γ.dv, (Γ.cons x φ.not).closeSubtermsOver σ b)
  | .trunc A =>
    { .bsubst σ (.trunc A) }
    ∪ Γ.closeSubtermsOver σ A
  | .choose A φ =>
    { .bsubst σ (.choose A φ) }
    ∪ Γ.closeSubtermsOver σ A
    ∪ (⋃x ∉ Γ.dv, (Γ.cons x A).closeSubtermsOver (σ.cvar x) φ)
  | .natrec C n z s =>
    { .bsubst σ (.natrec C n z s) }
    ∪ (⋃x ∉ Γ.dv, (Γ.cons x .nats).closeSubtermsOver (σ.cvar x) C)
    ∪ Γ.closeSubtermsOver σ n
    ∪ Γ.closeSubtermsOver σ z
    ∪ (⋃x ∉ Γ.dv, (Γ.cons x .nats).closeSubtermsOver (σ.cvar x) s)
  | .let₁ A a b =>
    { .bsubst σ (.let₁ A a b) }
    ∪ Γ.closeSubtermsOver σ A
    ∪ Γ.closeSubtermsOver σ a
    ∪ ⋃x ∉ Γ.dv, (Γ.cons x A).closeSubtermsOver (σ.cvar x) b
  | .bv i => { σ.get i }
  | a => { a }

theorem Ctx.closeSubtermsOver_dvs (Γ Δ : Ctx) (h : Γ.dv = Δ.dv)
  : Γ.closeSubtermsOver = Δ.closeSubtermsOver := by
  funext σ a
  induction a generalizing Γ Δ σ with
  | _ =>
    simp only [closeSubtermsOver] <;>
    congr <;> first
    | (apply_assumption; exact h)
    | (
      rw [h]
      apply Set.iUnion₂_congr
      intro x hx
      apply_assumption
      simp [Ctx.dv, h]
    )

theorem Ctx.closeSubtermsOver_dvs_left_cons
  (Γ : Ctx) (x : ℕ) (A B : Tm) (σ τ : Tm.BSubst) (a b : Tm)
  (h : (Γ.cons x A).closeSubtermsOver σ a = (Γ.cons x A).closeSubtermsOver τ b)
  : (Γ.cons x A).closeSubtermsOver σ a = (Γ.cons x B).closeSubtermsOver τ b := by
  rw [h, closeSubtermsOver_dvs]; simp only [Ctx.dv]

theorem Ctx.closeSubtermsOver_dvs_right_cons
  (Γ : Ctx) (x : ℕ) (A B : Tm) (σ τ : Tm.BSubst) (a b : Tm)
  (h : (Γ.cons x B).closeSubtermsOver σ a = (Γ.cons x B).closeSubtermsOver τ b)
  : (Γ.cons x A).closeSubtermsOver σ a = (Γ.cons x B).closeSubtermsOver τ b := by
  rw [<-h, closeSubtermsOver_dvs]; simp only [Ctx.dv]

inductive Tm.IsVar : Tm → Prop
  | bv (i : ℕ) : IsVar (.bv i)
  | fv (x : ℕ) : IsVar (.fv x)

def Tm.BSubst.Vars (σ : Tm.BSubst) : Prop := ∀ (i : ℕ), (σ.get i).IsVar

theorem Tm.BSubst.Vars.one : (1 : BSubst).Vars := fun i => .bv i

theorem Tm.IsVar.lift {t : Tm} (h : t.IsVar) : (↑0 t).IsVar := by cases h <;> constructor

theorem Tm.BSubst.Vars.lift {σ : Tm.BSubst} (hσ : σ.Vars) : (↑s σ).Vars
  := fun | 0 => .bv 0 | i + 1 => (hσ i).lift

theorem Tm.BSubst.Vars.cvar {σ : Tm.BSubst} (hσ : σ.Vars) (x : ℕ) : (σ.cvar x).Vars
  := fun | 0 => .fv x | i + 1 => hσ i

def Ctx.closeSubtermsOver_bsubst (Γ : Ctx) {σ τ : Tm.BSubst} (hτ : τ.Vars) (a : Tm)
  : Γ.closeSubtermsOver σ (a.bsubst τ) = Γ.closeSubtermsOver (σ * τ) a
  := by induction a generalizing σ τ Γ with
  | bv i =>
    simp only [Tm.bsubst, closeSubtermsOver, Tm.BSubst.get_mul]
    have ht := hτ i
    generalize τ.get i = t at *
    cases ht <;> simp only [closeSubtermsOver, Tm.bsubst]
  | _ =>
    simp only [closeSubtermsOver, Tm.bsubst, Tm.bsubst_bsubst, Tm.BSubst.lift_mul, *]
    <;> congr
    <;> {
      apply Set.iUnion₂_congr
      intro x hx
      apply Ctx.closeSubtermsOver_dvs_left_cons
      simp only [<-Tm.BSubst.cvar_mul_lift σ τ, hτ.lift, *]
    }

theorem Ctx.closeSubtermsOver_cvar1 (Γ : Ctx) (x : ℕ) (a : Tm)
  : Γ.closeSubtermsOver ((1 : Tm.BSubst).cvar x) a = Γ.closeSubtermsOver 1 (a.bs0 (.fv x))
  := by
  rw [Tm.bs0, closeSubtermsOver_bsubst]
  · apply congrFun; apply congrArg; ext i; cases i <;> rfl
  · intro i; cases i <;> constructor

@[simp]
theorem Ctx.closeSubtermsOver_fv (Γ : Ctx) (σ : Tm.BSubst) (x : ℕ)
  : Γ.closeSubtermsOver σ (.fv x) = { .fv x }
  := rfl

@[simp]
theorem Ctx.closeSubtermsOver1_bv (Γ : Ctx) (i : ℕ)
  : Γ.closeSubtermsOver 1 (.bv i) = { .bv i }
  := rfl

@[simp]
theorem Ctx.closeSubtermsOver_univ (Γ : Ctx) (σ : Tm.BSubst) (ℓ : ℕ)
  : Γ.closeSubtermsOver σ (.univ ℓ) = { .univ ℓ }
  := rfl

@[simp]
theorem Ctx.closeSubtermsOver_unit (Γ : Ctx) (σ : Tm.BSubst) (ℓ : ℕ)
  : Γ.closeSubtermsOver σ (.unit ℓ) = { .unit ℓ }
  := rfl

@[simp]
theorem Ctx.closeSubtermsOver_nil (Γ : Ctx) (σ : Tm.BSubst) (ℓ : ℕ)
  : Γ.closeSubtermsOver σ (.nil ℓ) = { .nil ℓ }
  := rfl

@[simp]
theorem Ctx.closeSubtermsOver_empty (Γ : Ctx) (σ : Tm.BSubst) (ℓ : ℕ)
  : Γ.closeSubtermsOver σ (.empty ℓ) = { .empty ℓ }
  := rfl

@[simp]
theorem Ctx.closeSubtermsOver1_eqn (Γ : Ctx) (A a b : Tm)
  : Γ.closeSubtermsOver 1 (.eqn A a b) = { .eqn A a b }
    ∪ Γ.closeSubtermsOver 1 A
    ∪ Γ.closeSubtermsOver 1 a
    ∪ Γ.closeSubtermsOver 1 b
  := by simp [closeSubtermsOver]

@[simp]
theorem Ctx.closeSubtermsOver1_pi (Γ : Ctx) (A B : Tm)
  : Γ.closeSubtermsOver 1 (.pi A B) = { .pi A B }
    ∪ Γ.closeSubtermsOver 1 A
    ∪ ⋃x ∉ Γ.dv, (Γ.cons x A).closeSubtermsOver 1 (B.bs0 (.fv x))
  := by simp [closeSubtermsOver, Ctx.closeSubtermsOver_cvar1]

@[simp]
theorem Ctx.closeSubtermsOver1_abs (Γ : Ctx) (A B b : Tm)
  : Γ.closeSubtermsOver 1 (.abs A B b) = { .abs A B b }
    ∪ Γ.closeSubtermsOver 1 A
    ∪ (⋃x ∉ Γ.dv, (Γ.cons x A).closeSubtermsOver 1 (B.bs0 (.fv x)))
    ∪ (⋃x ∉ Γ.dv, (Γ.cons x A).closeSubtermsOver 1 (b.bs0 (.fv x)))
  := by simp [closeSubtermsOver, Ctx.closeSubtermsOver_cvar1]

@[simp]
theorem Ctx.closeSubtermsOver1_app (Γ : Ctx) (A B f a : Tm)
  : Γ.closeSubtermsOver 1 (.app A B f a) = { .app A B f a }
    ∪ Γ.closeSubtermsOver 1 A
    ∪ (⋃x ∉ Γ.dv, (Γ.cons x A).closeSubtermsOver 1 (B.bs0 (.fv x)))
    ∪ Γ.closeSubtermsOver 1 f
    ∪ Γ.closeSubtermsOver 1 a
  := by simp [closeSubtermsOver, Ctx.closeSubtermsOver_cvar1]

@[simp]
theorem Ctx.closeSubtermsOver1_sigma (Γ : Ctx) (A B : Tm)
  : Γ.closeSubtermsOver 1 (.sigma A B) = { .sigma A B }
    ∪ Γ.closeSubtermsOver 1 A
    ∪ (⋃x ∉ Γ.dv, (Γ.cons x A).closeSubtermsOver 1 (B.bs0 (.fv x)))
  := by simp [closeSubtermsOver, Ctx.closeSubtermsOver_cvar1]

@[simp]
theorem Ctx.closeSubtermsOver1_pair (Γ : Ctx) (A B a b : Tm)
  : Γ.closeSubtermsOver 1 (.pair A B a b) = { .pair A B a b }
    ∪ Γ.closeSubtermsOver 1 A
    ∪ (⋃x ∉ Γ.dv, (Γ.cons x A).closeSubtermsOver 1 (B.bs0 (.fv x)))
    ∪ Γ.closeSubtermsOver 1 a
    ∪ Γ.closeSubtermsOver 1 b
  := by simp [closeSubtermsOver, Ctx.closeSubtermsOver_cvar1]

@[simp]
theorem Ctx.closeSubtermsOver1_fst (Γ : Ctx) (A B a : Tm)
  : Γ.closeSubtermsOver 1 (.fst A B a) = { .fst A B a }
    ∪ Γ.closeSubtermsOver 1 A
    ∪ (⋃x ∉ Γ.dv, (Γ.cons x A).closeSubtermsOver 1 (B.bs0 (.fv x)))
    ∪ Γ.closeSubtermsOver 1 a
  := by simp [closeSubtermsOver, Ctx.closeSubtermsOver_cvar1]

@[simp]
theorem Ctx.closeSubtermsOver1_snd (Γ : Ctx) (A B a : Tm)
  : Γ.closeSubtermsOver 1 (.snd A B a) = { .snd A B a }
    ∪ Γ.closeSubtermsOver 1 A
    ∪ (⋃x ∉ Γ.dv, (Γ.cons x A).closeSubtermsOver 1 (B.bs0 (.fv x)))
    ∪ Γ.closeSubtermsOver 1 a
  := by simp [closeSubtermsOver, Ctx.closeSubtermsOver_cvar1]

@[simp]
theorem Ctx.closeSubtermsOver1_dite (Γ : Ctx) (φ A a b : Tm)
  : Γ.closeSubtermsOver 1 (.dite φ A a b) = { .dite φ A a b }
    ∪ Γ.closeSubtermsOver 1 φ
    ∪ Γ.closeSubtermsOver 1 A
    ∪ Γ.closeSubtermsOver 1 A
    ∪ (⋃x ∉ Γ.dv, (Γ.cons x φ).closeSubtermsOver 1 a)
    ∪ (⋃x ∉ Γ.dv, (Γ.cons x φ.not).closeSubtermsOver 1 b)
  := by simp [closeSubtermsOver]

@[simp]
theorem Ctx.closeSubtermsOver1_trunc (Γ : Ctx) (A : Tm)
  : Γ.closeSubtermsOver 1 (.trunc A) = { .trunc A }
    ∪ Γ.closeSubtermsOver 1 A
  := by simp [closeSubtermsOver]

@[simp]
theorem Ctx.closeSubtermsOver1_choose (Γ : Ctx) (A φ : Tm)
  : Γ.closeSubtermsOver 1 (.choose A φ) = { .choose A φ }
    ∪ Γ.closeSubtermsOver 1 A
    ∪ (⋃x ∉ Γ.dv, (Γ.cons x A).closeSubtermsOver 1 (φ.bs0 (.fv x)))
  := by simp [closeSubtermsOver, Ctx.closeSubtermsOver_cvar1]

@[simp]
theorem Ctx.closeSubtermsOver_nats (Γ : Ctx) (σ : Tm.BSubst)
  : Γ.closeSubtermsOver σ .nats = { .nats }
  := rfl

@[simp]
theorem Ctx.closeSubtermsOver_zero (Γ : Ctx) (σ : Tm.BSubst)
  : Γ.closeSubtermsOver σ .zero = { .zero }
  := rfl

@[simp]
theorem Ctx.closeSubtermsOver_succ (Γ : Ctx) (σ : Tm.BSubst)
  : Γ.closeSubtermsOver σ .succ = { .succ }
  := rfl

@[simp]
theorem Ctx.closeSubtermsOver_natrec (Γ : Ctx) (C n z s : Tm)
  : Γ.closeSubtermsOver 1 (.natrec C n z s) = { .natrec C n z s }
    ∪ (⋃x ∉ Γ.dv, (Γ.cons x .nats).closeSubtermsOver 1 (C.bs0 (.fv x)))
    ∪ Γ.closeSubtermsOver 1 n
    ∪ Γ.closeSubtermsOver 1 z
    ∪ (⋃x ∉ Γ.dv, (Γ.cons x .nats).closeSubtermsOver 1 (s.bs0 (.fv x)))
  := by simp [closeSubtermsOver, Ctx.closeSubtermsOver_cvar1]

@[simp]
theorem Ctx.closeSubtermsOver_let₁ (Γ : Ctx) (A a b : Tm)
  : Γ.closeSubtermsOver 1 (.let₁ A a b) = { .let₁ A a b }
    ∪ Γ.closeSubtermsOver 1 A
    ∪ Γ.closeSubtermsOver 1 a
    ∪ ⋃x ∉ Γ.dv, (Γ.cons x A).closeSubtermsOver 1 (b.bs0 (.fv x))
  := by simp [closeSubtermsOver, Ctx.closeSubtermsOver_cvar1]

@[simp]
theorem Ctx.closeSubtermsOver_invalid (Γ : Ctx) (σ : Tm.BSubst)
  : Γ.closeSubtermsOver σ .invalid = { .invalid }
  := rfl

theorem Ctx.closeSubtermsOver_anti (Γ Δ : Ctx) (σ : Tm.BSubst) (a : Tm) (h : Γ.dv ⊆ Δ.dv)
  : Δ.closeSubtermsOver σ a ⊆ Γ.closeSubtermsOver σ a := by
  induction a generalizing Γ Δ σ <;> simp only [closeSubtermsOver, Set.Subset.refl]
  <;> (repeat first | apply Set.union_subset_union)
  <;> (try simp only [Set.Subset.refl, *])
  <;> {
    apply Set.iUnion_mono
    intro x
    simp only [Set.iUnion_subset_iff]
    intro hx
    have hx' : x ∉ Γ.dv := Set.notMem_subset h hx
    simp only [hx', not_false_eq_true, Set.iUnion_true]
    apply_assumption
    simp only [dv]
    apply Finset.union_subset_union_right
    exact h
  }

theorem Ctx.closeSubtermsOver_min (Γ : Ctx) (σ : Tm.BSubst) (a : Tm)
  : Γ.closeSubtermsOver σ a ⊆ Ctx.nil.closeSubtermsOver σ a
  := closeSubtermsOver_anti _ _ _ _ (by simp [dv])

def Ctx.tys : Ctx → Finset Tm
  | .nil => ∅
  | .cons Γ _ A => { A } ∪ Γ.tys

def Ctx.subterms (Γ : Ctx) : Set Tm := ⋃ A ∈ Γ.tys, Γ.closeSubtermsOver 1 A

def Ctx.strictSubtermsOver (Γ : Ctx) (a : Tm) : Set Tm := (Γ.closeSubtermsOver 1 a) \ {a}

@[simp]
theorem Ctx.mem_closeSubtermsOver1 (Γ : Ctx) (a : Tm)
  : a ∈ Γ.closeSubtermsOver 1 a := by cases a <;> simp

theorem Ctx.closeSubtermsOver1_strict (Γ : Ctx) (a : Tm)
  : Γ.closeSubtermsOver 1 a = {a} ∪ Γ.strictSubtermsOver a
  := by simp [strictSubtermsOver]

@[simp]
theorem Ctx.strictSubtermsOver_fv (Γ : Ctx) (x : ℕ)
  : Γ.strictSubtermsOver (.fv x) = ∅
  := by simp [strictSubtermsOver]

@[simp]
theorem Ctx.strictSubtermsOver_bv (Γ : Ctx) (i : ℕ)
  : Γ.strictSubtermsOver (.bv i) = ∅
  := by simp [strictSubtermsOver]

@[simp]
theorem Ctx.strictSubtermsOver_univ (Γ : Ctx) (ℓ : ℕ)
  : Γ.strictSubtermsOver (.univ ℓ) = ∅
  := by simp [strictSubtermsOver]

@[simp]
theorem Ctx.strictSubtermsOver_unit (Γ : Ctx) (ℓ : ℕ)
  : Γ.strictSubtermsOver (.unit ℓ) = ∅
  := by simp [strictSubtermsOver]

@[simp]
theorem Ctx.strictSubtermsOver_nil (Γ : Ctx) (ℓ : ℕ)
  : Γ.strictSubtermsOver (.nil ℓ) = ∅
  := by simp [strictSubtermsOver]

@[simp]
theorem Ctx.strictSubtermsOver_empty (Γ : Ctx) (ℓ : ℕ)
  : Γ.strictSubtermsOver (.empty ℓ) = ∅
  := by simp [strictSubtermsOver]

-- theorem Ctx.strictSubtermsOver_eqn (Γ : Ctx) (A a b : Tm)
--   : Γ.strictSubtermsOver (.eqn A a b)
--   = {A} ∪ {a} ∪ {b} ∪ Γ.strictSubtermsOver A ∪ Γ.strictSubtermsOver a ∪ Γ.strictSubtermsOver b
--   := by
--   simp only [strictSubtermsOver, closeSubtermsOver1_eqn]
--   rw [Set.union_assoc, Set.union_assoc, Set.union_comm, Set.diff_union_self]
--   simp only [Set.distrib_]

@[simp]
theorem Ctx.strictSubtermsOver_nats (Γ : Ctx)
  : Γ.strictSubtermsOver .nats = ∅
  := by simp [strictSubtermsOver]


theorem Ctx.strictSubtermsOverIndHelper (Γ : Ctx)
  (motive : Tm → Prop)
  (h : ∀ a, motive a ∧ ∀ b ∈ Γ.strictSubtermsOver a, motive b)
  : ∀ a, motive a
  := fun a => (h a).1

-- theorem Ctx.strictSubtermsOverInd (Γ : Ctx)
--   (motive : Tm → Prop)
--   (h : (∀ a, (∀ b ∈ Γ.strictSubtermsOver a, motive b) → motive a))
--   : ∀ a, motive a
--   := by
--   apply Ctx.strictSubtermsOverIndHelper .nil
--   intro a
--   generalize hb: a = b
--   induction b generalizing a with
--   | fv =>
--     have ha := h a
--     simp [hb, strictSubtermsOver] at ha
--     simp [ha]
--   | pi =>
--     have ha := h a
--     cases hb
--     simp at *
--     sorry
--   | _ => sorry

-- def Ctx.strictSubterms (Γ : Ctx) (a : Tm) : Set Tm := Γ.subterms ∪ Γ.strictSubtermsOver a

-- theorem Ctx.closeSubtermsInd
--   (motive : Ctx → Tm → Prop)
--   (h : (∀ Γ a, (∀ b ∈ Γ.strictSubterms a, motive Γ b) → motive Γ a))
--   : ∀ Γ a, motive Γ a
--   := by
--   intro Γ a
--   revert Γ
--   induction a using closeSubtermsOverInd .nil with
--   | h a I =>
--     sorry

inductive Ctx.StrictSubterms : Ctx → Tm → Set Tm
  | cons {Γ : Ctx} {x} {a A  : Tm} : (Γ.cons x A).StrictSubterms a A
  | sub_cons {Γ : Ctx} {x} {A s a : Tm} : Γ.StrictSubterms A s → (Γ.cons x A).StrictSubterms a s
  | eqn_ty {Γ : Ctx} {A a b : Tm} : Γ.StrictSubterms (.eqn A a b) A
  | sub_eqn_ty {Γ : Ctx} {A a b s : Tm} : Γ.StrictSubterms A s → Γ.StrictSubterms (.eqn A a b) s
  | eqn_lhs {Γ : Ctx} {A a b : Tm} : Γ.StrictSubterms (.eqn A a b) a
  | sub_eqn_lhs {Γ : Ctx} {A a b s : Tm} : Γ.StrictSubterms a s → Γ.StrictSubterms (.eqn A a b) s
  | eqn_rhs {Γ : Ctx} {A a b : Tm} : Γ.StrictSubterms (.eqn A a b) b
  | sub_eqn_rhs {Γ : Ctx} {A a b s : Tm} : Γ.StrictSubterms b s → Γ.StrictSubterms (.eqn A a b) s
  | pi_ty {Γ : Ctx} {A B : Tm} : Γ.StrictSubterms (.pi A B) A
  | sub_pi_ty {Γ : Ctx} {A B s : Tm} : Γ.StrictSubterms A s → Γ.StrictSubterms (.pi A B) s
  | pi_body {Γ : Ctx} {x : ℕ} {A B : Tm} : x ∉ Γ.dv → Γ.StrictSubterms (.pi A B) (B.bs0 (.fv x))
  | sub_pi_body {Γ : Ctx} {x : ℕ} {A B s : Tm}
    : x ∉ Γ.dv → (Γ.cons x A).StrictSubterms (B.bs0 (.fv x)) s → Γ.StrictSubterms (.pi A B) s
  | abs_ty {Γ : Ctx} {A B b : Tm} : Γ.StrictSubterms (.abs A B b) A
  | sub_abs_ty {Γ : Ctx} {A B b s : Tm} : Γ.StrictSubterms A s → Γ.StrictSubterms (.abs A B b) s
  | abs_res {Γ : Ctx} {x : ℕ} {A B b : Tm}
    : x ∉ Γ.dv → Γ.StrictSubterms (.abs A B b) (B.bs0 (.fv x))
  | sub_abs_res {Γ : Ctx} {x : ℕ} {A B b s : Tm}
    : x ∉ Γ.dv → (Γ.cons x A).StrictSubterms (B.bs0 (.fv x)) s → Γ.StrictSubterms (.abs A B b) s
  | abs_body {Γ : Ctx} {x : ℕ} {A B b : Tm}
    : x ∉ Γ.dv → Γ.StrictSubterms (.abs A B b) (b.bs0 (.fv x))
  | sub_abs_body {Γ : Ctx} {x : ℕ} {A B b s : Tm}
    : x ∉ Γ.dv → (Γ.cons x A).StrictSubterms (b.bs0 (.fv x)) s → Γ.StrictSubterms (.abs A B b) s
  | app_ty {Γ : Ctx} {A B f a : Tm} : Γ.StrictSubterms (.app A B f a) A
  | sub_app_ty {Γ : Ctx} {A B f a s : Tm}
    : Γ.StrictSubterms A s → Γ.StrictSubterms (.app A B f a) s
  | app_res {Γ : Ctx} {x : ℕ} {A B f a : Tm}
    : x ∉ Γ.dv → Γ.StrictSubterms (.app A B f a) (B.bs0 (.fv x))
  | sub_app_res {Γ : Ctx} {x : ℕ} {A B f a s : Tm}
    : x ∉ Γ.dv → (Γ.cons x A).StrictSubterms (B.bs0 (.fv x)) s → Γ.StrictSubterms (.app A B f a) s
  | app_f {Γ : Ctx} {A B f a : Tm} : Γ.StrictSubterms (.app A B f a) f
  | sub_app_f {Γ : Ctx} {A B f a s : Tm}
    : Γ.StrictSubterms f s → Γ.StrictSubterms (.app A B f a) s
  | app_a {Γ : Ctx} {A B f a : Tm} : Γ.StrictSubterms (.app A B f a) a
  | sub_app_a {Γ : Ctx} {A B f a s : Tm}
    : Γ.StrictSubterms a s → Γ.StrictSubterms (.app A B f a) s
  | sigma_ty {Γ : Ctx} {A B : Tm} : Γ.StrictSubterms (.sigma A B) A
  | sub_sigma_ty {Γ : Ctx} {A B s : Tm} : Γ.StrictSubterms A s → Γ.StrictSubterms (.sigma A B) s
  | sigma_body {Γ : Ctx} {x : ℕ} {A B : Tm}
    : x ∉ Γ.dv → Γ.StrictSubterms (.sigma A B) (B.bs0 (.fv x))
  | sub_sigma_body {Γ : Ctx} {x : ℕ} {A B s : Tm}
    : x ∉ Γ.dv → (Γ.cons x A).StrictSubterms (B.bs0 (.fv x)) s → Γ.StrictSubterms (.sigma A B) s
  | pair_ty {Γ : Ctx} {A B a b : Tm} : Γ.StrictSubterms (.pair A B a b) A
  | sub_pair_ty {Γ : Ctx} {A B a b s : Tm}
    : Γ.StrictSubterms A s → Γ.StrictSubterms (.pair A B a b) s
  | pair_res {Γ : Ctx} {x : ℕ} {A B a b : Tm}
    : x ∉ Γ.dv → Γ.StrictSubterms (.pair A B a b) (B.bs0 (.fv x))
  | sub_pair_res {Γ : Ctx} {x : ℕ} {A B a b s : Tm}
    : x ∉ Γ.dv → (Γ.cons x A).StrictSubterms (B.bs0 (.fv x)) s → Γ.StrictSubterms (.pair A B a b) s
  | pair_a {Γ : Ctx} {A B a b : Tm} : Γ.StrictSubterms (.pair A B a b) a
  | sub_pair_a {Γ : Ctx} {A B a b s : Tm}
    : Γ.StrictSubterms a s → Γ.StrictSubterms (.pair A B a b) s
  | pair_b {Γ : Ctx} {A B a b : Tm} : Γ.StrictSubterms (.pair A B a b) b
  | sub_pair_b {Γ : Ctx} {A B a b s : Tm}
    : Γ.StrictSubterms b s → Γ.StrictSubterms (.pair A B a b) s
  | fst_ty {Γ : Ctx} {A B a : Tm} : Γ.StrictSubterms (.fst A B a) A
  | sub_fst_ty {Γ : Ctx} {A B a s : Tm}
    : Γ.StrictSubterms A s → Γ.StrictSubterms (.fst A B a) s
  | fst_body {Γ : Ctx} {x : ℕ} {A B a : Tm}
    : x ∉ Γ.dv → Γ.StrictSubterms (.fst A B a) (B.bs0 (.fv x))
  | sub_fst_body {Γ : Ctx} {x : ℕ} {A B a s : Tm}
    : x ∉ Γ.dv → (Γ.cons x A).StrictSubterms (B.bs0 (.fv x)) s → Γ.StrictSubterms (.fst A B a) s
  | fst_a {Γ : Ctx} {A B a : Tm} : Γ.StrictSubterms (.fst A B a) a
  | sub_fst_a {Γ : Ctx} {A B a s : Tm}
    : Γ.StrictSubterms a s → Γ.StrictSubterms (.fst A B a) s
  | snd_ty {Γ : Ctx} {A B a : Tm} : Γ.StrictSubterms (.snd A B a) A
  | sub_snd_ty {Γ : Ctx} {A B a s : Tm}
    : Γ.StrictSubterms A s → Γ.StrictSubterms (.snd A B a) s
  | snd_body {Γ : Ctx} {x : ℕ} {A B a : Tm}
    : x ∉ Γ.dv → Γ.StrictSubterms (.snd A B a) (B.bs0 (.fv x))
  | sub_snd_body {Γ : Ctx} {x : ℕ} {A B a s : Tm}
    : x ∉ Γ.dv → (Γ.cons x A).StrictSubterms (B.bs0 (.fv x)) s → Γ.StrictSubterms (.snd A B a) s
  | snd_a {Γ : Ctx} {A B a : Tm} : Γ.StrictSubterms (.snd A B a) a
  | sub_snd_a {Γ : Ctx} {A B a s : Tm}
    : Γ.StrictSubterms a s → Γ.StrictSubterms (.snd A B a) s
  | dite_ty {Γ : Ctx} {φ A a b : Tm} : Γ.StrictSubterms (.dite φ A a b) φ
  | sub_dite_ty {Γ : Ctx} {φ A a b s : Tm}
    : Γ.StrictSubterms φ s → Γ.StrictSubterms (.dite φ A a b) s
  | dite_a {Γ : Ctx} {φ A a b : Tm} : Γ.StrictSubterms (.dite φ A a b) A
  | sub_dite_a {Γ : Ctx} {φ A a b s : Tm}
    : Γ.StrictSubterms A s → Γ.StrictSubterms (.dite φ A a b) s
  | dite_b {Γ : Ctx} {φ A a b : Tm} : Γ.StrictSubterms (.dite φ A a b) A
  | sub_dite_b {Γ : Ctx} {φ A a b s : Tm}
    : Γ.StrictSubterms A s → Γ.StrictSubterms (.dite φ A a b) s
  | dite_a_true {Γ : Ctx} {φ A a b : Tm}
    : Γ.StrictSubterms (.dite φ A a b) a
  | sub_dite_a_true {Γ : Ctx} {φ A a b s : Tm}
    : Γ.StrictSubterms a s → Γ.StrictSubterms (.dite φ A a b) s
  | dite_b_false {Γ : Ctx} {φ A a b : Tm}
    : Γ.StrictSubterms (.dite φ A a b) b
  | sub_dite_b_false {Γ : Ctx} {φ A a b s : Tm}
    : Γ.StrictSubterms b s → Γ.StrictSubterms (.dite φ A a b) s
  | trunc {Γ : Ctx} {A : Tm} : Γ.StrictSubterms (.trunc A) A
  | sub_trunc {Γ : Ctx} {A s : Tm}
    : Γ.StrictSubterms A s → Γ.StrictSubterms (.trunc A) s
  | choose_ty {Γ : Ctx} {A φ : Tm} : Γ.StrictSubterms (.choose A φ) A
  | sub_choose_ty {Γ : Ctx} {A φ s : Tm}
    : Γ.StrictSubterms A s → Γ.StrictSubterms (.choose A φ) s
  | choose_body {Γ : Ctx} {x : ℕ} {A φ : Tm}
    : x ∉ Γ.dv → Γ.StrictSubterms (.choose A φ) (φ.bs0 (.fv x))
  | sub_choose_body {Γ : Ctx} {x : ℕ} {A φ s : Tm}
    : x ∉ Γ.dv → (Γ.cons x A).StrictSubterms (φ.bs0 (.fv x)) s
    → Γ.StrictSubterms (.choose A φ) s
  | natrec_ty {Γ : Ctx} {C n z s : Tm} : Γ.StrictSubterms (.natrec C n z s) C
  | sub_natrec_ty {Γ : Ctx} {C n z s : Tm}
    : Γ.StrictSubterms C s → Γ.StrictSubterms (.natrec C n z s) s
  | natrec_n {Γ : Ctx} {C n z s : Tm} : Γ.StrictSubterms (.natrec C n z s) n
  | sub_natrec_n {Γ : Ctx} {C n z s : Tm}
    : Γ.StrictSubterms n s → Γ.StrictSubterms (.natrec C n z s) s
  | natrec_z {Γ : Ctx} {C n z s : Tm} : Γ.StrictSubterms (.natrec C n z s) z
  | sub_natrec_z {Γ : Ctx} {C n z s : Tm}
    : Γ.StrictSubterms z s → Γ.StrictSubterms (.natrec C n z s) s
  | natrec_s {Γ : Ctx} {x : ℕ} {C n z s : Tm}
    : x ∉ Γ.dv → Γ.StrictSubterms (.natrec C n z s) (s.bs0 (.fv x))
  | sub_natrec_s {Γ : Ctx} {x : ℕ} {C n z s : Tm}
    : x ∉ Γ.dv → (Γ.cons x C).StrictSubterms (s.bs0 (.fv x)) s
    → Γ.StrictSubterms (.natrec C n z s) s
