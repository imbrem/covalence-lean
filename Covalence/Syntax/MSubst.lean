import Covalence.Syntax.Basic

def Tm.MSubst := ℕ → Tm

def Tm.MSubst.get (f : Tm.MSubst) (n : ℕ) : Tm := f n

@[ext] theorem Tm.MSubst.get_ext (f g : Tm.MSubst) (h : ∀ n, f.get n = g.get n) : f = g := funext h

instance Tm.MSubst.instOne : One Tm.MSubst where
  one := .fv

@[simp] theorem Tm.MSubst.get_one (n : ℕ) : Tm.MSubst.get 1 n = .fv n := rfl

@[simp]
def Tm.msubst (σ : MSubst) : Tm → Tm
  | .fv x => σ.get x
  | .bv i => .bv i
  | .univ ℓ => .univ ℓ
  | .unit ℓ => .unit ℓ
  | .nil ℓ => .nil ℓ
  | .empty ℓ => .empty ℓ
  | .eqn A a b => .eqn (A.msubst σ) (a.msubst σ) (b.msubst σ)
  | .pi ℓ A B => .pi ℓ (A.msubst σ) (B.msubst σ)
  | .abs ℓ A B b => .abs ℓ (A.msubst σ) (B.msubst σ) (b.msubst σ)
  | .app ℓ A B f a => .app ℓ (A.msubst σ) (B.msubst σ) (f.msubst σ) (a.msubst σ)
  | .sigma ℓ A B => .sigma ℓ (A.msubst σ) (B.msubst σ)
  | .pair ℓ A B a b => .pair ℓ (A.msubst σ) (B.msubst σ) (a.msubst σ) (b.msubst σ)
  | .fst ℓ A B a => .fst ℓ (A.msubst σ) (B.msubst σ) (a.msubst σ)
  | .snd ℓ A B a => .snd ℓ (A.msubst σ) (B.msubst σ) (a.msubst σ)
  | .dite φ A a b => .dite (φ.msubst σ) (A.msubst σ) (a.msubst σ) (b.msubst σ)
  | .trunc A => .trunc (A.msubst σ)
  | .choose A φ => .choose (A.msubst σ) (φ.msubst σ)
  | .nats => .nats
  | .zero => .zero
  | .succ => .succ
  | .natrec C n z s => .natrec (C.msubst σ) (n.msubst σ) (z.msubst σ) (s.msubst σ)
  | .let₁ A a b => .let₁ (A.msubst σ) (a.msubst σ) (b.msubst σ)
  | .invalid => .invalid

theorem Tm.msubst_fst {σ : MSubst} {ℓ : ℕ} {A B a : Tm} :
  (Tm.fst ℓ A B a).msubst σ = .fst ℓ (A.msubst σ) (B.msubst σ) (a.msubst σ) := rfl

theorem Tm.msubst_choose {σ : MSubst} {A φ : Tm} :
  (Tm.choose A φ).msubst σ = .choose (A.msubst σ) (φ.msubst σ) := rfl

theorem Tm.msubst_app_succ {σ : MSubst} {ℓ : ℕ} {n : Tm} :
  (Tm.app ℓ .nats .nats .succ n).msubst σ = .app ℓ .nats .nats .succ (n.msubst σ) := rfl

@[simp]
theorem Tm.msubst_one (t : Tm) : t.msubst 1 = t := by induction t <;> simp [*]

instance Tm.MSubst.instMul : Mul Tm.MSubst where
  mul f g := fun n => (g.get n).msubst f

@[simp]
theorem Tm.MSubst.get_mul (f g : Tm.MSubst) (n : ℕ) : (f * g).get n = (g.get n).msubst f := rfl

theorem Tm.msubst_mul (t : Tm) (f g : MSubst) : t.msubst (f * g) = (t.msubst g).msubst f := by
  induction t generalizing f g <;> simp [*]

theorem Tm.msubst_msubst (t : Tm) (f g : MSubst) : (t.msubst g).msubst f = t.msubst (f * g) := by
  rw [msubst_mul]

instance Tm.MSubst.instMonoid : Monoid Tm.MSubst where
  mul_assoc f g h := by ext n; simp [msubst_mul]
  one_mul f := by ext n; simp
  mul_one f := by ext n; simp

def Tm.MSubst.set (σ : MSubst) (x : ℕ) (t : Tm) : MSubst := Function.update σ x t

theorem Tm.MSubst.get_set (σ : MSubst) (x : ℕ) (t : Tm) (y : ℕ) :
  (σ.set x t).get y = if y = x then t else σ.get y
  := by simp [set, Function.update, get]

@[simp]
theorem Tm.MSubst.get_set_self (σ : MSubst) (x : ℕ) (t : Tm) :
  (σ.set x t).get x = t := by simp [get_set]

def Tm.m0 (x : ℕ) (t : Tm) : Tm.MSubst := MSubst.set 1 x t

theorem Tm.get_m0 (t : Tm) (x : ℕ) (y : ℕ) :
  (t.m0 x).get y = if y = x then t else .fv y
  := by simp [m0, MSubst.get_set]

@[simp] theorem Tm.get_m0_self (t : Tm) (x : ℕ) : (t.m0 x).get x = t := by simp [get_m0]

theorem Tm.get_m0_other (t : Tm) (x : ℕ) (y : ℕ) (h : y ≠ x) : (t.m0 x).get y = .fv y
  := by simp [get_m0, h]

def Tm.ms0 (t : Tm) (x : ℕ) (a : Tm) : Tm := t.msubst (a.m0 x)

def Tm.MSubst.lift (σ : MSubst) (x : ℕ) : MSubst := σ.set x (.fv x)

theorem Tm.MSubst.get_lift (σ : MSubst) (x : ℕ) (y : ℕ) :
  (σ.lift x).get y = if y = x then .fv x else σ.get y
  := by simp [lift, get_set]

@[simp]
theorem Tm.MSubst.get_lift_self (σ : MSubst) (x : ℕ) :
  (σ.lift x).get x = .fv x := by simp [get_lift]

theorem Tm.MSubst.lift_comm (σ : MSubst) (x : ℕ) (y : ℕ) : (σ.lift x).lift y = (σ.lift y).lift x
  := by ext n; simp only [get_lift]; grind

theorem Tm.MSubst.lift_lift (σ : MSubst) (x : ℕ) : (σ.lift x).lift x = σ.lift x
  := by ext n; simp only [get_lift]; grind

def Tm.MSubst.Lc (σ : MSubst) (X : Finset ℕ) : Prop := ∀i ∈ X, (σ.get i).bvi = 0

@[simp] theorem Tm.MSubst.Lc.empty (σ : MSubst) : σ.Lc ∅ := fun i hi => by cases hi

theorem Tm.MSubst.Lc.union_iff {σ : MSubst} {X Y : Finset ℕ} :
  σ.Lc (X ∪ Y) ↔ σ.Lc X ∧ σ.Lc Y := by
  simp only [Lc, Finset.mem_union, ← forall_and]
  apply forall_congr'
  grind

theorem Tm.MSubst.Lc.anti {σ : MSubst} {X Y : Finset ℕ} (hXY : X ⊆ Y) (hσ : σ.Lc Y) :
  σ.Lc X := fun i hi => hσ i (hXY hi)

@[simp]
theorem Tm.MSubst.Lc.singleton_iff {σ : MSubst} {x : ℕ} :
  σ.Lc {x} ↔ (σ.get x).bvi = 0 := by
  simp only [Lc, Finset.mem_singleton, forall_eq]

theorem Tm.MSubst.Lc.lift {σ : MSubst} (X : Finset ℕ) (hσ : σ.Lc X) (x : ℕ) :
  (σ.lift x).Lc ({x} ∪ X) := fun i hi => by
  simp [get_lift]
  split
  · rfl
  · apply hσ; simp [*] at hi; exact hi

theorem Tm.msubst_fsv_empty (σ : MSubst) (t : Tm) (ht : t.fvs = ∅)
  : t.msubst σ = t := by induction t <;> simp at ht <;> simp [*]

theorem Tm.msubst_lift_fvs_singleton (σ : MSubst) (t : Tm) (x : ℕ) (hx : t.fvs ⊆ {x})
  : t.msubst (σ.lift x) = t := by induction t with
  | fv y => simp at hx; cases hx; simp
  | _ =>
    simp only [msubst]
    <;> simp only [fvs, Finset.union_subset_iff] at hx
    <;> (try casesm* _ ∧ _)
    <;> simp [*]

theorem Tm.MSubst.Lc.bsubst_fvs_singleton {σ : MSubst}
  (t : Tm) (hσ : σ.Lc t.fvs) (n : ℕ) (x : ℕ) (hx : x ∉ t.fvs) (a : Tm) (ha : a.fvs ⊆ {x})
  : (t.msubst σ).bsubst (BSubst.lift^[n] a.b0)
  = (t.bsubst (BSubst.lift^[n] a.b0)).msubst (σ.lift x)
  := by induction t generalizing n with
  | bv i =>
    simp only [msubst, Tm.bsubst, BSubst.get_liftn]
    split
    · rfl
    · generalize i - n = j; cases j <;> simp
      rw [Tm.msubst_lift_fvs_singleton]
      convert ha using 1
      clear * -
      induction n generalizing a <;> simp [*]
  | fv y =>
    simp at hx
    simp only [msubst, Tm.bsubst, get_lift, Ne.symm hx, ↓reduceIte]
    rw [bsubst_lc]
    apply hσ
    simp
  | _ =>
    simp [msubst, Tm.bsubst, <-Function.iterate_succ_apply', -Function.iterate_succ]
    <;> simp at hx
    <;> simp [Tm.MSubst.Lc.union_iff] at hσ
    <;> (try constructorm* _ ∧ _)
    <;> apply_assumption
    <;> simp [*]

theorem Tm.MSubst.Lc.bs0_fvs_singleton {σ : MSubst}
  (t : Tm) (hσ : σ.Lc t.fvs) (x : ℕ) (hx : x ∉ t.fvs) (a : Tm) (ha : a.fvs ⊆ {x})
  : (t.msubst σ).bs0 a = (t.bs0 a).msubst (σ.lift x)
  := hσ.bsubst_fvs_singleton t 0 x hx a ha

theorem Tm.MSubst.Lc.bsubst_var {σ : MSubst}
  (t : Tm) (hσ : σ.Lc t.fvs) (n : ℕ) (x : ℕ) (hx : x ∉ t.fvs)
  : (t.msubst σ).bsubst (BSubst.lift^[n] (Tm.fv x).b0)
  = (t.bsubst (BSubst.lift^[n] (Tm.fv x).b0)).msubst (σ.lift x)
  := hσ.bsubst_fvs_singleton t n x hx (Tm.fv x) (by simp)

theorem Tm.MSubst.Lc.bs0_var {σ : MSubst}
  (t : Tm) (hσ : σ.Lc t.fvs) (x : ℕ) (hx : x ∉ t.fvs)
  : (t.msubst σ).bs0 (.fv x) = (t.bs0 (.fv x)).msubst (σ.lift x)
  := hσ.bsubst_var t 0 x hx

def Tm.MSubst.bwk (f : BWk) (σ : MSubst) : MSubst | x => (σ.get x).bwk f

theorem Tm.MSubst.get_bwk (f : BWk) (σ : MSubst) (n : ℕ) :
  (σ.bwk f).get n = (σ.get n).bwk f := rfl

def Tm.MSubst.bsubst (f : BSubst) (σ : MSubst) : MSubst | x => (f.get x).bsubst σ

theorem Tm.MSubst.get_bsubst (f : BSubst) (σ : MSubst) (n : ℕ) :
  (σ.bsubst f).get n = (f.get n).bsubst σ := rfl

def Tm.BSubst.msubstOut (σ : MSubst) (f : BSubst) : BSubst | i => (f.get i).msubst σ

@[simp]
theorem Tm.BSubst.get_msubstOut (σ : MSubst) (f : BSubst) (i : ℕ) :
  (f.msubstOut σ).get i = (f.get i).msubst σ := rfl

theorem Tm.MSubst.Lc.bwk_msubst (f : BWk) {σ : MSubst} (a : Tm) (hσ : σ.Lc a.fvs) :
  (a.msubst σ).bwk f = (a.bwk f).msubst σ := by
  induction a generalizing f with
  | fv x =>
    apply Tm.bwk_lc
    apply hσ
    simp
  | _ =>
    simp only [Lc.union_iff, Tm.fvs] at hσ
    simp only [msubst, Tm.bwk] <;> congr <;> apply_assumption <;> simp [*]

theorem Tm.MSubst.Lc.bsubst_lift_b0 {σ : MSubst}
  (t : Tm) (hσ : σ.Lc t.fvs) (n : ℕ) (a : Tm) (ha : σ.Lc a.fvs)
  : (t.bsubst (BSubst.lift^[n] a.b0)).msubst σ
  = (t.msubst σ).bsubst (BSubst.lift^[n] (a.msubst σ).b0)
  := by induction t generalizing n with
  | bv i =>
    simp only [msubst, Tm.bsubst, BSubst.get_liftn]
    split
    · rfl
    case isFalse h =>
      clear h
      generalize i - n = j; cases j with
      | zero =>
      simp only [get_zero_b0]
      induction n with
        | zero => rfl
        | succ n I =>
          rw [Function.iterate_succ_apply', <-Lc.bwk_msubst, I, Function.iterate_succ_apply']
          convert ha using 1
          clear * -
          induction n generalizing a <;> simp [*]
      | succ => simp
  | fv x =>
    simp only [Tm.bsubst, msubst]
    rw [Tm.bsubst_lc _]
    apply hσ; simp
  | _ =>
    simp only [msubst, Tm.bsubst, <-Function.iterate_succ_apply']
    <;> simp only [Lc.union_iff, Tm.fvs] at hσ
    <;> congr
    <;> apply_assumption
    <;> simp [*]

theorem Tm.MSubst.Lc.bs0 {σ : MSubst}
  (t : Tm) (hσ : σ.Lc t.fvs) (a : Tm) (ha : σ.Lc a.fvs)
  : (t.bs0 a).msubst σ = (t.msubst σ).bs0 (a.msubst σ)
  := hσ.bsubst_lift_b0 t 0 a ha

theorem Tm.MSubst.Lc.bs0_fvs_empty {σ : MSubst}
  (t : Tm) (hσ : σ.Lc t.fvs) (a : Tm) (ha : a.fvs = ∅)
  : (t.bs0 a).msubst σ = (t.msubst σ).bs0 a := by
  rw [MSubst.Lc.bs0 (hσ := hσ) (ha := by simp [ha]), msubst_fsv_empty (ht := ha)]

theorem Tm.msubst_set_eq (σ : MSubst) (t : Tm) {x : ℕ} (hx : x ∉ t.fvs) (a : Tm) :
  t.msubst (σ.set x a) = t.msubst σ
  := by induction t generalizing σ with
  | fv y => simp only [fvs, Finset.mem_singleton] at hx; simp [MSubst.get_set, Ne.symm hx]
  | _ =>
    simp only [msubst]
    <;> (try simp only [fvs, Finset.mem_union, not_or] at hx)
    <;> congr 1 <;> apply_assumption <;> simp [*]

theorem Tm.msubst_lift_eq (σ : MSubst) (t : Tm) {x : ℕ} (hx : x ∉ t.fvs) :
  t.msubst (σ.lift x) = t.msubst σ
  := t.msubst_set_eq σ hx (.fv x)

def Tm.MSubst.EqOn (X : Finset ℕ) (σ τ : MSubst) : Prop := ∀ x ∈ X, σ.get x = τ.get x

theorem Tm.MSubst.EqOn.symm {σ τ : MSubst} {X : Finset ℕ}
  (h : σ.EqOn X τ) : τ.EqOn X σ := fun x hx => (h x hx).symm

theorem Tm.MSubst.lift_eqOn_of_notMem (σ : MSubst) (x : ℕ) (X : Finset ℕ) (h : x ∉ X)
  : σ.EqOn X (σ.lift x) := fun y hy => by
  rw [get_lift]
  split
  case isTrue h => cases h; contradiction
  simp

@[simp] theorem Tm.MSubst.EqOn.empty (σ τ : MSubst) : σ.EqOn ∅ τ := fun _ h => by cases h

@[simp]
theorem Tm.MSubst.EqOn.singleton_iff {σ τ : MSubst} {x : ℕ} :
  σ.EqOn {x} τ ↔ σ.get x = τ.get x := by
  simp only [EqOn, Finset.mem_singleton, forall_eq]

theorem Tm.MSubst.EqOn.union_iff {σ τ : MSubst} {X Y : Finset ℕ} :
  σ.EqOn (X ∪ Y) τ ↔ σ.EqOn X τ ∧ σ.EqOn Y τ := by
  simp only [EqOn, Finset.forall_mem_union]

theorem Tm.msubst_eqOn_subset {X : Finset ℕ} {σ τ : MSubst}
  (h : σ.EqOn X τ) (t : Tm) (hX : t.fvs ⊆ X) : t.msubst σ = t.msubst τ := by
  induction t generalizing X σ τ with
  | fv x => apply h; convert hX; simp
  | _ =>
    simp only [msubst] <;>
    congr 1 <;>
    apply_assumption <;>
    first | exact h | (simp only [fvs, Finset.union_subset_iff] at hX; simp [*])

theorem Tm.msubst_eqOn (t : Tm) {σ τ : MSubst} (h : σ.EqOn t.fvs τ) : t.msubst σ = t.msubst τ
:= t.msubst_eqOn_subset h (by rfl)

theorem Tm.ms0_bsubst_b0_notMem (t : Tm) (a : Tm) (ha : a.bvi = 0) (n : ℕ)
  : ∀x ∉ t.fvs, (t.bsubst (BSubst.lift^[n] (Tm.fv x).b0)).ms0 x a = t.bsubst (BSubst.lift^[n] a.b0)
  := fun x hx => by
  simp only [ms0]
  induction t generalizing n with
  | bv i =>
    simp only [bsubst, BSubst.get_liftn]
    split
    · rfl
    case isFalse h =>
      generalize i - n = j; cases j <;> simp
      clear h
      induction n with
      | zero => rfl
      | succ n I =>
        rw [Function.iterate_succ_apply', <-I, Tm.bwk_lc]
        exact ha
  | fv y => simp [get_m0]; intro hy; cases hy; simp at hx
  | _ =>
    simp only [bsubst, msubst, <-Function.iterate_succ_apply']
    <;> simp at hx
    <;> congr
    <;> apply_assumption
    <;> simp [*]

theorem Tm.msubst_eqOn_subset_one {X : Finset ℕ} {σ : MSubst}
  (h : σ.EqOn X 1) (t : Tm) (hX : t.fvs ⊆ X) : t.msubst σ = t
  := by rw [t.msubst_eqOn_subset h hX, msubst_one]

theorem Tm.msubst_eqOn_one (t : Tm) {σ : MSubst} (h : σ.EqOn t.fvs 1) : t.msubst σ = t
  := by rw [t.msubst_eqOn h, msubst_one]

theorem Tm.ms0_bs0_notMem (t : Tm) (a : Tm) (ha : a.bvi = 0)
  : ∀x ∉ t.fvs, (t.bs0 (.fv x)).ms0 x a = t.bs0 a
  := t.ms0_bsubst_b0_notMem a ha 0
