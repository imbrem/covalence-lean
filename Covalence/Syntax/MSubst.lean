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
  | .pi A B => .pi (A.msubst σ) (B.msubst σ)
  | .abs A b => .abs (A.msubst σ) (b.msubst σ)
  | .app A B f a => .app (A.msubst σ) (B.msubst σ) (f.msubst σ) (a.msubst σ)
  | .sigma A B => .sigma (A.msubst σ) (B.msubst σ)
  | .pair A B a b => .pair (A.msubst σ) (B.msubst σ) (a.msubst σ) (b.msubst σ)
  | .fst A B a => .fst (A.msubst σ) (B.msubst σ) (a.msubst σ)
  | .snd A B a => .snd (A.msubst σ) (B.msubst σ) (a.msubst σ)
  | .dite φ A a b => .dite (φ.msubst σ) (A.msubst σ) (a.msubst σ) (b.msubst σ)
  | .trunc A => .trunc (A.msubst σ)
  | .choose A φ => .choose (A.msubst σ) (φ.msubst σ)
  | .nats => .nats
  | .zero => .zero
  | .succ => .succ
  | .natrec C n z s => .natrec (C.msubst σ) (n.msubst σ) (z.msubst σ) (s.msubst σ)
  -- | .let₁ A a b => .let₁ (A.msubst σ) (a.msubst σ) (b.msubst σ)
  | .invalid => .invalid

theorem Tm.msubst_fst {σ : MSubst} {A B a : Tm} :
  (Tm.fst A B a).msubst σ = .fst (A.msubst σ) (B.msubst σ) (a.msubst σ) := rfl

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

def Tm.MSubst.lift (σ : MSubst) (x : ℕ) : MSubst := Function.update σ x (.fv x)

theorem Tm.MSubst.get_lift (σ : MSubst) (x : ℕ) (n : ℕ) :
  (σ.lift x).get n = if n = x then .fv x else σ.get n
  := by simp [lift, Function.update, get]

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

theorem Tm.MSubst.Lc.bsubst_var {σ : MSubst}
  (t : Tm) (hσ : σ.Lc t.fvs) (n : ℕ) (x : ℕ) (hx : x ∉ t.fvs)
  : (t.msubst σ).bsubst (BSubst.lift^[n] (Tm.fv x).b0)
  = (t.bsubst (BSubst.lift^[n] (Tm.fv x).b0)).msubst (σ.lift x)
  := by induction t generalizing n with
  | bv i =>
    simp only [msubst, Tm.bsubst, BSubst.get_liftn]
    split
    · rfl
    · generalize i - n = j; cases j <;> simp
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

theorem Tm.msubst_lift_eq (σ : MSubst) (t : Tm) {x : ℕ} (hx : x ∉ t.fvs) :
  t.msubst (σ.lift x) = t.msubst σ
  := by induction t generalizing σ with
  | fv y => simp only [fvs, Finset.mem_singleton] at hx; simp [MSubst.get_lift, Ne.symm hx]
  | _ =>
    simp only [msubst]
    <;> (try simp only [fvs, Finset.mem_union, not_or] at hx)
    <;> congr 1 <;> apply_assumption <;> simp [*]
