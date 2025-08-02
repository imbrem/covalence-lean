import Covalence.Syntax.Basic

def Tm.FSubst := ℕ → Tm

def Tm.FSubst.get (f : Tm.FSubst) (n : ℕ) : Tm := f n

@[ext] theorem Tm.FSubst.get_ext (f g : Tm.FSubst) (h : ∀ n, f.get n = g.get n) : f = g := funext h

instance Tm.FSubst.instOne : One Tm.FSubst where
  one := .fv

@[simp] theorem Tm.FSubst.get_one (n : ℕ) : Tm.FSubst.get 1 n = .fv n := rfl

def Tm.FSubst.wkOut (f : BWk) (σ : Tm.FSubst) : Tm.FSubst | n => (σ.get n).bwk f

@[simp] theorem Tm.FSubst.get_wkOut (f : BWk) (σ : Tm.FSubst) (n : ℕ)
  : (σ.wkOut f).get n = (σ.get n).bwk f := rfl

theorem Tm.FSubst.wkOut_wkOut (f g : BWk) (σ : Tm.FSubst) :
  (σ.wkOut f).wkOut g = σ.wkOut (g * f) := by ext n; simp [bwk_bwk]

def Tm.FSubst.lift (f : Tm.FSubst) : Tm.FSubst := f.wkOut .wk0

prefix:75 "↑f " => Tm.FSubst.lift

@[simp] theorem Tm.FSubst.get_lift (f : Tm.FSubst) (x : ℕ) : (↑f f).get x = ↑0 (f.get x) := rfl

@[simp] theorem Tm.FSubst.lift_one : ↑f 1 = 1 := by ext n; cases n <;> rfl

theorem Tm.FSubst.get_liftn (f : Tm.FSubst) (n : ℕ) (x : ℕ)
  : (FSubst.lift^[n] f).get x = (Tm.bwk BWk.wk0)^[n] (f.get x)
  := by induction n generalizing f
  <;> simp only [Function.iterate_zero, id_eq, Function.iterate_succ_apply', get_lift, *]

theorem Tm.FSubst.lift_wkOut_wk0 (f : BWk) (σ : Tm.FSubst) :
  ↑f (σ.wkOut f) = σ.wkOut (.wk0 * f) := by rw [lift, wkOut_wkOut]

theorem Tm.FSubst.lift_wkOut_lift (f : BWk) (σ : Tm.FSubst) :
  (↑f σ).wkOut (↑b f) = ↑f (σ.wkOut f) := by ext n; simp [bwk_bwk, BWk.lift_mul_wk0]

theorem Tm.FSubst.lift_wkOut (f : BWk) (σ : Tm.FSubst) :
  ↑f (σ.wkOut f) = (↑f σ).wkOut (↑b f) := by rw [lift_wkOut_lift]

@[simp]
def Tm.fsubst (σ : FSubst) : Tm → Tm
  | .fv x => σ.get x
  | .bv i => .bv i
  | .univ ℓ => .univ ℓ
  | .unit ℓ => .unit ℓ
  | .nil ℓ => .nil ℓ
  | .empty ℓ => .empty ℓ
  | .eqn A a b => .eqn (A.fsubst σ) (a.fsubst σ) (b.fsubst σ)
  | .pi ℓ A B => .pi ℓ (A.fsubst σ) (B.fsubst (↑f σ))
  | .abs ℓ A B b => .abs ℓ (A.fsubst σ) (B.fsubst (↑f σ)) (b.fsubst (↑f σ))
  | .app A B f a => .app (A.fsubst σ) (B.fsubst (↑f σ)) (f.fsubst σ) (a.fsubst σ)
  | .sigma ℓ A B => .sigma ℓ (A.fsubst σ) (B.fsubst (↑f σ))
  | .pair ℓ A B a b => .pair ℓ (A.fsubst σ) (B.fsubst (↑f σ)) (a.fsubst σ) (b.fsubst σ)
  | .fst A B a => .fst (A.fsubst σ) (B.fsubst (↑f σ)) (a.fsubst σ)
  | .snd A B a => .snd (A.fsubst σ) (B.fsubst (↑f σ)) (a.fsubst σ)
  | .dite φ A a b => .dite (φ.fsubst σ) (A.fsubst σ) (a.fsubst σ) (b.fsubst σ)
  | .trunc A => .trunc (A.fsubst σ)
  | .choose A φ => .choose (A.fsubst σ) (φ.fsubst (↑f σ))
  | .nats => .nats
  | .zero => .zero
  | .succ => .succ
  | .natrec C n z s => .natrec (C.fsubst (↑f σ)) (n.fsubst σ) (z.fsubst σ) (s.fsubst (↑f σ))
  | .let₁ A a b => .let₁ (A.fsubst σ) (a.fsubst σ) (b.fsubst (↑f σ))
  | .invalid => .invalid

@[simp]
theorem Tm.fsubst_one (t : Tm) : t.fsubst 1 = t := by induction t <;> simp [*]

instance Tm.FSubst.instMul : Mul Tm.FSubst where
  mul f g := fun n => (g.get n).fsubst f

@[simp]
theorem Tm.FSubst.get_mul (f g : Tm.FSubst) (n : ℕ) : (f * g).get n = (g.get n).fsubst f := rfl

theorem Tm.bwk_fsubst_wkOut (f : BWk) (σ : Tm.FSubst) (t : Tm) :
  (t.bwk f).fsubst (σ.wkOut f) = (t.fsubst σ).bwk f := by
  induction t generalizing f σ <;> simp [FSubst.lift_wkOut, *]

theorem Tm.bwk_fsubst (t : Tm) (f : BWk) (σ : Tm.FSubst) :
   (t.fsubst σ).bwk f = (t.bwk f).fsubst (σ.wkOut f) := by rw [bwk_fsubst_wkOut]

theorem Tm.wk0_fsubst_lift (σ : Tm.FSubst) (t : Tm) : (↑0 t).fsubst (↑f σ) = ↑0 (t.fsubst σ)
  := bwk_fsubst_wkOut .wk0 σ t

theorem Tm.FSubst.lift_mul (f g : Tm.FSubst) : ↑f (f * g) = ↑f f * ↑f g
  := by ext n; simp [Tm.wk0_fsubst_lift]

theorem Tm.fsubst_mul (t : Tm) (f g : FSubst) : t.fsubst (f * g) = (t.fsubst g).fsubst f := by
  induction t generalizing f g <;> simp [FSubst.lift_mul, *]

instance Tm.FSubst.instMonoid : Monoid Tm.FSubst where
  mul_assoc f g h := by ext n; simp [fsubst_mul]
  one_mul f := by ext n; simp
  mul_one f := by ext n; simp

def Tm.FSubst.bsubstOut (f : BSubst) (σ : Tm.FSubst) : FSubst | x => (σ.get x).bsubst f

@[simp]
theorem Tm.FSubst.get_bsubstOut (f : BSubst) (σ : Tm.FSubst) (x : ℕ) :
  (σ.bsubstOut f).get x = (σ.get x).bsubst f := rfl

-- theorem Tm.FSubst.lift_bsubstOut_wk0 (f : BSubst) (σ : Tm.FSubst) :
--   ↑f (σ.bsubstOut f) = σ.bsubstOut (f.wkOut .wk0) := by sorry

theorem Tm.FSubst.lift_bsubstOut_lift (f : BSubst) (σ : Tm.FSubst) :
  (↑f σ).bsubstOut (↑s f) = ↑f (σ.bsubstOut f) := by ext n; simp [bsubst_lift_wk0]

theorem Tm.FSubst.lift_bsubstOut (f : BSubst) (σ : Tm.FSubst) :
  ↑f (σ.bsubstOut f) = (↑f σ).bsubstOut (↑s f) := by rw [lift_bsubstOut_lift]

def Tm.BSubst.fsubstOut (σ : Tm.FSubst) (f : BSubst) : BSubst | i => (f.get i).fsubst σ

@[simp]
theorem Tm.BSubst.get_fsubstOut (σ : Tm.FSubst) (f : BSubst) (i : ℕ) :
  (f.fsubstOut σ).get i = (f.get i).fsubst σ := rfl

def Tm.FSubst.set (σ : FSubst) (x : ℕ) (t : Tm) : FSubst := Function.update σ x t

theorem Tm.FSubst.get_set (σ : FSubst) (x : ℕ) (t : Tm) (y : ℕ) :
  (σ.set x t).get y = if y = x then t else σ.get y
  := by simp [set, Function.update, get]

def Tm.f0 (x : ℕ) (t : Tm) : Tm.FSubst := FSubst.set 1 x t

theorem Tm.get_f0 (t : Tm) (x : ℕ) (y : ℕ) :
  (t.f0 x).get y = if y = x then t else .fv y
  := by simp [f0, FSubst.get_set]

@[simp] theorem Tm.get_f0_self (t : Tm) (x : ℕ) : (t.f0 x).get x = t := by simp [get_f0]

def Tm.fs0 (t : Tm) (x : ℕ) (a : Tm) : Tm := t.fsubst (a.f0 x)
