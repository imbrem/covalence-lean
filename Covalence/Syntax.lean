import Covalence.Ren
import Mathlib.Tactic.CasesM
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Lattice

inductive Tm : Type
| fv (x : ℕ) : Tm
| bv (i : ℕ) : Tm
| univ (ℓ : ℕ) : Tm
| unit (ℓ : ℕ) : Tm
| nil (ℓ : ℕ) : Tm
| empty (ℓ : ℕ) : Tm
| eqn (A a b : Tm) : Tm
| pi (A B : Tm) : Tm
| abs (A b : Tm) : Tm
| app (A B f a : Tm) : Tm
| sigma (A B : Tm) : Tm
| pair (A B a b : Tm) : Tm
| fst (A B a : Tm) : Tm
| snd (A B a : Tm) : Tm
| dite (φ A a b : Tm) : Tm
| trunc (A : Tm) : Tm
| choose (A φ : Tm) : Tm
| nats : Tm
| zero : Tm
| succ : Tm
| natrec (C n z s : Tm) : Tm
-- | let₁ (A a b : Tm) : Tm
| invalid : Tm

abbrev Tm.not (t : Tm) : Tm := .pi t (.empty 0)

@[simp]
def Tm.fvs : Tm → Finset ℕ
  | .fv x => {x}
  | .eqn A a b => A.fvs ∪ a.fvs ∪ b.fvs
  | .pi A B => A.fvs ∪ B.fvs
  | .abs A b => A.fvs ∪ b.fvs
  | .app A B f a => A.fvs ∪ B.fvs ∪ f.fvs ∪ a.fvs
  | .sigma A B => A.fvs ∪ B.fvs
  | .pair A B a b => A.fvs ∪ B.fvs ∪ a.fvs ∪ b.fvs
  | .fst A B a => A.fvs ∪ B.fvs ∪ a.fvs
  | .snd A B a => A.fvs ∪ B.fvs ∪ a.fvs
  | .dite φ A a b => φ.fvs ∪ A.fvs ∪ a.fvs ∪ b.fvs
  | .trunc A => A.fvs
  | .choose A φ => A.fvs ∪ φ.fvs
  | .natrec C n z s => C.fvs ∪ n.fvs ∪ z.fvs ∪ s.fvs
  -- | .let₁ A a b => A.fvs ∪ a.fvs ∪ b.fvs
  | _ => ∅

def Tm.bvi : Tm → ℕ
  | .bv i => (i + 1)
  | .eqn A a b => A.bvi ⊔ a.bvi ⊔ b.bvi
  | .pi A B => A.bvi ⊔ (B.bvi - 1)
  | .abs A b => A.bvi ⊔ (b.bvi - 1)
  | .app A B f a => A.bvi ⊔ (B.bvi - 1) ⊔ f.bvi ⊔ a.bvi
  | .sigma A B => A.bvi ⊔ (B.bvi - 1)
  | .pair A B a b => A.bvi ⊔ (B.bvi - 1) ⊔ a.bvi ⊔ b.bvi
  | .fst A B a => A.bvi ⊔ (B.bvi - 1) ⊔ a.bvi
  | .snd A B a => A.bvi ⊔ (B.bvi - 1) ⊔ a.bvi
  | .dite φ A a b => φ.bvi ⊔ A.bvi ⊔ a.bvi ⊔ b.bvi
  | .trunc A => A.bvi
  | .choose A φ => A.bvi ⊔ (φ.bvi - 1)
  | .natrec C n z s => (C.bvi - 1) ⊔ n.bvi ⊔ z.bvi ⊔ (s.bvi - 1)
  -- | .let₁ A a b => A.bvi ⊔ a.bvi ⊔ (b.bvi - 1)
  | _ => 0

@[simp]
def Tm.bwk (ρ : BWk) : Tm → Tm
  | .fv x => .fv x
  | .bv i => .bv (ρ.get i)
  | .univ ℓ => .univ ℓ
  | .unit ℓ => .unit ℓ
  | .nil ℓ => .nil ℓ
  | .empty ℓ => .empty ℓ
  | .eqn A a b => .eqn (A.bwk ρ) (a.bwk ρ) (b.bwk ρ)
  | .pi A B => .pi (A.bwk ρ) (B.bwk (↑b ρ))
  | .abs A b => .abs (A.bwk ρ) (b.bwk (↑b ρ))
  | .app A B f a => .app (A.bwk ρ) (B.bwk (↑b ρ)) (f.bwk ρ) (a.bwk ρ)
  | .sigma A B => .sigma (A.bwk ρ) (B.bwk (↑b ρ))
  | .pair A B a b => .pair (A.bwk ρ) (B.bwk (↑b ρ)) (a.bwk ρ) (b.bwk ρ)
  | .fst A B a => .fst (A.bwk ρ) (B.bwk (↑b ρ)) (a.bwk ρ)
  | .snd A B a => .snd (A.bwk ρ) (B.bwk (↑b ρ)) (a.bwk ρ)
  | .dite φ A a b => .dite (φ.bwk ρ) (A.bwk ρ) (a.bwk ρ) (b.bwk ρ)
  | .trunc A => .trunc (A.bwk ρ)
  | .choose A φ => .choose (A.bwk ρ) (φ.bwk (↑b ρ))
  | .nats => .nats
  | .zero => .zero
  | .succ => .succ
  | .natrec C n z s => .natrec (C.bwk (↑b ρ)) (n.bwk ρ) (z.bwk ρ) (s.bwk (↑b ρ))
  -- | .let₁ A a b => .let₁ (A.bwk ρ) (a.bwk ρ) (b.bwk (↑b ρ))
  | .invalid => .invalid

@[simp] theorem Tm.bwk_one (t : Tm) : t.bwk 1 = t := by induction t <;> simp [*]

theorem Tm.bwk_mul (f g : BWk) (t : Tm) : t.bwk (f * g) = (t.bwk g).bwk f := by
  induction t generalizing f g <;> simp [*]

theorem Tm.bwk_bwk (f g : BWk) (t : Tm) : (t.bwk g).bwk f = t.bwk (f * g) := by rw [bwk_mul]

theorem Tm.bwk_eqOn (t : Tm) {f g : BWk} (h : f.EqOn t.bvi g) : t.bwk f = t.bwk g
  := by induction t generalizing f g with
  | bv => simp only [bwk, bv.injEq]; apply h; simp [bvi]
  | _ =>
    simp only [bvi, BWk.EqOn.sup_iff, BWk.EqOn.pred_iff_lift] at *
    grind [bwk]

@[simp]
theorem Tm.bwk_eqOn_id (t : Tm) {f : BWk} (h : f.EqOn t.bvi 1) : t.bwk f = t
  := (t.bwk_eqOn h).trans t.bwk_one

@[simp]
theorem Tm.bwk_lc (t : Tm) (h : t.bvi = 0) (f : BWk) : t.bwk f = t := t.bwk_eqOn_id (by simp [h])

prefix:75 "↑0 " => Tm.bwk BWk.wk0

def Tm.BSubst := ℕ → Tm

def Tm.BSubst.get (f : Tm.BSubst) (n : ℕ) : Tm := f n

@[ext] theorem Tm.BSubst.get_ext (f g : Tm.BSubst) (h : ∀ n, f.get n = g.get n) : f = g := funext h

def Tm.BSubst.lift (f : Tm.BSubst) : Tm.BSubst | 0 => .bv 0 | n + 1 => ↑0 (f.get n)

@[simp] theorem Tm.BSubst.get_zero_lift (f : Tm.BSubst) : f.lift.get 0 = .bv 0 := rfl

@[simp]
theorem Tm.BSubst.get_succ_lift (f : Tm.BSubst) (n : ℕ) : f.lift.get (n + 1) = ↑0 (f.get n) := rfl

prefix:75 "↑s " => Tm.BSubst.lift

instance Tm.BSubst.instOne : One Tm.BSubst where
  one := .bv

@[simp] theorem Tm.BSubst.get_one (n : ℕ) : Tm.BSubst.get 1 n = .bv n := rfl

@[simp] theorem Tm.BSubst.lift_one : ↑s 1 = 1 := by ext n; cases n <;> rfl

@[simp]
def Tm.bsubst (σ : BSubst) : Tm → Tm
  | .fv x => .fv x
  | .bv i => σ.get i
  | .univ ℓ => .univ ℓ
  | .unit ℓ => .unit ℓ
  | .nil ℓ => .nil ℓ
  | .empty ℓ => .empty ℓ
  | .eqn A a b => .eqn (A.bsubst σ) (a.bsubst σ) (b.bsubst σ)
  | .pi A B => .pi (A.bsubst σ) (B.bsubst (↑s σ))
  | .abs A b => .abs (A.bsubst σ) (b.bsubst (↑s σ))
  | .app A B f a => .app (A.bsubst σ) (B.bsubst (↑s σ)) (f.bsubst σ) (a.bsubst σ)
  | .sigma A B => .sigma (A.bsubst σ) (B.bsubst (↑s σ))
  | .pair A B a b => .pair (A.bsubst σ) (B.bsubst (↑s σ)) (a.bsubst σ) (b.bsubst σ)
  | .fst A B a => .fst (A.bsubst σ) (B.bsubst (↑s σ)) (a.bsubst σ)
  | .snd A B a => .snd (A.bsubst σ) (B.bsubst (↑s σ)) (a.bsubst σ)
  | .dite φ A a b => .dite (φ.bsubst σ) (A.bsubst σ) (a.bsubst σ) (b.bsubst σ)
  | .trunc A => .trunc (A.bsubst σ)
  | .choose A φ => .choose (A.bsubst σ) (φ.bsubst (↑s σ))
  | .nats => .nats
  | .zero => .zero
  | .succ => .succ
  | .natrec C n z s => .natrec (C.bsubst (↑s σ)) (n.bsubst σ) (z.bsubst σ) (s.bsubst (↑s σ))
  -- | .let₁ A a b => .let₁ (A.bsubst σ) (a.bsubst σ) (b.bsubst (↑s σ))
  | .invalid => .invalid

@[simp] theorem Tm.bsubst_one (t : Tm) : t.bsubst 1 = t := by induction t <;> simp [*]

instance Tm.BSubst.instMul : Mul Tm.BSubst where
  mul f g := fun n => (g.get n).bsubst f

@[simp]
theorem Tm.BSubst.get_mul (f g : Tm.BSubst) (n : ℕ) : (f * g).get n = (g.get n).bsubst f := rfl

def Tm.BSubst.ofWk (f : BWk) : Tm.BSubst := fun n => .bv (f.get n)

@[simp]
theorem Tm.BSubst.get_ofWk (f : BWk) (n : ℕ) : Tm.BSubst.get (Tm.BSubst.ofWk f) n = .bv (f.get n)
  := rfl

theorem Tm.BSubst.ofWk_one : Tm.BSubst.ofWk 1 = 1 := rfl

theorem Tm.BSubst.ofWk_mul (f g : BWk) : ofWk (f * g) = ofWk f * ofWk g := rfl

theorem Tm.BSubst.ofWk_mul_ofWk (f g : BWk) : ofWk f * ofWk g = ofWk (f * g)
  := (ofWk_mul f g).symm

theorem Tm.BSubst.ofWk_lift (f : BWk) : Tm.BSubst.ofWk (↑b f) = ↑s (Tm.BSubst.ofWk f)
  := by ext n; cases n <;> rfl

theorem Tm.BSubst.lift_ofWk (f : BWk) : ↑s (Tm.BSubst.ofWk f) = Tm.BSubst.ofWk (↑b f)
  := by ext n; cases n <;> rfl

@[simp]
theorem Tm.bsubst_ofWk (t : Tm) (f : BWk) : t.bsubst (.ofWk f) = t.bwk f
  := by induction t generalizing f <;> simp [*, Tm.BSubst.lift_ofWk, *]

def Tm.BSubst.wkIn (f : BWk) (σ : BSubst) : BSubst | n => σ.get (f.get n)

theorem Tm.BSubst.mul_ofWk (f : BWk) (σ : BSubst) : σ * (.ofWk f) = σ.wkIn f := rfl

@[simp]
theorem Tm.BSubst.get_wkIn (f : BWk) (σ : BSubst) (n : ℕ) : (σ.wkIn f).get n = σ.get (f.get n)
  := rfl

@[simp]
theorem Tm.BSubst.lift_wkIn (f : BWk) (σ : BSubst) : ↑s (σ.wkIn f) = (↑s σ).wkIn (↑b f)
  := by ext n; cases n <;> simp

theorem Tm.bsubst_wkIn (t : Tm) (f : BWk) (σ : BSubst) :
  t.bsubst (σ.wkIn f) = (t.bwk f).bsubst σ
  := by induction t generalizing f σ <;> simp [*]

def Tm.BSubst.wkOut (f : BWk) (σ : BSubst) : BSubst | n => (σ.get n).bwk f

@[simp]
theorem Tm.BSubst.get_wkOut (f : BWk) (σ : BSubst) (n : ℕ) : (σ.wkOut f).get n = (σ.get n).bwk f
  := rfl

theorem Tm.BSubst.mul_ofWk_left (f : BWk) (σ : BSubst) : .ofWk f * σ = σ.wkOut f := by ext n; simp

@[simp]
theorem Tm.BSubst.lift_wkOut (f : BWk) (σ : BSubst) : ↑s (σ.wkOut f) = (↑s σ).wkOut (↑b f)
  := by ext n; cases n <;> simp [Tm.bwk_bwk, BWk.lift_mul_wk0]

theorem Tm.bsubst_wkOut (t : Tm) (f : BWk) (σ : BSubst) :
  t.bsubst (σ.wkOut f) = (t.bsubst σ).bwk f
  := by induction t generalizing f σ <;> simp [*]

theorem Tm.BSubst.lift_wkIn_wk0 (σ : BSubst) : (↑s σ).wkIn .wk0 = σ.wkOut .wk0 := by
  ext n; cases n <;> simp

@[simp]
theorem Tm.BSubst.lift_mul (f g : Tm.BSubst) :
  ↑s (f * g) = ↑s f * ↑s g := by ext n; cases n with
  | zero => rfl
  | succ n => simp only [get_succ_lift, get_mul, <-Tm.bsubst_wkIn, <-Tm.bsubst_wkOut, lift_wkIn_wk0]

theorem Tm.bsubst_mul (t : Tm) (f g : BSubst) : t.bsubst (f * g) = (t.bsubst g).bsubst f := by
  induction t generalizing f g <;> simp [*]

theorem Tm.bsubst_bsubst (t : Tm) (f g : BSubst) : (t.bsubst g).bsubst f = t.bsubst (f * g) := by
  rw [bsubst_mul]

theorem Tm.bsubst_lift_wk0 (t : Tm) (f : BSubst) : (↑0 t).bsubst (↑s f) = ↑0 (t.bsubst f)
  := by rw [<-Tm.bsubst_wkIn, BSubst.lift_wkIn_wk0, Tm.bsubst_wkOut]

instance Tm.BSubst.instMonoid : Monoid Tm.BSubst where
  mul_assoc f g h := by ext n; simp [bsubst_mul]
  one_mul f := by ext n; simp
  mul_one f := by ext n; simp

def Tm.BSubst.EqOn (n : ℕ) (σ τ : Tm.BSubst) : Prop := ∀i < n, σ.get i = τ.get i

theorem Tm.BSubst.EqOn.sup_iff {n m : ℕ} {σ τ : Tm.BSubst} :
  σ.EqOn (n ⊔ m) τ ↔ σ.EqOn n τ ∧ σ.EqOn m τ := by
  simp only [EqOn]
  rw [<-forall_and]
  apply forall_congr'
  grind

@[simp] theorem Tm.BSubst.EqOn.zero {σ τ : Tm.BSubst} : σ.EqOn 0 τ := by intro i hi; cases hi

theorem Tm.BSubst.EqOn.lift {n : ℕ} (f g : Tm.BSubst) (h : Tm.BSubst.EqOn n f g) :
  Tm.BSubst.EqOn (n + 1) (↑s f) (↑s g) := fun i hi => by cases i with
  | zero => rfl
  | succ i => rw [get_succ_lift, get_succ_lift, h i]; omega

theorem Tm.bwk_inj {f : BWk} (hf : f.Inj) : Function.Injective (Tm.bwk f) := by
  intro t s hts
  induction t generalizing s f with
  | bv i =>
    cases s <;> simp at hts
    rw [hf.get hts]
  | _ =>
    have hf' := hf.lift
    cases s <;> simp at hts
    (try casesm* _ ∧ _)
    simp <;> (try constructorm* _ ∧ _) <;> solve_by_elim

theorem Tm.bwk0_inj : Function.Injective (Tm.bwk BWk.wk0) := Tm.bwk_inj .wk0

theorem Tm.BSubst.EqOn.of_succ_lift {n : ℕ}
  (f g : Tm.BSubst) (h : Tm.BSubst.EqOn (n + 1) f.lift g.lift)
  : f.EqOn n g := fun i hi => by
  convert h (i + 1) (by omega) using 0; simp; exact Tm.bwk0_inj.eq_iff.symm

theorem Tm.BSubst.EqOn.succ_lift_iff {n : ℕ} (f g : Tm.BSubst)
  : f.lift.EqOn (n + 1) g.lift ↔ f.EqOn n g := ⟨fun h => h.of_succ_lift, fun h => h.lift⟩

theorem Tm.BSubst.EqOn.pred_iff_lift (n : ℕ) (f g : Tm.BSubst) :
  f.EqOn (n - 1) g ↔ f.lift.EqOn n g.lift := by cases n <;> simp [succ_lift_iff]

theorem Tm.bsubst_eqOn (t : Tm) {f g : BSubst} (h : f.EqOn t.bvi g) : t.bsubst f = t.bsubst g := by
  induction t generalizing f g with
  | bv i => exact h i (by simp [bvi])
  | _ =>
    simp only [bvi, BSubst.EqOn.sup_iff, BSubst.EqOn.pred_iff_lift] at *
    grind [bsubst]

theorem Tm.bsubst_eqOn_id (t : Tm) {f : BSubst} (h : f.EqOn t.bvi 1) : t.bsubst f = t
  := (t.bsubst_eqOn h).trans t.bsubst_one

@[simp]
theorem Tm.bsubst_lc (t : Tm) (h : t.bvi = 0) (f : BSubst) : t.bsubst f = t
  := t.bsubst_eqOn_id (by simp [h])

def Tm.b0 (t : Tm) : BSubst | 0 => t | n + 1 => .bv n

@[simp] theorem Tm.get_zero_b0 (t : Tm) : t.b0.get 0 = t := rfl

@[simp] theorem Tm.get_succ_b0 (t : Tm) (n : ℕ) : t.b0.get (n + 1) = .bv n := rfl

def Tm.bs0 (t : Tm) (s : Tm) : Tm := t.bsubst s.b0

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

theorem Tm.BSubst.get_liftn (σ : BSubst) (n : ℕ) (i : ℕ)
  : (BSubst.lift^[n] σ).get i = if i < n then .bv i else (Tm.bwk BWk.wk0)^[n] (σ.get (i - n))
  := by induction n generalizing i with
  | zero => rfl
  | succ n I =>
    rw [Function.iterate_succ_apply']
    cases i with
    | zero => simp only [get_zero_lift, Nat.zero_lt_succ, ↓reduceIte]
    | succ i =>
      simp only [get_succ_lift, Nat.add_lt_add_iff_right, Nat.reduceSubDiff, Function.iterate_succ,
        Function.comp_apply, I]
      split
      · rfl
      · rw [
          <-Function.iterate_succ_apply' (f := Tm.bwk BWk.wk0),
          <-Function.iterate_succ_apply (f := Tm.bwk BWk.wk0)
        ]

@[simp]
theorem Tm.bwk_iter_fv (f : BWk) (n : ℕ) (x : ℕ)
  : (Tm.bwk f)^[n] (.fv x) = .fv x := by induction n <;> simp [*]

@[simp]
theorem Tm.bwk_bwk0_iter_bv (n : ℕ) (i : ℕ)
  : (Tm.bwk BWk.wk0)^[n] (.bv i) = .bv (i + n) := by induction n generalizing i <;> simp +arith [*]

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

@[simp] theorem Tm.FSubst.get_lift (f : Tm.FSubst) (n : ℕ) : (↑f f).get n = ↑0 (f.get n) := rfl

@[simp] theorem Tm.FSubst.lift_one : ↑f 1 = 1 := by ext n; cases n <;> rfl

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
  | .pi A B => .pi (A.fsubst σ) (B.fsubst (↑f σ))
  | .abs A b => .abs (A.fsubst σ) (b.fsubst (↑f σ))
  | .app A B f a => .app (A.fsubst σ) (B.fsubst (↑f σ)) (f.fsubst σ) (a.fsubst σ)
  | .sigma A B => .sigma (A.fsubst σ) (B.fsubst (↑f σ))
  | .pair A B a b => .pair (A.fsubst σ) (B.fsubst (↑f σ)) (a.fsubst σ) (b.fsubst σ)
  | .fst A B a => .fst (A.fsubst σ) (B.fsubst (↑f σ)) (a.fsubst σ)
  | .snd A B a => .snd (A.fsubst σ) (B.fsubst (↑f σ)) (a.fsubst σ)
  | .dite φ A a b => .dite (φ.fsubst σ) (A.fsubst σ) (a.fsubst σ) (b.fsubst σ)
  | .trunc A => .trunc (A.fsubst σ)
  | .choose A φ => .choose (A.fsubst σ) (φ.fsubst (↑f σ))
  | .nats => .nats
  | .zero => .zero
  | .succ => .succ
  | .natrec C n z s => .natrec (C.fsubst (↑f σ)) (n.fsubst σ) (z.fsubst σ) (s.fsubst (↑f σ))
  -- | .let₁ A a b => .let₁ (A.fsubst σ) (a.fsubst σ) (b.fsubst (↑f σ))
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

-- theorem Tm.bsubst_fsubst (t : Tm) (f : BSubst) (σ : Tm.FSubst) :
--   (t.fsubst σ).bsubst f = (t.bsubst f).fsubst (σ.bsubstOut f) := by
--   induction t generalizing σ f <;> simp [*]
--   sorry

def Tm.BSubst.fsubstOut (σ : Tm.FSubst) (f : BSubst) : BSubst | i => (f.get i).fsubst σ

@[simp]
theorem Tm.BSubst.get_fsubstOut (σ : Tm.FSubst) (f : BSubst) (i : ℕ) :
  (f.fsubstOut σ).get i = (f.get i).fsubst σ := rfl

@[simp]
  theorem Tm.fvs_bwk (t : Tm) (f : BWk) : (t.bwk f).fvs = t.fvs
  := by induction t generalizing f <;> simp [*]

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

def Tm.BSubst.FvSub (f : Tm.BSubst) (X : Finset ℕ) : Prop := ∀i, (f.get i).fvs ⊆ X

theorem Tm.BSubst.FvSub.mono {f : Tm.BSubst} {X Y : Finset ℕ}
  (h : f.FvSub X) (hXY : X ⊆ Y) : f.FvSub Y := fun i => (h i).trans hXY

@[simp]
theorem Tm.BSubst.fv_sub_wkOut_iff (f : BWk) (ρ : Tm.BSubst) (X : Finset ℕ)
  : (ρ.wkOut f).FvSub X ↔ ρ.FvSub X := forall_congr' (fun i => by simp)

theorem Tm.BSubst.FvSub.lift {f : Tm.BSubst} {X : Finset ℕ} (h : f.FvSub X)
  : (↑s f).FvSub X | 0 => by simp | i + 1 => by simp [h i]

theorem Tm.BSubst.FvSub.of_lift {f : Tm.BSubst} {X : Finset ℕ} (h : (↑s f).FvSub X)
  : f.FvSub X | i => by convert h (i + 1) using 0; simp only [get_succ_lift, fvs_bwk]; rfl

@[simp]
theorem Tm.BSubst.fv_sub_lift_iff (f : Tm.BSubst) (X : Finset ℕ) : (↑s f).FvSub X ↔ f.FvSub X
  := ⟨FvSub.of_lift, FvSub.lift⟩

theorem Tm.BSubst.FvSub.bsubst {f : Tm.BSubst} {X : Finset ℕ}
  (h : f.FvSub X) {t : Tm} (ht : t.fvs ⊆ X) : (t.bsubst f).fvs ⊆ X
  := by
  induction t generalizing f with
  | bv i => exact h i
  | fv => exact ht
  | _ =>
    simp [Finset.union_subset_iff, *] at *
    (try (try constructorm* _ ∧ _) <;> apply_assumption <;> simp [*])

theorem Tm.b0_fv_sub {t : Tm} {X : Finset ℕ} (h : t.fvs ⊆ X) : t.b0.FvSub X
  | 0 => h | i + 1 => by simp

theorem Tm.bs0_fv_sub {t : Tm} {s : Tm} {X : Finset ℕ}
  (ht : t.fvs ⊆ X) (hs : s.fvs ⊆ X) : (t.bs0 s).fvs ⊆ X
  := (s.b0_fv_sub hs).bsubst ht

@[simp]
theorem Tm.bs0_fvs (t s : Tm) : (t.bs0 s).fvs ⊆ s.fvs ∪ t.fvs := bs0_fv_sub (by simp) (by simp)

@[simp]
theorem Tm.bs0_var_fvs (t : Tm) (x : ℕ) : (t.bs0 (.fv x)).fvs ⊆ {x} ∪ t.fvs := t.bs0_fvs (.fv x)

theorem Tm.bs0_var_sub {t : Tm} {X : Finset ℕ} (ht : t.fvs ⊆ X) (x : ℕ)
  : (t.bs0 (.fv x)).fvs ⊆ {x} ∪ X := (t.bs0_var_fvs x).trans (Finset.union_subset_union_right ht)

@[simp]
theorem Tm.fvs_bsubst_sub (f : BSubst) (t : Tm) : t.fvs ⊆ (t.bsubst f).fvs
  := by induction t generalizing f with
  | _ => simp <;> (repeat first | apply Finset.union_subset_union | apply_assumption)

@[simp] theorem Tm.fvs_bs0_sub (t : Tm) (s : Tm) : t.fvs ⊆ (t.bs0 s).fvs := t.fvs_bsubst_sub s.b0

theorem Tm.bs0_var_not_mem {t : Tm} {x : ℕ} {X : Finset ℕ} (hx : x ∉ t.fvs)
  (hX : (t.bs0 (.fv x)).fvs ⊆ {x} ∪ X) : t.fvs ⊆ X := by
  rw [<-Finset.subset_insert_iff_of_notMem hx, Finset.insert_eq]
  exact (t.fvs_bs0_sub (.fv x)).trans hX

theorem Tm.bs0_var_not_mem_iff (t : Tm) (x : ℕ) (X : Finset ℕ) (hx : x ∉ t.fvs)
  : (t.bs0 (.fv x)).fvs ⊆ {x} ∪ X ↔ t.fvs ⊆ X
  := ⟨fun hX => bs0_var_not_mem hx hX, fun hX => t.bs0_var_sub hX x⟩

theorem Tm.bs0_var_cofinite {t : Tm} {X : Finset ℕ} {L : Finset ℕ}
  (hX : ∀ x ∉ L, (t.bs0 (.fv x)).fvs ⊆ {x} ∪ X) : t.fvs ⊆ X := by
  have ⟨x, hx⟩ := (t.fvs ∪ L).exists_notMem
  simp only [Finset.mem_union, not_or] at hx
  apply bs0_var_not_mem (x := x) <;> simp only [not_false_eq_true, hx, hX]

theorem Tm.bs0_var_cofinite_iff (t : Tm) (X : Finset ℕ) (L : Finset ℕ)
  : (∀ x ∉ L, (t.bs0 (.fv x)).fvs ⊆ {x} ∪ X) ↔ t.fvs ⊆ X
  := ⟨fun h => t.bs0_var_cofinite h, fun hX x _ => t.bs0_var_sub hX x⟩

theorem Tm.fsv_cofinite {t : Tm} {X : Finset ℕ} {L : Finset ℕ}
  (hX : ∀ x ∉ L, t.fvs ⊆ {x} ∪ X) : t.fvs ⊆ X := by
  have ⟨x, hx⟩ := (t.fvs ∪ L).exists_notMem
  simp only [Finset.mem_union, not_or] at hx
  rw [<-Finset.subset_insert_iff_of_notMem hx.1, Finset.insert_eq]
  exact hX _ hx.2

theorem Tm.fsv_cofinite_iff (t : Tm) (X : Finset ℕ) (L : Finset ℕ)
  : (∀ x ∉ L, t.fvs ⊆ {x} ∪ X) ↔ t.fvs ⊆ X
  := ⟨fun hX => fsv_cofinite hX, fun hX _ _ => hX.trans Finset.subset_union_right⟩

theorem BWk.lift_get_i_lt_succ (f : BWk) (ℓ : ℕ) (m : ℕ)
  (h : ∀ i < ℓ - 1, f.get i < m) : ∀i < ℓ, (↑b f).get i < m + 1
  := fun i hi => by cases i with | zero => simp | succ i => have hf := h i (by omega); simp [hf]

theorem Tm.bvi_bwk_le (f : BWk) (t : Tm) (m : ℕ)
  (h : ∀ i < t.bvi, f.get i < m) : (t.bwk f).bvi ≤ m
  := by induction t generalizing f m with
  | bv i => exact h i (by simp [bvi])
  | _ =>
    simp only [bvi, bwk, Nat.zero_le, Nat.max_le, Nat.sub_le_iff_le_add, *] at * <;>
    (try constructorm* _ ∧ _) <;>
    apply_assumption <;>
    (try apply BWk.lift_get_i_lt_succ) <;>
    intro i hi <;>
    apply_assumption <;>
    simp [*]

theorem Tm.bvi_wk0_le (t : Tm) : (↑0 t).bvi ≤ t.bvi + 1
  := t.bvi_bwk_le _ _ (fun i hi => by simp [hi])

theorem Tm.BSubst.lift_get_i_le_succ (f : Tm.BSubst) (ℓ : ℕ) (m : ℕ)
  (h : ∀ i < ℓ - 1, (f.get i).bvi ≤ m) : ∀i < ℓ, ((↑s f).get i).bvi ≤ m + 1
  := fun i hi => by cases i with
  | zero => simp [bvi]
  | succ i => have hf := h i (by omega); apply le_trans (bvi_wk0_le _); simp [hf]

theorem Tm.bvi_bsubst_le (f : BSubst) (t : Tm) (m : ℕ)
  (h : ∀ i < t.bvi, (f.get i).bvi ≤ m) : (t.bsubst f).bvi ≤ m
  := by induction t generalizing f m with
  | bv i => exact h i (by simp [bvi])
  | _ =>
    simp only [bvi, bsubst, Nat.zero_le, Nat.max_le, Nat.sub_le_iff_le_add, *] at * <;>
    (try constructorm* _ ∧ _) <;>
    apply_assumption <;>
    (try apply Tm.BSubst.lift_get_i_le_succ) <;>
    intro i hi <;>
    apply_assumption <;>
    simp [*]

theorem Tm.bvi_bs0_le (t : Tm) (s : Tm) : (t.bs0 s).bvi ≤ t.bvi ⊔ s.bvi
  := bvi_bsubst_le _ _ _ (fun i hi => by cases i <;> simp [bvi]; omega)

def liftBvSet (S : Set ℕ) : Set ℕ := Nat.pred '' { x ∈ S | x > 0 }

theorem mem_liftBvSet_iff {S : Set ℕ} {i : ℕ} :
  i ∈ liftBvSet S ↔ i + 1 ∈ S := by
  simp only [liftBvSet, Nat.pred_eq_sub_one, gt_iff_lt, Set.mem_image, Set.mem_setOf_eq]
  constructor
  · intro ⟨j, hj⟩; convert hj.1.1; omega
  · intro h; exists (i + 1); simp [*]

def Tm.bvs : Tm → Set ℕ
  | .bv i => {i}
  | .eqn A a b => A.bvs ∪ a.bvs ∪ b.bvs
  | .pi A B => A.bvs ∪ liftBvSet B.bvs
  | .abs A b => A.bvs ∪ liftBvSet b.bvs
  | .app A B f a => A.bvs ∪ liftBvSet B.bvs ∪ f.bvs ∪ a.bvs
  | .sigma A B => A.bvs ∪ liftBvSet B.bvs
  | .pair A B a b => A.bvs ∪ liftBvSet B.bvs ∪ a.bvs ∪ b.bvs
  | .fst A B a => A.bvs ∪ liftBvSet B.bvs ∪ a.bvs
  | .snd A B a => A.bvs ∪ liftBvSet B.bvs ∪ a.bvs
  | .dite φ A a b => φ.bvs ∪ A.bvs ∪ a.bvs ∪ b.bvs
  | .trunc A => A.bvs
  | .choose A φ => A.bvs ∪ liftBvSet φ.bvs
  | .natrec C n z s => liftBvSet C.bvs ∪ n.bvs ∪ z.bvs ∪ liftBvSet s.bvs
  | _ => ∅

theorem Tm.bvs_max (t : Tm) : ∀ i ∈ t.bvs, i < t.bvi := by
  induction t with
  | bv i => simp [bvs, bvi]
  | _ =>
    simp only [bvs, bvi]
    intro i
    (try simp only [
      Set.mem_empty_iff_false, false_imp_iff, Set.mem_union, mem_liftBvSet_iff, lt_max_iff,
      Nat.lt_sub_iff_add_lt
    ]) <;>
    intro h <;>
    (try casesm* _ ∨ _) <;>
    simp [*]

def Tm.bvsi : Tm → Set ℕ
  | .bv i => {i + 1, 0}
  | .eqn A a b => A.bvsi ∪ a.bvsi ∪ b.bvsi
  | .pi A B => A.bvsi ∪ Nat.pred '' B.bvsi
  | .abs A b => A.bvsi ∪ Nat.pred '' b.bvsi
  | .app A B f a => A.bvsi ∪ Nat.pred '' B.bvsi ∪ f.bvsi ∪ a.bvsi
  | .sigma A B => A.bvsi ∪ Nat.pred '' B.bvsi
  | .pair A B a b => A.bvsi ∪ Nat.pred '' B.bvsi ∪ a.bvsi ∪ b.bvsi
  | .fst A B a => A.bvsi ∪ Nat.pred '' B.bvsi ∪ a.bvsi
  | .snd A B a => A.bvsi ∪ Nat.pred '' B.bvsi ∪ a.bvsi
  | .dite φ A a b => φ.bvsi ∪ A.bvsi ∪ a.bvsi ∪ b.bvsi
  | .trunc A => A.bvsi
  | .choose A φ => A.bvsi ∪ Nat.pred '' φ.bvsi
  | .natrec C n z s => Nat.pred '' C.bvsi ∪ n.bvsi ∪ z.bvsi ∪ Nat.pred '' s.bvsi
  | _ => {0}

theorem pred_image_zero_union_succ_image (S : Set ℕ) :
  Nat.pred '' ({0} ∪ Nat.succ '' S) = {0} ∪ S := by
  ext s; simp; apply or_congr _ Iff.rfl
  constructor <;> intro h <;> rw [h]

theorem mem_succ_image_liftBvSet_iff (i : ℕ) {S : Set ℕ} :
  i ∈ Nat.succ '' liftBvSet S ↔ i ≠ 0 ∧ i ∈ S := by
  constructor
  · simp [mem_liftBvSet_iff]; intro x hx hi; cases hi; simp [*]
  · intro ⟨h, h'⟩; cases i <;> simp [mem_liftBvSet_iff, h'] at *

theorem Tm.bvsi_eq_bvs (t : Tm) : t.bvsi = {0} ∪ Nat.succ '' t.bvs := by
  induction t with
  | bv i => simp [bvs, bvsi]
  | _ =>
    simp only [bvs, bvsi, Set.image_empty, Set.union_empty, pred_image_zero_union_succ_image, *] <;>
    ext x <;>
    simp only [
      Set.mem_union, Set.mem_singleton_iff, Set.image_union, mem_succ_image_liftBvSet_iff
    ] <;>
    grind

theorem max_mem_of_left_right_mem {l r : ℕ} {S : Set ℕ} (hl : l ∈ S) (hr : r ∈ S) :
  max l r ∈ S := by rw [max_def]; split <;> assumption

theorem Tm.mem_pred_image_bvsi (n : ℕ) (t : Tm) (hn : n ∈ t.bvsi) : n - 1 ∈ Nat.pred '' t.bvsi
  := ⟨n, hn, rfl⟩

theorem Tm.mem_pred_image_bvsi_helper (n : ℕ) (t : Tm) (hn : n ∈ t.bvsi)
  : n - 1 ∈ Nat.pred '' t.bvsi ↔ n ∈ t.bvsi
  := ⟨fun _ => hn, fun hn => mem_pred_image_bvsi _ _ hn⟩

theorem Tm.bvi_mem_bvsi (t : Tm) : t.bvi ∈ t.bvsi := by induction t with
  | bv i => simp [bvi, bvsi]
  | _ =>
    simp only [bvi, bvsi, Set.mem_singleton_iff] <;>
    (repeat apply max_mem_of_left_right_mem) <;>
    (try simp only [Set.mem_union, or_true, true_or, mem_pred_image_bvsi_helper, *])

theorem Tm.bvi_mem_bvs (t : Tm) (h : t.bvi ≠ 0) : t.bvi - 1 ∈ t.bvs := by
  convert t.bvi_mem_bvsi using 0
  simp [Tm.bvsi_eq_bvs, h]
  constructor
  · intro h; exists t.bvi - 1; simp [*]; omega
  · intro ⟨i, hi, hi'⟩; rw [<-hi']; simp [hi]

theorem Tm.bvs_emp_lc (t : Tm) (h : t.bvs = ∅) : t.bvi = 0 := by
  by_contra h'; have h' := t.bvi_mem_bvs h'; rw [h] at h'; cases h'

theorem Tm.lc_bvs_emp (t : Tm) (h : t.bvi = 0) : t.bvs = ∅ := by
  ext i; simp only [Set.mem_empty_iff_false, iff_false]
  intro h'; convert t.bvs_max _ h'; rw [h]; simp

theorem Tm.bvs_emp_iff (t : Tm) : t.bvs = ∅ ↔ t.bvi = 0 := ⟨t.bvs_emp_lc, t.lc_bvs_emp⟩

theorem BWk.liftBvSet_biUnion (f : BWk) (S : Set ℕ) :
  liftBvSet {x | ∃ i ∈ S, (↑b f).get i = x} = {a | ∃ x ∈ liftBvSet S, f.get x = a} := by
  ext x
  simp only [mem_liftBvSet_iff, Set.mem_setOf]
  constructor
  · intro ⟨i, hi, hi'⟩; cases i with
    | zero => simp at hi'
    | succ i => exists i; apply And.intro hi; convert hi' using 0; simp
  · intro ⟨i, hi, hi'⟩; exists (i + 1); apply And.intro hi; simp [hi']

theorem Tm.bvs_bwk (f : BWk) (t : Tm) : (t.bwk f).bvs = { f.get i | i ∈ t.bvs }
  := by induction t generalizing f with
  | bv i => simp [bvs]
  | _ =>
    simp only [
      bvs, Set.mem_empty_iff_false, false_and, exists_false, bwk, Set.setOf_false, Set.mem_union,
      or_and_right, exists_or, Set.setOf_or, BWk.liftBvSet_biUnion, *
    ]

theorem Tm.bvs_bwk0 (t : Tm) : (↑0 t).bvs = Nat.succ '' t.bvs := bvs_bwk _ _

theorem Tm.BSubst.liftBvSet_biUnion_bvs (f : Tm.BSubst) (S : Set ℕ) :
  liftBvSet (⋃ i ∈ S, ((↑s f).get i).bvs) = ⋃ i ∈ liftBvSet S, (f.get i).bvs := by
  ext x
  simp only [mem_liftBvSet_iff, Set.mem_iUnion, exists_prop]
  constructor
  · intro ⟨i, hi, hi'⟩; cases i with
    | zero => simp [bvs] at hi'
    | succ i => exists i; apply And.intro hi; convert hi' using 0; simp [bvs_bwk0]
  · intro ⟨i, hi, hi'⟩; exists (i + 1); apply And.intro hi; simp [bvs_bwk0, hi']

theorem Tm.bvs_bsubst (f : BSubst) (t : Tm) : (t.bsubst f).bvs = ⋃ i ∈ t.bvs, (f.get i).bvs
  := by induction t generalizing f with
  | bv i => simp [bvs]
  | _ =>
    simp only [
      bvs, bsubst, Set.biUnion_union, Set.biUnion_empty, Tm.BSubst.liftBvSet_biUnion_bvs, *
    ]

theorem Tm.bvs_bs0 (t : Tm) (s : Tm) : (t.bs0 s).bvs = (liftBvSet t.bvs) ∪ ⋃ i ∈ t.bvs ∩ {0} , s.bvs
  := by
  rw [bs0, bvs_bsubst]
  ext x
  simp only [Set.mem_iUnion, exists_prop, Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_union,
    mem_liftBvSet_iff, exists_and_right, exists_eq_right]
  constructor
  · intro ⟨i, hi, hi'⟩; cases i with
    | zero => exact Or.inr ⟨hi, hi'⟩
    | succ i =>
      simp [bvs] at hi'
      cases hi'
      exact Or.inl hi
  · intro h; cases h with
    | inl hi => exists x + 1
    | inr hi => exists 0

theorem Tm.bvs_Iio (t : Tm) : t.bvs ⊆ Set.Iio t.bvi := t.bvs_max

theorem liftBvSet_mono {S T : Set ℕ} (h : S ⊆ T) : liftBvSet S ⊆ liftBvSet T := by
  simp only [liftBvSet]
  apply Set.image_subset
  intro x
  simp
  intro hx hx'
  simp [hx', h hx]

theorem Tm.lift_bvs_emp (t : Tm) (h : liftBvSet t.bvs = ∅) : t.bvi ≤ 1 := by
  by_contra h'
  simp at h'
  have ht := t.bvi_mem_bvs (by omega)
  have htt : t.bvi - 2 ∈ liftBvSet t.bvs := by
    generalize t.bvi = tv at *
    cases tv with
    | zero => omega
    | succ tv => cases tv with
    | zero => omega
    | succ tv => simp [mem_liftBvSet_iff] at *; exact ht
  rw [h] at htt
  cases htt

theorem Tm.bvs_Iio' {t : Tm} {i : ℕ} (h : t.bvi ≤ i) : t.bvs ⊆ Set.Iio i
  := t.bvs_Iio.trans (Set.Iio_subset_Iio h)

theorem Tm.lift_bvs_emp_one (t : Tm) (h : t.bvi ≤ 1) : liftBvSet t.bvs = ∅ := by
  apply Set.eq_empty_of_subset_empty
  apply Set.Subset.trans (liftBvSet_mono (t.bvs_Iio' h))
  intro x; simp [liftBvSet]

theorem Tm.lift_bvs_emp_iff (t : Tm) : liftBvSet t.bvs = ∅ ↔ t.bvi ≤ 1
  := ⟨t.lift_bvs_emp, t.lift_bvs_emp_one⟩

theorem Tm.bs0_lc (t : Tm) (s : Tm) (h : (t.bs0 s).bvi = 0) : t.bvi ≤ 1 := by
  rw [<-Tm.bvs_emp_iff, Tm.bvs_bs0] at h
  simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.union_empty_iff, Set.iUnion_eq_empty,
    and_imp, Tm.lift_bvs_emp_iff] at h
  exact h.1

theorem Tm.bvs_Iio_iff (t : Tm) (i : ℕ) : t.bvi ≤ i ↔ t.bvs ⊆ Set.Iio i := ⟨
  Tm.bvs_Iio',
  fun h => by
    generalize hv : t.bvi = tv at *
    cases tv with
    | zero => simp
    | succ tv =>
      have h := h (t.bvi_mem_bvs (by omega))
      simp at h
      omega
⟩

theorem Tm.bvs_bs0_lc (t : Tm) (s : Tm) (h : s.bvi = 0) : (t.bs0 s).bvs = (liftBvSet t.bvs)
  := by
  rw [<-bvs_emp_iff] at h
  simp only [bvs_bs0, h, Set.iUnion_empty, Set.union_empty]

theorem Tm.bvs_bs0_var (t : Tm) (x : ℕ) : (t.bs0 (.fv x)).bvs = (liftBvSet t.bvs)
  := bvs_bs0_lc _ _ rfl

theorem Tm.bvs_bs0_zero (t : Tm) : (t.bs0 .zero).bvs = (liftBvSet t.bvs)
  := bvs_bs0_lc _ _ rfl

theorem Tm.bs0_lc_cofinite_iff (t : Tm) (L : Finset ℕ)
  : (∀ x ∉ L, (t.bs0 (.fv x)).bvi = 0) ↔ t.bvi ≤ 1 := by
  simp [bvs_Iio_iff, <-bvs_emp_iff, bvs_bs0_var, lift_bvs_emp_iff]
  constructor
  · intro h; have ⟨x, hx⟩ := L.exists_notMem; exact h x hx
  · intros; assumption

theorem Tm.lc_cofinite_iff (t : Tm) (L : Finset ℕ)
  : (∀ x ∉ L, t.bvi = 0) ↔ t.bvi = 0 := by
  constructor
  · intro h; have ⟨x, hx⟩ := L.exists_notMem; exact h x hx
  · intros; assumption

theorem Tm.bs0_lc_of (t : Tm) (s : Tm) (ht : t.bvi ≤ 1) (hs : s.bvi = 0) : (t.bs0 s).bvi = 0
  := by simp only [<-bvs_emp_iff, bvs_bs0_lc _ _ hs, lift_bvs_emp_iff, ht] at *

-- theorem Tm.le_bvs_bsubst (f : BSubst) (t : Tm) (m : ℕ)
--   (h : ∃ i ∈ t.bvs, (f.get i).bvi ≥ m) : (t.bsubst f).bvi ≥ m
--   := by
--   have ⟨i, ⟨hi, hi'⟩⟩ := h;
--   clear h
--   induction t generalizing f m i with
--   | bv i => simp [bvs] at *; exact h
--   | _ =>
--     simp only [
--       bvs, Set.mem_empty_iff_false, Set.mem_union, mem_liftBvSet_iff, bsubst, bvi
--     ] at * <;>
--     sorry
