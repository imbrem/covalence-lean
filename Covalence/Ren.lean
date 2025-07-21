import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Order.Lattice

/--
A weakening on bound variables
-/
def BWk := ℕ → ℕ

def bwkOf (f : ℕ → ℕ) : BWk := f

def BWk.get (f : BWk) (n : ℕ) : ℕ := f n

@[ext] theorem BWk.get_ext (f g : BWk) (h : ∀ n, f.get n = g.get n) : f = g := funext h

instance : Monoid BWk where
  one := id
  mul f g := f ∘ g
  mul_assoc f g h := rfl
  one_mul f := rfl
  mul_one f := rfl

@[simp] theorem BWk.get_one (n : ℕ) : BWk.get 1 n = n := rfl

@[simp] theorem BWk.get_mul (f g : BWk) (n : ℕ) : (f * g).get n = f.get (g.get n) := rfl

/--
Weaken the zeroth bound variable
-/
def BWk.wk0 : BWk := Nat.succ

@[simp] theorem BWk.get_wk0 (n : ℕ) : BWk.get .wk0 n = n + 1 := rfl

/--
Lift a weakening under a binder
-/
def BWk.lift (f : BWk) : BWk | 0 => 0 | n + 1 => (f n) + 1

@[inherit_doc] prefix:75 "↑b " => BWk.lift

@[simp] theorem BWk.get_zero_lift (f : BWk) : (↑b f).get 0 = 0 := rfl

@[simp] theorem BWk.get_succ_lift (f : BWk) (n : ℕ) : (↑b f).get (n + 1) = f.get n + 1 := rfl

@[simp] theorem BWk.lift_one : ↑b 1 = 1 := by ext n; cases n <;> rfl

@[simp] theorem BWk.lift_mul (f g : BWk) : ↑b (f * g) = ↑b f * ↑b g := by ext n; cases n <;> rfl

theorem BWk.lift_mul_wk0 (f : BWk) : ↑b f * .wk0 = .wk0 * f := by rfl

theorem BWk.lift_inj (f g : BWk) (h : ↑b f = ↑b g) : f = g := by
  ext x; rw [<-Nat.add_one_inj, <-get_succ_lift, <-get_succ_lift, h]

def BWk.EqOn (n : ℕ) (f g : BWk) : Prop := ∀ i < n, f.get i = g.get i

@[simp] theorem BWk.EqOn_refl (n : ℕ) (f : BWk) : BWk.EqOn n f f := fun _ _ => rfl

theorem BWk.EqOn.of_eq (n : ℕ) {f g : BWk} (h : f = g) : BWk.EqOn n f g := fun _ _ => by rw [h]

@[simp] theorem BWk.EqOn_zero (f g : BWk) : BWk.EqOn 0 f g := fun _ h => by cases h

theorem BWk.EqOn.symm {n : ℕ} {f g : BWk} (h : BWk.EqOn n f g) : BWk.EqOn n g f
  := fun i hi => (h i hi).symm

theorem BWk.EqOn.trans {n : ℕ} {f g h : BWk}
  (hfg : BWk.EqOn n f g) (hgh : BWk.EqOn n g h) : BWk.EqOn n f h := fun i hi =>
  by rw [hfg i hi, hgh i hi]

theorem BWk.EqOn.mono {n m : ℕ} (hm : m ≤ n) {f g : BWk} (h : f.EqOn n g) : f.EqOn m g
  := fun i hi => h i (by omega)

theorem BWk.EqOn.sup_iff (n m : ℕ) (f g : BWk)
  : f.EqOn (n ⊔ m) g ↔ f.EqOn n g ∧ f.EqOn m g
  := ⟨fun h => ⟨h.mono (by simp), h.mono (by simp)⟩, fun ⟨hn, hm⟩ i hi => by
    rw [lt_sup_iff] at hi; cases hi with | inl hi => exact hn i hi | inr hi => exact hm i hi⟩

theorem BWk.EqOn.lift {n : ℕ} (f g : BWk) (h : BWk.EqOn n f g) :
  BWk.EqOn (n + 1) (↑b f) (↑b g) := fun i hi => by cases i with
  | zero => rfl
  | succ i => rw [get_succ_lift, get_succ_lift, h i]; omega

theorem BWk.EqOn.of_succ_lift {n : ℕ} (f g : BWk) (h : BWk.EqOn (n + 1) f.lift g.lift)
  : f.EqOn n g := fun i hi => by convert h (i + 1) (by omega) using 0; simp

theorem BWk.EqOn.succ_lift_iff {n : ℕ} (f g : BWk)
  : f.lift.EqOn (n + 1) g.lift ↔ f.EqOn n g := ⟨fun h => h.of_succ_lift, fun h => h.lift⟩

theorem BWk.EqOn.pred_iff_lift (n : ℕ) (f g : BWk)
  : f.EqOn (n - 1) g ↔ f.lift.EqOn n g.lift := by cases n <;> simp [succ_lift_iff]
