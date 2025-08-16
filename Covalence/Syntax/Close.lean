import Covalence.Syntax.FSubst
import Covalence.Syntax.MSubst

def Tm.closeUnder (i : ℕ) (x : ℕ) : Tm → Tm
  | .bv j => if j < i then .bv j else .bv (j + 1)
  | .fv y => if y = x then .bv i else .fv y
  | .univ ℓ => .univ ℓ
  | .unit ℓ => .unit ℓ
  | .nil ℓ => .nil ℓ
  | .empty ℓ => .empty ℓ
  | .eqn A a b => .eqn (A.closeUnder i x) (a.closeUnder i x) (b.closeUnder i x)
  | .pi A B => .pi (A.closeUnder i x) (B.closeUnder (i + 1) x)
  | .abs A B b => .abs (A.closeUnder i x) (B.closeUnder (i + 1) x) (b.closeUnder (i + 1) x)
  | .app A B f a =>
    .app (A.closeUnder i x) (B.closeUnder (i + 1) x) (f.closeUnder i x) (a.closeUnder i x)
  | .sigma A B => .sigma (A.closeUnder i x) (B.closeUnder (i + 1) x)
  | .pair A B a b =>
    .pair (A.closeUnder i x) (B.closeUnder (i + 1) x) (a.closeUnder i x) (b.closeUnder i x)
  | .fst A B a => .fst (A.closeUnder i x) (B.closeUnder (i + 1) x) (a.closeUnder i x)
  | .snd A B a => .snd (A.closeUnder i x) (B.closeUnder (i + 1) x) (a.closeUnder i x)
  | .dite φ A a b
    => .dite (φ.closeUnder i x) (A.closeUnder i x) (a.closeUnder i x) (b.closeUnder i x)
  | .trunc A => .trunc (A.closeUnder i x)
  | .choose A φ => .choose (A.closeUnder i x) (φ.closeUnder (i + 1) x)
  | .nats => .nats
  | .zero => .zero
  | .succ => .succ
  | .natrec C n z s =>
    .natrec (C.closeUnder (i + 1) x) (n.closeUnder i x) (z.closeUnder i x) (s.closeUnder (i + 1) x)
  | .let₁ A a b => .let₁ (A.closeUnder i x) (a.closeUnder i x) (b.closeUnder (i + 1) x)
  | .invalid => .invalid

theorem Tm.closeUnder_notMem (t : Tm) {i : ℕ} (h : t.bvi ≤ i) (x : ℕ) (hx : x ∉ fvs t)
  : t.closeUnder i x = t := by
  induction t generalizing i with
  | bv => simp [closeUnder]; simp [bvi] at h; omega
  | fv => simp [closeUnder]; simp [fvs] at hx; exact Ne.symm hx
  | _ =>
    simp only [closeUnder]
    <;> simp [bvi] at h
    <;> simp [fvs] at hx
    <;> congr <;> apply_assumption
    <;> simp [*]

theorem Tm.liftn_b0_closeUnder (t : Tm) (x : ℕ) (a : Tm) (n : ℕ)
  : (t.closeUnder n x).bsubst (BSubst.lift^[n] a.b0) = t.fsubst (FSubst.lift^[n] (a.f0 x))
  := by induction t generalizing n x a with
  | bv j =>
    simp only [closeUnder, fsubst]
    split <;> simp [BSubst.get_liftn, *]
    split
    · omega
    · rw [Tm.get_b0]
      split
      · omega
      · simp only [bwk_bwk0_iter_bv, bv.injEq]; omega
  | fv y =>
    simp only [closeUnder, fsubst, FSubst.get_liftn]
    split
    case isTrue h => simp [BSubst.get_liftn, h]
    case isFalse h => simp [f0, FSubst.get_set, h]
  | _ =>
    simp only [closeUnder, bsubst, fsubst, <-Function.iterate_succ_apply']
    <;> congr <;> apply_assumption

abbrev Tm.close (t : Tm) (x : ℕ) := t.closeUnder 0 x

theorem Tm.close_notMem (t : Tm) (h : t.bvi = 0) (x : ℕ) (hx : x ∉ fvs t) : t.close x = t
  := t.closeUnder_notMem (by simp [h]) x hx

theorem Tm.bs0_close (t : Tm) (x : ℕ) (a : Tm) : (t.close x).bs0 a = t.fs0 x a
  := t.liftn_b0_closeUnder x a 0

def Tm.FSubst.Lc (σ : FSubst) (X : Finset ℕ) : Prop := ∀i ∈ X, (σ.get i).bvi = 0

@[simp] theorem Tm.FSubst.Lc.empty (σ : FSubst) : σ.Lc ∅ := fun i hi => by cases hi

theorem Tm.FSubst.Lc.union_iff {σ : FSubst} {X Y : Finset ℕ} :
  σ.Lc (X ∪ Y) ↔ σ.Lc X ∧ σ.Lc Y := by
  simp only [Lc, Finset.mem_union, ← forall_and]
  apply forall_congr'
  grind

theorem Tm.FSubst.Lc.anti {σ : FSubst} {X Y : Finset ℕ} (hXY : X ⊆ Y) (hσ : σ.Lc Y) :
  σ.Lc X := fun i hi => hσ i (hXY hi)

@[simp]
theorem Tm.FSubst.Lc.singleton_iff {σ : FSubst} {x : ℕ} :
  σ.Lc {x} ↔ (σ.get x).bvi = 0 := by
  simp only [Lc, Finset.mem_singleton, forall_eq]

theorem Tm.FSubst.Lc.lift {σ : FSubst} {X : Finset ℕ} (hσ : σ.Lc X) : σ.lift.Lc X
  := fun x hx => by convert hσ x hx using 1; rw [FSubst.get_lift, Tm.bwk_lc]; exact hσ x hx

theorem Tm.FSubst.Lc.of_lift {σ : FSubst} {X : Finset ℕ} (hσ : σ.lift.Lc X) : σ.Lc X
  := fun x hx => by
    convert hσ x hx using 1; rw [FSubst.get_lift, Tm.bwk_lc]
    apply Tm.lc_of_bwk_lc
    exact hσ x hx

def Tm.FSubst.toM (σ : Tm.FSubst) : Tm.MSubst := σ

@[simp] theorem Tm.FSubst.get_toM (σ : Tm.FSubst) (x : ℕ) : (σ.toM).get x = σ.get x := rfl

def Tm.MSubst.toF (σ : Tm.MSubst) : Tm.FSubst := σ

@[simp] theorem Tm.MSubst.get_toF (σ : Tm.MSubst) (x : ℕ) : (σ.toF).get x = σ.get x := rfl

theorem Tm.fsubst_liftn_eq_msubst (σ : FSubst) (t : Tm) (hσ : σ.Lc t.fvs) (n : ℕ)
  : t.fsubst (FSubst.lift^[n] σ) = t.msubst σ.toM
  := by induction t generalizing n with
  | fv x =>
    simp [fsubst, FSubst.get_liftn]
    induction n with
    | zero => rfl
    | succ n I => rw [Function.iterate_succ_apply', I, bwk_lc]; exact hσ x (by simp)
  | _ =>
    simp only [fsubst, msubst, <-Function.iterate_succ_apply']
    <;> simp [fvs, Tm.FSubst.Lc.union_iff] at hσ
    <;> congr 1
    <;> apply_assumption
    <;> simp [*]

theorem Tm.fsubst_eq_msubst (σ : FSubst) (t : Tm) (hσ : σ.Lc t.fvs)
  : t.fsubst σ = t.msubst σ.toM := t.fsubst_liftn_eq_msubst σ hσ 0

theorem Tm.rename_close (t : Tm) (x y : ℕ) : (t.close x).bs0 (.fv y) = t.ms0 x (.fv y)
  := by
  convert t.bs0_close x (.fv y) using 1; rw [fs0, fsubst_eq_msubst]
  · rfl
  · intro x hx; simp only [get_f0]; split <;> rfl

theorem Tm.fvs_closeUnder (t : Tm) (n : ℕ) (x : ℕ) : (t.closeUnder n x).fvs = t.fvs.erase x
  := by induction t generalizing n with
  | bv j => simp only [closeUnder]; split <;> simp
  | fv y => simp only [closeUnder]; split <;> simp [*]; rename_i h; simp [Ne.symm h]
  | _ => simp only [closeUnder, fvs, Finset.erase_empty, Finset.erase_union_distrib, *]

theorem Tm.fvs_close (t : Tm) (x : ℕ) : (t.close x).fvs = t.fvs.erase x
  := t.fvs_closeUnder 0 x

theorem Tm.fvs_close_subset (t : Tm) (x : ℕ) : (t.close x).fvs ⊆ t.fvs
  := by rw [Tm.fvs_close]; exact Finset.erase_subset _ _
