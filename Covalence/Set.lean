import Covalence.Logic

def Tm.set (ℓ : ℕ) (A : Tm) := Tm.pi (ℓ.imax 1) A (.univ 0)

theorem Ctx.JEq.set {Γ : Ctx} {ℓ : ℕ} {A B : Tm} (h : Γ.JEq (.univ ℓ) A B)
  : Γ.JEq (.univ (ℓ.imax 1)) (.set ℓ A) (.set ℓ B)
  := .pi_k h h.ok.univ rfl

theorem Ctx.HasTy.set {Γ : Ctx} {ℓ : ℕ} {A : Tm} (h : Γ.HasTy (.univ ℓ) A)
  : Γ.HasTy (.univ (ℓ.imax 1)) (.set ℓ A)
  := .pi_k h (.univ h.ok) rfl

theorem Ctx.HasTy.set' {Γ : Ctx} {ℓ : ℕ} {A : Tm} (h : Γ.HasTy (.univ (ℓ + 1)) A)
  : Γ.HasTy (.univ (ℓ + 1)) (.set (ℓ + 1) A)
  := by convert h.set using 2; simp [Nat.imax]

def Tm.mem (A : Tm) (S : Tm) (a : Tm) := Tm.app A (.univ 0) S a

theorem Ctx.JEq.mem {Γ : Ctx} {ℓ : ℕ} {A A' S S' a a' : Tm}
  (h : Γ.JEq (.univ ℓ) A A') (hS : Γ.JEq (.set ℓ A) S S') (ha : Γ.JEq A a a')
  : Γ.JEq (.univ 0) (.mem A S a) (.mem A' S' a')
  := .app_k h h.ok.univ rfl hS ha

theorem Ctx.HasTy.mem {Γ : Ctx} {ℓ : ℕ} {A S a : Tm}
  (hA : Γ.HasTy (.univ ℓ) A) (hS : Γ.HasTy (.set ℓ A) S) (ha : Γ.HasTy A a)
  : Γ.HasTy (.univ 0) (.mem A S a)
  := .app_k hA (.univ hA.ok) rfl hS ha

theorem Ctx.HasTy.mem_prop {Γ : Ctx} {ℓ : ℕ} {A S a : Tm}
  (hA : Γ.HasTy (.univ ℓ) A) (hS : Γ.HasTy (.set ℓ A) S) (ha : Γ.HasTy A a)
  : Γ.IsProp (.mem A S a) := hA.mem hS ha
