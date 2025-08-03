import Covalence.Set

def Tm.uF (ℓ : ℕ) : Tm := Tm.pi (ℓ + 1) (.univ ℓ) (.univ ℓ)

theorem Ctx.HasTy.uF {Γ : Ctx} {ℓ : ℕ} (hΓ : Γ.Ok) : Γ.HasTy (.univ (ℓ + 1)) (.uF ℓ)
  := .pi_k (.univ hΓ) (.univ hΓ) (by simp [Nat.imax])

def Tm.girF (ℓ : ℕ) : Tm := Tm.abs (ℓ + 1) (.univ ℓ) (.univ ℓ) -- λ X : Uℓ .
  (.pi ℓ
    (.pi ℓ (((Tm.bv 0).set ℓ).set ℓ) (Tm.bv 1)) -- (Set (Set X) → X) →
    (((Tm.bv 1).set ℓ).set ℓ)) -- Set (Set X)

theorem Ctx.HasTy.girF {Γ : Ctx} {ℓ : ℕ} (hΓ : Γ.Ok) : Γ.HasTy (.uF (ℓ + 1)) (.girF (ℓ + 1)) := by
  apply HasTy.abs_ty_cf (L := Γ.dv) (.univ hΓ) (.univ hΓ) (by simp [Nat.imax])
  intro x hx
  have hxℓ := HasTy.var (A := .univ (ℓ + 1)) (hΓ.cons hx hΓ.univ_ty) .here
  apply HasTy.pi_k (hxℓ.set'.set'.pi_k hxℓ (by simp [Nat.imax])) hxℓ.set'.set' (by simp [Nat.imax])

-- theorem Ctx.HasTy.girard {Γ : Ctx} {ℓ : ℕ} {badPi badAbs badApp : Tm}
--   (hpi : Γ.HasTy (.pi (ℓ + 2) (.uF (ℓ + 1)) (.univ (ℓ + 1))) badPi)
--   (habs : Γ.HasTy (.pi (ℓ + 2) (.uF (ℓ + 1))
--     (.pi (ℓ + 1)
--       (.pi (ℓ + 2) (.univ (ℓ + 1)) (.bv 0))
--       (.app (.uF (ℓ + 1)) (.univ (ℓ + 1)) badPi (.bv 1))))
--     badAbs)
--   (happ : Γ.HasTy (.pi (ℓ + 2) (.uF (ℓ + 1))
--     (.pi (ℓ + 2)
--       (.app (.uF (ℓ + 1)) (.univ (ℓ + 1)) badPi (.bv 0))
--       (.pi (ℓ + 2) (.univ (ℓ + 1)) (.app (.univ (ℓ + 1)) (.univ (ℓ + 1)) (.bv 1) (.bv 0)))))
--     badApp)
--   (hbeta : ∀ {A f x : Tm},
--     Γ.HasTy (.uF (ℓ + 1)) A
--     → Γ.HasTy (.pi (ℓ + 2) (.univ (ℓ + 1)) (.app (.univ (ℓ + 1)) (.univ (ℓ + 1)) A (.bv 0))) f
--     → Γ.HasTy (.univ (ℓ + 1)) x
--     → Γ.JEq (.univ (ℓ + 1))
--       (.app
--         (.univ (ℓ + 1))
--         (.app (.univ (ℓ + 1)) (.univ (ℓ + 1)) (.bv 1) (.bv 0))
--         (.app
--           (.app (.uF (ℓ + 1)) (.univ (ℓ + 1)) badPi (.bv 0))
--           (.pi (ℓ + 2) (.univ (ℓ + 1)) (.app (.univ (ℓ + 1)) (.univ (ℓ + 1)) (.bv 1) (.bv 0)))
--           badApp
--           (.app (.uF (ℓ + 1)) (.pi (ℓ + 1)
--             (.pi (ℓ + 2) (.univ (ℓ + 1)) (.bv 0))
--             (.app (.uF (ℓ + 1)) (.univ (ℓ + 1)) badPi (.bv 1))) badAbs f))
--         x)
--       (.app (.univ (ℓ + 1)) (.app (.univ (ℓ + 1)) (.univ (ℓ + 1)) A (.bv 0)) f x))
--   : Γ.Contra := by
--   let U := Tm.app (.uF (ℓ + 1)) (.univ (ℓ + 1)) badPi (.girF (ℓ + 1))
--   have ok := hpi.ok
--   have hU : Γ.HasTy (.univ (ℓ + 1)) U
--     := .app_k (.uF ok) (.univ ok) (by simp [Nat.imax]) hpi (.girF ok)
--   let G (T : Tm) : Tm :=
--     .abs (ℓ + 2) (.univ (ℓ + 1))
--          (.app (.univ (ℓ + 1)) (.univ (ℓ + 1)) (.girF (ℓ + 1)) (.bv 0))
--          (.abs (ℓ + 1) (.pi ℓ (((Tm.bv 0).set ℓ).set ℓ) (Tm.bv 1)) (((Tm.bv 1).set ℓ).set ℓ)
--           (.pi (ℓ + 1) (.univ (ℓ + 1)) (.mem (U.set (ℓ + 1)) T (
--             (.pi (ℓ + 1) U (.mem U (.bv 1) (.app
--               (((Tm.bv 4).set ℓ).set ℓ)
--               (Tm.bv 5)
--               (.bv 2)
--               (.app
--                 (.pi ℓ (((Tm.bv 4).set ℓ).set ℓ) (Tm.bv 5))
--                 (((Tm.bv 5).set ℓ).set ℓ)
--                 (.app (.univ (ℓ + 1))
--                   (.app (.univ (ℓ + 1)) (.univ (ℓ + 1)) (.girF (ℓ + 1)) (.bv 0))
--                   (.app
--                     U
--                     (.pi (ℓ + 2)
--                                 (.univ (ℓ + 1))
--                                 (.app (.univ (ℓ + 1)) (.univ (ℓ + 1)) (.girF (ℓ + 1)) (.bv 0)))
--                     (.app
--                       (.uF (ℓ + 1))
--                       (.pi (ℓ + 2)
--                         (.app (.uF (ℓ + 1)) (.univ (ℓ + 1)) badPi (.bv 0))
--                         (.pi (ℓ + 2)
--                                     (.univ (ℓ + 1))
--                                     (.app (.univ (ℓ + 1)) (.univ (ℓ + 1)) (.bv 1) (.bv 0))))
--                       badApp (.girF (ℓ + 1))) (.bv 0)) (.bv 4)) (.bv 3))
--             ))
--           )))))
--   sorry

-- theorem girard.{u} (pi : (Type u → Type u) → Type u)
--     (lam : ∀ {A : Type u → Type u}, (∀ x, A x) → pi A) (app : ∀ {A}, pi A → ∀ x, A x)
--     (beta : ∀ {A : Type u → Type u} (f : ∀ x, A x) (x), app (lam f) x = f x) : False :=
--   let F (X) := (Set (Set X) → X) → Set (Set X)
--   let U := pi F
--   let G (T : Set (Set U)) (X) : F X := fun f => {p | {x : U | f (app x X f) ∈ p} ∈ T}
--   let τ (T : Set (Set U)) : U := lam (G T)
--   let σ (S : U) : Set (Set U) := app S U τ
--   have στ : ∀ {s S}, s ∈ σ (τ S) ↔ {x | τ (σ x) ∈ s} ∈ S := fun {s S} =>
--     iff_of_eq (congr_arg (fun f : F U => s ∈ f τ) (beta (G S) U) :)
--   let ω : Set (Set U) := {p | ∀ x, p ∈ σ x → x ∈ p}
--   let δ (S : Set (Set U)) := ∀ p, p ∈ S → τ S ∈ p
--   have dw : δ ω := fun _p d => d (τ ω) <| στ.2 fun x h => d (τ (σ x)) (στ.2 h)
--   dw {y | ¬δ (σ y)} (fun _x e f => f _ e fun _p h => f _ (στ.1 h)) fun _p h => dw _ (στ.1 h)
