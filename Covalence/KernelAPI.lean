import Covalence.Rewrite

def Ctx.HasTyUnder (Γ : Ctx) (A B b : Tm) : Prop
  := ∃L : Finset ℕ, ∀x ∉ L, (Γ.cons x A).HasTy (B.bs0 (.fv x)) (b.bs0 (.fv x))

theorem Ctx.HasTyUnder.arg_regular {Γ : Ctx} {A B b : Tm}
  (h : Γ.HasTyUnder A B b) : Γ.IsTy A :=
  have ⟨L, h⟩ := h;
  have ⟨x, hx⟩ := L.exists_notMem;
  (h x hx).ok.ty

theorem Ctx.HasTyUnder.has_ty {Γ : Ctx} {A B b : Tm}
  (h : Γ.HasTyUnder A B b) : Γ.HasTy (.univ 0) (.pi 0 A (.has_ty b B)) :=
  have ⟨_, hA⟩ := h.arg_regular;
  have hA := hA.ty_lhs;
  have ⟨_, h⟩ := h;
  hA.pi_cf (ℓ := 0) (fun x hx => (h x hx).has_ty) rfl

-- theorem Ctx.HasTyUnder.of_has_ty {Γ : Ctx} {A B b : Tm}
--   (h : Γ.HasTy (.univ 0) (.pi 0 A (.has_ty b B))) : Γ.HasTyUnder A B b := by
--   have ⟨W, hAB, hW⟩ := h.outer_ty;
--   cases hAB with
--   | pi_cf hA hB hℓ =>
--   simp [Nat.imax] at hℓ
--   rename Finset ℕ => L
--   exists L
--   intro x hx
--   apply HasTy.of_has_ty
--   sorry
