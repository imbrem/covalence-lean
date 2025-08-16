import Covalence.Rewrite

-- The predicates defined in this file correspond to the kernel's `Check` API

-- Primitive predicates

-- `eq_in(Γ, a, b) -> bool`: the E-graph relation
notation Γ " ⊢ " a " ≡ " b => Ctx.Rw Γ a b

-- `is_wf(Γ, a) -> bool`
notation Γ " ⊢ " a " wf" => Ctx.Wf Γ a

-- `is_ty(Γ, a) -> bool`
notation Γ " ⊢ " a " ty" => Ctx.IsTy Γ a

-- `is_inhab(Γ, a) -> bool`
notation Γ " ⊢ " a => Ctx.IsInhab Γ a

-- Predicates defined _under binders_

-- has_ty_under(Γ, A, b, B) -> bool
def Ctx.HasTyUnder (Γ : Ctx) (A : Tm) (b : Tm) (B : Tm) : Prop
  := ∃L : Finset ℕ, ∀x ∉ L, (Γ.cons x A) ⊢ (b.bs0 (.fv x)) : B.bs0 (.fv x)

-- This says that
-- _If_
-- - `has_ty(Γ, b, B)`
-- - `is_ty(Γ, A)`
-- _Then_
-- - `has_ty_under(Γ, A, b, B)`
theorem Ctx.HasTy.has_ty_under {Γ : Ctx} {A B b : Tm} (h : Γ ⊢ b : B) (hA : Γ ⊢ A ty)
  : Γ.HasTyUnder A b B := ⟨Γ.dv, fun x hx => by
    convert h.wk0 hx hA <;> rw [Tm.bs0, Tm.bsubst_lc]
    · exact h.lc_ty
    · exact h.lc_tm
  ⟩

-- We can _store_ `has_ty_under` in the E-graph by instead storing that the appropriate
-- lambda-abstraction is well-formed:

-- theorem Ctx.HasTyUnder.to_wf {Γ : Ctx} {A B b : Tm} (h : Γ.HasTyUnder A b B)
--   : Γ ⊢ (.abs )
