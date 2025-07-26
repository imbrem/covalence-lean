import Covalence.Wk

theorem Ctx.Ok.var_regular {Γ : Ctx} {x : ℕ} {A : Tm} (h : Γ.Ok) (ha : Γ.At x A) :
  Γ.IsTy A := by
  induction ha with
  | here => cases h; apply Ctx.IsTy.wk0 <;> assumption
  | there _ I => cases h; apply Ctx.IsTy.wk0 <;> apply_assumption; assumption

theorem Ctx.JEq.regular {Γ : Ctx} {A a b : Tm} (h : Ctx.JEq Γ A a b) : Γ.IsTy A := by
  induction h with
  | var hΓ hA => exact hΓ.ok.var_regular hA
  | nil_ok => exact Ok.nil.nats_ty
  | cons_ok _ hA hx => exact (hA.lhs_ty.cons hx).nats_ty
  | succ hΓ I => exact ⟨1, .pi_cf hΓ.ok.nats (fun x hx => (I.cons hx).nats) rfl⟩
  | symm => assumption
  | trans => assumption
  | _ =>
    first | apply JEq.lhs_ty; assumption
          | apply JEq.rhs_ty; assumption
          | (constructor; constructor
            <;> first | rfl | assumption
                      | apply JEq.lhs; assumption
                      | intros; apply JEq.lhs; apply_assumption; assumption
                      | apply Ok.zero; apply JEq.ok ; assumption)
