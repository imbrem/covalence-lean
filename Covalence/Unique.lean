import Covalence.Factor

theorem Ctx.TyEq'.imax_congr_lhs {Γ : Ctx} {m m' n : ℕ}
  (hm : Γ.TyEq' (.univ m) (.univ m'))
  : Γ.TyEq' (.univ (m.imax n)) (.univ (m'.imax n)) := by
  sorry

theorem Ctx.TyEq'.max_congr_lhs {Γ : Ctx} {m m' n : ℕ}
  (hm : Γ.TyEq' (.univ m) (.univ m'))
  : Γ.TyEq' (.univ (m ⊔ n)) (.univ (m' ⊔ n)) := by
  sorry

theorem Ctx.HasTy.unique_inner_multi {Γ : Ctx} {X Y a : Tm} (hX : Γ.HasTy X a) (hY : Γ.InnerTy Y a)
  : TyEq' Γ X Y := by induction hX generalizing Y with
  | var hΓ hA => cases hY with | var hΓ' hB =>
    cases hΓ.at_eq hA hB; exact .single (JEq.regular (.var hΓ.zero hA))
  | pi_cf hA hB hℓ IA IB => cases hY with | pi_cf hA' hB' hℓ' =>
    have ⟨WA, hA', hWA⟩ := hA'.outer_ty;
    cases hℓ; cases hℓ'
    exact Ctx.TyEq'.imax_congr_lhs ((IA hA').trans hWA)
  | fst_cf | dite_cf | choose_cf =>
    cases hY; constructor; apply JEq.ty_eq <;> (apply HasTy.refl; assumption)
  | app_cf hA hB hf ha hBa IA IB If Ia => cases hY with | app_cf hA' hB' hf' ha' hBa' =>
    exact .trans (.single hBa.symm.ty_eq) (.single hBa'.ty_eq)
  | abs_cf hA hB hb IA IB Ib => cases hY with | abs_cf hA' hB' hb' =>
    exact .single ⟨_, JEq.pi_cf hA.refl (fun x hx => (hB x hx).refl) rfl⟩
  | pair_cf hA hB hℓ ha hb IA IB => cases hY with | pair_cf hA' hB' hℓ' ha' hb' =>
    exact .single ⟨_, JEq.sigma_cf hA.refl (fun x hx => (hB x hx).refl) hℓ⟩
  | snd_cf hA hB hℓ he hBa IA IB Ie => cases hY with | snd_cf hA' hB' hℓ' he' hBa' =>
    exact .trans (.single hBa.symm.ty_eq) (.single hBa'.ty_eq)
  | succ hΓ => cases hY; exact .single ⟨_, .pi_k hΓ.nats hΓ.nats rfl⟩
  | natrec_cf hC hn hz hs hCn IC In Iz Is => cases hY with | natrec_cf hC' hn' hz' hs' hCn' =>
    exact .trans (.single hCn.symm.ty_eq) (.single hCn'.ty_eq)
  | cast hAB ha IA => exact .head hAB.symm (IA hY)
  | _ =>
    cases hY; apply TyEq'.of_ty; constructor; constructor; apply Ctx.Ok.zero
            ; first | assumption | apply HasTy.ok; assumption

theorem Ctx.HasTy.unique_multi {Γ : Ctx} {X Y a : Tm} (hX : Γ.HasTy X a) (hY : Γ.HasTy Y a)
  : TyEq' Γ X Y := have ⟨_, hCa, hC⟩ := hY.outer_ty; (hX.unique_inner_multi hCa).trans hC

theorem Ctx.TyEq.trans {Γ : Ctx} {A B C : Tm} (hAB : Γ.TyEq A B) (hBC : Γ.TyEq B C) : Γ.TyEq A C :=
  have ⟨_, hAB⟩ := hAB; have ⟨n, hBC⟩ := hBC;
  have hmn := hAB.ty_rhs.unique_multi hBC.ty_lhs;
  ⟨n, (hAB.multicast hmn).trans hBC⟩

theorem Ctx.TyEq'.merge {Γ : Ctx} {A B : Tm} (hAB : Γ.TyEq' A B) : Γ.TyEq A B
  := by induction hAB with | single => assumption | tail => apply TyEq.trans <;> assumption

theorem Ctx.HasTy.unique {Γ : Ctx} {A B a : Tm} (hX : Γ.HasTy A a) (hY : Γ.HasTy B a)
  : TyEq Γ A B := (hX.unique_multi hY).merge

def Ctx.WfEq (Γ : Ctx) (a b : Tm) := ∃A, Γ.JEq A a b

theorem Ctx.WfEq.symm {Γ : Ctx} {a b : Tm} (h : Γ.WfEq a b) : Γ.WfEq b a
  := let ⟨A, hA⟩ := h; ⟨A, hA.symm⟩

theorem Ctx.WfEq.trans {Γ : Ctx} {a b c : Tm} (hAB : Γ.WfEq a b) (hBC : Γ.WfEq b c) : Γ.WfEq a c :=
  let ⟨_, hab⟩ := hAB; let ⟨B, hbc⟩ := hBC;
  have hAB := hab.ty_rhs.unique hbc.ty_lhs;
  ⟨B, (hAB.cast hab).trans hbc⟩

theorem Ctx.TyEq.wf_eq {Γ : Ctx} {A B : Tm} (hAB : Γ.TyEq A B) : Γ.WfEq A B
  := have ⟨_, hAB⟩ := hAB; ⟨_, hAB⟩

theorem Ctx.WfEq.ty_left {Γ : Ctx} {A B : Tm} (h : Γ.WfEq A B) (hA : Γ.IsTy A) : Γ.TyEq A B :=
  let ⟨_, hAB⟩ := h;
  let ⟨_, hA⟩ := hA;
  have hu := hAB.ty_lhs.unique hA.ty_rhs;
  ⟨_, .symm ((hu.cast hAB.symm).trans hA)⟩

theorem Ctx.WfEq.ty_right {Γ : Ctx} {A B : Tm} (h : Γ.WfEq A B) (hB : Γ.IsTy B) : Γ.TyEq A B :=
  (h.symm.ty_left hB).symm

theorem Ctx.WfEq.lc_lhs {Γ : Ctx} {a b : Tm} (h : Γ.WfEq a b) : a.bvi = 0 :=
  have ⟨_, h⟩ := h; h.lc_lhs

theorem Ctx.WfEq.lc_rhs {Γ : Ctx} {a b : Tm} (h : Γ.WfEq a b) : b.bvi = 0 := h.symm.lc_lhs

def Ctx.Wf (Γ : Ctx) (a : Tm) := Γ.WfEq a a

theorem Ctx.WfEq.lhs {Γ : Ctx} {a b : Tm} (h : Γ.WfEq a b) : Γ.Wf a := h.trans h.symm

theorem Ctx.WfEq.rhs {Γ : Ctx} {a b : Tm} (h : Γ.WfEq a b) : Γ.Wf b := h.symm.lhs

theorem Ctx.Wf.has_ty {Γ : Ctx} {a : Tm} (h : Γ.Wf a) : ∃A, Γ.HasTy A a
  := let ⟨A, hA⟩ := h; ⟨A, hA.ty_lhs⟩

theorem Ctx.Wf.lc {Γ : Ctx} {a : Tm} (h : Γ.Wf a) : a.bvi = 0 := h.lc_lhs

theorem Ctx.Wf.of_ty {Γ : Ctx} {A a : Tm} (h : Γ.HasTy A a) : Γ.Wf a := ⟨A, h.refl⟩

theorem Ctx.WfEq.jeq {Γ : Ctx} {A a b : Tm} (h : Γ.WfEq a b) (ha : Γ.HasTy A a) : Γ.JEq A a b :=
  let ⟨_, h⟩ := h; have hAB := h.ty_lhs.unique ha; hAB.cast h

theorem Ctx.WfEq.wk0 {Γ : Ctx} {A a b : Tm} (h : Γ.WfEq a b) {x} (hx : x ∉ Γ.dv) (hA : Γ.IsTy A)
  : (Γ.cons x A).WfEq a b := have ⟨_, h⟩ := h; ⟨_, h.wk0 hx hA⟩
