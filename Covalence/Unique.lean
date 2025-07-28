import Covalence.HasTy

def Ctx.TyEq' (Γ : Ctx) := Relation.TransGen Γ.TyEq

theorem Ctx.TyEq'.symm {Γ : Ctx} {A B : Tm} (hAB : Γ.TyEq' A B) : Γ.TyEq' B A
  := by induction hAB with | single h => exact .single h.symm | tail _ h I => exact .head h.symm I

theorem Ctx.TyEq'.trans {Γ : Ctx} {A B C : Tm} (hAB : Γ.TyEq' A B) (hBC : Γ.TyEq' B C) : Γ.TyEq' A C
  := Relation.TransGen.trans hAB hBC

theorem Ctx.HasTy.multicast {Γ : Ctx} {A B : Tm} (hAB : Γ.TyEq' A B) {a : Tm} (h : Γ.HasTy A a)
  : Γ.HasTy B a := by induction hAB <;> apply HasTy.cast <;> assumption

theorem Ctx.TyEq'.of_ty {Γ : Ctx} {A B : Tm} (hAB : Γ.TyEq A B) : Γ.TyEq' A B
  := .single hAB

inductive Ctx.InnerTy : Ctx → Tm → Tm → Prop
  | univ {Γ : Ctx} {ℓ : ℕ} : Γ.Ok → InnerTy Γ (.univ (ℓ + 1)) (.univ ℓ)
  | var {Γ : Ctx} {x : ℕ} {A : Tm} : Γ.Ok → Γ.At x A → InnerTy Γ A (.fv x)
  | unit {Γ : Ctx} {ℓ : ℕ} : Γ.Ok → InnerTy Γ (.univ ℓ) (.unit ℓ)
  | nil {Γ : Ctx} {ℓ : ℕ} : Γ.Ok → InnerTy Γ (.unit ℓ) (.nil ℓ)
  | empty {Γ : Ctx} {ℓ : ℕ} : Γ.Ok → InnerTy Γ (.univ ℓ) (.empty ℓ)
  | eqn {Γ : Ctx} {ℓ : ℕ} {A a b : Tm}
    : HasTy Γ (.univ ℓ) A
    → HasTy Γ A a
    → HasTy Γ A b
    → InnerTy Γ (.univ 0) (.eqn A a b)
  | pi_cf {Γ : Ctx} {ℓ m n : ℕ} {A B : Tm} {L : Finset ℕ}
    : HasTy Γ (.univ m) A
    → (∀ x ∉ L, HasTy (Γ.cons x A) (.univ n) (B.bs0 (.fv x)))
    → (ℓ = m.imax n)
    → InnerTy Γ (.univ ℓ) (.pi ℓ A B)
  | app_cf {Γ : Ctx} {ℓ m n : ℕ} {A B Ba f a : Tm} {L : Finset ℕ}
    : HasTy Γ (.univ m) A
    → (∀ x ∉ L, HasTy (Γ.cons x A) (.univ n) (B.bs0 (.fv x)))
    → (ℓ = m.imax n)
    → HasTy Γ (.pi ℓ A B) f
    → HasTy Γ A a
    → JEq Γ (.univ n) (B.bs0 a) Ba
    → InnerTy Γ Ba (.app ℓ A B f a)
  | abs_cf {Γ : Ctx} {ℓ m n : ℕ} {A B b : Tm} {L : Finset ℕ}
    : HasTy Γ (.univ m) A
    → (∀ x ∉ L, HasTy (Γ.cons x A) (.univ n) (B.bs0 (.fv x)))
    → (ℓ = m.imax n)
    → (∀ x ∉ L, HasTy (Γ.cons x A) (B.bs0 (.fv x)) (b.bs0 (.fv x)))
    → InnerTy Γ (.pi ℓ A B) (.abs ℓ A b)
  | sigma_cf {Γ : Ctx} {ℓ m n : ℕ} {A B : Tm} {L : Finset ℕ}
    : HasTy Γ (.univ m) A
    → (∀ x ∉ L, HasTy (Γ.cons x A) (.univ n) (B.bs0 (.fv x)))
    → (ℓ = m ⊔ n)
    → InnerTy Γ (.univ ℓ) (.sigma ℓ A B)
  | pair_cf {Γ : Ctx} {ℓ m n : ℕ} {A B a b : Tm} {L : Finset ℕ}
    : HasTy Γ (.univ m) A
    → (∀ x ∉ L, HasTy (Γ.cons x A) (.univ n) (B.bs0 (.fv x)))
    → (ℓ = m ⊔ n)
    → HasTy Γ A a
    → HasTy Γ (B.bs0 a) b
    → InnerTy Γ (.sigma ℓ A B) (.pair ℓ A B a b)
  | fst_cf {Γ : Ctx} {ℓ m n : ℕ} {A B e : Tm} {L : Finset ℕ}
    : HasTy Γ (.univ m) A
    → (∀ x ∉ L, HasTy (Γ.cons x A) (.univ n) (B.bs0 (.fv x)))
    → (ℓ = m ⊔ n)
    → HasTy Γ (.sigma ℓ A B) e
    → InnerTy Γ A (.fst ℓ A B e)
  | snd_cf {Γ : Ctx} {ℓ m n : ℕ} {A B Ba e : Tm} {L : Finset ℕ}
    : HasTy Γ (.univ m) A
    → (∀ x ∉ L, HasTy (Γ.cons x A) (.univ n) (B.bs0 (.fv x)))
    → (ℓ = m ⊔ n)
    → HasTy Γ (.sigma ℓ A B) e
    → JEq Γ (.univ n) (B.bs0 (.fst ℓ A B e)) Ba
    → InnerTy Γ Ba (.snd ℓ A B e)
  | dite_cf {Γ : Ctx} {ℓ : ℕ} {φ A a b : Tm} {L : Finset ℕ}
    : HasTy Γ (.univ 0) φ
    → HasTy Γ (.univ ℓ) A
    → (∀ x ∉ L, HasTy (Γ.cons x φ) A a)
    → (∀ x ∉ L, HasTy (Γ.cons x (.not φ)) A b)
    → InnerTy Γ A (.dite φ A a b)
  | trunc {Γ : Ctx} {ℓ : ℕ} {A : Tm}
    : HasTy Γ (.univ ℓ) A
    → InnerTy Γ (.univ 0) (.trunc A)
  | choose_cf {Γ : Ctx} {ℓ} {A φ : Tm} {L : Finset ℕ}
    : HasTy Γ (.univ ℓ) A
    → JEq Γ (.univ 0) (.trunc A) (.unit 0)
    → (∀ x ∉ L, HasTy (Γ.cons x A) (.univ 0) (φ.bs0 (.fv x)))
    → InnerTy Γ A (.choose A φ)
  | nats {Γ : Ctx} : Γ.Ok → InnerTy Γ (.univ 1) .nats
  | zero {Γ : Ctx} : Γ.Ok → InnerTy Γ .nats .zero
  | succ {Γ : Ctx} : Γ.Ok → InnerTy Γ (.pi 1 .nats .nats) .succ
  | natrec_cf {Γ : Ctx} {ℓ : ℕ} {C n z s Cn : Tm} {L : Finset ℕ}
    : (∀ x ∉ L, HasTy (Γ.cons x .nats) (.univ ℓ) (C.bs0 (.fv x)))
    → HasTy Γ .nats n
    → HasTy Γ (C.bs0 .zero) z
    → (∀ x ∉ L,
        HasTy (Γ.cons x .nats) (.pi ℓ (C.bs0 (.fv x))
              (C.bs0 (.app 1 .nats .nats .succ (.fv x)))) (s.bs0 (.fv x)))
    → JEq Γ (.univ ℓ) (C.bs0 n) Cn
    → InnerTy Γ Cn (.natrec C n z s)

theorem Ctx.InnerTy.has_ty {Γ : Ctx} {A a : Tm} (h : Γ.InnerTy A a) : Γ.HasTy A a
  := by cases h <;> constructor <;> assumption

def Ctx.OuterTy (Γ : Ctx) (A : Tm) (a : Tm) := ∃B, Γ.InnerTy B a ∧ Γ.TyEq' B A

theorem Ctx.OuterTy.cast
  {Γ : Ctx} {A B : Tm} (hAB : Γ.TyEq A B) {a : Tm} (h : Γ.OuterTy A a) : Γ.OuterTy B a
  := let ⟨C, hC, hCA⟩ := h; ⟨C, hC, hCA.tail hAB⟩

theorem Ctx.InnerTy.outer_ty {Γ : Ctx} {A a : Tm} (h : Γ.InnerTy A a) : Γ.OuterTy A a
  := ⟨A, h, .single h.has_ty.regular⟩

theorem Ctx.OuterTy.has_ty {Γ : Ctx} {A a : Tm} (h : Γ.OuterTy A a) : Γ.HasTy A a
  := have ⟨_, ha, hBA⟩ := h; ha.has_ty.multicast hBA

theorem Ctx.HasTy.outer_ty {Γ : Ctx} {A a : Tm} (h : Γ.HasTy A a) : Γ.OuterTy A a
  := by induction h with
  | cast => apply OuterTy.cast <;> assumption
  | _ => apply Ctx.InnerTy.outer_ty; constructor <;> assumption

theorem Ctx.OuterTy.has_ty_iff {Γ : Ctx} {A a : Tm} : Γ.OuterTy A a ↔ Γ.HasTy A a
  := ⟨Ctx.OuterTy.has_ty, Ctx.HasTy.outer_ty⟩

theorem Ctx.Ok.at_eq {Γ : Ctx} {x : ℕ} {A B : Tm} (h : Γ.Ok) (hA : Γ.At x A) (hB : Γ.At x B) : A = B
  := by induction hA with
  | here => cases hB with
    | here => rfl
    | there hx => exact (h.var hx.mem_dv).elim
  | there hx I => cases hB with
    | here => exact (h.var hx.mem_dv).elim
    | there hy => exact I h.tail hy

theorem Ctx.HasTy.unique_helper {Γ : Ctx} {X Y a : Tm} (hX : Γ.HasTy X a) (hY : Γ.InnerTy Y a)
  : TyEq' Γ X Y := by induction hX generalizing Y with
  | var hΓ hA => cases hY with | var hΓ' hB =>
    cases hΓ.at_eq hA hB; exact .single (JEq.regular (.var hΓ.zero hA))
  | univ | unit | nil | empty | eqn | pi_cf | sigma_cf | trunc | nats | zero =>
    cases hY; apply TyEq'.of_ty; constructor; constructor; apply Ctx.Ok.zero
            ; first | assumption | apply HasTy.ok; assumption
  | app_cf hA hB hℓ hf ha hBa IA IB If Ia => cases hY with | app_cf hA' hB' hℓ' hf' ha' hBa' =>
    exact .trans (.single hBa.symm.ty_eq) (.single hBa'.ty_eq)
  | abs_cf hA hB hℓ hb IA IB Ib => cases hY with | abs_cf hA' hB' hℓ' hb' =>
    apply Relation.TransGen.single
    constructor
    apply JEq.pi_cf (L := _ ∪ _) hA.refl
    · intro x hx
      simp only [Finset.mem_union, not_or] at hx
      apply JEq.symm
      have hBx := hB x hx.1
      have hBx' := hB' x hx.2
      have ⟨C, hCx, hC⟩ := hBx.outer_ty;
      have hn := IB x hx.1 hCx
      sorry
    exact hℓ
  | cast hAB ha IA => exact .head hAB.symm (IA hY)
  | _ => sorry

-- -- Step 6: hasty is TyEq* unique

-- -- Step 7: TyEq is transitive, so TyEq* == TyEq

-- -- Step 8: hasty is unique
