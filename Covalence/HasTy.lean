import Covalence.Subst

inductive Ctx.HasTy : Ctx → Tm → Tm → Prop
  | univ {Γ : Ctx} {ℓ : ℕ} : Γ.Ok → HasTy Γ (.univ (ℓ + 1)) (.univ ℓ)
  | var {Γ : Ctx} {x : ℕ} {A : Tm} : Γ.Ok → Γ.At x A → HasTy Γ A (.fv x)
  | unit {Γ : Ctx} {ℓ : ℕ} : Γ.Ok → HasTy Γ (.univ ℓ) (.unit ℓ)
  | nil {Γ : Ctx} {ℓ : ℕ} : Γ.Ok → HasTy Γ (.unit ℓ) (.nil ℓ)
  | empty {Γ : Ctx} {ℓ : ℕ} : Γ.Ok → HasTy Γ (.univ ℓ) (.empty ℓ)
  | eqn {Γ : Ctx} {ℓ : ℕ} {A a b : Tm}
    : HasTy Γ (.univ ℓ) A
    → HasTy Γ A a
    → HasTy Γ A b
    → HasTy Γ (.univ 0) (.eqn A a b)
  | pi_cf {Γ : Ctx} {ℓ m n : ℕ} {A B : Tm} {L : Finset ℕ}
    : HasTy Γ (.univ m) A
    → (∀ x ∉ L, HasTy (Γ.cons x A) (.univ n) (B.bs0 (.fv x)))
    → (ℓ = m.imax n)
    → HasTy Γ (.univ ℓ) (.pi A B)
  | app_cf {Γ : Ctx} {m n : ℕ} {A B Ba f a : Tm} {L : Finset ℕ}
    : HasTy Γ (.univ m) A
    → (∀ x ∉ L, HasTy (Γ.cons x A) (.univ n) (B.bs0 (.fv x)))
    → HasTy Γ (.pi A B) f
    → HasTy Γ A a
    → JEq Γ (.univ n) (B.bs0 a) Ba
    → HasTy Γ Ba (.app A B f a)
  | abs_cf {Γ : Ctx} {m n : ℕ} {A B b : Tm} {L : Finset ℕ}
    : HasTy Γ (.univ m) A
    → (∀ x ∉ L, HasTy (Γ.cons x A) (.univ n) (B.bs0 (.fv x)))
    → (∀ x ∉ L, HasTy (Γ.cons x A) (B.bs0 (.fv x)) (b.bs0 (.fv x)))
    → HasTy Γ (.pi A B) (.abs A b)
  | sigma_cf {Γ : Ctx} {ℓ m n : ℕ} {A B Ba f a : Tm} {L : Finset ℕ}
    : HasTy Γ (.univ m) A
    → (∀ x ∉ L, HasTy (Γ.cons x A) (.univ n) (B.bs0 (.fv x)))
    → (ℓ = m ⊔ n)
    → HasTy Γ (.univ ℓ) (.sigma A B)
  | pair_cf {Γ : Ctx} {m n : ℕ} {A B a b : Tm} {L : Finset ℕ}
    : HasTy Γ (.univ m) A
    → HasTy Γ A a
    → (∀ x ∉ L, HasTy (Γ.cons x A) (.univ n) (B.bs0 (.fv x)))
    → HasTy Γ (B.bs0 a) b
    → HasTy Γ (.sigma A B) (.pair A B a b)
  | fst_cf {Γ : Ctx} {m n : ℕ} {A B e : Tm} {L : Finset ℕ}
    : HasTy Γ (.univ m) A
    → (∀ x ∉ L, HasTy (Γ.cons x A) (.univ n) (B.bs0 (.fv x)))
    → HasTy Γ (.sigma A B) e
    → HasTy Γ A (.fst A B e)
  | snd_cf {Γ : Ctx} {m n : ℕ} {A B Ba e : Tm} {L : Finset ℕ}
    : HasTy Γ (.univ m) A
    → (∀ x ∉ L, HasTy (Γ.cons x A) (.univ n) (B.bs0 (.fv x)))
    → HasTy Γ (.sigma A B) e
    → JEq Γ (.univ n) (B.bs0 (.fst A B e)) Ba
    → HasTy Γ Ba (.snd A B e)
  | dite_cf {Γ : Ctx} {ℓ : ℕ} {φ A a b : Tm} {L : Finset ℕ}
    : HasTy Γ (.univ 0) φ
    → HasTy Γ (.univ ℓ) A
    → (∀ x ∉ L, HasTy (Γ.cons x φ) A a)
    → (∀ x ∉ L, HasTy (Γ.cons x (.not φ)) A b)
    → HasTy Γ A (.dite φ A a b)
  | trunc {Γ : Ctx} {ℓ : ℕ} {A : Tm}
    : HasTy Γ (.univ ℓ) A
    → HasTy Γ (.univ 0) (.trunc A)
  | choose_cf {Γ : Ctx} {ℓ} {A φ : Tm} {L : Finset ℕ}
    : HasTy Γ (.univ ℓ) A
    → JEq Γ (.univ 0) (.trunc A) (.unit 0)
    → (∀ x ∉ L, HasTy (Γ.cons x A) (.univ 0) (φ.bs0 (.fv x)))
    → HasTy Γ A (.choose A φ)
  | nats {Γ : Ctx} : Γ.Ok → HasTy Γ (.univ 1) .nats
  | zero {Γ : Ctx} : Γ.Ok → HasTy Γ .nats .zero
  | succ {Γ : Ctx} : Γ.Ok → HasTy Γ (.pi .nats .nats) .succ
  | natrec_cf {Γ : Ctx} {ℓ : ℕ} {C n z s Cn : Tm} {L : Finset ℕ}
    : (∀ x ∉ L, HasTy (Γ.cons x .nats) (.univ ℓ) (C.bs0 (.fv x)))
    → HasTy Γ .nats n
    → HasTy Γ (C.bs0 .zero) z
    → (∀ x ∉ L,
        HasTy (Γ.cons x .nats) (.pi (C.bs0 (.fv x))
              (C.bs0 (.app .nats .nats .succ (.fv x)))) (s.bs0 (.fv x)))
    → JEq Γ (.univ ℓ) (C.bs0 n) Cn
    → HasTy Γ Cn (.natrec C n z s)
  | cast {Γ : Ctx} {A B a : Tm}
    : TyEq Γ A B
    → HasTy Γ A a
    → HasTy Γ B a

theorem Ctx.HasTy.refl {Γ : Ctx} {A a : Tm} (h : Ctx.HasTy Γ A a) : Γ.JEq A a a
  := by induction h with
  | cast hA ha Ia => exact hA.cast Ia
  | zero => rw [<-ok_iff_zero] ; assumption
  | _ =>
    constructor <;>
    (try simp only [<-ok_iff_zero]) <;>
    assumption

theorem Ctx.HasTy.is_ty {Γ : Ctx} {ℓ : ℕ} {A : Tm} (h : Ctx.HasTy Γ (.univ ℓ) A) : Γ.IsTy A
  := ⟨_, h.refl⟩

theorem Ctx.HasTy.ok {Γ : Ctx} {A a : Tm} (h : Ctx.HasTy Γ A a) : Γ.Ok := h.refl.ok

theorem Ctx.HasTy.not {Γ : Ctx} {ℓ : ℕ} {φ : Tm} (h : Ctx.HasTy Γ (.univ ℓ) φ)
  : Γ.HasTy (.univ 0) φ.not
  :=  .pi_cf (L := Γ.dv) h (fun _ hx => .empty (h.ok.cons hx h.is_ty)) rfl

theorem Ctx.Var.ty {Γ : Ctx} {x : ℕ} {A : Tm} (h : Γ.Var x A) : Γ.HasTy A (.fv x)
  := have ⟨_, hΓ, hX⟩ := h; (HasTy.var hX.ok hΓ).cast hX

theorem Ctx.HasTy.wk {Γ Δ : Ctx} (h : Γ.Wk Δ) {a A : Tm} (h : Δ.HasTy a A) : Γ.HasTy a A
  := by induction h generalizing Γ with
  | cast hA ha I => exact (I h).cast (hA.wk h)
  | var hΓ hA => exact (h.at hA).ty
  | _ =>
    constructor <;> (first | exact h.src_ok | (try apply JEq.wk) <;> apply_assumption | {
      rename Finset ℕ => L
      intro x hx
      have ⟨hL, hΓ⟩ : x ∉ L ∧ x ∉ Γ.dv := by rw [<-Finset.notMem_union]; exact hx
      apply_assumption <;> (first | assumption | apply Wk.lift) <;> first
        | assumption | (apply HasTy.is_ty; (try apply not) <;> first | assumption | constructor)
      <;> exact h.trg_ok
    }) <;> assumption

theorem Ctx.HasTy.cast0
  {Γ : Ctx} {x : ℕ} {B C a : Tm} (h : (Γ.cons x B).HasTy C a)
  {A : Tm} (hB : Γ.TyEq A B) : (Γ.cons x A).HasTy C a
  := h.wk (hB.ok.wk.lift h.ok.var hB)

def Ctx.Cmp (Γ : Ctx) (A a b : Tm) : Prop := Γ.HasTy A a ∧ Γ.HasTy A b

theorem Ctx.HasTy.cmp {Γ : Ctx} {A a : Tm} (h : Γ.HasTy A a) : Γ.Cmp A a a := ⟨h, h⟩

theorem Ctx.Cmp.symm {Γ : Ctx} {A a b : Tm} (h : Γ.Cmp A a b) : Γ.Cmp A b a := ⟨h.2, h.1⟩

theorem Ctx.Cmp.trans {Γ : Ctx} {A a b c : Tm} (hab : Γ.Cmp A a b) (hbc : Γ.Cmp A b c)
  : Γ.Cmp A a c := ⟨hab.1, hbc.2⟩

--TODO: we need substitution here...
theorem Ctx.JEq.cmp {Γ : Ctx} {A a b : Tm} (h : Ctx.JEq Γ A a b)
  : Γ.Cmp A a b
  := by induction h with
  | nil_ok => apply HasTy.cmp; apply HasTy.zero; constructor
  | cons_ok hΓ =>
    apply HasTy.cmp; apply HasTy.zero; constructor
    · exact hΓ.ok
    · assumption
    · apply JEq.lhs_ty; assumption
  | univ | var | unit | nil | empty | nats | succ =>
    apply HasTy.cmp; constructor <;> (try apply ok) <;> assumption
  | eqn hA ha hb IA Ia Ib
    => exact ⟨IA.1.eqn Ia.1 Ib.1, IA.2.eqn (Ia.2.cast hA.ty_eq) (Ib.2.cast hA.ty_eq)⟩
  | pi_cf hA hB hℓ IA IB =>
    exact ⟨
      IA.1.pi_cf (fun x hx => (IB x hx).1) hℓ,
      IA.2.pi_cf (fun x hx => (IB x hx).2.cast0 hA.ty_eq.symm) hℓ
    ⟩
  | app_cf hA hB hf hg hBa IA IB If Ig IBa =>
    exact ⟨
      IA.1.app_cf (fun x hx => (IB x hx).1) If.1 Ig.1 hBa,
      (IA.2.app_cf (fun x hx => (IB x hx).2.cast0 hA.ty_eq.symm)
       (If.2.cast ⟨_, hA.pi_cf hB rfl⟩) (Ig.2.cast ⟨_, hA⟩) (.trans sorry hBa))
    ⟩
  | eqn_ext => sorry
  | pi_ext_cf hA hB hf hg hL => sorry
  | sigma_ext_cf hA hB he => sorry
  | prop_ext hA hB mp mpr => sorry
  | cast => sorry
  | _ => sorry
