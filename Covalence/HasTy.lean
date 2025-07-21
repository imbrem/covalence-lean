import Covalence.JEq

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
    → (Ba = B.bs0 a)
    → HasTy Γ Ba (.app A B f a)
  | abs_cf {Γ : Ctx} {m : ℕ} {A B b : Tm} {L : Finset ℕ}
    : HasTy Γ (.univ m) A
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
    → (Ba = B.bs0 (.fst A B e))
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
        HasTy (Γ.cons x .nats) (.pi (C.bs0 (.fv x)) (C.bs0 (.app .nats .nats .succ (.fv x)))) s)
    → (Cn = C.bs0 n)
    → HasTy Γ Cn (.natrec C n z s)
  | cast {Γ : Ctx} {ℓ : ℕ} {A B a : Tm}
    : JEq Γ (.univ ℓ) A B
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

theorem Ctx.HasTy.ok {Γ : Ctx} {A a : Tm} (h : Ctx.HasTy Γ A a) : Γ.Ok := h.refl.ok

theorem Ctx.JEq.has_ty_both {Γ : Ctx} {A a b : Tm} (h : Ctx.JEq Γ A a b)
  : Γ.HasTy A a ∧ Γ.HasTy A b
  := by induction h with
  | nil_ok => rw [and_self]; apply HasTy.zero; constructor
  | cons_ok hΓ =>
    rw [and_self]; apply HasTy.zero; constructor
    · exact hΓ.ok
    · assumption
    · assumption
  | univ | var | unit | nil | empty | nats | succ =>
    rw [and_self]
    constructor <;> (try apply ok) <;> assumption
  | eqn hA ha hb IA Ia Ib => exact ⟨IA.1.eqn Ia.1 Ib.1, IA.2.eqn (Ia.2.cast hA) (Ib.2.cast hA)⟩
  | pi_cf hA hB hℓ IA IB =>
    stop
    exact ⟨IA.1.pi_cf (fun x hx => (IB x hx).1) hℓ, IA.2.pi_cf (fun x hx => (IB x hx).2) hℓ⟩
  | eqn_ext => sorry
  | pi_ext_cf hA hB hf hg hL => sorry
  | sigma_ext_cf hA hB he => sorry
  | prop_ext hA hB mp mpr => sorry
  | prop_uniq hA ha hb => sorry
  | cast => sorry
  | _ => sorry
