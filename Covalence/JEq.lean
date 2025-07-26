import Covalence.Syntax

inductive Ctx : Type where
  | nil : Ctx
  | cons (Γ : Ctx) (x : ℕ) (A : Tm) : Ctx

def Ctx.length : Ctx → ℕ
  | nil => 0
  | cons Γ _ _ => Γ.length + 1

def Ctx.dv : Ctx → Finset ℕ
  | nil => ∅
  | cons Γ x _ => {x} ∪ Γ.dv

inductive Ctx.At : Ctx → ℕ → Tm → Prop
  | here {Γ : Ctx} {x : ℕ} {A : Tm} : Ctx.At (Ctx.cons Γ x A) x A
  | there {Γ : Ctx} {x y : ℕ} {A B : Tm} (h : Ctx.At Γ x A) : Ctx.At (Ctx.cons Γ y B) x A

@[simp]
theorem Ctx.At.mem_dv {Γ : Ctx} {x : ℕ} {A : Tm} (h : Ctx.At Γ x A) : x ∈ Γ.dv := by
  induction h <;> simp [dv, *]

inductive Ctx.NoRep : Ctx → Prop
  | nil : Ctx.NoRep .nil
  | cons {Γ : Ctx} {x : ℕ} {A : Tm} (h : Ctx.NoRep Γ) (hx : x ∉ Γ.dv) : Ctx.NoRep (Ctx.cons Γ x A)

-- Yaar; go over these and add requirements...
inductive Ctx.JEq : Ctx → Tm → Tm → Tm → Prop
  -- Congruence
  | univ {Γ : Ctx} {ℓ : ℕ} : JEq Γ .nats .zero .zero → JEq Γ (.univ (ℓ + 1)) (.univ ℓ) (.univ ℓ)
  | var {Γ : Ctx} {x : ℕ} {A : Tm} : JEq Γ .nats .zero .zero → Γ.At x A → JEq Γ A (.fv x) (.fv x)
  | unit {Γ : Ctx} {ℓ : ℕ} : JEq Γ .nats .zero .zero → JEq Γ (.univ ℓ) (.unit ℓ) (.unit ℓ)
  | nil {Γ : Ctx} {ℓ : ℕ} : JEq Γ .nats .zero .zero → JEq Γ (.unit ℓ) (.nil ℓ) (.nil ℓ)
  | empty {Γ : Ctx} {ℓ : ℕ} : JEq Γ .nats .zero .zero → JEq Γ (.univ ℓ) (.empty ℓ) (.empty ℓ)
  | eqn {Γ : Ctx} {ℓ : ℕ} {A A' a a' b b' : Tm}
    : JEq Γ (.univ ℓ) A A'
    → JEq Γ A a a'
    → JEq Γ A b b'
    → JEq Γ (.univ 0) (.eqn A a b) (.eqn A' a' b')
  | pi_cf {Γ : Ctx} {ℓ m n : ℕ} {A A' B B' : Tm} {L : Finset ℕ}
    : JEq Γ (.univ m) A A'
    → (∀ x ∉ L, JEq (Γ.cons x A) (.univ n) (B.bs0 (.fv x)) (B'.bs0 (.fv x)))
    → (ℓ = m.imax n)
    → JEq Γ (.univ ℓ) (.pi A B) (.pi A' B')
  | app_cf {Γ : Ctx} {m n : ℕ} {A A' B B' Ba f f' a a' : Tm} {L : Finset ℕ}
    : JEq Γ (.univ m) A A'
    → (∀ x ∉ L, JEq (Γ.cons x A) (.univ n) (B.bs0 (.fv x)) (B'.bs0 (.fv x)))
    → JEq Γ (.pi A B) f f'
    → JEq Γ A a a'
    → JEq Γ (.univ n) (B.bs0 a) Ba
    → JEq Γ Ba (.app A B f a) (.app A' B' f' a')
  | abs_cf {Γ : Ctx} {m n : ℕ} {A A' B b b' : Tm} {L : Finset ℕ}
    : JEq Γ (.univ m) A A'
    → (∀ x ∉ L, JEq (Γ.cons x A) (.univ n) (B.bs0 (.fv x)) (B.bs0 (.fv x)))
    → (∀ x ∉ L, JEq (Γ.cons x A) (B.bs0 (.fv x)) (b.bs0 (.fv x)) (b'.bs0 (.fv x)))
    → JEq Γ (.pi A B) (.abs A b) (.abs A' b')
  | sigma_cf {Γ : Ctx} {ℓ m n : ℕ} {A A' B B' : Tm} {L : Finset ℕ}
    : JEq Γ (.univ m) A A'
    → (∀ x ∉ L, JEq (Γ.cons x A) (.univ n) (B.bs0 (.fv x)) (B'.bs0 (.fv x)))
    → (ℓ = m ⊔ n)
    → JEq Γ (.univ ℓ) (.sigma A B) (.sigma A' B')
  | pair_cf {Γ : Ctx} {m n : ℕ} {A A' B B' a a' b b' : Tm} {L : Finset ℕ}
    : JEq Γ (.univ m) A A'
    → (∀ x ∉ L, JEq (Γ.cons x A) (.univ n) (B.bs0 (.fv x)) (B'.bs0 (.fv x)))
    → JEq Γ A a a'
    → JEq Γ (B.bs0 a) b b'
    → JEq Γ (.sigma A B) (.pair A B a b) (.pair A' B' a' b')
  | fst_cf {Γ : Ctx} {m n : ℕ} {A A' B B' e e' : Tm} {L : Finset ℕ}
    : JEq Γ (.univ m) A A'
    → (∀ x ∉ L, JEq (Γ.cons x A) (.univ n) (B.bs0 (.fv x)) (B'.bs0 (.fv x)))
    → JEq Γ (.sigma A B) e e'
    → JEq Γ A (.fst A B e) (.fst A' B' e')
  | snd_cf  {Γ : Ctx} {m n : ℕ} {A A' B B' Ba e e' : Tm} {L : Finset ℕ}
    : JEq Γ (.univ m) A A'
    → (∀ x ∉ L, JEq (Γ.cons x A) (.univ n) (B.bs0 (.fv x)) (B'.bs0 (.fv x)))
    → JEq Γ (.sigma A B) e e'
    → JEq Γ (.univ n) (B.bs0 (.fst A B e)) Ba
    → JEq Γ Ba (.snd A B e) (.snd A' B' e')
  | dite_cf {Γ : Ctx} {ℓ : ℕ} {φ φ' A A' a a' b b' : Tm} {L : Finset ℕ}
    : JEq Γ (.univ 0) φ φ'
    → JEq Γ (.univ ℓ) A A'
    → (∀ x ∉ L, JEq (Γ.cons x φ) A a a')
    → (∀ x ∉ L, JEq (Γ.cons x (.not φ)) A b b')
    → JEq Γ A (.dite φ A a b) (.dite φ' A' a' b')
  | trunc {Γ : Ctx} {ℓ : ℕ} {A A' : Tm}
    : JEq Γ (.univ ℓ) A A'
    → JEq Γ (.univ 0) (.trunc A) (.trunc A')
  | choose_cf {Γ : Ctx} {ℓ} {A A' φ φ' : Tm} {L : Finset ℕ}
    : JEq Γ (.univ ℓ) A A'
    → JEq Γ (.univ 0) (.trunc A) (.unit 0)
    → (∀ x ∉ L, JEq (Γ.cons x A) (.univ 0) (φ.bs0 (.fv x)) (φ'.bs0 (.fv x)))
    → JEq Γ A (.choose A φ) (.choose A' φ')
  | nats {Γ : Ctx} : JEq Γ .nats .zero .zero → JEq Γ (.univ 1) .nats .nats
  | succ {Γ : Ctx} : JEq Γ .nats .zero .zero → JEq Γ (.pi .nats .nats) .succ .succ
  | natrec_cf {Γ : Ctx} {ℓ : ℕ} {C C' n n' z z' s s' Cn : Tm} {L : Finset ℕ}
    : (∀ x ∉ L, JEq (Γ.cons x .nats) (.univ ℓ) (C.bs0 (.fv x)) (C'.bs0 (.fv x)))
    → JEq Γ .nats n n'
    → JEq Γ (C.bs0 .zero) z z'
    → (∀ x ∉ L,
        JEq (Γ.cons x .nats) (.pi (C.bs0 (.fv x)) (C.bs0 (.app .nats .nats .succ (.fv x))))
          (s.bs0 (.fv x)) (s'.bs0 (.fv x)))
    → JEq Γ (.univ ℓ) (C.bs0 n) Cn
    → JEq Γ Cn (.natrec C n z s) (.natrec C' n' z' s')
  -- Equations
  | nil_uniq {Γ : Ctx} {A a b : Tm} : JEq Γ (.univ 0) A A → JEq Γ A a a → JEq Γ A a (.nil 0)
  | explode {Γ : Ctx} {ℓ : ℕ} {a : Tm} : JEq Γ (.empty ℓ) a a → JEq Γ (.univ 0) (.unit 0) (.empty 0)
  | eqn_rfl {Γ : Ctx} {A a b : Tm} : JEq Γ A a b → JEq Γ (.univ 0) (.eqn A a b) (.unit 0)
  | beta_abs_cf {Γ : Ctx} {m n : ℕ} {A B a b Ba ba : Tm} {L : Finset ℕ}
    : JEq Γ (.univ m) A A
    → (∀ x ∉ L, JEq (Γ.cons x A) (B.bs0 (.fv x)) (b.bs0 (.fv x)) (b.bs0 (.fv x)))
    → JEq Γ A a a
    → JEq Γ (.univ n) (B.bs0 a) Ba
    → JEq Γ Ba (b.bs0 a) ba
    → JEq Γ Ba (.app A B (.abs A b) a) ba
  | beta_fst_cf {Γ : Ctx} {m n : ℕ} {A B a b : Tm} {L : Finset ℕ}
    : JEq Γ (.univ m) A A
    → (∀ x ∉ L, JEq (Γ.cons x A) (.univ n) (B.bs0 (.fv x)) (B.bs0 (.fv x)))
    → JEq Γ A a a
    → JEq Γ (B.bs0 a) b b
    → JEq Γ A (.fst A B (.pair A B a b)) a
  | beta_snd_cf {Γ : Ctx} {m n : ℕ} {A B a b Ba : Tm} {L : Finset ℕ}
    : JEq Γ (.univ m) A A
    → (∀ x ∉ L, JEq (Γ.cons x A) (.univ n) (B.bs0 (.fv x)) (B.bs0 (.fv x)))
    → JEq Γ A a a
    → JEq Γ (B.bs0 a) b b
    → JEq Γ (.univ n) (B.bs0 a) Ba
    → JEq Γ Ba (.snd A B (.pair A B a b)) b
  | inhab {Γ : Ctx} {A a : Tm}
    : JEq Γ A a a
    → JEq Γ (.univ 0) (.trunc A) (.unit 0)
  | spec_cf {Γ : Ctx} {ℓ} {A φ φa : Tm} {L : Finset ℕ}
    : JEq Γ (.univ ℓ) A A
    → JEq Γ (.univ 0) (.trunc A) (.unit 0)
    → (∀ x ∉ L, JEq (Γ.cons x A) (.univ 0) (φ.bs0 (.fv x)) (φ.bs0 (.fv x)))
    → JEq Γ (.univ 0) (φ.bs0 (.choose A φ)) φa
    → JEq Γ (.univ 0) φa (.trunc (.sigma A φ))
  --TODO: think long and hard about the binding structure here...
  | beta_true_cf {Γ : Ctx} {ℓ : ℕ} {φ A a b : Tm} {L : Finset ℕ}
    : JEq Γ (.univ 0) φ (.unit 0)
    → JEq Γ (.univ ℓ) A A
    → (∀ x ∉ L, JEq (Γ.cons x φ) A a a)
    → (∀ x ∉ L, JEq (Γ.cons x (.not φ)) A b b)
    → JEq Γ A (.dite φ A a b) a
  | beta_false_cf {Γ : Ctx} {ℓ : ℕ} {φ A a b : Tm} {L : Finset ℕ}
    : JEq Γ (.univ 0) φ (.empty 0)
    → JEq Γ (.univ ℓ) A A
    → (∀ x ∉ L, JEq (Γ.cons x φ) A a a)
    → (∀ x ∉ L, JEq (Γ.cons x (.not φ)) A b b)
    → JEq Γ A (.dite φ A a b) b
  | beta_zero_cf {Γ : Ctx} {ℓ : ℕ} {C z s C0 : Tm} {L : Finset ℕ}
    : (∀ x ∉ L, JEq (Γ.cons x .nats) (.univ ℓ) (C.bs0 (.fv x)) (C.bs0 (.fv x)))
    → JEq Γ (C.bs0 .zero) z z
    → (∀ x ∉ L,
        JEq (Γ.cons x .nats) (.pi (C.bs0 (.fv x)) (C.bs0 (.app .nats .nats .succ (.fv x))))
          (s.bs0 (.fv x)) (s.bs0 (.fv x)))
    → JEq Γ (.univ ℓ) (C.bs0 .zero) C0
    → JEq Γ C0 (.natrec C .zero z s) z
  | beta_succ_cf {Γ : Ctx} {ℓ : ℕ} {C n z s sn Cn Cs : Tm} {L : Finset ℕ}
    : (∀ x ∉ L, JEq (Γ.cons x .nats) (.univ ℓ) (C.bs0 (.fv x)) (C.bs0 (.fv x)))
    → JEq Γ .nats n n
    → JEq Γ (C.bs0 .zero) z z
    → (∀ x ∉ L,
        JEq (Γ.cons x .nats) (.pi (C.bs0 (.fv x)) (C.bs0 (.app .nats .nats .succ (.fv x))))
          (s.bs0 (.fv x)) (s.bs0 (.fv x)))
    → JEq Γ (.pi (C.bs0 n) (C.bs0 (.app .nats .nats .succ n))) (s.bs0 n) sn
    → JEq Γ (.univ ℓ) (C.bs0 n) Cn
    → JEq Γ (.univ ℓ) (C.bs0 (.app .nats .nats .succ n)) Cs
    → JEq Γ Cs (.natrec C (.app .nats .nats .succ n) z s) (.app Cn Cs sn (.natrec C n z s))
  -- Context well-formedness
  | nil_ok : JEq .nil .nats .zero .zero
  | cons_ok {Γ : Ctx} {ℓ : ℕ} {x : ℕ} {A : Tm}
    : JEq Γ .nats .zero .zero → JEq Γ (.univ ℓ) A A → x ∉ Γ.dv → JEq (Γ.cons x A) .nats .zero .zero
  -- Extensionality
  | eqn_ext {Γ : Ctx} {ℓ : ℕ} {A a b : Tm}
    : JEq Γ (.univ ℓ) A A
    → JEq Γ A a a
    → JEq Γ A b b
    → JEq Γ (.univ 0) (.eqn A a b) (.unit 0)
    → JEq Γ A a b
  | pi_ext_cf {Γ : Ctx} {m n : ℕ} {A B f g : Tm} {L : Finset ℕ}
    : JEq Γ (.univ m) A A
    → (∀ x ∉ L, JEq (Γ.cons x A) (.univ n) (B.bs0 (.fv x)) (B.bs0 (.fv x)))
    → JEq Γ (.pi A B) f f
    → JEq Γ (.pi A B) g g
    → (∀ x ∉ L, JEq (Γ.cons x A) (B.bs0 (.fv x)) (.app A B f (.fv x)) (.app A B g (.fv x)))
    → JEq Γ (.pi A B) f g
  | sigma_ext_cf {Γ : Ctx} {n m : ℕ} {A B e : Tm} {L : Finset ℕ}
    : JEq Γ (.univ m) A A
    → (∀ x ∉ L, JEq (Γ.cons x A) (.univ n) (B.bs0 (.fv x)) (B.bs0 (.fv x)))
    → JEq Γ (.sigma A B) e e
    → JEq Γ (.sigma A B) e (.pair A B (.fst A B e) (.snd A B e))
  | prop_ext {Γ : Ctx} {A B mp mpr : Tm}
    : JEq Γ (.univ 0) A A
    → JEq Γ (.univ 0) B B
    → JEq Γ (.pi A B) mp mp
    → JEq Γ (.pi B A) mpr mpr
    → JEq Γ (.univ 0) A B
  -- Equivalence relations
  | trans {Γ : Ctx} {A a b c : Tm} : JEq Γ A a b → JEq Γ A b c → JEq Γ A a c
  | symm {Γ : Ctx} {A a b : Tm} : JEq Γ A a b → JEq Γ A b a
  | cast {Γ : Ctx} {ℓ : ℕ} {A B a b : Tm} : JEq Γ (.univ ℓ) A B → JEq Γ A a b → JEq Γ B a b

theorem Ctx.JEq.lhs {Γ : Ctx} {A a b : Tm} (h : JEq Γ A a b) : Γ.JEq A a a := h.trans h.symm

theorem Ctx.JEq.rhs {Γ : Ctx} {A a b : Tm} (h : JEq Γ A a b) : Γ.JEq A b b := h.symm.trans h

def Ctx.TyEq (Γ : Ctx) (A B : Tm) : Prop := ∃ℓ, Ctx.JEq Γ (.univ ℓ) A B

theorem Ctx.JEq.ty_eq {Γ : Ctx} {ℓ : ℕ} {A B : Tm} (h : Ctx.JEq Γ (.univ ℓ) A B)
  : Γ.TyEq A B := ⟨ℓ, h⟩

theorem Ctx.TyEq.symm {Γ : Ctx} {A B : Tm} (h : Γ.TyEq A B) : Γ.TyEq B A
  := have ⟨ℓ, h⟩ := h; ⟨ℓ, h.symm⟩

theorem Ctx.TyEq.cast {Γ : Ctx} {A B : Tm} (h : Γ.TyEq A B) {a b : Tm} (ha : Γ.JEq A a b)
  : Γ.JEq B a b := have ⟨_, h⟩ := h; h.cast ha

def Ctx.IsTy (Γ : Ctx) (A : Tm) : Prop := Γ.TyEq A A

theorem Ctx.TyEq.lhs {Γ : Ctx} {A B : Tm} (h : Γ.TyEq A B) : Γ.IsTy A
  := have ⟨ℓ, h⟩ := h; ⟨ℓ, h.lhs⟩

theorem Ctx.TyEq.rhs {Γ : Ctx} {A B : Tm} (h : Γ.TyEq A B) : Γ.IsTy B
  := have ⟨ℓ, h⟩ := h; ⟨ℓ, h.rhs⟩

theorem Ctx.IsTy.refl {Γ : Ctx} {A : Tm} (h : Γ.IsTy A) : Γ.TyEq A A := h

theorem Ctx.JEq.lhs_ty {Γ : Ctx} {ℓ : ℕ} {A B : Tm} (h : Γ.JEq (.univ ℓ) A B) : Γ.IsTy A
  := h.lhs.ty_eq

theorem Ctx.JEq.rhs_ty {Γ : Ctx} {ℓ : ℕ} {A B : Tm} (h : Γ.JEq (.univ ℓ) A B) : Γ.IsTy B
  := h.rhs.ty_eq

inductive Ctx.Ok : Ctx → Prop
  | nil : Ctx.Ok .nil
  | cons {Γ : Ctx} {x : ℕ} {A : Tm} : Ctx.Ok Γ → x ∉ Γ.dv → IsTy Γ A → Ctx.Ok (Γ.cons x A)

attribute [simp] Ctx.Ok.nil

theorem Ctx.Ok.no_rep {Γ : Ctx} (h : Γ.Ok) : Ctx.NoRep Γ
  := by induction h <;> constructor <;> assumption

theorem Ctx.Ok.var {Γ : Ctx} {x : ℕ} {A : Tm} (h : (Γ.cons x A).Ok) : x ∉ Γ.dv
  := by cases h; assumption

theorem Ctx.Ok.ty {Γ : Ctx} {x : ℕ} {A : Tm} (h : (Γ.cons x A).Ok) : IsTy Γ A
  := by cases h; assumption

theorem Ctx.Ok.tail {Γ : Ctx} {x : ℕ} {A : Tm} (h : (Γ.cons x A).Ok) : Ctx.Ok Γ
  := by cases h; assumption

theorem Ctx.JEq.ok {Γ : Ctx} {A a b : Tm} (h : Ctx.JEq Γ A a b) : Γ.Ok := by induction h with
  | nil_ok | cons_ok => constructor <;> first | assumption | constructor <;> assumption
  | _ => assumption

theorem Ctx.Ok.zero {Γ : Ctx} (h : Γ.Ok) : Γ.JEq .nats .zero .zero
  := by induction h with
  | nil => constructor
  | cons hΓ hx hA =>
    cases hA
    constructor <;> assumption

theorem Ctx.Ok.univ {Γ : Ctx} (h : Γ.Ok) {ℓ : ℕ} : Γ.JEq (.univ (ℓ + 1)) (.univ ℓ) (.univ ℓ)
  := h.zero.univ

theorem Ctx.Ok.unit {Γ : Ctx} (h : Γ.Ok) {ℓ : ℕ} : Γ.JEq (.univ ℓ) (.unit ℓ) (.unit ℓ)
  := h.zero.unit

theorem Ctx.Ok.empty {Γ : Ctx} (h : Γ.Ok) {ℓ : ℕ} : Γ.JEq (.univ ℓ) (.empty ℓ) (.empty ℓ)
  := h.zero.empty

theorem Ctx.Ok.nats {Γ : Ctx} (h : Γ.Ok) : Γ.JEq (.univ 1) .nats .nats
  := h.zero.nats

theorem Ctx.JEq.not {Γ : Ctx} {ℓ : ℕ} {A A' : Tm} (h : JEq Γ (.univ ℓ) A A')
  : JEq Γ (.univ 0) (.not A) (.not A')
  := .pi_cf (L := Γ.dv) h (fun _ hx => (h.ok.cons hx h.lhs_ty).empty) rfl

theorem Ctx.ok_iff_zero {Γ : Ctx} : Γ.Ok ↔ Γ.JEq .nats .zero .zero := ⟨Ok.zero, JEq.ok⟩

inductive Ctx.Scoped : Ctx → Prop
  | nil : Ctx.Scoped .nil
  | cons {Γ : Ctx} {x : ℕ} {A : Tm} (h : Ctx.Scoped Γ) (hx : x ∉ Γ.dv) (hA : A.fvs ⊆ Γ.dv)
    : Ctx.Scoped (Ctx.cons Γ x A)

attribute [simp] Ctx.Scoped.nil

theorem Ctx.Scoped.var {Γ : Ctx} {x : ℕ} {A : Tm} (h : Ctx.Scoped (Ctx.cons Γ x A)) : x ∉ Γ.dv
  := by cases h; assumption

theorem Ctx.Scoped.ty {Γ : Ctx} {x : ℕ} {A : Tm} (h : Ctx.Scoped (Ctx.cons Γ x A)) : A.fvs ⊆ Γ.dv
  := by cases h; assumption

theorem Ctx.Scoped.tail {Γ : Ctx} {x : ℕ} {A : Tm} (h : Ctx.Scoped (Ctx.cons Γ x A)) : Ctx.Scoped Γ
  := by cases h; assumption

theorem Ctx.Scoped.cons_iff {Γ : Ctx} {x : ℕ} {A : Tm} :
  Ctx.Scoped (Ctx.cons Γ x A) ↔ Ctx.Scoped Γ ∧ x ∉ Γ.dv ∧ A.fvs ⊆ Γ.dv
  := ⟨fun h => by cases h; simp [*], fun h => by constructor <;> simp [*]⟩

theorem Ctx.Scoped.at_ty
  {Γ : Ctx} {x : ℕ} {A : Tm} (h : Ctx.Scoped Γ) (hA : Γ.At x A) : A.fvs ⊆ Γ.dv
  := by induction hA with
  | here => exact Finset.Subset.trans h.ty Finset.subset_union_right
  | there _ I => exact Finset.Subset.trans (I h.tail) Finset.subset_union_right

theorem Ctx.Scoped.at
  {Γ : Ctx} {x : ℕ} {A : Tm} (h : Ctx.Scoped Γ) (hA : Γ.At x A) : {x} ∪ A.fvs ⊆ Γ.dv
  := by simp [Finset.union_subset_iff, h.at_ty hA, hA.mem_dv]

theorem Ctx.JEq.scoped_all {Γ : Ctx} {A a b : Tm} (h : Ctx.JEq Γ A a b)
  : Γ.Scoped ∧ A.fvs ⊆ Γ.dv ∧ a.fvs ⊆ Γ.dv ∧ b.fvs ⊆ Γ.dv
  := by induction h with
  | var hΓ hA IA => simp [hA.mem_dv, IA.1.at_ty hA, IA.1]
  | cons_ok => simp [Scoped.cons_iff, *]
  | _ =>
    simp only [forall_and, Ctx.dv, Tm.bs0_var_cofinite_iff, Tm.fsv_cofinite_iff] at *
    simp [Finset.union_subset_iff, *]

theorem Ctx.JEq.scoped_ctx {Γ : Ctx} {A a b : Tm} (h : Ctx.JEq Γ A a b)
  : Γ.Scoped := h.scoped_all.1

theorem Ctx.JEq.scoped_ty {Γ : Ctx} {A a b : Tm} (h : Ctx.JEq Γ A a b)
  : A.fvs ⊆ Γ.dv := h.scoped_all.2.1

theorem Ctx.JEq.scoped_lhs {Γ : Ctx} {A a b : Tm} (h : Ctx.JEq Γ A a b)
  : a.fvs ⊆ Γ.dv := h.scoped_all.2.2.1

theorem Ctx.JEq.scoped_rhs {Γ : Ctx} {A a b : Tm} (h : Ctx.JEq Γ A a b)
  : b.fvs ⊆ Γ.dv := h.scoped_all.2.2.2

-- theorem Ctx.JEq.scoped_cf_all {Γ : Ctx} {A B a b : Tm} {L : Finset ℕ}
--   (h : ∀x ∉ L, Ctx.JEq (Γ.cons x A) (B.bs0 (.fv x)) (a.bs0 (.fv x)) (b.bs0 (.fv x)))
--   : Γ.Scoped ∧ A.fvs ⊆ Γ.dv ∧ a.fvs ⊆ Γ.dv ∧ b.fvs ⊆ Γ.dv
--   := by induction h with
--   | var hΓ hA IA => simp [hA.mem_dv, IA.1.at_ty hA, IA.1]
--   | cons_ok => simp [Scoped.cons_iff, *]

theorem Ctx.JEq.scoped_cf_ty {Γ : Ctx} {A B : Tm} {ax bx : ℕ → Tm} {L : Finset ℕ}
  (h : ∀ x ∉ L, Ctx.JEq (Γ.cons x A) (B.bs0 (.fv x)) (ax x) (bx x))
  : B.fvs ⊆ Γ.dv := by
  have ⟨y, hy⟩ := Finset.exists_notMem (L ∪ B.fvs);
  have ⟨hL, ha⟩ : y ∉ L ∧ y ∉ B.fvs := by simp [Finset.mem_union] at hy; exact hy;
  intro x hx
  convert (B.fvs_bsubst_sub _).trans (h y hL).scoped_ty hx using 0
  simp [dv]
  intro h; cases h; exact (ha hx).elim

theorem Ctx.JEq.scoped_cf_lhs {Γ : Ctx} {A a : Tm} {Bx bx : ℕ → Tm} {L : Finset ℕ}
  (h : ∀ x ∉ L, Ctx.JEq (Γ.cons x A) (Bx x) (a.bs0 (.fv x)) (bx x))
  : a.fvs ⊆ Γ.dv := by
  have ⟨y, hy⟩ := Finset.exists_notMem (L ∪ a.fvs);
  have ⟨hL, ha⟩ : y ∉ L ∧ y ∉ a.fvs := by simp [Finset.mem_union] at hy; exact hy;
  intro x hx
  convert (a.fvs_bsubst_sub _).trans (h y hL).scoped_lhs hx using 0
  simp [dv]
  intro h; cases h; exact (ha hx).elim

theorem Ctx.JEq.scoped_cf_rhs {Γ : Ctx} {A b : Tm} {Bx ax : ℕ → Tm} {L : Finset ℕ}
  (h : ∀ x ∉ L, Ctx.JEq (Γ.cons x A) (Bx x) (ax x) (b.bs0 (.fv x)))
  : b.fvs ⊆ Γ.dv := by
  have h' := fun x hx => (h x hx).symm;
  apply scoped_cf_lhs
  apply h'

theorem Ctx.JEq.scoped_cf_ty' {Γ : Ctx} {A B : Tm} {ax bx : ℕ → Tm} {L : Finset ℕ}
  (h : ∀ x ∉ L, Ctx.JEq (Γ.cons x A) B (ax x) (bx x))
  : B.fvs ⊆ Γ.dv := by
  have ⟨y, hy⟩ := Finset.exists_notMem (L ∪ B.fvs);
  have ⟨hL, ha⟩ : y ∉ L ∧ y ∉ B.fvs := by simp [Finset.mem_union] at hy; exact hy;
  intro x hx
  convert (h y hL).scoped_ty hx using 0
  simp [dv]
  intro h; cases h; exact (ha hx).elim

theorem Ctx.JEq.scoped_cf_lhs' {Γ : Ctx} {A a : Tm} {Bx bx : ℕ → Tm} {L : Finset ℕ}
  (h : ∀ x ∉ L, Ctx.JEq (Γ.cons x A) (Bx x) a (bx x))
  : a.fvs ⊆ Γ.dv := by
  have ⟨y, hy⟩ := Finset.exists_notMem (L ∪ a.fvs);
  have ⟨hL, ha⟩ : y ∉ L ∧ y ∉ a.fvs := by simp [Finset.mem_union] at hy; exact hy;
  intro x hx
  convert (h y hL).scoped_lhs hx using 0
  simp [dv]
  intro h; cases h; exact (ha hx).elim

theorem Ctx.JEq.scoped_cf_rhs' {Γ : Ctx} {A b : Tm} {Bx ax : ℕ → Tm} {L : Finset ℕ}
  (h : ∀ x ∉ L, Ctx.JEq (Γ.cons x A) (Bx x) (ax x) b)
  : b.fvs ⊆ Γ.dv := by
  have h' := fun x hx => (h x hx).symm;
  apply scoped_cf_lhs'
  apply h'

theorem Ctx.TyEq.scoped_lhs {Γ : Ctx} {A B : Tm} (h : Ctx.TyEq Γ A B) : A.fvs ⊆ Γ.dv
  := have ⟨_, h⟩ := h; h.scoped_lhs

theorem Ctx.TyEq.scoped_rhs {Γ : Ctx} {A B : Tm} (h : Ctx.TyEq Γ A B) : B.fvs ⊆ Γ.dv
  := have ⟨_, h⟩ := h; h.scoped_rhs

theorem Ctx.IsTy.scoped {Γ : Ctx} {A : Tm} (h : Γ.IsTy A) : A.fvs ⊆ Γ.dv
  := h.scoped_lhs

theorem Ctx.Ok.scoped {Γ : Ctx} (h : Γ.Ok) : Γ.Scoped := h.zero.scoped_ctx

inductive Ctx.Lc : Ctx → Prop
  | nil : Ctx.Lc .nil
  | cons {Γ : Ctx} {x : ℕ} {A : Tm} (h : Ctx.Lc Γ) (hA : A.bvi = 0) : Ctx.Lc (Ctx.cons Γ x A)

theorem Ctx.Lc.head {Γ : Ctx} {x : ℕ} {A : Tm} (h : Ctx.Lc (Ctx.cons Γ x A)) : A.bvi = 0
  := by cases h; assumption

theorem Ctx.Lc.tail {Γ : Ctx} {x : ℕ} {A : Tm} (h : Ctx.Lc (Ctx.cons Γ x A)) : Ctx.Lc Γ
  := by cases h; assumption

theorem Ctx.Lc.cons_iff {Γ : Ctx} {x : ℕ} {A : Tm} :
  Ctx.Lc (Ctx.cons Γ x A) ↔ Ctx.Lc Γ ∧ A.bvi = 0
  := ⟨fun h => by cases h; simp [*], fun h => by constructor <;> simp [*]⟩

theorem Ctx.Lc.at {Γ : Ctx} {x : ℕ} {A : Tm} (h : Ctx.Lc Γ) (hA : Γ.At x A) : A.bvi = 0
  := by induction hA with | here => exact h.head | there _ I => exact I h.tail

theorem Ctx.JEq.lc_all {Γ : Ctx} {A a b : Tm} (h : Ctx.JEq Γ A a b)
  : Γ.Lc ∧ A.bvi = 0 ∧ a.bvi = 0 ∧ b.bvi = 0
  := by induction h with
  | var hΓ hA IA => simp [IA.1.at hA, Tm.bvi, *]
  | cons_ok => simp [Tm.bvi, Ctx.Lc.cons_iff, *]
  | _ =>
    simp only [
      Tm.bvi, forall_and, true_and, and_true, Nat.max_eq_zero_iff, Ctx.Lc.nil,
      Nat.sub_eq_zero_iff_le, Tm.bs0_lc_cofinite_iff, Tm.lc_cofinite_iff
    ] at * <;> simp [*]

theorem Ctx.JEq.lc_ctx {Γ : Ctx} {A a b : Tm} (h : Ctx.JEq Γ A a b)
  : Γ.Lc := h.lc_all.1

theorem Ctx.JEq.lc_ty {Γ : Ctx} {A a b : Tm} (h : Ctx.JEq Γ A a b)
  : A.bvi = 0 := h.lc_all.2.1

theorem Ctx.JEq.lc_lhs {Γ : Ctx} {A a b : Tm} (h : Ctx.JEq Γ A a b)
  : a.bvi = 0 := h.lc_all.2.2.1

theorem Ctx.JEq.lc_rhs {Γ : Ctx} {A a b : Tm} (h : Ctx.JEq Γ A a b)
  : b.bvi = 0 := h.lc_all.2.2.2

theorem Ctx.JEq.lhs_ok {Γ : Ctx} {ℓ : ℕ} {A B : Tm}
  (h : Ctx.JEq Γ (.univ ℓ) A B) {x : ℕ} (hx : x ∉ Γ.dv)
  : (Γ.cons x A).Ok := h.ok.cons hx h.lhs_ty

theorem Ctx.JEq.rhs_ok {Γ : Ctx} {ℓ : ℕ} {A B : Tm}
  (h : Ctx.JEq Γ (.univ ℓ) A B) {x : ℕ} (hx : x ∉ Γ.dv)
  : (Γ.cons x B).Ok := h.ok.cons hx h.rhs_ty

theorem Ctx.TyEq.ok {Γ : Ctx} {A B : Tm} (h : Γ.TyEq A B) : Γ.Ok := have ⟨_, h⟩ := h; h.ok

theorem Ctx.TyEq.not {Γ : Ctx} {A A' : Tm} (h : TyEq Γ A A')
  : JEq Γ (.univ 0) (.not A) (.not A')
  := have ⟨_, h⟩ := h; h.not

theorem Ctx.TyEq.not_ty {Γ : Ctx} {A A' : Tm} (h : TyEq Γ A A')
  : Γ.TyEq (.not A) (.not A') := ⟨0, h.not⟩

theorem Ctx.IsTy.ok {Γ : Ctx} {A : Tm} (h : Γ.IsTy A) : Γ.Ok := TyEq.ok h

theorem Ctx.IsTy.cons {Γ : Ctx} {A : Tm} (h : Γ.IsTy A) {x : ℕ} (hx : x ∉ Γ.dv)
  : (Γ.cons x A).Ok := h.ok.cons hx h

theorem Ctx.Ok.univ_ty {Γ : Ctx} (h : Γ.Ok) {ℓ : ℕ} : Γ.IsTy (.univ ℓ)
  := ⟨ℓ + 1, h.univ⟩

theorem Ctx.Ok.unit_ty {Γ : Ctx} (h : Γ.Ok) {ℓ : ℕ} : Γ.IsTy (.unit ℓ)
  := ⟨ℓ, h.unit⟩

theorem Ctx.Ok.empty_ty {Γ : Ctx} (h : Γ.Ok) {ℓ : ℕ} : Γ.IsTy (.empty ℓ)
  := ⟨ℓ, h.empty⟩

theorem Ctx.Ok.nats_ty {Γ : Ctx} (h : Γ.Ok) : Γ.IsTy .nats
  := ⟨1, h.nats⟩
