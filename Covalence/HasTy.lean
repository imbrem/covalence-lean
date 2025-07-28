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
  | sigma_cf {Γ : Ctx} {ℓ m n : ℕ} {A B : Tm} {L : Finset ℕ}
    : HasTy Γ (.univ m) A
    → (∀ x ∉ L, HasTy (Γ.cons x A) (.univ n) (B.bs0 (.fv x)))
    → (ℓ = m ⊔ n)
    → HasTy Γ (.univ ℓ) (.sigma A B)
  | pair_cf {Γ : Ctx} {m n : ℕ} {A B a b : Tm} {L : Finset ℕ}
    : HasTy Γ (.univ m) A
    → (∀ x ∉ L, HasTy (Γ.cons x A) (.univ n) (B.bs0 (.fv x)))
    → HasTy Γ A a
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

theorem Ctx.HasTy.wk0
  {Γ : Ctx} {A a : Tm} (h : Γ.HasTy A a)
  {x : ℕ} {B C : Tm} (hx : x ∉ Γ.dv) (hB : Γ.TyEq B C) : (Γ.cons x B).HasTy A a
  := h.wk (hB.lhs_pure_wk0 hx).wk

theorem Ctx.HasTy.to_cf_dv {Γ : Ctx} {A B a : Tm} (h : Γ.HasTy A a) (hB : Γ.IsTy B)
  : ∀x ∉ Γ.dv, (Γ.cons x B).HasTy (A.bs0 (.fv x)) (a.bs0 (.fv x))
  := fun x hx => by
    convert h.wk0 hx hB using 1
    · rw [Tm.bs0, Tm.bsubst_lc]; exact h.refl.lc_ty
    · rw [Tm.bs0, Tm.bsubst_lc]; exact h.refl.lc_lhs

theorem Ctx.HasTy.cast0
  {Γ : Ctx} {x : ℕ} {B C a : Tm} (h : (Γ.cons x B).HasTy C a)
  {A : Tm} (hB : Γ.TyEq A B) : (Γ.cons x A).HasTy C a
  := h.wk (hB.ok.wk.lift h.ok.var hB)

theorem Ctx.HasTy.pi_k {Γ : Ctx} {m n : ℕ} {A B : Tm}
  (hA : Γ.HasTy (.univ m) A) (hB : Γ.HasTy (.univ n) B)
  : Γ.HasTy (.univ (Nat.imax m n)) (.pi A B)
  := .pi_cf hA (hB.to_cf_dv hA.refl.ty_eq) rfl

theorem Ctx.HasTy.app_k {Γ : Ctx} {m n : ℕ} {A B f a : Tm}
  (hA : Γ.HasTy (.univ m) A) (hB : Γ.HasTy (.univ n) B)
  (hf : Γ.HasTy (.pi A B) f) (ha : Γ.HasTy A a)
  : Γ.HasTy B (.app A B f a)
  := .app_cf hA (hB.to_cf_dv hA.refl.ty_eq) hf ha (by
    convert hB.refl; rw [Tm.bs0, Tm.bsubst_lc]; exact hB.refl.lc_lhs)

theorem Ctx.HasTy.abs_k {Γ : Ctx} {m n : ℕ} {A B b : Tm}
  (hA : Γ.HasTy (.univ m) A) (hB : Γ.HasTy (.univ n) B) (hb : Γ.HasTy B b)
  : Γ.HasTy (.pi A B) (.abs A b)
  := .abs_cf hA (hB.to_cf_dv hA.refl.ty_eq) (hb.to_cf_dv hA.refl.ty_eq)

def Ctx.Cmp (Γ : Ctx) (A a b : Tm) : Prop := Γ.HasTy A a ∧ Γ.HasTy A b

theorem Ctx.Cmp.lhs_ty {Γ : Ctx} {A a b : Tm} (h : Γ.Cmp A a b) : Γ.HasTy A a := h.1

theorem Ctx.Cmp.rhs_ty {Γ : Ctx} {A a b : Tm} (h : Γ.Cmp A a b) : Γ.HasTy A b := h.2

theorem Ctx.HasTy.cmp {Γ : Ctx} {A a : Tm} (h : Γ.HasTy A a) : Γ.Cmp A a a := ⟨h, h⟩

theorem Ctx.Cmp.symm {Γ : Ctx} {A a b : Tm} (h : Γ.Cmp A a b) : Γ.Cmp A b a := ⟨h.2, h.1⟩

theorem Ctx.Cmp.trans {Γ : Ctx} {A a b c : Tm} (hab : Γ.Cmp A a b) (hbc : Γ.Cmp A b c)
  : Γ.Cmp A a c := ⟨hab.1, hbc.2⟩

theorem Ctx.Cmp.cast {Γ : Ctx} {A B a b : Tm} (h : Γ.Cmp A a b) (hAB : Γ.TyEq A B)
  : Γ.Cmp B a b := ⟨h.1.cast hAB, h.2.cast hAB⟩

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
  | univ | var | unit | nil | empty | nats | succ | explode =>
    constructor <;> constructor <;> (try apply ok) <;> assumption
  | eqn hA ha hb IA Ia Ib
    => exact ⟨IA.1.eqn Ia.1 Ib.1, IA.2.eqn (Ia.2.cast hA.ty_eq) (Ib.2.cast hA.ty_eq)⟩
  | pi_cf hA hB hℓ IA IB => exact ⟨
      IA.1.pi_cf (fun x hx => (IB x hx).1) hℓ,
      IA.2.pi_cf (fun x hx => (IB x hx).2.cast0 hA.ty_eq.symm) hℓ
    ⟩
  | app_cf hA hB hf ha hBa IA IB If Ia IBa => exact ⟨
      IA.1.app_cf (fun x hx => (IB x hx).1) If.1 Ia.1 hBa,
      (IA.2.app_cf (fun x hx => (IB x hx).2.cast0 hA.ty_eq.symm)
       (If.2.cast ⟨_, hA.pi_cf hB rfl⟩) (Ia.2.cast ⟨_, hA⟩)
                                        (.trans (.symm (.bs0_cf_univ hB ha)) hBa))
    ⟩
  | abs_cf hA hB hb IA IB Ib => exact ⟨
      IA.1.abs_cf (fun x hx => (IB x hx).1) (fun x hx => (Ib x hx).1),
      (IA.2.abs_cf
        (fun x hx => (IB x hx).2.cast0 hA.ty_eq.symm)
        (fun x hx => (Ib x hx).2.cast0 hA.ty_eq.symm)).cast
        ⟨_, .pi_cf hA.symm (fun x hx => (hB x hx).cast0 hA.ty_eq.symm) rfl⟩
    ⟩
  | sigma_cf hA hB hℓ IA IB => exact ⟨
      IA.1.sigma_cf (fun x hx => (IB x hx).1) hℓ,
      IA.2.sigma_cf (fun x hx => (IB x hx).2.cast0 hA.ty_eq.symm) hℓ
    ⟩
  | pair_cf hA hB ha hb IA IB Ia Ib => exact ⟨
      IA.1.pair_cf (fun x hx => (IB x hx).1) Ia.1 Ib.1,
      (IA.2.pair_cf
        (fun x hx => (IB x hx).2.cast0 hA.ty_eq.symm)
        (Ia.2.cast hA.ty_eq)
        (Ib.2.cast ⟨_, ha.bs0_cf_univ hB⟩)
        ).cast ⟨_, .symm (.sigma_cf hA hB rfl)⟩
      ⟩
  | fst_cf hA hB he IA IB Ie => exact ⟨
      IA.1.fst_cf (fun x hx => (IB x hx).1) Ie.1,
      (IA.2.fst_cf
        (fun x hx => (IB x hx).2.cast0 hA.ty_eq.symm)
        (Ie.2.cast ⟨_, .sigma_cf hA hB rfl⟩)).cast ⟨_, hA.symm⟩
    ⟩
  | snd_cf hA hB he hBa IA IB Ie IBa => exact ⟨
      IA.1.snd_cf (fun x hx => (IB x hx).1) Ie.1 hBa,
      (IA.2.snd_cf
        (fun x hx => (IB x hx).2.cast0 hA.ty_eq.symm)
        (Ie.2.cast ⟨_, .sigma_cf hA hB rfl⟩)
        (.trans (.symm (.bs0_cf_univ hB (.fst_cf hA hB he))) hBa))
      ⟩
  | dite_cf hφ hA ha hb Iφ IA Ia Ib => exact ⟨
      Iφ.1.dite_cf IA.1 (fun x hx => (Ia x hx).1) (fun x hx => (Ib x hx).1),
      (Iφ.2.dite_cf (L := _ ∪ _) IA.2
        (fun x hx => by
        simp at hx
        exact ((Ia x hx.1).2.cast0 ⟨_, hφ.symm⟩).cast ⟨_, hA.wk0 hx.2 ⟨_, hφ.symm⟩⟩)
        (fun x hx => by
        simp at hx
        exact ((Ib x hx.1).2.cast0 ⟨_, hφ.symm.not⟩).cast ⟨_, hA.wk0 hx.2 ⟨_, hφ.symm.not⟩⟩)
      ).cast ⟨_, hA.symm⟩
    ⟩
  | trunc hA IA => exact ⟨IA.1.trunc, IA.2.trunc⟩
  | choose_cf hA ht hφ IA It Iφ => exact ⟨
      IA.1.choose_cf ht (fun x hx => (Iφ x hx).1),
      (IA.2.choose_cf (hA.trunc.symm.trans ht)
        (fun x hx => (Iφ x hx).2.cast0 ⟨_, hA.symm⟩)).cast ⟨_, hA.symm⟩
    ⟩
  | natrec_cf hC hn hz hs hCn IC In Iz Is ICn =>
    rename Finset ℕ => L
    exact ⟨
    .natrec_cf (fun x hx => (IC x hx).1) In.1 Iz.1 (fun x hx => (Is x hx).1) hCn,
    .natrec_cf (L := L ∪ _)
      (fun x hx => by simp at hx; exact (IC x hx.1).2)
      In.2
      (Iz.2.cast ⟨_, hz.ok.zero.bs0_cf_univ hC⟩)
      (fun x hx => by
        simp at hx
        exact (Is x hx.1).2.cast ⟨_,
          .pi_k
            (hC x hx.1)
            (.bs0_cf_univ (L := {x} ∪ L)
              (fun y hy => by
                simp at hy
                apply (hC y hy.2).wk1 _ hCn.ok.nats_ty
                simp [Ne.symm hy.1]
                exact hx.2
                )
              (.app_k
                (hC x hx.1).ok.nats (hC x hx.1).ok.nats (.succ (hC x hx.1).ok.zero)
                (.var (hC x hx.1).ok.zero .here)
              ))
        ⟩)
      (.trans (.symm (.bs0_cf_univ hC hn)) hCn)
  ⟩
  | nil_uniq hA ha IA Ia =>
    exact ⟨Ia.lhs_ty, .cast ⟨_, .symm <| .prop_ext_true hA ha⟩ (.nil (ℓ := 0) ha.ok)⟩
  | eqn_rfl hA hab IA Iab => exact ⟨.eqn IA.1 Iab.1 Iab.2, .unit hab.ok⟩
  | beta_abs_cf _ _ _ _ hBa hba IA IB Ib Ia _ Iba =>
    exact ⟨.app_cf IA.1 (fun x hx => (IB x hx).1)
            (.abs_cf IA.1 (fun x hx => (IB x hx).1) (fun x hx => (Ib x hx).1)) Ia.1 hBa, Iba.2⟩
  | beta_fst_cf hA hB ha hb IA IB Ia Ib =>
    exact ⟨IA.1.fst_cf (fun x hx => (IB x hx).1)
            (.pair_cf IA.1 (fun x hx => (IB x hx).1) Ia.1 Ib.1), Ia.2
          ⟩
  | beta_snd_cf hA hB ha hb hBa IA IB Ia Ib Iba =>
    exact ⟨IA.1.snd_cf (fun x hx => (IB x hx).1)
            (.pair_cf IA.1 (fun x hx => (IB x hx).1) Ia.1 Ib.1)
            (.trans (.bs0_cf_univ hB (.beta_fst_cf hA hB ha hb)) hBa),
            Ib.1.cast hBa.ty_eq⟩
  | inhab hA ha IA Ia => exact ⟨.trunc IA.1, .unit hA.ok⟩
  | spec_cf hA ht hφ hφa IA It Iφ Iφa =>
    exact ⟨Iφa.2, .trunc (.sigma_cf IA.1 (fun x hx => (Iφ x hx).1) rfl)⟩
  | beta_true_cf hφ hA ha hb Iφ IA Ia Ib =>
    --TODO true substitution
    exact ⟨Iφ.1.dite_cf IA.1 (fun x hx => (Ia x hx).1) (fun x hx => (Ib x hx).1), sorry⟩
  | beta_false_cf hφ hA ha hb Iφ IA Ia Ib =>
    --TODO true substitution of false substitution
    exact ⟨Iφ.1.dite_cf IA.1 (fun x hx => (Ia x hx).1) (fun x hx => (Ib x hx).1), sorry⟩
  | beta_zero_cf hC hz hs hC0 IC Iz Is IC0 => exact ⟨
      .natrec_cf (fun x hx => (IC x hx).1) (.zero hz.ok) Iz.1 (fun x hx => (Is x hx).1) hC0,
      Iz.1.cast ⟨_, hC0⟩
    ⟩
  | beta_succ_cf hC hn hz hs hsn hCn hCs IC In Iz Is Isn ICn ICs => exact ⟨
      .natrec_cf  (fun x hx => (IC x hx).1)
                  (.app_k (.nats hz.ok) (.nats hz.ok) (.succ hz.ok) In.1) Iz.1
                  (fun x hx => (Is x hx).1) hCs,
      .app_k ICn.2 ICs.2 (Isn.2.cast ⟨_, .pi_k hCn hCs⟩)
        (.natrec_cf (fun x hx => (IC x hx).1) In.1 Iz.1 (fun x hx => (Is x hx).1) hCn)
    ⟩
  | eqn_ext hA ha hb he IA Ia Ib Ie => exact ⟨Ia.1, Ib.1⟩
  | pi_ext_cf hA hB hf hg hfg IA IB If Ig Ifg => exact ⟨If.1, Ig.1⟩
  | sigma_ext_cf hA hB he IA IB Ie => exact ⟨
      Ie.1, .pair_cf IA.1 (fun x hx => (IB x hx).1)
              (.fst_cf IA.1 (fun x hx => (IB x hx).1) Ie.1)
              (.snd_cf IA.1 (fun x hx => (IB x hx).1) Ie.1 (.bs0_cf_univ hB (.fst_cf hA hB he)))⟩
  | prop_ext hA hB hmp hmpr IA IB Imp Impr => exact ⟨IA.1, IB.1⟩
  | symm => apply Ctx.Cmp.symm; assumption
  | trans => apply Ctx.Cmp.trans <;> assumption
  | cast hA ha IA Ia => exact Ia.cast ⟨_, hA⟩

theorem Ctx.JEq.ty_lhs {Γ : Ctx} {A a b : Tm} (h : Ctx.JEq Γ A a b) : Γ.HasTy A a
  := h.cmp.1

theorem Ctx.JEq.ty_rhs {Γ : Ctx} {A a b : Tm} (h : Ctx.JEq Γ A a b) : Γ.HasTy A b
  := h.cmp.2

theorem Ctx.JEq.refl_iff (Γ : Ctx) (A a : Tm) : Γ.JEq A a a ↔ Γ.HasTy A a
  := ⟨Ctx.JEq.ty_lhs, Ctx.HasTy.refl⟩
