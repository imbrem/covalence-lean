import Covalence.Unique

inductive Ctx.Rw (Γ : Ctx) : Tm → Tm → Prop
  | fv (x : ℕ) : Rw Γ (.fv x) (.fv x)
  | bv (i : ℕ) : Rw Γ (.bv i) (.bv i)
  | univ (ℓ : ℕ) : Rw Γ (.univ ℓ) (.univ ℓ)
  | unit (ℓ : ℕ) : Rw Γ (.unit ℓ) (.unit ℓ)
  | nil (ℓ : ℕ) : Rw Γ (.nil ℓ) (.nil ℓ)
  | empty (ℓ : ℕ) : Rw Γ (.empty ℓ) (.empty ℓ)
  | eqn {A A' a a' b b' : Tm}
    : Rw Γ A A' → Rw Γ a a' → Rw Γ b b' → Rw Γ (.eqn A a b) (.eqn A' a' b')
  | pi {A A' B B' : Tm} : Rw Γ A A' → Rw Γ B B' → Rw Γ (.pi A B) (.pi A' B')
  | abs {A A' B B' b b' : Tm}
    : Rw Γ A A' → Rw Γ B B' → Rw Γ b b' → Rw Γ (.abs A B b) (.abs A' B' b')
  | app {A A' B B' f f' a a' : Tm}
    : Rw Γ A A' → Rw Γ B B' → Rw Γ f f' → Rw Γ a a' → Rw Γ (.app A B f a) (.app A' B' f' a')
  | sigma (ℓ : ℕ) {A A' B B' : Tm} : Rw Γ A A' → Rw Γ B B' → Rw Γ (.sigma ℓ A B) (.sigma ℓ A' B')
  | pair (ℓ : ℕ) {A A' B B' a a' b b' : Tm}
    : Rw Γ A A' → Rw Γ B B' → Rw Γ a a' → Rw Γ b b' → Rw Γ (.pair ℓ A B a b) (.pair ℓ A' B' a' b')
  | fst {A A' B B' a a' : Tm}
    : Rw Γ A A' → Rw Γ B B' → Rw Γ a a' → Rw Γ (.fst A B a) (.fst A' B' a')
  | snd {A A' B B' a a' : Tm}
    : Rw Γ A A' → Rw Γ B B' → Rw Γ a a' → Rw Γ (.snd A B a) (.snd A' B' a')
  | dite {φ φ' A A' a a' b b' : Tm}
    : Rw Γ φ φ' → Rw Γ A A' → Rw Γ a a' → Rw Γ b b' → Rw Γ (.dite φ A a b) (.dite φ' A' a' b')
  | trunc {A A' : Tm} : Rw Γ A A' → Rw Γ (.trunc A) (.trunc A')
  | choose {A A' φ φ' : Tm} : Rw Γ A A' → Rw Γ φ φ' → Rw Γ (.choose A φ) (.choose A' φ')
  | nats : Rw Γ .nats .nats
  | zero : Rw Γ .zero .zero
  | succ : Rw Γ .succ .succ
  | natrec {C C' n n' z z' s s' : Tm}
    : Rw Γ C C' → Rw Γ n n' → Rw Γ z z' → Rw Γ s s' → Rw Γ (.natrec C n z s) (.natrec C' n' z' s')
  | let₁ {A A' a a' b b' : Tm}
    : Rw Γ A A' → Rw Γ a a' → Rw Γ b b' → Rw Γ (.let₁ A a b) (.let₁ A' a' b')
  | invalid : Rw Γ .invalid .invalid
  | wf {a b : Tm} : Γ.WfEq a b → Rw Γ a b

@[simp]
theorem Ctx.Rw.refl {Γ : Ctx} {a : Tm} : Γ.Rw a a := by induction a <;> constructor <;> assumption

theorem Ctx.Rw.symm {Γ : Ctx} {a b : Tm} (h : Γ.Rw a b) : Γ.Rw b a := by
  induction h with
  | wf h => exact .wf h.symm
  | _ => constructor <;> assumption

theorem Ctx.Rw.bsubst (σ : Tm.BSubst) {Γ : Ctx} {a b : Tm} (h : Γ.Rw a b)
  : Γ.Rw (.bsubst σ a) (.bsubst σ b)
  := by induction h generalizing σ with
  | bv i => exact .refl
  | wf h =>
    convert Rw.wf h <;> rw [Tm.bsubst_lc]
    · exact h.lc_lhs
    · exact h.lc_rhs
  | _ => constructor <;> apply_assumption

theorem Ctx.Rw.bs0 (a : Tm) {Γ : Ctx} {b c : Tm} (h : Γ.Rw b c)
  : Γ.Rw (.bs0 b a) (.bs0 c a) := h.bsubst a.b0

theorem Ctx.Rw.wk0 {Γ : Ctx} {A a b : Tm} (h : Γ.Rw a b) {x} (hx : x ∉ Γ.dv) (hA : Γ.IsTy A)
  : (Γ.cons x A).Rw a b := by induction h with
  | wf h => exact .wf (h.wk0 hx hA)
  | _ => constructor <;> assumption

theorem Ctx.Rw.bind {Γ : Ctx} {A a b : Tm} (h : Γ.Rw a b) {x} (hx : x ∉ Γ.dv) (hA : Γ.IsTy A)
  : (Γ.cons x A).Rw (a.bs0 (.fv x)) (b.bs0 (.fv x)) := .bs0 _ (h.wk0 hx hA)

theorem Ctx.Rw.jeq {Γ : Ctx} {A a b : Tm} (h : Γ.Rw a b) (ha : Γ.HasTy A a) : Γ.JEq A a b
  := by
  induction ha generalizing b with
  | cast hA ha Ia => exact hA.cast (Ia h)
  | _ => cases h with
    | wf h => apply h.jeq; constructor <;> assumption
    | _ =>
      first
      | apply HasTy.refl; constructor <;> assumption
      | {
        constructor <;> first
        | apply_assumption <;> assumption
        | {
          rename Ctx => Γ
          rename Finset ℕ => L
          intro x hx
          have ⟨hL, hΓ⟩ : x ∉ L ∧ x ∉ Γ.dv := by rw [<-Finset.notMem_union]; exact hx
          apply_assumption
          · exact hL
          first | apply Rw.bind | apply Rw.wk0
          · assumption
          · exact hΓ
          · first | apply HasTy.regular ; assumption
                  | apply HasTy.is_ty; (try apply HasTy.not); assumption
        }
      }

theorem Ctx.Rw.to_wf {Γ : Ctx} {a b : Tm} (h : Γ.Rw a b) (ha : Γ.Wf a) : Γ.WfEq a b
  := have ⟨_, ha⟩ := ha.has_ty; ⟨_, h.jeq ha⟩

theorem Ctx.Rw.rw_wf {Γ : Ctx} {a b : Tm} (h : Γ.Rw a b) (ha : Γ.Wf a) : Γ.Wf b
  := have ⟨_, ha⟩ := ha.has_ty; ⟨_, (h.jeq ha).rhs⟩

theorem Ctx.Rw.rw_wf_iff {Γ : Ctx} {a b : Tm} (h : Γ.Rw a b) : Γ.Wf a ↔ Γ.Wf b
  := ⟨h.rw_wf, h.symm.rw_wf⟩

theorem Ctx.Rw.trans {Γ : Ctx} {a b c : Tm} (hab : Γ.Rw a b) (hbc : Γ.Rw b c) : Γ.Rw a c := by
  induction hab generalizing c with
  | wf hab => exact .wf (hab.trans (hbc.to_wf hab.rhs))
  | _ => cases hbc with
  | wf hbc =>
    exact .wf (.trans (.symm (Rw.to_wf (.symm (by constructor <;> assumption)) hbc.lhs)) hbc)
  | _ => constructor <;> apply_assumption <;> assumption
