import Covalence.JEq

-- NOPE: regularity requires _monosubstitution_

-- inductive Ctx.IsTy : Ctx → Tm → Prop
--   | univ {Γ : Ctx} {ℓ : ℕ} : Γ.Ok → IsTy Γ (.univ ℓ)
--   | unit {Γ : Ctx} {ℓ : ℕ} : Γ.Ok → IsTy Γ (.unit ℓ)
--   | empty {Γ : Ctx} {ℓ : ℕ} : Γ.Ok → IsTy Γ (.empty ℓ)
--   | eqn {Γ : Ctx} {A a b : Tm}
--     : IsTy Γ A → JEq Γ A a a → JEq Γ A b b → IsTy Γ (.eqn A a b)
--   | pi {Γ : Ctx} {A B : Tm} {L : Finset ℕ}
--     : IsTy Γ A → (∀ x ∉ L, IsTy (Γ.cons x A) (B.bs0 (.fv x))) → IsTy Γ (.pi A B)
--   | sigma {Γ : Ctx} {A B : Tm} {L : Finset ℕ}
--     : IsTy Γ A → (∀ x ∉ L, IsTy (Γ.cons x A) (B.bs0 (.fv x))) → IsTy Γ (.sigma A B)
--   | trunc {Γ : Ctx} {A : Tm} : IsTy Γ A → IsTy Γ (.trunc A)
--   | nats {Γ : Ctx} {ℓ : ℕ} : Γ.Ok → IsTy Γ .nats
--   | of_level {Γ : Ctx} {A : Tm} {ℓ : ℕ} : Γ.JEq (.univ ℓ) A A → IsTy Γ A

-- theorem Ctx.IsTy.level {Γ : Ctx} {A : Tm} (h : Γ.IsTy A) : ∃ ℓ, Γ.JEq (.univ ℓ) A A := by
--   induction h with
--   | univ hΓ => exact ⟨_, hΓ.univ⟩
--   | unit hΓ => exact ⟨_, hΓ.unit⟩
--   | empty hΓ => exact ⟨_, hΓ.empty⟩
--   | eqn _ ha hb IA => have ⟨_, IA⟩ := IA; exact ⟨_, IA.eqn ha hb⟩
--   | pi _ _ IA IB => sorry
--   | _ => sorry

-- theorem Ctx.IsTy.level_iff {Γ : Ctx} {A : Tm} : Γ.IsTy A ↔ ∃ ℓ, Γ.JEq (.univ ℓ) A A
--   := ⟨level, fun ⟨_, h⟩ => .of_level h⟩

-- -- def Ctx.IsTy (Γ : Ctx) (A : Tm) : Prop := ∃ ℓ, Γ.JEq (.univ ℓ) A A

-- -- theorem Ctx.IsTy.univ {Γ : Ctx} {ℓ : ℕ} (hΓ : Γ.Ok) : Γ.IsTy (.univ ℓ) := ⟨_, hΓ.univ⟩

-- -- theorem Ctx.IsTy.unit {Γ : Ctx} {ℓ : ℕ} (hΓ : Γ.Ok) : Γ.IsTy (.unit ℓ) := ⟨_, hΓ.unit⟩

-- -- theorem Ctx.IsTy.empty {Γ : Ctx} {ℓ : ℕ} (hΓ : Γ.Ok) : Γ.IsTy (.empty ℓ) := ⟨_, hΓ.empty⟩

-- theorem Ctx.JEq.regular {Γ : Ctx} {A a b : Tm} (h : Γ.JEq A a b) : Γ.IsTy A := by
--   sorry
