import Covalence.Factor

inductive Ctx.MaybeSubsort : Ctx → ℕ → Tm → Prop
  | var {Γ : Ctx} {x : ℕ} {A : Tm} {ℓ : ℕ}
    : Γ.NoRep → Γ.At x A → MaybeSubsort Γ (ℓ + 1) A → MaybeSubsort Γ ℓ (.fv x)
  | univ {Γ : Ctx} {ℓ : ℕ} : MaybeSubsort Γ (ℓ + 2) (.univ ℓ)
  | unit {Γ : Ctx} {ℓ : ℕ} : MaybeSubsort Γ (ℓ + 1) (.unit ℓ)
  | nil {Γ : Ctx} {ℓ : ℕ} : MaybeSubsort Γ ℓ (.nil ℓ)
  | empty {Γ : Ctx} {ℓ : ℕ} : MaybeSubsort Γ (ℓ + 1) (.empty ℓ)
  | eqn {Γ : Ctx} {A a b : Tm} {ℓ : ℕ}
    :
    -- MaybeSubsort Γ ℓ a → MaybeSubsort Γ ℓ b →
    MaybeSubsort Γ 1 (.eqn A a b)
  | pi {Γ : Ctx} {A B : Tm} {ℓ m n : ℕ} {L : Finset ℕ}
    : MaybeSubsort Γ (m + 1) A
    → (∀x ∉ L, MaybeSubsort (Γ.cons x A) (n + 1) (B.bs0 (.fv x)))
    → (hℓ : ℓ = m.imax n) → MaybeSubsort Γ (ℓ + 1) (.pi A B)
  | abs {Γ : Ctx} {A B b : Tm} {ℓ m n : ℕ} {L : Finset ℕ}
    : MaybeSubsort Γ (m + 1) A
    → (∀x ∉ L, MaybeSubsort (Γ.cons x A) (n + 1) (B.bs0 (.fv x)))
    → (hℓ : ℓ = m.imax n)
    → MaybeSubsort Γ ℓ (.abs A B b)
  | app {Γ : Ctx} {A B f a : Tm} {m n : ℕ} {L : Finset ℕ}
    : MaybeSubsort Γ (m + 1) A
    → (∀x ∉ L, MaybeSubsort (Γ.cons x A) (n + 1) (B.bs0 (.fv x)))
    → MaybeSubsort Γ n (.app A B f a)
  | sigma {Γ : Ctx} {ℓ : ℕ} {A B : Tm} {m n : ℕ} {L : Finset ℕ}
    : MaybeSubsort Γ (m + 1) A
    → (∀x ∉ L, MaybeSubsort (Γ.cons x A) (n + 1) (B.bs0 (.fv x)))
    → (hℓ : ℓ = m ⊔ n)
    → MaybeSubsort Γ (ℓ + 1) (.sigma A B)
  | pair {Γ : Ctx} {ℓ : ℕ} {A B a b : Tm} {m n : ℕ} {L : Finset ℕ}
    : MaybeSubsort Γ (m + 1) A
    → (∀x ∉ L, MaybeSubsort (Γ.cons x A) (n + 1) (B.bs0 (.fv x)))
    → (hℓ : ℓ = m ⊔ n)
    → MaybeSubsort Γ ℓ (.pair A B a b)
  | fst {Γ : Ctx} {A B a : Tm} {m : ℕ}
    : MaybeSubsort Γ (m + 1) A → MaybeSubsort Γ m (.fst A B a)
  | snd {Γ : Ctx} {A B a : Tm} {m n : ℕ} {L : Finset ℕ}
    : MaybeSubsort Γ (m + 1) A
    → (∀x ∉ L, MaybeSubsort (Γ.cons x A) (n + 1) (B.bs0 (.fv x)))
    → MaybeSubsort Γ n (.snd A B a)
  | dite {Γ : Ctx} {φ A a b : Tm} {ℓ : ℕ}
    : MaybeSubsort Γ (ℓ + 1) A → MaybeSubsort Γ ℓ (.dite φ A a b)
  | trunc {Γ : Ctx} {A : Tm} : MaybeSubsort Γ 1 (.trunc A)
  | choose {Γ : Ctx} {A φ : Tm} {ℓ : ℕ} : MaybeSubsort Γ (ℓ + 1) A → MaybeSubsort Γ ℓ (.choose A φ)
  | nats {Γ : Ctx} : MaybeSubsort Γ 2 .nats
  | zero {Γ : Ctx} : MaybeSubsort Γ 1 .zero
  | succ {Γ : Ctx} : MaybeSubsort Γ 1 .succ
  | natrec {Γ : Ctx} {C n z s : Tm} {ℓ : ℕ} {L : Finset ℕ}
    : (∀x ∉ L, MaybeSubsort (Γ.cons x .nats) (ℓ + 1) (C.bs0 (.fv x)))
    → MaybeSubsort Γ ℓ (.natrec C n z s)

theorem Ctx.MaybeSubsort.sub_map {Γ Δ : Ctx} (hΓΔ : Γ.SubMap Δ) {a : Tm} {ℓ : ℕ}
  (h : Δ.MaybeSubsort ℓ a) : Γ.MaybeSubsort ℓ a
  := by induction h generalizing Γ with
  | var _ hx hA IA => exact .var hΓΔ.src_no_rep (hΓΔ.at hx) (IA hΓΔ)
  | _ =>
    constructor <;>
    first
    | apply_assumption <;> assumption
    | {
      rename Finset ℕ => L
      intro x hx
      have ⟨hΓ, hL⟩ : x ∉ Γ.dv ∧ x ∉ L := by simp only [<-Finset.notMem_union]; exact hx
      simp only [Finset.mem_union, not_or] at hx
      apply_assumption
      · exact hL
      · apply hΓΔ.lift hΓ
    }

theorem Ctx.MaybeSubsort.pure_str {Γ Δ : Ctx} (hΓΔ : Γ.SubScope Δ) {a : Tm} {ℓ : ℕ}
  (h : Γ.MaybeSubsort ℓ a) (ha : a.fvs ⊆ Δ.dv) : Δ.MaybeSubsort ℓ a
  := by induction h generalizing Δ with
  | var _ hx hA IA =>
    exact .var
      hΓΔ.sub_map.trg_no_rep (hΓΔ.sub_map.at_anti (by convert ha; simp) hx)
      (IA hΓΔ (hΓΔ.at_sub_anti (by convert ha; simp) hx))
  | _ =>
    (try simp only [Tm.fvs, Finset.union_subset_iff] at ha)
    constructor <;>
    first
    | apply_assumption <;> first | assumption | simp [ha]
    | {
      rename Finset ℕ => L
      intro x hx
      have ⟨hΓ, hL⟩ : x ∉ hΓΔ.src.dv ∧ x ∉ L := by simp only [<-Finset.notMem_union]; exact hx
      simp only [Finset.mem_union, not_or] at hx
      apply_assumption
      · exact hL
      · apply hΓΔ.lift hΓ (by simp [ha])
      · apply Tm.bs0_fv_sub (Finset.Subset.trans _ Finset.subset_union_right) <;> simp [ha]
      }

@[simp]
theorem Ctx.MaybeSubsort.univ_iff {Γ : Ctx} {ℓ ℓ' : ℕ} :
  MaybeSubsort Γ ℓ (.univ ℓ') ↔ ℓ = ℓ' + 2
  := by constructor <;> intro h <;> cases h <;> constructor

@[simp]
theorem Ctx.MaybeSubsort.unit_iff {Γ : Ctx} {ℓ ℓ' : ℕ} :
  MaybeSubsort Γ ℓ (.unit ℓ') ↔ ℓ = ℓ' + 1
  := by constructor <;> intro h <;> cases h <;> constructor

@[simp]
theorem Ctx.MaybeSubsort.nil_iff {Γ : Ctx} {ℓ ℓ' : ℕ} :
  MaybeSubsort Γ ℓ (.nil ℓ') ↔ ℓ = ℓ'
  := by constructor <;> intro h <;> cases h <;> constructor

@[simp]
theorem Ctx.MaybeSubsort.empty_iff {Γ : Ctx} {ℓ ℓ' : ℕ} :
  MaybeSubsort Γ ℓ (.empty ℓ') ↔ ℓ = ℓ' + 1
  := by constructor <;> intro h <;> cases h <;> constructor

@[simp]
theorem Ctx.MaybeSubsort.fst_iff {Γ : Ctx} {A B a : Tm} {m : ℕ} :
  MaybeSubsort Γ m (.fst A B a) ↔ MaybeSubsort Γ (m + 1) A
  := ⟨fun h => by cases h; assumption, fun h => .fst h⟩

@[simp]
theorem Ctx.MaybeSubsort.dite_iff {Γ : Ctx} {φ A a b : Tm} {ℓ : ℕ} :
  MaybeSubsort Γ ℓ (.dite φ A a b) ↔ MaybeSubsort Γ (ℓ + 1) A
  := ⟨fun h => by cases h; assumption, fun h => .dite h⟩

@[simp]
theorem Ctx.MaybeSupport.trunc_iff {Γ : Ctx} {A : Tm} {ℓ : ℕ} :
  MaybeSubsort Γ ℓ (.trunc A) ↔ ℓ = 1
  := by constructor <;> intro h <;> cases h <;> constructor

@[simp]
theorem Ctx.MaybeSubsort.choose_iff {Γ : Ctx} {A φ : Tm} {ℓ : ℕ} :
  MaybeSubsort Γ ℓ (.choose A φ) ↔ MaybeSubsort Γ (ℓ + 1) A
  := ⟨fun h => by cases h; assumption, fun h => .choose h⟩

@[simp]
theorem Ctx.MaybeSubsort.nats_iff {Γ : Ctx} {ℓ : ℕ} :
  MaybeSubsort Γ ℓ .nats ↔ ℓ = 2
  := by constructor <;> intro h <;> cases h <;> constructor

@[simp]
theorem Ctx.MaybeSubsort.zero_iff {Γ : Ctx} {ℓ : ℕ} :
  MaybeSubsort Γ ℓ .zero ↔ ℓ = 1
  := by constructor <;> intro h <;> cases h <;> constructor

@[simp]
theorem Ctx.MaybeSubsort.succ_iff {Γ : Ctx} {ℓ : ℕ} :
  MaybeSubsort Γ ℓ .succ ↔ ℓ = 1
  := by constructor <;> intro h <;> cases h <;> constructor

theorem Ctx.MaybeSubsort.unique {Γ : Ctx} {a : Tm} {m n : ℕ}
  (ha : MaybeSubsort Γ m a) (ha' : MaybeSubsort Γ n a) : m = n := by
  induction ha generalizing n with
  | var hΓ hx hA IA => cases ha' with | var  _ hx' hA' =>
    cases hΓ.at_eq hx hx'; have IA := IA hA'; omega
  | pi hA hB hℓ IA IB =>
    rename Finset ℕ => L
    cases hℓ
    cases ha' with | pi hA' hB' hℓ =>
    rename Finset ℕ => L'
    cases hℓ
    have ⟨x, hx⟩ := Finset.exists_notMem (L ∪ L');
    have IA := IA hA'
    have hBx := hB x (by simp at hx; exact hx.left);
    have hBx' := hB' x (by simp at hx; exact hx.right);
    have IBx := IB x (by simp at hx; exact hx.left) hBx'
    cases IA; cases IBx; rfl
  | app hA hB IA IB =>
    rename Finset ℕ => L
    cases ha' with | app hA' hB' =>
    rename Finset ℕ => L'
    have ⟨x, hx⟩ := Finset.exists_notMem (L ∪ L');
    have hBx := hB x (by simp at hx; exact hx.left);
    have hBx' := hB' x (by simp at hx; exact hx.right);
    have IBx := IB x (by simp at hx; exact hx.left) hBx'
    cases IBx; rfl
  | abs hA hB hℓ IA IB =>
    rename Finset ℕ => L
    cases hℓ
    cases ha' with | abs hA' hB' hℓ =>
    rename Finset ℕ => L'
    cases hℓ
    have ⟨x, hx⟩ := Finset.exists_notMem (L ∪ L');
    have IA := IA hA'
    have hBx := hB x (by simp at hx; exact hx.left);
    have hBx' := hB' x (by simp at hx; exact hx.right);
    have IBx := IB x (by simp at hx; exact hx.left) hBx'
    cases IA; cases IBx; rfl
  | sigma hA hB hℓ IA IB =>
    rename Finset ℕ => L
    cases hℓ
    cases ha' with | sigma hA' hB' hℓ =>
    rename Finset ℕ => L'
    cases hℓ
    have ⟨x, hx⟩ := Finset.exists_notMem (L ∪ L');
    have IA := IA hA'
    have hBx := hB x (by simp at hx; exact hx.left);
    have hBx' := hB' x (by simp at hx; exact hx.right);
    have IBx := IB x (by simp at hx; exact hx.left) hBx'
    cases IA; cases IBx; rfl
  | pair hA hB hℓ IA IB =>
    rename Finset ℕ => L
    cases hℓ
    cases ha' with | pair hA' hB' hℓ =>
    rename Finset ℕ => L'
    cases hℓ
    have ⟨x, hx⟩ := Finset.exists_notMem (L ∪ L');
    have IA := IA hA'
    have hBx := hB x (by simp at hx; exact hx.left);
    have hBx' := hB' x (by simp at hx; exact hx.right);
    have IBx := IB x (by simp at hx; exact hx.left) hBx'
    cases IA; cases IBx; rfl
  | fst hA IA => cases ha' with | fst hA' => cases IA hA'; rfl
  | snd hA hB IA IB =>
    rename Finset ℕ => L
    cases ha' with | snd hA' hB' =>
    rename Finset ℕ => L'
    have ⟨x, hx⟩ := Finset.exists_notMem (L ∪ L');
    have hBx := hB x (by simp at hx; exact hx.left);
    have hBx' := hB' x (by simp at hx; exact hx.right);
    have IBx := IB x (by simp at hx; exact hx.left) hBx'
    cases IBx; rfl
  | dite hA IA => cases ha' with | dite hA' => cases IA hA'; rfl
  | choose hA IA => cases ha' with | choose hA' => cases IA hA'; rfl
  | natrec hC IC =>
    rename Finset ℕ => L
    cases ha' with | natrec hC' =>
    rename Finset ℕ => L'
    have ⟨x, hx⟩ := Finset.exists_notMem (L ∪ L');
    have hCx := hC x (by simp at hx; exact hx.left);
    have hCx' := hC' x (by simp at hx; exact hx.right);
    have ICx := IC x (by simp at hx; exact hx.left) hCx'
    cases ICx; rfl
  | _ => cases ha'; rfl

def Ctx.HasTy.ctx {Γ : Ctx} {a A : Tm} (_ : Γ ⊢ a : A) : Ctx := Γ

inductive Ctx.OkTy : Ctx → Tm → Tm → Prop
  | univ {Γ : Ctx} {ℓ : ℕ} : Γ.Ok → OkTy Γ (.univ (ℓ + 1)) (.univ ℓ)
  | var {Γ : Ctx} {x : ℕ} {A : Tm} {ℓ : ℕ}
    : OkTy Γ (.univ ℓ) A → Γ.At x A → OkTy Γ A (.fv x)
  | unit {Γ : Ctx} {ℓ : ℕ} : Γ.Ok → OkTy Γ (.univ ℓ) (.unit ℓ)
  | nil {Γ : Ctx} {ℓ : ℕ} : Γ.Ok → OkTy Γ (.unit ℓ) (.nil ℓ)
  | empty {Γ : Ctx} {ℓ : ℕ} : Γ.Ok → OkTy Γ (.univ ℓ) (.empty ℓ)
  | eqn {Γ : Ctx} {ℓ : ℕ} {A a b : Tm}
    : OkTy Γ (.univ ℓ) A
    → OkTy Γ A a
    → OkTy Γ A b
    → OkTy Γ (.univ 0) (.eqn A a b)
  | pi_cf {Γ : Ctx} {ℓ m n : ℕ} {A B : Tm} {L : Finset ℕ}
    : OkTy Γ (.univ m) A
    → (∀ x ∉ L, OkTy (Γ.cons x A) (.univ n) (B.bs0 (.fv x)))
    → (ℓ = m.imax n)
    → OkTy Γ (.univ ℓ) (.pi A B)
  | app_cf {Γ : Ctx} {m n : ℕ} {A B Ba f a : Tm} {L : Finset ℕ}
    : OkTy Γ (.univ m) A
    → (∀ x ∉ L, OkTy (Γ.cons x A) (.univ n) (B.bs0 (.fv x)))
    → OkTy Γ (.pi A B) f
    → OkTy Γ A a
    → JEq Γ (.univ n) (B.bs0 a) Ba
    → OkTy Γ Ba (.app A B f a)
  | abs_cf {Γ : Ctx} {m n : ℕ} {A B b : Tm} {L : Finset ℕ}
    : OkTy Γ (.univ m) A
    → (∀ x ∉ L, OkTy (Γ.cons x A) (.univ n) (B.bs0 (.fv x)))
    → (∀ x ∉ L, OkTy (Γ.cons x A) (B.bs0 (.fv x)) (b.bs0 (.fv x)))
    → OkTy Γ (.pi A B) (.abs A B b)
  | sigma_cf {Γ : Ctx} {ℓ m n : ℕ} {A B : Tm} {L : Finset ℕ}
    : OkTy Γ (.univ m) A
    → (∀ x ∉ L, OkTy (Γ.cons x A) (.univ n) (B.bs0 (.fv x)))
    → (ℓ = m ⊔ n)
    → OkTy Γ (.univ ℓ) (.sigma A B)
  | pair_cf {Γ : Ctx} {m n : ℕ} {A B a b : Tm} {L : Finset ℕ}
    : OkTy Γ (.univ m) A
    → (∀ x ∉ L, OkTy (Γ.cons x A) (.univ n) (B.bs0 (.fv x)))
    → OkTy Γ A a
    → OkTy Γ (B.bs0 a) b
    → OkTy Γ (.sigma A B) (.pair A B a b)
  | fst_cf {Γ : Ctx} {m n : ℕ} {A B e : Tm} {L : Finset ℕ}
    : OkTy Γ (.univ m) A
    → (∀ x ∉ L, OkTy (Γ.cons x A) (.univ n) (B.bs0 (.fv x)))
    → OkTy Γ (.sigma A B) e
    → OkTy Γ A (.fst A B e)
  | snd_cf {Γ : Ctx} {m n : ℕ} {A B Ba e : Tm} {L : Finset ℕ}
    : OkTy Γ (.univ m) A
    → (∀ x ∉ L, OkTy (Γ.cons x A) (.univ n) (B.bs0 (.fv x)))
    → OkTy Γ (.sigma A B) e
    → JEq Γ (.univ n) (B.bs0 (.fst A B e)) Ba
    → OkTy Γ Ba (.snd A B e)
  | dite_cf {Γ : Ctx} {ℓ : ℕ} {φ A a b : Tm} {L : Finset ℕ}
    : OkTy Γ (.univ 0) φ
    → OkTy Γ (.univ ℓ) A
    → (∀ x ∉ L, OkTy (Γ.cons x φ) A a)
    → (∀ x ∉ L, OkTy (Γ.cons x (.not φ)) A b)
    → OkTy Γ A (.dite φ A a b)
  | trunc {Γ : Ctx} {ℓ : ℕ} {A : Tm}
    : OkTy Γ (.univ ℓ) A
    → OkTy Γ (.univ 0) (.trunc A)
  | choose_cf {Γ : Ctx} {ℓ} {A φ : Tm} {L : Finset ℕ}
    : OkTy Γ (.univ ℓ) A
    → JEq Γ (.univ 0) (.trunc A) (.unit 0)
    → (∀ x ∉ L, OkTy (Γ.cons x A) (.univ 0) (φ.bs0 (.fv x)))
    → OkTy Γ A (.choose A φ)
  | nats {Γ : Ctx} : Γ.Ok → OkTy Γ (.univ 1) .nats
  | zero {Γ : Ctx} : Γ.Ok → OkTy Γ .nats .zero
  | succ {Γ : Ctx} : Γ.Ok → OkTy Γ (.pi .nats .nats) .succ
  | natrec_cf {Γ : Ctx} {ℓ : ℕ} {C n z s Cn : Tm} {L : Finset ℕ}
    : (∀ x ∉ L, OkTy (Γ.cons x .nats) (.univ ℓ) (C.bs0 (.fv x)))
    → OkTy Γ .nats n
    → OkTy Γ (C.bs0 .zero) z
    → (∀ x ∉ L,
        OkTy (Γ.cons x .nats) (.pi (C.bs0 (.fv x))
              (C.bs0 (.app .nats .nats .succ (.fv x)))) (s.bs0 (.fv x)))
    → JEq Γ (.univ ℓ) (C.bs0 n) Cn
    → OkTy Γ Cn (.natrec C n z s)
  | cast {Γ : Ctx} {A B a : Tm}
    : TyEq Γ A B
    → OkTy Γ A a
    → OkTy Γ B a

-- theorem Ctx.OkTy.has_ty {Γ : Ctx} {A a : Tm}
--   (ha : OkTy Γ A a) : Γ ⊢ a : A := by induction ha <;> constructor <;> assumption

inductive Ctx.NestTy : Ctx → Tm → Tm → Prop
  | univ {Γ : Ctx} {ℓ : ℕ} : Γ.Ok → NestTy Γ (.univ (ℓ + 1)) (.univ ℓ)
  | var {Γ : Ctx} {x : ℕ} {A : Tm} {ℓ : ℕ}
    : Γ.Ok → Γ.At x A → NestTy Γ (.univ ℓ) A → NestTy Γ A (.fv x)
  | unit {Γ : Ctx} {ℓ : ℕ} : Γ.Ok → NestTy Γ (.univ ℓ) (.unit ℓ)
  | nil {Γ : Ctx} {ℓ : ℕ} : Γ.Ok → NestTy Γ (.unit ℓ) (.nil ℓ)
  | empty {Γ : Ctx} {ℓ : ℕ} : Γ.Ok → NestTy Γ (.univ ℓ) (.empty ℓ)
  | eqn {Γ : Ctx} {ℓ : ℕ} {A a b : Tm}
    : NestTy Γ (.univ ℓ) A
    → NestTy Γ A a
    → NestTy Γ A b
    → NestTy Γ (.univ 0) (.eqn A a b)
  | pi_cf {Γ : Ctx} {ℓ m n : ℕ} {A B : Tm} {L : Finset ℕ}
    : NestTy Γ (.univ m) A
    → (∀ x ∉ L, NestTy (Γ.cons x A) (.univ n) (B.bs0 (.fv x)))
    → (ℓ = m.imax n)
    → NestTy Γ (.univ ℓ) (.pi A B)
  | app_cf {Γ : Ctx} {m n : ℕ} {A B Ba f a : Tm} {L : Finset ℕ}
    : NestTy Γ (.univ m) A
    → (∀ x ∉ L, NestTy (Γ.cons x A) (.univ n) (B.bs0 (.fv x)))
    → NestTy Γ (.pi A B) f
    → NestTy Γ A a
    → JEq Γ (.univ n) (B.bs0 a) Ba
    → NestTy Γ Ba (.app A B f a)
  | abs_cf {Γ : Ctx} {m n : ℕ} {A B b : Tm} {L : Finset ℕ}
    : NestTy Γ (.univ m) A
    → (∀ x ∉ L, NestTy (Γ.cons x A) (.univ n) (B.bs0 (.fv x)))
    → (∀ x ∉ L, NestTy (Γ.cons x A) (B.bs0 (.fv x)) (b.bs0 (.fv x)))
    → NestTy Γ (.pi A B) (.abs A B b)
  | sigma_cf {Γ : Ctx} {ℓ m n : ℕ} {A B : Tm} {L : Finset ℕ}
    : NestTy Γ (.univ m) A
    → (∀ x ∉ L, NestTy (Γ.cons x A) (.univ n) (B.bs0 (.fv x)))
    → (ℓ = m ⊔ n)
    → NestTy Γ (.univ ℓ) (.sigma A B)
  | pair_cf {Γ : Ctx} {m n : ℕ} {A B a b : Tm} {L : Finset ℕ}
    : NestTy Γ (.univ m) A
    → (∀ x ∉ L, NestTy (Γ.cons x A) (.univ n) (B.bs0 (.fv x)))
    → NestTy Γ A a
    → NestTy Γ (B.bs0 a) b
    → NestTy Γ (.sigma A B) (.pair A B a b)
  | fst_cf {Γ : Ctx} {m n : ℕ} {A B e : Tm} {L : Finset ℕ}
    : NestTy Γ (.univ m) A
    → (∀ x ∉ L, NestTy (Γ.cons x A) (.univ n) (B.bs0 (.fv x)))
    → NestTy Γ (.sigma A B) e
    → NestTy Γ A (.fst A B e)
  | snd_cf {Γ : Ctx} {m n : ℕ} {A B Ba e : Tm} {L : Finset ℕ}
    : NestTy Γ (.univ m) A
    → (∀ x ∉ L, NestTy (Γ.cons x A) (.univ n) (B.bs0 (.fv x)))
    → NestTy Γ (.sigma A B) e
    → JEq Γ (.univ n) (B.bs0 (.fst A B e)) Ba
    → NestTy Γ Ba (.snd A B e)
  | dite_cf {Γ : Ctx} {ℓ : ℕ} {φ A a b : Tm} {L : Finset ℕ}
    : NestTy Γ (.univ 0) φ
    → NestTy Γ (.univ ℓ) A
    → (∀ x ∉ L, NestTy (Γ.cons x φ) A a)
    → (∀ x ∉ L, NestTy (Γ.cons x (.not φ)) A b)
    → NestTy Γ A (.dite φ A a b)
  | trunc {Γ : Ctx} {ℓ : ℕ} {A : Tm}
    : NestTy Γ (.univ ℓ) A
    → NestTy Γ (.univ 0) (.trunc A)
  | choose_cf {Γ : Ctx} {ℓ} {A φ : Tm} {L : Finset ℕ}
    : NestTy Γ (.univ ℓ) A
    → JEq Γ (.univ 0) (.trunc A) (.unit 0)
    → (∀ x ∉ L, NestTy (Γ.cons x A) (.univ 0) (φ.bs0 (.fv x)))
    → NestTy Γ A (.choose A φ)
  | nats {Γ : Ctx} : Γ.Ok → NestTy Γ (.univ 1) .nats
  | zero {Γ : Ctx} : Γ.Ok → NestTy Γ .nats .zero
  | succ {Γ : Ctx} : Γ.Ok → NestTy Γ (.pi .nats .nats) .succ
  | natrec_cf {Γ : Ctx} {ℓ : ℕ} {C n z s Cn : Tm} {L : Finset ℕ}
    : (∀ x ∉ L, NestTy (Γ.cons x .nats) (.univ ℓ) (C.bs0 (.fv x)))
    → NestTy Γ .nats n
    → NestTy Γ (C.bs0 .zero) z
    → (∀ x ∉ L,
        NestTy (Γ.cons x .nats) (.pi (C.bs0 (.fv x))
              (C.bs0 (.app .nats .nats .succ (.fv x)))) (s.bs0 (.fv x)))
    → JEq Γ (.univ ℓ) (C.bs0 n) Cn
    → NestTy Γ Cn (.natrec C n z s)
  | cast {Γ : Ctx} {A B a : Tm}
    : TyEq Γ A B
    → NestTy Γ A a
    → NestTy Γ B a

theorem Ctx.HasTy.nest_ty {Γ : Ctx} {A a : Tm} (ha : Γ ⊢ a : A) :
  OkTy Γ A a := by induction ha with
  | var hx hA => sorry
  | _ => constructor <;> assumption

-- theorem Ctx.HasTy.maybe_subsort {Γ : Ctx} {A a : Tm} {ℓ : ℕ}
--   (ha : Γ ⊢ a : A) (hA : Γ ⊢ A : .univ ℓ) : Γ.MaybeSubsort ℓ a := by
--   induction ha generalizing ℓ with
--   | var hΓ ha =>

--     sorry
--   | _ => sorry

def Ctx.MaybeCmp (Γ : Ctx) (ℓ : ℕ) (a b : Tm) : Prop :=
  MaybeSubsort Γ ℓ a ∧ MaybeSubsort Γ ℓ b

theorem Ctx.MaybeSubsort.refl {Γ : Ctx} {ℓ : ℕ} {a : Tm} (h : MaybeSubsort Γ ℓ a) :
  Ctx.MaybeCmp Γ ℓ a a := ⟨h, h⟩

theorem Ctx.MaybeCmp.symm {Γ : Ctx} {ℓ : ℕ} {a b : Tm}
  (h : Ctx.MaybeCmp Γ ℓ a b) : Ctx.MaybeCmp Γ ℓ b a :=
  ⟨h.2, h.1⟩

theorem Ctx.MaybeCmp.trans {Γ : Ctx} {ℓ : ℕ} {a b c : Tm}
  (h₁ : Ctx.MaybeCmp Γ ℓ a b) (h₂ : Ctx.MaybeCmp Γ ℓ b c)
  : Ctx.MaybeCmp Γ ℓ a c := ⟨h₁.1, h₂.2⟩

theorem Ctx.MaybeCmp.sub_map {Γ Δ : Ctx} (hΓΔ : Γ.SubMap Δ) {ℓ : ℕ} {a b : Tm}
  (h : Ctx.MaybeCmp Δ ℓ a b) : Ctx.MaybeCmp Γ ℓ a b :=
  ⟨h.1.sub_map hΓΔ, h.2.sub_map hΓΔ⟩

theorem Ctx.MaybeCmp.pure_str {Γ Δ : Ctx} (hΓΔ : Γ.SubScope Δ) {ℓ : ℕ} {a b : Tm}
  (h : Ctx.MaybeCmp Γ ℓ a b) (ha : a.fvs ⊆ Δ.dv) (hb : b.fvs ⊆ Δ.dv)
  : Ctx.MaybeCmp Δ ℓ a b :=
  ⟨h.1.pure_str hΓΔ ha, h.2.pure_str hΓΔ hb⟩

theorem Ctx.MaybeCmp.fuse {Γ : Ctx} {ℓ : ℕ} {a : Tm}
  (h : Ctx.MaybeCmp Γ ℓ a a) : Γ.MaybeSubsort ℓ a := h.left

-- theorem Ctx.JEq.maybe_cmp {Γ : Ctx} {A a b : Tm} (hab : Γ.JEq A a b) {ℓ : ℕ}
--   (hA : Γ.HasTy (.univ ℓ) A) : Ctx.MaybeCmp Γ ℓ a b := by
--   induction hab generalizing ℓ with
--   | beta_true_cf hφ hA' hl hr Iφ IA' Il Ir =>
--     rename Finset ℕ => L
--     have ⟨x, hx⟩ := Finset.exists_notMem (hA.ctx.dv ∪ L);
--     simp only [Finset.mem_union, not_or] at hx
--     have Il := Il x hx.right (hA.wk0 hx.left hφ.ty_eq)
--     constructor
--     · constructor; apply MaybeCmp.fuse; apply_assumption; apply HasTy.cast
--       · sorry
--       · constructor; exact hA.ok
--     · sorry
--   | _ => sorry

-- theorem Ctx.MaybeSubsort.jeq_univ {Γ : Ctx} {A a b : Tm} {ℓ : ℕ}
--   (ha : Γ.MaybeSubsort ℓ a) (hb : Γ.MaybeSubsort ℓ b) (hab : Γ.JEq A a b)
--   : Γ.HasTy (.univ ℓ) A
--   := by induction hab generalizing ℓ with
--   | univ | unit | nil | empty | eqn | explode | eqn_rfl | inhab | nats
--     => cases ha; constructor; apply JEq.ok; assumption
--   | nil_uniq | eqn_ext
--     => apply_assumption <;> assumption
--   | spec_cf =>
--     cases hb; constructor; apply JEq.ok; assumption
--   | beta_true_cf _ hA =>
--     have hA' := hA.ty_lhs
--     sorry
--   | _ => sorry

-- theorem Ctx.JEq.maybe_subsort_iff {Γ : Ctx} {A a b : Tm} {ℓ : ℕ} (hab : Γ.JEq A a b) :
--   MaybeSubsort Γ ℓ a ↔ MaybeSubsort Γ ℓ b := by induction hab generalizing ℓ with
--   | eqn_ext hA ha hb heqn IA Ia Ib Ieqn =>
--     have Ieqn := Ieqn (ℓ := 1)
--     simp only [MaybeSubsort.unit_iff, zero_add, iff_true] at Ieqn
--     cases Ieqn with
--     | eqn ha hb =>

--       sorry
--   | _ => stop simp [*]
