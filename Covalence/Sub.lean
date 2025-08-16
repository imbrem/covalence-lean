import Covalence.JEq

inductive Ctx.SubMap : Ctx → Ctx → Prop
  | nil : SubMap .nil .nil
  | lift' {Γ Δ : Ctx} {x : ℕ} {A : Tm}
    : SubMap Γ Δ
    → x ∉ Γ.dv
    → x ∉ Δ.dv
    → SubMap (Γ.cons x A) (Δ.cons x A)
  | skip {Γ Δ : Ctx} {x : ℕ} {A : Tm}
    : SubMap Γ Δ
    → x ∉ Γ.dv
    → SubMap (Γ.cons x A) Δ

theorem Ctx.SubMap.dv_anti {Γ Δ : Ctx} (h : Ctx.SubMap Γ Δ) : Δ.dv ⊆ Γ.dv := by
  induction h with
  | nil => rfl
  | lift' => simp [dv]; apply Finset.union_subset_union_right; assumption
  | skip _ _ I => apply Finset.Subset.trans I; simp [dv]

theorem Ctx.SubMap.lift {Γ Δ : Ctx} {x : ℕ} {A : Tm}
  (h : Ctx.SubMap Γ Δ) (hx : x ∉ Γ.dv) : Ctx.SubMap (Γ.cons x A) (Δ.cons x A)
  := h.lift' hx (Finset.not_mem_subset h.dv_anti hx)

theorem Ctx.SubMap.src_no_rep {Γ Δ : Ctx} (h : Ctx.SubMap Γ Δ) : Γ.NoRep
  := by induction h <;> constructor <;> assumption

theorem Ctx.SubMap.trg_no_rep {Γ Δ : Ctx} (h : Ctx.SubMap Γ Δ) : Δ.NoRep
  := by induction h <;> repeat first | assumption | constructor

theorem Ctx.SubMap.at {Γ Δ : Ctx} (h : Ctx.SubMap Γ Δ) {x : ℕ} {A : Tm} (hA : Δ.At x A) : Γ.At x A
  := by induction h with
  | nil => exact hA
  | lift' _ _ _ I => cases hA with
    | here => apply At.here
    | there => apply At.there; apply I; assumption
  | skip _ _ I => apply At.there; exact I hA

theorem Ctx.SubMap.at_anti {Γ Δ : Ctx}
  (h : Ctx.SubMap Γ Δ) {x : ℕ} {A : Tm} (hx : x ∈ Δ.dv) (hA : Γ.At x A) : Δ.At x A
  := by induction h with
  | nil => exact hA
  | lift' _ hΓ _ I => cases hA with
    | here => apply At.here
    | there hΓ' =>
      simp only [dv, Finset.mem_union, Finset.mem_singleton] at hx
      cases hx with
      | inl h => cases h; exact (hΓ hΓ'.mem_dv).elim
      | inr h => apply At.there; apply I <;> assumption
  | skip h hΓ I => cases hA with
    | here => exact (hΓ (h.dv_anti hx)).elim
    | there => apply I <;> assumption

inductive Ctx.SubScope : Ctx → Ctx → Prop
  | nil : SubScope .nil .nil
  | lift' {Γ Δ : Ctx} {x : ℕ} {A : Tm}
    : SubScope Γ Δ
    → x ∉ Γ.dv
    → x ∉ Δ.dv
    → A.fvs ⊆ Γ.dv
    → A.fvs ⊆ Δ.dv
    → SubScope (Γ.cons x A) (Δ.cons x A)
  | skip {Γ Δ : Ctx} {x : ℕ} {A : Tm}
    : SubScope Γ Δ
    → x ∉ Γ.dv
    → A.fvs ⊆ Γ.dv
    → SubScope (Γ.cons x A) Δ

def Ctx.SubScope.src {Γ Δ : Ctx} (_ : Ctx.SubScope Γ Δ) : Ctx := Γ

theorem Ctx.SubScope.sub_map {Γ Δ : Ctx} (h : Ctx.SubScope Γ Δ) : Ctx.SubMap Γ Δ
  := by induction h <;> constructor <;> assumption

theorem Ctx.SubScope.src_no_rep {Γ Δ : Ctx} (h : Ctx.SubScope Γ Δ) : Γ.NoRep
  := h.sub_map.src_no_rep

theorem Ctx.SubScope.trg_no_rep {Γ Δ : Ctx} (h : Ctx.SubScope Γ Δ) : Δ.NoRep
  := h.sub_map.trg_no_rep

theorem Ctx.SubScope.dv_anti {Γ Δ : Ctx} (h : Ctx.SubScope Γ Δ) : Δ.dv ⊆ Γ.dv
  := h.sub_map.dv_anti

theorem Ctx.SubScope.at {Γ Δ : Ctx} (h : Ctx.SubScope Γ Δ) {x : ℕ} {A : Tm}
  (hA : Δ.At x A) : Γ.At x A := h.sub_map.at hA

theorem Ctx.SubScope.at_anti {Γ Δ : Ctx} (h : Ctx.SubScope Γ Δ) {x : ℕ} {A : Tm}
  (hx : x ∈ Δ.dv) (hA : Γ.At x A) : Δ.At x A := h.sub_map.at_anti hx hA

theorem Ctx.SubScope.at_sub_trg {Γ Δ : Ctx} (h : Ctx.SubScope Γ Δ) {x : ℕ} {A : Tm}
  (hA : Δ.At x A) : A.fvs ⊆ Δ.dv := by induction h with
  | nil => cases hA
  | lift' _ _ _ _ hAΔ I => cases hA with
    | here => apply Finset.Subset.trans hAΔ; simp [dv]
    | there hx => apply Finset.Subset.trans (I hx); simp [dv]
  | skip _ _ _ I => exact I hA

theorem Ctx.SubScope.at_sub_anti {Γ Δ : Ctx} (h : Ctx.SubScope Γ Δ) {x : ℕ} {A : Tm}
  (hx : x ∈ Δ.dv) (hA : Γ.At x A) : A.fvs ⊆ Δ.dv := h.at_sub_trg (h.at_anti hx hA)

theorem Ctx.SubScope.lift {Γ Δ : Ctx} (h : Ctx.SubScope Γ Δ) {x : ℕ} {A : Tm}
  (hx : x ∉ Γ.dv) (hA : A.fvs ⊆ Δ.dv) : Ctx.SubScope (Γ.cons x A) (Δ.cons x A)
  := h.lift' hx (Set.notMem_subset h.dv_anti hx) (hA.trans h.dv_anti) hA
