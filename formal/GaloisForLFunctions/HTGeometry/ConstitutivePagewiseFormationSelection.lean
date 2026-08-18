import GaloisForLFunctions.HTGeometry.FiniteDiagonalOperator

/-!
# Pagewise formation and stable-organ selection: diagonal normal form

A finite Hilbert realization of a law-history spectral machine is unitarily equivalent to a
diagonal response: nonzero coordinates are page-death layers and zero coordinates are stable
survivors. This module certifies the normal-form selection mechanism:

* old page formation misses exactly the stable sector;
* every response factored through old formation remains blind there;
* a separating terminal block makes completed formation injective and quantitatively proper;
* unit-modulus gauge changes preserve the global gap.
-/

open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]

/-- Old page gains, extended by zero on the stable sector. -/
def pageFormationGain (g : ι → ℂ) : Sum ι σ → ℂ
  | Sum.inl i => g i
  | Sum.inr _ => 0

/-- Old page gains completed by a terminal response on the stable sector. -/
def completedPageFormationGain (g : ι → ℂ) (b : σ → ℂ) : Sum ι σ → ℂ
  | Sum.inl i => g i
  | Sum.inr s => b s

/-- Stable coordinate sector missed by all old page responses. -/
def pageStableSubmodule : Submodule ℂ (EuclideanSpace ℂ (Sum ι σ)) where
  carrier := {x | ∀ i, x (Sum.inl i) = 0}
  zero_mem' _ := rfl
  add_mem' hx hy i := by rw [PiLp.add_apply, hx i, hy i, add_zero]
  smul_mem' c x hx i := by rw [PiLp.smul_apply, hx i, smul_zero]

@[simp]
theorem mem_pageStableSubmodule_iff (x : EuclideanSpace ℂ (Sum ι σ)) :
    x ∈ (pageStableSubmodule : Submodule ℂ (EuclideanSpace ℂ (Sum ι σ))) ↔
      ∀ i, x (Sum.inl i) = 0 :=
  Iff.rfl

/-- Exact global kernel: old page formation misses precisely stable coordinates. -/
theorem ker_pageFormation_eq_stable (g : ι → ℂ) (hg : ∀ i, g i ≠ 0) :
    LinearMap.ker (euclideanDiagOp (pageFormationGain (σ := σ) g)).toLinearMap =
      pageStableSubmodule := by
  ext x
  rw [LinearMap.mem_ker, mem_pageStableSubmodule_iff]
  constructor
  · intro hx i
    have hi := congrArg (fun y : EuclideanSpace ℂ (Sum ι σ) => y (Sum.inl i)) hx
    change g i * x (Sum.inl i) = 0 at hi
    exact (mul_eq_zero.mp hi).resolve_left (hg i)
  · intro hx
    ext j
    cases j with
    | inl i => simp [diagOp_apply, pageFormationGain, hx i]
    | inr s => simp [diagOp_apply, pageFormationGain]

/-- Every response factored through old page formation remains blind on the stable sector. -/
theorem factoredPageResponse_vanishes_on_stable
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z]
    (g : ι → ℂ)
    (S : EuclideanSpace ℂ (Sum ι σ) →L[ℂ] Z)
    (x : EuclideanSpace ℂ (Sum ι σ)) (hx : x ∈ pageStableSubmodule) :
    (S ∘L euclideanDiagOp (pageFormationGain (σ := σ) g)) x = 0 := by
  rw [ContinuousLinearMap.comp_apply]
  have hold : euclideanDiagOp (pageFormationGain (σ := σ) g) x = 0 := by
    ext j
    cases j with
    | inl i => simp [diagOp_apply, pageFormationGain, hx i]
    | inr s => simp [diagOp_apply, pageFormationGain]
  rw [hold, map_zero]

/-- Adjoining a boundedly factored response cannot shrink the old common kernel. -/
theorem ker_inf_ker_factoredPageResponse
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z]
    (g : ι → ℂ)
    (S : EuclideanSpace ℂ (Sum ι σ) →L[ℂ] Z) :
    LinearMap.ker (euclideanDiagOp (pageFormationGain (σ := σ) g)).toLinearMap ⊓
        LinearMap.ker
          (S.comp (euclideanDiagOp (pageFormationGain (σ := σ) g))).toLinearMap =
      LinearMap.ker (euclideanDiagOp (pageFormationGain (σ := σ) g)).toLinearMap := by
  apply le_antisymm inf_le_left
  intro x hx
  refine ⟨hx, ?_⟩
  change (S.comp (euclideanDiagOp (pageFormationGain (σ := σ) g))) x = 0
  rw [ContinuousLinearMap.comp_apply]
  have hx0 : euclideanDiagOp (pageFormationGain (σ := σ) g) x = 0 := by
    exact LinearMap.mem_ker.mp hx
  rw [hx0, map_zero]

/-- A nonempty stable sector makes every old page formation noninjective. -/
theorem pageFormation_not_injective [Nonempty σ] (g : ι → ℂ) :
    ¬ Function.Injective (euclideanDiagOp (pageFormationGain (σ := σ) g)) := by
  intro hinj
  let s : σ := Classical.choice inferInstance
  let e : EuclideanSpace ℂ (Sum ι σ) := EuclideanSpace.single (Sum.inr s) 1
  have heq : euclideanDiagOp (pageFormationGain (σ := σ) g) e =
      euclideanDiagOp (pageFormationGain (σ := σ) g) 0 := by
    ext j
    cases j with
    | inl i => simp [e, diagOp_apply, pageFormationGain]
    | inr t => simp [e, diagOp_apply, pageFormationGain]
  have h := congrArg (fun x : EuclideanSpace ℂ (Sum ι σ) => x (Sum.inr s)) (hinj heq)
  simpa [e] using h

/-- A separating terminal block makes completed page formation injective. -/
theorem completedPageFormation_injective
    (g : ι → ℂ) (b : σ → ℂ) (hg : ∀ i, g i ≠ 0) (hb : ∀ s, b s ≠ 0) :
    Function.Injective (euclideanDiagOp (completedPageFormationGain g b)) := by
  intro x y hxy
  ext j
  have hj := congrArg (fun z : EuclideanSpace ℂ (Sum ι σ) => z j) hxy
  rw [diagOp_apply, diagOp_apply] at hj
  cases j with
  | inl i => exact mul_left_cancel₀ (hg i) hj
  | inr s => exact mul_left_cancel₀ (hb s) hj

/-- Finite global properness: least page-or-terminal gain bounds assembled response. -/
theorem completedPageFormation_lower [Nonempty ι]
    (g : ι → ℂ) (b : σ → ℂ) (x : EuclideanSpace ℂ (Sum ι σ)) :
    diagMin (completedPageFormationGain g b) * ‖x‖ ≤
      ‖euclideanDiagOp (completedPageFormationGain g b) x‖ :=
  diagMin_mul_norm_le (completedPageFormationGain g b) x

/-- Unit-modulus gauge changes preserve the global page/terminal gap. -/
theorem diagMin_phase_mul [Nonempty ι]
    (u h : Sum ι σ → ℂ) (hu : ∀ j, ‖u j‖ = 1) :
    diagMin (fun j => u j * h j) = diagMin h := by
  unfold diagMin
  congr 1
  funext j
  rw [norm_mul, hu j, one_mul]

/-- Capstone: old-page blindness, terminal selection, quantitative properness, and phase neutrality
hold simultaneously in finite Hodge normal form. -/
theorem pagewiseFormationSelection_capstone [Nonempty ι] [Nonempty σ]
    (g : ι → ℂ) (b : σ → ℂ) (hg : ∀ i, g i ≠ 0) (hb : ∀ s, b s ≠ 0)
    (u : Sum ι σ → ℂ) (hu : ∀ j, ‖u j‖ = 1) :
    LinearMap.ker (euclideanDiagOp (pageFormationGain (σ := σ) g)).toLinearMap =
        pageStableSubmodule ∧
      ¬ Function.Injective (euclideanDiagOp (pageFormationGain (σ := σ) g)) ∧
      Function.Injective (euclideanDiagOp (completedPageFormationGain g b)) ∧
      0 < diagMin (completedPageFormationGain g b) ∧
      diagMin (fun j => u j * completedPageFormationGain g b j) =
        diagMin (completedPageFormationGain g b) := by
  refine ⟨ker_pageFormation_eq_stable g hg, pageFormation_not_injective g,
    completedPageFormation_injective g b hg hb, ?_,
    diagMin_phase_mul u (completedPageFormationGain g b) hu⟩
  apply diagMin_pos
  intro j
  cases j with
  | inl i => exact hg i
  | inr s => exact hb s

end

end GaloisForLFunctions.HTGeometry
