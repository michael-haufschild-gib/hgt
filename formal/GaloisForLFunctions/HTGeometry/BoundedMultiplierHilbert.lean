import GaloisForLFunctions.HTGeometry.LpBoundedMultiplier
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Bounded multiplication operators on a Hilbert `L²`

Multiplication by a bounded measurable real-valued symbol is self-adjoint on `L²(μ)` for an
arbitrary measure `μ`, and it is injective as soon as the symbol vanishes nowhere.  An injective
self-adjoint operator on a Hilbert space has dense range, because a vector orthogonal to the range
is annihilated by the operator.

These are the measure-agnostic forms of the corresponding statements for Lebesgue measure on a
finite-dimensional inner product space.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

/-- A continuous linear map on a Hilbert space whose range has trivial orthogonal complement has
dense range. -/
theorem denseRange_of_orthogonal_trivial {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {T : H →L[ℂ] H}
    (h : ∀ g : H, (∀ f : H, inner ℂ (T f) g = (0 : ℂ)) → g = 0) :
    DenseRange T := by
  set K : Submodule ℂ H := LinearMap.range (T : H →ₗ[ℂ] H) with hK
  have hperp : Kᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro g hg
    refine h g fun f => ?_
    exact (Submodule.mem_orthogonal K g).mp hg (T f) ⟨f, rfl⟩
  have hclos := Submodule.orthogonal_orthogonal_eq_closure K
  rw [hperp, Submodule.bot_orthogonal_eq_top] at hclos
  have hdense : Dense (K : Set H) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr hclos.symm
  have hset : (K : Set H) = Set.range (T : H → H) := by
    ext y
    simp [hK, LinearMap.mem_range, Set.mem_range]
  rw [hset] at hdense
  exact hdense

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {φ : α → ℂ} {C : ℝ}

/-- **Multiplication by a real-valued bounded symbol is self-adjoint on `L²(μ)`.** -/
theorem lpBoundedMulCLM_inner_general (hφ : Measurable φ) (hC0 : 0 ≤ C) (hC : ∀ x, ‖φ x‖ ≤ C)
    (hreal : ∀ x, (starRingEnd ℂ) (φ x) = φ x) (f g : Lp ℂ 2 μ) :
    (inner ℂ (lpBoundedMulCLM (p := 2) (μ := μ) hφ hC0 hC f) g : ℂ)
      = inner ℂ f (lpBoundedMulCLM (p := 2) (μ := μ) hφ hC0 hC g) := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [lpBoundedMulCLM_coeFn (p := 2) (μ := μ) hφ hC0 hC f,
    lpBoundedMulCLM_coeFn (p := 2) (μ := μ) hφ hC0 hC g] with x h1 h2
  rw [h1, h2, RCLike.inner_apply', RCLike.inner_apply', map_mul, hreal]
  ring

/-- **The adjoint of a complex multiplication operator is multiplication by the pointwise
conjugate.**  This is the complex-symbol form of `lpBoundedMulCLM_inner_general`; unlike the
real-symbol specialization, it supplies the involution law needed by represented smooth
function algebras. -/
theorem lpBoundedMulCLM_eq_adjoint_conj_general
    {psi : α → ℂ} {D : ℝ}
    (hφ : Measurable φ) (hC0 : 0 ≤ C) (hC : ∀ x, ‖φ x‖ ≤ C)
    (hpsi : Measurable psi) (hD0 : 0 ≤ D) (hD : ∀ x, ‖psi x‖ ≤ D)
    (hconj : ∀ x, psi x = (starRingEnd ℂ) (φ x)) :
    lpBoundedMulCLM (p := 2) (μ := μ) hpsi hD0 hD =
      ContinuousLinearMap.adjoint
        (lpBoundedMulCLM (p := 2) (μ := μ) hφ hC0 hC) := by
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro f g
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [lpBoundedMulCLM_coeFn (p := 2) (μ := μ) hpsi hD0 hD f,
    lpBoundedMulCLM_coeFn (p := 2) (μ := μ) hφ hC0 hC g] with x h1 h2
  rw [h1, h2, RCLike.inner_apply', RCLike.inner_apply', map_mul, hconj]
  have hinv : (starRingEnd ℂ) ((starRingEnd ℂ) (φ x)) = φ x := star_star (φ x)
  rw [hinv]
  ring

/-- **A multiplication operator with a nowhere vanishing symbol is injective.** -/
theorem lpBoundedMulCLM_injective_general {p : ℝ≥0∞} [Fact (1 ≤ p)] (hφ : Measurable φ)
    (hC0 : 0 ≤ C) (hC : ∀ x, ‖φ x‖ ≤ C) (hne : ∀ x, φ x ≠ 0) :
    Function.Injective (lpBoundedMulCLM (p := p) (μ := μ) hφ hC0 hC) := by
  intro f g hfg
  have hae : ((lpBoundedMulCLM (p := p) (μ := μ) hφ hC0 hC f : Lp ℂ p μ) : α → ℂ)
      =ᵐ[μ] ((lpBoundedMulCLM (p := p) (μ := μ) hφ hC0 hC g : Lp ℂ p μ) : α → ℂ) := by
    rw [hfg]
  refine Lp.ext ?_
  filter_upwards [lpBoundedMulCLM_coeFn (p := p) (μ := μ) hφ hC0 hC f,
    lpBoundedMulCLM_coeFn (p := p) (μ := μ) hφ hC0 hC g, hae] with x h1 h2 h3
  rw [h1, h2] at h3
  exact mul_left_cancel₀ (hne x) h3

/-- **A multiplication operator with an almost-everywhere nonvanishing symbol is injective.**
This is the measure-theoretically sharp form: values on a null set cannot affect an `Lᵖ`
operator. -/
theorem lpBoundedMulCLM_injective_of_ae_ne_zero {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hφ : Measurable φ) (hC0 : 0 ≤ C) (hC : ∀ x, ‖φ x‖ ≤ C)
    (hne : ∀ᵐ x ∂μ, φ x ≠ 0) :
    Function.Injective (lpBoundedMulCLM (p := p) (μ := μ) hφ hC0 hC) := by
  intro f g hfg
  have hae : ((lpBoundedMulCLM (p := p) (μ := μ) hφ hC0 hC f : Lp ℂ p μ) : α → ℂ)
      =ᵐ[μ] ((lpBoundedMulCLM (p := p) (μ := μ) hφ hC0 hC g : Lp ℂ p μ) : α → ℂ) := by
    rw [hfg]
  refine Lp.ext ?_
  filter_upwards [lpBoundedMulCLM_coeFn (p := p) (μ := μ) hφ hC0 hC f,
    lpBoundedMulCLM_coeFn (p := p) (μ := μ) hφ hC0 hC g, hae, hne]
    with x h1 h2 h3 hx
  rw [h1, h2] at h3
  exact mul_left_cancel₀ hx h3

/-- **An injective self-adjoint multiplication operator has dense range.** -/
theorem denseRange_lpBoundedMulCLM [CompleteSpace (Lp ℂ 2 μ)] (hφ : Measurable φ) (hC0 : 0 ≤ C)
    (hC : ∀ x, ‖φ x‖ ≤ C) (hreal : ∀ x, (starRingEnd ℂ) (φ x) = φ x) (hne : ∀ x, φ x ≠ 0) :
    DenseRange (lpBoundedMulCLM (p := 2) (μ := μ) hφ hC0 hC) := by
  refine denseRange_of_orthogonal_trivial fun g hg => ?_
  have h := hg (lpBoundedMulCLM (p := 2) (μ := μ) hφ hC0 hC g)
  rw [lpBoundedMulCLM_inner_general hφ hC0 hC hreal _ g] at h
  have hzero : lpBoundedMulCLM (p := 2) (μ := μ) hφ hC0 hC g = 0 :=
    inner_self_eq_zero.mp h
  exact lpBoundedMulCLM_injective_general hφ hC0 hC hne (by simpa using hzero)

/-- **An almost-everywhere injective self-adjoint multiplication operator has dense range.** -/
theorem denseRange_lpBoundedMulCLM_of_ae_ne_zero [CompleteSpace (Lp ℂ 2 μ)]
    (hφ : Measurable φ) (hC0 : 0 ≤ C) (hC : ∀ x, ‖φ x‖ ≤ C)
    (hreal : ∀ x, (starRingEnd ℂ) (φ x) = φ x)
    (hne : ∀ᵐ x ∂μ, φ x ≠ 0) :
    DenseRange (lpBoundedMulCLM (p := 2) (μ := μ) hφ hC0 hC) := by
  refine denseRange_of_orthogonal_trivial fun g hg => ?_
  have h := hg (lpBoundedMulCLM (p := 2) (μ := μ) hφ hC0 hC g)
  rw [lpBoundedMulCLM_inner_general hφ hC0 hC hreal _ g] at h
  have hzero : lpBoundedMulCLM (p := 2) (μ := μ) hφ hC0 hC g = 0 :=
    inner_self_eq_zero.mp h
  exact lpBoundedMulCLM_injective_of_ae_ne_zero hφ hC0 hC hne (by simpa using hzero)

end GaloisForLFunctions.HTGeometry
