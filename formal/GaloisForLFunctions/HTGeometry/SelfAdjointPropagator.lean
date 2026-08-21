import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# The Schrödinger propagator of a bounded self-adjoint Hamiltonian

For a bounded self-adjoint operator `H` on a complex Hilbert space, the Banach-algebra exponential

```text
propagator H t = exp (t • (-i H))
```

is the exact solution operator of `i ψ' = H ψ`.  This file records the four properties any
perturbative argument needs and that mathlib does not package: the group law, the derivative, the
adjoint, and unitarity.  Unitarity is proved from `star (exp x) = exp (star x)` together with
`exp (x + y) = exp x * exp y` for commuting arguments; no spectral theory is involved.
-/

open scoped InnerProductSpace
open NormedSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [InnerProductSpace ℂ 𝓗] [CompleteSpace 𝓗]

/-- The Schrödinger propagator `exp (-i t H)` of a bounded Hamiltonian. -/
def propagator (H : 𝓗 →L[ℂ] 𝓗) (t : ℝ) : 𝓗 →L[ℂ] 𝓗 :=
  NormedSpace.exp (t • ((-Complex.I) • H))

omit [CompleteSpace 𝓗] in
@[simp] theorem propagator_zero (H : 𝓗 →L[ℂ] 𝓗) : propagator H 0 = 1 := by
  simp [propagator]

/-- **The propagator solves the Schrödinger equation.** -/
theorem hasDerivAt_propagator (H : 𝓗 →L[ℂ] 𝓗) (t : ℝ) :
    HasDerivAt (propagator H) ((-Complex.I) • (H ∘L propagator H t)) t := by
  have h := hasDerivAt_exp_smul_const' (𝕂 := ℝ) ((-Complex.I) • H) t
  have hrw : ((-Complex.I) • H) * NormedSpace.exp (t • ((-Complex.I) • H))
      = (-Complex.I) • (H ∘L propagator H t) := by
    rw [propagator]
    rfl
  rw [hrw] at h
  exact h

/-- The propagator is a one-parameter group. -/
theorem propagator_comp (H : 𝓗 →L[ℂ] 𝓗) (s t : ℝ) :
    propagator H s ∘L propagator H t = propagator H (s + t) := by
  have hc : Commute (s • ((-Complex.I) • H)) (t • ((-Complex.I) • H)) := by
    refine Commute.smul_left ?_ _
    refine Commute.smul_right ?_ _
    exact Commute.refl _
  have hadd : (s + t) • ((-Complex.I) • H) = s • ((-Complex.I) • H) + t • ((-Complex.I) • H) :=
    add_smul _ _ _
  letI : NormedAlgebra ℚ (𝓗 →L[ℂ] 𝓗) := NormedAlgebra.restrictScalars ℚ ℂ _
  rw [propagator, propagator, propagator, hadd, NormedSpace.exp_add_of_commute hc]
  rfl

/-- The adjoint of the propagator is the reversed propagator. -/
theorem star_propagator {H : 𝓗 →L[ℂ] 𝓗} (hH : IsSelfAdjoint H) (t : ℝ) :
    star (propagator H t) = propagator H (-t) := by
  have hstar : star (t • ((-Complex.I) • H)) = (-t) • ((-Complex.I) • H) := by
    rw [star_smul, star_smul, hH.star_eq]
    simp [neg_smul]
  rw [propagator, propagator, NormedSpace.star_exp, hstar]

/-- **Unitarity of the propagator.** -/
theorem propagator_mem_unitary {H : 𝓗 →L[ℂ] 𝓗} (hH : IsSelfAdjoint H) (t : ℝ) :
    propagator H t ∈ unitary (𝓗 →L[ℂ] 𝓗) := by
  letI : NormedAlgebra ℚ (𝓗 →L[ℂ] 𝓗) := NormedAlgebra.restrictScalars ℚ ℂ _
  refine NormedSpace.exp_mem_unitary_of_mem_skewAdjoint ?_
  rw [skewAdjoint.mem_iff, star_smul, star_smul, hH.star_eq]
  simp [neg_smul]

theorem norm_propagator_apply {H : 𝓗 →L[ℂ] 𝓗} (hH : IsSelfAdjoint H) (t : ℝ) (x : 𝓗) :
    ‖propagator H t x‖ = ‖x‖ := by
  have hone : (ContinuousLinearMap.adjoint (propagator H t)) (propagator H t x) = x := by
    have h := (Unitary.mem_iff.mp (propagator_mem_unitary hH t)).1
    have h2 := congrArg (fun T : 𝓗 →L[ℂ] 𝓗 => T x) h
    simpa [ContinuousLinearMap.star_eq_adjoint] using h2
  have hinner : (inner ℂ (propagator H t x) (propagator H t x) : ℂ) = inner ℂ x x := by
    rw [← ContinuousLinearMap.adjoint_inner_right (propagator H t) x (propagator H t x), hone]
  have hsq : ‖propagator H t x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ),
      InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ), hinner]
  calc ‖propagator H t x‖ = Real.sqrt (‖propagator H t x‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (‖x‖ ^ 2) := by rw [hsq]
    _ = ‖x‖ := Real.sqrt_sq (norm_nonneg _)

theorem norm_propagator_le_one {H : 𝓗 →L[ℂ] 𝓗} (hH : IsSelfAdjoint H) (t : ℝ) :
    ‖propagator H t‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    rw [norm_propagator_apply hH t x, one_mul]

theorem continuous_propagator (H : 𝓗 →L[ℂ] 𝓗) : Continuous (propagator H) := by
  refine continuous_iff_continuousAt.mpr fun t => ?_
  exact (hasDerivAt_propagator H t).continuousAt

end GaloisForLFunctions.HTGeometry
