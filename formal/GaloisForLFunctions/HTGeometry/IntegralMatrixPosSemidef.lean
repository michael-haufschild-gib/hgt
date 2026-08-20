/-
# Entrywise integration preserves positive semidefiniteness

A pointwise positive semidefinite complex matrix density integrates entrywise to a positive
semidefinite matrix: the quadratic form of the integral is the integral of the quadratic forms.
-/
import Mathlib

noncomputable section

open MeasureTheory
open scoped ComplexOrder BigOperators

namespace GaloisForLFunctions.HTGeometry

variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}

/-- **Entrywise integration preserves positivity.** -/
theorem posSemidef_integral_matrix (μ : Measure Ω) (Kf : Ω → Matrix (Fin n) (Fin n) ℂ)
    (hint : ∀ j k, Integrable (fun ω => Kf ω j k) μ)
    (hPSD : ∀ ω, (Kf ω).PosSemidef) :
    (Matrix.of fun j k => ∫ ω, Kf ω j k ∂μ).PosSemidef := by
  classical
  have hherm : (Matrix.of fun j k => ∫ ω, Kf ω j k ∂μ).IsHermitian := by
    ext j k
    rw [Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.of_apply, RCLike.star_def,
      ← integral_conj]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    have := (hPSD ω).isHermitian
    have h := congrFun (congrFun this j) k
    rw [Matrix.conjTranspose_apply, RCLike.star_def] at h
    exact h
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hherm (fun c => ?_)
  have hpoint : ∀ ω, (0 : ℂ) ≤ star c ⬝ᵥ (Kf ω).mulVec c :=
    fun ω => (hPSD ω).dotProduct_mulVec_nonneg c
  have hintq : Integrable (fun ω => star c ⬝ᵥ (Kf ω).mulVec c) μ := by
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, RCLike.star_def]
    refine integrable_finsetSum _ (fun j _ => ?_)
    exact Integrable.const_mul (integrable_finsetSum _ (fun k _ => (hint j k).mul_const _)) _
  have hval : star c ⬝ᵥ (Matrix.of fun j k => ∫ ω, Kf ω j k ∂μ).mulVec c
      = ∫ ω, star c ⬝ᵥ (Kf ω).mulVec c ∂μ := by
    simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, RCLike.star_def]
    have hIj : ∀ j : Fin n,
        Integrable (fun ω => (starRingEnd ℂ) (c j) * ∑ k, Kf ω j k * c k) μ := by
      intro j
      exact Integrable.const_mul (integrable_finsetSum _ (fun k _ => (hint j k).mul_const _)) _
    rw [integral_finsetSum _ (fun j _ => hIj j)]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [integral_const_mul, integral_finsetSum _ (fun k _ => (hint j k).mul_const _)]
    refine congrArg _ (Finset.sum_congr rfl (fun k _ => ?_))
    rw [integral_mul_const]
  have hre : ∀ ω, star c ⬝ᵥ (Kf ω).mulVec c
      = (((star c ⬝ᵥ (Kf ω).mulVec c).re : ℝ) : ℂ) := by
    intro ω
    have h := hpoint ω
    rw [Complex.le_def] at h
    refine Complex.ext rfl ?_
    simpa using h.2.symm
  rw [hval, integral_congr_ae (Filter.Eventually.of_forall hre), integral_complex_ofReal,
    Complex.le_def]
  refine ⟨?_, by simp⟩
  simp only [Complex.zero_re, Complex.ofReal_re]
  refine integral_nonneg (fun ω => ?_)
  have h := hpoint ω
  rw [Complex.le_def] at h
  simpa using h.1

end GaloisForLFunctions.HTGeometry
