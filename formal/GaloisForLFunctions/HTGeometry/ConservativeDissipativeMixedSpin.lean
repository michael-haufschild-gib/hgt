import GaloisForLFunctions.HTGeometry.ConservativeDissipativeSpinDensityFlow
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# Exact mixed-state spin evolution on invariant spectral spheres

The Schaffer–Exl spin mechanism (arXiv:2609.04530) extends through the corpus's
Lorentz density encoding to arbitrary constructed Bloch radii. A precise
radius correction of the representative damping produces solutions of the
same nonlinear quantum field. Positivity and trace are preserved; a moving
pair of complementary projectors yields every matrix power explicitly and
proves all trace powers constant. Positive damping nevertheless drives the
state to its lowest-energy orientation on that fixed spectral sphere.
-/

set_option autoImplicit false
open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator
open Matrix Filter
namespace GaloisForLFunctions.HTGeometry.SchafferExl
noncomputable section

/-- A positive Bloch radius at most one, constructed from an unrestricted real mixing coordinate. -/
def spinMixRadius (u : ℝ) : ℝ := (1 + u ^ 2)⁻¹

/-- The mixing construction never produces a negative or zero radius. -/
theorem spinMixRadius_pos (u : ℝ) : 0 < spinMixRadius u := by unfold spinMixRadius; positivity

/-- The mixing radius always stays in the physical Bloch ball. -/
theorem spinMixRadius_le_one (u : ℝ) : spinMixRadius u ≤ 1 := by
  have hd : 1 + u ^ 2 ≠ 0 := by positivity
  have he : spinMixRadius u * (1 + u ^ 2) = 1 := by simp [spinMixRadius, hd]
  have hp := mul_nonneg (spinMixRadius_pos u).le (sq_nonneg u)
  nlinarith

/-- Effective damping on the unit-spin representative of a mixed-state sphere. -/
def spinMixAmplitude (a u : ℝ) : ℝ := a * spinChartScale (u : ℂ)

/-- The effective squared damping is exactly the original damping times the Bloch radius. -/
theorem spinMixAmplitude_sq (a u : ℝ) : spinMixAmplitude a u ^ 2 = a ^ 2 * spinMixRadius u := by
  rw [spinMixAmplitude, mul_pow, spinChartScale_sq]
  simp [spinMixRadius, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- Exact scaling law of the nonlinear classical field at every unrestricted real spin. -/
theorem spinSphereField_mixed_scale (a u : ℝ) (m : EuclideanSpace ℝ (Fin 3)) :
    spinSphereField a (spinMixRadius u • m) =
      spinMixRadius u • spinSphereField (spinMixAmplitude a u) m := by
  ext i
  fin_cases i <;> simp [spinSphereField_components, spinMixAmplitude_sq] <;> ring

/-- Arbitrary-radius real spin evolving with the same original nonlinear field. -/
def spinMixedVector (a u : ℝ) (z : ℂ) (t : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  spinMixRadius u • spinSphereFlow (spinMixAmplitude a u) z t

/-- The rescaled trajectory solves the original spin equation, not a rescaled vector field. -/
theorem hasDerivAt_spinMixedVector (a u : ℝ) (z : ℂ) (t : ℝ) :
    HasDerivAt (spinMixedVector a u z) (spinSphereField a (spinMixedVector a u z t)) t := by
  have h := (hasDerivAt_spinSphereFlow (spinMixAmplitude a u) z t).const_smul (spinMixRadius u)
  change HasDerivAt (fun v => spinMixRadius u • spinSphereFlow (spinMixAmplitude a u) z v) _ t
  change HasDerivAt (fun v => spinMixRadius u • spinSphereFlow (spinMixAmplitude a u) z v)
    (spinMixRadius u • spinSphereField (spinMixAmplitude a u)
      (spinSphereFlow (spinMixAmplitude a u) z t)) t at h
  simpa only [spinMixedVector, spinSphereField_mixed_scale] using h

/-- The Bloch radius is conserved at every real time. -/
theorem spinMixedVector_norm (a u : ℝ) (z : ℂ) (t : ℝ) :
    ‖spinMixedVector a u z t‖ = spinMixRadius u := by
  rw [spinMixedVector, norm_smul, spinSphereFlow_norm, mul_one,
    Real.norm_of_nonneg (spinMixRadius_pos u).le]

/-- Scaling a real spin is precisely mixing its density with the maximally mixed state. -/
theorem spinMatrix_smul (r : ℝ) (m : EuclideanSpace ℝ (Fin 3)) :
    spinMatrix (r • m) = (((1 - r) / 2 : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
      (r : ℂ) • spinMatrix m := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinMatrix, lorentzHermitianMatrix, Matrix.smul_apply] <;> ring

/-- The actual mixed density trajectory on its invariant Bloch sphere. -/
def spinMixedDensity (a u : ℝ) (z : ℂ) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  spinMatrix (spinMixedVector a u z t)

/-- Literal convex mixture with the already constructed pure-state solution. -/
theorem spinMixedDensity_mixture (a u : ℝ) (z : ℂ) (t : ℝ) :
    spinMixedDensity a u z t = (((1 - spinMixRadius u) / 2 : ℝ) : ℂ) •
      (1 : Matrix (Fin 2) (Fin 2) ℂ) +
      (spinMixRadius u : ℂ) • spinDensityFlow (spinMixAmplitude a u) z t := by
  rw [spinMixedDensity, spinMixedVector, spinMatrix_smul, spinDensityFlow_eq_spinMatrix]

/-- Positivity and unit trace hold for the entire mixed quantum evolution. -/
theorem spinMixedDensity_state (a u : ℝ) (z : ℂ) (t : ℝ) :
    (spinMixedDensity a u z t).PosSemidef ∧ Matrix.trace (spinMixedDensity a u z t) = 1 := by
  constructor
  · rw [spinMixedDensity_mixture]
    have h0 : (0 : ℂ) ≤ (((1 - spinMixRadius u) / 2 : ℝ) : ℂ) := by
      exact_mod_cast (div_nonneg (sub_nonneg.mpr (spinMixRadius_le_one u)) (show (0 : ℝ) ≤ 2 by positivity))
    have hr : (0 : ℂ) ≤ (spinMixRadius u : ℂ) := by exact_mod_cast (spinMixRadius_pos u).le
    exact (Matrix.PosSemidef.one.smul h0).add ((spinDensityFlow_state _ _ _).1.smul hr)
  · exact spinMatrix_trace _

/-- Mixed and pure states solve exactly the same nonlinear quantum matrix equation. -/
theorem hasDerivAt_spinMixedDensity (a u : ℝ) (z : ℂ) (t : ℝ) :
    HasDerivAt (spinMixedDensity a u z) (spinDensityField a (spinMixedDensity a u z t)) t := by
  have h := (hasFDerivAt_spinMatrix (spinMixedVector a u z t)).comp_hasDerivAt t
    (hasDerivAt_spinMixedVector a u z t)
  change HasDerivAt (fun v => spinMatrix (spinMixedVector a u z v)) _ t
  simpa only [spinMixedDensity, Function.comp_def, spinMatrixTangent_field] using h

/-- The two time-independent spectral values of the mixed spin density. -/
def spinMixEigenPlus (u : ℝ) : ℝ := (1 + spinMixRadius u) / 2

def spinMixEigenMinus (u : ℝ) : ℝ := (1 - spinMixRadius u) / 2

/-- Exact spectral-projector decomposition with complementary moving pure projectors. -/
theorem spinMixedDensity_spectral (a u : ℝ) (z : ℂ) (t : ℝ) :
    spinMixedDensity a u z t = (spinMixEigenPlus u : ℂ) •
      spinDensityFlow (spinMixAmplitude a u) z t + (spinMixEigenMinus u : ℂ) •
      (1 - spinDensityFlow (spinMixAmplitude a u) z t) := by
  rw [spinMixedDensity_mixture, spinMixEigenPlus, spinMixEigenMinus]
  push_cast
  module

/-- Every matrix power follows the same two complementary spectral projectors. -/
theorem spinMixedDensity_pow (a u : ℝ) (z : ℂ) (t : ℝ) (n : ℕ) :
    spinMixedDensity a u z t ^ n = ((spinMixEigenPlus u : ℂ) ^ n) •
      spinDensityFlow (spinMixAmplitude a u) z t + ((spinMixEigenMinus u : ℂ) ^ n) •
      (1 - spinDensityFlow (spinMixAmplitude a u) z t) := by
  have hP := (spinDensityFlow_state (spinMixAmplitude a u) z t).2.2
  induction n with
  | zero => simp only [pow_zero, one_smul]; module
  | succ n ih =>
    rw [pow_succ, ih, spinMixedDensity_spectral]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
      hP, sub_self, smul_zero, add_zero, pow_succ]
    module

/-- All spectral trace powers are constant along the actual mixed density ODE. -/
theorem spinMixedDensity_trace_pow (a u : ℝ) (z : ℂ) (t : ℝ) (n : ℕ) :
    Matrix.trace (spinMixedDensity a u z t ^ n) =
      (spinMixEigenPlus u : ℂ) ^ n + (spinMixEigenMinus u : ℂ) ^ n := by
  have hP := (spinDensityFlow_state (spinMixAmplitude a u) z t).2.1
  rw [spinMixedDensity_pow]
  simp [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_sub, hP]
  ring

/-- The determinant of every real-spin matrix records its squared Bloch radius. -/
theorem spinMatrix_det (m : EuclideanSpace ℝ (Fin 3)) :
    (spinMatrix m).det = (((1 - ‖m‖ ^ 2) / 4 : ℝ) : ℂ) := by
  have hn : ‖m‖ ^ 2 = m 0 ^ 2 + m 1 ^ 2 + m 2 ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_three]
    simp [Real.norm_eq_abs, sq_abs]
  rw [spinMatrix, Matrix.det_smul, lorentzHermitianMatrix_det, hn]
  simp only [Fintype.card_fin]
  push_cast
  ring

/-- The determinant is the product of the two constructed spectral values. -/
theorem spinMixedDensity_det (a u : ℝ) (z : ℂ) (t : ℝ) :
    (spinMixedDensity a u z t).det = (spinMixEigenPlus u : ℂ) * (spinMixEigenMinus u : ℂ) := by
  rw [spinMixedDensity, spinMatrix_det, spinMixedVector_norm, spinMixEigenPlus, spinMixEigenMinus]
  push_cast
  ring

/-- Exact characteristic polynomial of the evolving mixed state. -/
theorem spinMixedDensity_charpoly (a u : ℝ) (z : ℂ) (t : ℝ) :
    (spinMixedDensity a u z t).charpoly =
      (Polynomial.X - Polynomial.C (spinMixEigenPlus u : ℂ)) *
        (Polynomial.X - Polynomial.C (spinMixEigenMinus u : ℂ)) := by
  have hs : (spinMixEigenPlus u : ℂ) + (spinMixEigenMinus u : ℂ) = 1 := by
    unfold spinMixEigenPlus spinMixEigenMinus
    push_cast
    ring
  rw [Matrix.charpoly_fin_two, (spinMixedDensity_state a u z t).2, spinMixedDensity_det,
    map_mul, map_one, one_mul]
  calc
    _ = Polynomial.X ^ 2 -
        (Polynomial.C (spinMixEigenPlus u : ℂ) + Polynomial.C (spinMixEigenMinus u : ℂ)) *
          Polynomial.X + Polynomial.C (spinMixEigenPlus u : ℂ) *
            Polynomial.C (spinMixEigenMinus u : ℂ) := by
      rw [← map_add, hs, map_one, one_mul]
    _ = _ := by ring

/-- The actual complex spectrum consists exactly of the two time-independent eigenvalues. -/
theorem spinMixedDensity_spectrum (a u : ℝ) (z : ℂ) (t : ℝ) :
    spectrum ℂ (spinMixedDensity a u z t) =
      {(spinMixEigenPlus u : ℂ), (spinMixEigenMinus u : ℂ)} := by
  ext c
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, spinMixedDensity_charpoly]
  simp [Polynomial.IsRoot, sub_eq_zero]

/-- Quantum energy follows the exact classical latitude on its conserved mixed-state radius. -/
theorem spinMixedDensity_energy (a u : ℝ) (z : ℂ) (t : ℝ) :
    (Matrix.trace (spinMixedDensity a u z t * QuantumAlg.pauliZ)).re =
      spinMixRadius u * spinSphereFlow (spinMixAmplitude a u) z t 2 := by
  rw [spinMixedDensity, spinMatrix_expectation_Z]
  rfl

/-- Positive original damping remains positive after the mixed-radius time-scale correction. -/
theorem spinMixAmplitude_exp (s u : ℝ) :
    spinMixAmplitude (Real.exp s) u = Real.exp (s + Real.log (spinChartScale (u : ℂ))) := by
  rw [spinMixAmplitude, Real.exp_add, Real.exp_log (spinChartScale_pos _)]

/-- Damped mixed states converge to the lowest-energy orientation with their original spectral values. -/
theorem spinMixedDensity_positive_tendsto (s u : ℝ) (z : ℂ) :
    Tendsto (spinMixedDensity (Real.exp s) u z) atTop
      (nhds (spinMatrix (spinMixRadius u • _root_.Bottcher.stereo 0))) := by
  have h := spinSphereFlow_positive_tendsto (s + Real.log (spinChartScale (u : ℂ))) z
  rw [← spinMixAmplitude_exp] at h
  have hv := h.const_smul (spinMixRadius u)
  have hd := (hasFDerivAt_spinMatrix (spinMixRadius u • _root_.Bottcher.stereo 0)).continuousAt.tendsto.comp hv
  exact hd

end
end GaloisForLFunctions.HTGeometry.SchafferExl
