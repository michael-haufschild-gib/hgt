import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.ProbeSectorMassPairings
import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.ProbePhaseDynamics
import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.ProbeZeroPhaseSensitivity
import GaloisForLFunctions.HTGeometry.ConstitutivePolarAmplitudeFisherPhase

/-!
# Berry holonomy of the actual zero-reflection orbit

Differentiating the orbital phase gives the negative-sector mass as its
Berry connection. Integrating around a full period yields holonomy `-1`
for an off-line coordinate and `1` for a fixed reflection coordinate.
-/

noncomputable section
open scoped BigOperators Classical
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk
open ArithmeticCastelnuovoSeveri Zeta23

/-- Normalized reflection-sector masses, with zero assigned to the zero vector. -/
def sectorProbability (x : ZeroSpace) : Fin 2 → ℝ :=
  ![positiveMass x / ‖x‖ ^ 2, negativeMass x / ‖x‖ ^ 2]

theorem sectorProbability_sum (x : ZeroSpace) :
    ∑ i, sectorProbability x i = if x = 0 then 0 else 1 := by
  classical
  simp only [sectorProbability, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    ← add_div, sector_mass_sum]
  by_cases hx : x = 0
  · simp only [hx, if_true, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_div]
  · rw [if_neg hx, div_self (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))]

theorem sectorProbability_nonneg (x : ZeroSpace) (i : Fin 2) :
    0 ≤ sectorProbability x i := by
  fin_cases i <;>
    exact div_nonneg (sq_nonneg _) (sq_nonneg _)

private theorem sector_velocity_mean (x : ZeroSpace) :
    HTGeometry.velMean (sectorProbability x) HTGeometry.twoLevelVel =
      negativeMass x / ‖x‖ ^ 2 := by
  simp only [HTGeometry.velMean, sectorProbability, HTGeometry.twoLevelVel,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Int.cast_zero, Int.cast_one, mul_zero, mul_one, zero_add]

/-- The actual tangent pairing is the imaginary negative-sector mass. -/
theorem timePhase_tangent_pairing (t : ℝ) (x : ZeroSpace) :
    inner ℂ (timePhase t x) (deriv (fun s : ℝ => timePhase s x) t) =
      Complex.I * (negativeMass x : ℂ) := by
  rw [(timePhase_hasDerivAt t x).deriv, inner_smul_right, inner_negativePart_eq_mass]
  have hm : negativeMass (timePhase t x) = negativeMass x := by
    simp only [negativeMass, timePhase, negativePart_phaseRotate, norm_smul,
      Circle.norm_coe, one_mul]
  rw [hm]

/-- Berry connection read directly from the differentiated Hilbert-space orbit. -/
def phaseBerryConnection (t : ℝ) (x : ZeroSpace) : ℝ :=
  (inner ℂ (timePhase t x) (deriv (fun s : ℝ => timePhase s x) t)).im /
    ‖timePhase t x‖ ^ 2

/-- The actual connection is constant and equals the negative-sector probability. -/
theorem phaseBerryConnection_value (t : ℝ) (x : ZeroSpace) :
    phaseBerryConnection t x = negativeMass x / ‖x‖ ^ 2 := by
  rw [phaseBerryConnection, timePhase_tangent_pairing]
  have hn : ‖timePhase t x‖ = ‖x‖ := (phaseRotationEquiv (Circle.exp t)).norm_map x
  rw [hn]
  simp only [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, one_mul, zero_add]

/-- The existing two-level holonomy evaluated on the actual Weil sector masses. -/
def phaseBerryHolonomy (x : ZeroSpace) : ℂ :=
  HTGeometry.berryHolonomy (sectorProbability x) HTGeometry.twoLevelVel

/-- Sector holonomy is exactly the integral of the actual orbit connection. -/
theorem phaseBerryHolonomy_eq_exp_integral (x : ZeroSpace) :
    phaseBerryHolonomy x = Complex.exp
      (Complex.I * ((∫ t : ℝ in 0..(2 * Real.pi), phaseBerryConnection t x : ℝ) : ℂ)) := by
  rw [phaseBerryHolonomy, HTGeometry.berryHolonomy_eq_exp_integral, sector_velocity_mean]
  simp_rw [phaseBerryConnection_value]

/-- The full-loop phase depends only on the negative-sector mass fraction. -/
theorem phaseBerryHolonomy_value (x : ZeroSpace) :
    phaseBerryHolonomy x = Complex.exp
      (Complex.I * ((2 * Real.pi * (negativeMass x / ‖x‖ ^ 2) : ℝ) : ℂ)) := by
  rw [phaseBerryHolonomy, HTGeometry.berryHolonomy, sector_velocity_mean]

/-- A single off-line zero carries the nontrivial two-level Berry holonomy. -/
theorem phaseBerryHolonomy_zeroBasis (z : zetaZeroConfig.carrier) :
    phaseBerryHolonomy (zeroBasis z) = if (z : ℂ).re = 1 / 2 then 1 else -1 := by
  classical
  by_cases hz : (z : ℂ).re = 1 / 2
  · rw [if_pos hz, phaseBerryHolonomy_value, norm_zeroBasis,
      (sector_masses_zeroBasis z).2, if_pos hz]
    simp only [one_pow, zero_div, mul_zero, Complex.ofReal_zero, Complex.exp_zero]
  · rw [if_neg hz, phaseBerryHolonomy]
    have hp : sectorProbability (zeroBasis z) = HTGeometry.twoLevelProb := by
      rw [sectorProbability, norm_zeroBasis, (sector_masses_zeroBasis z).1,
        (sector_masses_zeroBasis z).2, if_neg hz]
      simp only [if_neg hz, one_pow, div_one, HTGeometry.twoLevelProb]
    rw [hp]
    exact HTGeometry.twoLevel_example.2.2.2

#print axioms timePhase_tangent_pairing
#print axioms phaseBerryConnection_value
#print axioms phaseBerryHolonomy_eq_exp_integral
#print axioms phaseBerryHolonomy_value
#print axioms phaseBerryHolonomy_zeroBasis
end GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk
