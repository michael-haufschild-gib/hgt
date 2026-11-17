import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.ProbePhaseGeometry
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheHeckeTowerOfAPrimeIsThePeriodQuotient

/-!
# Exact phase sensitivity of individual zero coordinates

A critical-line coordinate lies entirely in the positive reflection sector.
Every off-line coordinate has equal positive and negative masses. Its phase
orbit therefore attains the maximal projective sensitivity allowed by its
Hilbert norm. This is an exact dichotomy, independent of zero location data.
-/

noncomputable section
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk
open ArithmeticCastelnuovoSeveri Zeta23

/-- The unit coordinate at one actual nontrivial zeta zero. -/
def zeroBasis (z : zetaZeroConfig.carrier) : ZeroSpace := by
  classical
  exact lp.single 2 z (1 : ℂ)

theorem norm_zeroBasis (z : zetaZeroConfig.carrier) : ‖zeroBasis z‖ = 1 := by
  classical
  rw [zeroBasis, lp.norm_single (by norm_num), norm_one]

/-- A zero coordinate is fixed by reflection exactly on the critical line. -/
theorem zeroCarrier_reflection_fixed_iff (z : zetaZeroConfig.carrier) :
    reflectCarrier zetaZeroConfig z = z ↔ (z : ℂ).re = 1 / 2 := by
  constructor
  · intro h
    have hre := congrArg (fun q : zetaZeroConfig.carrier => (q : ℂ).re) h
    rw [re_reflectCarrier] at hre
    linarith only [hre]
  · exact reflectCarrier_eq_self

/-- Signed energy of a single coordinate is the indicator of the critical line. -/
theorem reflectionEnergy_zeroBasis (z : zetaZeroConfig.carrier) :
    reflectionEnergy (zeroBasis z) = if (z : ℂ).re = 1 / 2 then 1 else 0 := by
  classical
  rw [reflectionEnergy, zeroBasis, zeroReflection_apply, reflectVec_single,
    inner_single_single]
  simp only [zeroCarrier_reflection_fixed_iff, apply_ite, Complex.one_re, Complex.zero_re]

/-- Off-line coordinates split equally between the two Weil sectors. -/
theorem sector_masses_zeroBasis (z : zetaZeroConfig.carrier) :
    positiveMass (zeroBasis z) = (if (z : ℂ).re = 1 / 2 then 1 else 1 / 2) ∧
      negativeMass (zeroBasis z) = (if (z : ℂ).re = 1 / 2 then 0 else 1 / 2) := by
  classical
  have hs := sector_mass_sum (zeroBasis z)
  rw [norm_zeroBasis, one_pow] at hs
  have he := reflectionEnergy_eq_mass_difference (zeroBasis z)
  rw [reflectionEnergy_zeroBasis] at he
  by_cases hz : (z : ℂ).re = 1 / 2
  · simp only [if_pos hz] at he ⊢
    constructor <;> linarith only [hs, he]
  · simp only [if_neg hz] at he ⊢
    constructor <;> linarith only [hs, he]

/-- Every off-line coordinate has the same maximal projective phase-loss law. -/
theorem zeroBasis_projective_loss (z : zetaZeroConfig.carrier) (u v : Circle) :
    1 - ‖inner ℂ (phaseRotate u (zeroBasis z)) (phaseRotate v (zeroBasis z))‖ ^ 2 =
      if (z : ℂ).re = 1 / 2 then 0 else (1 / 4) * ‖(u : ℂ) - (v : ℂ)‖ ^ 2 := by
  classical
  have h := phaseRotate_projective_loss u v (zeroBasis z)
  rw [norm_zeroBasis, one_pow, (sector_masses_zeroBasis z).1,
    (sector_masses_zeroBasis z).2] at h
  by_cases hz : (z : ℂ).re = 1 / 2
  · simp only [if_pos hz, mul_zero, zero_mul] at h ⊢
    exact h
  · simp only [if_neg hz] at h ⊢
    nlinarith only [h]

/-- A pair of phase translates is projectively indistinguishable exactly at equal phases
or a critical-line zero. -/
theorem zeroBasis_projective_loss_zero_iff (z : zetaZeroConfig.carrier) (u v : Circle) :
    1 - ‖inner ℂ (phaseRotate u (zeroBasis z)) (phaseRotate v (zeroBasis z))‖ ^ 2 = 0 ↔
      (z : ℂ).re = 1 / 2 ∨ u = v := by
  classical
  rw [zeroBasis_projective_loss]
  by_cases hz : (z : ℂ).re = 1 / 2
  · simp only [if_pos hz, hz, true_or]
  · simp only [if_neg hz, hz, false_or, mul_eq_zero,
      show (1 / 4 : ℝ) ≠ 0 by norm_num, false_or, sq_eq_zero_iff, norm_eq_zero, sub_eq_zero]
    exact ⟨Subtype.ext, congrArg Subtype.val⟩

#print axioms reflectionEnergy_zeroBasis
#print axioms sector_masses_zeroBasis
#print axioms zeroBasis_projective_loss
#print axioms zeroBasis_projective_loss_zero_iff

end GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk
