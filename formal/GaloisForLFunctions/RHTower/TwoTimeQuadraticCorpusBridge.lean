import GaloisForLFunctions.HTGeometry.TwoTimeQuadratic
import GaloisForLFunctions.RHTower.RationalHurwitzLorentzBoost
import GaloisForLFunctions.RHTower.PolyatomicSourceApplications

/-!
# The two-negative-direction form on boost and exchange flows

The Lorentz boost preserves an indefinite Krein form, whereas the
two-negative-direction form has an exact nonzero boost defect. A symmetric
two-channel exchange flow preserves the sum coordinate and changes the
difference coordinate by its exact exponential factor.
-/

namespace RHTower

open scoped Matrix

/-- A boost of the first basis vector changes the negative-definite form by
twice the square of its hyperbolic sine coordinate. -/
theorem twoTimeQuadratic_lorentzBoost_e0 (u : ℝ) :
    GaloisForLFunctions.HTGeometry.twoTimeQuadratic
      (((lorentzBoost u).mulVec ![1, 0]) 0,
       ((lorentzBoost u).mulVec ![1, 0]) 1) =
        -(1 + 2 * Real.sinh u ^ (2 : ℕ)) := by
  rw [lorentzBoost_mulVec_e0]
  simp only [GaloisForLFunctions.HTGeometry.twoTimeQuadratic]
  simp
  nlinarith [Real.cosh_sq_sub_sinh_sq u]

/-- The negative-form boost defect is twice the normalized rational-Hurwitz
seam energy. -/
theorem twoTimeQuadratic_hurwitzBoost_e0 (rho : ℂ) (n : ℕ) :
    GaloisForLFunctions.HTGeometry.twoTimeQuadratic
      (((hurwitzBoost rho n).mulVec ![1, 0]) 0,
       ((hurwitzBoost rho n).mulVec ![1, 0]) 1) =
        -1 - 2 * normalizedScaleSeamEnergy n rho := by
  rw [hurwitzBoost, twoTimeQuadratic_lorentzBoost_e0,
    normalizedScaleSeamEnergy_eq_sinh]
  ring

/-- At modulus two, unchanged two-negative-direction length of the boosted
basis vector is equivalent to the critical horizontal coordinate. -/
theorem twoTimeQuadratic_hurwitzBoost_two_eq_iff (rho : ℂ) :
    GaloisForLFunctions.HTGeometry.twoTimeQuadratic
      (((hurwitzBoost rho 2).mulVec ![1, 0]) 0,
       ((hurwitzBoost rho 2).mulVec ![1, 0]) 1) = -1 ↔
      rho.re = 1 / 2 := by
  rw [twoTimeQuadratic_hurwitzBoost_e0]
  have h : -1 - 2 * normalizedScaleSeamEnergy 2 rho = -1 ↔
      normalizedScaleSeamEnergy 2 rho = 0 := by
    constructor <;> intro h <;> linarith
  exact h.trans (normalizedScaleSeamEnergy_eq_zero_iff rho 2 (Nat.le_refl 2))

/-- Exact negative-form law for the reflection-symmetric two-channel flow. -/
theorem twoTimeQuadratic_reflectedBiHeatMarkovFlow (r t : ℝ) (p : ℝ × ℝ) :
    GaloisForLFunctions.HTGeometry.twoTimeQuadratic
      (reflectedBiHeatMarkovFlow r t p) =
        -((p.1 + p.2) ^ (2 : ℕ) +
          (Real.exp (-2 * r * t) * (p.1 - p.2)) ^ (2 : ℕ)) / 2 := by
  rw [GaloisForLFunctions.HTGeometry.twoTimeQuadratic_sum_difference,
    reflectedBiHeatMarkovFlow_add, reflectedBiHeatMarkovFlow_sub]

/-- The polyatomic exchange flow has the same sum/difference decomposition,
with its selected relaxation rate. -/
theorem twoTimeQuadratic_polyatomicLandauTellerFlow (d t : ℝ) (p : ℝ × ℝ) :
    GaloisForLFunctions.HTGeometry.twoTimeQuadratic
      (polyatomicLandauTellerFlow d t p) =
        -((p.1 + p.2) ^ (2 : ℕ) +
          (Real.exp (-GaloisForLFunctions.HTGeometry.polyatomicLandauTellerRate d * t) *
            (p.1 - p.2)) ^ (2 : ℕ)) / 2 := by
  rw [GaloisForLFunctions.HTGeometry.twoTimeQuadratic_sum_difference,
    polyatomicLandauTellerFlow_conservation, polyatomicLandauTellerFlow_exchange]

/-- With a squared exchange rate and squared forward time, the negative
quadratic form is a monotone quantity for the symmetric Markov flow. -/
theorem twoTimeQuadratic_reflectedBiHeatMarkovFlow_mono
    (r t : ℝ) (p : ℝ × ℝ) :
    GaloisForLFunctions.HTGeometry.twoTimeQuadratic p ≤
      GaloisForLFunctions.HTGeometry.twoTimeQuadratic
        (reflectedBiHeatMarkovFlow (r ^ (2 : ℕ)) (t ^ (2 : ℕ)) p) := by
  rw [twoTimeQuadratic_reflectedBiHeatMarkovFlow,
    GaloisForLFunctions.HTGeometry.twoTimeQuadratic_sum_difference]
  have hrt : 0 ≤ r ^ (2 : ℕ) * t ^ (2 : ℕ) :=
    mul_nonneg (sq_nonneg r) (sq_nonneg t)
  have he : Real.exp (-2 * r ^ (2 : ℕ) * t ^ (2 : ℕ)) ≤ 1 := by
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    nlinarith
  have he0 : 0 ≤ Real.exp (-2 * r ^ (2 : ℕ) * t ^ (2 : ℕ)) :=
    (Real.exp_pos _).le
  have heSq : Real.exp (-2 * r ^ (2 : ℕ) * t ^ (2 : ℕ)) ^ (2 : ℕ) ≤ 1 := by
    nlinarith [mul_nonneg he0 (sub_nonneg.mpr he)]
  have hprod := mul_nonneg (sub_nonneg.mpr heSq) (sq_nonneg (p.1 - p.2))
  nlinarith

/-- The beta-selected polyatomic flow has the same monotone negative form
at every squared forward time. -/
theorem twoTimeQuadratic_polyatomicLandauTellerFlow_mono
    (d t : ℝ) (p : ℝ × ℝ) :
    GaloisForLFunctions.HTGeometry.twoTimeQuadratic p ≤
      GaloisForLFunctions.HTGeometry.twoTimeQuadratic
        (polyatomicLandauTellerFlow d (t ^ (2 : ℕ)) p) := by
  rw [twoTimeQuadratic_polyatomicLandauTellerFlow,
    GaloisForLFunctions.HTGeometry.twoTimeQuadratic_sum_difference]
  have hr : 0 ≤ GaloisForLFunctions.HTGeometry.polyatomicLandauTellerRate d := by
    linarith [GaloisForLFunctions.HTGeometry.polyatomicLandauTeller_rate_bounds d]
  have hrt : 0 ≤ GaloisForLFunctions.HTGeometry.polyatomicLandauTellerRate d *
      t ^ (2 : ℕ) := mul_nonneg hr (sq_nonneg t)
  have he : Real.exp
      (-GaloisForLFunctions.HTGeometry.polyatomicLandauTellerRate d * t ^ (2 : ℕ)) ≤ 1 := by
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    linarith
  have he0 : 0 ≤ Real.exp
      (-GaloisForLFunctions.HTGeometry.polyatomicLandauTellerRate d * t ^ (2 : ℕ)) :=
    (Real.exp_pos _).le
  have heSq : Real.exp
      (-GaloisForLFunctions.HTGeometry.polyatomicLandauTellerRate d * t ^ (2 : ℕ)) ^
        (2 : ℕ) ≤ 1 := by
    nlinarith [mul_nonneg he0 (sub_nonneg.mpr he)]
  have hprod := mul_nonneg (sub_nonneg.mpr heSq) (sq_nonneg (p.1 - p.2))
  nlinarith

end RHTower
