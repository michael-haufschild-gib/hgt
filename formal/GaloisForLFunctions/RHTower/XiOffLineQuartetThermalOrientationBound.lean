import GaloisForLFunctions.RHTower.XiEndpointOffLineQuartetHeightGap
import GaloisForLFunctions.RHTower.XiGuinandWeilRectangularGammaPolarSourceLaw

/-!
# Off-line-quartet thermal orientation bound

The four-copy endpoint budget forces every off-critical Xi zero above squared ordinate `85`.
Together with the open critical strip, this makes the transverse part of every centered
reciprocal-square coordinate at most `1 / 84` of its positive thermal square.  Summation sharpens
the unconditional source/thermal interval and identifies the fixed-window prime--polar
negative-abscissa target with the zero fibre of this small orientation energy.
-/

open Complex Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- **Off-line-quartet atomwise orientation bound.**  The transverse reciprocal-square energy of
every Xi zero is at most one eighty-fourth of its positive thermal-node square.  On-line atoms
vanish; off-line atoms use the exact four-copy endpoint height amplification. -/
theorem xiThermalOrientationTerm_le_one_over_eightyFour_node_sq
    (q : XiZeroCopy) :
    (xiZeroCopyReciprocalSquare q).im ^ (2 : ℕ) ≤
      (1 / 84 : ℝ) * xiThermalNode q ^ (2 : ℕ) := by
  by_cases hoff : (q.1 : ℂ).re = 1 / 2
  · rw [xiZeroCopyReciprocalSquare_im_formula, hoff]
    norm_num
    positivity
  · let u : ℝ := ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ)
    let v : ℝ := (q.1 : ℂ).im ^ (2 : ℕ)
    let D : ℝ := (u + v) ^ (2 : ℕ)
    have hu0 : 0 ≤ u := by dsimp [u]; positivity
    have hu : u < 1 / 4 :=
      xi_divisor_support_centered_re_sq_lt_quarter q.1
    have hv : 85 < v := by
      simpa only [v] using xiZeroCopy_offLine_eightyFive_lt_im_sq q hoff
    have hv0 : 0 < v := by linarith
    have h340 : 340 * u < v := by nlinarith
    have hprod : 0 ≤ v * (v - 340 * u) :=
      mul_nonneg hv0.le (sub_nonneg.mpr h340.le)
    have hcore : 4 * u * v ≤ (1 / 84 : ℝ) * (v - u) ^ (2 : ℕ) := by
      nlinarith [mul_nonneg hu0 hv0.le]
    have hD : 0 < D := by dsimp [D]; positivity
    rw [xiThermalNode, xiZeroCopyReciprocalSquare_re_formula,
      xiZeroCopyReciprocalSquare_im_formula]
    change (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im /
          (((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) + (q.1 : ℂ).im ^ (2 : ℕ)) ^ (2 : ℕ)) ^ (2 : ℕ) ≤
      (1 / 84 : ℝ) *
        (((q.1 : ℂ).im ^ (2 : ℕ) - ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ)) /
          (((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) + (q.1 : ℂ).im ^ (2 : ℕ)) ^ (2 : ℕ)) ^ (2 : ℕ)
    rw [show ((q.1 : ℂ).re - 1 / 2) ^ (2 : ℕ) = u by rfl,
      show (q.1 : ℂ).im ^ (2 : ℕ) = v by rfl,
      show (u + v) ^ (2 : ℕ) = D by rfl]
    rw [div_pow, div_pow]
    rw [show (1 / 84 : ℝ) * ((v - u) ^ (2 : ℕ) / D ^ (2 : ℕ)) =
        ((1 / 84 : ℝ) * (v - u) ^ (2 : ℕ)) / D ^ (2 : ℕ) by ring]
    apply (div_le_div_iff_of_pos_right (sq_pos_of_pos hD)).2
    calc
      (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ (2 : ℕ) =
          4 * u * v := by
        dsimp [u, v]
        ring
      _ ≤ (1 / 84 : ℝ) * (v - u) ^ (2 : ℕ) := hcore

/-- The complete thermal orientation energy is at most one eighty-fourth of the positive thermal
second moment. -/
theorem xiThermalOrientationEnergy_le_one_over_eightyFour_secondMoment :
    xiThermalOrientationEnergy ≤
      (1 / 84 : ℝ) * xiThermalSecondMoment := by
  rw [xiThermalOrientationEnergy, xiThermalSecondMoment, ← tsum_mul_left]
  exact summable_xiThermalOrientationTerm.tsum_le_tsum
    (fun q => xiThermalOrientationTerm_le_one_over_eightyFour_node_sq q)
    (summable_xiThermalNode_sq.mul_left (1 / 84 : ℝ))

/-- The prime--Gamma source retains at least `83 / 84` of the positive thermal second moment. -/
theorem eightyThree_over_eightyFour_thermalSecondMoment_le_source :
    (83 / 84 : ℝ) * xiThermalSecondMoment ≤
      normalizedPrimeArchMoment 1 := by
  have hgap := xiThermalSecondMoment_sub_orientationEnergy_eq_source
  have hbound := xiThermalOrientationEnergy_le_one_over_eightyFour_secondMoment
  nlinarith

/-- The unconditional thermal/source multiplicative gap is at most `84 / 83`. -/
theorem xiThermalSecondMoment_le_eightyFour_over_eightyThree_source :
    xiThermalSecondMoment ≤
      (84 / 83 : ℝ) * normalizedPrimeArchMoment 1 := by
  have h := eightyThree_over_eightyFour_thermalSecondMoment_le_source
  nlinarith

/-- The first coordinate of the positive thermal tower is already exactly the zeroth
prime--Gamma source moment, without RH. -/
theorem xiThermalPositiveMoment_zero_eq_source :
    xiThermalPositiveMoment 0 = normalizedPrimeArchMoment 0 := by
  have hsum := summable_xiZeroCopyReciprocalSquare
  calc
    xiThermalPositiveMoment 0 =
        ∑' q : XiZeroCopy, (xiZeroCopyReciprocalSquare q).re := by
      simp [xiThermalPositiveMoment, xiThermalNode]
    _ = (∑' q : XiZeroCopy, xiZeroCopyReciprocalSquare q).re := by
      rw [Complex.re_tsum hsum]
    _ = (xiCentralReciprocalMoment 0).re := by
      congr 1
      simpa using tsum_xiZeroCopyReciprocalSquare_pow 0
    _ = normalizedPrimeArchMoment 0 := by
      have hsource := primeArchSourceMoment_eq_xiCentralReciprocalMoment 0
      simpa [normalizedPrimeArchMoment, normalizedPrimeArchMomentGerm] using
        congrArg Complex.re hsource.symm

/-- The finite KMS truncations converge unconditionally to the source value in coordinate zero.
Thus the first unresolved thermodynamic coordinate is exactly coordinate one. -/
theorem tendsto_xiThermalTruncation_zero_source :
    Tendsto (fun N => xiThermalTruncation N 0) atTop
      (nhds (normalizedPrimeArchMoment 0)) := by
  have hzero := (tendsto_pi_nhds.mp
    tendsto_xiThermalTruncation_positiveMoment) 0
  rwa [xiThermalPositiveMoment_zero_eq_source] at hzero

/-- The Gamma-free fixed-window negative-abscissa target is exactly vanishing of the thermal
orientation energy. -/
theorem rectangularPrimePolarSource_negativeAbscissa_le_one_iff_orientationEnergy_zero
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2) :
    LSeries.abscissaOfAbsConv
          (rectangularPrimePolarSourceTailNegativeDirichletCoefficient L N) ≤
        ((1 : ℝ) : EReal) ↔
      xiThermalOrientationEnergy = 0 := by
  exact
    (riemannHypothesis_iff_rectangularPrimePolarSource_negativeAbscissa_le_one
      hL hN).symm.trans xiThermalOrientationEnergy_eq_zero_iff_rh.symm

/-- The Gamma-free negative-abscissa target is exactly the missing reverse scalar inequality
between the positive thermal second moment and the source value. -/
theorem rectangularPrimePolarSource_negativeAbscissa_le_one_iff_thermalSecondMoment_le_source
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2) :
    LSeries.abscissaOfAbsConv
          (rectangularPrimePolarSourceTailNegativeDirichletCoefficient L N) ≤
        ((1 : ℝ) : EReal) ↔
      xiThermalSecondMoment ≤ normalizedPrimeArchMoment 1 := by
  exact
    (riemannHypothesis_iff_rectangularPrimePolarSource_negativeAbscissa_le_one
      hL hN).symm.trans xiThermalSecondMoment_le_source_iff_rh.symm

/-- The Gamma-free negative-abscissa target is exactly convergence of the finite KMS second
moments to the source-defined second value.  Coordinate zero converges unconditionally by the
preceding theorem. -/
theorem rectangularPrimePolarSource_negativeAbscissa_le_one_iff_thermalSecondMoment_tendsto
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2) :
    LSeries.abscissaOfAbsConv
          (rectangularPrimePolarSourceTailNegativeDirichletCoefficient L N) ≤
        ((1 : ℝ) : EReal) ↔
      Tendsto (fun M => xiThermalTruncation M 1) atTop
        (nhds (normalizedPrimeArchMoment 1)) := by
  exact
    (riemannHypothesis_iff_rectangularPrimePolarSource_negativeAbscissa_le_one
      hL hN).symm.trans tendsto_xiThermalTruncation_one_iff_rh.symm

end

end RHTower
