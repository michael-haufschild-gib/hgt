import GaloisForLFunctions.RHTower.XiShiftedAdaptiveArithmeticSourceMovingDegreeOneChamber
import GaloisForLFunctions.RHTower.XiShiftedAdaptiveDegreeOneAdmittedKernelPositivity

/-!
# Canonical degree-one admission selects the positive source chamber

Moving monic degree-one amplitudes can carry a cofinally negative literal arithmetic source.
Canonical Hankel admission does not: its scaled root converges to the arcsine mean `1/2`, and the
corresponding adaptive source recession constant is `11/64 > 0`.

This is an admission-sensitive source theorem.  It does not use pointwise mixed-kernel positivity,
a fixed reporter, or reflection aggregation.
-/

open Filter Polynomial Topology

namespace RHTower

noncomputable section

/-- Canonical degree-one null root, in its natural dimensionless mass coordinate, converges to the
arcsine mean. -/
theorem tendsto_scaled_xiShiftedDegreeOneNullRoot_squareParam :
    Tendsto
      (fun w : ℝ => w ^ 2 * xiShiftedDegreeOneNullRoot (w ^ 2))
      atTop (nhds (1 / 2 : ℝ)) := by
  have h0 := tendsto_scaled_re_xiShiftedReciprocalMoment_squareParam 0
  have h1 := tendsto_scaled_re_xiShiftedReciprocalMoment_squareParam 1
  have hdiv := h1.div h0 (by
    norm_num [GaloisForLFunctions.HTGeometry.normalizedCentralBinom,
      Nat.centralBinom, Nat.choose])
  have hlim :
      GaloisForLFunctions.HTGeometry.normalizedCentralBinom 1 /
          GaloisForLFunctions.HTGeometry.normalizedCentralBinom 0 =
        (1 / 2 : ℝ) := by
    norm_num [GaloisForLFunctions.HTGeometry.normalizedCentralBinom,
      Nat.centralBinom, Nat.choose]
  rw [hlim] at hdiv
  apply hdiv.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with w hw
  have hw0 : w ≠ 0 := ne_of_gt (lt_trans zero_lt_one hw)
  have hlog : Real.log w ≠ 0 := ne_of_gt (Real.log_pos hw)
  have hm0 : (xiShiftedReciprocalMoment (w ^ 2) 0).re ≠ 0 := by
    simpa [xiShiftedCassiniResponse] using
      (xiShiftedCassiniResponse_pos (sq_pos_of_pos (lt_trans zero_lt_one hw))).ne'
  rw [xiShiftedDegreeOneNullRoot, xiShiftedCassiniResponse]
  simp only [Pi.div_apply]
  field_simp [hw0, hlog, hm0]
  ring

/-- Canonical degree-one null polynomial is the scaled moving amplitude at its endogenous root. -/
theorem xiShiftedDegreeOneNullPolynomial_eq_scaledAmplitude
    {w : ℝ} (hw : w ≠ 0) :
    xiShiftedDegreeOneNullPolynomial (w ^ 2) =
      xiShiftedAdaptiveScaledDegreeOneAmplitude
        (w ^ 2 * xiShiftedDegreeOneNullRoot (w ^ 2)) w := by
  simp only [xiShiftedDegreeOneNullPolynomial,
    xiShiftedAdaptiveScaledDegreeOneAmplitude]
  congr 1
  field_simp [hw]

/-- **Canonical admitted-source recession.**  The literal completed arithmetic source selected by
the moving first Hankel null flag has exact positive limit `11/64`. -/
theorem tendsto_scaled_xiShiftedDegreeOneAdmittedArithmeticSource :
    Tendsto
      (fun w : ℝ => w ^ 9 / Real.log w *
        xiShiftedAdaptiveMixedCompletedArithmeticSource w
          (xiShiftedDegreeOneNullPolynomial (w ^ 2)))
      atTop (nhds (11 / 64 : ℝ)) := by
  let R : ℝ → ℝ := fun w => w ^ 2 * xiShiftedDegreeOneNullRoot (w ^ 2)
  have hR : Tendsto R atTop (nhds (1 / 2 : ℝ)) := by
    simpa [R] using tendsto_scaled_xiShiftedDegreeOneNullRoot_squareParam
  have h2 := tendsto_scaled_re_xiShiftedReciprocalMoment_squareParam 2
  have h3 := tendsto_scaled_re_xiShiftedReciprocalMoment_squareParam 3
  have h4 := tendsto_scaled_re_xiShiftedReciprocalMoment_squareParam 4
  have ht2 := (hR.pow 2).mul h2
  have ht3 := (hR.const_mul (-3)).mul h3
  have ht4 := h4.const_mul 2
  have h := (ht2.add ht3).add ht4
  have hlim :
      (1 / 2 : ℝ) ^ 2 *
          GaloisForLFunctions.HTGeometry.normalizedCentralBinom 2 +
        (-3 * (1 / 2 : ℝ)) *
          GaloisForLFunctions.HTGeometry.normalizedCentralBinom 3 +
        2 * GaloisForLFunctions.HTGeometry.normalizedCentralBinom 4 =
          (11 / 64 : ℝ) := by
    norm_num [GaloisForLFunctions.HTGeometry.normalizedCentralBinom,
      Nat.centralBinom, Nat.choose]
  rw [hlim] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with w hw
  have hw0 : w ≠ 0 := ne_of_gt (lt_trans zero_lt_one hw)
  rw [xiShiftedDegreeOneNullPolynomial_eq_scaledAmplitude hw0]
  rw [xiShiftedAdaptiveMixedCompletedArithmeticSource_scaledDegreeOne
    (by linarith : 1 / 2 < w)]
  have hlog : Real.log w ≠ 0 := ne_of_gt (Real.log_pos hw)
  field_simp [hw0, hlog]
  ring

/-- Canonical moving degree-one admission makes the actual arithmetic source strictly positive
sufficiently far right. -/
theorem xiShiftedDegreeOneAdmittedArithmeticSource_eventually_pos :
    ∀ᶠ w : ℝ in atTop,
      0 < xiShiftedAdaptiveMixedCompletedArithmeticSource w
        (xiShiftedDegreeOneNullPolynomial (w ^ 2)) := by
  have hlimit : (0 : ℝ) < 11 / 64 := by norm_num
  have hscaled := tendsto_scaled_xiShiftedDegreeOneAdmittedArithmeticSource.eventually
    (Ioi_mem_nhds hlimit)
  filter_upwards [hscaled, eventually_gt_atTop (1 : ℝ)] with w hs hw
  have hscale : 0 < w ^ 9 / Real.log w :=
    div_pos (pow_pos (lt_trans zero_lt_one hw) _) (Real.log_pos hw)
  rcases mul_pos_iff.mp hs with h | h
  · exact h.2
  · exact (not_lt_of_ge hscale.le h.1).elim

end

end RHTower
