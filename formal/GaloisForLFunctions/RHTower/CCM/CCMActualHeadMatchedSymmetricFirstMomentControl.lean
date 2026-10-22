import GaloisForLFunctions.RHTower.CCM.CCMActualHeadMatchedCosinePhaseNormalForm

/-!
# First-moment control of matched symmetric prime--polar cells

Mass matching leaves two actual-head currents.  The asymmetric Suzuki current was already known to
be absolutely summable by a quadratic aperture gain.  The even symmetric residual still appeared
to require the unavailable full physical derivative.

This module proves that one fractional step is enough.  The exact matched radius and the global
Lipschitz bound for cosine give

`profile_n(xi) ≤ pi * w_n^(2 : ℕ) / exp(log(n)/2) * |xi|`.

The arithmetic coefficient is dominated by `Lambda(n) log(n) n^(-3/2)` and is summable.  Hence a
single finite Fourier first moment of an actual head makes both the symmetric residual and the full
mass-matched prime-minus-polar cell family absolutely summable.  This crosses the all-prime
convergence wall without assuming the nonintegrable full derivative and without severing any
prime atom from its literal matched polar cell.  No sign claim is made.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct InnerProductSpace BigOperators ComplexConjugate

noncomputable section

namespace RHTower

private lemma two_sub_two_cos_le_two_mul_abs (x : ℝ) :
    2 - 2 * Real.cos x ≤ 2 * |x| := by
  calc
    2 - 2 * Real.cos x = 2 * (1 - Real.cos x) := by ring
    _ ≤ 2 * |1 - Real.cos x| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) (by norm_num)
    _ = 2 * |Real.cos x - Real.cos 0| := by
      rw [Real.cos_zero, abs_sub_comm]
    _ ≤ 2 * |x - 0| :=
      mul_le_mul_of_nonneg_left (Real.abs_cos_sub_cos_le x 0) (by norm_num)
    _ = 2 * |x| := by simp

private lemma arsinh_le_self_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    Real.arsinh x ≤ x := by
  calc
    Real.arsinh x ≤ Real.sinh (Real.arsinh x) :=
      Real.self_le_sinh_iff.mpr (Real.arsinh_nonneg_iff.mpr hx)
    _ = x := Real.sinh_arsinh x

/-- The total even polar coefficient in one matched cell is exactly half its critical Mellin
atom weight. -/
theorem integral_ccmActualHeadMatchedCoshCoefficient_eq_half_weight (n : ℕ) :
    (∫ r in (0 : ℝ)..ccmActualHeadMatchedPrimePolarRadius n,
        Real.exp (Real.log n / 2) * Real.cosh (r / 2)) =
      criticalMellinAtomWeight n / 2 := by
  let ρ := ccmActualHeadMatchedPrimePolarRadius n
  let A := Real.exp (Real.log n / 2)
  let P : ℝ → ℝ := fun r => 2 * A * Real.sinh (r / 2)
  have hderiv : ∀ r ∈ uIcc (0 : ℝ) ρ,
      HasDerivAt P (A * Real.cosh (r / 2)) r := by
    intro r hr
    have hbase := (Real.hasDerivAt_sinh (r / 2)).comp r
      ((hasDerivAt_id r).div_const 2)
    change HasDerivAt (fun x : ℝ => 2 * A * Real.sinh (x / 2)) _ r
    apply (hbase.const_mul (2 * A)).congr_deriv
    ring
  have hint : IntervalIntegrable (fun r : ℝ => A * Real.cosh (r / 2))
      volume 0 ρ :=
    (by fun_prop : Continuous fun r : ℝ =>
      A * Real.cosh (r / 2)).intervalIntegrable _ _
  change (∫ r in (0 : ℝ)..ρ, A * Real.cosh (r / 2)) = _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  dsimp only [P]
  simp only [zero_div, Real.sinh_zero, mul_zero, sub_zero]
  unfold ρ ccmActualHeadMatchedPrimePolarRadius
  rw [show (2 * Real.arsinh
      (criticalMellinAtomWeight n / (4 * Real.exp (Real.log n / 2)))) / 2 =
      Real.arsinh
        (criticalMellinAtomWeight n / (4 * Real.exp (Real.log n / 2))) by ring,
    Real.sinh_arsinh]
  dsimp only [A]
  field_simp [Real.exp_ne_zero]
  ring

/-- The exact matched radius is at most its linearized critical Mellin aperture. -/
theorem ccmActualHeadMatchedPrimePolarRadius_le_weight_div (n : ℕ) :
    ccmActualHeadMatchedPrimePolarRadius n ≤
      criticalMellinAtomWeight n /
        (2 * Real.exp (Real.log n / 2)) := by
  let z := criticalMellinAtomWeight n /
    (4 * Real.exp (Real.log n / 2))
  have hz : 0 ≤ z := by
    dsimp only [z]
    exact div_nonneg (criticalMellinAtomWeight_nonneg_cCMActualHeadWallGramSignedProducer n)
      (mul_nonneg (by norm_num) (Real.exp_pos _).le)
  unfold ccmActualHeadMatchedPrimePolarRadius
  change 2 * Real.arsinh z ≤ _
  have h := arsinh_le_self_of_nonneg hz
  calc
    2 * Real.arsinh z ≤ 2 * z :=
      mul_le_mul_of_nonneg_left h (by norm_num)
    _ = criticalMellinAtomWeight n /
        (2 * Real.exp (Real.log n / 2)) := by
      dsimp only [z]
      field_simp [Real.exp_ne_zero]
      ring

/-- **Fractional matched-cell gain.**  The nonnegative even cosine profile is bounded by the
summable quadratic prime aperture times one absolute Fourier frequency. -/
theorem ccmActualHeadMatchedCosinePhaseProfile_le_firstMomentKernel
    (n : ℕ) (xi : ℝ) :
    ccmActualHeadMatchedCosinePhaseProfile n xi ≤
      Real.pi * criticalMellinAtomWeight n ^ 2 /
        Real.exp (Real.log n / 2) * |xi| := by
  let ρ := ccmActualHeadMatchedPrimePolarRadius n
  let A := Real.exp (Real.log n / 2)
  let w := criticalMellinAtomWeight n
  have hρ : 0 ≤ ρ := ccmActualHeadMatchedPrimePolarRadius_nonneg n
  have hA : 0 ≤ A := (Real.exp_pos _).le
  have hpoint : ∀ r ∈ Icc (0 : ℝ) ρ,
      A * Real.cosh (r / 2) *
          (2 - 2 * Real.cos (2 * Real.pi * r * xi)) ≤
        A * Real.cosh (r / 2) * (4 * Real.pi * ρ * |xi|) := by
    intro r hr
    have hcos := two_sub_two_cos_le_two_mul_abs
      (2 * Real.pi * r * xi)
    have hr0 : 0 ≤ r := hr.1
    have hrρ : r ≤ ρ := hr.2
    have hpi : 0 ≤ Real.pi := Real.pi_pos.le
    have habs : |2 * Real.pi * r * xi| = 2 * Real.pi * r * |xi| := by
      rw [abs_mul, abs_mul, abs_mul,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_of_nonneg hpi, abs_of_nonneg hr0]
    rw [habs] at hcos
    have hphase : 2 - 2 * Real.cos (2 * Real.pi * r * xi) ≤
        4 * Real.pi * ρ * |xi| := by
      calc
        _ ≤ 2 * (2 * Real.pi * r * |xi|) := hcos
        _ = (4 * Real.pi * |xi|) * r := by ring
        _ ≤ (4 * Real.pi * |xi|) * ρ :=
          mul_le_mul_of_nonneg_left hrρ (by positivity)
        _ = 4 * Real.pi * ρ * |xi| := by ring
    exact mul_le_mul_of_nonneg_left hphase
      (mul_nonneg hA (Real.cosh_pos _).le)
  have hleftInt : IntervalIntegrable (fun r : ℝ =>
      A * Real.cosh (r / 2) *
        (2 - 2 * Real.cos (2 * Real.pi * r * xi))) volume 0 ρ :=
    (by fun_prop : Continuous fun r : ℝ =>
      A * Real.cosh (r / 2) *
        (2 - 2 * Real.cos (2 * Real.pi * r * xi))).intervalIntegrable _ _
  have hrightInt : IntervalIntegrable (fun r : ℝ =>
      A * Real.cosh (r / 2) * (4 * Real.pi * ρ * |xi|)) volume 0 ρ :=
    (by fun_prop : Continuous fun r : ℝ =>
      A * Real.cosh (r / 2) *
        (4 * Real.pi * ρ * |xi|)).intervalIntegrable _ _
  have hint := intervalIntegral.integral_mono_on hρ hleftInt hrightInt hpoint
  unfold ccmActualHeadMatchedCosinePhaseProfile
  change (∫ r in (0 : ℝ)..ρ,
      A * Real.cosh (r / 2) *
        (2 - 2 * Real.cos (2 * Real.pi * r * xi))) ≤ _
  calc
    _ ≤ ∫ r in (0 : ℝ)..ρ,
        A * Real.cosh (r / 2) * (4 * Real.pi * ρ * |xi|) := hint
    _ = (4 * Real.pi * ρ * |xi|) * (w / 2) := by
      rw [show (fun r : ℝ => A * Real.cosh (r / 2) *
          (4 * Real.pi * ρ * |xi|)) =
          fun r : ℝ => (4 * Real.pi * ρ * |xi|) *
            (A * Real.cosh (r / 2)) by funext r; ring,
        intervalIntegral.integral_const_mul,
        integral_ccmActualHeadMatchedCoshCoefficient_eq_half_weight]
    _ ≤ (4 * Real.pi * (w / (2 * A)) * |xi|) * (w / 2) := by
      have hrad : ρ ≤ w / (2 * A) := by
        simpa only [ρ, w, A] using
          ccmActualHeadMatchedPrimePolarRadius_le_weight_div n
      have hw : 0 ≤ w := by
        dsimp only [w]
        exact criticalMellinAtomWeight_nonneg_cCMActualHeadWallGramSignedProducer n
      have hnonneg : 0 ≤ 4 * Real.pi * |xi| * (w / 2) :=
        mul_nonneg (mul_nonneg (by positivity) (abs_nonneg xi))
          (div_nonneg hw (by norm_num))
      calc
        (4 * Real.pi * ρ * |xi|) * (w / 2) =
            (4 * Real.pi * |xi| * (w / 2)) * ρ := by ring
        _ ≤ (4 * Real.pi * |xi| * (w / 2)) * (w / (2 * A)) :=
          mul_le_mul_of_nonneg_left hrad hnonneg
        _ = (4 * Real.pi * (w / (2 * A)) * |xi|) * (w / 2) := by ring
    _ = Real.pi * w ^ 2 / A * |xi| := by
      field_simp [show A ≠ 0 by
        dsimp only [A]
        exact Real.exp_ne_zero _]
      ring

/-- Absolute first moment of the physical head's Fourier density. -/
def ccmActualHeadFourierFirstMoment (f : SoninL2) : ℝ :=
  ∫ xi : ℝ, |xi| * ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2

theorem ccmActualHeadFourierFirstMoment_nonneg (f : SoninL2) :
    0 ≤ ccmActualHeadFourierFirstMoment f := by
  unfold ccmActualHeadFourierFirstMoment
  exact integral_nonneg fun xi => mul_nonneg (abs_nonneg xi) (sq_nonneg _)

/-- One matched symmetric residual is controlled by the summable quadratic prime aperture times
the head's first Fourier moment. -/
theorem abs_ccmActualHeadMatchedSymmetricCellResidual_le_firstMoment
    (f : SoninL2)
    (hf : Integrable (fun xi : ℝ =>
      |xi| * ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2))
    (n : ℕ) :
    |ccmActualHeadMatchedSymmetricCellResidual n f| ≤
      2 * Real.pi *
        (criticalMellinAtomWeight n ^ 2 /
          Real.exp (Real.log n / 2)) *
            ccmActualHeadFourierFirstMoment f := by
  let C : ℝ := Real.pi * criticalMellinAtomWeight n ^ 2 /
    Real.exp (Real.log n / 2)
  let D : ℝ → ℝ := fun xi =>
    |xi| * ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2
  let F : ℝ → ℝ := fun xi =>
    Real.cos (2 * Real.pi * Real.log n * xi) *
      ccmActualHeadMatchedCosinePhaseProfile n xi *
      ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  have hD : Integrable D := by simpa only [D] using hf
  have hF : Integrable F := by
    simpa only [F] using
      integrable_ccmActualHeadMatchedCosinePhaseProfile_mul_density n f
  have hpoint : ∀ xi : ℝ, |F xi| ≤ C * D xi := by
    intro xi
    have hprofile0 := ccmActualHeadMatchedCosinePhaseProfile_nonneg n xi
    have hprofile :=
      ccmActualHeadMatchedCosinePhaseProfile_le_firstMomentKernel n xi
    have hcos := Real.abs_cos_le_one
      (2 * Real.pi * Real.log n * xi)
    have hnorm : 0 ≤ ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2 := sq_nonneg _
    dsimp only [F, C, D]
    rw [abs_mul, abs_mul, abs_of_nonneg hprofile0,
      abs_of_nonneg hnorm]
    calc
      |Real.cos (2 * Real.pi * Real.log n * xi)| *
          ccmActualHeadMatchedCosinePhaseProfile n xi *
          ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2 ≤
        1 * (Real.pi * criticalMellinAtomWeight n ^ 2 /
          Real.exp (Real.log n / 2) * |xi|) *
          ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2 := by gcongr
      _ = (Real.pi * criticalMellinAtomWeight n ^ 2 /
          Real.exp (Real.log n / 2)) *
          (|xi| * ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2) := by ring
  have hInt : (∫ xi : ℝ, |F xi|) ≤ ∫ xi : ℝ, C * D xi := by
    exact integral_mono hF.norm (hD.const_mul C) hpoint
  rw [ccmActualHeadMatchedSymmetricCellResidual_eq_cosinePhaseProfile]
  change |-2 * ∫ xi : ℝ, F xi| ≤ _
  calc
    |-2 * ∫ xi : ℝ, F xi| = 2 * |∫ xi : ℝ, F xi| := by
      rw [abs_mul]
      norm_num
    _ ≤ 2 * ∫ xi : ℝ, |F xi| :=
      mul_le_mul_of_nonneg_left abs_integral_le_integral_abs (by norm_num)
    _ ≤ 2 * ∫ xi : ℝ, C * D xi :=
      mul_le_mul_of_nonneg_left hInt (by norm_num)
    _ = 2 * Real.pi *
        (criticalMellinAtomWeight n ^ 2 /
          Real.exp (Real.log n / 2)) *
            ccmActualHeadFourierFirstMoment f := by
      rw [integral_const_mul]
      dsimp only [C, D, ccmActualHeadFourierFirstMoment]
      ring

theorem summable_criticalMellinAtomWeight_sq_div_exp_half_log :
    Summable (fun n : ℕ =>
      criticalMellinAtomWeight n ^ 2 /
        Real.exp (Real.log n / 2)) := by
  have hbase := summable_vonMangoldt_logPow
    (σ := (3 / 2 : ℝ)) (by norm_num) 1
  apply Summable.of_norm_bounded hbase
  intro n
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · simpa using criticalMellinAtomWeight_sq_div_exp_le_logMajorant n
  · exact div_nonneg (sq_nonneg _) (Real.exp_pos _).le

/-- The complete even matched-cell residual is absolutely summable for every actual head with one
finite Fourier moment. -/
theorem summable_ccmActualHeadMatchedSymmetricCellResidual_of_firstMoment
    (f : SoninL2)
    (hf : Integrable (fun xi : ℝ =>
      |xi| * ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2)) :
    Summable (fun n : ℕ => ccmActualHeadMatchedSymmetricCellResidual n f) := by
  have hmajor := summable_criticalMellinAtomWeight_sq_div_exp_half_log.mul_left
    (2 * Real.pi * ccmActualHeadFourierFirstMoment f)
  apply Summable.of_norm_bounded hmajor
  intro n
  rw [Real.norm_eq_abs]
  have h := abs_ccmActualHeadMatchedSymmetricCellResidual_le_firstMoment f hf n
  simpa only [mul_assoc, mul_left_comm, mul_comm] using h

/-- **Completed all-prime convergence.**  Under one finite Fourier moment, the literal family
`prime translation defect - its mass-matched polar cell` is absolutely summable.  Both its even
and asymmetric currents remain intact. -/
theorem summable_ccmActualHeadMatchedPrimePolarCellDifference_of_firstMoment
    (f : SoninL2)
    (hf : Integrable (fun xi : ℝ =>
      |xi| * ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2)) :
    Summable (fun n : ℕ =>
      criticalMellinAtomWeight n *
          ccmActualHeadTranslationDefect (Real.log n) f -
        ccmActualHeadOutgoingPolarSymmetricCell
          (Real.log n) (ccmActualHeadMatchedPrimePolarRadius n) f) := by
  have h :=
    (summable_ccmActualHeadMatchedSymmetricCellResidual_of_firstMoment f hf).sub
      (summable_ccmActualHeadMatchedSuzukiCurrent f)
  apply h.congr
  intro n
  exact
    (ccmActualHeadPrimeWeight_sub_matchedPolarCell_eq_symmetric_sub_suzuki n f).symm

end RHTower
