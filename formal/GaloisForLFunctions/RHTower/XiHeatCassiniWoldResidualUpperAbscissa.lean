import GaloisForLFunctions.RHTower.XiHeatCassiniWoldResidualHardyPolarization
import GaloisForLFunctions.RHTower.XiHeatCassiniPrimeGapMomentThreshold

/-!
# Exact upper abscissa of the Route-T residual Hardy source

Lower-half-plane holomorphy and every real-boundary derivative follow from the unconditional
square-root-exponential Wold residual estimate.  They do not cross the real boundary.  At a
positive imaginary height `a`, one residual prime-log edge has the exact mass

`|R_N| exp(a h_N) (exp(a Δh_N) - 1)`.

For `0 < a ≤ 1`, Bertrand's bound gives `0 ≤ a Δh_N ≤ 1`, so this mass is uniformly comparable
to `a |R_N| Δh_N exp(a h_N)`.  Hence absolute convergence at height `a` is equivalent to one
explicit exponentially weighted residual-variation series.  This is the sharp source-side
quantity hidden by all polynomial/Gevrey boundary jets.
-/

open Complex Filter Set Topology
open scoped BigOperators

namespace RHTower

noncomputable section

@[simp]
theorem xiHeatCassiniOrderedPrimeComplexNegativePhase_mul_I
    (N : ℕ) (a : ℝ) :
    xiHeatCassiniOrderedPrimeComplexNegativePhase N
        (Complex.I * (a : ℂ)) =
      (Real.exp (a * xiMassNthPrimeLogHeight N) : ℂ) := by
  rw [xiHeatCassiniOrderedPrimeComplexNegativePhase]
  congr 1
  calc
    -(Complex.I * (xiMassNthPrimeLogHeight N : ℂ) *
        (Complex.I * (a : ℂ))) =
        -(Complex.I * Complex.I) *
          ((xiMassNthPrimeLogHeight N : ℂ) * (a : ℂ)) := by ring
    _ = (a * xiMassNthPrimeLogHeight N : ℝ) := by
      rw [Complex.I_mul_I]
      push_cast
      ring

/-- Exact mass of one residual edge at positive imaginary height. -/
theorem norm_xiHeatCassiniWoldResidualComplexPhaseConnectionAtom_mul_I
    {a : ℝ} (ha : 0 ≤ a) (N : ℕ) :
    ‖xiHeatCassiniWoldResidualComplexPhaseConnectionAtom
        (Complex.I * (a : ℂ)) N‖ =
      |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| *
        Real.exp (a * xiMassNthPrimeLogHeight N) *
          (Real.exp (a * xiHeatCassiniOrderedPrimeLogGap N) - 1) := by
  rw [xiHeatCassiniWoldResidualComplexPhaseConnectionAtom, norm_mul,
    xiHeatCassiniOrderedPrimeComplexNegativePhase_mul_I,
    xiHeatCassiniOrderedPrimeComplexNegativePhase_mul_I,
    Complex.norm_real, Real.norm_eq_abs]
  have hheight :
      xiMassNthPrimeLogHeight (N + 1) =
        xiMassNthPrimeLogHeight N + xiHeatCassiniOrderedPrimeLogGap N := by
    dsimp only [xiHeatCassiniOrderedPrimeLogGap]
    ring
  rw [hheight, mul_add, Real.exp_add]
  have hgap : 0 ≤ a * xiHeatCassiniOrderedPrimeLogGap N :=
    mul_nonneg ha (xiHeatCassiniOrderedPrimeLogGap_nonneg N)
  rw [show (Real.exp (a * xiMassNthPrimeLogHeight N) : ℂ) -
        (Real.exp (a * xiMassNthPrimeLogHeight N) *
          Real.exp (a * xiHeatCassiniOrderedPrimeLogGap N) : ℝ) =
      ((Real.exp (a * xiMassNthPrimeLogHeight N) *
        (1 - Real.exp (a * xiHeatCassiniOrderedPrimeLogGap N)) : ℝ) : ℂ) by
        push_cast; ring]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (Real.exp_nonneg _), abs_of_nonpos]
  · ring
  · exact sub_nonpos.mpr ((Real.exp_zero).symm.trans_le (Real.exp_le_exp.mpr hgap))

/-- Exponentially weighted residual variation at upper height `a`. -/
def xiHeatCassiniWoldResidualUpperVariationAtom (a : ℝ) (N : ℕ) : ℝ :=
  |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| *
    xiHeatCassiniOrderedPrimeLogGap N *
      Real.exp (a * xiMassNthPrimeLogHeight N)

/-- Upper edge mass is bounded below by the weighted residual variation. -/
theorem residualUpperVariationAtom_mul_le_norm
    {a : ℝ} (ha : 0 ≤ a) (N : ℕ) :
    a * xiHeatCassiniWoldResidualUpperVariationAtom a N ≤
      ‖xiHeatCassiniWoldResidualComplexPhaseConnectionAtom
        (Complex.I * (a : ℂ)) N‖ := by
  rw [norm_xiHeatCassiniWoldResidualComplexPhaseConnectionAtom_mul_I ha]
  have hgap : 0 ≤ a * xiHeatCassiniOrderedPrimeLogGap N :=
    mul_nonneg ha (xiHeatCassiniOrderedPrimeLogGap_nonneg N)
  have hexp := Real.add_one_le_exp (a * xiHeatCassiniOrderedPrimeLogGap N)
  dsimp only [xiHeatCassiniWoldResidualUpperVariationAtom]
  have hscale : 0 ≤ |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| *
      Real.exp (a * xiMassNthPrimeLogHeight N) :=
    mul_nonneg (abs_nonneg _) (Real.exp_nonneg _)
  nlinarith [mul_le_mul_of_nonneg_left hexp hscale]

/-- For `0 ≤ a ≤ 1`, upper edge mass costs at most twice the weighted residual variation. -/
theorem norm_le_two_mul_residualUpperVariationAtom
    {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (N : ℕ) :
    ‖xiHeatCassiniWoldResidualComplexPhaseConnectionAtom
        (Complex.I * (a : ℂ)) N‖ ≤
      2 * a * xiHeatCassiniWoldResidualUpperVariationAtom a N := by
  rw [norm_xiHeatCassiniWoldResidualComplexPhaseConnectionAtom_mul_I ha]
  let d : ℝ := xiHeatCassiniOrderedPrimeLogGap N
  have hd0 : 0 ≤ d := xiHeatCassiniOrderedPrimeLogGap_nonneg N
  have hd1 : d ≤ 1 := xiHeatCassiniOrderedPrimeLogGap_le_one N
  have had0 : 0 ≤ a * d := mul_nonneg ha hd0
  have had1 : |a * d| ≤ 1 := by
    rw [abs_of_nonneg had0]
    nlinarith
  have hexp := Real.abs_exp_sub_one_le had1
  have hexp0 : 0 ≤ Real.exp (a * d) - 1 := by
    exact sub_nonneg.mpr <| by
      simpa only [Real.exp_zero] using Real.exp_le_exp.mpr had0
  rw [abs_of_nonneg hexp0, abs_of_nonneg had0] at hexp
  dsimp only [xiHeatCassiniWoldResidualUpperVariationAtom]
  dsimp only [d] at hexp
  have hscale : 0 ≤ |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| *
      Real.exp (a * xiMassNthPrimeLogHeight N) :=
    mul_nonneg (abs_nonneg _) (Real.exp_nonneg _)
  nlinarith [mul_le_mul_of_nonneg_left hexp hscale]

/-- **Exact upper-abscissa law.**  For `0 < a ≤ 1`, absolute convergence of the raw residual
Hardy series at height `a` is equivalent to summability of its exponentially weighted residual
variation. -/
theorem summable_norm_residualAtom_mul_I_iff_upperVariation
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    Summable (fun N : ℕ =>
      ‖xiHeatCassiniWoldResidualComplexPhaseConnectionAtom
        (Complex.I * (a : ℂ)) N‖) ↔
    Summable (xiHeatCassiniWoldResidualUpperVariationAtom a) := by
  constructor
  · intro hnorm
    have hscaled : Summable (fun N : ℕ =>
        a * xiHeatCassiniWoldResidualUpperVariationAtom a N) := by
      exact Summable.of_nonneg_of_le
        (fun N => mul_nonneg ha.le <| mul_nonneg
          (mul_nonneg (abs_nonneg _)
            (xiHeatCassiniOrderedPrimeLogGap_nonneg N))
          (Real.exp_nonneg _))
        (fun N => residualUpperVariationAtom_mul_le_norm ha.le N) hnorm
    have := hscaled.mul_left a⁻¹
    simpa [ha.ne'] using this
  · intro hvariation
    have hmajor := hvariation.mul_left (2 * a)
    exact Summable.of_nonneg_of_le
      (fun N => norm_nonneg _)
      (fun N => norm_le_two_mul_residualUpperVariationAtom ha.le ha1 N)
      hmajor

end

end RHTower
