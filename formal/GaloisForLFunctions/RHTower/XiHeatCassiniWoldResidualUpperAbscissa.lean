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
  rw [xiHeatCassiniOrderedPrimeComplexNegativePhase, Complex.ofReal_exp]
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
    abs_of_nonneg (Real.exp_nonneg _)]
  have hone : 1 - Real.exp (a * xiHeatCassiniOrderedPrimeLogGap N) ≤ 0 :=
    sub_nonpos.mpr ((Real.exp_zero).symm.trans_le (Real.exp_le_exp.mpr hgap))
  rw [abs_of_nonpos hone]
  ring

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

/-- Any exponential bound on prime-log cells with rate strictly beyond `1/2` forces the critical
additive prime-gap energy.  One logarithmic cell is retained for the exact exponential-potential
telescope; only the other is spent on the pointwise rate. -/
theorem summable_primeGapCriticalEnergy_of_primeLogGap_exp_rate
    {d C : ℝ} (hd : 1 / 2 < d) (hC : 0 ≤ C)
    (hgapRate : ∀ᶠ N : ℕ in atTop,
      xiHeatCassiniOrderedPrimeLogGap N ≤
        C * Real.exp (-d * xiMassNthPrimeLogHeight N)) :
    Summable xiHeatCassiniPrimeGapCriticalEnergy := by
  have hrate : 0 < d - 1 / 2 := sub_pos.mpr hd
  have hmajor :=
    (summable_primeLogGap_mul_exp_neg_height hrate).mul_left (4 * C)
  apply hmajor.of_norm_bounded_eventually
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [hgapRate] with N hN
  let p : ℝ := nthPrimeSubtype N
  let delta : ℝ := xiHeatCassiniOrderedPrimeLogGap N
  have hp : 0 < p := nthPrimeSubtype_pos N
  have hdelta : 0 ≤ delta := xiHeatCassiniOrderedPrimeLogGap_nonneg N
  have hgap : 0 ≤ xiHeatCassiniOrderedPrimeGap N :=
    xiHeatCassiniOrderedPrimeGap_nonneg N
  have hnormalized :
      xiHeatCassiniOrderedPrimeGap N / p ≤ 2 * delta := by
    have hbase := primeGap_div_two_prime_le_primeLogGap N
    dsimp only [p, delta] at hbase ⊢
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2)] at hbase
    convert hbase using 1 <;> ring
  have hsqrt : Real.sqrt p =
      Real.exp (xiMassNthPrimeLogHeight N / 2) := by
    rw [xiMassNthPrimeLogHeight]
    rw [← Real.exp_log (Real.sqrt_pos.mpr hp)]
    congr 1
    exact (Real.log_sqrt hp.le).symm
  rw [Real.norm_eq_abs, abs_of_nonneg
    (xiHeatCassiniPrimeGapCriticalEnergy_nonneg N)]
  unfold xiHeatCassiniPrimeGapCriticalEnergy
  dsimp only [p]
  rw [hsqrt]
  calc
    (xiHeatCassiniOrderedPrimeGap N / p) ^ 2 *
          Real.exp (xiMassNthPrimeLogHeight N / 2) ≤
        (2 * delta) ^ 2 *
          Real.exp (xiMassNthPrimeLogHeight N / 2) := by
      gcongr
    _ = 4 * delta * delta *
          Real.exp (xiMassNthPrimeLogHeight N / 2) := by ring
    _ ≤ 4 * (C * Real.exp (-d * xiMassNthPrimeLogHeight N)) * delta *
          Real.exp (xiMassNthPrimeLogHeight N / 2) := by
      gcongr
    _ = (4 * C) * (delta *
          Real.exp (-(d - 1 / 2) * xiMassNthPrimeLogHeight N)) := by
      rw [show 4 * (C * Real.exp (-d * xiMassNthPrimeLogHeight N)) * delta *
            Real.exp (xiMassNthPrimeLogHeight N / 2) =
          (4 * C) * delta *
            (Real.exp (-d * xiMassNthPrimeLogHeight N) *
              Real.exp (xiMassNthPrimeLogHeight N / 2)) by ring,
        ← Real.exp_add]
      congr 2
      ring

/-- A genuine exponential residual estimate of rate `c` opens every upper height `a < c`.
Unlike the unconditional square-root-exponential estimate, it defeats the factor `exp(a h_N)`
exactly. -/
theorem summable_residualUpperVariationAtom_of_exp_height_rate
    {a c B : ℝ} (hac : a < c) (hB : 0 ≤ B)
    (hrate : ∀ᶠ N : ℕ in atTop,
      |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| ≤
        B * Real.exp (-c * xiMassNthPrimeLogHeight N)) :
    Summable (xiHeatCassiniWoldResidualUpperVariationAtom a) := by
  have hca : 0 < c - a := sub_pos.mpr hac
  have hmajor :=
    (summable_primeLogGap_mul_exp_neg_height hca).mul_left B
  apply hmajor.of_norm_bounded_eventually
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [hrate] with N hN
  have hgap : 0 ≤ xiHeatCassiniOrderedPrimeLogGap N :=
    xiHeatCassiniOrderedPrimeLogGap_nonneg N
  have hexp : 0 ≤ Real.exp (a * xiMassNthPrimeLogHeight N) :=
    Real.exp_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · dsimp only [xiHeatCassiniWoldResidualUpperVariationAtom]
    calc
      |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| *
            xiHeatCassiniOrderedPrimeLogGap N *
          Real.exp (a * xiMassNthPrimeLogHeight N) ≤
        (B * Real.exp (-c * xiMassNthPrimeLogHeight N)) *
            xiHeatCassiniOrderedPrimeLogGap N *
          Real.exp (a * xiMassNthPrimeLogHeight N) := by gcongr
      _ = B * xiHeatCassiniOrderedPrimeLogGap N *
          (Real.exp (-c * xiMassNthPrimeLogHeight N) *
            Real.exp (a * xiMassNthPrimeLogHeight N)) := by ring
      _ = B * (xiHeatCassiniOrderedPrimeLogGap N *
          Real.exp (-(c - a) * xiMassNthPrimeLogHeight N)) := by
        rw [← Real.exp_add]
        congr 2
        ring
  · exact mul_nonneg
      (mul_nonneg (abs_nonneg _) hgap) hexp

/-- Hence an exponential height estimate opens absolute convergence of the raw residual Hardy
series at every legal upper height below its rate. -/
theorem summable_norm_residualAtom_mul_I_of_exp_height_rate
    {a c B : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hac : a < c) (hB : 0 ≤ B)
    (hrate : ∀ᶠ N : ℕ in atTop,
      |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| ≤
        B * Real.exp (-c * xiMassNthPrimeLogHeight N)) :
    Summable (fun N : ℕ =>
      ‖xiHeatCassiniWoldResidualComplexPhaseConnectionAtom
        (Complex.I * (a : ℂ)) N‖) := by
  exact (summable_norm_residualAtom_mul_I_iff_upperVariation ha ha1).2
    (summable_residualUpperVariationAtom_of_exp_height_rate hac hB hrate)

end

end RHTower
