import GaloisForLFunctions.HTGeometry.SummableSpectrumScrewBohrCoefficients
import GaloisForLFunctions.RHTower.CCMRectangularFullObservableDivisorTomography
import GaloisForLFunctions.RHTower.CCMFirstClockAsymptoticBohrLaw
import GaloisForLFunctions.RHTower.CCMFirstClockCreaseCurrent

/-!
# Unitary--polar source atlas

The complete Xi divisor splits into two source-readable spectral strata.  Fixed-width rectangular
source continuation records every strict-right copy as a simple pole with normalized residue equal
to its analytic multiplicity; functional-equation reflection supplies the strict-left copies.
After those polar contributions are subtracted from the literal scaled first CCM clock, the exact
residual is the rational divisor over critical-line copies alone.  This residual converges to a
unique continuous Bohr almost-periodic screw model, and its nonzero Bohr coefficients recover
critical multiplicities exactly.

Together with finite-aperture crease tomography, this yields one unconditional
crease--pole--frequency atlas: creases recover every von Mangoldt atom, poles recover every
off-critical divisor copy, and frequencies recover every critical divisor copy.  The theorem does
not assert that the polar sector is empty and does not prove the Riemann hypothesis.
-/

open Complex Filter Set Topology
open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry
open HTGeometry

namespace RHTower

noncomputable section

/-- Multiplicity copies of Xi zeros on the critical line. -/
abbrev XiCriticalZeroCopy :=
  {q : XiZeroCopy // (I * xiSpectralPoint q).re = 0}

/-- Real centered ordinate of a critical Xi copy. -/
def xiCriticalOrdinate (q : XiCriticalZeroCopy) : ℝ :=
  (xiSpectralPoint q.1).re

theorem xiSpectralPoint_eq_of_critical (q : XiCriticalZeroCopy) :
    xiSpectralPoint q.1 = (xiCriticalOrdinate q : ℂ) := by
  apply Complex.ext
  · rfl
  · have h := q.2
    simp only [mul_re, I_re, I_im, zero_mul, one_mul, zero_sub] at h
    simpa only [ofReal_im] using neg_eq_zero.mp h

theorem xiCriticalOrdinate_ne_zero (q : XiCriticalZeroCopy) :
    xiCriticalOrdinate q ≠ 0 := by
  intro h
  apply xiSpectralPoint_ne_zero q.1
  rw [xiSpectralPoint_eq_of_critical q, h]
  norm_num

theorem four_lt_abs_xiCriticalOrdinate (q : XiCriticalZeroCopy) :
    4 < |xiCriticalOrdinate q| := by
  have h := four_lt_norm_xiSpectralPoint q.1
  rw [xiSpectralPoint_eq_of_critical q, Complex.norm_real,
    Real.norm_eq_abs] at h
  exact h

/-- Reciprocal-square screw weight of one critical divisor copy. -/
def xiLineScrewWeight (q : XiCriticalZeroCopy) : ℝ :=
  1 / xiCriticalOrdinate q ^ 2

theorem xiLineScrewWeight_nonneg (q : XiCriticalZeroCopy) :
    0 ≤ xiLineScrewWeight q := by
  unfold xiLineScrewWeight
  positivity

theorem summable_xiLineScrewWeight : Summable xiLineScrewWeight := by
  have h := xiSpectralPoint_inv_sq_summable.subtype
    {q : XiZeroCopy | (I * xiSpectralPoint q).re = 0}
  change Summable (fun q : XiCriticalZeroCopy =>
    1 / ‖xiSpectralPoint q.1‖ ^ 2) at h
  apply h.congr
  intro q
  rw [xiLineScrewWeight, xiSpectralPoint_eq_of_critical q,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- Critical-line screw signal, indexed by multiplicity copies. -/
def xiLineScrewSeries (L : ℝ) : ℝ :=
  screwSeries xiLineScrewWeight xiCriticalOrdinate L

theorem xiLineScrewSeries_continuous : Continuous xiLineScrewSeries := by
  exact screwSeries_continuous xiLineScrewWeight_nonneg
    summable_xiLineScrewWeight

theorem xiLineScrewSeries_isBohrAlmostPeriodic :
    IsBohrAlmostPeriodic xiLineScrewSeries := by
  exact isBohrAlmostPeriodic_screwSeries xiLineScrewWeight_nonneg
    summable_xiLineScrewWeight

/-- Critical-line part of the exact first-clock rational divisor. -/
def ccmFirstClockCriticalRationalDivisor (L : ℝ) : ℂ :=
  ∑' q : XiCriticalZeroCopy,
    ccmFirstClockRationalKernel L (xiSpectralPoint q.1)

theorem summable_ccmFirstClockCriticalRationalKernel
    {L : ℝ} (hL : Real.pi / 2 ≤ L) :
    Summable (fun q : XiCriticalZeroCopy =>
      ccmFirstClockRationalKernel L (xiSpectralPoint q.1)) := by
  exact (summable_ccmFirstClockRationalKernel_xiSpectralPoint hL).comp_injective
    Subtype.val_injective

theorem ccmFirstClockRationalKernel_re_eq_of_critical
    (L : ℝ) (q : XiCriticalZeroCopy) :
    (ccmFirstClockRationalKernel L (xiSpectralPoint q.1)).re =
      (1 - Real.cos (xiCriticalOrdinate q * L)) /
        (xiCriticalOrdinate q ^ 2 - (2 * Real.pi / L) ^ 2) := by
  rw [xiSpectralPoint_eq_of_critical q]
  unfold ccmFirstClockRationalKernel
  have hcos : Complex.cos ((L : ℂ) * (xiCriticalOrdinate q : ℂ)) =
      (Real.cos (xiCriticalOrdinate q * L) : ℂ) := by
    rw [show (L : ℂ) * (xiCriticalOrdinate q : ℂ) =
      ((xiCriticalOrdinate q * L : ℝ) : ℂ) by push_cast; ring]
    exact (Complex.ofReal_cos _).symm
  rw [hcos]
  rw [show (1 : ℂ) - (Real.cos (xiCriticalOrdinate q * L) : ℂ) =
      ((1 - Real.cos (xiCriticalOrdinate q * L) : ℝ) : ℂ) by push_cast; rfl]
  rw [show (xiCriticalOrdinate q : ℂ) ^ 2 -
        (((2 * Real.pi / L : ℝ) : ℂ)) ^ 2 =
      ((xiCriticalOrdinate q ^ 2 - (2 * Real.pi / L) ^ 2 : ℝ) : ℂ) by
        push_cast; rfl]
  rw [← Complex.ofReal_div]
  exact Complex.ofReal_re _

/-- Sharp uniform moving-denominator error for one critical-line copy. -/
theorem ccmFirstClockRationalKernel_sub_lineScrewTerm_bounds
    {L : ℝ} (hL : 2 * Real.pi ≤ L) (q : XiCriticalZeroCopy) :
    0 ≤ (ccmFirstClockRationalKernel L (xiSpectralPoint q.1)).re -
        xiLineScrewWeight q *
          (1 - Real.cos (xiCriticalOrdinate q * L)) ∧
      (ccmFirstClockRationalKernel L (xiSpectralPoint q.1)).re -
          xiLineScrewWeight q *
            (1 - Real.cos (xiCriticalOrdinate q * L)) ≤
        (2 / 15 : ℝ) * (2 * Real.pi / L) ^ 2 * xiLineScrewWeight q := by
  let r : ℝ := xiCriticalOrdinate q
  let w : ℝ := 2 * Real.pi / L
  have hLpos : 0 < L := lt_of_lt_of_le (mul_pos (by norm_num) Real.pi_pos) hL
  have hw0 : 0 ≤ w := by dsimp only [w]; positivity
  have hw1 : w ≤ 1 := by
    dsimp only [w]
    exact (div_le_one hLpos).2 hL
  have hr4 : 4 < |r| := four_lt_abs_xiCriticalOrdinate q
  have hr2 : 16 < r ^ 2 := by
    rw [← sq_abs]
    nlinarith [sq_nonneg (|r| - 4)]
  have hr2pos : 0 < r ^ 2 := lt_trans (by norm_num) hr2
  have hrne : r ≠ 0 := by nlinarith [sq_nonneg r]
  have hden15 : 15 < r ^ 2 - w ^ 2 := by
    nlinarith [sq_nonneg w]
  have hdenpos : 0 < r ^ 2 - w ^ 2 := lt_trans (by norm_num) hden15
  have hn0 : 0 ≤ 1 - Real.cos (r * L) := sub_nonneg.mpr (Real.cos_le_one _)
  have hn2 : 1 - Real.cos (r * L) ≤ 2 := by
    linarith [Real.neg_one_le_cos (r * L)]
  have hid :
      (1 - Real.cos (r * L)) / (r ^ 2 - w ^ 2) -
          (1 / r ^ 2) * (1 - Real.cos (r * L)) =
        (1 - Real.cos (r * L)) * w ^ 2 /
          (r ^ 2 * (r ^ 2 - w ^ 2)) := by
    field_simp [hrne, ne_of_gt hdenpos]
    ring
  rw [ccmFirstClockRationalKernel_re_eq_of_critical L q]
  change 0 ≤ (1 - Real.cos (r * L)) / (r ^ 2 - w ^ 2) -
      (1 / r ^ 2) * (1 - Real.cos (r * L)) ∧
    (1 - Real.cos (r * L)) / (r ^ 2 - w ^ 2) -
        (1 / r ^ 2) * (1 - Real.cos (r * L)) ≤
      (2 / 15 : ℝ) * w ^ 2 * (1 / r ^ 2)
  rw [hid]
  constructor
  · positivity
  · calc
      (1 - Real.cos (r * L)) * w ^ 2 / (r ^ 2 * (r ^ 2 - w ^ 2)) =
          (((1 - Real.cos (r * L)) * w ^ 2 / r ^ 2) /
            (r ^ 2 - w ^ 2)) := by
              field_simp [hrne, ne_of_gt hdenpos]
      _ ≤ ((2 * w ^ 2 / r ^ 2) / (r ^ 2 - w ^ 2)) := by
        gcongr
      _ ≤ (2 * w ^ 2 / r ^ 2) / 15 := by
        exact div_le_div_of_nonneg_left (by positivity) (by norm_num) hden15.le
      _ = (2 / 15 : ℝ) * w ^ 2 * (1 / r ^ 2) := by ring

/-- Difference between the critical rational divisor and its limiting screw series. -/
def ccmFirstClockCriticalMovingDenominatorError (L : ℝ) : ℝ :=
  (ccmFirstClockCriticalRationalDivisor L).re - xiLineScrewSeries L

theorem ccmFirstClockCriticalMovingDenominatorError_bounds
    {L : ℝ} (hL : 2 * Real.pi ≤ L) :
    0 ≤ ccmFirstClockCriticalMovingDenominatorError L ∧
      ccmFirstClockCriticalMovingDenominatorError L ≤
        (2 / 15 : ℝ) * (2 * Real.pi / L) ^ 2 *
          ∑' q : XiCriticalZeroCopy, xiLineScrewWeight q := by
  have hphysical : Real.pi / 2 ≤ L := by
    have hpi := Real.pi_pos
    linarith
  have hQ := summable_ccmFirstClockCriticalRationalKernel hphysical
  have hQre : Summable (fun q : XiCriticalZeroCopy =>
      (ccmFirstClockRationalKernel L (xiSpectralPoint q.1)).re) :=
    hQ.map Complex.reCLM Complex.reCLM.continuous
  have hS := summable_screwSeries_term (omega := xiCriticalOrdinate)
    xiLineScrewWeight_nonneg summable_xiLineScrewWeight L
  have herr : Summable (fun q : XiCriticalZeroCopy =>
      (ccmFirstClockRationalKernel L (xiSpectralPoint q.1)).re -
        xiLineScrewWeight q *
          (1 - Real.cos (xiCriticalOrdinate q * L))) := hQre.sub hS
  have hmajor : Summable (fun q : XiCriticalZeroCopy =>
      (2 / 15 : ℝ) * (2 * Real.pi / L) ^ 2 * xiLineScrewWeight q) :=
    summable_xiLineScrewWeight.mul_left
      ((2 / 15 : ℝ) * (2 * Real.pi / L) ^ 2)
  rw [ccmFirstClockCriticalMovingDenominatorError,
    ccmFirstClockCriticalRationalDivisor, Complex.re_tsum hQ,
    xiLineScrewSeries, screwSeries, ← Summable.tsum_sub hQre hS]
  constructor
  · exact tsum_nonneg fun q =>
      (ccmFirstClockRationalKernel_sub_lineScrewTerm_bounds hL q).1
  · calc
      (∑' q : XiCriticalZeroCopy,
          ((ccmFirstClockRationalKernel L (xiSpectralPoint q.1)).re -
            xiLineScrewWeight q *
              (1 - Real.cos (xiCriticalOrdinate q * L)))) ≤
          ∑' q : XiCriticalZeroCopy,
            ((2 / 15 : ℝ) * (2 * Real.pi / L) ^ 2 *
              xiLineScrewWeight q) :=
        herr.tsum_le_tsum
          (fun q =>
            (ccmFirstClockRationalKernel_sub_lineScrewTerm_bounds hL q).2)
          hmajor
      _ = (2 / 15 : ℝ) * (2 * Real.pi / L) ^ 2 *
          ∑' q : XiCriticalZeroCopy, xiLineScrewWeight q := by
        rw [tsum_mul_left]

theorem ccmFirstClockCriticalMovingDenominatorError_tendsto_zero :
    Tendsto ccmFirstClockCriticalMovingDenominatorError atTop (𝓝 0) := by
  apply squeeze_zero'
  · filter_upwards [eventually_ge_atTop (2 * Real.pi)] with L hL
    exact (ccmFirstClockCriticalMovingDenominatorError_bounds hL).1
  · filter_upwards [eventually_ge_atTop (2 * Real.pi)] with L hL
    exact (ccmFirstClockCriticalMovingDenominatorError_bounds hL).2
  · have hw : Tendsto (fun L : ℝ => 2 * Real.pi / L) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have hw2 := hw.pow 2
    have hscaled := hw2.const_mul
      ((2 / 15 : ℝ) * ∑' q : XiCriticalZeroCopy, xiLineScrewWeight q)
    simpa [mul_assoc, mul_comm, mul_left_comm] using hscaled

/-- Critical divisor copies at unsigned frequency `|lam|`. -/
def xiCriticalAbsoluteOrdinateFiber (lam : ℝ) : Set XiCriticalZeroCopy :=
  {q | xiCriticalOrdinate q = lam ∨ -xiCriticalOrdinate q = lam}

theorem finite_xiCriticalAbsoluteOrdinateFiber (lam : ℝ) :
    (xiCriticalAbsoluteOrdinateFiber lam).Finite := by
  let A : Set XiZeroCopy := {q | xiSpectralPoint q = (lam : ℂ)}
  let B : Set XiZeroCopy := {q | xiSpectralPoint q = ((-lam : ℝ) : ℂ)}
  have hAB : (A ∪ B).Finite :=
    (finite_xiSpectralPoint_fiber (lam : ℂ)).union
      (finite_xiSpectralPoint_fiber ((-lam : ℝ) : ℂ))
  have hpre : (Subtype.val ⁻¹' (A ∪ B) : Set XiCriticalZeroCopy).Finite :=
    hAB.preimage Subtype.val_injective.injOn
  apply hpre.subset
  intro q hq
  change xiCriticalOrdinate q = lam ∨ -xiCriticalOrdinate q = lam at hq
  change q.1 ∈ A ∪ B
  rcases hq with hq | hq
  · left
    change xiSpectralPoint q.1 = (lam : ℂ)
    rw [xiSpectralPoint_eq_of_critical q, hq]
  · right
    change xiSpectralPoint q.1 = ((-lam : ℝ) : ℂ)
    rw [xiSpectralPoint_eq_of_critical q]
    congr 1
    linarith

def xiCriticalAbsoluteOrdinateMultiplicity (lam : ℝ) : ℕ :=
  (finite_xiCriticalAbsoluteOrdinateFiber lam).toFinset.card

/-- Exact termwise Bohr coefficient of the unconditional critical screw model. -/
theorem bohrCoefficient_two_mul_xiLineScrewSeries_eq_tsum (lam : ℝ) :
    bohrCoefficient
        (fun L => ((2 * xiLineScrewSeries L : ℝ) : ℂ)) lam =
      2 * ∑' q : XiCriticalZeroCopy,
        screwAtomBohrCoefficient (xiLineScrewWeight q)
          (xiCriticalOrdinate q) lam := by
  have hfun :
      (fun L : ℝ => ((2 * xiLineScrewSeries L : ℝ) : ℂ)) =
        fun L : ℝ => (2 : ℂ) * (xiLineScrewSeries L : ℂ) := by
    funext L
    push_cast
    ring
  rw [hfun, bohrCoefficient_const_mul]
  · unfold xiLineScrewSeries
    rw [bohrCoefficient_complex_screwSeries
      xiLineScrewWeight_nonneg summable_xiLineScrewWeight]
  · exact Complex.continuous_ofReal.comp xiLineScrewSeries_continuous
  · exact isBohrAlmostPeriodic_ofReal xiLineScrewSeries_isBohrAlmostPeriodic

theorem bohrCoefficient_two_mul_xiLineScrewSeries_eq_fiberMass
    {lam : ℝ} (hlam : lam ≠ 0) :
    bohrCoefficient
        (fun L => ((2 * xiLineScrewSeries L : ℝ) : ℂ)) lam =
      ∑' q : XiCriticalZeroCopy,
        if xiCriticalOrdinate q = lam ∨ -xiCriticalOrdinate q = lam
        then -((1 / lam ^ 2 : ℝ) : ℂ) else 0 := by
  classical
  rw [bohrCoefficient_two_mul_xiLineScrewSeries_eq_tsum lam,
    ← tsum_mul_left]
  apply tsum_congr
  intro q
  have hwne : xiCriticalOrdinate q ≠ 0 := xiCriticalOrdinate_ne_zero q
  rw [xiLineScrewWeight]
  unfold screwAtomBohrCoefficient
  simp only [if_neg (Ne.symm hlam)]
  by_cases hp : xiCriticalOrdinate q = lam
  · have hn : -xiCriticalOrdinate q ≠ lam := by
      rw [hp]
      intro h
      apply hlam
      linarith
    rw [if_pos hp, if_neg hn, if_pos (Or.inl hp)]
    push_cast
    rw [hp]
    ring
  · by_cases hn : -xiCriticalOrdinate q = lam
    · rw [if_neg hp, if_pos hn, if_pos (Or.inr hn)]
      have homega : xiCriticalOrdinate q = -lam := by linarith
      rw [homega]
      push_cast
      ring
    · rw [if_neg hp, if_neg hn, if_neg (not_or_intro hp hn)]
      ring

/-- Quantized critical Torelli law, without RH or an almost-periodicity hypothesis. -/
theorem bohrCoefficient_two_mul_xiLineScrewSeries_eq_multiplicity
    {lam : ℝ} (hlam : lam ≠ 0) :
    bohrCoefficient
        (fun L => ((2 * xiLineScrewSeries L : ℝ) : ℂ)) lam =
      -(xiCriticalAbsoluteOrdinateMultiplicity lam : ℂ) / (lam : ℂ) ^ 2 := by
  classical
  rw [bohrCoefficient_two_mul_xiLineScrewSeries_eq_fiberMass hlam]
  let S : Finset XiCriticalZeroCopy :=
    (finite_xiCriticalAbsoluteOrdinateFiber lam).toFinset
  rw [tsum_eq_sum (s := S)]
  · calc
      ∑ q ∈ S, (if xiCriticalOrdinate q = lam ∨
          -xiCriticalOrdinate q = lam
          then -((1 / lam ^ 2 : ℝ) : ℂ) else 0) =
          ∑ _q ∈ S, -((1 / lam ^ 2 : ℝ) : ℂ) := by
            apply Finset.sum_congr rfl
            intro q hq
            rw [if_pos]
            have hmem : q ∈ xiCriticalAbsoluteOrdinateFiber lam := by
              simpa only [S, Set.Finite.mem_toFinset] using hq
            simpa only [xiCriticalAbsoluteOrdinateFiber, Set.mem_setOf_eq] using hmem
      _ = -(xiCriticalAbsoluteOrdinateMultiplicity lam : ℂ) / (lam : ℂ) ^ 2 := by
        unfold xiCriticalAbsoluteOrdinateMultiplicity
        dsimp only [S]
        push_cast
        simp
        ring
  · intro q hq
    rw [if_neg]
    intro hmem
    apply hq
    have hset : q ∈ xiCriticalAbsoluteOrdinateFiber lam := by
      simpa only [xiCriticalAbsoluteOrdinateFiber, Set.mem_setOf_eq] using hmem
    simpa only [S, Set.Finite.mem_toFinset] using hset

theorem two_mul_xiLineScrewSeries_recovers_multiplicity
    {lam : ℝ} (hlam : lam ≠ 0) :
    -((lam : ℂ) ^ 2) *
        bohrCoefficient (fun L => ((2 * xiLineScrewSeries L : ℝ) : ℂ)) lam =
      (xiCriticalAbsoluteOrdinateMultiplicity lam : ℂ) := by
  rw [bohrCoefficient_two_mul_xiLineScrewSeries_eq_multiplicity hlam]
  have hlamC : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam
  field_simp [hlamC]

/-- The first-clock rational kernel is even in the centered spectral coordinate. -/
theorem ccmFirstClockRationalKernel_neg (L : ℝ) (z : ℂ) :
    ccmFirstClockRationalKernel L (-z) = ccmFirstClockRationalKernel L z := by
  unfold ccmFirstClockRationalKernel
  rw [mul_neg, Complex.cos_neg]
  congr 1
  ring

/-- Strict-right part of the exact first-clock rational divisor. -/
def ccmFirstClockRightRationalDivisor (L : ℝ) : ℂ :=
  ∑' q : XiRightZeroCopy,
    ccmFirstClockRationalKernel L (xiSpectralPoint q.1)

theorem summable_ccmFirstClockRightRationalKernel
    {L : ℝ} (hL : Real.pi / 2 ≤ L) :
    Summable (fun q : XiRightZeroCopy =>
      ccmFirstClockRationalKernel L (xiSpectralPoint q.1)) :=
  (summable_ccmFirstClockRationalKernel_xiSpectralPoint hL).comp_injective
    Subtype.val_injective

theorem tsum_ccmFirstClockRationalKernel_left_eq_right (L : ℝ) :
    (∑' q : XiLeftZeroCopy,
      ccmFirstClockRationalKernel L (xiSpectralPoint q.1)) =
    ∑' q : XiRightZeroCopy,
      ccmFirstClockRationalKernel L (xiSpectralPoint q.1) := by
  calc
    (∑' q : XiLeftZeroCopy,
        ccmFirstClockRationalKernel L (xiSpectralPoint q.1)) =
      ∑' q : XiRightZeroCopy,
        ccmFirstClockRationalKernel L
          (xiSpectralPoint (xiRightLeftReflectEquiv q).1) :=
      (xiRightLeftReflectEquiv.tsum_eq
        (fun q : XiLeftZeroCopy =>
          ccmFirstClockRationalKernel L (xiSpectralPoint q.1))).symm
    _ = ∑' q : XiRightZeroCopy,
        ccmFirstClockRationalKernel L (xiSpectralPoint q.1) := by
      apply tsum_congr
      intro q
      rw [show xiSpectralPoint (xiRightLeftReflectEquiv q).1 =
          -xiSpectralPoint q.1 by
        exact xiSpectralPoint_reflect q.1,
        ccmFirstClockRationalKernel_neg]

/-- Exact three-sector functional-equation fold of the complete first-clock divisor. -/
theorem ccmFirstClockXiRationalDivisor_eq_two_right_add_critical
    {L : ℝ} (hL : Real.pi / 2 ≤ L) :
    ccmFirstClockXiRationalDivisor L =
      2 * ccmFirstClockRightRationalDivisor L +
        ccmFirstClockCriticalRationalDivisor L := by
  let f : XiZeroCopy → ℂ := fun q =>
    ccmFirstClockRationalKernel L (xiSpectralPoint q)
  let P : Set XiZeroCopy := {q | 0 < (I * xiSpectralPoint q).re}
  let M : Set XiZeroCopy := {q | (I * xiSpectralPoint q).re < 0}
  let C : Set XiZeroCopy := {q | (I * xiSpectralPoint q).re = 0}
  have hsum : Summable f :=
    summable_ccmFirstClockRationalKernel_xiSpectralPoint hL
  have hpoint : f = P.indicator f + M.indicator f + C.indicator f := by
    funext q
    rcases lt_trichotomy (I * xiSpectralPoint q).re 0 with hneg | hzero | hpos
    · rw [Pi.add_apply, Pi.add_apply,
        Set.indicator_of_notMem, Set.indicator_of_mem, Set.indicator_of_notMem]
      · simp
      · exact hneg.ne
      · exact hneg
      · exact not_lt.mpr hneg.le
    · rw [Pi.add_apply, Pi.add_apply,
        Set.indicator_of_notMem, Set.indicator_of_notMem, Set.indicator_of_mem]
      · simp
      · exact hzero
      · exact hzero.not_lt
      · exact hzero.symm.not_lt
    · rw [Pi.add_apply, Pi.add_apply,
        Set.indicator_of_mem, Set.indicator_of_notMem, Set.indicator_of_notMem]
      · simp
      · exact hpos.ne'
      · exact not_lt.mpr hpos.le
      · exact hpos
  calc
    ccmFirstClockXiRationalDivisor L = ∑' q : XiZeroCopy, f q := rfl
    _ = ∑' q : XiZeroCopy,
        ((P.indicator f q + M.indicator f q) + C.indicator f q) := by
      apply tsum_congr
      intro q
      exact congrFun hpoint q
    _ = (∑' q : XiZeroCopy,
          (P.indicator f q + M.indicator f q)) +
        ∑' q : XiZeroCopy, C.indicator f q :=
      ((hsum.indicator P).add (hsum.indicator M)).tsum_add
        (hsum.indicator C)
    _ = ((∑' q : XiZeroCopy, P.indicator f q) +
          ∑' q : XiZeroCopy, M.indicator f q) +
        ∑' q : XiZeroCopy, C.indicator f q := by
      rw [(hsum.indicator P).tsum_add (hsum.indicator M)]
    _ = ((∑' q : P, f q.1) + ∑' q : M, f q.1) +
        ∑' q : C, f q.1 := by
      rw [tsum_subtype, tsum_subtype, tsum_subtype]
    _ = ((∑' q : XiRightZeroCopy,
          ccmFirstClockRationalKernel L (xiSpectralPoint q.1)) +
        ∑' q : XiLeftZeroCopy,
          ccmFirstClockRationalKernel L (xiSpectralPoint q.1)) +
      ∑' q : XiCriticalZeroCopy,
        ccmFirstClockRationalKernel L (xiSpectralPoint q.1) := rfl
    _ = 2 * ccmFirstClockRightRationalDivisor L +
        ccmFirstClockCriticalRationalDivisor L := by
      rw [tsum_ccmFirstClockRationalKernel_left_eq_right]
      unfold ccmFirstClockRightRationalDivisor
      unfold ccmFirstClockCriticalRationalDivisor
      ring

/-- Literal scaled source after subtraction of the pole-reconstructed strict-right/left sector. -/
def ccmFirstClockPolarSubtractedSource (L : ℝ) : ℝ :=
  ccmFirstClockScaledPublishedSource L -
    4 * (ccmFirstClockRightRationalDivisor L).re

/-- Exact source/divisor split: polar subtraction leaves only critical copies. -/
theorem ccmFirstClockPolarSubtractedSource_eq_critical
    {L : ℝ} (hL : Real.pi / 2 ≤ L) :
    ccmFirstClockPolarSubtractedSource L =
      2 * (ccmFirstClockCriticalRationalDivisor L).re := by
  have hLpos : 0 < L := lt_of_lt_of_le (by positivity) hL
  rw [ccmFirstClockPolarSubtractedSource,
    ccmFirstClockScaledPublishedSource,
    ccmPublishedSourceSineCoefficient_firstClock_eq_xiRationalDivisor hL,
    ccmFirstClockXiRationalDivisor_eq_two_right_add_critical hL]
  simp only [Complex.add_re, Complex.mul_re]
  norm_num
  field_simp [hLpos.ne']
  ring

/-- Unconditional residual clock converges to twice the critical Bohr screw model. -/
theorem ccmFirstClockPolarSubtractedSource_sub_screw_tendsto_zero :
    Tendsto
      (fun L => ccmFirstClockPolarSubtractedSource L -
        2 * xiLineScrewSeries L) atTop (𝓝 0) := by
  have herr : Tendsto
      (fun L => 2 * ccmFirstClockCriticalMovingDenominatorError L)
      atTop (𝓝 0) := by
    simpa using
      ccmFirstClockCriticalMovingDenominatorError_tendsto_zero.const_mul 2
  have heq :
      (fun L => ccmFirstClockPolarSubtractedSource L -
        2 * xiLineScrewSeries L) =ᶠ[atTop]
      (fun L => 2 * ccmFirstClockCriticalMovingDenominatorError L) := by
    filter_upwards [eventually_ge_atTop (2 * Real.pi)] with L hL
    have hphysical : Real.pi / 2 ≤ L := by
      have hpi := Real.pi_pos
      linarith
    rw [ccmFirstClockPolarSubtractedSource_eq_critical hphysical,
      ccmFirstClockCriticalMovingDenominatorError]
    ring
  exact herr.congr' heq.symm

/-- The critical screw is the unique continuous Bohr asymptote of the polar-subtracted source. -/
theorem ccmFirstClockPolarSubtractedSource_asymptote_unique
    {P : ℝ → ℝ}
    (hPc : Continuous P) (hPa : IsBohrAlmostPeriodic P)
    (hP : Tendsto
      (fun L => ccmFirstClockPolarSubtractedSource L - P L)
      atTop (𝓝 0)) :
    P = fun L => 2 * xiLineScrewSeries L := by
  apply asymptoticBohrModel_unique hPc hPa
    (continuous_const.mul xiLineScrewSeries_continuous)
    (by
      have hcont := xiLineScrewSeries_continuous
      have hap := xiLineScrewSeries_isBohrAlmostPeriodic
      have hadd := isBohrAlmostPeriodic_add hcont hap hcont hap
      change IsBohrAlmostPeriodic (fun t => 2 * xiLineScrewSeries t)
      simpa only [two_mul] using hadd)
    hP ccmFirstClockPolarSubtractedSource_sub_screw_tendsto_zero

/-- **Crease--pole--frequency source atlas.**  One source architecture exposes exact arithmetic
atoms at finite-aperture creases, the strict-right divisor at continuation poles, and the
critical divisor in the unique Bohr asymptote after polar subtraction. -/
theorem ccmFirstClockCreasePolarFrequencyAtlas
    {A : ℝ} (hA : 0 < A) :
    (∀ k : ℕ, 1 < k →
      ∃ d : ℝ,
        HasDerivWithinAt ccmFirstClockArithmeticTrace
          (d + ccmFirstClockPrimeEntrySlope k)
          (Set.Ici (Real.log k)) (Real.log k) ∧
        HasDerivWithinAt ccmFirstClockArithmeticTrace d
          (Set.Iic (Real.log k)) (Real.log k) ∧
        (-(Real.log k) / (2 * Real.pi) *
            ((d + ccmFirstClockPrimeEntrySlope k) - d)) *
              Real.exp (Real.log k / 2) =
          ArithmeticFunction.vonMangoldt k) ∧
    (∀ s : ℂ, 1 < s.re →
      (meromorphicOrderAt (xiRectangularWeilFullContinuation A) s =
          ((-1 : ℤ) : WithTop ℤ) ↔
        ∃ q : XiRightZeroCopy, xiRightShiftedPole q = s)) ∧
    (∀ q : XiRightZeroCopy,
      meromorphicTrailingCoeffAt (xiRectangularWeilFullContinuation A)
            (xiRightShiftedPole q) /
          (2 * xiRectangularRightCoefficient A q) =
        (xiRightMultiplicity q : ℂ)) ∧
    (∀ L : ℝ, Real.pi / 2 ≤ L →
      ccmFirstClockPolarSubtractedSource L =
        2 * (ccmFirstClockCriticalRationalDivisor L).re) ∧
    Continuous (fun L => 2 * xiLineScrewSeries L) ∧
    IsBohrAlmostPeriodic (fun L => 2 * xiLineScrewSeries L) ∧
    Tendsto
      (fun L => ccmFirstClockPolarSubtractedSource L -
        2 * xiLineScrewSeries L) atTop (𝓝 0) ∧
    (∀ lam : ℝ, lam ≠ 0 →
      -((lam : ℂ) ^ 2) *
          bohrCoefficient
            (fun L => ((2 * xiLineScrewSeries L : ℝ) : ℂ)) lam =
        (xiCriticalAbsoluteOrdinateMultiplicity lam : ℂ)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    exact ccmFirstClockArithmeticTrace_entry_recovers_vonMangoldt hk
  · intro s hs
    exact meromorphicOrderAt_xiRectangularWeilFullContinuation_eq_neg_one_iff
      hA hs
  · intro q
    exact normalizedFullObservableResidue_eq_xiRightMultiplicity hA q
  · intro L hL
    exact ccmFirstClockPolarSubtractedSource_eq_critical hL
  · exact continuous_const.mul xiLineScrewSeries_continuous
  · have hcont := xiLineScrewSeries_continuous
    have hap := xiLineScrewSeries_isBohrAlmostPeriodic
    have hadd := isBohrAlmostPeriodic_add hcont hap hcont hap
    change IsBohrAlmostPeriodic (fun t => 2 * xiLineScrewSeries t)
    simpa only [two_mul] using hadd
  · exact ccmFirstClockPolarSubtractedSource_sub_screw_tendsto_zero
  · intro lam hlam
    exact two_mul_xiLineScrewSeries_recovers_multiplicity hlam

end

end RHTower

