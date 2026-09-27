import GaloisForLFunctions.RHTower.CCMRestrictedWeilPrimeInterference
import GaloisForLFunctions.RHTower.CCMActualHeadOutgoingQuantileTransportProducer

/-!
# Collective interference of separated actual prime bands

All von Mangoldt atoms in two fixed-width terminal bands are summed before
their norms are estimated. Every cross-band pair has the same two-step
support nilpotence. The resulting squared-norm saving involves the product
of the complete band masses, rather than the mass of two selected atoms.
-/

open Complex MeasureTheory Set
open scoped BigOperators InnerProduct
noncomputable section
namespace RHTower

def ccmActualPrimeBand (a : SuzukiPositiveAperture) (lo hi : ℝ) : Finset ℕ := by
  classical
  exact (Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊).filter
    (fun n => 2 * a.1 - lo < Real.log n ∧ Real.log n ≤ 2 * a.1 - hi)

def ccmActualPrimeBandMass (a : SuzukiPositiveAperture) (lo hi : ℝ) : ℝ :=
  ∑ n ∈ ccmActualPrimeBand a lo hi, criticalMellinAtomWeight n

def ccmActualPrimeBandOperator (a : SuzukiPositiveAperture) (lo hi : ℝ) :
    suzukiApertureHilbert a →L[ℂ] suzukiApertureHilbert a :=
  ∑ n ∈ ccmActualPrimeBand a lo hi, (criticalMellinAtomWeight n : ℂ) •
    ccmApertureCompression a (ccmSymmetricLogTranslation (Real.log n))

theorem ccmActualPrimeBandMass_nonneg (a : SuzukiPositiveAperture) (lo hi : ℝ) :
    0 ≤ ccmActualPrimeBandMass a lo hi :=
  Finset.sum_nonneg fun n _ =>
    criticalMellinAtomWeight_nonneg_cCMActualHeadWallGramSignedProducer n

private theorem band_lag {a : SuzukiPositiveAperture} {lo hi : ℝ} {n : ℕ}
    (hn : n ∈ ccmActualPrimeBand a lo hi) :
    2 * a.1 - lo < Real.log n ∧ Real.log n ≤ 2 * a.1 - hi :=
  (Finset.mem_filter.mp hn).2

private theorem band_norm_le (a : SuzukiPositiveAperture) (lo hi : ℝ)
    (houter : ∀ n ∈ ccmActualPrimeBand a lo hi, a.1 < Real.log n)
    (f : suzukiApertureHilbert a) :
    ‖ccmActualPrimeBandOperator a lo hi f‖ ≤ ccmActualPrimeBandMass a lo hi * ‖f‖ := by
  classical
  unfold ccmActualPrimeBandOperator ccmActualPrimeBandMass
  rw [ContinuousLinearMap.sum_apply, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
  intro n hn
  have hw := criticalMellinAtomWeight_nonneg_cCMActualHeadWallGramSignedProducer n
  rw [ContinuousLinearMap.smul_apply, norm_smul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hw]
  apply mul_le_mul_of_nonneg_left _ hw
  exact (ContinuousLinearMap.le_opNorm _ f).trans (by
    nlinarith [norm_ccmApertureSymmetricTranslation_le_one a (houter n hn), norm_nonneg f])

private theorem cross_pair_bound (a : SuzukiPositiveAperture) (ha : 4 < a.1)
    {n m : ℕ} (hn : n ∈ ccmActualPrimeBand a 4 3)
    (hm : m ∈ ccmActualPrimeBand a 1 0) (f : suzukiApertureHilbert a) :
    8 * (inner ℂ
      (ccmApertureCompression a (ccmSymmetricLogTranslation (Real.log n)) f)
      (ccmApertureCompression a (ccmSymmetricLogTranslation (Real.log m)) f)).re ≤
        7 * ‖f‖ ^ 2 := by
  have hnlag := band_lag hn
  have hmlag := band_lag hm
  have hno : a.1 < Real.log n := by linarith
  have hmo : a.1 < Real.log m := by linarith
  have horder : Real.log n < Real.log m := by linarith
  let A := ccmApertureCompression a (ccmSymmetricLogTranslation (Real.log n))
  let B := ccmApertureCompression a (ccmSymmetricLogTranslation (Real.log m))
  have hA := norm_ccmApertureSymmetricTranslation_le_one a hno
  have hB := norm_ccmApertureSymmetricTranslation_le_one a hmo
  have hAB : ‖A * B‖ ≤ 1 :=
    (norm_mul_le A B).trans (by nlinarith [norm_nonneg A, norm_nonneg B])
  have hz : (A * B) ^ 2 = 0 :=
    ccmOuterShiftProduct_pow_eq_zero a hno hmo horder 2 (by norm_num) (by
      norm_num
      linarith)
  have h := HTGeometry.nilpotent_contraction_real_inner_gap (A * B) hAB 2 hz f
  have hsa := (ccmApertureCompression_isSelfAdjoint a
    (ccmSymmetricLogTranslation_isSelfAdjoint (Real.log n))).isSymmetric
  have heq : inner ℂ (A f) (B f) = inner ℂ f ((A * B) f) := hsa f (B f)
  change 8 * (inner ℂ (A f) (B f)).re ≤ _
  rw [heq]
  norm_num at h
  exact h

/-- A fixed interference constant for every cross term of the complete two bands. -/
theorem ccmActualPrimeBands_cross_bound
    (a : {a : SuzukiPositiveAperture // 4 < a.1}) (f : suzukiApertureHilbert a.1) :
    8 * (inner ℂ (ccmActualPrimeBandOperator a.1 4 3 f)
      (ccmActualPrimeBandOperator a.1 1 0 f)).re ≤
        7 * ccmActualPrimeBandMass a.1 4 3 * ccmActualPrimeBandMass a.1 1 0 * ‖f‖ ^ 2 := by
  classical
  have hpair (n m : ℕ) (hn : n ∈ ccmActualPrimeBand a.1 4 3)
      (hm : m ∈ ccmActualPrimeBand a.1 1 0) :
      8 * (inner ℂ
        ((criticalMellinAtomWeight n : ℂ) •
          ccmApertureCompression a.1 (ccmSymmetricLogTranslation (Real.log n)) f)
        ((criticalMellinAtomWeight m : ℂ) •
          ccmApertureCompression a.1 (ccmSymmetricLogTranslation (Real.log m)) f)).re ≤
        7 * criticalMellinAtomWeight n * criticalMellinAtomWeight m * ‖f‖ ^ 2 := by
    have h := mul_le_mul_of_nonneg_left (cross_pair_bound a.1 a.2 hn hm f)
      (mul_nonneg
        (criticalMellinAtomWeight_nonneg_cCMActualHeadWallGramSignedProducer n)
        (criticalMellinAtomWeight_nonneg_cCMActualHeadWallGramSignedProducer m))
    rw [inner_smul_real_left, inner_smul_real_right]
    simp only [Complex.smul_re, smul_eq_mul]
    nlinarith only [h]
  have hs := Finset.sum_le_sum fun n hn => Finset.sum_le_sum fun m hm => hpair n m hn hm
  unfold ccmActualPrimeBandOperator ccmActualPrimeBandMass
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    sum_inner, inner_sum, Complex.re_sum]
  simpa only [Finset.mul_sum, Finset.sum_mul, mul_assoc] using hs

/-- Independent of the vector, its coefficients, and the number of atoms in either band. -/
theorem ccmActualPrimeBands_sq_bound
    (a : {a : SuzukiPositiveAperture // 4 < a.1}) (f : suzukiApertureHilbert a.1) :
    4 * ‖ccmActualPrimeBandOperator a.1 4 3 f +
      ccmActualPrimeBandOperator a.1 1 0 f‖ ^ 2 ≤
      (4 * (ccmActualPrimeBandMass a.1 4 3 + ccmActualPrimeBandMass a.1 1 0) ^ 2 -
        ccmActualPrimeBandMass a.1 4 3 * ccmActualPrimeBandMass a.1 1 0) * ‖f‖ ^ 2 := by
  have hL := band_norm_le a.1 4 3 (fun n hn => by
    have h := band_lag hn; linarith [a.2]) f
  have hR := band_norm_le a.1 1 0 (fun n hn => by
    have h := band_lag hn; linarith [a.2]) f
  have hLs := pow_le_pow_left₀ (norm_nonneg _) hL 2
  have hRs := pow_le_pow_left₀ (norm_nonneg _) hR 2
  have hcross := ccmActualPrimeBands_cross_bound a f
  rw [norm_add_sq (𝕜 := ℂ)]
  nlinarith only [hLs, hRs, hcross]

end RHTower
