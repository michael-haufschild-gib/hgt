import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmWardKernelAbelProjector
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmAdjacentFeatureKreinIndexSeparator

/-!
# Lattice-summed prime--Gamma budget with diagonal multiplicity removed

The raw integer-lattice sum of the critical-feature prime--Gamma diagonal cannot be a useful
off-line budget: every Xi multiplicity copy deposits at least `32/25` in its nearest channel.
The three-quarters scale is only `8/2025`, a factor `324` smaller.  This module proves that
obstruction before introducing the corrected quantity.

The correction subtracts the exact critical-line feature-energy trace from the explicit
prime--Gamma diagonal.  A sharpened sector argument treats critical-line values with constant one
and off-line values with constant one half.  It yields the source comparison

`Ward trace <= 2 * C * (prime--Gamma diagonal - critical-line energy)`.

Finite lattice summation then gives a multiplicity-exact strict-right count and an exact 75%
receiver.  Abel traces approximate the subtracted projector.  What is not proved here is the
remaining arithmetic upper bound for those Abel-corrected lattice budgets; the Abel trace still
uses the Xi divisor and is not itself a pre-divisor pole--Gamma--von-Mangoldt evaluation.
-/

open Complex Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

def criticalFeaturePrimeGammaRawLatticeBudget (K : Finset ℤ) : ℝ :=
  ∑ k ∈ K, (criticalFeaturePrimeGammaSourceDiagonal (k : ℝ)).re

theorem card_mul_criticalFeatureFrameQuantum_le_hermitianLattice
    (K : Finset ℤ) (S : Finset XiZeroCopy)
    (hcenter : ∀ q ∈ S, round (xiSpectralPoint q).re ∈ K) :
    (S.card : ℝ) * (64 / 25 : ℝ) ≤
      ∑ k ∈ K, criticalFeatureHermitianEnergyTrace (k : ℝ) := by
  calc
    (S.card : ℝ) * (64 / 25 : ℝ) = ∑ _q ∈ S, (64 / 25 : ℝ) := by simp
    _ ≤ ∑ q ∈ S, ∑ k ∈ K,
        Complex.normSq (criticalFeatureCauchyKernelTest (k : ℝ) (xiSpectralPoint q)) := by
      gcongr with q hq
      let kq : ℤ := round (xiSpectralPoint q).re
      have hmem : kq ∈ K := hcenter q hq
      have hframe : (64 / 25 : ℝ) ≤
          Complex.normSq
            (HedenmalmThetaSource.criticalEvaluation
              (xiSpectralPoint q) (abs_xiSpectralPoint_im_lt_half q)
              (HedenmalmThetaSource.criticalFeature ((kq : ℝ) : ℂ) (by norm_num))) := by
        apply normSq_criticalEvaluation_realCriticalFeature_ge_of_abs_sub_le_half
        exact abs_sub_round _
      have heq :
          HedenmalmThetaSource.criticalEvaluation
              (xiSpectralPoint q) (abs_xiSpectralPoint_im_lt_half q)
              (HedenmalmThetaSource.criticalFeature ((kq : ℝ) : ℂ) (by norm_num)) =
            criticalFeatureCauchyKernelTest (kq : ℝ) (xiSpectralPoint q) := by
        rw [criticalEvaluation_realCriticalFeature_eq_hardyCauchySum]
        rfl
      rw [heq] at hframe
      exact hframe.trans (Finset.single_le_sum (s := K) (a := kq)
        (f := fun k : ℤ => Complex.normSq
          (criticalFeatureCauchyKernelTest (k : ℝ) (xiSpectralPoint q)))
        (fun k hk => Complex.normSq_nonneg _) hmem)
    _ = ∑ k ∈ K, ∑ q ∈ S,
        Complex.normSq (criticalFeatureCauchyKernelTest (k : ℝ) (xiSpectralPoint q)) := by
      rw [Finset.sum_comm]
    _ ≤ ∑ k ∈ K, criticalFeatureHermitianEnergyTrace (k : ℝ) := by
      gcongr with k hk
      exact (criticalFeatureHermitianEnergy_summable (k : ℝ)).sum_le_tsum S
        (fun q _ => Complex.normSq_nonneg _)

theorem card_mul_thirtyTwo_twentyFive_le_rawLatticeBudget
    (K : Finset ℤ) (S : Finset XiZeroCopy)
    (hcenter : ∀ q ∈ S, round (xiSpectralPoint q).re ∈ K) :
    (S.card : ℝ) * (32 / 25 : ℝ) ≤
      criticalFeaturePrimeGammaRawLatticeBudget K := by
  have hframe := card_mul_criticalFeatureFrameQuantum_le_hermitianLattice K S hcenter
  have hsource :
      (∑ k ∈ K, criticalFeatureHermitianEnergyTrace (k : ℝ)) ≤
        2 * criticalFeaturePrimeGammaRawLatticeBudget K := by
    rw [criticalFeaturePrimeGammaRawLatticeBudget, Finset.mul_sum]
    gcongr with k hk
    simpa [xiWeilPolarization_criticalFeatureCauchyKernelTest_eq_sourceDiagonal]
      using criticalFeatureHermitianEnergyTrace_le_two_re_xiWeilPolarization (k : ℝ)
  nlinarith

theorem rawLatticeBudget_threeQuartersScale_forces_empty
    (K : Finset ℤ) (S : Finset XiZeroCopy)
    (hcenter : ∀ q ∈ S, round (xiSpectralPoint q).re ∈ K)
    (hbudget : criticalFeaturePrimeGammaRawLatticeBudget K ≤
      (S.card : ℝ) * (8 / 2025 : ℝ)) :
    S = ∅ := by
  have hlower := card_mul_thirtyTwo_twentyFive_le_rawLatticeBudget K S hcenter
  have hcard : (S.card : ℝ) = 0 := by
    have hnonneg : (0 : ℝ) ≤ S.card := by positivity
    nlinarith
  exact Finset.card_eq_zero.mp (by exact_mod_cast hcard)

theorem criticalFeatureEnergy_add_lineEnergy_le_two_re_sq
    (t : ℝ) (q : XiZeroCopy) :
    Complex.normSq (criticalFeatureCauchyKernelTest t (xiSpectralPoint q)) +
        criticalLineCriticalFeatureEnergy t q ≤
      2 * ((criticalFeatureCauchyKernelTest t (xiSpectralPoint q)) ^ (2 : ℕ)).re := by
  by_cases hq : (q.1 : ℂ).re = 1 / 2
  · rw [criticalLineCriticalFeatureEnergy, if_pos hq]
    have hspim : (xiSpectralPoint q).im = 0 := by
      rw [xiSpectralPoint_im_eq, hq]
      ring
    have heq :
        HedenmalmThetaSource.criticalEvaluation
            (xiSpectralPoint q) (abs_xiSpectralPoint_im_lt_half q)
            (HedenmalmThetaSource.criticalFeature (t : ℂ) (by norm_num)) =
          criticalFeatureCauchyKernelTest t (xiSpectralPoint q) := by
      rw [criticalEvaluation_realCriticalFeature_eq_hardyCauchySum]
      rfl
    have hFim :
        (criticalFeatureCauchyKernelTest t (xiSpectralPoint q)).im = 0 := by
      rw [← heq]
      exact criticalEvaluation_realCriticalFeature_im_eq_zero_of_im_eq_zero
        t (abs_xiSpectralPoint_im_lt_half q) hspim
    rw [Complex.normSq_apply]
    simp [pow_two, Complex.mul_re, hFim]
    nlinarith
  · rw [criticalLineCriticalFeatureEnergy, if_neg hq, add_zero]
    have hsector := half_mul_normSq_criticalFeatureCauchyKernelTest_le_re_sq
      t (abs_xiSpectralPoint_im_lt_half q)
    nlinarith

theorem criticalFeatureHermitian_add_line_le_two_sourceDiagonal (t : ℝ) :
    criticalFeatureHermitianEnergyTrace t +
        criticalLineCriticalFeatureEnergyTrace t ≤
      2 * (criticalFeaturePrimeGammaSourceDiagonal t).re := by
  let F : ℂ → ℂ := criticalFeatureCauchyKernelTest t
  have hnorm : Summable (fun q : XiZeroCopy =>
      Complex.normSq (F (xiSpectralPoint q))) := by
    simpa only [F] using criticalFeatureHermitianEnergy_summable t
  have hleft : Summable (fun q : XiZeroCopy =>
      Complex.normSq (F (xiSpectralPoint q)) +
        criticalLineCriticalFeatureEnergy t q) :=
    hnorm.add (criticalLineCriticalFeatureEnergy_summable t)
  have hsquareNorm : Summable (fun q : XiZeroCopy =>
      ‖(F (xiSpectralPoint q)) ^ (2 : ℕ)‖) := by
    simpa only [norm_pow, Complex.normSq_eq_norm_sq] using hnorm
  have hsquare : Summable (fun q : XiZeroCopy =>
      (F (xiSpectralPoint q)) ^ (2 : ℕ)) := summable_norm_iff.mp hsquareNorm
  have hre : Summable (fun q : XiZeroCopy =>
      ((F (xiSpectralPoint q)) ^ (2 : ℕ)).re) := by
    exact hsquare.map Complex.reCLM Complex.reCLM.continuous
  have hright : Summable (fun q : XiZeroCopy =>
      2 * ((F (xiSpectralPoint q)) ^ (2 : ℕ)).re) := hre.mul_left 2
  have hsum := hleft.tsum_le_tsum
    (fun q => by simpa only [F] using
      criticalFeatureEnergy_add_lineEnergy_le_two_re_sq t q) hright
  calc
    criticalFeatureHermitianEnergyTrace t +
        criticalLineCriticalFeatureEnergyTrace t =
        ∑' q : XiZeroCopy,
          (Complex.normSq (F (xiSpectralPoint q)) +
            criticalLineCriticalFeatureEnergy t q) := by
      rw [criticalFeatureHermitianEnergyTrace,
        criticalLineCriticalFeatureEnergyTrace]
      change (∑' q : XiZeroCopy, Complex.normSq (F (xiSpectralPoint q))) +
          (∑' q : XiZeroCopy, criticalLineCriticalFeatureEnergy t q) = _
      rw [← hnorm.tsum_add (criticalLineCriticalFeatureEnergy_summable t)]
    _ ≤ ∑' q : XiZeroCopy, 2 * ((F (xiSpectralPoint q)) ^ (2 : ℕ)).re := hsum
    _ = 2 * (∑' q : XiZeroCopy, ((F (xiSpectralPoint q)) ^ (2 : ℕ)).re) := by
      rw [tsum_mul_left]
    _ = 2 * (∑' q : XiZeroCopy, (F (xiSpectralPoint q)) ^ (2 : ℕ)).re := by
      rw [Complex.re_tsum hsquare]
    _ = 2 * (xiWeilPolarization F F).re := by
      unfold xiWeilPolarization
      rw [show xiWeilSharp F = F by
        simpa only [F] using xiWeilSharp_criticalFeatureCauchyKernelTest t]
      congr 2
      apply tsum_congr
      intro q
      ring
    _ = 2 * (criticalFeaturePrimeGammaSourceDiagonal t).re := by
      rw [show xiWeilPolarization F F =
          criticalFeaturePrimeGammaSourceDiagonal t by
        simpa only [F] using
          xiWeilPolarization_criticalFeatureCauchyKernelTest_eq_sourceDiagonal t]

/-- Prime--Gamma diagonal after deleting its exact critical-line multiplicity channel. -/
def criticalFeaturePrimeGammaOffLineExcess (t : ℝ) : ℝ :=
  (criticalFeaturePrimeGammaSourceDiagonal t).re -
    criticalLineCriticalFeatureEnergyTrace t

/-- The real holomorphic critical-feature diagonal never exceeds its Hermitian diagonal. -/
theorem re_criticalFeaturePrimeGammaSourceDiagonal_le_hermitianEnergyTrace (t : ℝ) :
    (criticalFeaturePrimeGammaSourceDiagonal t).re ≤
      criticalFeatureHermitianEnergyTrace t := by
  let F : ℂ → ℂ := criticalFeatureCauchyKernelTest t
  have hnorm : Summable (fun q : XiZeroCopy =>
      Complex.normSq (F (xiSpectralPoint q))) := by
    simpa only [F] using criticalFeatureHermitianEnergy_summable t
  have hsquareNorm : Summable (fun q : XiZeroCopy =>
      ‖(F (xiSpectralPoint q)) ^ (2 : ℕ)‖) := by
    simpa only [norm_pow, Complex.normSq_eq_norm_sq] using hnorm
  have hsquare : Summable (fun q : XiZeroCopy =>
      (F (xiSpectralPoint q)) ^ (2 : ℕ)) := summable_norm_iff.mp hsquareNorm
  have hre : Summable (fun q : XiZeroCopy =>
      ((F (xiSpectralPoint q)) ^ (2 : ℕ)).re) := by
    exact hsquare.map Complex.reCLM Complex.reCLM.continuous
  have hpoint (q : XiZeroCopy) :
      ((F (xiSpectralPoint q)) ^ (2 : ℕ)).re ≤
        Complex.normSq (F (xiSpectralPoint q)) := by
    rw [Complex.normSq_apply]
    simp only [pow_two, Complex.mul_re]
    nlinarith [sq_nonneg (F (xiSpectralPoint q)).im]
  have hsum := hre.tsum_le_tsum hpoint hnorm
  calc
    (criticalFeaturePrimeGammaSourceDiagonal t).re =
        (xiWeilPolarization F F).re := by
      rw [show xiWeilPolarization F F =
          criticalFeaturePrimeGammaSourceDiagonal t by
        simpa only [F] using
          xiWeilPolarization_criticalFeatureCauchyKernelTest_eq_sourceDiagonal t]
    _ = (∑' q : XiZeroCopy, (F (xiSpectralPoint q)) ^ (2 : ℕ)).re := by
      unfold xiWeilPolarization
      rw [show xiWeilSharp F = F by
        simpa only [F] using xiWeilSharp_criticalFeatureCauchyKernelTest t]
      congr 2
      funext q
      ring
    _ = ∑' q : XiZeroCopy, ((F (xiSpectralPoint q)) ^ (2 : ℕ)).re := by
      rw [Complex.re_tsum hsquare]
    _ ≤ ∑' q : XiZeroCopy,
        Complex.normSq (F (xiSpectralPoint q)) := hsum
    _ = criticalFeatureHermitianEnergyTrace t := by rfl

theorem offLineCriticalFeatureEnergyTrace_le_two_primeGammaOffLineExcess (t : ℝ) :
    offLineCriticalFeatureEnergyTrace t ≤
      2 * criticalFeaturePrimeGammaOffLineExcess t := by
  have henhanced := criticalFeatureHermitian_add_line_le_two_sourceDiagonal t
  have hsplit := criticalFeatureHermitianEnergyTrace_eq_line_add_offLine t
  rw [criticalFeaturePrimeGammaOffLineExcess]
  linarith

/-- The diagonal-subtracted source excess is at most the exact off-line Hermitian energy.  Together
with `offLineCriticalFeatureEnergyTrace_le_two_primeGammaOffLineExcess`, this identifies the
corrected quantity, up to the sharp sector factor two, as a post-divisor off-line energy. -/
theorem primeGammaOffLineExcess_le_offLineCriticalFeatureEnergyTrace (t : ℝ) :
    criticalFeaturePrimeGammaOffLineExcess t ≤
      offLineCriticalFeatureEnergyTrace t := by
  have hsource :=
    re_criticalFeaturePrimeGammaSourceDiagonal_le_hermitianEnergyTrace t
  have hsplit := criticalFeatureHermitianEnergyTrace_eq_line_add_offLine t
  rw [criticalFeaturePrimeGammaOffLineExcess]
  linarith

theorem criticalFeaturePrimeGammaOffLineExcess_nonneg (t : ℝ) :
    0 ≤ criticalFeaturePrimeGammaOffLineExcess t := by
  have hoff := offLineCriticalFeatureEnergyTrace_le_two_primeGammaOffLineExcess t
  have hoffnonneg : 0 ≤ offLineCriticalFeatureEnergyTrace t := by
    rw [offLineCriticalFeatureEnergyTrace]
    exact tsum_nonneg (offLineCriticalFeatureEnergy_nonneg t)
  linarith

/-- A single corrected feature channel vanishes exactly under RH. -/
theorem criticalFeaturePrimeGammaOffLineExcess_eq_zero_iff_rh (t : ℝ) :
    criticalFeaturePrimeGammaOffLineExcess t = 0 ↔ RiemannHypothesis := by
  constructor
  · intro hzero
    apply (offLineCriticalFeatureEnergyTrace_eq_zero_iff_rh t).mp
    have hlower := offLineCriticalFeatureEnergyTrace_le_two_primeGammaOffLineExcess t
    have hnonneg : 0 ≤ offLineCriticalFeatureEnergyTrace t := by
      rw [offLineCriticalFeatureEnergyTrace]
      exact tsum_nonneg (offLineCriticalFeatureEnergy_nonneg t)
    rw [hzero] at hlower
    linarith
  · intro hRH
    have hoff := (offLineCriticalFeatureEnergyTrace_eq_zero_iff_rh t).mpr hRH
    have hnonneg := criticalFeaturePrimeGammaOffLineExcess_nonneg t
    have hupper := primeGammaOffLineExcess_le_offLineCriticalFeatureEnergyTrace t
    rw [hoff] at hupper
    linarith

theorem fiveShiftCriticalFeatureWardGreenCurrent_le_offLineEnergy
    (t : ℝ) (q : XiZeroCopy) :
    fiveShiftCriticalFeatureWardGreenCurrent t q ≤
      fiveShiftWardGreenUpperConstant * offLineCriticalFeatureEnergy t q := by
  by_cases hq : (q.1 : ℂ).re = 1 / 2
  · have hzero :=
      (fiveShiftCriticalFeatureWardGreenCurrent_eq_zero_iff_line t q).mpr hq
    rw [hzero, offLineCriticalFeatureEnergy, if_pos hq]
    simp
  · rw [offLineCriticalFeatureEnergy, if_neg hq]
    have hle := fiveShiftCriticalFeatureWardGreenCurrent_le t q
    have heq :
        HedenmalmThetaSource.criticalEvaluation
            (xiSpectralPoint q) (abs_xiSpectralPoint_im_lt_half q)
            (HedenmalmThetaSource.criticalFeature (t : ℂ) (by norm_num)) =
          criticalFeatureCauchyKernelTest t (xiSpectralPoint q) := by
      rw [criticalEvaluation_realCriticalFeature_eq_hardyCauchySum]
      rfl
    simpa only [heq] using hle

theorem fiveShiftCriticalFeatureWardGreenTrace_le_offLineEnergy (t : ℝ) :
    fiveShiftCriticalFeatureWardGreenTrace t ≤
      fiveShiftWardGreenUpperConstant * offLineCriticalFeatureEnergyTrace t := by
  have hmajor : Summable (fun q : XiZeroCopy =>
      fiveShiftWardGreenUpperConstant * offLineCriticalFeatureEnergy t q) :=
    (offLineCriticalFeatureEnergy_summable t).mul_left
      fiveShiftWardGreenUpperConstant
  have hsum := (fiveShiftCriticalFeatureWardGreenCurrent_summable t).tsum_le_tsum
    (fiveShiftCriticalFeatureWardGreenCurrent_le_offLineEnergy t) hmajor
  rw [fiveShiftCriticalFeatureWardGreenTrace,
    offLineCriticalFeatureEnergyTrace, ← tsum_mul_left]
  exact hsum

/-- Corrected fixed-channel source inequality: critical-line multiplicity is subtracted before
the Ward ceiling is applied. -/
theorem fiveShiftCriticalFeatureWardGreenTrace_le_primeGammaOffLineExcess (t : ℝ) :
    fiveShiftCriticalFeatureWardGreenTrace t ≤
      2 * fiveShiftWardGreenUpperConstant *
        criticalFeaturePrimeGammaOffLineExcess t := by
  have hmul := mul_le_mul_of_nonneg_left
    (offLineCriticalFeatureEnergyTrace_le_two_primeGammaOffLineExcess t)
    fiveShiftWardGreenUpperConstant_nonneg
  exact (fiveShiftCriticalFeatureWardGreenTrace_le_offLineEnergy t).trans
    (by simpa [mul_assoc, mul_left_comm, mul_comm] using hmul)

def criticalFeaturePrimeGammaOffLineLatticeBudget (K : Finset ℤ) : ℝ :=
  ∑ k ∈ K, criticalFeaturePrimeGammaOffLineExcess (k : ℝ)

def fiveShiftCriticalFeatureWardGreenLatticeTrace (K : Finset ℤ) : ℝ :=
  ∑ k ∈ K, fiveShiftCriticalFeatureWardGreenTrace (k : ℝ)

theorem primeGammaOffLineLatticeBudget_nonneg (K : Finset ℤ) :
    0 ≤ criticalFeaturePrimeGammaOffLineLatticeBudget K := by
  rw [criticalFeaturePrimeGammaOffLineLatticeBudget]
  exact Finset.sum_nonneg (fun k hk =>
    criticalFeaturePrimeGammaOffLineExcess_nonneg (k : ℝ))

/-- The corrected lattice budget is bounded above by the corresponding exact off-line energy. -/
theorem primeGammaOffLineLatticeBudget_le_offLineEnergy (K : Finset ℤ) :
    criticalFeaturePrimeGammaOffLineLatticeBudget K ≤
      ∑ k ∈ K, offLineCriticalFeatureEnergyTrace (k : ℝ) := by
  rw [criticalFeaturePrimeGammaOffLineLatticeBudget]
  gcongr with k hk
  exact primeGammaOffLineExcess_le_offLineCriticalFeatureEnergyTrace (k : ℝ)

/-- Every nonempty corrected lattice detects RH exactly at zero budget. -/
theorem primeGammaOffLineLatticeBudget_eq_zero_iff_rh
    {K : Finset ℤ} (hK : K.Nonempty) :
    criticalFeaturePrimeGammaOffLineLatticeBudget K = 0 ↔ RiemannHypothesis := by
  constructor
  · intro hzero
    obtain ⟨k, hk⟩ := hK
    have htermNonneg :
        0 ≤ criticalFeaturePrimeGammaOffLineExcess (k : ℝ) :=
      criticalFeaturePrimeGammaOffLineExcess_nonneg (k : ℝ)
    have htermLe :
        criticalFeaturePrimeGammaOffLineExcess (k : ℝ) ≤
          criticalFeaturePrimeGammaOffLineLatticeBudget K := by
      rw [criticalFeaturePrimeGammaOffLineLatticeBudget]
      exact Finset.single_le_sum (s := K) (a := k)
        (f := fun j : ℤ => criticalFeaturePrimeGammaOffLineExcess (j : ℝ))
        (fun j hj => criticalFeaturePrimeGammaOffLineExcess_nonneg (j : ℝ)) hk
    have htermZero : criticalFeaturePrimeGammaOffLineExcess (k : ℝ) = 0 := by
      rw [hzero] at htermLe
      linarith
    exact (criticalFeaturePrimeGammaOffLineExcess_eq_zero_iff_rh (k : ℝ)).mp htermZero
  · intro hRH
    rw [criticalFeaturePrimeGammaOffLineLatticeBudget]
    apply Finset.sum_eq_zero
    intro k hk
    exact (criticalFeaturePrimeGammaOffLineExcess_eq_zero_iff_rh (k : ℝ)).mpr hRH

theorem fiveShiftCriticalFeatureWardGreenLatticeTrace_le_budget (K : Finset ℤ) :
    fiveShiftCriticalFeatureWardGreenLatticeTrace K ≤
      2 * fiveShiftWardGreenUpperConstant *
        criticalFeaturePrimeGammaOffLineLatticeBudget K := by
  rw [fiveShiftCriticalFeatureWardGreenLatticeTrace,
    criticalFeaturePrimeGammaOffLineLatticeBudget, Finset.mul_sum]
  gcongr with k hk
  exact fiveShiftCriticalFeatureWardGreenTrace_le_primeGammaOffLineExcess (k : ℝ)

/-- Every finite strict-right packet deposits the full nearest-feature frame quantum into the
off-line lattice energy. -/
theorem finite_strictRight_card_mul_frameQuantum_le_offLineLatticeEnergy
    (K : Finset ℤ) (S : Finset XiZeroCopy)
    (hright : ∀ q ∈ S, 0 < (I * xiSpectralPoint q).re)
    (hcenter : ∀ q ∈ S, round (xiSpectralPoint q).re ∈ K) :
    (S.card : ℝ) * (64 / 25 : ℝ) ≤
      ∑ k ∈ K, offLineCriticalFeatureEnergyTrace (k : ℝ) := by
  calc
    (S.card : ℝ) * (64 / 25 : ℝ) = ∑ _q ∈ S, (64 / 25 : ℝ) := by simp
    _ ≤ ∑ q ∈ S, ∑ k ∈ K, offLineCriticalFeatureEnergy (k : ℝ) q := by
      gcongr with q hq
      let kq : ℤ := round (xiSpectralPoint q).re
      have hmem : kq ∈ K := hcenter q hq
      have hqoff : (q.1 : ℂ).re ≠ 1 / 2 := by
        intro hline
        have hp := hright q hq
        rw [I_mul_xiSpectralPoint, Complex.sub_re, hline] at hp
        norm_num at hp
      have hframe : (64 / 25 : ℝ) ≤
          Complex.normSq
            (HedenmalmThetaSource.criticalEvaluation
              (xiSpectralPoint q) (abs_xiSpectralPoint_im_lt_half q)
              (HedenmalmThetaSource.criticalFeature ((kq : ℝ) : ℂ) (by norm_num))) := by
        apply normSq_criticalEvaluation_realCriticalFeature_ge_of_abs_sub_le_half
        exact abs_sub_round _
      have heq :
          HedenmalmThetaSource.criticalEvaluation
              (xiSpectralPoint q) (abs_xiSpectralPoint_im_lt_half q)
              (HedenmalmThetaSource.criticalFeature ((kq : ℝ) : ℂ) (by norm_num)) =
            criticalFeatureCauchyKernelTest (kq : ℝ) (xiSpectralPoint q) := by
        rw [criticalEvaluation_realCriticalFeature_eq_hardyCauchySum]
        rfl
      rw [heq] at hframe
      have hoffeq :
          Complex.normSq
              (criticalFeatureCauchyKernelTest (kq : ℝ) (xiSpectralPoint q)) =
            offLineCriticalFeatureEnergy (kq : ℝ) q := by
        rw [offLineCriticalFeatureEnergy, if_neg hqoff]
      rw [hoffeq] at hframe
      exact hframe.trans (Finset.single_le_sum (s := K) (a := kq)
        (f := fun k : ℤ => offLineCriticalFeatureEnergy (k : ℝ) q)
        (fun k hk => offLineCriticalFeatureEnergy_nonneg (k : ℝ) q) hmem)
    _ = ∑ k ∈ K, ∑ q ∈ S, offLineCriticalFeatureEnergy (k : ℝ) q := by
      rw [Finset.sum_comm]
    _ ≤ ∑ k ∈ K, offLineCriticalFeatureEnergyTrace (k : ℝ) := by
      gcongr with k hk
      exact (offLineCriticalFeatureEnergy_summable (k : ℝ)).sum_le_tsum S
        (fun q _ => offLineCriticalFeatureEnergy_nonneg (k : ℝ) q)

/-- Sharp lattice count directly from the diagonal-subtracted prime--Gamma budget.  This avoids
the coarse five-shift Ward ceiling entirely. -/
theorem finite_strictRight_card_mul_thirtyTwo_twentyFive_le_offLineLatticeBudget
    (K : Finset ℤ) (S : Finset XiZeroCopy)
    (hright : ∀ q ∈ S, 0 < (I * xiSpectralPoint q).re)
    (hcenter : ∀ q ∈ S, round (xiSpectralPoint q).re ∈ K) :
    (S.card : ℝ) * (32 / 25 : ℝ) ≤
      criticalFeaturePrimeGammaOffLineLatticeBudget K := by
  have hframe :=
    finite_strictRight_card_mul_frameQuantum_le_offLineLatticeEnergy
      K S hright hcenter
  have hsource :
      (∑ k ∈ K, offLineCriticalFeatureEnergyTrace (k : ℝ)) ≤
        2 * criticalFeaturePrimeGammaOffLineLatticeBudget K := by
    rw [criticalFeaturePrimeGammaOffLineLatticeBudget, Finset.mul_sum]
    gcongr with k hk
    exact offLineCriticalFeatureEnergyTrace_le_two_primeGammaOffLineExcess (k : ℝ)
  nlinarith

/-- Exact 75% receiver at the sharp corrected-source scale `4N/25`. -/
theorem three_quarters_line_of_sharp_primeGammaOffLineLatticeBudget
    {N N₀ : ℝ} (K : Finset ℤ) (S : Finset XiZeroCopy)
    (hright : ∀ q ∈ S, 0 < (I * xiSpectralPoint q).re)
    (hcenter : ∀ q ∈ S, round (xiSpectralPoint q).re ∈ K)
    (hsplit : N = N₀ + 2 * S.card)
    (hbudget : criticalFeaturePrimeGammaOffLineLatticeBudget K ≤
      (4 / 25 : ℝ) * N) :
    3 * N / 4 ≤ N₀ := by
  have hcharge :=
    finite_strictRight_card_mul_thirtyTwo_twentyFive_le_offLineLatticeBudget
      K S hright hcenter
  have hcount : (S.card : ℝ) ≤ N / 8 := by
    nlinarith
  nlinarith

theorem finite_strictRight_card_mul_quantum_le_wardGreenLatticeTrace
    (K : Finset ℤ) (S : Finset XiZeroCopy)
    (hright : ∀ q ∈ S, 0 < (I * xiSpectralPoint q).re)
    (hcenter : ∀ q ∈ S, round (xiSpectralPoint q).re ∈ K) :
    (S.card : ℝ) * (64 / 2025 : ℝ) ≤
      fiveShiftCriticalFeatureWardGreenLatticeTrace K := by
  calc
    (S.card : ℝ) * (64 / 2025 : ℝ) = ∑ _q ∈ S, (64 / 2025 : ℝ) := by simp
    _ ≤ ∑ q ∈ S, ∑ k ∈ K,
        fiveShiftCriticalFeatureWardGreenCurrent (k : ℝ) q := by
      gcongr with q hq
      let qr : XiRightZeroCopy := ⟨q, hright q hq⟩
      let kq : ℤ := round (xiSpectralPoint q).re
      have hmem : kq ∈ K := hcenter q hq
      have hquantum :=
        fiveShiftCriticalFeatureWardGreenCurrent_xiRightZeroCopy_round_ge qr
      change (64 / 2025 : ℝ) ≤
        fiveShiftCriticalFeatureWardGreenCurrent (kq : ℝ) q at hquantum
      exact hquantum.trans (Finset.single_le_sum (s := K) (a := kq)
        (f := fun k : ℤ => fiveShiftCriticalFeatureWardGreenCurrent (k : ℝ) q)
        (fun k hk => fiveShiftCriticalFeatureWardGreenCurrent_nonneg (k : ℝ) q) hmem)
    _ = ∑ k ∈ K, ∑ q ∈ S,
        fiveShiftCriticalFeatureWardGreenCurrent (k : ℝ) q := by
      rw [Finset.sum_comm]
    _ ≤ ∑ k ∈ K, fiveShiftCriticalFeatureWardGreenTrace (k : ℝ) := by
      gcongr with k hk
      exact (fiveShiftCriticalFeatureWardGreenCurrent_summable (k : ℝ)).sum_le_tsum S
        (fun q _ => fiveShiftCriticalFeatureWardGreenCurrent_nonneg (k : ℝ) q)
    _ = fiveShiftCriticalFeatureWardGreenLatticeTrace K := by
      rfl

theorem finite_strictRight_card_mul_quantum_le_primeGammaOffLineLatticeBudget
    (K : Finset ℤ) (S : Finset XiZeroCopy)
    (hright : ∀ q ∈ S, 0 < (I * xiSpectralPoint q).re)
    (hcenter : ∀ q ∈ S, round (xiSpectralPoint q).re ∈ K) :
    (S.card : ℝ) * (64 / 2025 : ℝ) ≤
      2 * fiveShiftWardGreenUpperConstant *
        criticalFeaturePrimeGammaOffLineLatticeBudget K := by
  exact (finite_strictRight_card_mul_quantum_le_wardGreenLatticeTrace
    K S hright hcenter).trans
      (fiveShiftCriticalFeatureWardGreenLatticeTrace_le_budget K)

theorem three_quarters_line_of_primeGammaOffLineLatticeBudget
    {N N₀ : ℝ} (K : Finset ℤ) (S : Finset XiZeroCopy)
    (hright : ∀ q ∈ S, 0 < (I * xiSpectralPoint q).re)
    (hcenter : ∀ q ∈ S, round (xiSpectralPoint q).re ∈ K)
    (hsplit : N = N₀ + 2 * S.card)
    (hbudget : 2 * fiveShiftWardGreenUpperConstant *
      criticalFeaturePrimeGammaOffLineLatticeBudget K ≤
        (64 / 2025 : ℝ) * (N / 8)) :
    3 * N / 4 ≤ N₀ := by
  have hcharge :=
    finite_strictRight_card_mul_quantum_le_primeGammaOffLineLatticeBudget
      K S hright hcenter
  have hcount : (S.card : ℝ) ≤ N / 8 := by
    nlinarith
  nlinarith

def criticalFeaturePrimeGammaAbelOffLineLatticeBudget
    (n : ℕ) (K : Finset ℤ) : ℝ :=
  ∑ k ∈ K, ((criticalFeaturePrimeGammaSourceDiagonal (k : ℝ)).re -
    thetaXiWardKernelAbelCriticalFeatureTrace n (k : ℝ))

theorem tendsto_criticalFeaturePrimeGammaAbelOffLineLatticeBudget
    (K : Finset ℤ) :
    Tendsto
      (fun n : ℕ => criticalFeaturePrimeGammaAbelOffLineLatticeBudget n K)
      atTop (𝓝 (criticalFeaturePrimeGammaOffLineLatticeBudget K)) := by
  simp only [criticalFeaturePrimeGammaAbelOffLineLatticeBudget,
    criticalFeaturePrimeGammaOffLineLatticeBudget,
    criticalFeaturePrimeGammaOffLineExcess]
  apply tendsto_finsetSum K
  intro k hk
  exact tendsto_const_nhds.sub
    (tendsto_thetaXiWardKernelAbelCriticalFeatureTrace (k : ℝ))

end

end RHTower
