import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.AffineShellErrorsHavePolynomialHarmonicBounds
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.SmallWidthRealizesTheUpwardPrimeOffsets
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.UpwardKernelLinearizationHasPolynomialCost
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.PrimeBoundaryErrorsHavePolynomialHarmonicBounds
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.NearGammaDownwardCancellationHasPolynomialGrowth

/-!
# Polynomial bounds for the actual upward prime source

Exact finite offsets retain both directions and horizon cutoffs. Polynomial
kernel and boundary estimates, combined with the signed reciprocal-shell
source, bound the normalized squared residual by `K c^10 / sqrt (log N)`.
-/

noncomputable section
open MeasureTheory Finset Filter Topology
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open RenormalizedArithmeticPotentialTheory SpacingScaleHarmonicAnalysis ArithmeticElectrostatics
  BezoutValuationIncidence RenormalizedArithmeticPotentialTheory.CompletedShell

/-- The symmetric reciprocal source inherits the quantitative bound of its two affine shifts. -/
private theorem reciprocalUpwardCoefficient_shell_sq_of_shifted_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    {m N : ℕ} (hm : 1 ≤ m) {K : ℝ}
    (hsource : ∀ c : ℝ, 1 ≤ c → ∀ shift : ℕ → ℕ,
      (∑ n ∈ Icc 1 N, shiftedReciprocalUpwardRowError φ c shift N m n ^ 2) / Real.log N ≤
        K * c ^ 6 / Real.sqrt (Real.log N))
    {c : ℝ} (hc1 : 1 ≤ c) {B : ℕ} (hB : ⌈c⌉₊ ≤ B) :
    (∑ n ∈ Icc 1 N,
      ((reciprocalUpwardCoefficient φ c B N m n -
        ramanujanLagCoefficient m n * shellCorrection φ c m) / Real.sqrt n) ^ 2) / Real.log N ≤
      K * c ^ 6 / Real.sqrt (Real.log N) := by
  have hc : 0 < c := zero_lt_one.trans_le hc1
  have hid : shellCorrectionOfShift φ c m id = shellCorrection φ c m := rfl
  have hrow (n : ℕ) (hn : 1 ≤ n) :
      (reciprocalUpwardCoefficient φ c B N m n -
        ramanujanLagCoefficient m n * shellCorrection φ c m) / Real.sqrt n =
      (shiftedReciprocalUpwardRowError φ c id N m n +
        shiftedReciprocalUpwardRowError φ c (reflectedAffineShift m) N m n) / 2 := by
    rw [reciprocalUpwardCoefficient_eq_shifted_corrections hφ hsupp hc hB N m n hn]
    dsimp only [shiftedReciprocalUpwardRowError]
    rw [hid, shellCorrectionOfShift_reflected hm]
    ring
  have hsum : (∑ n ∈ Icc 1 N,
      ((reciprocalUpwardCoefficient φ c B N m n -
        ramanujanLagCoefficient m n * shellCorrection φ c m) / Real.sqrt n) ^ 2) ≤
      ∑ n ∈ Icc 1 N, (shiftedReciprocalUpwardRowError φ c id N m n ^ 2 +
        shiftedReciprocalUpwardRowError φ c (reflectedAffineShift m) N m n ^ 2) / 2 := by
    apply sum_le_sum
    intro n hn
    rw [hrow n (mem_Icc.mp hn).1]
    nlinarith only [sq_nonneg (shiftedReciprocalUpwardRowError φ c id N m n -
      shiftedReciprocalUpwardRowError φ c (reflectedAffineShift m) N m n)]
  have hfinal := div_le_div_of_nonneg_right hsum (Real.log_natCast_nonneg N)
  rw [← sum_div, sum_add_distrib] at hfinal
  have hp := hsource c hc1 id
  have hn := hsource c hc1 (reflectedAffineShift m)
  have havg : ((∑ n ∈ Icc 1 N, shiftedReciprocalUpwardRowError φ c id N m n ^ 2) +
      ∑ n ∈ Icc 1 N, shiftedReciprocalUpwardRowError φ c (reflectedAffineShift m) N m n ^ 2) /
      2 / Real.log N ≤ K * c ^ 6 / Real.sqrt (Real.log N) := by
    rw [div_right_comm, add_div]
    linarith only [hp, hn]
  exact hfinal.trans havg

/-- Every literal upward source residual has polynomial overlap cost at one common horizon. -/
theorem exists_actualUpwardRowError_polynomial_harmonic_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {m : ℕ} (hm : 1 ≤ m) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c →
      4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ (N : ℝ) →
      (∑ n ∈ Icc 1 N, actualUpwardRowError φ c N m n ^ 2) / Real.log N ≤
        K * c ^ 10 / Real.sqrt (Real.log N) := by
  obtain ⟨Ca, hCa, ha⟩ := exists_logarithmicUpwardCoefficient_polynomial_harmonic_bound hφ hsupp hM m
  obtain ⟨Cb, hCb, hb⟩ := exists_linearizedUpwardCoefficient_boundary_polynomial_harmonic_bound hφ hsupp hM hm
  obtain ⟨Cd, hCd, hd⟩ := exists_shiftedReciprocalUpwardRowError_polynomial_harmonic_bound hm hφ hsupp hM
  let d : ℝ := Real.exp 1 + 2
  let K := 3 * (Ca * d ^ 6 + Cb * d ^ 6 + Cd)
  have hdpos : 0 < d := by dsimp only [d]; positivity
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K, hK, ?_⟩
  have hloglim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hd, eventually_ge_atTop 1, hloglim.eventually_ge_atTop 1] with N hsource hN hlog
  intro c hc1 hlarge
  have hc : 0 < c := zero_lt_one.trans_le hc1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  let B := linearPrimeStrip c
  have hBc : (B : ℝ) ≤ (Real.exp 1 + 1) * c := linearPrimeStrip_le hc1
  have hB1 : (B : ℝ) + 1 ≤ d * c := by dsimp only [d]; nlinarith only [hBc, hc1]
  have hc2 : c ≤ c ^ 2 := by nlinarith only [hc1]
  have hexp := Real.exp_pos 1
  have hwidth : c / N ≤ 1 := by
    apply (div_le_one hN0).mpr
    have hcoef : 1 ≤ 4 * (Real.exp 1 + 3) ^ 2 := by nlinarith only [hexp]
    have h := mul_le_mul_of_nonneg_right hcoef (sq_nonneg c)
    nlinarith only [hlarge, hc2, h]
  have hcN : c ≤ (N : ℝ) := (div_le_one hN0).mp hwidth
  have hBN : B ≤ N := by
    have hcoef : Real.exp 1 + 1 ≤ 4 * (Real.exp 1 + 3) ^ 2 := by nlinarith only [hexp]
    have h1 := mul_le_mul_of_nonneg_left hc2 (show 0 ≤ Real.exp 1 + 1 by positivity)
    have h2 := mul_le_mul_of_nonneg_right hcoef (sq_nonneg c)
    have h : (B : ℝ) ≤ N := by nlinarith only [hBc, h1, h2, hlarge]
    exact_mod_cast h
  have hkernel : 2 * ((Real.exp 1 + 3) * c) * B ≤ (N : ℝ) := by
    have hcoef : 2 * (Real.exp 1 + 3) * (Real.exp 1 + 1) ≤
        4 * (Real.exp 1 + 3) ^ 2 := by nlinarith only [hexp]
    have h1 := mul_le_mul_of_nonneg_left hBc
      (show 0 ≤ 2 * ((Real.exp 1 + 3) * c) by positivity)
    have h2 := mul_le_mul_of_nonneg_right hcoef (sq_nonneg c)
    nlinarith only [h1, h2, hlarge]
  have hB : ⌈c⌉₊ ≤ B := by
    apply Nat.ceil_le.mpr
    have h := mul_le_mul_of_nonneg_left
      (Real.one_le_exp_iff.mpr (by norm_num : (0 : ℝ) ≤ 1)) hc.le
    have hce : c ≤ c * Real.exp 1 := by simpa only [mul_one] using h
    exact hce.trans (Nat.le_ceil _)
  let a : ℕ → ℝ := fun n =>
    (logarithmicUpwardCoefficient φ c B N m n - linearizedUpwardCoefficient φ c B N m n) / Real.sqrt n
  let b : ℕ → ℝ := fun n =>
    (linearizedUpwardCoefficient φ c B N m n - reciprocalUpwardCoefficient φ c B N m n) / Real.sqrt n
  let r : ℕ → ℝ := fun n =>
    (reciprocalUpwardCoefficient φ c B N m n -
      ramanujanLagCoefficient m n * shellCorrection φ c m) / Real.sqrt n
  have ha' : (∑ n ∈ Icc 1 N, a n ^ 2) / Real.log N ≤
      (Ca * d ^ 6) * c ^ 10 / Real.sqrt (Real.log N) := by
    refine (ha N hN hlog c hc1 hwidth B hBN hkernel).trans ?_
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
    have hpow := pow_le_pow_left₀ (show 0 ≤ (B : ℝ) + 1 by positivity) hB1 6
    have h := mul_le_mul_of_nonneg_left hpow (show 0 ≤ Ca * c ^ 4 by positivity)
    exact h.trans_eq (by ring)
  have hb' : (∑ n ∈ Icc 1 N, b n ^ 2) / Real.log N ≤
      (Cb * d ^ 6) * c ^ 10 / Real.sqrt (Real.log N) := by
    refine (hb N hN hlog c hc hcN B).trans ?_
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
    calc
      _ ≤ Cb * (d * c) ^ 6 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hB1 6) hCb.le
      _ = (Cb * d ^ 6) * c ^ 6 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hc1 (by norm_num : 6 ≤ 10)) (by positivity)
  have hr' : (∑ n ∈ Icc 1 N, r n ^ 2) / Real.log N ≤
      Cd * c ^ 10 / Real.sqrt (Real.log N) := by
    refine (reciprocalUpwardCoefficient_shell_sq_of_shifted_bound hφ hsupp hm hsource hc1 hB).trans ?_
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hc1 (by norm_num : 6 ≤ 10)) hCd.le)
      (Real.sqrt_nonneg _)
  have hrow (n : ℕ) (hn : n ∈ Icc 1 N) : actualUpwardRowError φ c N m n = a n + b n + r n := by
    have hs : Real.sqrt n ≠ 0 := (Real.sqrt_pos.mpr
      (by exact_mod_cast (mem_Icc.mp hn).1 : (0 : ℝ) < n)).ne'
    have hu : upwardPrimeRow (atomDilate φ (c / N)) N
        (fun j => ramanujanLagCoefficient m j / Real.sqrt j) n /
          (∫ u, atomDilate φ (c / N) u ^ 2) =
        logarithmicUpwardCoefficient φ c B N m n / Real.sqrt n := by
      apply (eq_div_iff hs).mpr
      simpa only [mul_comm] using sqrt_mul_upwardRamanujanRow_eq_logarithmicCoefficient_small_width
        hsupp hc hn hwidth m
    rw [actualUpwardRowError, hu]
    dsimp only [a, b, r]
    ring
  have hsum : (∑ n ∈ Icc 1 N, actualUpwardRowError φ c N m n ^ 2) ≤
      ∑ n ∈ Icc 1 N, 3 * (a n ^ 2 + b n ^ 2 + r n ^ 2) := by
    apply sum_le_sum
    intro n hn
    rw [hrow n hn]
    nlinarith only [sq_nonneg (a n - b n), sq_nonneg (a n - r n), sq_nonneg (b n - r n)]
  have hfinal := div_le_div_of_nonneg_right hsum (Real.log_natCast_nonneg N)
  rw [← mul_sum, sum_add_distrib, sum_add_distrib, mul_div_assoc, add_div, add_div] at hfinal
  calc
    _ ≤ 3 * ((∑ n ∈ Icc 1 N, a n ^ 2) / Real.log N +
        (∑ n ∈ Icc 1 N, b n ^ 2) / Real.log N + (∑ n ∈ Icc 1 N, r n ^ 2) / Real.log N) := hfinal
    _ ≤ 3 * ((Ca * d ^ 6) * c ^ 10 / Real.sqrt (Real.log N) +
        (Cb * d ^ 6) * c ^ 10 / Real.sqrt (Real.log N) + Cd * c ^ 10 / Real.sqrt (Real.log N)) :=
      mul_le_mul_of_nonneg_left (add_le_add (add_le_add ha' hb') hr') (by norm_num)
    _ = _ := by dsimp only [K]; ring

/-- The actual normalized upward prime vector has the same polynomial squared-norm law. -/
theorem exists_normalizedUpwardPrimeResidual_norm_sq_polynomial_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {m : ℕ} (hm : 1 ≤ m) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c →
      4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ (N : ℝ) →
      ‖normalizedUpwardPrimeResidual φ c N m‖ ^ 2 ≤ K * c ^ 10 / Real.sqrt (Real.log N) := by
  simpa only [normalizedUpwardPrimeResidual_norm_sq] using
    exists_actualUpwardRowError_polynomial_harmonic_bound hφ hsupp hM hm

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_actualUpwardRowError_polynomial_harmonic_bound
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_normalizedUpwardPrimeResidual_norm_sq_polynomial_bound
