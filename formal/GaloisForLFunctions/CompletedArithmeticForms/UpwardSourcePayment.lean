import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.AffineShellErrorsHavePolynomialHarmonicBounds
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.PrimeBoundaryErrorsHavePolynomialHarmonicBounds
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.UpwardKernelLinearizationHasPolynomialCost
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.SmallWidthRealizesTheUpwardPrimeOffsets
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheActualUpwardSourceIsUniformOnBoundedOverlap

/-!
# Quantitative payment of the actual upward source

The literal prime-power action has a polynomial overlap cost. Its kernel
linearization retains the stronger squared `log N / N` factor, separately
from the harmonic boundary and affine-shell costs. The finite strip has
width `ceil (e c)` and keeps both signs and both horizon cutoffs.
-/

noncomputable section

open MeasureTheory Finset Filter Topology

namespace GaloisForLFunctions.CompletedArithmeticForms

open CriticalArithmeticCorrelationTheory RenormalizedArithmeticPotentialTheory
  SpacingScaleHarmonicAnalysis ArithmeticElectrostatics BezoutValuationIncidence

/-- The logarithmic kernel retains its actual squared horizon decay. -/
theorem exists_logarithmicUpward_error_sharp_horizon_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 1 ≤ N → 1 ≤ Real.log (N : ℝ) →
      ∀ c : ℝ, 1 ≤ c → c / N ≤ 1 → ∀ B : ℕ, B ≤ N →
      2 * ((Real.exp 1 + 3) * c) * B ≤ (N : ℝ) →
      (∑ n ∈ Icc 1 N,
        ((logarithmicUpwardCoefficient φ c B N m n -
          linearizedUpwardCoefficient φ c B N m n) / Real.sqrt n) ^ 2) / Real.log N ≤
        K * c ^ 4 * ((B : ℝ) + 1) ^ 6 * (Real.log (N : ℝ) / N) ^ 2 := by
  obtain ⟨D, hD, hsource⟩ := exists_logarithmicUpwardCoefficient_polynomial_bound hφ hsupp hM m
  obtain ⟨J, hJ, hmert⟩ := exists_mertensSum_add_le_log_multiple
  let E := D * (J + 2)
  refine ⟨2 * E ^ 2, by positivity, ?_⟩
  intro N hN hL c hc hw B hBN hlarge
  let a := E * c ^ 2 * ((B : ℝ) + 1) ^ 3 * (Real.log N / N)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hL0 : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hL
  have ha : ∀ n : ℕ, 1 ≤ n →
      |logarithmicUpwardCoefficient φ c B N m n - linearizedUpwardCoefficient φ c B N m n| ≤ a := by
    intro n hn
    refine (hsource c hc B N hN hw hlarge n hn).trans ?_
    calc
      _ ≤ D * c ^ 2 * ((B : ℝ) + 1) ^ 3 * ((J + 2) * Real.log N) / N :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hmert N B hN hL hBN) (by positivity)) hN0.le
      _ = _ := by dsimp only [a, E]; ring
  have hsum : (∑ n ∈ Icc 1 N,
      ((logarithmicUpwardCoefficient φ c B N m n - linearizedUpwardCoefficient φ c B N m n) /
        Real.sqrt n) ^ 2) ≤ a ^ 2 * (harmonic N : ℝ) := by
    calc
      _ ≤ ∑ n ∈ Icc 1 N, a ^ 2 / (n : ℝ) := by
        apply sum_le_sum
        intro n hn
        have hsq := mul_self_le_mul_self (abs_nonneg _) (ha n (mem_Icc.mp hn).1)
        rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
        simpa only [← sq, sq_abs] using hsq
      _ = _ := by
        rw [← _root_.RHTower.Sieve.sum_Icc_one_div_eq_harmonic, mul_sum]
        exact sum_congr rfl fun n _ => by ring
  have hH : (harmonic N : ℝ) / Real.log N ≤ 2 := by
    apply (div_le_iff₀ hL0).mpr
    linarith only [harmonic_le_one_add_log N, hL]
  calc
    _ ≤ (a ^ 2 * (harmonic N : ℝ)) / Real.log N := div_le_div_of_nonneg_right hsum hL0.le
    _ = a ^ 2 * ((harmonic N : ℝ) / Real.log N) := by ring
    _ ≤ a ^ 2 * 2 := mul_le_mul_of_nonneg_left hH (sq_nonneg _)
    _ = _ := by dsimp only [a]; ring

/-- Both reflected affine shells share one polynomial harmonic payment. -/
theorem exists_reciprocalUpward_shell_polynomial_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {m : ℕ} (hm : 0 < m) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → ∀ B : ℕ, ⌈c⌉₊ ≤ B →
      (∑ n ∈ Icc 1 N,
        ((reciprocalUpwardCoefficient φ c B N m n -
          ramanujanLagCoefficient m n * CompletedShell.shellCorrection φ c m) /
            Real.sqrt n) ^ 2) / Real.log N ≤ K * c ^ 6 / Real.sqrt (Real.log N) := by
  obtain ⟨K, hK, hbound⟩ :=
    exists_shiftedReciprocalUpwardRowError_polynomial_harmonic_bound hm hφ hsupp hM
  refine ⟨K, hK, ?_⟩
  filter_upwards [hbound] with N hN
  intro c hc1 B hB
  have hc : 0 < c := zero_lt_one.trans_le hc1
  have hid : shellCorrectionOfShift φ c m id = CompletedShell.shellCorrection φ c m := rfl
  have hrow (n : ℕ) (hn : 1 ≤ n) :
      (reciprocalUpwardCoefficient φ c B N m n -
        ramanujanLagCoefficient m n * CompletedShell.shellCorrection φ c m) / Real.sqrt n =
      (shiftedReciprocalUpwardRowError φ c id N m n +
        shiftedReciprocalUpwardRowError φ c (reflectedAffineShift m) N m n) / 2 := by
    rw [reciprocalUpwardCoefficient_eq_shifted_corrections hφ hsupp hc hB N m n hn]
    dsimp only [shiftedReciprocalUpwardRowError]
    rw [hid, shellCorrectionOfShift_reflected hm]
    ring
  have hsum : (∑ n ∈ Icc 1 N,
      ((reciprocalUpwardCoefficient φ c B N m n -
        ramanujanLagCoefficient m n * CompletedShell.shellCorrection φ c m) / Real.sqrt n) ^ 2) ≤
      ∑ n ∈ Icc 1 N, (shiftedReciprocalUpwardRowError φ c id N m n ^ 2 +
        shiftedReciprocalUpwardRowError φ c (reflectedAffineShift m) N m n ^ 2) / 2 := by
    apply sum_le_sum
    intro n hn
    rw [hrow n (mem_Icc.mp hn).1]
    nlinarith only [sq_nonneg (shiftedReciprocalUpwardRowError φ c id N m n -
      shiftedReciprocalUpwardRowError φ c (reflectedAffineShift m) N m n)]
  have hfinal := div_le_div_of_nonneg_right hsum (Real.log_natCast_nonneg N)
  rw [← sum_div, sum_add_distrib, div_right_comm, add_div] at hfinal
  have hp := hN c hc1 id
  have hn := hN c hc1 (reflectedAffineShift m)
  linarith only [hfinal, hp, hn]

/-- Linear prime geometry costs a sixth power of overlap, with a universal strip constant. -/
theorem linearPrimeStrip_sixth_le {c : ℝ} (hc : 1 ≤ c) :
    ((linearPrimeStrip c : ℝ) + 1) ^ 6 ≤ (Real.exp 1 + 2) ^ 6 * c ^ 6 := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hb : (linearPrimeStrip c : ℝ) < c * Real.exp 1 + 1 := by
    exact Nat.ceil_lt_add_one (by positivity)
  have hbase : (linearPrimeStrip c : ℝ) + 1 ≤ (Real.exp 1 + 2) * c := by
    nlinarith only [hb, hc]
  simpa only [mul_pow] using pow_le_pow_left₀ (by positivity) hbase 6

/-- The literal upward action keeps separate kernel and shell costs at growing overlap. -/
theorem exists_actualUpward_polynomial_payment {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {m : ℕ} (hm : 0 < m) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c / N ≤ 1 →
      linearPrimeStrip c ≤ N → 2 * ((Real.exp 1 + 3) * c) * linearPrimeStrip c ≤ (N : ℝ) →
      ‖normalizedUpwardPrimeResidual φ c N m‖ ^ 2 ≤
        C * (c ^ 10 * (Real.log (N : ℝ) / N) ^ 2 + c ^ 6 / Real.sqrt (Real.log N)) := by
  obtain ⟨A, hA, ha⟩ := exists_logarithmicUpward_error_sharp_horizon_bound hφ hsupp hM m
  obtain ⟨B, hB, hb⟩ :=
    exists_linearizedUpwardCoefficient_boundary_polynomial_harmonic_bound hφ hsupp hM hm
  obtain ⟨D, hD, hd⟩ := exists_reciprocalUpward_shell_polynomial_bound hφ hsupp hM hm
  let L := (Real.exp 1 + 2) ^ 6
  let C := 3 * (A * L + B * L + D)
  have hL : 0 < L := by dsimp only [L]; positivity
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hd, eventually_ge_atTop 1, hlog.eventually_ge_atTop 1] with N hdN hN hlogN
  intro c hc1 hw hBN hlarge
  have hc : 0 < c := zero_lt_one.trans_le hc1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hcN : c ≤ (N : ℝ) := by simpa only [one_mul] using (div_le_iff₀ hN0).mp hw
  let strip := linearPrimeStrip c
  have hstrip : ⌈c⌉₊ ≤ strip := by
    apply Nat.ceil_le.mpr
    have he : c ≤ c * Real.exp 1 := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (Real.one_le_exp_iff.mpr (by norm_num : (0 : ℝ) ≤ 1)) hc.le
    exact he.trans (Nat.le_ceil _)
  let a : ℕ → ℝ := fun n =>
    (logarithmicUpwardCoefficient φ c strip N m n -
      linearizedUpwardCoefficient φ c strip N m n) / Real.sqrt n
  let b : ℕ → ℝ := fun n =>
    (linearizedUpwardCoefficient φ c strip N m n -
      reciprocalUpwardCoefficient φ c strip N m n) / Real.sqrt n
  let d : ℕ → ℝ := fun n =>
    (reciprocalUpwardCoefficient φ c strip N m n -
      ramanujanLagCoefficient m n * CompletedShell.shellCorrection φ c m) / Real.sqrt n
  have hrow (n : ℕ) (hn : n ∈ Icc 1 N) : actualUpwardRowError φ c N m n = a n + b n + d n := by
    have hs : Real.sqrt n ≠ 0 := (Real.sqrt_pos.mpr
      (by exact_mod_cast (mem_Icc.mp hn).1 : (0 : ℝ) < n)).ne'
    have hu : upwardPrimeRow (atomDilate φ (c / N)) N
        (fun j => ramanujanLagCoefficient m j / Real.sqrt j) n /
          (∫ u, atomDilate φ (c / N) u ^ 2) =
        logarithmicUpwardCoefficient φ c strip N m n / Real.sqrt n := by
      apply (eq_div_iff hs).mpr
      simpa only [mul_comm] using
        sqrt_mul_upwardRamanujanRow_eq_logarithmicCoefficient_small_width hsupp hc hn hw m
    rw [actualUpwardRowError, hu]
    dsimp only [a, b, d]
    ring
  have hsum : (∑ n ∈ Icc 1 N, actualUpwardRowError φ c N m n ^ 2) ≤
      3 * ((∑ n ∈ Icc 1 N, a n ^ 2) + (∑ n ∈ Icc 1 N, b n ^ 2) +
        ∑ n ∈ Icc 1 N, d n ^ 2) := by
    rw [← sum_add_distrib, ← sum_add_distrib, mul_sum]
    apply sum_le_sum
    intro n hn
    rw [hrow n hn]
    nlinarith only [sq_nonneg (a n - b n), sq_nonneg (a n - d n), sq_nonneg (b n - d n)]
  have haN := ha N hN hlogN c hc1 hw strip hBN hlarge
  have hbN := hb N hN hlogN c hc hcN strip
  have hdN' := hdN c hc1 strip hstrip
  have hwidth := linearPrimeStrip_sixth_le hc1
  have ha' : (∑ n ∈ Icc 1 N, a n ^ 2) / Real.log N ≤
      (A * L) * (c ^ 10 * (Real.log (N : ℝ) / N) ^ 2) := by
    refine haN.trans ?_
    calc
      _ ≤ A * c ^ 4 * (L * c ^ 6) * (Real.log (N : ℝ) / N) ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hwidth (by positivity)) (sq_nonneg _)
      _ = _ := by ring
  have hb' : (∑ n ∈ Icc 1 N, b n ^ 2) / Real.log N ≤
      (B * L) * (c ^ 6 / Real.sqrt (Real.log N)) := by
    refine hbN.trans ?_
    calc
      _ ≤ B * (L * c ^ 6) / Real.sqrt (Real.log N) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hwidth hB.le) (Real.sqrt_nonneg _)
      _ = _ := by ring
  have hd' : (∑ n ∈ Icc 1 N, d n ^ 2) / Real.log N ≤
      D * (c ^ 6 / Real.sqrt (Real.log N)) := by simpa only [mul_div_assoc] using hdN'
  rw [normalizedUpwardPrimeResidual_norm_sq]
  have hfinal := div_le_div_of_nonneg_right hsum (Real.log_natCast_nonneg N)
  rw [mul_div_assoc, add_div, add_div] at hfinal
  have hcross₁ : 0 ≤ (A * L) * (c ^ 6 / Real.sqrt (Real.log N)) := by positivity
  have hcross₂ : 0 ≤ (B * L + D) * (c ^ 10 * (Real.log (N : ℝ) / N) ^ 2) := by positivity
  dsimp only [C]
  nlinarith only [hfinal, ha', hb', hd', hcross₁, hcross₂]

/-- The actual tilted-spline source satisfies the polynomial payment with no analytic premise. -/
theorem exists_tiltedWeil_upward_polynomial_payment {m : ℕ} (hm : 0 < m) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c / N ≤ 1 →
      linearPrimeStrip c ≤ N → 2 * ((Real.exp 1 + 3) * c) * linearPrimeStrip c ≤ (N : ℝ) →
      ‖normalizedUpwardPrimeResidual tiltedUnitSpline c N m‖ ^ 2 ≤
        C * (c ^ 10 * (Real.log (N : ℝ) / N) ^ 2 + c ^ 6 / Real.sqrt (Real.log N)) :=
  exists_actualUpward_polynomial_payment contDiff_tiltedUnitSpline
    tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos hm

#print axioms exists_logarithmicUpward_error_sharp_horizon_bound
#print axioms exists_reciprocalUpward_shell_polynomial_bound
#print axioms exists_actualUpward_polynomial_payment
#print axioms exists_tiltedWeil_upward_polynomial_payment

end GaloisForLFunctions.CompletedArithmeticForms
