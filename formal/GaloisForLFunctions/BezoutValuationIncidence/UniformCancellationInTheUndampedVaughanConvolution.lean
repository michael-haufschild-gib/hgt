import GaloisForLFunctions.BezoutValuationIncidence.UniformFloorMeansAndMovingVaughanGrams
import GaloisForLFunctions.RHTower.MoebiusFloorSummatory
import GaloisForLFunctions.RHTower.BaezDuarteMobiusPrefixApproximation
import GaloisForLFunctions.BezoutValuationIncidence.TheBalancedStatisticIsTheQuasiRiemannHypothesis
import GaloisForLFunctions.RHTower.Sieve.MoebiusHarmonicArbitraryLogRate

/-!
# Uniform cancellation in the undamped Vaughan convolution

The double truncated Möbius convolution has a common finite error bound at every
cutoff pair. Small cutoffs are controlled by floor rounding; a large cutoff is
controlled by the exact Vaughan identity and a common Mertens tail modulus.
Arbitrary logarithmic Mertens and harmonic bounds discharge that modulus.
-/
open Finset Filter ArithmeticFunction RHTower
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open scoped BigOperators Topology
noncomputable section
namespace GaloisForLFunctions.BezoutValuationIncidence
set_option autoImplicit false

/-- The summatory undamped small-small convolution. -/
def pmUndampedVaughanConvolutionPrefix (U V n : ℕ) : ℝ :=
  ∑ d ∈ Icc 1 n, pmPronicVaughanSmallSmallCoeff U V d

/-- The undamped both-large convolution, before taking its summatory function. -/
def pmUndampedVaughanLargeCoeff (U V : ℕ) : ArithmeticFunction ℝ :=
  ((moebius : ArithmeticFunction ℝ) - Sieve.truncatedMoebius U) *
    ((zeta : ArithmeticFunction ℝ) * ((moebius : ArithmeticFunction ℝ) - Sieve.truncatedMoebius V))

private theorem truncated_mu_sum_mul (U n : ℕ) (w : ℕ → ℝ) :
    (∑ d ∈ Icc 1 n, Sieve.truncatedMoebius U d * w d) =
      ∑ d ∈ Icc 1 (min U n), moebiusReal d * w d := by
  calc
    _ = ∑ d ∈ Icc 1 (min U n), Sieve.truncatedMoebius U d * w d := by
      symm
      apply sum_subset (Icc_subset_Icc_right (min_le_right U n))
      intro d hd hnot
      have hdU : ¬ d ≤ U := by
        intro h
        exact hnot (mem_Icc.mpr ⟨(mem_Icc.mp hd).1, le_min h (mem_Icc.mp hd).2⟩)
      simp [hdU]
    _ = _ := by
      apply sum_congr rfl
      intro d hd
      simp [moebiusReal, (mem_Icc.mp hd).2.trans (min_le_left U n)]

private theorem mu_tail_apply (U d : ℕ) :
    ((moebius : ArithmeticFunction ℝ) - Sieve.truncatedMoebius U) d =
      if d ≤ U then 0 else moebiusReal d := by
  change ((moebius d : ℤ) : ℝ) -
    (if d ≤ U then ((moebius d : ℤ) : ℝ) else 0) = _
  split_ifs <;> simp only [sub_self, sub_zero, moebiusReal]

private theorem mu_tail_sum_mul (U n : ℕ) (w : ℕ → ℝ) :
    (∑ d ∈ Icc 1 n, ((moebius : ArithmeticFunction ℝ) - Sieve.truncatedMoebius U) d * w d) =
      ∑ d ∈ Ioc U n, moebiusReal d * w d := by
  symm
  calc
    _ = ∑ d ∈ Ioc U n,
        ((moebius : ArithmeticFunction ℝ) - Sieve.truncatedMoebius U) d * w d := by
      apply sum_congr rfl
      intro d hd
      rw [mu_tail_apply, if_neg (by have := (mem_Ioc.mp hd).1; omega)]
    _ = _ := by
      apply sum_subset
      · intro d hd
        exact mem_Icc.mpr ⟨by have := (mem_Ioc.mp hd).1; omega, (mem_Ioc.mp hd).2⟩
      · intro d hd hnot
        have hdU : d ≤ U := by
          have := (mem_Icc.mp hd).2
          simp only [mem_Ioc] at hnot
          omega
        rw [mu_tail_apply, if_pos hdU, zero_mul]

/-- The harmonic Möbius sums are bounded by one, including the empty cutoff. -/
theorem abs_deningerHarmonicPartial_le_one (U : ℕ) : |deningerHarmonicPartial U| ≤ 1 := by
  rw [deningerHarmonicPartial_eq_sum_Icc]
  rcases Nat.eq_zero_or_pos U with rfl | hU
  · simp
  · exact abs_sum_moebius_div_le_one U hU

/-- Swapping the two finite cutoffs leaves the convolution prefix unchanged. -/
theorem pmUndampedVaughanConvolutionPrefix_comm (U V n : ℕ) :
    pmUndampedVaughanConvolutionPrefix U V n = pmUndampedVaughanConvolutionPrefix V U n := by
  unfold pmUndampedVaughanConvolutionPrefix pmPronicVaughanSmallSmallCoeff
  rw [mul_left_comm (Sieve.truncatedMoebius U) (Sieve.truncatedMoebius V)]

/-- The exact Möbius identity has a both-large remainder in the arithmetic-function ring. -/
theorem moebius_eq_truncations_sub_smallSmall_add_large (U V : ℕ) :
    (moebius : ArithmeticFunction ℝ) = Sieve.truncatedMoebius U + Sieve.truncatedMoebius V -
      Sieve.truncatedMoebius U * (Sieve.truncatedMoebius V * (zeta : ArithmeticFunction ℝ)) +
        pmUndampedVaughanLargeCoeff U V := by
  have hkey : (moebius : ArithmeticFunction ℝ) * (zeta : ArithmeticFunction ℝ) = 1 :=
    coe_moebius_mul_coe_zeta
  unfold pmUndampedVaughanLargeCoeff
  linear_combination -((moebius : ArithmeticFunction ℝ) -
    Sieve.truncatedMoebius U - Sieve.truncatedMoebius V) * hkey

/-- The convolution prefix is a combination of three actual Mertens sums and one remainder. -/
theorem pmUndampedVaughanConvolutionPrefix_eq_mertens (U V n : ℕ) :
    pmUndampedVaughanConvolutionPrefix U V n =
      (∑ d ∈ Icc 1 (min U n), moebiusReal d) +
        (∑ d ∈ Icc 1 (min V n), moebiusReal d) -
          (∑ d ∈ Icc 1 n, moebiusReal d) +
            ∑ d ∈ Icc 1 n, pmUndampedVaughanLargeCoeff U V d := by
  have h := congrArg (fun f : ArithmeticFunction ℝ => ∑ d ∈ Icc 1 n, f d)
    (moebius_eq_truncations_sub_smallSmall_add_large U V)
  change (∑ d ∈ Icc 1 n, moebiusReal d) =
    ∑ d ∈ Icc 1 n, (Sieve.truncatedMoebius U d + Sieve.truncatedMoebius V d -
      pmPronicVaughanSmallSmallCoeff U V d + pmUndampedVaughanLargeCoeff U V d) at h
  simp only [sum_add_distrib, sum_sub_distrib] at h
  have hU : (∑ d ∈ Icc 1 n, Sieve.truncatedMoebius U d) =
      ∑ d ∈ Icc 1 (min U n), moebiusReal d := by
    simpa only [mul_one] using truncated_mu_sum_mul U n (fun _ => 1)
  have hV : (∑ d ∈ Icc 1 n, Sieve.truncatedMoebius V d) =
      ∑ d ∈ Icc 1 (min V n), moebiusReal d := by
    simpa only [mul_one] using truncated_mu_sum_mul V n (fun _ => 1)
  rw [hU, hV] at h
  change (∑ d ∈ Icc 1 n, pmPronicVaughanSmallSmallCoeff U V d) = _
  linarith only [h]

/-- Hyperbola summation exposes actual Möbius tail blocks in the both-large remainder. -/
theorem sum_pmUndampedVaughanLargeCoeff_eq_blocks (U V n : ℕ) :
    (∑ d ∈ Icc 1 n, pmUndampedVaughanLargeCoeff U V d) =
      ∑ a ∈ Ioc U n, moebiusReal a *
        ∑ k ∈ Icc 1 (n / a), ∑ b ∈ Ioc V ((n / a) / k), moebiusReal b := by
  rw [pmUndampedVaughanLargeCoeff, sum_Icc_mul_apply, mu_tail_sum_mul]
  apply sum_congr rfl
  intro a _
  congr 1
  rw [sum_Icc_mul_apply]
  apply sum_congr rfl
  intro k hk
  rw [Sieve.zeta_real_apply_of_ne_zero (by have := (mem_Icc.mp hk).1; omega), one_mul]
  simpa only [mul_one] using mu_tail_sum_mul V ((n / a) / k) (fun _ => 1)

private theorem abs_mu_block_le_linear {D V q : ℕ} {L : ℝ}
    (hL : 0 ≤ L) (hDV : D ≤ V)
    (hM : ∀ x : ℕ, D ≤ x → |∑ d ∈ Icc 1 x, moebiusReal d| ≤ L * x) :
    |∑ b ∈ Ioc V q, moebiusReal b| ≤ 2 * L * q := by
  by_cases hVq : V ≤ q
  · have hIcc (x : ℕ) : Icc 1 x = Ioc 0 x := by
      ext d
      simp only [mem_Icc, mem_Ioc]
      omega
    have hsum : (∑ b ∈ Ioc V q, moebiusReal b) =
        (∑ b ∈ Icc 1 q, moebiusReal b) - ∑ b ∈ Icc 1 V, moebiusReal b := by
      rw [hIcc q, hIcc V]
      have h := sum_Ioc_consecutive moebiusReal (Nat.zero_le V) hVq
      linarith only [h]
    have hq := hM q (hDV.trans hVq)
    have hV := hM V hDV
    have hLV : L * (V : ℝ) ≤ L * q := mul_le_mul_of_nonneg_left (by exact_mod_cast hVq) hL
    rw [hsum]
    exact (abs_sub _ _).trans (by linarith only [hq, hV, hLV])
  · rw [Ioc_eq_empty (by omega), sum_empty, abs_zero]
    positivity

/-- One long cutoff controls the full remainder at the cost of two harmonic sums. -/
theorem abs_sum_pmUndampedVaughanLargeCoeff_le {D V : ℕ} {L : ℝ}
    (hL : 0 ≤ L) (hDV : D ≤ V)
    (hM : ∀ x : ℕ, D ≤ x → |∑ d ∈ Icc 1 x, moebiusReal d| ≤ L * x)
    (U n : ℕ) :
    |∑ d ∈ Icc 1 n, pmUndampedVaughanLargeCoeff U V d| ≤
      2 * L * n * (∑ k ∈ Icc 1 n, 1 / (k : ℝ)) ^ 2 := by
  let H : ℝ := ∑ k ∈ Icc 1 n, 1 / (k : ℝ)
  have hH : 0 ≤ H := sum_nonneg fun k _ => by positivity
  have hinner (a : ℕ) (ha : a ∈ Ioc U n) :
      |∑ k ∈ Icc 1 (n / a), ∑ b ∈ Ioc V ((n / a) / k), moebiusReal b| ≤
        (2 * L * n / a) * H := by
    have ha0 : (0 : ℝ) < a := by exact_mod_cast (by have := (mem_Ioc.mp ha).1; omega : 0 < a)
    calc
      _ ≤ ∑ k ∈ Icc 1 (n / a), (2 * L * n / a) * (1 / (k : ℝ)) := by
        apply (abs_sum_le_sum_abs _ _).trans
        apply sum_le_sum
        intro k hk
        have hk0 : (0 : ℝ) < k := by exact_mod_cast (mem_Icc.mp hk).1
        have hdiv : (((n / a) / k : ℕ) : ℝ) ≤ (n : ℝ) / a / k :=
          (Nat.cast_div_le).trans (div_le_div_of_nonneg_right Nat.cast_div_le hk0.le)
        exact (abs_mu_block_le_linear hL hDV hM).trans
          ((mul_le_mul_of_nonneg_left hdiv (by positivity : 0 ≤ 2 * L)).trans_eq (by ring))
      _ ≤ ∑ k ∈ Icc 1 n, (2 * L * n / a) * (1 / (k : ℝ)) :=
        sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right (Nat.div_le_self n a))
          (fun k _ _ => by positivity)
      _ = _ := by rw [← mul_sum]
  rw [sum_pmUndampedVaughanLargeCoeff_eq_blocks]
  calc
    _ ≤ ∑ a ∈ Ioc U n, (2 * L * n / a) * H := by
      apply (abs_sum_le_sum_abs _ _).trans
      apply sum_le_sum
      intro a ha
      rw [abs_mul]
      have hnonneg : 0 ≤ (2 * L * n / a) * H := by positivity
      exact (mul_le_mul (abs_moebiusReal_le_one' a) (hinner a ha) (abs_nonneg _) zero_le_one).trans_eq
        (one_mul _)
    _ ≤ ∑ a ∈ Icc 1 n, (2 * L * n / a) * H := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro a ha
        exact mem_Icc.mpr ⟨by have := (mem_Ioc.mp ha).1; omega, (mem_Ioc.mp ha).2⟩
      · intro a _ _
        positivity
    _ = 2 * L * n * H ^ 2 := by
      simp only [div_eq_mul_inv, ← sum_mul, ← mul_sum]
      dsimp only [H]
      simp only [one_div]
      rw [pow_two]
      ring

private theorem sum_three_convolution_rectangle (f g : ArithmeticFunction ℝ) (n : ℕ) :
    (∑ d ∈ Icc 1 n, (f * (g * (zeta : ArithmeticFunction ℝ))) d) =
      ∑ a ∈ Icc 1 n, f a * ∑ b ∈ Icc 1 n, g b * ((n / (a * b) : ℕ) : ℝ) := by
  have hZ (q : ℕ) : (∑ k ∈ Icc 1 q, (zeta : ArithmeticFunction ℝ) k) = q := by
    calc
      _ = ∑ _k ∈ Icc 1 q, (1 : ℝ) := sum_congr rfl fun k hk =>
        Sieve.zeta_real_apply_of_ne_zero (by have := (mem_Icc.mp hk).1; omega)
      _ = _ := by simp
  rw [sum_Icc_mul_apply]
  apply sum_congr rfl
  intro a ha
  congr 1
  rw [sum_Icc_mul_apply]
  simp only [hZ, Nat.div_div_eq_div_mul]
  apply sum_subset (Icc_subset_Icc_right (Nat.div_le_self n a))
  intro b hb hnot
  have ha0 : 0 < a := (mem_Icc.mp ha).1
  have hbn : n / a < b := by
    have := (mem_Icc.mp hb).1
    simp only [mem_Icc] at hnot
    omega
  have hprod : n < a * b := by
    by_contra h
    have hle := (Nat.le_div_iff_mul_le ha0).mpr
      (by simpa only [Nat.mul_comm] using le_of_not_gt h)
    omega
  rw [Nat.div_eq_of_lt hprod, Nat.cast_zero, mul_zero]

private theorem sum_Icc_min_eq_of_zero_above (f : ℕ → ℝ) (U n : ℕ)
    (hf : ∀ d : ℕ, n < d → f d = 0) :
    (∑ d ∈ Icc 1 (min U n), f d) = ∑ d ∈ Icc 1 U, f d := by
  apply sum_subset (Icc_subset_Icc_right (min_le_left U n))
  intro d hd hnot
  apply hf
  have hdU := (mem_Icc.mp hd).2
  have hd1 := (mem_Icc.mp hd).1
  simp only [mem_Icc] at hnot
  omega

/-- The undamped convolution prefix is the double Möbius floor sum at every cutoff. -/
theorem pmUndampedVaughanConvolutionPrefix_eq_rectangle (U V n : ℕ) :
    pmUndampedVaughanConvolutionPrefix U V n =
      ∑ a ∈ Icc 1 U, moebiusReal a *
        ∑ b ∈ Icc 1 V, moebiusReal b * ((n / (a * b) : ℕ) : ℝ) := by
  unfold pmUndampedVaughanConvolutionPrefix pmPronicVaughanSmallSmallCoeff
  rw [sum_three_convolution_rectangle, truncated_mu_sum_mul]
  simp_rw [truncated_mu_sum_mul]
  calc
    _ = ∑ a ∈ Icc 1 (min U n), moebiusReal a *
        ∑ b ∈ Icc 1 V, moebiusReal b * ((n / (a * b) : ℕ) : ℝ) := by
      apply sum_congr rfl
      intro a ha
      congr 1
      apply sum_Icc_min_eq_of_zero_above
      intro b hbn
      have hprod : n < a * b := hbn.trans_le
        (Nat.le_mul_of_pos_left b (mem_Icc.mp ha).1)
      rw [Nat.div_eq_of_lt hprod, Nat.cast_zero, mul_zero]
    _ = _ := by
      apply sum_Icc_min_eq_of_zero_above
      intro a han
      have hz : (∑ b ∈ Icc 1 V, moebiusReal b * ((n / (a * b) : ℕ) : ℝ)) = 0 := by
        apply sum_eq_zero
        intro b hb
        have hprod : n < a * b := han.trans_le
          (Nat.le_mul_of_pos_right a (mem_Icc.mp hb).1)
        rw [Nat.div_eq_of_lt hprod, Nat.cast_zero, mul_zero]
      rw [hz, mul_zero]

/-- Direct floor rounding costs only the product of the two finite cutoffs. -/
theorem abs_pmUndampedVaughanConvolutionPrefix_sub_mean_le (U V n : ℕ) :
    |pmUndampedVaughanConvolutionPrefix U V n -
      (n : ℝ) * deningerHarmonicPartial U * deningerHarmonicPartial V| ≤ (U : ℝ) * V := by
  have hmean : (n : ℝ) * deningerHarmonicPartial U * deningerHarmonicPartial V =
      ∑ a ∈ Icc 1 U, ∑ b ∈ Icc 1 V,
        moebiusReal a * moebiusReal b * ((n : ℝ) / (a * b : ℕ)) := by
    simp only [deningerHarmonicPartial_eq_sum_Icc, mul_sum, sum_mul]
    rw [sum_comm]
    apply sum_congr rfl
    intro a _
    apply sum_congr rfl
    intro b _
    simp only [moebiusReal, Nat.cast_mul, div_mul_eq_div_div]
    ring
  have herror : pmUndampedVaughanConvolutionPrefix U V n -
      (n : ℝ) * deningerHarmonicPartial U * deningerHarmonicPartial V =
      ∑ a ∈ Icc 1 U, ∑ b ∈ Icc 1 V,
        (moebiusReal a * moebiusReal b) *
          (((n / (a * b) : ℕ) : ℝ) - (n : ℝ) / (a * b : ℕ)) := by
    rw [pmUndampedVaughanConvolutionPrefix_eq_rectangle, hmean]
    simp only [mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro a _
    apply sum_congr rfl
    intro b _
    ring
  rw [herror]
  calc
    _ ≤ ∑ a ∈ Icc 1 U, ∑ b ∈ Icc 1 V, (1 : ℝ) := by
      apply (abs_sum_le_sum_abs _ _).trans
      apply sum_le_sum
      intro a ha
      apply (abs_sum_le_sum_abs _ _).trans
      apply sum_le_sum
      intro b hb
      have hab : 1 ≤ a * b := Nat.mul_pos (mem_Icc.mp ha).1 (mem_Icc.mp hb).1
      rw [abs_mul, abs_mul]
      have hμ : |moebiusReal a| * |moebiusReal b| ≤ 1 := by
        simpa only [one_mul] using mul_le_mul (abs_moebiusReal_le_one' a)
          (abs_moebiusReal_le_one' b) (abs_nonneg _) zero_le_one
      exact (mul_le_mul hμ (abs_natDiv_sub_div_le n (a * b) hab) (abs_nonneg _) zero_le_one).trans_eq
        (one_mul _)
    _ = _ := by simp

private theorem abs_moebius_partial_sum_le_self (x : ℕ) :
    |∑ d ∈ Icc 1 x, moebiusReal d| ≤ x := by
  calc
    _ ≤ ∑ _d ∈ Icc 1 x, (1 : ℝ) := (abs_sum_le_sum_abs _ _).trans
      (sum_le_sum fun d _ => abs_moebiusReal_le_one' d)
    _ = _ := by simp

private theorem abs_double_convolution_error_of_large_right {D V n : ℕ} {L K : ℝ}
    (hL : 0 ≤ L) (_hK : 0 ≤ K) (hDn : D ≤ n) (hDV : D ≤ V)
    (hM : ∀ x : ℕ, D ≤ x → |∑ d ∈ Icc 1 x, moebiusReal d| ≤ L * x)
    (hH : ∀ x : ℕ, D ≤ x → |deningerHarmonicPartial x| ≤ K) (U : ℕ) :
    |pmUndampedVaughanConvolutionPrefix U V n -
      (n : ℝ) * deningerHarmonicPartial U * deningerHarmonicPartial V| ≤
        D + 3 * L * n + 2 * L * n * (∑ k ∈ Icc 1 n, 1 / (k : ℝ)) ^ 2 + K * n := by
  have hMU : |∑ d ∈ Icc 1 (min U n), moebiusReal d| ≤ D + L * n := by
    by_cases hDmin : D ≤ min U n
    · have hle : L * (min U n : ℕ) ≤ L * n :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast min_le_right U n) hL
      exact (hM _ hDmin).trans (by linarith only [hle, (Nat.cast_nonneg D : (0 : ℝ) ≤ D)])
    · have hmin : ((min U n : ℕ) : ℝ) ≤ D := by exact_mod_cast (lt_of_not_ge hDmin).le
      have hLn : 0 ≤ L * n := mul_nonneg hL (Nat.cast_nonneg n)
      exact (abs_moebius_partial_sum_le_self _).trans (by linarith only [hmin, hLn])
  have hMV : |∑ d ∈ Icc 1 (min V n), moebiusReal d| ≤ L * n :=
    (hM _ (le_min hDV hDn)).trans
      (mul_le_mul_of_nonneg_left (by exact_mod_cast min_le_right V n) hL)
  have hMn := hM n hDn
  have hR := abs_sum_pmUndampedVaughanLargeCoeff_le hL hDV hM U n
  have hmean : |(n : ℝ) * deningerHarmonicPartial U * deningerHarmonicPartial V| ≤ K * n := by
    have hh := mul_le_mul (abs_deningerHarmonicPartial_le_one U) (hH V hDV) (abs_nonneg _) zero_le_one
    have h := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg n)
    simpa only [abs_mul, Nat.abs_cast, one_mul, mul_one, mul_assoc, mul_comm, mul_left_comm] using h
  rw [pmUndampedVaughanConvolutionPrefix_eq_mertens]
  calc
    _ ≤ |∑ d ∈ Icc 1 (min U n), moebiusReal d| +
        |∑ d ∈ Icc 1 (min V n), moebiusReal d| +
          |∑ d ∈ Icc 1 n, moebiusReal d| +
            |∑ d ∈ Icc 1 n, pmUndampedVaughanLargeCoeff U V d| +
              |(n : ℝ) * deningerHarmonicPartial U * deningerHarmonicPartial V| := by
      apply (abs_sub _ _).trans
      apply add_le_add _ le_rfl
      apply (abs_add_le _ _).trans
      apply add_le_add _ le_rfl
      exact (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ _ := by linarith only [hMU, hMV, hMn, hR, hmean]

/-- A common Mertens and harmonic tail modulus controls the convolution at every cutoff pair. -/
theorem abs_pmUndampedVaughanConvolutionPrefix_sub_mean_le_uniform {D n : ℕ} {L K : ℝ}
    (hL : 0 ≤ L) (hK : 0 ≤ K) (hDn : D ≤ n)
    (hM : ∀ x : ℕ, D ≤ x → |∑ d ∈ Icc 1 x, moebiusReal d| ≤ L * x)
    (hH : ∀ x : ℕ, D ≤ x → |deningerHarmonicPartial x| ≤ K) (U V : ℕ) :
    |pmUndampedVaughanConvolutionPrefix U V n -
      (n : ℝ) * deningerHarmonicPartial U * deningerHarmonicPartial V| ≤
        (D : ℝ) ^ 2 + D + 3 * L * n +
          2 * L * n * (∑ k ∈ Icc 1 n, 1 / (k : ℝ)) ^ 2 + K * n := by
  by_cases hDV : D ≤ V
  · have h := abs_double_convolution_error_of_large_right hL hK hDn hDV hM hH U
    linarith only [h, sq_nonneg (D : ℝ)]
  · by_cases hDU : D ≤ U
    · have h := abs_double_convolution_error_of_large_right hL hK hDn hDU hM hH V
      rw [pmUndampedVaughanConvolutionPrefix_comm V U] at h
      have hmean : (n : ℝ) * deningerHarmonicPartial V * deningerHarmonicPartial U =
          (n : ℝ) * deningerHarmonicPartial U * deningerHarmonicPartial V := by ring
      rw [hmean] at h
      linarith only [h, sq_nonneg (D : ℝ)]
    · have hUD : (U : ℝ) ≤ D := by exact_mod_cast (lt_of_not_ge hDU).le
      have hVD : (V : ℝ) ≤ D := by exact_mod_cast (lt_of_not_ge hDV).le
      have hprod : (U : ℝ) * V ≤ (D : ℝ) ^ 2 := by
        simpa only [pow_two] using mul_le_mul hUD hVD (Nat.cast_nonneg V) (Nat.cast_nonneg D)
      have hrest : 0 ≤ (D : ℝ) + 3 * L * n +
          2 * L * n * (∑ k ∈ Icc 1 n, 1 / (k : ℝ)) ^ 2 + K * n := by positivity
      exact (abs_pmUndampedVaughanConvolutionPrefix_sub_mean_le U V n).trans
        (by linarith only [hprod, hrest])

/-- Arbitrary logarithmic source bounds give one finite estimate for every cutoff pair. -/
theorem exists_uniform_pmUndampedVaughanConvolutionPrefix_log_bound (p : ℕ) (hp : 0 < p) :
    ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧ ∃ D₀ : ℕ, 2 ≤ D₀ ∧
      ∀ D n : ℕ, D₀ ≤ D → D ≤ n → ∀ U V : ℕ,
        |pmUndampedVaughanConvolutionPrefix U V n -
          (n : ℝ) * deningerHarmonicPartial U * deningerHarmonicPartial V| ≤
            (D : ℝ) ^ 2 + D +
              (3 * B * n + 2 * B * n * (∑ k ∈ Icc 1 n, 1 / (k : ℝ)) ^ 2 + C * n) /
                Real.log (D : ℝ) ^ p := by
  obtain ⟨B, hB, hM⟩ := Sieve.deningerMertensM_log_pow_rate p
  obtain ⟨C, hC, hH⟩ := Sieve.exists_abs_deningerHarmonicPartial_le_const_div_log_pow p hp
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp hM
  obtain ⟨H₀, hH₀⟩ := eventually_atTop.mp hH
  refine ⟨B, C, hB, hC, max M₀ (max H₀ 2), (le_max_right H₀ 2).trans (le_max_right _ _),
    fun D n hD hDn U V => ?_⟩
  have hD2 : 2 ≤ D := ((le_max_right H₀ 2).trans (le_max_right M₀ _)).trans hD
  have hD0 : (0 : ℝ) < D := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hD2)
  have hlogD : 0 < Real.log (D : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < D))
  have hM' (x : ℕ) (hx : D ≤ x) :
      |∑ d ∈ Icc 1 x, moebiusReal d| ≤ (B / Real.log (D : ℝ) ^ p) * x := by
    have hlog : Real.log (D : ℝ) ^ p ≤ Real.log (x : ℝ) ^ p :=
      pow_le_pow_left₀ hlogD.le (Real.log_le_log hD0 (by exact_mod_cast hx)) p
    rw [sum_Icc_moebiusReal_eq_mertensM]
    calc
      _ ≤ B * x / Real.log (x : ℝ) ^ p := hM₀ x (((le_max_left _ _).trans hD).trans hx)
      _ ≤ B * x / Real.log (D : ℝ) ^ p :=
        div_le_div_of_nonneg_left (mul_nonneg hB (Nat.cast_nonneg x)) (pow_pos hlogD p) hlog
      _ = _ := by ring
  have hH' (x : ℕ) (hx : D ≤ x) :
      |deningerHarmonicPartial x| ≤ C / Real.log (D : ℝ) ^ p := by
    have hlog : Real.log (D : ℝ) ^ p ≤ Real.log (x : ℝ) ^ p :=
      pow_le_pow_left₀ hlogD.le (Real.log_le_log hD0 (by exact_mod_cast hx)) p
    exact (hH₀ x ((((le_max_left H₀ 2).trans (le_max_right M₀ _)).trans hD).trans hx)).trans
      (div_le_div_of_nonneg_left hC (pow_pos hlogD p) hlog)
  have h := abs_pmUndampedVaughanConvolutionPrefix_sub_mean_le_uniform
    (div_nonneg hB (pow_nonneg hlogD.le _)) (div_nonneg hC (pow_nonneg hlogD.le _)) hDn hM' hH' U V
  refine h.trans_eq ?_
  ring

end GaloisForLFunctions.BezoutValuationIncidence
