import GaloisForLFunctions.RHTower.Sieve.GeneralAffineMeanSquareInfinite
import GaloisForLFunctions.RHTower.Sieve.InghamPoleRegularizedDetector
import GaloisForLFunctions.RHTower.Sieve.HeathBrownDyadicCoefficientBound
import GaloisForLFunctions.RHTower.FourthMomentDiagonal

open Complex MeasureTheory Set Finset ArithmeticFunction

namespace RHTower.Sieve

noncomputable section

/-!
# Uniform right-edge mean square for Ingham's sharp Möbius detector

For every fixed `beta > 1`, Möbius cancellation makes `1 - M_X(s) * zeta(s)` an exact
infinite Dirichlet series supported above `X`. Its coefficients are uniformly bounded by the
divisor function. Absolute convergence, the plain square mass, and the `n`-weighted square mass
then feed the infinite affine Montgomery--Vaughan theorem. The result is a literal cutoff-uniform
`O(T)` second moment for `zeta(beta+it) * M_X(beta+it) - 1`.

The threshold `beta > 1` is structural: the weighted mass becomes
`sum d(n)^2 n^(-2(beta-1/2))`, convergent exactly in this divisor-bound argument when
`beta - 1/2 > 1/2`.
-/

/-- The sharp Möbius convolution defect has divisor-size coefficients, uniformly in the cutoff. -/
theorem norm_moebiusZetaDefect_le_card_divisors
    {X : ℕ} (hX : 1 ≤ X) (n : ℕ) :
    ‖moebiusZetaDefect X n‖ ≤ (n.divisors.card : ℝ) := by
  by_cases hnX : n ≤ X
  · have hz : moebiusZetaDefect X n = 0 :=
      (moebiusZetaDefect_vanishesBelow X) n (by omega)
    rw [hz, norm_zero]
    positivity
  · have hn1 : n ≠ 1 := by omega
    have hconv := norm_mul_apply_le_divisors_pow_add_succ
      (r := 0) (s := 0) (F := truncatedMoebius X)
      (G := (ArithmeticFunction.zeta : ArithmeticFunction ℝ))
      (norm_truncatedMoebius_le_one X)
      (fun m => by
        by_cases hm : m = 0
        · subst m; simp
        · simp [ArithmeticFunction.zeta_apply, hm]) n
    rw [moebiusZetaDefect]
    change ‖(1 : ArithmeticFunction ℝ) n -
      (truncatedMoebius X * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) n‖ ≤ _
    rw [ArithmeticFunction.one_apply_ne hn1, zero_sub, norm_neg]
    simpa using hconv

theorem norm_complexCoeff_moebiusZetaDefect_le_card_divisors
    {X : ℕ} (hX : 1 ≤ X) (n : ℕ) :
    ‖complexCoeff (moebiusZetaDefect X) n‖ ≤ (n.divisors.card : ℝ) := by
  rw [complexCoeff_apply, Complex.norm_real]
  exact norm_moebiusZetaDefect_le_card_divisors hX n

@[simp] theorem complexCoeff_moebiusZetaDefect_zero (X : ℕ) :
    complexCoeff (moebiusZetaDefect X) 0 = 0 := by
  simp [complexCoeff, moebiusZetaDefect]

/-- Divisor coefficients remain absolutely summable after every damping exponent above one. -/
theorem summable_card_divisors_mul_rpow {beta : ℝ} (hbeta : 1 < beta) :
    Summable (fun n : ℕ => (n.divisors.card : ℝ) * (n : ℝ) ^ (-beta)) := by
  set eps : ℝ := (beta - 1) / 2 with heps_def
  have heps : 0 < eps := by rw [heps_def]; linarith
  obtain ⟨C, hCpos, hC⟩ := card_divisors_le_const_mul_rpow heps
  set p : ℝ := (beta + 1) / 2 with hp_def
  have hp : 1 < p := by rw [hp_def]; linarith
  have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (-p)) := by
    refine ((Real.summable_one_div_nat_rpow (p := p)).mpr hp).congr (fun n => ?_)
    rw [one_div, ← Real.rpow_neg (Nat.cast_nonneg n)]
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (hbase.mul_left C)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hp0 : p ≠ 0 := by linarith
    simp [Real.zero_rpow, hp0]
  · have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hd := hC n hn
    calc
      (n.divisors.card : ℝ) * (n : ℝ) ^ (-beta)
          ≤ (C * (n : ℝ) ^ eps) * (n : ℝ) ^ (-beta) :=
        mul_le_mul_of_nonneg_right hd (Real.rpow_nonneg hnR.le _)
      _ = C * (n : ℝ) ^ (-p) := by
        rw [mul_assoc, ← Real.rpow_add hnR]
        congr 2
        rw [heps_def, hp_def]
        ring

private theorem norm_defect_damped_le
    {X : ℕ} (hX : 1 ≤ X) (beta : ℝ) (n : ℕ) :
    ‖complexCoeff (moebiusZetaDefect X) n *
        (((n : ℝ) ^ (-beta) : ℝ) : ℂ)‖
      ≤ (n.divisors.card : ℝ) * (n : ℝ) ^ (-beta) := by
  rw [norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
  exact mul_le_mul_of_nonneg_right
    (norm_complexCoeff_moebiusZetaDefect_le_card_divisors hX n)
    (Real.rpow_nonneg (Nat.cast_nonneg n) _)

theorem summable_norm_complexCoeff_moebiusZetaDefect_damped
    {X : ℕ} (hX : 1 ≤ X) {beta : ℝ} (hbeta : 1 < beta) :
    Summable (fun n : ℕ =>
      ‖complexCoeff (moebiusZetaDefect X) n *
        (((n : ℝ) ^ (-beta) : ℝ) : ℂ)‖) := by
  exact Summable.of_nonneg_of_le (fun n => norm_nonneg _)
    (fun n => norm_defect_damped_le hX beta n)
    (summable_card_divisors_mul_rpow hbeta)

theorem summable_normSq_complexCoeff_moebiusZetaDefect_damped
    {X : ℕ} (hX : 1 ≤ X) {beta : ℝ} (hbeta : 1 < beta) :
    Summable (fun n : ℕ =>
      ‖complexCoeff (moebiusZetaDefect X) n *
        (((n : ℝ) ^ (-beta) : ℝ) : ℂ)‖ ^ 2) := by
  have hbase := summable_divisor_sq_rpow (show 1 / 2 < beta by linarith)
  refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_) hbase
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hamp := norm_defect_damped_le hX beta n
    calc
      ‖complexCoeff (moebiusZetaDefect X) n *
          (((n : ℝ) ^ (-beta) : ℝ) : ℂ)‖ ^ 2
          ≤ ((n.divisors.card : ℝ) * (n : ℝ) ^ (-beta)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hamp 2
      _ = (n.divisors.card : ℝ) ^ 2 * (n : ℝ) ^ (-2 * beta) := by
        rw [mul_pow, ← Real.rpow_natCast ((n : ℝ) ^ (-beta)) 2,
          ← Real.rpow_mul hnR.le]
        congr 2
        push_cast
        ring

theorem summable_weighted_normSq_complexCoeff_moebiusZetaDefect_damped
    {X : ℕ} (hX : 1 ≤ X) {beta : ℝ} (hbeta : 1 < beta) :
    Summable (fun n : ℕ => (n : ℝ) *
      ‖complexCoeff (moebiusZetaDefect X) n *
        (((n : ℝ) ^ (-beta) : ℝ) : ℂ)‖ ^ 2) := by
  have hshift : 1 / 2 < beta - 1 / 2 := by linarith
  have hbase := summable_divisor_sq_rpow hshift
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hbase
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hamp := norm_defect_damped_le hX beta n
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hamp 2
    calc
      (n : ℝ) * ‖complexCoeff (moebiusZetaDefect X) n *
          (((n : ℝ) ^ (-beta) : ℝ) : ℂ)‖ ^ 2
          ≤ (n : ℝ) * ((n.divisors.card : ℝ) * (n : ℝ) ^ (-beta)) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq hnR.le
      _ = (n.divisors.card : ℝ) ^ 2 *
          (n : ℝ) ^ (-2 * (beta - 1 / 2)) := by
        rw [mul_pow, ← Real.rpow_natCast ((n : ℝ) ^ (-beta)) 2,
          ← Real.rpow_mul hnR.le]
        nth_rewrite 1 [← Real.rpow_one (n : ℝ)]
        calc
          (n : ℝ) ^ (1 : ℝ) *
              ((n.divisors.card : ℝ) ^ 2 * (n : ℝ) ^ (-beta * (2 : ℝ))) =
              (n.divisors.card : ℝ) ^ 2 *
                ((n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-beta * (2 : ℝ))) := by ring
          _ = (n.divisors.card : ℝ) ^ 2 *
              (n : ℝ) ^ ((1 : ℝ) + (-beta * (2 : ℝ))) := by
                rw [Real.rpow_add hnR]
          _ = (n.divisors.card : ℝ) ^ 2 *
              (n : ℝ) ^ (-2 * (beta - 1 / 2)) := by ring_nf

/-- The finite L-series of the sharp Möbius cutoff is literally Ingham's mollifier. -/
theorem LSeries_complexCoeff_truncatedMoebius_eq_inghamMollifier
    (X : ℕ) (s : ℂ) :
    LSeries (complexCoeff (truncatedMoebius X)) s = inghamMollifier X s := by
  rw [LSeries_eq_sum_term_of_support
    (s := Finset.Icc 1 X)
    (fun n hn => coeffTrunc_support_Icc
      (((ArithmeticFunction.moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ))
      (by
        rw [← truncatedMoebius_eq_coeffTrunc]
        exact Complex.ofReal_injective.ne_iff.mp hn))]
  rw [inghamMollifier]
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : n ≠ 0 := Nat.ne_of_gt (Finset.mem_Icc.mp hn).1
  have hnX : n ≤ X := (Finset.mem_Icc.mp hn).2
  rw [LSeries.term_def, if_neg hn0, complexCoeff_apply,
    truncatedMoebius_apply, if_pos hnX]
  push_cast
  rw [div_eq_mul_inv, ← Complex.cpow_neg]

/-- Real arithmetic zeta complexifies to the classical Riemann zeta L-series. -/
theorem LSeriesSummable_complexCoeff_zeta {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable
      (complexCoeff (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) s := by
  have h := (ArithmeticFunction.LSeriesHasSum_zeta hs).LSeriesSummable
  have hseq : complexCoeff (ArithmeticFunction.zeta : ArithmeticFunction ℝ) =
      (fun n : ℕ => ((ArithmeticFunction.zeta n : ℕ) : ℂ)) := by
    funext n
    by_cases hn : n = 0
    · simp [complexCoeff, hn]
    · simp [complexCoeff, ArithmeticFunction.zeta_apply, hn]
  rw [hseq]
  exact h

theorem LSeries_complexCoeff_zeta_eq_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    LSeries (complexCoeff (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) s =
      riemannZeta s := by
  have h := ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs
  have hseq : complexCoeff (ArithmeticFunction.zeta : ArithmeticFunction ℝ) =
      (fun n : ℕ => ((ArithmeticFunction.zeta n : ℕ) : ℂ)) := by
    funext n
    by_cases hn : n = 0
    · simp [complexCoeff, hn]
    · simp [complexCoeff, ArithmeticFunction.zeta_apply, hn]
  rw [hseq]
  exact h

theorem complexCoeff_sub (F G : ArithmeticFunction ℝ) :
    complexCoeff (F - G) = complexCoeff F - complexCoeff G := by
  funext n
  change (((F n - G n : ℝ) : ℂ)) = (F n : ℂ) - (G n : ℂ)
  push_cast
  rfl

/-- Exact half-plane source identity for the sharp Möbius convolution defect. -/
theorem LSeries_complexCoeff_moebiusZetaDefect_eq
    (X : ℕ) {s : ℂ} (hs : 1 < s.re) :
    LSeries (complexCoeff (moebiusZetaDefect X)) s =
      1 - inghamMollifier X s * riemannZeta s := by
  have hM := LSeriesSummable_complexCoeff_truncatedMoebius X s
  have hZ := LSeriesSummable_complexCoeff_zeta hs
  have hP := LSeriesSummable_complexCoeff_mul hM hZ
  have h1 := LSeriesSummable_complexCoeff_one s
  have hfun : complexCoeff (moebiusZetaDefect X) =
      complexCoeff (1 : ArithmeticFunction ℝ) -
        complexCoeff (truncatedMoebius X *
          (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) := by
    rw [moebiusZetaDefect, complexCoeff_sub]
  rw [hfun, LSeries_sub h1 hP, LSeries_complexCoeff_one,
    LSeries_complexCoeff_mul hM hZ,
    LSeries_complexCoeff_truncatedMoebius_eq_inghamMollifier,
    LSeries_complexCoeff_zeta_eq_riemannZeta hs]

/-- Universal affine right-edge constant at damping exponent `beta`. -/
noncomputable def inghamRightEdgeMeanSquareConstant (beta : ℝ) : ℝ :=
  1 + 5 * Real.pi * Real.exp 1 *
      (∑' n : ℕ, (n.divisors.card : ℝ) ^ 2 *
        (n : ℝ) ^ (-2 * (beta - 1 / 2))) +
    (5 * Real.pi / 2) *
      (∑' n : ℕ, (n.divisors.card : ℝ) ^ 2 *
        (n : ℝ) ^ (-2 * beta))

theorem inghamRightEdgeMeanSquareConstant_pos (beta : ℝ) :
    0 < inghamRightEdgeMeanSquareConstant beta := by
  unfold inghamRightEdgeMeanSquareConstant
  have hW : 0 ≤ ∑' n : ℕ, (n.divisors.card : ℝ) ^ 2 *
      (n : ℝ) ^ (-2 * (beta - 1 / 2)) := tsum_nonneg fun n => by positivity
  have hP : 0 ≤ ∑' n : ℕ, (n.divisors.card : ℝ) ^ 2 *
      (n : ℝ) ^ (-2 * beta) := tsum_nonneg fun n => by positivity
  positivity

/-- **Uniform right-edge mean square.**  On every fixed line `beta > 1`, the literal Ingham
mollified error has second moment `O(T)`, uniformly in the sharp Möbius cutoff `X`. -/
theorem integral_Icc_normSq_inghamMollifiedError_right_le
    {beta : ℝ} (hbeta : 1 < beta) {X : ℕ} (hX : 1 ≤ X)
    {T : ℝ} (hT : 1 ≤ T) :
    (∫ t in Set.Icc (-T) T,
      ‖riemannZeta ((beta : ℂ) + (t : ℝ) * I) *
          inghamMollifier X ((beta : ℂ) + (t : ℝ) * I) - 1‖ ^ 2) ≤
      inghamRightEdgeMeanSquareConstant beta * T := by
  let a : ℕ → ℂ := complexCoeff (moebiusZetaDefect X)
  have habs := summable_norm_complexCoeff_moebiusZetaDefect_damped hX hbeta
  have hplain := summable_normSq_complexCoeff_moebiusZetaDefect_damped hX hbeta
  have hweighted :=
    summable_weighted_normSq_complexCoeff_moebiusZetaDefect_damped hX hbeta
  have hbase := integral_Icc_normSq_LSeries_le_general_affine_infinite
    (a := a) (complexCoeff_moebiusZetaDefect_zero X) beta
    habs hplain hweighted hT
  have hsource (t : ℝ) :
      ‖LSeries a ((beta : ℂ) + (t : ℝ) * I)‖ =
        ‖riemannZeta ((beta : ℂ) + (t : ℝ) * I) *
          inghamMollifier X ((beta : ℂ) + (t : ℝ) * I) - 1‖ := by
    have hs : 1 < (((beta : ℂ) + (t : ℝ) * I)).re := by
      simpa using hbeta
    rw [show a = complexCoeff (moebiusZetaDefect X) by rfl,
      LSeries_complexCoeff_moebiusZetaDefect_eq X hs]
    rw [show 1 - inghamMollifier X ((beta : ℂ) + (t : ℝ) * I) *
          riemannZeta ((beta : ℂ) + (t : ℝ) * I) =
        -(riemannZeta ((beta : ℂ) + (t : ℝ) * I) *
          inghamMollifier X ((beta : ℂ) + (t : ℝ) * I) - 1) by ring,
      norm_neg]
  have hplainPoint (n : ℕ) :
      ‖a n * (((n : ℝ) ^ (-beta) : ℝ) : ℂ)‖ ^ 2 ≤
        (n.divisors.card : ℝ) ^ 2 * (n : ℝ) ^ (-2 * beta) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [a]
    · have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      have hamp := norm_defect_damped_le hX beta n
      calc
        ‖a n * (((n : ℝ) ^ (-beta) : ℝ) : ℂ)‖ ^ 2
            ≤ ((n.divisors.card : ℝ) * (n : ℝ) ^ (-beta)) ^ 2 := by
          simpa [a] using pow_le_pow_left₀ (norm_nonneg _) hamp 2
        _ = (n.divisors.card : ℝ) ^ 2 * (n : ℝ) ^ (-2 * beta) := by
          rw [mul_pow, ← Real.rpow_natCast ((n : ℝ) ^ (-beta)) 2,
            ← Real.rpow_mul hnR.le]
          congr 2
          push_cast
          ring
  have hweightedPoint (n : ℕ) :
      (n : ℝ) * ‖a n * (((n : ℝ) ^ (-beta) : ℝ) : ℂ)‖ ^ 2 ≤
        (n.divisors.card : ℝ) ^ 2 *
          (n : ℝ) ^ (-2 * (beta - 1 / 2)) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [a]
    · have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      have hsq := hplainPoint n
      calc
        (n : ℝ) * ‖a n * (((n : ℝ) ^ (-beta) : ℝ) : ℂ)‖ ^ 2
            ≤ (n : ℝ) * ((n.divisors.card : ℝ) ^ 2 *
              (n : ℝ) ^ (-2 * beta)) :=
          mul_le_mul_of_nonneg_left hsq hnR.le
        _ = (n.divisors.card : ℝ) ^ 2 *
            (n : ℝ) ^ (-2 * (beta - 1 / 2)) := by
          nth_rewrite 1 [← Real.rpow_one (n : ℝ)]
          calc
            (n : ℝ) ^ (1 : ℝ) *
                ((n.divisors.card : ℝ) ^ 2 * (n : ℝ) ^ (-2 * beta)) =
                (n.divisors.card : ℝ) ^ 2 *
                  ((n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-2 * beta)) := by ring
            _ = (n.divisors.card : ℝ) ^ 2 *
                (n : ℝ) ^ ((1 : ℝ) + (-2 * beta)) := by
                  rw [Real.rpow_add hnR]
            _ = (n.divisors.card : ℝ) ^ 2 *
                (n : ℝ) ^ (-2 * (beta - 1 / 2)) := by ring_nf
  have hWbase := summable_divisor_sq_rpow
    (show 1 / 2 < beta - 1 / 2 by linarith)
  have hPbase := summable_divisor_sq_rpow
    (show 1 / 2 < beta by linarith)
  have hW : (∑' n : ℕ, (n : ℝ) *
      ‖a n * (((n : ℝ) ^ (-beta) : ℝ) : ℂ)‖ ^ 2) ≤
      ∑' n : ℕ, (n.divisors.card : ℝ) ^ 2 *
        (n : ℝ) ^ (-2 * (beta - 1 / 2)) :=
    Summable.tsum_le_tsum hweightedPoint hweighted hWbase
  have hP : (∑' n : ℕ,
      ‖a n * (((n : ℝ) ^ (-beta) : ℝ) : ℂ)‖ ^ 2) ≤
      ∑' n : ℕ, (n.divisors.card : ℝ) ^ 2 * (n : ℝ) ^ (-2 * beta) :=
    Summable.tsum_le_tsum hplainPoint hplain hPbase
  have hW0 : 0 ≤ ∑' n : ℕ, (n.divisors.card : ℝ) ^ 2 *
      (n : ℝ) ^ (-2 * (beta - 1 / 2)) := tsum_nonneg fun n => by positivity
  have hP0 : 0 ≤ ∑' n : ℕ, (n.divisors.card : ℝ) ^ 2 *
      (n : ℝ) ^ (-2 * beta) := tsum_nonneg fun n => by positivity
  have hT0 : 0 ≤ T := by linarith
  calc
    (∫ t in Set.Icc (-T) T,
      ‖riemannZeta ((beta : ℂ) + (t : ℝ) * I) *
          inghamMollifier X ((beta : ℂ) + (t : ℝ) * I) - 1‖ ^ 2) =
        ∫ t in Set.Icc (-T) T,
          ‖LSeries a ((beta : ℂ) + (t : ℝ) * I)‖ ^ 2 := by
            apply integral_congr_ae
            filter_upwards with t
            rw [hsource]
    _ ≤ 5 * Real.pi * Real.exp 1 *
          (∑' n : ℕ, (n : ℝ) *
            ‖a n * (((n : ℝ) ^ (-beta) : ℝ) : ℂ)‖ ^ 2) +
        (5 * Real.pi / 2) *
          (∑' n : ℕ, ‖a n * (((n : ℝ) ^ (-beta) : ℝ) : ℂ)‖ ^ 2) * T := hbase
    _ ≤ 5 * Real.pi * Real.exp 1 *
          (∑' n : ℕ, (n.divisors.card : ℝ) ^ 2 *
            (n : ℝ) ^ (-2 * (beta - 1 / 2))) +
        ((5 * Real.pi / 2) *
          (∑' n : ℕ, (n.divisors.card : ℝ) ^ 2 *
            (n : ℝ) ^ (-2 * beta))) * T := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hW (by positivity))
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hP (by positivity)) hT0)
    _ ≤ inghamRightEdgeMeanSquareConstant beta * T := by
      unfold inghamRightEdgeMeanSquareConstant
      have hA0 : 0 ≤ 5 * Real.pi * Real.exp 1 *
          (∑' n : ℕ, (n.divisors.card : ℝ) ^ 2 *
            (n : ℝ) ^ (-2 * (beta - 1 / 2))) := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hT hA0]

end

end RHTower.Sieve
