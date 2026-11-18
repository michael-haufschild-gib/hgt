import GaloisForLFunctions.ExceptionalLayerTheory.PairedCofactorBoundsForOrdinaryPrimeCounts
import GaloisForLFunctions.RHTower.ChebyshevPsiLogSummatory
import GaloisForLFunctions.RHTower.DirichletDivisorAsymptotic
import GaloisForLFunctions.RHTower.HarmonicStirlingExactBounds
import GaloisForLFunctions.RHTower.ZetaLittlewoodDeficit
import GaloisForLFunctions.RHTower.RouteECofactorSquarefreeHarmonic

/-!
# Completing the divisor row retains the original prime error

The complete divisor average of the ordinary Chebyshev error has linear
term `-2γN` and square-root remainder by the Dirichlet hyperbola formula.
The Vaughan cofactor also contains a unit coefficient. After the linear
term is removed, completing this cofactor therefore reproduces the
ordinary prime error with an explicit error for every Möbius cutoff.
-/

noncomputable section

open Finset ArithmeticFunction
open RHTower.Sieve

namespace GaloisForLFunctions.ExceptionalLayerTheory

private abbrev excess := vonMangoldt - (zeta : ArithmeticFunction ℝ)

/-- Sum of the prime error over all integral divisor rows. -/
def completeDivisorError (N : ℕ) : ℝ :=
  ∑ d ∈ Icc 1 N, (Chebyshev.psi (N / d : ℕ) - (N / d : ℕ))

private theorem zeta_excess_sum (N : ℕ) :
    (∑ n ∈ Icc 1 N, ((zeta : ArithmeticFunction ℝ) * excess) n) = completeDivisorError N := by
  rw [RHTower.sum_Icc_mul_apply]
  refine sum_congr rfl fun d hd => ?_
  rw [sum_vonMangoldt_sub_zeta, ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply,
    if_neg (Nat.ne_of_gt (mem_Icc.mp hd).1)]
  simp

/-- The unweighted complete divisor row has square-root error around its linear mean. -/
theorem abs_completeDivisorError_add_le (N : ℕ) :
    |completeDivisorError N + 2 * Real.eulerMascheroniConstant * N| ≤ 25 * Real.sqrt N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [completeDivisorError]
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hs : 1 ≤ Real.sqrt N := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hn
  have hpsi (q : ℕ) : Chebyshev.psi q = RHTower.chebyshevPsi q := by
    unfold Chebyshev.psi RHTower.chebyshevPsi
    rw [Nat.floor_natCast]
    rfl
  have hsum : completeDivisorError N = (∑ n ∈ Icc 1 N, Real.log n) -
      ∑ d ∈ Icc 1 N, ((N / d : ℕ) : ℝ) := by
    unfold completeDivisorError
    rw [sum_sub_distrib, ← RHTower.floorSummatory_chebyshevPsi]
    simp only [hpsi, RHTower.floorSummatory]
  have hd := abs_le.mp (RHTower.abs_sum_div_sub_dirichlet_le N hN)
  have hlow := RHTower.stirling_le_sum_log N hN
  have hup := (RHTower.sum_log_Icc_exact_stirling_bounds hN).2
  have hπ := Real.log_le_sub_one_of_pos (show 0 < 2 * Real.pi by positivity)
  have hinv : 1 / (12 * (N : ℝ)) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith only [hn])
  have hlog := RHTower.log_le_sqrt (zero_lt_one.trans_le hn)
  rw [hsum, abs_le]
  constructor
  · linarith only [hd.2, hlow, hs]
  · linarith only [hd.1, hup, hπ, Real.pi_lt_four, hinv, hlog, hs]

/-- For every cutoff, completing the cofactor recovers the prime error minus
the truncated Möbius average of complete divisor errors. -/
theorem completedCofactor_eq_prime_sub_divisor (V N : ℕ) :
    cofactorCountError V N N = Chebyshev.psi N - N -
      ∑ d ∈ Icc 1 N, truncAF (moebius : ArithmeticFunction ℝ) V d *
        completeDivisorError (N / d) := by
  have hrow := RHTower.sum_Icc_mul_apply (typeIIShort V) excess N
  simp_rw [sum_vonMangoldt_sub_zeta] at hrow
  rw [cofactorCountError_eq, min_self, ← hrow]
  let μ := truncAF (moebius : ArithmeticFunction ℝ) V
  have hsplit : typeIIShort V * excess = excess - μ * ((zeta : ArithmeticFunction ℝ) * excess) := by
    change (1 - (zeta : ArithmeticFunction ℝ) * μ) * excess = _
    rw [sub_mul, one_mul, mul_comm (zeta : ArithmeticFunction ℝ) μ, mul_assoc]
  rw [hsplit]
  change (∑ n ∈ Icc 1 N, (excess n - (μ * ((zeta : ArithmeticFunction ℝ) * excess)) n)) = _
  rw [sum_sub_distrib, sum_vonMangoldt_sub_zeta, RHTower.sum_Icc_mul_apply]
  simp only [zeta_excess_sum, μ]

/-- Quantitative comparison, uniform in both the Möbius cutoff and the count horizon. -/
theorem abs_completedCofactor_sub_prime_sub_mean_le (V N : ℕ) :
    |cofactorCountError V N N - (Chebyshev.psi N - N) -
      2 * Real.eulerMascheroniConstant * ∑ d ∈ Icc 1 N,
        truncAF (moebius : ArithmeticFunction ℝ) V d * (N / d : ℕ)| ≤
      25 * ∑ d ∈ Icc 1 N, |truncAF (moebius : ArithmeticFunction ℝ) V d| *
        Real.sqrt (N / d : ℕ) := by
  rw [completedCofactor_eq_prime_sub_divisor]
  let μ := truncAF (moebius : ArithmeticFunction ℝ) V
  have heq : Chebyshev.psi N - N - (∑ d ∈ Icc 1 N, μ d * completeDivisorError (N/d)) -
      (Chebyshev.psi N - N) - 2 * Real.eulerMascheroniConstant *
      (∑ d ∈ Icc 1 N, μ d * (N / d : ℕ)) =
      -(∑ d ∈ Icc 1 N, μ d * (completeDivisorError (N/d) +
        2 * Real.eulerMascheroniConstant * (N / d : ℕ))) := by
    simp_rw [mul_add, sum_add_distrib, mul_sum]
    have h (d : ℕ) : μ d * (2 * Real.eulerMascheroniConstant * (N/d : ℕ)) =
        2 * Real.eulerMascheroniConstant * (μ d * (N/d : ℕ)) := by ring
    simp_rw [h]
    ring
  rw [heq, abs_neg, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun d _ => ?_)
  rw [abs_mul]
  exact (mul_le_mul_of_nonneg_left (abs_completeDivisorError_add_le (N / d)) (abs_nonneg _)).trans_eq
    (by ring)

/-- Uniform cost of completing the divisor row when the Möbius cutoff also moves. -/
theorem abs_completedCofactor_sub_prime_sub_mean_le_sqrt (V N : ℕ) :
    |cofactorCountError V N N - (Chebyshev.psi N - N) -
      2 * Real.eulerMascheroniConstant * ∑ d ∈ Icc 1 N,
        truncAF (moebius : ArithmeticFunction ℝ) V d * (N / d : ℕ)| ≤
      50 * Real.sqrt N * Real.sqrt V := by
  let μ := truncAF (moebius : ArithmeticFunction ℝ) V
  have hsum : (∑ d ∈ Icc 1 N, |μ d| * Real.sqrt (N / d : ℕ)) ≤
      Real.sqrt N * (2 * Real.sqrt V) := by
    calc
      _ = ∑ d ∈ Icc 1 (min N V), |μ d| * Real.sqrt (N / d : ℕ) := by
        apply (sum_subset (Icc_subset_Icc_right (min_le_left N V)) _).symm
        intro d hd hnot
        have hdV : V < d := by
          by_contra! h
          exact hnot (mem_Icc.mpr ⟨(mem_Icc.mp hd).1, le_min (mem_Icc.mp hd).2 h⟩)
        simp only [μ, truncAF_apply_of_gt hdV, abs_zero, zero_mul]
      _ ≤ ∑ d ∈ Icc 1 (min N V), Real.sqrt N * (Real.sqrt d)⁻¹ := by
        apply sum_le_sum
        intro d _
        calc
          _ ≤ Real.sqrt (N / d : ℕ) := mul_le_of_le_one_left (Real.sqrt_nonneg _) (abs_truncAF_moebius_le_one V d)
          _ ≤ Real.sqrt ((N : ℝ) / d) := Real.sqrt_le_sqrt (Nat.cast_div_le (m := N) (n := d))
          _ = _ := by rw [Real.sqrt_div (Nat.cast_nonneg _), div_eq_mul_inv]
      _ ≤ _ := by
        rw [← mul_sum]
        apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
        exact (sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right (min_le_right N V))
          (fun d _ _ => inv_nonneg.mpr (Real.sqrt_nonneg d))).trans (sum_sqrtInv_le V)
  exact (abs_completedCofactor_sub_prime_sub_mean_le V N).trans
    ((mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 25)).trans_eq (by ring))

/-- Restoring the omitted cofactors changes the cut count by a signed sum
of ordinary prime errors at the complementary divided horizons. -/
theorem cofactorCount_add_tail (V W N : ℕ) :
    cofactorCountError V W N + (∑ d ∈ Ioc W N, typeIIShort V d *
      (Chebyshev.psi (N / d : ℕ) - (N / d : ℕ))) = cofactorCountError V N N := by
  let f (d : ℕ) := typeIIShort V d * (Chebyshev.psi (N / d : ℕ) - (N / d : ℕ))
  have hsmall : (Icc 1 N).filter (· ≤ W) = Icc 1 (min N W) := by
    ext d
    simp only [mem_filter, mem_Icc, le_min_iff]
    tauto
  have hlarge : (Icc 1 N).filter (fun d => ¬ d ≤ W) = Ioc W N := by
    ext d
    simp only [mem_filter, mem_Icc, mem_Ioc]
    omega
  simpa only [cofactorCountError_eq, min_self, hsmall, hlarge, f] using
    (sum_filter_add_sum_filter_not (Icc 1 N) (· ≤ W) f)

/-- An explicit square-root estimate for the fixed-cutoff count together
with its complementary divisor sum, uniform even in a moving Möbius cutoff. -/
theorem abs_cofactorCount_add_tail_sub_prime_sub_mean_le (V W N : ℕ) :
    |cofactorCountError V W N + (∑ d ∈ Ioc W N, typeIIShort V d *
      (Chebyshev.psi (N / d : ℕ) - (N / d : ℕ))) - (Chebyshev.psi N - N) -
      2 * Real.eulerMascheroniConstant * ∑ d ∈ Icc 1 N,
        truncAF (moebius : ArithmeticFunction ℝ) V d * (N / d : ℕ)| ≤
      50 * Real.sqrt N * Real.sqrt V := by
  rw [cofactorCount_add_tail]
  exact abs_completedCofactor_sub_prime_sub_mean_le_sqrt V N

#print axioms abs_completeDivisorError_add_le
#print axioms abs_cofactorCount_add_tail_sub_prime_sub_mean_le

end GaloisForLFunctions.ExceptionalLayerTheory
