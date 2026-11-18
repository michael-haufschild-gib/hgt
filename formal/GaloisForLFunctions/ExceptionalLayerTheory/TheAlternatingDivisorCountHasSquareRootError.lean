import GaloisForLFunctions.ExceptionalLayerTheory.TheCompletedCofactorRowRetainsThePrimeError

/-!
# The alternating divisor count of the ordinary prime error

Subtracting twice the divisor count at half the cutoff removes its linear
term. On each prime column the resulting cumulative weight is the parity
of the integral quotient, hence takes only the values zero and one.
-/

noncomputable section

open Finset ArithmeticFunction
open scoped LSeries.notation
open RHTower.Sieve hiding dirPoly
open RHTower.WeilFiniteType

namespace GaloisForLFunctions.ExceptionalLayerTheory

private abbrev primeExcess := vonMangoldt - (zeta : ArithmeticFunction ℝ)

/-- The finite dilation whose convolution turns constant coefficients into alternating signs. -/
def dyadicCountDifference : ArithmeticFunction ℝ where
  toFun n := (if n = 1 then 1 else 0) - (if n = 2 then 2 else 0)
  map_zero' := by norm_num

private theorem dyadicCountDifference_apply (n : ℕ) : dyadicCountDifference n =
    (if n = 1 then 1 else 0) - (if n = 2 then 2 else 0) := rfl

/-- The signed coefficient with summatory function equal to parity. -/
def alternatingDivisorCoeff : ArithmeticFunction ℝ := dyadicCountDifference * zeta

/-- The alternating convolution of the centered von Mangoldt count. -/
def alternatingPrimeExcess : ArithmeticFunction ℝ := alternatingDivisorCoeff * primeExcess

private theorem apply_dyadic_count (F : ℕ → ℝ) (hF : F 0 = 0) (N : ℕ) :
    ∑ d ∈ Icc 1 N, dyadicCountDifference d * F (N/d) = F N - 2 * F (N/2) := by
  simp_rw [dyadicCountDifference_apply, sub_mul, ite_mul, zero_mul, one_mul]
  rw [sum_sub_distrib, sum_ite_eq', sum_ite_eq']
  by_cases h : 2 ≤ N
  · simp [mem_Icc, h, (by omega : 1 ≤ N)]
  · obtain rfl | rfl : N = 0 ∨ N = 1 := by omega
    · simp [hF]
    · norm_num [hF]

private theorem prefix_zeta (N : ℕ) : (∑ n ∈ Icc 1 N, (zeta : ArithmeticFunction ℝ) n) = N := by
  have hterm (n : ℕ) (hn : n ∈ Icc 1 N) : (zeta : ArithmeticFunction ℝ) n = 1 := by
    simp [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, Nat.ne_of_gt (mem_Icc.mp hn).1]
  rw [sum_congr rfl hterm]
  simp

/-- Each prefix of the alternating coefficients is zero or one according to its parity. -/
theorem prefix_alternatingDivisorCoeff (N : ℕ) :
    (∑ n ∈ Icc 1 N, alternatingDivisorCoeff n) = (N % 2 : ℕ) := by
  rw [alternatingDivisorCoeff,RHTower.sum_Icc_mul_apply]
  simp_rw [prefix_zeta]
  rw [apply_dyadic_count (fun n : ℕ => (n : ℝ)) (by simp)]
  have h : ((N % 2 : ℕ) : ℝ) + 2 * ((N/2 : ℕ) : ℝ) = N := by exact_mod_cast Nat.mod_add_div N 2
  linarith only [h]

private theorem prefix_all_prime_excess (N : ℕ) :
    (∑ n ∈ Icc 1 N, ((zeta : ArithmeticFunction ℝ) * primeExcess) n) = completeDivisorError N := by
  rw [RHTower.sum_Icc_mul_apply]
  refine sum_congr rfl fun d hd => ?_
  rw [sum_vonMangoldt_sub_zeta, ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply,
    if_neg (Nat.ne_of_gt (mem_Icc.mp hd).1)]
  simp

/-- The entire signed row is a difference of two complete divisor counts. -/
theorem prefix_alternatingPrimeExcess (N : ℕ) :
    (∑ n ∈ Icc 1 N, alternatingPrimeExcess n) = completeDivisorError N - 2*completeDivisorError (N/2) := by
  rw [alternatingPrimeExcess,alternatingDivisorCoeff,mul_assoc,RHTower.sum_Icc_mul_apply]
  simp_rw [prefix_all_prime_excess]
  exact apply_dyadic_count _ (by simp [completeDivisorError]) N

/-- The same row is a sum of actual prime excesses on the odd-quotient columns. -/
theorem alternatingPrimeExcess_eq_parity_count (N : ℕ) :
    (∑ n ∈ Icc 1 N, alternatingPrimeExcess n) =
      ∑ d ∈ Icc 1 N, primeExcess d * ((N/d % 2 : ℕ) : ℝ) := by
  rw [alternatingPrimeExcess,mul_comm,RHTower.sum_Icc_mul_apply]
  simp_rw [prefix_alternatingDivisorCoeff]

/-- The parity-weighted count has square-root error at every integral cutoff. -/
theorem abs_prefix_alternatingPrimeExcess (N : ℕ) :
    |∑ n ∈ Icc 1 N, alternatingPrimeExcess n| ≤ (75 + 2*|Real.eulerMascheroniConstant|) * Real.sqrt N := by
  rw [prefix_alternatingPrimeExcess]
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [completeDivisorError]
  let γ := Real.eulerMascheroniConstant
  have h₁ := abs_completeDivisorError_add_le N
  have h₂ := abs_completeDivisorError_add_le (N/2)
  have hs := Real.sqrt_le_sqrt (show ((N/2 : ℕ) : ℝ) ≤ N by exact_mod_cast Nat.div_le_self N 2)
  have hone : 1 ≤ Real.sqrt N := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (show (1:ℝ) ≤ N by exact_mod_cast hN)
  have hmod : ((N % 2 : ℕ) : ℝ) + 2 * ((N/2 : ℕ) : ℝ) = N := by exact_mod_cast Nat.mod_add_div N 2
  have hrem : |2*γ*((N%2 : ℕ):ℝ)| ≤ 2 * |γ| * Real.sqrt N := by
    rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg (N%2) : (0:ℝ) ≤ (N%2:ℕ)),
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact mul_le_mul_of_nonneg_left ((show ((N%2 : ℕ):ℝ) ≤ 1 by
      exact_mod_cast (show N%2 ≤ 1 by omega)).trans hone)
      (by positivity)
  have he : completeDivisorError N - 2*completeDivisorError (N/2) =
      (completeDivisorError N + 2*γ*N) - 2*(completeDivisorError (N/2) + 2*γ*((N/2 : ℕ):ℝ)) -
        2*γ*((N%2 : ℕ):ℝ) := by linear_combination 2*γ*hmod
  rw [he]
  apply (abs_sub _ _).trans
  apply (add_le_add (abs_sub _ _) le_rfl).trans
  rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
  change _ ≤ (75 + 2*|γ|) * Real.sqrt N
  linarith only [h₁,h₂,hs,hrem]

private abbrev complexCoeff (f : ArithmeticFunction ℝ) := fun n : ℕ => (f n : ℂ)

private theorem complexCoeff_mul (f g : ArithmeticFunction ℝ) :
    complexCoeff (f*g) = (complexCoeff f ⍟ complexCoeff g) := by
  funext n
  rw [LSeries.convolution_def]
  exact coe_mul_apply _ _ _

private theorem complexCoeff_zeta : complexCoeff (zeta : ArithmeticFunction ℝ) =
    fun n => ((zeta n : ℕ) : ℂ) := by
  funext n
  by_cases hn : n = 0 <;> simp [complexCoeff, ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, hn]

/-- Symbol of the signed dilation at one and two. -/
def alternatingDivisorFactor (s : ℂ) : ℂ := 1 - 2*(2:ℂ)^(-s)

private theorem dyadic_series (s : ℂ) : LSeriesSummable (complexCoeff dyadicCountDifference) s ∧
    LSeries (complexCoeff dyadicCountDifference) s = alternatingDivisorFactor s := by
  have hs : SupportedIn 2 dyadicCountDifference := ⟨ArithmeticFunction.map_zero, fun n hn => by
    simp [dyadicCountDifference_apply, show n ≠ 1 by omega, show n ≠ 2 by omega]⟩
  refine ⟨LSeriesSummable_of_supportedIn hs s, ?_⟩
  rw [LSeries_eq_dirPoly hs, dirPoly, show Icc 1 2 = ({1,2} : Finset ℕ) by ext n; simp; omega]
  norm_num [dyadicCountDifference_apply, alternatingDivisorFactor]
  ring

/-- The two ordinary Dirichlet series, before and after convolution with the prime excess. -/
theorem alternatingDivisor_series_on_euler {s : ℂ} (hs : 1 < s.re) :
    (LSeriesSummable (complexCoeff alternatingDivisorCoeff) s ∧
      LSeries (complexCoeff alternatingDivisorCoeff) s = alternatingDivisorFactor s * riemannZeta s) ∧
    (LSeriesSummable (complexCoeff alternatingPrimeExcess) s ∧
      LSeries (complexCoeff alternatingPrimeExcess) s = alternatingDivisorFactor s * riemannZeta s *
        (-deriv riemannZeta s / riemannZeta s - riemannZeta s)) := by
  obtain ⟨hd,hD⟩ := dyadic_series s
  have hz : LSeriesSummable (complexCoeff (zeta : ArithmeticFunction ℝ)) s := by
    rw [complexCoeff_zeta]
    exact ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs
  have hZ : LSeries (complexCoeff (zeta : ArithmeticFunction ℝ)) s = riemannZeta s := by
    rw [complexCoeff_zeta]
    exact ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs
  have ha : complexCoeff alternatingDivisorCoeff = complexCoeff dyadicCountDifference ⍟
      complexCoeff (zeta : ArithmeticFunction ℝ) := complexCoeff_mul _ _
  have hA : LSeries (complexCoeff alternatingDivisorCoeff) s = alternatingDivisorFactor s * riemannZeta s := by
    rw [ha,LSeries_convolution' hd hz,hD,hZ]
  have has : LSeriesSummable (complexCoeff alternatingDivisorCoeff) s := by
    rw [ha]
    exact hd.convolution hz
  have he : complexCoeff primeExcess = complexCoeff vonMangoldt - complexCoeff (zeta : ArithmeticFunction ℝ) :=
    funext fun n => Complex.ofReal_sub _ _
  have hl : LSeriesSummable (complexCoeff vonMangoldt) s := ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have hes : LSeriesSummable (complexCoeff primeExcess) s := by
    rw [he]
    exact hl.sub hz
  refine ⟨⟨has,hA⟩,?_,?_⟩
  · rw [alternatingPrimeExcess,complexCoeff_mul]
    exact has.convolution hes
  · rw [alternatingPrimeExcess,complexCoeff_mul,LSeries_convolution' has hes,hA,he,LSeries_sub hl hz,
      ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs,hZ]

#print axioms alternatingPrimeExcess_eq_parity_count
#print axioms abs_prefix_alternatingPrimeExcess
#print axioms alternatingDivisor_series_on_euler

end GaloisForLFunctions.ExceptionalLayerTheory
