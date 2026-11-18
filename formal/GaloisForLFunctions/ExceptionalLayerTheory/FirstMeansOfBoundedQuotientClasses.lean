import GaloisForLFunctions.ExceptionalLayerTheory.TheDirichletSeriesOfDyadicBinomialPrimeCounts
import GaloisForLFunctions.ExceptionalLayerTheory.FiniteDilationsOfArithmeticKernels
import GaloisForLFunctions.ExceptionalLayerTheory.PairedCofactorBoundsForOrdinaryPrimeCounts

/-!
# First means of bounded quotient classes

If the prefix of a row is between zero and one, its piecewise linear
primitive has slopes in the same interval. Dividing the primitive by its
argument gives the first-mean kernel. At consecutive divisors its change
is at most the reciprocal of the larger divisor, independently of the row.
-/

noncomputable section

open Finset ArithmeticFunction

namespace GaloisForLFunctions.ExceptionalLayerTheory

private def tri (v : ℝ) : ℝ := if 1 ≤ v then 1-v⁻¹ else 0

private theorem tri_zero {x : ℝ} (hx : x ≤ 1) : tri x = 0 := by
  rcases hx.lt_or_eq with h | rfl
  · exact if_neg (not_le.mpr h)
  · norm_num [tri]

private def ramp (a : ArithmeticFunction ℝ) (x : ℝ) := x * arithmeticKernel a tri x

private theorem kernel_zero (a : ArithmeticFunction ℝ) {x : ℝ} (hx : x ≤ 1) :
    arithmeticKernel a tri x = 0 := by
  apply sum_eq_zero
  intro n hn
  have h1 : (1:ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp hn).1
  rw [tri_zero ((div_le_one (zero_lt_one.trans_le h1)).mpr (hx.trans h1)),smul_zero]

private theorem ramp_on_cell (a : ArithmeticFunction ℝ) {n : ℕ} {x : ℝ}
    (hx : (n:ℝ) ≤ x) (hu : x ≤ (n:ℝ)+1) :
    ramp a x = ∑ d ∈ Icc 1 n, a d*(x-d) := by
  rw [ramp,arithmeticKernel_on_unit_interval _ _ (tri_zero le_rfl) hx hu,mul_sum]
  refine sum_congr rfl fun d hd => ?_
  have hd0 : (0:ℝ) < d := by exact_mod_cast (mem_Icc.mp hd).1
  have hdx := (show (d:ℝ) ≤ n by exact_mod_cast (mem_Icc.mp hd).2).trans hx
  rw [tri,if_pos ((one_le_div hd0).mpr hdx),smul_eq_mul,inv_div]
  field_simp [(hd0.trans_le hdx).ne']

private theorem ramp_increments (a : ArithmeticFunction ℝ)
    (ha : ∀ n, 0 ≤ ∑ d ∈ Icc 1 n, a d ∧ ∑ d ∈ Icc 1 n, a d ≤ 1)
    {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    0 ≤ ramp a y-ramp a x ∧ ramp a y-ramp a x ≤ y-x := by
  apply of_adjacent_unit_intervals (P := fun u v =>
    0 ≤ ramp a v-ramp a u ∧ ramp a v-ramp a u ≤ v-u) _ _ hx hxy
  · intro n hn u v hnu huv hvn
    have he : ramp a v-ramp a u = (∑ d ∈ Icc 1 n, a d)*(v-u) := by
      rw [ramp_on_cell a (hnu.trans huv) hvn,ramp_on_cell a hnu (huv.trans hvn),
        ← sum_sub_distrib,sum_mul]
      exact sum_congr rfl fun d _ => by ring
    rw [he]
    exact ⟨mul_nonneg (ha n).1 (sub_nonneg.mpr huv),
      mul_le_of_le_one_left (sub_nonneg.mpr huv) (ha n).2⟩
  · intro u v w hv hw
    constructor <;> linarith only [hv.1,hv.2,hw.1,hw.2]

private theorem kernel_at_consecutive_divisors (a : ArithmeticFunction ℝ)
    (ha : ∀ n, 0 ≤ ∑ d ∈ Icc 1 n, a d ∧ ∑ d ∈ Icc 1 n, a d ≤ 1)
    {X n : ℕ} (hn : 1 ≤ n) (hnX : n ≤ X) :
    |arithmeticKernel a tri ((X:ℝ)/n)-arithmeticKernel a tri ((X:ℝ)/(n+1))| ≤ 1/(n+1) := by
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast hn
  have hs : 0 < (n:ℝ)+1 := by positivity
  rcases hnX.lt_or_eq with h | rfl
  · let x := (X:ℝ)/(n+1)
    let y := (X:ℝ)/n
    have hX : 0 < (X:ℝ) := by exact_mod_cast (show 0 < X by omega)
    have hx : 1 ≤ x := (one_le_div hs).mpr (by exact_mod_cast h)
    have hxy : x ≤ y := div_le_div_of_nonneg_left hX.le hn0 (by linarith)
    have hR := ramp_increments a ha hx hxy
    have hbase := ramp_increments a ha le_rfl hx
    have hz : ramp a 1 = 0 := by rw [ramp,kernel_zero a le_rfl,mul_zero]
    rw [hz,sub_zero] at hbase
    have hstep : (n:ℝ)*(y-x) = x := by dsimp only [x,y]; field_simp; ring
    have hi := mul_le_mul_of_nonneg_left hR.2 hn0.le
    rw [hstep] at hi
    have hlo := mul_nonneg hn0.le hR.1
    have hidentity : (X:ℝ)*(arithmeticKernel a tri y-arithmeticKernel a tri x) =
        n*(ramp a y-ramp a x)-ramp a x := by
      have hnY : (n:ℝ)*y = X := by dsimp only [y]; field_simp
      have hnX' : ((n:ℝ)+1)*x = X := by dsimp only [x]; field_simp
      unfold ramp
      linear_combination arithmeticKernel a tri x * hnX' - arithmeticKernel a tri y * hnY
    change |arithmeticKernel a tri y-arithmeticKernel a tri x| ≤ _
    have he : |(X:ℝ)*(arithmeticKernel a tri y-arithmeticKernel a tri x)| ≤ x := by
      rw [hidentity,abs_le]
      constructor <;> linarith only [hlo,hi,hbase.1,hbase.2]
    rw [abs_mul,abs_of_pos hX] at he
    apply le_of_mul_le_mul_left _ hX
    simpa only [mul_one_div] using he
  · rw [div_self hn0.ne',kernel_zero a le_rfl,kernel_zero a ((div_le_one hs).mpr (by linarith)),
      sub_zero,abs_zero]
    positivity

/-- Difference of the prime and integer first means for the last quotient class. -/
def lastClassFirstMeanExcess (q X : ℕ) : ℝ :=
  arithmeticKernel ((vonMangoldt-(zeta : ArithmeticFunction ℝ))*lastClassCoefficients q) tri X

/-- Count obtained by giving every positive integer weight one in the quotient class. -/
def lastClassIntegerCount (q M : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 M, ((zeta : ArithmeticFunction ℝ)*lastClassCoefficients q) n

private theorem weighted_eq_sum_prefix (f : ℕ → ℝ) (N : ℕ) :
    (∑ d ∈ Icc 1 N, f d*((N:ℝ)-d)) = ∑ k ∈ range N, ∑ d ∈ Icc 1 k, f d := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_Icc_succ_top (by omega : 1 ≤ N+1),Finset.sum_range_succ,← ih]
    simp only [Nat.cast_succ,sub_self,mul_zero,add_zero,← sum_add_distrib]
    exact sum_congr rfl fun d _ => by ring

/-- The triangular weight gives exactly the discrete mean over all earlier cutoffs. -/
theorem lastClassFirstMeanExcess_eq_sum (q X : ℕ) (hq : 2 ≤ q) :
    (X:ℝ)*lastClassFirstMeanExcess q X =
      ∑ k ∈ range X, (lastClassPrimeMass q k-lastClassIntegerCount q k) := by
  let f := (vonMangoldt-(zeta : ArithmeticFunction ℝ))*lastClassCoefficients q
  change ramp f X = _
  rw [ramp_on_cell f (n := X) le_rfl (by linarith),weighted_eq_sum_prefix]
  refine sum_congr rfl fun k _ => ?_
  rw [lastClassPrimeMass_eq_prefix q hq,lastClassIntegerCount,← sum_sub_distrib]
  refine sum_congr rfl fun n _ => ?_
  rw [show f = lastClassPrimeCoeff q - (zeta : ArithmeticFunction ℝ)*lastClassCoefficients q from
    sub_mul ..]
  rfl

/-- One universal constant controls the first-mean excess for every modulus. -/
theorem abs_lastClassFirstMeanExcess_le (q X : ℕ) (hq : 2 ≤ q) :
    |lastClassFirstMeanExcess q X| ≤ ∑ n ∈ Icc 1 X, |Chebyshev.psi n-n| / (n+1) := by
  let a := lastClassCoefficients q
  let c := vonMangoldt - (zeta : ArithmeticFunction ℝ)
  change |arithmeticKernel (c*a) tri (X:ℝ)| ≤ _
  rw [arithmeticKernel_mul c a tri (X:ℝ),
    arithmeticKernel_eq_prefix_differences c (arithmeticKernel a tri) (fun _ hy => kernel_zero a hy) X]
  simp only [c,sum_vonMangoldt_sub_zeta,smul_eq_mul]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro n hn
  rw [abs_mul]
  have hw := kernel_at_consecutive_divisors a (lastClassCoefficients_prefix_bounds q hq)
    (X := X) (mem_Icc.mp hn).1 (mem_Icc.mp hn).2
  exact (mul_le_mul_of_nonneg_left hw (abs_nonneg (Chebyshev.psi n-n))).trans_eq
    (div_eq_mul_one_div _ _).symm

#print axioms abs_lastClassFirstMeanExcess_le
#print axioms lastClassFirstMeanExcess_eq_sum

end GaloisForLFunctions.ExceptionalLayerTheory
