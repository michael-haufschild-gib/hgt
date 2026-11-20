import GaloisForLFunctions.RestrictedFactorizationCalculus.ThePrimeReadingsBeyondTheHyperbola
import GaloisForLFunctions.RestrictedFactorizationCalculus.TheSmoothPopulationAtAnInteriorQuotientCut

/-!
# The first rows of the corrected prime-power interior

The worst-case perturbation estimate in Shi, Chen, Huang and Wang,
Corollary 5.2, suggests measuring sensitivity to the full box of
independent increment errors. For a corrected rough hyperbola reading its exact norm
is the Mangoldt-weighted absolute mass of its quotient coefficients.
Above the first potential composite cofactor those coefficients count primes.
-/
noncomputable section
open Finset ArithmeticFunction RHTower.CoprimeMobius
open scoped Classical ArithmeticFunction.Moebius
open GaloisForLFunctions.BezoutValuationIncidence
namespace GaloisForLFunctions.RestrictedFactorizationCalculus

/-- Coefficient of one input increment in the corrected rough interior. -/
def interiorKernel (y X T q : ℕ) :=
  coprimeMoebiusSum (primorial y) (X/q)-coprimeMoebiusSum (primorial y) (min X T/q)

private theorem extended_head (a : ArithmeticFunction ℝ) (y : ℕ) {L X : ℕ} (hle : L ≤ X) :
    (∑ q∈Icc 1 L,a q*coprimeMoebiusSum (primorial y) (L/q))=
      ∑ q∈Icc 1 X,a q*coprimeMoebiusSum (primorial y) (L/q) := by
  apply sum_subset (Icc_subset_Icc_right hle)
  intro q hq hnot
  have hhigh : L < q := lt_of_not_ge (fun h => hnot (mem_Icc.mpr ⟨(mem_Icc.mp hq).1,h⟩))
  simp [Nat.div_eq_of_lt hhigh,coprimeMoebiusSum]

/-- Every arithmetic increment has a coefficient independent of the input.
The lower endpoint uses the same rough prefix as the upper endpoint. -/
theorem rough_interior_as_kernel (a : ArithmeticFunction ℝ) (y X T : ℕ) :
    roughInteriorReading a y X T=∑ q∈Icc 1 X,a q*interiorKernel y X T q := by
  have h := rough_head_and_interior a y X T
  rw [rough_action_as_a_coefficient_prefix] at h
  change quotientReading (roughFloorCoefficient y a) X=roughInteriorReading a y X T+_ at h
  rw [coefficient_head_as_quotient_sum,coefficient_head_as_quotient_sum,
    extended_head a y (min_le_left X T)] at h
  simp only [interiorKernel,mul_sub,sum_sub_distrib]
  linarith only [h]

/-- Exact operator norm for independently bounded Mangoldt increments. -/
def interiorMangoldtNorm (y X T : ℕ) :=
  ∑ q∈Icc 1 X,vonMangoldt q*|interiorKernel y X T q|

private def saturatingWeight (y X T : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun q => if 0 ≤ interiorKernel y X T q then vonMangoldt q else -vonMangoldt q,by simp⟩

/-- The upper bound is attained at a signed Mangoldt weight, including
cutoffs at which some or all quotient coefficients disappear. -/
theorem exact_norm_of_rough_interior (y X T : ℕ) :
    IsGreatest {v : ℝ | ∃ a : ArithmeticFunction ℝ,(∀ n,|a n| ≤ vonMangoldt n) ∧
      v=|roughInteriorReading a y X T|} (interiorMangoldtNorm y X T) := by
  constructor
  · refine ⟨saturatingWeight y X T,fun n => ?_,?_⟩
    · change |if _ then vonMangoldt n else -vonMangoldt n| ≤ _
      split <;> simp [abs_of_nonneg (vonMangoldt_nonneg (n:=n))]
    · rw [rough_interior_as_kernel]
      have hterm (q : ℕ) : saturatingWeight y X T q*interiorKernel y X T q=
          vonMangoldt q*|interiorKernel y X T q| := by
        change (if _ then _ else _)*_=_
        split_ifs with h
        · rw [abs_of_nonneg h]
        · rw [abs_of_neg (lt_of_not_ge h)];ring
      simp_rw [hterm]
      exact (abs_of_nonneg (sum_nonneg fun i _ => mul_nonneg
        (vonMangoldt_nonneg (n:=i)) (abs_nonneg _))).symm
  · rintro v ⟨a,ha,rfl⟩
    rw [rough_interior_as_kernel]
    exact (abs_sum_le_sum_abs ..).trans (sum_le_sum fun q _ => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (ha q) (abs_nonneg _))

/-- The unit and the surviving prime atoms determine the rough prefix
through the first possible composite cofactor. -/
theorem rough_prefix_before_composites {y m : ℕ} (hm : 0 < m) (hy : m ≤ y^2) :
    coprimeMoebiusSum (primorial y) m=1-((RHTower.Sieve.bigPrimeSet y m).card:ℝ) := by
  have h := rough_row_through_the_first_prime_band hm hy (fun _ => (1:ℝ))
  simp only [mul_one,sum_const,nsmul_eq_mul,mul_one] at h
  rw [←h]
  exact sum_congr rfl (fun n hn => primorial_indicator_eq_deleted_mobius y n (mem_Icc.mp hn).1)

/-- In the prime-only cofactor range the top rows pass through unchanged,
the next rows vanish, and every further prime subtracts one unit. -/
theorem interior_kernel_before_composites {y X T q : ℕ} (hq : 0 < q) (hqX : q ≤ X)
    (ht : T < q) (hr : X/q ≤ y^2) :
    interiorKernel y X T q=1-((RHTower.Sieve.bigPrimeSet y (X/q)).card:ℝ) := by
  have hzero : min X T/q=0 := Nat.div_eq_of_lt ((min_le_right X T).trans_lt ht)
  have hz : coprimeMoebiusSum (primorial y) 0=0 := by simp [coprimeMoebiusSum]
  rw [interiorKernel,hzero,hz,sub_zero]
  exact rough_prefix_before_composites (Nat.div_pos hqX hq) hr

/-- A unit coefficient persists until the first possible surviving prime
cofactor. This applies to all arithmetic inputs, with either sign. -/
theorem interior_kernel_upper_plateau {y X T q : ℕ} (hq : 0 < q) (hqX : q ≤ X)
    (ht : T < q) (hr : X/q ≤ y) : interiorKernel y X T q=1 := by
  have hsq : y ≤ y^2 := Nat.le_self_pow (by decide : 2≠0) y
  rw [interior_kernel_before_composites hq hqX ht (hr.trans hsq)]
  have hnone : RHTower.Sieve.bigPrimeSet y (X/q)=∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro n hn
    obtain ⟨hmem,_⟩ := mem_filter.mp hn
    obtain ⟨hl,hu⟩ := mem_Icc.mp hmem
    omega
  simp [hnone]

/-- On an isolated upper block the norm equals its full positive mass;
every input increment there reaches the interior with sign and size intact. -/
theorem upper_block_passes_through (a : ArithmeticFunction ℝ) {y X T B : ℕ}
    (ht : T ≤ B) (hc : X/(y+1) ≤ B) (hs : ∀ q ≤ B,a q=0) :
    roughInteriorReading a y X T=∑ q∈Ioc B X,a q := by
  rw [rough_interior_as_kernel]
  have hterm (q : ℕ) (hq : q∈Icc 1 X) :
      a q*interiorKernel y X T q=if B < q then a q else 0 := by
    by_cases hb : B < q
    · rw [if_pos hb,interior_kernel_upper_plateau (mem_Icc.mp hq).1 (mem_Icc.mp hq).2
        (ht.trans_lt hb) (by
          apply Nat.lt_succ_iff.mp
          apply (Nat.div_lt_iff_lt_mul (mem_Icc.mp hq).1).mpr
          have h := (Nat.div_lt_iff_lt_mul (Nat.succ_pos y)).mp (hc.trans_lt hb)
          simpa only [Nat.mul_comm] using h),mul_one]
    · simp [hb,hs q (le_of_not_gt hb)]
  rw [sum_congr rfl hterm,←sum_filter]
  congr 1
  ext q
  simp only [mem_filter,mem_Icc,mem_Ioc]
  omega

#print axioms exact_norm_of_rough_interior
#print axioms rough_prefix_before_composites
#print axioms interior_kernel_before_composites
#print axioms upper_block_passes_through
end GaloisForLFunctions.RestrictedFactorizationCalculus
