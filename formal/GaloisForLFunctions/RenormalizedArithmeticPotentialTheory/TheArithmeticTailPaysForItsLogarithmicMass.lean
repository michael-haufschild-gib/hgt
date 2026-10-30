import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.ThePrimeDefectLocalizesAtAMacroscopicCutoff
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheMarkovFormFailsInsideTheSeparatedRegime

/-!
# Arithmetic cutoffs and logarithmic tail mass

A coefficient cutoff gives an exact decomposition of the synthesized test
and its coefficient mass. Below the cutoff spacing, the two synthesized
supports are ordered. The prime-edge defect pays the horizon logarithm on
the tail with an arbitrarily near-unit coefficient and a bounded cutoff
remainder.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Finset
open scoped Chebyshev
namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
open ArithmeticFunction ArithmeticElectrostatics SpacingScaleHarmonicAnalysis

/-- Coefficients strictly above an arithmetic cutoff. -/
def atomicTailCoefficients (M : ℕ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  if M < n then x n else 0

/-- The prefix and complementary tail partition a finite arithmetic interval. -/
theorem sum_Icc_prefix_add_tail {M N : ℕ} (hMN : M ≤ N) (f : ℕ → ℝ) :
    (∑ n ∈ Icc 1 M, f n) + (∑ n ∈ Icc 1 N, if M < n then f n else 0) =
      ∑ n ∈ Icc 1 N, f n := by
  have hfilter : (Icc 1 N).filter (fun n => n ≤ M) = Icc 1 M := by
    ext n
    simp only [mem_filter, mem_Icc]
    omega
  have hlow : (∑ n ∈ Icc 1 N, if n ≤ M then f n else 0) =
      ∑ n ∈ Icc 1 M, f n := by rw [← sum_filter, hfilter]
  rw [← hlow, ← sum_add_distrib]
  refine sum_congr rfl fun n _ => ?_
  by_cases h : M < n
  · rw [if_neg (not_le.mpr h), if_pos h, zero_add]
  · rw [if_pos (le_of_not_gt h), if_neg h, add_zero]

/-- Squaring preserves the sharp coefficient cutoff. -/
theorem atomicTailCoefficients_sq (M : ℕ) (x : ℕ → ℝ) (n : ℕ) :
    atomicTailCoefficients M x n ^ 2 = if M < n then x n ^ 2 else 0 := by
  by_cases h : M < n
  · simp only [atomicTailCoefficients, if_pos h]
  · simp only [atomicTailCoefficients, if_neg h, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]

/-- Coefficient square mass splits exactly at the cutoff. -/
theorem sum_sq_prefix_add_tail {M N : ℕ} (hMN : M ≤ N) (x : ℕ → ℝ) :
    (∑ n ∈ Icc 1 M, x n ^ 2) +
      (∑ n ∈ Icc 1 N, atomicTailCoefficients M x n ^ 2) =
        ∑ n ∈ Icc 1 N, x n ^ 2 := by
  simp_rw [atomicTailCoefficients_sq]
  exact sum_Icc_prefix_add_tail hMN _

/-- The original synthesized test is the exact sum of its prefix and tail. -/
theorem atomicTest_eq_prefix_add_tail {M N : ℕ} (hMN : M ≤ N)
    (x : ℕ → ℝ) (g : ℝ → ℝ) :
    atomicTest N x g = fun u => atomicTest M x g u + atomicTest N (atomicTailCoefficients M x) g u := by
  funext u
  unfold atomicTest
  have ht : (∑ n ∈ Icc 1 N, atomicTailCoefficients M x n * g (u - Real.log n)) =
      ∑ n ∈ Icc 1 N, if M < n then x n * g (u - Real.log n) else 0 := by
    refine sum_congr rfl fun n _ => ?_
    by_cases h : M < n <;> simp only [atomicTailCoefficients, h, if_true, if_false, zero_mul]
  rw [ht]
  exact (sum_Icc_prefix_add_tail hMN _).symm

/-- The prefix ends no later than its final logarithmic atom plus the profile width. -/
theorem atomicTest_prefix_eq_zero {g : ℝ → ℝ} {w : ℝ}
    (hsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) {M : ℕ}
    (x : ℕ → ℝ) {u : ℝ} (hu : Real.log M + w < u) : atomicTest M x g u = 0 := by
  apply sum_eq_zero
  intro n hn
  have hn1 := (mem_Icc.mp hn).1
  have hnM := (mem_Icc.mp hn).2
  have hl : Real.log n ≤ Real.log M :=
    Real.log_le_log (by exact_mod_cast hn1) (by exact_mod_cast hnM)
  rw [hsupp _ (fun h => by linarith only [hu, hl, h.2]), mul_zero]

/-- The tail starts no earlier than the first omitted logarithmic atom. -/
theorem atomicTest_tail_eq_zero {g : ℝ → ℝ} {w : ℝ}
    (hsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (M N : ℕ)
    (x : ℕ → ℝ) {u : ℝ} (hu : u < Real.log (M + 1 : ℕ)) :
    atomicTest N (atomicTailCoefficients M x) g u = 0 := by
  apply sum_eq_zero
  intro n _
  by_cases hn : M < n
  · have hl : Real.log (M + 1 : ℕ) ≤ Real.log n :=
        Real.log_le_log (by positivity) (by exact_mod_cast (show M + 1 ≤ n by omega))
    rw [hsupp _ (fun h => by linarith only [hu, hl, h.1]), mul_zero]
  · simp only [atomicTailCoefficients, if_neg hn, zero_mul]

/-- A width below the cutoff spacing leaves an ordered gap between prefix and tail. -/
theorem atomicTest_prefix_tail_ordered {g : ℝ → ℝ} {w : ℝ}
    (hsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) {M : ℕ} (hM : 1 ≤ M)
    (hw : w < atomSpacing M) (N : ℕ) (x : ℕ → ℝ) :
    ∃ b : ℝ, (∀ u, b ≤ u → atomicTest M x g u = 0) ∧
      (∀ u, u ≤ b → atomicTest N (atomicTailCoefficients M x) g u = 0) := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hgap : atomSpacing M = Real.log (M + 1 : ℕ) - Real.log M := by
    rw [← Real.log_div (by positivity) hMR.ne']
    unfold atomSpacing
    congr 1
    push_cast
    field_simp [hMR.ne']
  have hlt : Real.log M + w < Real.log (M + 1 : ℕ) := by
    rw [hgap] at hw
    linarith only [hw]
  refine ⟨(Real.log M + w + Real.log (M + 1 : ℕ)) / 2, ?_, ?_⟩
  · intro u hu
    exact atomicTest_prefix_eq_zero hsupp x (by linarith only [hu, hlt])
  · intro u hu
    exact atomicTest_tail_eq_zero hsupp M N x (by linarith only [hu, hlt])

/-- Increasing the arithmetic horizon only adds nonnegative prime-edge squares. -/
theorem poleDefect_prefix_le {M N : ℕ} (hMN : M ≤ N) (x : ℕ → ℝ) :
    poleDefect M x ≤ poleDefect N x := by
  rw [poleDefect_eq_cutoff_add_tail hMN]
  apply le_add_of_nonneg_right
  exact sum_nonneg fun m _ => sum_nonneg fun t _ => by
    split_ifs
    · exact mul_nonneg vonMangoldt_nonneg (sq_nonneg _)
    · exact le_rfl

/-- The full horizon logarithm on the tail is paid by the prime defect at near-unit cost. -/
theorem log_mul_tail_mass_le_defect {M N : ℕ} (hM : 1 ≤ M) (hMN : M ≤ N)
    (x : ℕ → ℝ) {u : ℝ} (hu : 0 < u) :
    Real.log N * (∑ n ∈ Icc 1 N, atomicTailCoefficients M x n ^ 2) ≤
      (1 + 1 / u) * poleDefect N x +
        ((1 + u) * cutoffPrimeCost M N + Real.log N - Real.log M) *
          (∑ n ∈ Icc 1 N, x n ^ 2) := by
  have hMNlog : Real.log M ≤ Real.log N :=
    Real.log_le_log (by exact_mod_cast hM) (by exact_mod_cast hMN)
  have hpoint : ∀ n ∈ Icc 1 N,
      Real.log N * atomicTailCoefficients M x n ^ 2 ≤
        (if M < n then Real.log n * x n ^ 2 else 0) +
          (Real.log N - Real.log M) * x n ^ 2 := by
    intro n _
    rw [atomicTailCoefficients_sq]
    by_cases hn : M < n
    · simp only [if_pos hn]
      have hl : Real.log M ≤ Real.log n :=
        Real.log_le_log (by exact_mod_cast hM) (by exact_mod_cast hn.le)
      nlinarith only [mul_nonneg (sub_nonneg.mpr hl) (sq_nonneg (x n))]
    · simp only [if_neg hn, mul_zero, zero_add]
      exact mul_nonneg (sub_nonneg.mpr hMNlog) (sq_nonneg _)
  have hsum := sum_le_sum hpoint
  simp only [sum_add_distrib, ← mul_sum] at hsum
  change Real.log N * _ ≤ logarithmicTailMass M N x + _ at hsum
  have htail := logarithmicTailMass_le_poleDefect hM hMN x hu
  linarith only [hsum, htail]

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
#print axioms GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.log_mul_tail_mass_le_defect
