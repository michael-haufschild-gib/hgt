import GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekBoundedPairwisePositiveMatrixEndpointTomography
import GaloisForLFunctions.HTGeometry.NonnegativeSumCriterionNoGo
import GaloisForLFunctions.HTGeometry.TwoChannelKernelWitnesses

/-!
# Absolutely admissible unbounded PW matrix endpoint tomography

The bounded pairwise-positive matrix theorem leaves unbounded histories as an explicit PW-B
survivor.  Uniform boundedness is unnecessary.  Write `q_j = exp (-(j+1))` and let `a_n` be the
total-grade antidiagonal coefficient of a countable matrix history.  Absolute convergence of
`sum |a_n| q_0^n` makes the anchored coefficients `b_n = a_n q_0^n` bounded.  The exact physical
semigroup law `q_(j+1) = q_0 q_j` converts darkness at the shifted endpoint nodes into the existing
bounded power-series uniqueness problem for `b`.  Hence every antidiagonal vanishes.

For a symmetric pairwise-positive kernel, vanishing even antidiagonals then kills the diagonal and
complete rows successively.  Thus every absolutely endpoint-admissible history in this class is
detected unless it is zero, with no bound on its entries.  The explicit Gram kernel
`K(i,j) = 2^i 2^j` is absolutely admissible and unbounded, proving that this result strictly extends
the bounded theorem rather than repackaging it.

This kills the unbounded-but-absolutely-admissible positive quadratic endpoint-response branch in

`PW endpoint darkness → response uniqueness → source balance → Borel partner balance
  → shared Ward endpoint → RH`.

A surviving PW-B producer must be indefinite, non-absolutely-summable/singular, or leave the
pointwise quadratic endpoint-energy framework.

`[NEW] [PW-B ROUTE-CLASS NO-GO] [UNBOUNDED MATRIX TOMOGRAPHY]
[ABSOLUTE ENDPOINT ADMISSIBILITY] [LEAN-PROVED]`
-/

open Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Exact semigroup law of the physical PW endpoint schedule. -/
theorem schwarzschildParikhWilczekEndpointTomographyNode_succ_eq_zero_mul (j : ℕ) :
    schwarzschildParikhWilczekEndpointTomographyNode (j + 1) =
      schwarzschildParikhWilczekEndpointTomographyNode 0 *
        schwarzschildParikhWilczekEndpointTomographyNode j := by
  simp only [schwarzschildParikhWilczekEndpointTomographyNode]
  rw [← Real.exp_add]
  congr 1
  push_cast
  ring

/-- Absolute endpoint admissibility at the largest physical node.  This controls total-grade
coefficients but imposes no uniform bound on individual matrix entries. -/
def PWMatrixEndpointAbsolutelyAdmissible (K : ℕ → ℕ → ℝ) : Prop :=
  Summable fun n : ℕ =>
    |pwMatrixEndpointAntidiagonalCoefficient K n| *
      schwarzschildParikhWilczekEndpointTomographyNode 0 ^ n

/-- Absolute endpoint admissibility plus darkness at every physical scale kills every total-grade
antidiagonal coefficient, without a bounded-kernel assumption. -/
theorem pwMatrixEndpointAntidiagonalCoefficient_eq_zero_of_absoluteAdmissible_dark
    {K : ℕ → ℕ → ℝ} (hadm : PWMatrixEndpointAbsolutelyAdmissible K)
    (hzero : ∀ j : ℕ, schwarzschildParikhWilczekBoundedMatrixEndpointEnergy K j = 0) :
    ∀ n, pwMatrixEndpointAntidiagonalCoefficient K n = 0 := by
  let q0 := schwarzschildParikhWilczekEndpointTomographyNode 0
  let a := pwMatrixEndpointAntidiagonalCoefficient K
  let b : ℕ → ℝ := fun n => a n * q0 ^ n
  have hq0pos : 0 < q0 := by
    dsimp [q0, schwarzschildParikhWilczekEndpointTomographyNode]
    positivity
  have hbabs : Summable fun n : ℕ => |b n| := by
    simpa [PWMatrixEndpointAbsolutelyAdmissible, b, a, q0, abs_mul,
      abs_pow, abs_of_pos hq0pos] using hadm
  have hb : Summable b := summable_norm_iff.mp (by
    simpa [Real.norm_eq_abs] using hbabs)
  let C := ∑' n : ℕ, |b n|
  have hbound : ∀ n, |b n| ≤ C := by
    intro n
    exact GaloisForLFunctions.term_le_tsum_of_nonneg hbabs (fun m => abs_nonneg (b m)) n
  have hqpos (j : ℕ) : 0 < schwarzschildParikhWilczekEndpointTomographyNode j := by
    rw [schwarzschildParikhWilczekEndpointTomographyNode]
    positivity
  have hqlt (j : ℕ) :
      |schwarzschildParikhWilczekEndpointTomographyNode j| < 1 := by
    rw [abs_of_pos (hqpos j), schwarzschildParikhWilczekEndpointTomographyNode,
      Real.exp_lt_one_iff]
    have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  have hrawzero (j : ℕ) :
      ∑' n : ℕ, a n *
        schwarzschildParikhWilczekEndpointTomographyNode (j + 1) ^ n = 0 := by
    have h := hzero (j + 1)
    rw [schwarzschildParikhWilczekBoundedMatrixEndpointEnergy] at h
    let q := schwarzschildParikhWilczekEndpointTomographyNode (j + 1)
    have hfac :
        (∑' n : ℕ, a n * q ^ (n + 2)) =
          q ^ 2 * ∑' n : ℕ, a n * q ^ n := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro n
      rw [pow_add]
      ring
    rw [hfac] at h
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero 2 (hqpos (j + 1)).ne')
  have hbzeroAt (j : ℕ) :
      ∑' n : ℕ, b n * schwarzschildParikhWilczekEndpointTomographyNode j ^ n = 0 := by
    rw [← hrawzero j]
    apply tsum_congr
    intro n
    rw [schwarzschildParikhWilczekEndpointTomographyNode_succ_eq_zero_mul]
    dsimp [b, q0]
    rw [mul_pow]
    ring
  have hbzero : ∀ n, b n = 0 :=
    boundedPowerSeries_coeff_eq_zero_of_zeroSequence hbound hqpos hqlt
      tendsto_schwarzschildParikhWilczekEndpointTomographyNode_zero hbzeroAt
  intro n
  have hn := hbzero n
  dsimp [b, a] at hn
  exact (mul_eq_zero.mp hn).resolve_right (pow_ne_zero n hq0pos.ne')

/-- A symmetric pairwise-positive, absolutely endpoint-admissible matrix dark at every physical
scale is the zero matrix.  Individual entries may be unbounded. -/
theorem symmetric_pairwisePositive_kernel_eq_zero_of_absoluteAdmissible_endpointEnergy_zero
    {K : ℕ → ℕ → ℝ} (hadm : PWMatrixEndpointAbsolutelyAdmissible K)
    (hSymm : ∀ i j, K i j = K j i)
    (hPositive : GaloisForLFunctions.HTGeometry.PairwiseNonnegativeKernel K)
    (hzero : ∀ j : ℕ, schwarzschildParikhWilczekBoundedMatrixEndpointEnergy K j = 0) :
    K = 0 := by
  have ha : ∀ n, pwMatrixEndpointAntidiagonalCoefficient K n = 0 :=
    pwMatrixEndpointAntidiagonalCoefficient_eq_zero_of_absoluteAdmissible_dark hadm hzero
  have hrows : ∀ m i, K m i = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      have hsum := ha (2 * m)
      rw [pwMatrixEndpointAntidiagonalCoefficient] at hsum
      have hsingle :
          (∑ i ∈ Finset.range (2 * m + 1), K i (2 * m - i)) = K m m := by
        calc
          (∑ i ∈ Finset.range (2 * m + 1), K i (2 * m - i)) =
              K m (2 * m - m) := by
            apply Finset.sum_eq_single m
            · intro i hi him
              simp only [Finset.mem_range] at hi
              by_cases hlt : i < m
              · exact ih i hlt (2 * m - i)
              · have hgt : m < i :=
                  lt_of_le_of_ne (Nat.le_of_not_gt hlt) (Ne.symm him)
                have hsub : 2 * m - i < m := by omega
                rw [hSymm]
                exact ih (2 * m - i) hsub i
            · intro hnot
              exfalso
              apply hnot
              simp
              omega
          _ = K m m := by
            have hsub : 2 * m - m = m := by omega
            rw [hsub]
      rw [hsingle] at hsum
      exact
        GaloisForLFunctions.HTGeometry.pairwiseNonnegativeKernel_row_eq_zero_of_symmetric_of_diagonal_eq_zero
          hPositive hSymm hsum
  funext i j
  exact hrows i j

/-- Closed proposition for the unbounded-but-absolutely-admissible positive PW endpoint branch. -/
def SchwarzschildParikhWilczekAbsolutelyAdmissiblePairwisePositiveEndpointDarkRouteKilled :
    Prop :=
  ∀ K : ℕ → ℕ → ℝ,
    PWMatrixEndpointAbsolutelyAdmissible K →
    (∀ i j, K i j = K j i) →
    GaloisForLFunctions.HTGeometry.PairwiseNonnegativeKernel K →
    K ≠ 0 →
    ∃ j : ℕ, schwarzschildParikhWilczekBoundedMatrixEndpointEnergy K j ≠ 0

/-- **PW-B route-class kill.** Every nonzero symmetric pairwise-positive countable matrix with an
absolutely admissible endpoint response is detected at a physical scale, even when its entries are
unbounded. -/
theorem schwarzschildParikhWilczekAbsolutelyAdmissiblePairwisePositiveEndpointDarkRouteKilled :
    SchwarzschildParikhWilczekAbsolutelyAdmissiblePairwisePositiveEndpointDarkRouteKilled := by
  intro K hadm hSymm hPositive hKne
  by_contra h
  have hall : ∀ j : ℕ, schwarzschildParikhWilczekBoundedMatrixEndpointEnergy K j = 0 := by
    intro j
    by_contra hj
    exact h ⟨j, hj⟩
  exact hKne
    (symmetric_pairwisePositive_kernel_eq_zero_of_absoluteAdmissible_endpointEnergy_zero
      hadm hSymm hPositive hall)

/-! ## Strict unbounded witness -/

/-- Explicit unbounded Gram history showing that the new admissible class strictly exceeds bounded
matrix histories. -/
def pwExponentialGramKernel (i j : ℕ) : ℝ :=
  (2 : ℝ) ^ i * (2 : ℝ) ^ j

theorem pwExponentialGramKernel_symmetric (i j : ℕ) :
    pwExponentialGramKernel i j = pwExponentialGramKernel j i := by
  simp [pwExponentialGramKernel, mul_comm]

theorem pwExponentialGramKernel_pairwisePositive :
    GaloisForLFunctions.HTGeometry.PairwiseNonnegativeKernel pwExponentialGramKernel := by
  change GaloisForLFunctions.HTGeometry.PairwiseNonnegativeKernel
    (fun i j : ℕ => (2 : ℝ) ^ i * (2 : ℝ) ^ j)
  exact GaloisForLFunctions.HTGeometry.pairwiseNonnegativeKernel_gram
    (fun i : ℕ => (2 : ℝ) ^ i)

/-- The witness has no uniform entry bound. -/
theorem pwExponentialGramKernel_not_uniformlyBounded :
    ¬ ∃ B : ℝ, ∀ i j, |pwExponentialGramKernel i j| ≤ B := by
  rintro ⟨B, hB⟩
  obtain ⟨k, hk⟩ := exists_nat_gt B
  have hpow : (k : ℝ) < (2 : ℝ) ^ k := by
    exact_mod_cast (Nat.lt_two_pow_self : k < 2 ^ k)
  have h := hB k 0
  simp [pwExponentialGramKernel] at h
  exact (not_lt_of_ge h) (hk.trans hpow)

/-- Every antidiagonal of the exponential Gram history has an exact closed form. -/
theorem pwMatrixEndpointAntidiagonalCoefficient_exponentialGram (n : ℕ) :
    pwMatrixEndpointAntidiagonalCoefficient pwExponentialGramKernel n =
      ((n : ℝ) + 1) * (2 : ℝ) ^ n := by
  rw [pwMatrixEndpointAntidiagonalCoefficient]
  calc
    (∑ i ∈ Finset.range (n + 1), pwExponentialGramKernel i (n - i)) =
        ∑ _i ∈ Finset.range (n + 1), (2 : ℝ) ^ n := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Finset.mem_range] at hi
      have hin : i ≤ n := by omega
      rw [pwExponentialGramKernel, ← pow_add, Nat.add_sub_of_le hin]
    _ = ((n : ℝ) + 1) * (2 : ℝ) ^ n := by simp [Nat.cast_add]

/-- The explicit unbounded witness is absolutely endpoint-admissible because its anchored
antidiagonals are `(n+1) (2q₀)^n` and `2q₀ < 1`. -/
theorem pwExponentialGramKernel_absolutelyAdmissible :
    PWMatrixEndpointAbsolutelyAdmissible pwExponentialGramKernel := by
  let r := pwMatrixEndpointRescaledNode 0
  have hr0 : 0 < r := pwMatrixEndpointRescaledNode_pos 0
  have hr1 : |r| < 1 := abs_pwMatrixEndpointRescaledNode_lt_one 0
  have hnat : Summable fun n : ℕ => (n : ℝ) * r ^ n := by
    have h := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 (by
      simpa [Real.norm_eq_abs] using hr1)
    simpa using h
  have hgeom : Summable fun n : ℕ => r ^ n :=
    summable_geometric_of_norm_lt_one (by simpa [Real.norm_eq_abs] using hr1)
  have hsum : Summable fun n : ℕ => ((n : ℝ) + 1) * r ^ n := by
    refine (hnat.add hgeom).congr fun n => ?_
    ring
  rw [PWMatrixEndpointAbsolutelyAdmissible]
  refine hsum.congr fun n => ?_
  rw [pwMatrixEndpointAntidiagonalCoefficient_exponentialGram]
  have hn : 0 ≤ (n : ℝ) + 1 := by positivity
  have htwo : 0 ≤ (2 : ℝ) ^ n := pow_nonneg (by norm_num) n
  rw [abs_of_nonneg (mul_nonneg hn htwo)]
  dsimp [r, pwMatrixEndpointRescaledNode]
  rw [mul_pow]
  ring

end

end RHTower
