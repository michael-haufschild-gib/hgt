import GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekAbsolutelyAdmissibleMatrixEndpointTomography

/-!
# Sequentially convergent PW matrix endpoint tomography

Absolute endpoint admissibility is unnecessary for the positive countable PW-B matrix branch.
Use natural ordered partial sums, so conditional convergence is not silently replaced by Lean's
unconditional `tsum`. If the endpoint response converges to zero at every physical node, its
convergence at the largest node bounds the anchored antidiagonal coefficients. The exact node
semigroup transports every remaining zero limit into one bounded power series whose zero set
accumulates at the interior point zero. Hence every antidiagonal coefficient vanishes.

For a symmetric pairwise-positive matrix, the even antidiagonals then kill each diagonal and
complete row. Thus every nonzero matrix in this class is detected at some physical scale. This
kills the conditionally convergent/non-absolutely-admissible positive endpoint-response branch in

`PW endpoint darkness -> response uniqueness -> source balance -> Borel partner balance
  -> shared Ward endpoint -> RH`.

The sharp survivors are responses with no natural ordered zero limit at some physical scale,
indefinite matrices, or nonlinear/nonpointwise/distributional source laws.

`[NEW] [PW-B ROUTE-CLASS NO-GO] [SEQUENTIAL TOMOGRAPHY]
[CONDITIONAL CONVERGENCE] [LEAN-PROVED]`
-/

open Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Natural-order endpoint darkness at every prescribed physical PW scale. Unlike `tsum`, this
definition permits conditionally convergent series. -/
def PWMatrixEndpointSequentiallyDark (K : ℕ → ℕ → ℝ) : Prop :=
  ∀ j : ℕ, Tendsto
    (fun N : ℕ => ∑ n ∈ Finset.range N,
      pwMatrixEndpointAntidiagonalCoefficient K n *
        schwarzschildParikhWilczekEndpointTomographyNode j ^ (n + 2))
    atTop (𝓝 0)

/-- Sequential endpoint darkness kills every total-grade antidiagonal coefficient. Convergence at
the largest node supplies the coefficient bound needed for power-series uniqueness; no absolute
summability or entrywise matrix bound is assumed. -/
theorem pwMatrixEndpointAntidiagonalCoefficient_eq_zero_of_sequentiallyDark
    {K : ℕ → ℕ → ℝ} (hdark : PWMatrixEndpointSequentiallyDark K) :
    ∀ n, pwMatrixEndpointAntidiagonalCoefficient K n = 0 := by
  let q0 := schwarzschildParikhWilczekEndpointTomographyNode 0
  let a := pwMatrixEndpointAntidiagonalCoefficient K
  let b : ℕ → ℝ := fun n => a n * q0 ^ n
  let S : ℕ → ℝ := fun N => ∑ n ∈ Finset.range N, a n * q0 ^ (n + 2)
  have hS : Tendsto S atTop (𝓝 0) := by
    simpa [PWMatrixEndpointSequentiallyDark, S, a, q0] using hdark 0
  obtain ⟨C, hC⟩ := (isBounded_iff_forall_norm_le).1 hS.cauchySeq.isBounded_range
  have hSC : ∀ N, |S N| ≤ C := by
    intro N
    simpa only [Real.norm_eq_abs] using hC (S N) ⟨N, rfl⟩
  have hC0 : 0 ≤ C := (abs_nonneg (S 0)).trans (hSC 0)
  have hq0pos : 0 < q0 := by
    dsimp [q0, schwarzschildParikhWilczekEndpointTomographyNode]
    positivity
  have hterm : ∀ n, |a n * q0 ^ (n + 2)| ≤ 2 * C := by
    intro n
    have hdiff : a n * q0 ^ (n + 2) = S (n + 1) - S n := by
      dsimp only [S]
      rw [Finset.sum_range_succ]
      ring
    rw [hdiff]
    exact (abs_sub _ _).trans (by linarith [hSC (n + 1), hSC n])
  have hb : ∀ n, |b n| ≤ 2 * C / q0 ^ (2 : ℕ) := by
    intro n
    have hq02 : 0 < q0 ^ (2 : ℕ) := sq_pos_of_pos hq0pos
    have heq : |b n| = |a n * q0 ^ (n + 2)| / q0 ^ (2 : ℕ) := by
      dsimp only [b]
      rw [abs_mul, abs_pow, abs_of_pos hq0pos,
        abs_mul, abs_pow, abs_of_pos hq0pos, pow_add]
      field_simp [hq02.ne']
    rw [heq]
    exact div_le_div_of_nonneg_right (hterm n) hq02.le
  have hqpos (j : ℕ) : 0 < schwarzschildParikhWilczekEndpointTomographyNode j := by
    rw [schwarzschildParikhWilczekEndpointTomographyNode]
    positivity
  have hqlt (j : ℕ) :
      |schwarzschildParikhWilczekEndpointTomographyNode j| < 1 := by
    rw [abs_of_pos (hqpos j), schwarzschildParikhWilczekEndpointTomographyNode,
      Real.exp_lt_one_iff]
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith
  have hbzeroAt (j : ℕ) :
      ∑' n : ℕ, b n * schwarzschildParikhWilczekEndpointTomographyNode j ^ n = 0 := by
    let q := schwarzschildParikhWilczekEndpointTomographyNode j
    let qnext := schwarzschildParikhWilczekEndpointTomographyNode (j + 1)
    have hsum : Summable fun n : ℕ => b n * q ^ n :=
      GaloisForLFunctions.HTGeometry.summable_of_bounded_coeff hb (by
        simpa [q] using hqlt j)
    have hlim := hsum.hasSum.tendsto_sum_nat
    have hscaled := hlim.const_mul (qnext ^ (2 : ℕ))
    have hphysical : Tendsto
        (fun N : ℕ => qnext ^ (2 : ℕ) * ∑ n ∈ Finset.range N, b n * q ^ n)
        atTop (𝓝 0) := by
      have hz := hdark (j + 1)
      have heq : (fun N : ℕ => qnext ^ (2 : ℕ) * ∑ n ∈ Finset.range N, b n * q ^ n) =
          (fun N : ℕ => ∑ n ∈ Finset.range N,
            a n * qnext ^ (n + 2)) := by
        funext N
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _hn
        have hsemigroup : qnext = q0 * q := by
          simpa [qnext, q, q0] using
            schwarzschildParikhWilczekEndpointTomographyNode_succ_eq_zero_mul j
        rw [hsemigroup]
        dsimp [b]
        simp only [mul_pow]
        ring
      rw [heq]
      simpa [PWMatrixEndpointSequentiallyDark, a, qnext] using hz
    have hlimitEq : qnext ^ (2 : ℕ) * (∑' n : ℕ, b n * q ^ n) = 0 :=
      tendsto_nhds_unique hscaled hphysical
    exact (mul_eq_zero.mp hlimitEq).resolve_left
      (pow_ne_zero 2 (hqpos (j + 1)).ne')
  have hbzero : ∀ n, b n = 0 :=
    boundedPowerSeries_coeff_eq_zero_of_zeroSequence hb hqpos hqlt
      tendsto_schwarzschildParikhWilczekEndpointTomographyNode_zero hbzeroAt
  intro n
  have hn := hbzero n
  dsimp [b, a] at hn
  exact (mul_eq_zero.mp hn).resolve_right (pow_ne_zero n hq0pos.ne')

/-- Complete classification of the conditionally convergent positive branch: a symmetric
pairwise-positive matrix dark in natural order at every physical endpoint is the zero matrix. -/
theorem symmetric_pairwisePositive_kernel_eq_zero_of_sequentiallyDark
    {K : ℕ → ℕ → ℝ}
    (hSymm : ∀ i j, K i j = K j i)
    (hPositive : GaloisForLFunctions.HTGeometry.PairwiseNonnegativeKernel K)
    (hdark : PWMatrixEndpointSequentiallyDark K) :
    K = 0 := by
  have ha : ∀ n, pwMatrixEndpointAntidiagonalCoefficient K n = 0 :=
    pwMatrixEndpointAntidiagonalCoefficient_eq_zero_of_sequentiallyDark hdark
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

/-- Closed route class: every nonzero symmetric pairwise-positive countable PW matrix is detected
by failure of natural-order zero convergence at some physical endpoint scale. -/
def SchwarzschildParikhWilczekSequentiallyAdmissiblePairwisePositiveEndpointDarkRouteKilled :
    Prop :=
  ∀ K : ℕ → ℕ → ℝ,
    (∀ i j, K i j = K j i) →
    GaloisForLFunctions.HTGeometry.PairwiseNonnegativeKernel K →
    K ≠ 0 →
    ∃ j : ℕ, ¬ Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N,
        pwMatrixEndpointAntidiagonalCoefficient K n *
          schwarzschildParikhWilczekEndpointTomographyNode j ^ (n + 2))
      atTop (𝓝 0)

/-- **PW-B route-class kill.** Conditional natural-order convergence cannot rescue a nonzero
positive countable matrix from all-scale physical endpoint tomography. -/
theorem schwarzschildParikhWilczekSequentiallyAdmissiblePairwisePositiveEndpointDarkRouteKilled :
    SchwarzschildParikhWilczekSequentiallyAdmissiblePairwisePositiveEndpointDarkRouteKilled := by
  intro K hSymm hPositive hKne
  by_contra h
  push Not at h
  exact hKne (symmetric_pairwisePositive_kernel_eq_zero_of_sequentiallyDark
    hSymm hPositive h)

end

end RHTower
