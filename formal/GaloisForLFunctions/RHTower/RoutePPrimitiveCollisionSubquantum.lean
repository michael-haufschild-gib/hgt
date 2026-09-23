import GaloisForLFunctions.RHTower.RoutePPrimitiveCollisionTraceBudget
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Route P: primitive collision budget lies below one zero quantum

The cubic collision kernel charges a strict-right displacement `0 < a ≤ 1 / 2` at least
`115 / 108`.  This module proves that the complete primitive Euler collision-trace budget is
strictly smaller than that single-zero quantum.

The proof is fully symbolic.  It bounds the integer logarithmic series by its first nonzero term
plus the integral tail, using `2 / 3 < log 2`, and then dominates the prime-depth Euler source by
the corresponding geometric product.  No finite prime cutoff or numerical evaluation enters.

This closes the scalar capacity side of Route P.  The remaining seam is structural: an exact
coefficient-faithful contraction transporting completed primitive source trace to strict-right
zero trace.
-/

open Set MeasureTheory
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Continuous interpolation of `invNatLogSq` used for the integral tail comparison. -/
def routePInvLogSqContinuous (x : ℝ) : ℝ := x⁻¹ / (Real.log x) ^ (2 : ℕ)

/-- The logarithmic inverse-square density decreases from `2` onward. -/
theorem routePInvLogSqContinuous_antitoneOn :
    AntitoneOn routePInvLogSqContinuous (Ici 2) := by
  intro x hx y hy hxy
  change 2 ≤ x at hx
  change 2 ≤ y at hy
  have hxpos : 0 < x := by linarith
  have hypos : 0 < y := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  have hinv : y⁻¹ ≤ x⁻¹ := (inv_le_inv₀ hypos hxpos).2 hxy
  have hlog : Real.log x ≤ Real.log y :=
    Real.strictMonoOn_log.monotoneOn hxpos hypos hxy
  have hsq : (Real.log x) ^ (2 : ℕ) ≤ (Real.log y) ^ (2 : ℕ) :=
    (sq_le_sq₀ hlogx.le hlogy.le).2 hlog
  exact div_le_div₀ (inv_nonneg.mpr hxpos.le) hinv (sq_pos_of_pos hlogx) hsq

/-- Symbolic global estimate for the ambient integer logarithmic series. -/
theorem tsum_invNatLogSq_lt_four :
    (∑' n : ℕ, invNatLogSq n) < 4 := by
  have htail :
      (∑' n : ℕ, routePInvLogSqContinuous (n + 2 + 1 : ℕ)) ≤
        (Real.log 2)⁻¹ := by
    simpa [routePInvLogSqContinuous] using
      routePInvLogSqContinuous_antitoneOn.tsum_comp_add_le_integral 2
        (integrableOn_inv_div_log_sq_Ioi (by norm_num : (1 : ℝ) < 2))
        (fun t ht => by
          change 2 < t at ht
          dsimp [routePInvLogSqContinuous]
          exact div_nonneg (inv_nonneg.mpr (by linarith))
            (sq_nonneg (Real.log t)))
  have htail' :
      (∑' n : ℕ, invNatLogSq (n + 3)) ≤ (Real.log 2)⁻¹ := by
    convert htail using 1
    · apply tsum_congr
      intro n
      rw [invNatLogSq, routePInvLogSqContinuous]
      norm_cast
      ring_nf
  have hsplit := summable_invNatLogSq.sum_add_tsum_nat_add 3
  have hlog : (2 / 3 : ℝ) < Real.log 2 := by
    exact lt_trans (by norm_num) Real.log_two_gt_d9
  have hlogpos : 0 < Real.log 2 := by linarith
  have hlogsq : (2 / 3 : ℝ) ^ (2 : ℕ) < (Real.log 2) ^ (2 : ℕ) :=
    (sq_lt_sq₀ (by norm_num : (0 : ℝ) ≤ 2 / 3) hlogpos.le).2 hlog
  have hfirst : invNatLogSq 2 < 2 := by
    rw [invNatLogSq]
    apply (div_lt_iff₀ (mul_pos (by norm_num) (sq_pos_of_pos hlogpos))).2
    norm_num at hlogsq ⊢
    nlinarith
  have hinvlog : (Real.log 2)⁻¹ < 2 := by
    exact (inv_lt_iff_one_lt_mul₀' hlogpos).2 (by linarith)
  calc
    (∑' n : ℕ, invNatLogSq n) =
        invNatLogSq 2 + ∑' i, invNatLogSq (i + 3) := by
      rw [← hsplit]
      simp [invNatLogSq, Finset.sum_range_succ]
    _ ≤ invNatLogSq 2 + (Real.log 2)⁻¹ := add_le_add (le_refl _) htail'
    _ < 2 + 2 := add_lt_add hfirst hinvlog
    _ = 4 := by norm_num

/-- **P-G175.** Complete primitive Euler collision trace is strictly below the least possible
cubic collision charge of one strict-right zero. -/
theorem routePPrimitiveCollisionCubicTraceBudget_lt_quantum :
    routePPrimitiveCollisionCubicTraceBudget < 115 / 108 := by
  let major : Nat.Primes × ℕ → ℝ := fun pe =>
    (115 / 864 : ℝ) * invNatLogSq pe.1 * (1 / 2 : ℝ) ^ pe.2
  have hmajorNonneg : 0 ≤ major := by
    intro pe
    dsimp only [major]
    rw [invNatLogSq]
    positivity
  have hmajor : Summable major := by
    rw [summable_prod_of_nonneg hmajorNonneg]
    constructor
    · intro p
      exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left
        ((115 / 864 : ℝ) * invNatLogSq p)
    · have hprime := summable_prime_invNatLogSq.mul_left (115 / 432 : ℝ)
      apply hprime.congr
      intro p
      dsimp only [major]
      rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      ring
  have hbudgetMajor :
      routePPrimitiveCollisionCubicTraceBudget ≤ ∑' pe, major pe := by
    rw [routePPrimitiveCollisionCubicTraceBudget]
    exact Summable.tsum_le_tsum xiGammaEulerPrimitiveCubicLogMomentWeight_le
      summable_xiGammaEulerPrimitiveCubicLogMomentWeight hmajor
  have hmajorEq :
      (∑' pe, major pe) =
        (115 / 432 : ℝ) * ∑' p : Nat.Primes, invNatLogSq p := by
    rw [hmajor.tsum_prod, ← tsum_mul_left]
    apply tsum_congr
    intro p
    dsimp only [major]
    rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    ring
  have hprimeLe :
      (∑' p : Nat.Primes, invNatLogSq p) ≤ ∑' n : ℕ, invNatLogSq n := by
    exact summable_prime_invNatLogSq.tsum_le_tsum_of_inj
      Subtype.val Subtype.val_injective
      (fun n _ => by rw [invNatLogSq]; positivity)
      (fun p => le_rfl)
      summable_invNatLogSq
  rw [hmajorEq] at hbudgetMajor
  have hprimeLt : (∑' p : Nat.Primes, invNatLogSq p) < 4 :=
    lt_of_le_of_lt hprimeLe tsum_invNatLogSq_lt_four
  calc
    routePPrimitiveCollisionCubicTraceBudget ≤
        (115 / 432 : ℝ) * ∑' p : Nat.Primes, invNatLogSq p := hbudgetMajor
    _ < (115 / 432 : ℝ) * 4 :=
      mul_lt_mul_of_pos_left hprimeLt (by norm_num)
    _ = 115 / 108 := by norm_num

end

end RHTower
