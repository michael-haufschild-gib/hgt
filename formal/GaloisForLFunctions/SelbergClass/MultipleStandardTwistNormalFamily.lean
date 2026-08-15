import GaloisForLFunctions.SelbergClass.MultipleStandardTwistInitialHolomorphy

/-!
# Initial-domain uniform bounds for damped multiple standard twists

For a ball whose doubled left shift remains in the initial absolute-convergence
domain, the exponentially damped multiple standard twists have one summable
majorant independent of the damping parameter `X`.  This proves a concrete
local boundedness statement for the actual family `D.damped X` on the initial
domain only.

It does not construct the contour-transformed remainders needed on domains
crossing the initial boundary, and therefore does not assert a global normal
family or any meromorphic continuation.
-/

open Complex Filter Set Topology
open scoped BigOperators

namespace GaloisForLFunctions.SelbergClass

/-- Moving inside a radius-`r` ball costs at most the fixed `2r` left shift in
the undamped term.  The auxiliary index product from the existing derivative
estimate is at least one, so it can be discarded here. -/
theorem norm_multipleStandardTwistTerm_le_shift_of_mem_ball {N : ℕ}
    (a : Fin N → ℕ → ℂ) (κ : Fin N → ℝ) (α : ℝ)
    (s₀ z : Fin N → ℂ) (n : Fin N → ℕ+) {r : ℝ}
    (hr : 0 < r) (hz : z ∈ Metric.ball s₀ r) :
    ‖multipleStandardTwistTerm a κ α z n‖ ≤
      ‖multipleStandardTwistTerm a κ α (fun i => s₀ i - (2 * r : ℝ)) n‖ := by
  have hindex : 1 ≤ multipleIndexPower (fun _ : Fin N => r) n := by
    unfold multipleIndexPower
    apply Finset.one_le_prod
    intro i hi
    exact Real.one_le_rpow (by exact_mod_cast (n i).property) hr.le
  calc
    ‖multipleStandardTwistTerm a κ α z n‖ =
        ‖multipleStandardTwistExpTerm a κ α z n‖ := by
          rw [multipleStandardTwistExpTerm_eq_term]
    _ ≤ ‖multipleStandardTwistExpTerm a κ α z n‖ *
          multipleIndexPower (fun _ : Fin N => r) n := by
            calc
              ‖multipleStandardTwistExpTerm a κ α z n‖ =
                  ‖multipleStandardTwistExpTerm a κ α z n‖ * 1 := by ring
              _ ≤ ‖multipleStandardTwistExpTerm a κ α z n‖ *
                  multipleIndexPower (fun _ : Fin N => r) n :=
                mul_le_mul_of_nonneg_left hindex (norm_nonneg _)
    _ ≤ _ := norm_multipleStandardTwistExpTerm_mul_index_le_shift a κ α s₀ z n hz

/-- Exact `X`-uniform majorant on an initial-domain ball.  If the `2r` left
shift of the centre remains coordinatewise to the right of `1`, then every
positive-damping member of the actual family is bounded by the same absolutely
convergent undamped series. -/
theorem MultipleStandardTwistData.norm_damped_le_initial_majorant_on_ball
    {N : ℕ} (D : MultipleStandardTwistData N) (s₀ : Fin N → ℂ) {r X : ℝ}
    (hr : 0 < r) (hshift : ∀ i, 1 < (s₀ i - (2 * r : ℝ)).re) (hX : 0 < X)
    {z : Fin N → ℂ} (hz : z ∈ Metric.ball s₀ r) :
    ‖D.damped X z‖ ≤ ∑' n : Fin N → ℕ+,
      ‖multipleStandardTwistTerm D.coeff D.kappa D.alpha
        (fun i => s₀ i - (2 * r : ℝ)) n‖ := by
  let q : Fin N → ℂ := fun i => s₀ i - (2 * r : ℝ)
  have hmajor : Summable fun n : Fin N → ℕ+ =>
      ‖multipleStandardTwistTerm D.coeff D.kappa D.alpha q n‖ :=
    D.summable_norm_initialTerm q (by simpa [q] using hshift)
  have hterm : ∀ n : Fin N → ℕ+,
      ‖dampedMultipleStandardTwistTerm D.coeff D.kappa D.alpha X z n‖ ≤
        ‖multipleStandardTwistTerm D.coeff D.kappa D.alpha q n‖ := by
    intro n
    calc
      ‖dampedMultipleStandardTwistTerm D.coeff D.kappa D.alpha X z n‖ ≤
          ‖multipleStandardTwistTerm D.coeff D.kappa D.alpha z n‖ :=
        norm_dampedMultipleStandardTwistTerm_le_undamped D.coeff D.kappa
          D.alpha_pos.le hX z n
      _ ≤ ‖multipleStandardTwistTerm D.coeff D.kappa D.alpha q n‖ := by
        simpa only [q] using norm_multipleStandardTwistTerm_le_shift_of_mem_ball
          D.coeff D.kappa D.alpha s₀ z n hr hz
  have hsum : Summable fun n : Fin N → ℕ+ =>
      ‖dampedMultipleStandardTwistTerm D.coeff D.kappa D.alpha X z n‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hmajor
  change ‖∑' n : Fin N → ℕ+,
      dampedMultipleStandardTwistTerm D.coeff D.kappa D.alpha X z n‖ ≤ _
  exact (norm_tsum_le_tsum_norm hsum).trans (hsum.tsum_le_tsum hterm hmajor)

end GaloisForLFunctions.SelbergClass
