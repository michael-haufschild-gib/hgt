import GaloisForLFunctions.RHTower.Sieve.FibreWindowBridge

/-!
# The fibre bridge for a weight of arbitrary size

The passage from the fibre mean square to the `L²` norm of the logarithmic window sum is stated in
the corpus for a unit-bounded weight.  The short-interval argument needs it for a weight multiplied
by a prime count, which is not unit bounded, so the bridge is rescaled here: both sides are
quadratic in the weight, and only the rounding term carries the bound explicitly.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- The logarithmic window sum is linear in its coefficients. -/
theorem logWindowSum_div (a : ℕ → ℂ) (s : Finset ℕ) (δ u : ℝ) (B : ℂ) :
    logWindowSum (fun n => a n / B) s δ u = logWindowSum a s δ u / B := by
  rw [logWindowSum, logWindowSum, Finset.sum_div]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [smul_div_assoc]

/-- **The fibre bridge at an arbitrary scale.**  For a weight bounded by `B`, both the fibre mean
square and the window `L²` norm scale like `B²`; only the rounding cost shows the bound. -/
theorem sum_fibreSum_sq_le_integral_scaled {f : ℕ → ℝ} {B : ℝ} (hB : 0 < B)
    (hf : ∀ n, |f n| ≤ B) {x h : ℝ} (hx : 4 ≤ x) (hh0 : 0 ≤ h) (hhx : h ≤ Real.sqrt x) :
    ∑ a ∈ outerBlock x h, (∑ b ∈ innerFibre x h a, f b) ^ (2 : ℕ)
      ≤ 8 * Real.sqrt x * (∫ u : ℝ, ‖logWindowSum (fun n => ((f n : ℝ) : ℂ))
            (fibreIndex x h) (fibreWidth x h) u‖ ^ (2 : ℕ))
        + 102 * B ^ (2 : ℕ) * (Real.sqrt x + 1) := by
  classical
  have hBne : (B : ℝ) ≠ 0 := ne_of_gt hB
  have hBC : ((B : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hBne
  set g : ℕ → ℝ := fun n => f n / B with hg
  have hg1 : ∀ n, |g n| ≤ 1 := by
    intro n
    rw [hg, abs_div, abs_of_pos hB, div_le_one hB]
    exact hf n
  have hbase := sum_fibreSum_sq_le_integral hg1 hx hh0 hhx
  -- both sides scale
  have hcast : ∀ n : ℕ, ((g n : ℝ) : ℂ) = ((f n : ℝ) : ℂ) / ((B : ℝ) : ℂ) := by
    intro n
    rw [hg]
    push_cast
    ring
  have hwindow : ∀ u : ℝ, ‖logWindowSum (fun n => ((g n : ℝ) : ℂ))
      (fibreIndex x h) (fibreWidth x h) u‖ ^ (2 : ℕ)
      = ‖logWindowSum (fun n => ((f n : ℝ) : ℂ)) (fibreIndex x h) (fibreWidth x h) u‖ ^ (2 : ℕ)
          / B ^ (2 : ℕ) := by
    intro u
    have hfun : (fun n => ((g n : ℝ) : ℂ)) = fun n => ((f n : ℝ) : ℂ) / ((B : ℝ) : ℂ) := by
      funext n
      exact hcast n
    rw [hfun, logWindowSum_div, norm_div, div_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hB]
  have hint : (∫ u : ℝ, ‖logWindowSum (fun n => ((g n : ℝ) : ℂ))
        (fibreIndex x h) (fibreWidth x h) u‖ ^ (2 : ℕ))
      = (∫ u : ℝ, ‖logWindowSum (fun n => ((f n : ℝ) : ℂ))
          (fibreIndex x h) (fibreWidth x h) u‖ ^ (2 : ℕ)) / B ^ (2 : ℕ) := by
    rw [← MeasureTheory.integral_div]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hwindow)
  have hlhs : ∑ a ∈ outerBlock x h, (∑ b ∈ innerFibre x h a, g b) ^ (2 : ℕ)
      = (∑ a ∈ outerBlock x h, (∑ b ∈ innerFibre x h a, f b) ^ (2 : ℕ)) / B ^ (2 : ℕ) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hg]
    rw [show (∑ b ∈ innerFibre x h a, f b / B) = (∑ b ∈ innerFibre x h a, f b) / B from
      (Finset.sum_div _ _ _).symm, div_pow]
  rw [hlhs, hint] at hbase
  have hB2 : (0 : ℝ) < B ^ (2 : ℕ) := by positivity
  rw [div_le_iff₀ hB2] at hbase
  have hval : (8 * Real.sqrt x * ((∫ u : ℝ, ‖logWindowSum (fun n => ((f n : ℝ) : ℂ))
        (fibreIndex x h) (fibreWidth x h) u‖ ^ (2 : ℕ)) / B ^ (2 : ℕ)) + 102 * (Real.sqrt x + 1)) * B ^ (2 : ℕ)
      = 8 * Real.sqrt x * (∫ u : ℝ, ‖logWindowSum (fun n => ((f n : ℝ) : ℂ))
          (fibreIndex x h) (fibreWidth x h) u‖ ^ (2 : ℕ))
        + 102 * B ^ (2 : ℕ) * (Real.sqrt x + 1) := by
    field_simp
  rwa [hval] at hbase

end

end RHTower.Sieve
