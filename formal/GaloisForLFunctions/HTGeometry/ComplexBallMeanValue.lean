import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Basic

/-!
# Mean-value and quotient-difference bounds on complex balls

Two elementary estimates used whenever a holomorphic family has to be controlled uniformly on a
small ball:

* a derivative bound on a closed ball turns into a Lipschitz bound there;
* the difference of two quotients is controlled by the differences of numerators and denominators
  together with a lower bound on the denominators.
-/

namespace HTGeometry

open Metric

/-- **Mean-value bound on a closed ball.**  A complex-differentiable function with derivative
bounded by `C` on a closed ball is `C`-Lipschitz there. -/
theorem norm_sub_le_of_hasDerivAt_ball {f f' : ℂ → ℂ} {c : ℂ} {r C : ℝ}
    (hf : ∀ w : ℂ, HasDerivAt f (f' w) w)
    (hC : ∀ w ∈ closedBall c r, ‖f' w‖ ≤ C)
    {x y : ℂ} (hx : x ∈ closedBall c r) (hy : y ∈ closedBall c r) :
    ‖f y - f x‖ ≤ C * ‖y - x‖ := by
  refine (convex_closedBall c r).norm_image_sub_le_of_norm_fderiv_le
    (fun w _ => (hf w).differentiableAt) (fun w hw => ?_) hx hy
  rw [(hf w).hasFDerivAt.fderiv, ContinuousLinearMap.norm_toSpanSingleton]
  exact hC w hw

/-- **Quotient difference bound.**  If both denominators are at least `m > 0` in norm, the
numerator and denominator at the base point are at most `L`, and both numerator and denominator
move by at most `K`, then the quotients differ by at most `2LK/m²`. -/
theorem norm_div_sub_div_le {A B A₀ B₀ : ℂ} {K L m : ℝ} (hm : 0 < m)
    (hB : m ≤ ‖B‖) (hB₀ : m ≤ ‖B₀‖) (hA₀ : ‖A₀‖ ≤ L) (hB₀L : ‖B₀‖ ≤ L)
    (hA : ‖A - A₀‖ ≤ K) (hBd : ‖B - B₀‖ ≤ K) (hK : 0 ≤ K) :
    ‖A / B - A₀ / B₀‖ ≤ 2 * L * K / m ^ (2 : ℕ) := by
  have hB0 : B ≠ 0 := by
    intro h
    rw [h, norm_zero] at hB
    linarith
  have hB₀0 : B₀ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hB₀
    linarith
  have hL : 0 ≤ L := le_trans (norm_nonneg _) hA₀
  have hkey : A / B - A₀ / B₀ = ((A - A₀) * B₀ - A₀ * (B - B₀)) / (B * B₀) := by
    field_simp
    ring
  rw [hkey, norm_div, norm_mul]
  have hnum : ‖(A - A₀) * B₀ - A₀ * (B - B₀)‖ ≤ 2 * L * K := by
    calc ‖(A - A₀) * B₀ - A₀ * (B - B₀)‖
        ≤ ‖(A - A₀) * B₀‖ + ‖A₀ * (B - B₀)‖ := norm_sub_le _ _
      _ = ‖A - A₀‖ * ‖B₀‖ + ‖A₀‖ * ‖B - B₀‖ := by rw [norm_mul, norm_mul]
      _ ≤ K * L + L * K := by gcongr
      _ = 2 * L * K := by ring
  have hden : m ^ (2 : ℕ) ≤ ‖B‖ * ‖B₀‖ := by
    have := mul_le_mul hB hB₀ (le_of_lt hm) (le_trans (le_of_lt hm) hB)
    nlinarith
  have hden0 : (0 : ℝ) < ‖B‖ * ‖B₀‖ := by nlinarith
  exact div_le_div₀ (by positivity) hnum (by positivity) hden

end HTGeometry
