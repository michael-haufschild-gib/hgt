import GaloisForLFunctions.HagedornBootstrap.BesselSeries
import GaloisForLFunctions.HagedornBootstrap.EdgeFunction

/-!
# The edges of the strip and the parabolic region of the Cardy kernel

With `t = c'b²/3` the strip `|Im b| < 1/2` is the image of the parabolic region of the `t`-plane
whose vertex is the vacuum `t = −a` (`a = c'/12`) and whose focus is the BTZ threshold `t = 0`.
In the variable `α = −t` the region is `{α : (Re √α)² ≤ a} = {Re α ≤ a − (Im α)²/(4a)}`.

* **Edges.** On `b = x ± i/2`, `α = −c'b²/3` has the root `w = √(c'/3)(1/2 ∓ ix)` with
  `Re w = √(c'/3)/2`, so `(Re √α)² = c'/12 = a` on both edges for every real `x`.
* **Parabola.** If `(Re w)² ≤ a` then `Re(w²) ≤ a − (Im(w²))²/(4a)`; on the boundary parabola
  the points are equidistant from the focus `0` and the directrix `Re α = 2a`.
* **Kernel bound.** The complex modified Bessel function `I₀(z) = (1/π)∫₀^π cosh(z sin θ) dθ`
  obeys `‖I₀(z)‖ ≤ I₀(Re z)` (using `|cosh(x + iy)|² = sinh²x + cos²y ≤ cosh²x`), with the corpus
  `I₀` on the right. On the edges this gives `‖K_α(t)‖ ≤ K_a(t)`: the continued kernel has exactly
  Cardy growth.
-/

noncomputable section

open Real Set MeasureTheory

namespace GaloisForLFunctions.HagedornBootstrap

/-! ### Edges and the parabola -/

/-- The edge root `w = √(c'/3)(1/2 − ix)` squares to `−(c'/3)(x + i/2)²`. -/
theorem edge_root_sq (c' x : ℝ) (hc : 0 ≤ c') :
    ((√(c' / 3) : ℂ) * (1 / 2 - x * Complex.I)) ^ 2 = -((c' / 3 : ℝ) : ℂ) * ((x : ℂ) + Complex.I / 2) ^ 2 := by
  have h := Real.sq_sqrt (show 0 ≤ c' / 3 by positivity)
  have hC : ((√(c' / 3) : ℝ) : ℂ) ^ 2 = ((c' / 3 : ℝ) : ℂ) := by exact_mod_cast h
  rw [mul_pow, hC]
  linear_combination (((c' / 3 : ℝ) : ℂ) * x) * Complex.I * 0 + (((c' / 3 : ℝ) : ℂ)) * (x ^ 2 * 0) +
    (-((c' / 3 : ℝ) : ℂ) * (1 / 4 - x ^ 2) + ((c' / 3 : ℝ) : ℂ) * (1 / 4 - x ^ 2)) * 0 +
    (((c' / 3 : ℝ) : ℂ) * (x ^ 2 * 1)) * 0 + ((c' / 3 : ℝ) : ℂ) * (x ^ 2 - 1 / 4 * 1) * 0 +
    (((c' / 3 : ℝ) : ℂ) * (-(x ^ 2) + 1 / 4 + 1 / 4 - 1 / 4) - ((c' / 3 : ℝ) : ℂ) * (1 / 4 - x ^ 2)) * 0 +
    (((c' / 3 : ℝ) : ℂ) * (x ^ 2) - ((c' / 3 : ℝ) : ℂ) * (x ^ 2)) * Complex.I_sq * 0 +
    (-(((c' / 3 : ℝ) : ℂ)) * x ^ 2 + ((c' / 3 : ℝ) : ℂ) * (1 / 4)) * 0 +
    (((c' / 3 : ℝ) : ℂ) * (x ^ 2) - ((c' / 3 : ℝ) : ℂ) / 4) * Complex.I_sq + (((c' / 3 : ℝ) : ℂ) * x ^ 2 * 0)

/-- **On the edges, `(Re √α)² = a = c'/12`.** -/
theorem edge_root_re_sq (c' x : ℝ) (hc : 0 ≤ c') :
    (((√(c' / 3) : ℂ) * (1 / 2 - x * Complex.I)).re) ^ 2 = c' / 12 := by
  have h := Real.sq_sqrt (show 0 ≤ c' / 3 by positivity)
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_im, Complex.I_re, Complex.I_im]
  norm_num
  rw [mul_pow, h]
  ring

/-- **The parabolic region.** If `(Re w)² ≤ a` then `α = w²` satisfies
`Re α ≤ a − (Im α)²/(4a)`. -/
theorem sq_re_le_parabola {a : ℝ} (ha : 0 < a) {w : ℂ} (hw : w.re ^ 2 ≤ a) :
    (w ^ 2).re ≤ a - (w ^ 2).im ^ 2 / (4 * a) := by
  have hre : (w ^ 2).re = w.re ^ 2 - w.im ^ 2 := by rw [sq, Complex.mul_re]; ring
  have him : (w ^ 2).im = 2 * w.re * w.im := by rw [sq, Complex.mul_im]; ring
  rw [hre, him, le_sub_iff_add_le, ← le_sub_iff_add_le', div_le_iff₀ (by positivity)]
  nlinarith [mul_nonneg (sq_nonneg w.im) (sub_nonneg.mpr hw), sq_nonneg (w.re ^ 2 - a)]

/-- **Focus and directrix.** On the boundary parabola `Re α = a − (Im α)²/(4a)` the distance to
the focus `0` equals the distance `2a − Re α` to the directrix. -/
theorem parabola_focus_directrix {a : ℝ} (ha : 0 < a) {α : ℂ} (h : α.re = a - α.im ^ 2 / (4 * a)) :
    ‖α‖ = 2 * a - α.re := by
  have hnn : 0 ≤ 2 * a - α.re := by
    rw [h]; have : 0 ≤ α.im ^ 2 / (4 * a) := by positivity
    linarith
  rw [← Real.sqrt_sq hnn, Complex.norm_def, Complex.normSq_apply]
  congr 1
  have : α.im ^ 2 = 4 * a * (a - α.re) := by rw [h]; field_simp; ring
  nlinarith [this]

/-- The vacuum `b = ±i/2` sits at `t = −a` and the threshold `b = 0` at `t = 0`. -/
theorem vacuum_t (c' : ℝ) : c' * (Complex.I / 2) ^ 2 / 3 = -((c' / 12 : ℝ) : ℂ) := by
  push_cast
  rw [div_pow, Complex.I_sq]
  ring

/-! ### The complex Bessel bound -/

/-- `|cosh(x + iy)| ≤ cosh x`. -/
theorem norm_cosh_le (z : ℂ) : ‖Complex.cosh z‖ ≤ Real.cosh z.re := by
  have h := normSq_cosh_add_mul_I z.re z.im
  rw [show (z.re : ℂ) + (z.im : ℂ) * Complex.I = z from Complex.re_add_im z] at h
  rw [Complex.norm_def, h, ← Real.sqrt_sq (Real.cosh_pos z.re).le]
  apply Real.sqrt_le_sqrt
  rw [Real.cosh_sq]
  nlinarith [Real.cos_sq_le_one z.im]

/-- The modified Bessel function of order zero for complex arguments, by its integral. -/
def besselI0C (z : ℂ) : ℂ := (1 / π) * ∫ θ in (0 : ℝ)..π, Complex.cosh (z * Real.sin θ)

/-- On real arguments it is the corpus `I₀`. -/
theorem besselI0C_ofReal (u : ℝ) : besselI0C u = (RHTower.besselI0 u : ℂ) := by
  unfold besselI0C RHTower.besselI0
  push_cast
  congr 1
  rw [intervalIntegral.integral_ofReal]
  congr 1; funext θ
  rw [← Complex.ofReal_mul, Complex.ofReal_cosh]

/-- **`‖I₀(z)‖ ≤ I₀(Re z)`.** -/
theorem norm_besselI0C_le (z : ℂ) : ‖besselI0C z‖ ≤ RHTower.besselI0 z.re := by
  unfold besselI0C RHTower.besselI0
  rw [norm_mul, norm_div, norm_one, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc ‖∫ θ in (0 : ℝ)..π, Complex.cosh (z * Real.sin θ)‖
      ≤ ∫ θ in (0 : ℝ)..π, ‖Complex.cosh (z * Real.sin θ)‖ :=
        intervalIntegral.norm_integral_le_integral_norm Real.pi_pos.le
    _ ≤ ∫ θ in (0 : ℝ)..π, Real.cosh (z.re * Real.sin θ) := by
        apply intervalIntegral.integral_mono_on Real.pi_pos.le
        · exact (by fun_prop : Continuous fun θ : ℝ => ‖Complex.cosh (z * Real.sin θ)‖).intervalIntegrable _ _
        · exact (by fun_prop : Continuous fun θ : ℝ => Real.cosh (z.re * Real.sin θ)).intervalIntegrable _ _
        · intro θ _
          have := norm_cosh_le (z * Real.sin θ)
          simpa [Complex.mul_re] using this

/-- **Cardy growth on the edges:** with `w` the edge root, `‖I₀(4π√t · w)‖ ≤ K_a(t)`, `a = c'/12`. -/
theorem norm_edge_kernel_le (c' x t : ℝ) (hc : 0 ≤ c') (ht : 0 ≤ t) :
    ‖besselI0C (4 * π * √t * ((√(c' / 3) : ℂ) * (1 / 2 - x * Complex.I)))‖ ≤ cardyKernel (c' / 12) t := by
  refine (norm_besselI0C_le _).trans (le_of_eq ?_)
  rw [cardyKernel_eq_besselI0 (by positivity) ht]
  congr 1
  have hre : ((√(c' / 3) : ℂ) * (1 / 2 - x * Complex.I)).re = √(c' / 3) / 2 := by
    simp [Complex.mul_re]
  rw [show (4 * π * √t * ((√(c' / 3) : ℂ) * (1 / 2 - x * Complex.I)) : ℂ) =
      ((4 * π * √t : ℝ) : ℂ) * ((√(c' / 3) : ℂ) * (1 / 2 - x * Complex.I)) by push_cast; ring,
    Complex.re_ofReal_mul, hre]
  rw [show c' / 12 * t = (√(c' / 3) / 2) ^ 2 * t by
    rw [div_pow, Real.sq_sqrt (by positivity)]; ring, Real.sqrt_mul (by positivity),
    Real.sqrt_sq (by positivity)]
  ring

end GaloisForLFunctions.HagedornBootstrap
