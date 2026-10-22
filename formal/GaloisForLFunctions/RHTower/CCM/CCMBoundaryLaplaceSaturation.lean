import Mathlib

/-!
# Universal saturation of the polar–Euler frame level by a fixed boundary profile

Three exact mechanisms of the card are formalized.

*The polar two-edge expansion.*  `2|e^{a/2}F_- + e^{-a/2}F_+|² = 2 e^{a}|F_-|² + O_f(1)` is an exact
algebraic identity with a remainder bounded uniformly in `a ≥ 0`.  This is `(5)`.

*The Laplace–Fubini identity.*  `∫ e^{-r/2} (f ⋆ f)(r) dr = (∫ e^{-s/2} f(s) ds)²`, i.e. the exact
last equality of `(9)`: weighting the autocorrelation by the exponential character factors it into
the square of the weighted integral.

*Frame saturation.*  If the restricted Weil value is `o(e^a)` and the scalar level is `4e^a(1+o(1))`,
then the relative Rayleigh ratio tends to `1` — equations `(13)`–`(16)`.

The prime number theorem, the weak convergence `(8)`, the Gamma bound `(12)` and the analysis map
`B_a` are cited parents and stay outside the Lean statement.
-/

open Filter Topology MeasureTheory

noncomputable section

namespace GaloisForLFunctions.RHTower

/-! ## The polar two-edge expansion -/

/-- **Equation (5), exact expansion.** -/
theorem polar_two_edge_expansion (a A B : ℝ) :
    2 * (Real.exp (a / 2) * A + Real.exp (-(a / 2)) * B) ^ (2 : ℕ)
      = 2 * Real.exp a * A ^ (2 : ℕ) + 4 * A * B + 2 * Real.exp (-a) * B ^ (2 : ℕ) := by
  have h1 : Real.exp (a / 2) * Real.exp (a / 2) = Real.exp a := by
    rw [← Real.exp_add]
    ring_nf
  have h2 : Real.exp (a / 2) * Real.exp (-(a / 2)) = 1 := by
    rw [← Real.exp_add]
    simp
  have h3 : Real.exp (-(a / 2)) * Real.exp (-(a / 2)) = Real.exp (-a) := by
    rw [← Real.exp_add]
    ring_nf
  calc 2 * (Real.exp (a / 2) * A + Real.exp (-(a / 2)) * B) ^ (2 : ℕ)
      = 2 * (Real.exp (a / 2) * Real.exp (a / 2)) * A ^ (2 : ℕ)
        + 4 * (Real.exp (a / 2) * Real.exp (-(a / 2))) * A * B
        + 2 * (Real.exp (-(a / 2)) * Real.exp (-(a / 2))) * B ^ (2 : ℕ) := by ring
    _ = 2 * Real.exp a * A ^ (2 : ℕ) + 4 * A * B + 2 * Real.exp (-a) * B ^ (2 : ℕ) := by
        rw [h1, h2, h3]
        ring

/-- **Equation (5), remainder bound.**  The remainder is bounded uniformly in the aperture. -/
theorem polar_two_edge_remainder_le {a : ℝ} (ha : 0 ≤ a) (A B : ℝ) :
    |2 * (Real.exp (a / 2) * A + Real.exp (-(a / 2)) * B) ^ (2 : ℕ) - 2 * Real.exp a * A ^ (2 : ℕ)|
      ≤ 4 * |A| * |B| + 2 * B ^ (2 : ℕ) := by
  rw [polar_two_edge_expansion]
  have hexp : Real.exp (-a) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  have hexppos : 0 < Real.exp (-a) := Real.exp_pos _
  have hsimp : 2 * Real.exp a * A ^ (2 : ℕ) + 4 * A * B + 2 * Real.exp (-a) * B ^ (2 : ℕ)
      - 2 * Real.exp a * A ^ (2 : ℕ) = 4 * A * B + 2 * Real.exp (-a) * B ^ (2 : ℕ) := by ring
  rw [hsimp]
  have h1 : |4 * A * B + 2 * Real.exp (-a) * B ^ (2 : ℕ)|
      ≤ |4 * A * B| + |2 * Real.exp (-a) * B ^ (2 : ℕ)| := by
    simpa only [Real.norm_eq_abs] using norm_add_le (4 * A * B) (2 * Real.exp (-a) * B ^ (2 : ℕ))
  have h2 : |4 * A * B| = 4 * |A| * |B| := by
    rw [abs_mul, abs_mul]
    norm_num
  have h3 : |2 * Real.exp (-a) * B ^ (2 : ℕ)| ≤ 2 * B ^ (2 : ℕ) := by
    rw [abs_of_nonneg (by positivity)]
    nlinarith [sq_nonneg B]
  linarith

/-! ## The Laplace–Fubini identity -/

/-- Pulling the exponential character inside the autocorrelation integral. -/
theorem expWeight_autocorrelation_eq (f : ℝ → ℝ) (r : ℝ) :
    Real.exp (-(r / 2)) * (∫ t, f t * f (r - t))
      = ∫ t, (Real.exp (-(t / 2)) * f t) * (Real.exp (-((r - t) / 2)) * f (r - t)) := by
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  have hexp : Real.exp (-(t / 2)) * Real.exp (-((r - t) / 2)) = Real.exp (-(r / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc Real.exp (-(r / 2)) * (f t * f (r - t))
      = (Real.exp (-(t / 2)) * Real.exp (-((r - t) / 2))) * (f t * f (r - t)) := by rw [hexp]
    _ = (Real.exp (-(t / 2)) * f t) * (Real.exp (-((r - t) / 2)) * f (r - t)) := by ring

/-- **Equation (9), last equality.**  The exponentially weighted autocorrelation integrates to the
square of the weighted integral. -/
theorem integral_expWeight_autocorrelation {f : ℝ → ℝ}
    (hg : Integrable (fun s => Real.exp (-(s / 2)) * f s)) :
    (∫ r, Real.exp (-(r / 2)) * (∫ t, f t * f (r - t)))
      = (∫ s, Real.exp (-(s / 2)) * f s) * (∫ s, Real.exp (-(s / 2)) * f s) := by
  have hconv := MeasureTheory.integral_convolution
    (ContinuousLinearMap.mul ℝ ℝ) hg hg
  have hrw : (∫ r, Real.exp (-(r / 2)) * (∫ t, f t * f (r - t)))
      = ∫ r, MeasureTheory.convolution (fun s => Real.exp (-(s / 2)) * f s)
          (fun s => Real.exp (-(s / 2)) * f s) (ContinuousLinearMap.mul ℝ ℝ) volume r := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
    show Real.exp (-(r / 2)) * (∫ t, f t * f (r - t)) = _
    rw [expWeight_autocorrelation_eq f r]
    rfl
  rw [hrw, hconv]
  rfl

/-! ## Frame saturation -/

/-- **Equations (13)–(16).**  A restricted Weil value of size `o(e^a)` against a scalar level
`4 e^a (1+o(1))` gives relative Rayleigh ratio tending to `1`: every fixed boundary profile
saturates the frame level. -/
theorem tendsto_frame_saturation {QW mu Bsq : ℝ → ℝ} {N : ℝ} (hN : 0 < N)
    (hB : ∀ a, Bsq a = QW a + mu a * (2 * N))
    (hQ : Tendsto (fun a => QW a / Real.exp a) atTop (nhds 0))
    (hmu : Tendsto (fun a => mu a / Real.exp a) atTop (nhds 4)) :
    Tendsto (fun a => Bsq a / (mu a * (2 * N))) atTop (nhds 1) := by
  have hden : Tendsto (fun a => (mu a / Real.exp a) * (2 * N)) atTop (nhds (4 * (2 * N))) :=
    hmu.mul_const _
  have hzero : Tendsto (fun a => (QW a / Real.exp a) / ((mu a / Real.exp a) * (2 * N)))
      atTop (nhds (0 / (4 * (2 * N)))) := hQ.div hden (by positivity)
  rw [zero_div] at hzero
  have hone := hzero.add_const 1
  rw [zero_add] at hone
  refine hone.congr' ?_
  have hmupos : ∀ᶠ a : ℝ in atTop, 0 < mu a / Real.exp a := by
    have := hmu.eventually (lt_mem_nhds (show (2 : ℝ) < 4 by norm_num))
    filter_upwards [this] with a ha
    linarith
  filter_upwards [hmupos] with a ha
  have hexppos : (0 : ℝ) < Real.exp a := Real.exp_pos a
  have hmune : mu a ≠ 0 := by
    intro h0
    rw [h0, zero_div] at ha
    exact absurd ha (lt_irrefl 0)
  rw [hB a]
  field_simp

end GaloisForLFunctions.RHTower

end
