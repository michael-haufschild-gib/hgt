/-
# RescaleTannery — the doc 25 (E3) uniform-convergence conclusion (task #143 / #135)

Doc 25 (25-tracking-clearance.md) (E3) `[PROVED HERE]`: with `g = Σ_j c_j z^j` entire (so
`Σ_j ‖c_j‖ρ^j < ∞` on every disc), the rescaled sections `Ã_d(z) = Σ_j φ_d(j) c_j z^j`
converge to `g` — because `φ_d(j) ∈ [0,1]` and `φ_d(j) → 1` pointwise dominate against the
summable coefficient bound. Flat grading: a direct application of Tannery's theorem
(`tendsto_tsum_of_dominated_convergence`); nothing new.

* `rescaledSection_tendsto` — **(E3) pointwise**: for `‖z‖ ≤ ρ`, `Ã_d(z) → g(z)`.
* `rescale_defect_tendsto_zero` — **(E3) uniform bound → 0**: the majorant of the sup-error,
  `Σ_j (1 − φ_d(j))‖c_j‖ρ^j`, tends to `0`; since `sup_{‖z‖≤ρ}‖Ã_d − g‖` is bounded by it
  (each term `‖(φ_d(j)−1)c_j z^j‖ ≤ (1−φ_d(j))‖c_j‖ρ^j`), the convergence is uniform on the disc.

The domination hypothesis `Summable (fun j => ‖c j‖ * ρ^j)` is exactly the entire-function
condition on `g`; the factor hypotheses `hφ01`/`hφlim` are supplied by `RescaleLimit`
(`phi_product_le_one`, `phi_product_tendsto_one`) with `φ d j = ∏_{i<j}(1 − i/d)`.
-/
import Mathlib

noncomputable section

namespace RHTower

open Filter Topology

/-- **(E3) pointwise convergence** (doc 25): for a coefficient sequence `c` with the
entire-function domination `Σ ‖c_j‖ρ^j < ∞`, and rescaling factors `φ_d(j) ∈ [0,1]` with
`φ_d(j) → 1`, the rescaled section `Ã_d(z) = Σ_j φ_d(j) c_j z^j` converges to `g(z) = Σ_j c_j z^j`
at every `‖z‖ ≤ ρ`. Tannery's theorem with bound `‖c_j‖ρ^j`. -/
theorem rescaledSection_tendsto {c : ℕ → ℂ} {z : ℂ} {ρ : ℝ} (hz : ‖z‖ ≤ ρ)
    (hsum : Summable (fun j => ‖c j‖ * ρ ^ j))
    {φ : ℕ → ℕ → ℝ} (hφ01 : ∀ d j, 0 ≤ φ d j ∧ φ d j ≤ 1)
    (hφlim : ∀ j, Tendsto (fun d => φ d j) atTop (nhds 1)) :
    Tendsto (fun d => ∑' j, (φ d j : ℂ) * c j * z ^ j) atTop
      (nhds (∑' j, c j * z ^ j)) := by
  have hρ : 0 ≤ ρ := le_trans (norm_nonneg z) hz
  apply tendsto_tsum_of_dominated_convergence hsum
  · intro j
    have hcast : Tendsto (fun d => (φ d j : ℂ)) atTop (nhds 1) := by
      have := (Complex.continuous_ofReal.tendsto 1).comp (hφlim j)
      simpa using this
    have := hcast.mul_const (c j * z ^ j)
    simpa [mul_assoc] using this
  · filter_upwards with d
    intro j
    have hz' : ‖z ^ j‖ ≤ ρ ^ j := by
      rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg z) hz j
    have hφabs : |φ d j| ≤ 1 := abs_le.mpr ⟨by linarith [(hφ01 d j).1], (hφ01 d j).2⟩
    have hnorm : ‖(φ d j : ℂ) * c j * z ^ j‖ = |φ d j| * ‖c j‖ * ‖z ^ j‖ := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [hnorm]
    calc |φ d j| * ‖c j‖ * ‖z ^ j‖
        ≤ 1 * ‖c j‖ * ρ ^ j := by gcongr
      _ = ‖c j‖ * ρ ^ j := by ring

/-- **(E3) uniform bound → 0** (doc 25): the majorant `Σ_j (1 − φ_d(j))‖c_j‖ρ^j` of the
sup-error on `‖z‖ ≤ ρ` tends to `0`. Each summand `(1 − φ_d(j))‖c_j‖ρ^j → 0` and is dominated
by the summable `‖c_j‖ρ^j`; Tannery with limit `0`. -/
theorem rescale_defect_tendsto_zero {c : ℕ → ℂ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hsum : Summable (fun j => ‖c j‖ * ρ ^ j))
    {φ : ℕ → ℕ → ℝ} (hφ01 : ∀ d j, 0 ≤ φ d j ∧ φ d j ≤ 1)
    (hφlim : ∀ j, Tendsto (fun d => φ d j) atTop (nhds 1)) :
    Tendsto (fun d => ∑' j, (1 - φ d j) * (‖c j‖ * ρ ^ j)) atTop (nhds 0) := by
  have hzero : (0 : ℝ) = ∑' _j : ℕ, (0 : ℝ) := by simp
  rw [hzero]
  apply tendsto_tsum_of_dominated_convergence hsum
  · intro j
    have h1 : Tendsto (fun d => 1 - φ d j) atTop (nhds 0) := by
      have := (tendsto_const_nhds (x := (1 : ℝ))).sub (hφlim j)
      simpa using this
    have := h1.mul_const (‖c j‖ * ρ ^ j)
    simpa using this
  · filter_upwards with d
    intro j
    have hb : 0 ≤ ‖c j‖ * ρ ^ j := by positivity
    have h1 : 0 ≤ 1 - φ d j := by linarith [(hφ01 d j).2]
    have h2 : 1 - φ d j ≤ 1 := by linarith [(hφ01 d j).1]
    rw [Real.norm_of_nonneg (by positivity)]
    nlinarith [hb, h1, h2]

end RHTower
