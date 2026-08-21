import Mathlib

/-!
# Connes' logarithmic shift kernel of §VII (44)-(45)

Formalization of the scaling step (44)-(45) inside the proof of Lemma 2 of §VII of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

Lemma VII.2 bounds the error term `δ_q(Λ)` of the `S`-local trace formula by a Besov-type norm; the
key pointwise input is that for the fractional convolution operator `C_{α,v}` one has

  `∫_{k_v} ψ(|ε|) |log|x+ε| - log|x|| dε/|ε|^{1+α} ≤ c'_α |x|^{-α}`,        (45)

with the finite constant `c'_α = ∫_{k_v} log|1+y| dy/|y|^{1+α}` of (44).

The content of (45) is the exact scaling `ε = x y`, proved here without hypotheses at the real
place; the resulting kernel `connesLogShiftKernel` is exactly Connes' integrand of (44), so that
(45) follows by dropping the cut-off `0 ≤ ψ ≤ 1`.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section
open MeasureTheory Set Real Filter Topology

/-- Connes' §VII (44) kernel: the logarithmic difference weighted by `|y|^{-(1+α)}`. -/
def connesLogShiftKernel (α : ℝ) (y : ℝ) : ℝ :=
  abs (Real.log |1 + y|) * (|y| ^ (1 + α))⁻¹

/-- **§VII (45), the scaling identity.**  The logarithmic-difference integral at the point `x` is
`|x|^{-α}` times the same integral at `1`.  This is the exact form of Connes' inequality (45)
before dropping the cut-off `ψ`. -/
theorem connes_logShift_substitution {x : ℝ} (hx : x ≠ 0) (α : ℝ) (Ψ : ℝ → ℝ) :
    (∫ ε : ℝ, Ψ (ε / x) *
        (abs (Real.log |x + ε| - Real.log |x|) * (|ε| ^ (1 + α))⁻¹))
      = (|x| ^ (-α)) * ∫ y : ℝ, Ψ y * connesLogShiftKernel α y := by
  have hxpos : (0:ℝ) < |x| := abs_pos.mpr hx
  set H : ℝ → ℝ := fun ε => Ψ (ε / x) *
      (abs (Real.log |x + ε| - Real.log |x|) * (|ε| ^ (1 + α))⁻¹) with hH
  have hae : ∀ᵐ y : ℝ, y ≠ 0 ∧ 1 + y ≠ 0 := by
    have h0 : (volume : Measure ℝ) {(0:ℝ)} = 0 := Real.volume_singleton
    have h1 : (volume : Measure ℝ) {(-1:ℝ)} = 0 := Real.volume_singleton
    filter_upwards [compl_mem_ae_iff.2 h0, compl_mem_ae_iff.2 h1] with y hy0 hy1
    refine ⟨by simpa using hy0, ?_⟩
    intro hc
    exact (by simpa using hy1 : y ≠ -1) (by linarith [hc])
  have hpt : ∀ y : ℝ, y ≠ 0 → 1 + y ≠ 0 →
      H (x * y) = (|x| ^ (1 + α))⁻¹ * (Ψ y * connesLogShiftKernel α y) := by
    intro y hy0 hy1
    have hdiv : x * y / x = y := by field_simp
    have habs : |x + x * y| = |x| * |1 + y| := by
      rw [show x + x * y = x * (1 + y) by ring, abs_mul]
    have hlog : Real.log |x + x * y| - Real.log |x| = Real.log |1 + y| := by
      rw [habs, Real.log_mul (ne_of_gt hxpos) (abs_ne_zero.mpr hy1)]
      ring
    have habsxy : |x * y| = |x| * |y| := abs_mul x y
    have hpow : (|x * y| ^ (1 + α))⁻¹ = (|x| ^ (1 + α))⁻¹ * (|y| ^ (1 + α))⁻¹ := by
      rw [habsxy, Real.mul_rpow (le_of_lt hxpos) (abs_nonneg y), mul_inv]
    simp only [hH, hdiv, hlog, hpow, connesLogShiftKernel]
    ring
  have hshift : (∫ y : ℝ, H (x * y)) = |x|⁻¹ * ∫ ε : ℝ, H ε := by
    have h := Measure.integral_comp_mul_left H x
    rw [abs_inv] at h
    simpa [smul_eq_mul] using h
  have hcongr : (∫ y : ℝ, H (x * y))
      = (|x| ^ (1 + α))⁻¹ * ∫ y : ℝ, Ψ y * connesLogShiftKernel α y := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hae] with y hy
    exact hpt y hy.1 hy.2
  rw [hcongr] at hshift
  have hxne : (|x| : ℝ) ≠ 0 := ne_of_gt hxpos
  have hval : |x| ^ (-α) = |x| * (|x| ^ (1 + α))⁻¹ := by
    have h1 : (-α : ℝ) = 1 + (-(1 + α)) := by ring
    rw [h1, Real.rpow_add hxpos, Real.rpow_one, Real.rpow_neg (le_of_lt hxpos)]
  rw [hval]
  have hI : (∫ ε : ℝ, H ε)
      = |x| * ((|x| ^ (1 + α))⁻¹ * ∫ y : ℝ, Ψ y * connesLogShiftKernel α y) := by
    calc (∫ ε : ℝ, H ε) = |x| * (|x|⁻¹ * ∫ ε : ℝ, H ε) := by field_simp
      _ = |x| * ((|x| ^ (1 + α))⁻¹ * ∫ y : ℝ, Ψ y * connesLogShiftKernel α y) := by
          rw [← hshift]
  rw [hI]
  ring

end

end GaloisForLFunctions.RHTower
