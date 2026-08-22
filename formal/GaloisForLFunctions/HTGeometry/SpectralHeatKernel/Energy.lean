import GaloisForLFunctions.HTGeometry.SpectralHeatKernel.Flow
import GaloisForLFunctions.HTGeometry.DaiYoshikawa.PowerExpSup
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# The energy identity `d/dt ‖e^{−tΔ}v‖² = −2 Q(e^{−tΔ}v)`

Every Nash-type ultracontractivity argument starts from the fact that the squared `L²` norm along
the heat flow decays at the rate given by the Dirichlet form.  Spectrally,

```text
‖e^{−tΔ}v‖² = Σₙ e^{−2tλₙ}|cₙ|² ,    d/dt ‖e^{−tΔ}v‖² = −2 Σₙ λₙ e^{−2tλₙ}|cₙ|² ,
```

and differentiating the series term by term is legitimate on every half-line `t > t₀ > 0` because
`λ e^{−t₀λ} ≤ 1/(e t₀)` — the extremal inequality of `PowerExpSup` — makes the differentiated series
dominated by a multiple of the heat trace.
-/

open Set Filter Real

namespace GaloisForLFunctions.HTGeometry

/-- The spectral energy profile `t ↦ Σₙ e^{−2tλₙ} aₙ`. -/
noncomputable def spectralEnergy (lam a : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑' n, Real.exp (-(2 * t * lam n)) * a n

/-- `λ e^{−t₀λ} ≤ 1/(e t₀)`, the extremal inequality in the form used to dominate the
differentiated heat series. -/
theorem mul_exp_neg_le_inv {t₀ : ℝ} (ht₀ : 0 < t₀) {μ : ℝ} (hμ : 0 ≤ μ) :
    μ * Real.exp (-(t₀ * μ)) ≤ 1 / (Real.exp 1 * t₀) := by
  have h := DaiYoshikawa.pow_mul_exp_neg_div_le 1 (a := 1 / t₀) (by positivity) hμ
  have harg : μ / (1 / t₀) = t₀ * μ := by field_simp
  rw [harg, pow_one] at h
  refine h.trans (le_of_eq ?_)
  push_cast
  rw [Real.exp_neg]
  field_simp

/-- The differentiated series is dominated on `(t₀,∞)`. -/
theorem spectralEnergy_deriv_bound {lam a : ℕ → ℝ} {t₀ : ℝ} (ht₀ : 0 < t₀)
    (hlam : ∀ n, 0 ≤ lam n) (ha : ∀ n, 0 ≤ a n) (n : ℕ) {y : ℝ} (hy : t₀ < y) :
    ‖-(2 * lam n) * (Real.exp (-(2 * y * lam n)) * a n)‖
      ≤ 2 / (Real.exp 1 * t₀) * (Real.exp (-(t₀ * lam n)) * a n) := by
  have hEy : (0 : ℝ) ≤ Real.exp (-(2 * y * lam n)) := Real.exp_nonneg _
  have hEt : (0 : ℝ) ≤ Real.exp (-(t₀ * lam n)) := Real.exp_nonneg _
  have hnn : 0 ≤ 2 * lam n * (Real.exp (-(2 * y * lam n)) * a n) :=
    mul_nonneg (by linarith [hlam n]) (mul_nonneg hEy (ha n))
  have hnorm : ‖-(2 * lam n) * (Real.exp (-(2 * y * lam n)) * a n)‖
      = 2 * lam n * (Real.exp (-(2 * y * lam n)) * a n) := by
    rw [Real.norm_eq_abs, neg_mul, abs_neg, abs_of_nonneg hnn]
  rw [hnorm]
  have hexp : Real.exp (-(2 * y * lam n)) ≤ Real.exp (-(2 * t₀ * lam n)) := by
    refine Real.exp_le_exp.mpr ?_
    nlinarith [hlam n, ht₀, hy]
  have hsplit : Real.exp (-(2 * t₀ * lam n))
      = Real.exp (-(t₀ * lam n)) * Real.exp (-(t₀ * lam n)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hkey : lam n * Real.exp (-(t₀ * lam n)) ≤ 1 / (Real.exp 1 * t₀) :=
    mul_exp_neg_le_inv ht₀ (hlam n)
  have hbound : lam n * Real.exp (-(2 * y * lam n))
      ≤ 1 / (Real.exp 1 * t₀) * Real.exp (-(t₀ * lam n)) := by
    calc lam n * Real.exp (-(2 * y * lam n))
        ≤ lam n * Real.exp (-(2 * t₀ * lam n)) := mul_le_mul_of_nonneg_left hexp (hlam n)
      _ = (lam n * Real.exp (-(t₀ * lam n))) * Real.exp (-(t₀ * lam n)) := by
          rw [hsplit]; ring
      _ ≤ (1 / (Real.exp 1 * t₀)) * Real.exp (-(t₀ * lam n)) :=
          mul_le_mul_of_nonneg_right hkey hEt
  calc 2 * lam n * (Real.exp (-(2 * y * lam n)) * a n)
      = 2 * a n * (lam n * Real.exp (-(2 * y * lam n))) := by ring
    _ ≤ 2 * a n * (1 / (Real.exp 1 * t₀) * Real.exp (-(t₀ * lam n))) :=
        mul_le_mul_of_nonneg_left hbound (by linarith [ha n])
    _ = 2 / (Real.exp 1 * t₀) * (Real.exp (-(t₀ * lam n)) * a n) := by ring

/-- **The energy identity.**

On every half-line `t > t₀ > 0` the spectral energy is differentiable with derivative
`−2 Σₙ λₙ e^{−2tλₙ} aₙ`. -/
theorem hasDerivAt_spectralEnergy {lam a : ℕ → ℝ} {t₀ t : ℝ} (ht₀ : 0 < t₀) (ht : t₀ < t)
    (hlam : ∀ n, 0 ≤ lam n) (ha : ∀ n, 0 ≤ a n)
    (hsum : Summable fun n => Real.exp (-(t₀ * lam n)) * a n) :
    HasDerivAt (spectralEnergy lam a)
      (∑' n, -(2 * lam n) * (Real.exp (-(2 * t * lam n)) * a n)) t := by
  have hu : Summable fun n => 2 / (Real.exp 1 * t₀) * (Real.exp (-(t₀ * lam n)) * a n) :=
    hsum.mul_left _
  have hg : ∀ (n : ℕ) (y : ℝ), y ∈ Ioi t₀ →
      HasDerivAt (fun z => Real.exp (-(2 * z * lam n)) * a n)
        (-(2 * lam n) * (Real.exp (-(2 * y * lam n)) * a n)) y := by
    intro n y _
    have hfun : (fun z : ℝ => Real.exp (-(2 * z * lam n)) * a n)
        = fun z : ℝ => Real.exp ((-(2 * lam n)) * z) * a n := by
      funext z
      congr 2
      ring
    rw [hfun]
    have h1 : HasDerivAt (fun z : ℝ => (-(2 * lam n)) * z) (-(2 * lam n)) y := by
      simpa using (hasDerivAt_id y).const_mul (-(2 * lam n))
    have h2 := (h1.exp).mul_const (a n)
    have hval : Real.exp ((-(2 * lam n)) * y) * (-(2 * lam n)) * a n
        = -(2 * lam n) * (Real.exp (-(2 * y * lam n)) * a n) := by
      have : Real.exp ((-(2 * lam n)) * y) = Real.exp (-(2 * y * lam n)) := by
        congr 1
        ring
      rw [this]
      ring
    rwa [hval] at h2
  have hg' : ∀ (n : ℕ) (y : ℝ), y ∈ Ioi t₀ →
      ‖-(2 * lam n) * (Real.exp (-(2 * y * lam n)) * a n)‖
        ≤ 2 / (Real.exp 1 * t₀) * (Real.exp (-(t₀ * lam n)) * a n) :=
    fun n y hy => spectralEnergy_deriv_bound ht₀ hlam ha n hy
  have hy₀ : (t₀ + (t - t₀) / 2) ∈ Ioi t₀ := by
    simp only [Set.mem_Ioi]
    linarith
  have hg0 : Summable fun n =>
      Real.exp (-(2 * (t₀ + (t - t₀) / 2) * lam n)) * a n := by
    refine Summable.of_nonneg_of_le
      (fun n => mul_nonneg (Real.exp_nonneg _) (ha n)) (fun n => ?_) hsum
    refine mul_le_mul_of_nonneg_right ?_ (ha n)
    refine Real.exp_le_exp.mpr ?_
    nlinarith [hlam n, ht₀, ht]
  exact hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioi isPreconnected_Ioi hg hg' hy₀ hg0
    (Set.mem_Ioi.mpr ht)

end GaloisForLFunctions.HTGeometry
