import GaloisForLFunctions.SquareRootThreshold.GroundEnergyAbscissaAndLagGridAttainmentBridge
import GaloisForLFunctions.RHTower.DeBruijnNewmanHalfBound
import GaloisForLFunctions.RHTower.ZetaXiZeroCorrespondence

/-!
# The lag rate and the ground-energy rate bound the de Bruijn–Newman heat time

Three measures of the zero width `Θ − ½ = sup |Re ρ − ½|` live in different parts of the corpus:

* the negativity rate of the one-parameter lag family: for all but countably many widths `w`,
  every zero has `Re ρ ≤ ½ + σ` iff the prime-window functional `P_{w,v}` is `≥ −C e^{σv}` for all
  large lags (`zeta_re_le_iff_lag_primeWindow_ge_neg_exp`);
* the negativity rate of the restricted Weil ground energy: `μ(A) ≥ −C e^{2σA}` for all large
  apertures forces `Re ρ ≤ ½ + σ` (`re_le_of_ccmRestrictedWeilGroundEnergy_ge_neg_exp`);
* the heat time of the de Bruijn–Newman deformation `H_t(z) = ∫ Φ(x) e^{tx²} e^{izx} dx` of `Ξ`:
  a zero strip `(Im z)² ≤ D` of `Ξ` contracts to `(Im z)² ≤ max(D − 2t, 0)` under the flow
  (`cosTransform_heat_zeros_im_sq_le`).

This module joins them. A zero `w` of `Ξ` is the nontrivial zero `½ + iw` of `ζ`
(`mem_zetaZeroConfig_of_cosTransform_riemannKernel_eq_zero`), so a zero width `σ` is the strip
`(Im w)² ≤ σ²` of `Ξ` and gives `(Im z)² ≤ max(σ² − 2t, 0)` for the zeros of `H_t`
(`riemannHeat_zeros_im_sq_le_of_re_le`). Hence:

* **lag rate `σ` ⟹ heat time `σ²/2`** (`riemannHeat_zeros_real_of_lag_primeWindow_ge_neg_exp`):
  if `P_{w,v} ≥ −C e^{σv}` for all large `v`, every zero of `H_t` is real for every `t ≥ σ²/2`;
* **ground-energy rate `2σ` ⟹ heat time `σ²/2`**
  (`riemannHeat_zeros_real_of_ccmRestrictedWeilGroundEnergy_ge_neg_exp`): if `μ(A) ≥ −C e^{2σA}`
  for all large `A`, every zero of `H_t` is real for every `t ≥ σ²/2`.

In this normalization the de Bruijn–Newman constant is the least `t` from which `H_t` is
real-rooted; the unconditional width `½` gives de Bruijn's `t ≥ 1/8` (`riemannHeat_zeros_real`),
and `σ = 0` (RH) gives `t ≥ 0`. Any sub-exponential improvement of the lag envelope or of the
ground-energy floor at infinity therefore lowers the heat time quadratically; the corpus's
envelope `e^{v/2 − √v/10}` is not a power saving and leaves `1/8`.
-/

open Complex Set Filter Topology
open scoped Real

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower GaloisForLFunctions.ArithmeticCriticalityTheory

/-- A zero `w` of `Ξ(w) = ξ(½ + iw)` is the nontrivial zero `½ + iw` of `ζ`. -/
theorem mem_zetaZeroConfig_of_cosTransform_riemannKernel_eq_zero {w : ℂ}
    (hw : cosTransform riemannKernelReal w = 0) :
    (1 / 2 + I * w) ∈ zetaZeroConfig.carrier := by
  rw [cosTransform_riemannKernel] at hw
  obtain ⟨h0, h1⟩ := xi_zero_re_mem_open_unit hw
  exact show IsNontrivialZero (1 / 2 + I * w) from
    ⟨(xi_eq_zero_iff_riemannZeta_eq_zero_and_nontrivial.mp hw).1, h0, h1⟩

/-- **A zero width is a heat strip.** If every nontrivial zero of `ζ` has `Re ρ ≤ ½ + σ`
(`σ ≥ 0`), then every zero of `H_t`, `t ≥ 0`, satisfies `(Im z)² ≤ max(σ² − 2t, 0)`. The
reflection `ρ ↦ 1 − ρ̄` turns the one-sided bound into `|Re ρ − ½| ≤ σ`, the strip `(Im w)² ≤ σ²`
of `Ξ`, which the heat flow contracts. -/
theorem riemannHeat_zeros_im_sq_le_of_re_le {σ : ℝ} (hσ : 0 ≤ σ)
    (h : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1 / 2 + σ) {t : ℝ} (ht : 0 ≤ t) {z : ℂ}
    (hz : riemannHeat t z = 0) : z.im ^ 2 ≤ max (σ ^ 2 - 2 * t) 0 := by
  have hstrip : ∀ w : ℂ, cosTransform riemannKernelReal w = 0 → w.im ^ 2 ≤ σ ^ 2 := by
    intro w hw
    have hmem := mem_zetaZeroConfig_of_cosTransform_riemannKernel_eq_zero hw
    have h1 := h _ hmem
    have h2 := h _ (zetaZeroConfig.reflect_mem _ hmem)
    have hre : (1 / 2 + I * w).re = 1 / 2 - w.im := by simp; ring
    have hrefl : (Zeta23.reflect (1 / 2 + I * w)).re = 1 - (1 / 2 + I * w).re := by
      simp [Zeta23.reflect]
    rw [hrefl, hre] at h2
    rw [hre] at h1
    have habs : |w.im| ≤ σ := abs_le.mpr ⟨by linarith, by linarith⟩
    calc w.im ^ 2 = |w.im| ^ 2 := (sq_abs _).symm
      _ ≤ σ ^ 2 := by gcongr
  rcases ht.lt_or_eq with ht' | rfl
  · exact cosTransform_heat_zeros_im_sq_le riemannKernel_superExp hstrip ht' z hz
  · have h0 : cosTransform riemannKernelReal z = 0 := by
      rw [cosTransform_riemannKernel, ← riemannHeat_zero]; exact hz
    rw [mul_zero, sub_zero, max_eq_left (sq_nonneg σ)]
    exact hstrip z h0

/-- **A zero width is a heat time.** If every nontrivial zero has `Re ρ ≤ ½ + σ`, every zero of
`H_t` is real for every `t ≥ σ²/2`. -/
theorem riemannHeat_zeros_real_of_re_le {σ : ℝ} (hσ : 0 ≤ σ)
    (h : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1 / 2 + σ) {t : ℝ} (ht : σ ^ 2 / 2 ≤ t) {z : ℂ}
    (hz : riemannHeat t z = 0) : z.im = 0 := by
  have ht0 : 0 ≤ t := le_trans (by positivity) ht
  have hsq := riemannHeat_zeros_im_sq_le_of_re_le hσ h ht0 hz
  rw [max_eq_right (by linarith)] at hsq
  exact (pow_eq_zero_iff two_ne_zero).mp (le_antisymm hsq (sq_nonneg _))

/-- **The lag rate bounds the heat time.** For all but countably many widths `w ∈ (0, ½ log 2)`
and every `σ ≥ 0`: if the dyadic prime-window functional `P_{w,v}` of the difference test is
`≥ −C e^{σv}` for all large lags `v`, then every zero of `H_t` is real for every `t ≥ σ²/2`. -/
theorem riemannHeat_zeros_real_of_lag_primeWindow_ge_neg_exp :
    ∃ E : Set ℝ, E.Countable ∧ ∀ w : ℝ, 0 < w → 2 * w < Real.log 2 → w ∉ E → ∀ σ : ℝ, 0 ≤ σ →
      (∃ C V : ℝ, 0 ≤ V ∧ ∀ v : ℝ, V ≤ v → -(C * Real.exp (σ * v)) ≤
        (lagPrimeWindowRHS v w (EF.weilTest (twoBump (modScaledBump w 0) v (-1))
          (twoBump (modScaledBump w 0) v (-1)))).re) →
      ∀ t : ℝ, σ ^ 2 / 2 ≤ t → ∀ z : ℂ, riemannHeat t z = 0 → z.im = 0 := by
  obtain ⟨E, hE, hlaw⟩ := zeta_re_le_iff_lag_primeWindow_ge_neg_exp
  refine ⟨E, hE, fun w hw hw2 hwE σ hσ hlag t ht z hz => ?_⟩
  exact riemannHeat_zeros_real_of_re_le hσ ((hlaw w hw hw2 hwE σ hσ).mpr hlag) ht hz

/-- **The ground-energy rate bounds the heat time.** If the restricted Weil ground energy
satisfies `μ(A) ≥ −C e^{2σA}` for all large apertures (`σ ≥ 0`), then every zero of `H_t` is
real for every `t ≥ σ²/2`. -/
theorem riemannHeat_zeros_real_of_ccmRestrictedWeilGroundEnergy_ge_neg_exp {σ C A₀ : ℝ}
    (hσ : 0 ≤ σ)
    (hμ : ∀ A : SuzukiPositiveAperture, A₀ ≤ A.1 →
      -(C * Real.exp (2 * σ * A.1)) ≤ ccmRestrictedWeilGroundEnergy A)
    {t : ℝ} (ht : σ ^ 2 / 2 ≤ t) {z : ℂ} (hz : riemannHeat t z = 0) : z.im = 0 :=
  riemannHeat_zeros_real_of_re_le hσ (re_le_of_ccmRestrictedWeilGroundEnergy_ge_neg_exp hσ hμ)
    ht hz

/-- **The heat strip from the ground-energy rate.** Under `μ(A) ≥ −C e^{2σA}` for all large
apertures, every zero of `H_t`, `t ≥ 0`, satisfies `(Im z)² ≤ max(σ² − 2t, 0)`. -/
theorem riemannHeat_zeros_im_sq_le_of_ccmRestrictedWeilGroundEnergy_ge_neg_exp {σ C A₀ : ℝ}
    (hσ : 0 ≤ σ)
    (hμ : ∀ A : SuzukiPositiveAperture, A₀ ≤ A.1 →
      -(C * Real.exp (2 * σ * A.1)) ≤ ccmRestrictedWeilGroundEnergy A)
    {t : ℝ} (ht : 0 ≤ t) {z : ℂ} (hz : riemannHeat t z = 0) :
    z.im ^ 2 ≤ max (σ ^ 2 - 2 * t) 0 :=
  riemannHeat_zeros_im_sq_le_of_re_le hσ (re_le_of_ccmRestrictedWeilGroundEnergy_ge_neg_exp hσ hμ)
    ht hz

end GaloisForLFunctions.SquareRootThreshold
