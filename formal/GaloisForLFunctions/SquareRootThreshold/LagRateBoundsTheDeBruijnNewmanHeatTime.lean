import GaloisForLFunctions.SquareRootThreshold.GroundEnergyAbscissaAndLagGridAttainmentBridge
import GaloisForLFunctions.RHTower.DeBruijnNewmanHalfBound
import GaloisForLFunctions.RHTower.ZetaXiZeroCorrespondence

/-!
# The zero width, its lag and ground-energy readings, and the de Bruijn–Newman heat time

The **zero width** `zetaZeroWidth = sup |Re ρ − ½|` over the nontrivial zeros `ρ` of `ζ` is a
number in `[0, ½]`, and RH is `zetaZeroWidth = 0` (`riemannHypothesis_iff_zetaZeroWidth_eq_zero`).
Three parts of the corpus measure it, and this module joins them.

* **Lag side** (`zetaZeroWidth_le_iff_lag_primeWindow_ge_neg_exp`). For all but countably many
  widths `w ∈ (0, ½ log 2)` and every `σ ≥ 0`: `zetaZeroWidth ≤ σ` iff the dyadic prime-window
  functional `P_{w,v}` of the difference test is `≥ −C e^{σv}` for all large lags. The width is
  the exact negativity rate of the one-parameter lag family.
* **Ground-energy side** (`zetaZeroWidth_le_of_ccmRestrictedWeilGroundEnergy_ge_neg_exp`). A floor
  `μ(A) ≥ −C e^{2σA}` on the restricted Weil ground energy at all large apertures gives
  `zetaZeroWidth ≤ σ`.
* **Heat side** (`riemannHeat_zeros_im_sq_le_of_zetaZeroWidth`,
  `riemannHeat_zeros_real_of_half_sq_zetaZeroWidth_le`). A zero `w` of `Ξ(w) = ξ(½ + iw)` is the
  nontrivial zero `½ + iw` of `ζ` (`mem_zetaZeroConfig_of_cosTransform_riemannKernel_eq_zero`), so
  `Ξ` has the zero strip `(Im w)² ≤ zetaZeroWidth²`, which the de Bruijn–Newman flow
  `H_t(z) = ∫ Φ(x) e^{tx²} e^{izx} dx` contracts (`cosTransform_heat_zeros_im_sq_le`):
  every zero of `H_t` has `(Im z)² ≤ max(zetaZeroWidth² − 2t, 0)`, and `H_t` is real-rooted for
  every `t ≥ zetaZeroWidth²/2`.

In this normalization the de Bruijn–Newman constant is the least heat time from which `H_t` is
real-rooted; it is at most `zetaZeroWidth²/2`. The unconditional width `½` gives de Bruijn's
`1/8` (`riemannHeat_zeros_real`). Read through the lag family: a lag envelope `P_{w,v} ≥ −C e^{σv}`
is a heat time `σ²/2` (`riemannHeat_zeros_real_of_lag_primeWindow_ge_neg_exp`); read through the
ground energy: a floor `μ(A) ≥ −C e^{2σA}` is a heat time `σ²/2`
(`riemannHeat_zeros_real_of_ccmRestrictedWeilGroundEnergy_ge_neg_exp`). The corpus's unconditional
envelope `e^{v/2 − √v/10}` is no power saving and leaves `1/8`.
-/

open Complex Set Filter Topology
open scoped Real

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower _root_.RHTower.DeBruijn GaloisForLFunctions.ArithmeticCriticalityTheory

/-! ### 1. The zero width -/

/-- The zero width of `ζ`: the supremum of `|Re ρ − ½|` over the nontrivial zeros `ρ`. -/
noncomputable def zetaZeroWidth : ℝ :=
  sSup ((fun ρ : ℂ => |ρ.re - 1 / 2|) '' zetaZeroConfig.carrier)

/-- Every nontrivial zero lies in the open strip, so `|Re ρ − ½| < ½`. -/
theorem abs_re_sub_half_lt_half_of_mem_zetaZeroConfig {ρ : ℂ} (hρ : ρ ∈ zetaZeroConfig.carrier) :
    |ρ.re - 1 / 2| < 1 / 2 := by
  obtain ⟨-, h0, h1⟩ := (show IsNontrivialZero ρ from hρ)
  rw [abs_lt]; constructor <;> linarith

theorem bddAbove_image_abs_re_sub_half :
    BddAbove ((fun ρ : ℂ => |ρ.re - 1 / 2|) '' zetaZeroConfig.carrier) :=
  ⟨1 / 2, by
    rintro _ ⟨ρ, hρ, rfl⟩
    exact (abs_re_sub_half_lt_half_of_mem_zetaZeroConfig hρ).le⟩

/-- Every nontrivial zero has `|Re ρ − ½| ≤ zetaZeroWidth`. -/
theorem abs_re_sub_half_le_zetaZeroWidth {ρ : ℂ} (hρ : ρ ∈ zetaZeroConfig.carrier) :
    |ρ.re - 1 / 2| ≤ zetaZeroWidth :=
  le_csSup bddAbove_image_abs_re_sub_half ⟨ρ, hρ, rfl⟩

theorem zetaZeroWidth_nonneg : 0 ≤ zetaZeroWidth :=
  Real.sSup_nonneg fun _ ⟨_, _, h⟩ => h ▸ abs_nonneg _

theorem zetaZeroWidth_le_half : zetaZeroWidth ≤ 1 / 2 :=
  Real.sSup_le (by
    rintro _ ⟨ρ, hρ, rfl⟩
    exact (abs_re_sub_half_lt_half_of_mem_zetaZeroConfig hρ).le) (by norm_num)

/-- `zetaZeroWidth ≤ σ` iff every nontrivial zero has `Re ρ ≤ ½ + σ` (the reflection
`ρ ↦ 1 − ρ̄` supplies the other side of the strip). -/
theorem zetaZeroWidth_le_iff_re_le {σ : ℝ} (hσ : 0 ≤ σ) :
    zetaZeroWidth ≤ σ ↔ ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1 / 2 + σ := by
  constructor
  · intro h ρ hρ
    have := (abs_re_sub_half_le_zetaZeroWidth hρ).trans h
    linarith [(abs_le.mp this).2]
  · intro h
    refine Real.sSup_le ?_ hσ
    rintro _ ⟨ρ, hρ, rfl⟩
    have h1 := h ρ hρ
    have h2 := h _ (zetaZeroConfig.reflect_mem ρ hρ)
    have hrefl : (Zeta23.reflect ρ).re = 1 - ρ.re := by simp [Zeta23.reflect]
    rw [hrefl] at h2
    rw [abs_le]; constructor <;> linarith

/-- **RH is the vanishing of the zero width.** -/
theorem riemannHypothesis_iff_zetaZeroWidth_eq_zero : RiemannHypothesis ↔ zetaZeroWidth = 0 := by
  rw [riemannHypothesis_iff_zetaZeroConfig_onLine]
  constructor
  · intro h
    refine le_antisymm ?_ zetaZeroWidth_nonneg
    exact (zetaZeroWidth_le_iff_re_le le_rfl).mpr fun ρ hρ => by rw [h ρ hρ]; norm_num
  · intro h ρ hρ
    have := abs_re_sub_half_le_zetaZeroWidth hρ
    rw [h, abs_nonpos_iff] at this
    linarith

/-! ### 2. The lag and ground-energy readings of the width -/

/-- **The lag family measures the zero width.** For all but countably many widths
`w ∈ (0, ½ log 2)` and every `σ ≥ 0`: `zetaZeroWidth ≤ σ` iff the dyadic prime-window functional
`P_{w,v}` of the difference test is `≥ −C e^{σv}` for all large lags `v`. -/
theorem zetaZeroWidth_le_iff_lag_primeWindow_ge_neg_exp :
    ∃ E : Set ℝ, E.Countable ∧ ∀ w : ℝ, 0 < w → 2 * w < Real.log 2 → w ∉ E → ∀ σ : ℝ, 0 ≤ σ →
      (zetaZeroWidth ≤ σ ↔ ∃ C V : ℝ, 0 ≤ V ∧ ∀ v : ℝ, V ≤ v → -(C * Real.exp (σ * v)) ≤
        (lagPrimeWindowRHS v w (EF.weilTest (twoBump (modScaledBump w 0) v (-1))
          (twoBump (modScaledBump w 0) v (-1)))).re) := by
  obtain ⟨E, hE, hlaw⟩ := zeta_re_le_iff_lag_primeWindow_ge_neg_exp
  exact ⟨E, hE, fun w hw hw2 hwE σ hσ =>
    (zetaZeroWidth_le_iff_re_le hσ).trans (hlaw w hw hw2 hwE σ hσ)⟩

/-- **A ground-energy floor bounds the zero width.** If `μ(A) ≥ −C e^{2σA}` for all large
apertures (`σ ≥ 0`), then `zetaZeroWidth ≤ σ`. -/
theorem zetaZeroWidth_le_of_ccmRestrictedWeilGroundEnergy_ge_neg_exp {σ C A₀ : ℝ} (hσ : 0 ≤ σ)
    (hμ : ∀ A : SuzukiPositiveAperture, A₀ ≤ A.1 →
      -(C * Real.exp (2 * σ * A.1)) ≤ ccmRestrictedWeilGroundEnergy A) :
    zetaZeroWidth ≤ σ :=
  (zetaZeroWidth_le_iff_re_le hσ).mpr (re_le_of_ccmRestrictedWeilGroundEnergy_ge_neg_exp hσ hμ)

/-! ### 3. The heat strip and the de Bruijn–Newman heat time -/

/-- A zero `w` of `Ξ(w) = ξ(½ + iw)` is the nontrivial zero `½ + iw` of `ζ`. -/
theorem mem_zetaZeroConfig_of_cosTransform_riemannKernel_eq_zero {w : ℂ}
    (hw : cosTransform riemannKernelReal w = 0) :
    (1 / 2 + I * w) ∈ zetaZeroConfig.carrier := by
  rw [cosTransform_riemannKernel] at hw
  obtain ⟨h0, h1⟩ := xi_zero_re_mem_open_unit hw
  exact show IsNontrivialZero (1 / 2 + I * w) from
    ⟨(xi_eq_zero_iff_riemannZeta_eq_zero_and_nontrivial.mp hw).1, h0, h1⟩

/-- **The zero strip of `Ξ` has half-width `zetaZeroWidth`.** -/
theorem im_sq_le_zetaZeroWidth_sq_of_cosTransform_riemannKernel_eq_zero {w : ℂ}
    (hw : cosTransform riemannKernelReal w = 0) : w.im ^ 2 ≤ zetaZeroWidth ^ 2 := by
  have hmem := mem_zetaZeroConfig_of_cosTransform_riemannKernel_eq_zero hw
  have h := abs_re_sub_half_le_zetaZeroWidth hmem
  have hre : (1 / 2 + I * w).re - 1 / 2 = -w.im := by simp
  rw [hre, abs_neg] at h
  calc w.im ^ 2 = |w.im| ^ 2 := (sq_abs _).symm
    _ ≤ zetaZeroWidth ^ 2 := by gcongr

/-- **The heat strip.** Every zero of the de Bruijn–Newman deformation `H_t`, `t ≥ 0`, satisfies
`(Im z)² ≤ max(zetaZeroWidth² − 2t, 0)`: the strip of `Ξ` contracts under the heat flow. -/
theorem riemannHeat_zeros_im_sq_le_of_zetaZeroWidth {t : ℝ} (ht : 0 ≤ t) {z : ℂ}
    (hz : riemannHeat t z = 0) : z.im ^ 2 ≤ max (zetaZeroWidth ^ 2 - 2 * t) 0 := by
  rcases ht.lt_or_eq with ht' | rfl
  · exact cosTransform_heat_zeros_im_sq_le riemannKernel_superExp
      (fun w hw => im_sq_le_zetaZeroWidth_sq_of_cosTransform_riemannKernel_eq_zero hw) ht' z hz
  · have h0 : cosTransform riemannKernelReal z = 0 := by
      rw [cosTransform_riemannKernel, ← riemannHeat_zero]; exact hz
    rw [mul_zero, sub_zero, max_eq_left (sq_nonneg _)]
    exact im_sq_le_zetaZeroWidth_sq_of_cosTransform_riemannKernel_eq_zero h0

/-- **The de Bruijn–Newman heat time is at most half the square of the zero width.** For every
`t ≥ zetaZeroWidth²/2` all zeros of `H_t` are real. -/
theorem riemannHeat_zeros_real_of_half_sq_zetaZeroWidth_le {t : ℝ}
    (ht : zetaZeroWidth ^ 2 / 2 ≤ t) {z : ℂ} (hz : riemannHeat t z = 0) : z.im = 0 := by
  have ht0 : 0 ≤ t := le_trans (by positivity) ht
  have hsq := riemannHeat_zeros_im_sq_le_of_zetaZeroWidth ht0 hz
  rw [max_eq_right (by linarith)] at hsq
  exact (pow_eq_zero_iff two_ne_zero).mp (le_antisymm hsq (sq_nonneg _))

/-- **A zero width is a heat time.** If every nontrivial zero has `Re ρ ≤ ½ + σ` (`σ ≥ 0`), every
zero of `H_t` is real for every `t ≥ σ²/2`. -/
theorem riemannHeat_zeros_real_of_re_le {σ : ℝ} (hσ : 0 ≤ σ)
    (h : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1 / 2 + σ) {t : ℝ} (ht : σ ^ 2 / 2 ≤ t) {z : ℂ}
    (hz : riemannHeat t z = 0) : z.im = 0 := by
  have hw := (zetaZeroWidth_le_iff_re_le hσ).mpr h
  exact riemannHeat_zeros_real_of_half_sq_zetaZeroWidth_le
    (le_trans (by gcongr; exact zetaZeroWidth_nonneg) ht) hz

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

end GaloisForLFunctions.SquareRootThreshold
