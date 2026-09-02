import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The Selberg-ledger ceiling

In the Selberg trace formula for `SL(2,ℤ)` the zeros of ζ enter only through the scattering density
`−(1/4π) φ'/φ(½ + ir) = Σ_ρ K_ρ(r)`, `φ(s) = ξ(2s−1)/ξ(2s)`, where for `ρ = β + iγ`

  `K_ρ(r) = (1/2π) [ (1−β)/((1−β)² + (2r−γ)²) + β/(β² + (2r−γ)²) ]`

is a pair of Poisson kernels centred at `r = γ/2`.  For an admissible `h ≥ 0` the trace formula reads
`Σ_j h(t_j) + Σ_ρ w_h(ρ) = G(h)` with `w_h(ρ) = ∫ h K_ρ`; its only created positivity is
`Σ_j h(t_j) ≥ 0`, so its only consequence for the zeros is `Σ_ρ w_h(ρ) ≤ G(h)`.  Such an
inequality can contradict the existence of a zero `ρ₀` only if `w_h(ρ₀)` exceeds the sum of the
weights of the other zeros.  This file proves the two bounds that cap that comparison,

  `w_h(ρ₀) ≤ (‖h‖₁/2π)(1/(1−β₀) + 1/β₀)`  and  `w_h(ρ) ≥ (2/29π) ‖h‖₁`

for `h` supported in `|r − γ₀/2| ≤ ¼` and `|γ − γ₀| ≤ 2`, and their consequence: with `Z` any set
of such zeros, `w_h(ρ₀) > Σ_{ρ ∈ Z} w_h(ρ)` forces `(4/29)|Z| < 1/(1−β₀) + 1/β₀`, hence
`1 − β₀ < 1/((4/29)|Z| − 2)`.  Since `|Z| ≫ log γ₀` unconditionally, the ledger only reaches the
de la Vallée Poussin width `c/log γ₀`.
-/

open MeasureTheory Real

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- The scattering density of one zero `ρ = β + iγ` at the spectral point `r`. -/
def zeroKernel (β γ r : ℝ) : ℝ :=
  (1 / (2 * π)) * ((1 - β) / ((1 - β) ^ 2 + (2 * r - γ) ^ 2) + β / (β ^ 2 + (2 * r - γ) ^ 2))

theorem zeroKernel_nonneg {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (γ r : ℝ) : 0 ≤ zeroKernel β γ r := by
  unfold zeroKernel
  have : 0 ≤ 1 - β := sub_nonneg.mpr hβ1
  positivity

/-- The kernel is maximal at its centre: `K_ρ ≤ (1/2π)(1/(1−β) + 1/β)`. -/
theorem zeroKernel_le_peak {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (γ r : ℝ) :
    zeroKernel β γ r ≤ (1 / (2 * π)) * (1 / (1 - β) + 1 / β) := by
  unfold zeroKernel
  have h1 : 0 < 1 - β := sub_pos.mpr hβ1
  have hA : (1 - β) / ((1 - β) ^ 2 + (2 * r - γ) ^ 2) ≤ 1 / (1 - β) := by
    calc (1 - β) / ((1 - β) ^ 2 + (2 * r - γ) ^ 2) ≤ (1 - β) / (1 - β) ^ 2 :=
          div_le_div_of_nonneg_left h1.le (pow_pos h1 2) (le_add_of_nonneg_right (sq_nonneg _))
      _ = 1 / (1 - β) := by field_simp
  have hB : β / (β ^ 2 + (2 * r - γ) ^ 2) ≤ 1 / β := by
    calc β / (β ^ 2 + (2 * r - γ) ^ 2) ≤ β / β ^ 2 :=
          div_le_div_of_nonneg_left hβ0.le (pow_pos hβ0 2) (le_add_of_nonneg_right (sq_nonneg _))
      _ = 1 / β := by field_simp
  have hpi : (0 : ℝ) ≤ 1 / (2 * π) := by positivity
  exact mul_le_mul_of_nonneg_left (add_le_add hA hB) hpi

/-- The kernel floor `K_ρ ≥ (1/2π)/(1 + (2r−γ)²)`, uniform in `β ∈ [0,1]`. -/
theorem zeroKernel_ge {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (γ r : ℝ) :
    (1 / (2 * π)) / (1 + (2 * r - γ) ^ 2) ≤ zeroKernel β γ r := by
  unfold zeroKernel
  have h1 : 0 < 1 - β := sub_pos.mpr hβ1
  have hA : (1 - β) / (1 + (2 * r - γ) ^ 2) ≤ (1 - β) / ((1 - β) ^ 2 + (2 * r - γ) ^ 2) :=
    div_le_div_of_nonneg_left h1.le (add_pos_of_pos_of_nonneg (pow_pos h1 2) (sq_nonneg _))
      (by nlinarith)
  have hB : β / (1 + (2 * r - γ) ^ 2) ≤ β / (β ^ 2 + (2 * r - γ) ^ 2) :=
    div_le_div_of_nonneg_left hβ0.le (add_pos_of_pos_of_nonneg (pow_pos hβ0 2) (sq_nonneg _))
      (by nlinarith)
  have hsum : (1 / (2 * π)) / (1 + (2 * r - γ) ^ 2)
      = (1 / (2 * π)) * ((1 - β) / (1 + (2 * r - γ) ^ 2) + β / (1 + (2 * r - γ) ^ 2)) := by
    rw [← add_div, sub_add_cancel, div_eq_mul_one_div]
  rw [hsum]
  have hpi : (0 : ℝ) ≤ 1 / (2 * π) := by positivity
  exact mul_le_mul_of_nonneg_left (add_le_add hA hB) hpi

theorem continuous_zeroKernel {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (γ : ℝ) :
    Continuous (zeroKernel β γ) := by
  unfold zeroKernel
  have h1 : 0 < 1 - β := sub_pos.mpr hβ1
  refine continuous_const.mul (Continuous.add ?_ ?_)
  · exact continuous_const.div (by fun_prop) fun r =>
      (add_pos_of_pos_of_nonneg (pow_pos h1 2) (sq_nonneg _)).ne'
  · exact continuous_const.div (by fun_prop) fun r =>
      (add_pos_of_pos_of_nonneg (pow_pos hβ0 2) (sq_nonneg _)).ne'

/-- The ledger weight `w_h(ρ) = ∫ h K_ρ`. -/
def ledgerWeight (h : ℝ → ℝ) (β γ : ℝ) : ℝ := ∫ r, h r * zeroKernel β γ r

theorem integrable_mul_zeroKernel {h : ℝ → ℝ} (hh : Integrable h) {β : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (γ : ℝ) : Integrable fun r => h r * zeroKernel β γ r := by
  have := hh.bdd_mul (c := (1 / (2 * π)) * (1 / (1 - β) + 1 / β))
    (continuous_zeroKernel hβ0 hβ1 γ).aestronglyMeasurable
    (ae_of_all _ fun r => by
      rw [Real.norm_of_nonneg (zeroKernel_nonneg hβ0.le hβ1.le γ r)]
      exact zeroKernel_le_peak hβ0 hβ1 γ r)
  exact this.congr (ae_of_all _ fun r => mul_comm _ _)

/-- **The peak bound**: `w_h(ρ) ≤ (‖h‖₁/2π)(1/(1−β) + 1/β)` for `h ≥ 0`. -/
theorem ledgerWeight_le_peak_mul {h : ℝ → ℝ} (hh : Integrable h) (hpos : ∀ r, 0 ≤ h r) {β : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (γ : ℝ) :
    ledgerWeight h β γ ≤ (1 / (2 * π)) * (1 / (1 - β) + 1 / β) * ∫ r, h r := by
  unfold ledgerWeight
  rw [← integral_const_mul]
  refine integral_mono (integrable_mul_zeroKernel hh hβ0 hβ1 γ) (hh.const_mul _) fun r => ?_
  show h r * zeroKernel β γ r ≤ (1 / (2 * π)) * (1 / (1 - β) + 1 / β) * h r
  rw [mul_comm _ (h r)]
  exact mul_le_mul_of_nonneg_left (zeroKernel_le_peak hβ0 hβ1 γ r) (hpos r)

/-- **The floor bound**: for `h ≥ 0` supported in `|r − r₀| ≤ ¼` and a zero with `|γ − 2r₀| ≤ 2`,
`w_h(ρ) ≥ (2/29π) ‖h‖₁`. -/
theorem ledgerWeight_ge_of_support {h : ℝ → ℝ} (hh : Integrable h) (hpos : ∀ r, 0 ≤ h r) {β : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) {r₀ γ : ℝ} (hsupp : ∀ r, h r ≠ 0 → |r - r₀| ≤ 1 / 4)
    (hγ : |γ - 2 * r₀| ≤ 2) :
    (2 / (29 * π)) * ∫ r, h r ≤ ledgerWeight h β γ := by
  unfold ledgerWeight
  rw [← integral_const_mul]
  refine integral_mono (hh.const_mul _) (integrable_mul_zeroKernel hh hβ0 hβ1 γ) fun r => ?_
  show (2 / (29 * π)) * h r ≤ h r * zeroKernel β γ r
  by_cases hr : h r = 0
  · rw [hr]
    simp
  · have hle := hsupp r hr
    have hsq : (2 * r - γ) ^ 2 ≤ 25 / 4 := by
      have h1 : |2 * r - γ| ≤ 5 / 2 := by
        calc |2 * r - γ| = |2 * (r - r₀) + (2 * r₀ - γ)| := by ring_nf
          _ ≤ |2 * (r - r₀)| + |2 * r₀ - γ| := abs_add_le _ _
          _ ≤ 2 * (1 / 4) + 2 := by
              rw [abs_mul, abs_two, abs_sub_comm (2 * r₀) γ]
              gcongr
          _ = 5 / 2 := by norm_num
      have := abs_le.mp h1
      nlinarith
    have hK : 2 / (29 * π) ≤ zeroKernel β γ r := by
      refine le_trans ?_ (zeroKernel_ge hβ0 hβ1 γ r)
      rw [show (2 : ℝ) / (29 * π) = (1 / (2 * π)) / (29 / 4) by field_simp; ring]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
    rw [mul_comm _ (h r)]
    exact mul_le_mul_of_nonneg_left hK (hpos r)

/-- **The Selberg-ledger ceiling.** If the weight of a zero `ρ₀ = β₀ + iγ₀` exceeds the summed
weights of any family `Z` of zeros in the window `|γ − γ₀| ≤ 2` (the only way the positivity
`Σ_ρ w_h(ρ) ≤ G(h)` can contradict `ρ₀`), then `(4/29)|Z| < 1/(1−β₀) + 1/β₀`. -/
theorem selberg_ledger_exclusion {h : ℝ → ℝ} (hh : Integrable h) (hpos : ∀ r, 0 ≤ h r)
    {β₀ γ₀ : ℝ} (hβ₀ : 0 < β₀) (hβ₀' : β₀ < 1)
    (hsupp : ∀ r, h r ≠ 0 → |r - γ₀ / 2| ≤ 1 / 4) (Z : Finset (ℝ × ℝ))
    (hZ : ∀ ρ ∈ Z, 0 < ρ.1 ∧ ρ.1 < 1 ∧ |ρ.2 - γ₀| ≤ 2) (hint : 0 < ∫ r, h r)
    (hcontra : ∑ ρ ∈ Z, ledgerWeight h ρ.1 ρ.2 < ledgerWeight h β₀ γ₀) :
    (4 / 29 : ℝ) * Z.card < 1 / (1 - β₀) + 1 / β₀ := by
  have hup := ledgerWeight_le_peak_mul hh hpos hβ₀ hβ₀' γ₀
  have hlow : (Z.card : ℝ) * ((2 / (29 * π)) * ∫ r, h r) ≤ ∑ ρ ∈ Z, ledgerWeight h ρ.1 ρ.2 := by
    have := Finset.card_nsmul_le_sum Z (fun ρ : ℝ × ℝ => ledgerWeight h ρ.1 ρ.2)
      ((2 / (29 * π)) * ∫ r, h r) fun ρ hρ =>
        ledgerWeight_ge_of_support hh hpos (hZ ρ hρ).1 (hZ ρ hρ).2.1 (r₀ := γ₀ / 2) hsupp
          (by rw [show 2 * (γ₀ / 2) = γ₀ by ring]; exact (hZ ρ hρ).2.2)
    simpa [nsmul_eq_mul] using this
  have hchain := lt_of_le_of_lt hlow (lt_of_lt_of_le hcontra hup)
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hI : 0 < (∫ r, h r) / (2 * π) := by positivity
  have h1 : (Z.card : ℝ) * ((2 / (29 * π)) * ∫ r, h r)
      = ((4 / 29 : ℝ) * Z.card) * ((∫ r, h r) / (2 * π)) := by
    field_simp
    ring
  have h2 : (1 / (2 * π)) * (1 / (1 - β₀) + 1 / β₀) * ∫ r, h r
      = (1 / (1 - β₀) + 1 / β₀) * ((∫ r, h r) / (2 * π)) := by
    field_simp
  rw [h1, h2] at hchain
  exact lt_of_mul_lt_mul_right hchain hI.le

/-- **The width form of the ceiling**: with `β₀ ≥ ½`, any exclusion by the Selberg ledger needs
`1 − β₀ < 1/((4/29)|Z| − 2)`. -/
theorem selberg_ledger_width {h : ℝ → ℝ} (hh : Integrable h) (hpos : ∀ r, 0 ≤ h r)
    {β₀ γ₀ : ℝ} (hβ₀ : 1 / 2 ≤ β₀) (hβ₀' : β₀ < 1)
    (hsupp : ∀ r, h r ≠ 0 → |r - γ₀ / 2| ≤ 1 / 4) (Z : Finset (ℝ × ℝ))
    (hZ : ∀ ρ ∈ Z, 0 < ρ.1 ∧ ρ.1 < 1 ∧ |ρ.2 - γ₀| ≤ 2) (hint : 0 < ∫ r, h r)
    (hcontra : ∑ ρ ∈ Z, ledgerWeight h ρ.1 ρ.2 < ledgerWeight h β₀ γ₀)
    (hbig : 2 < (4 / 29 : ℝ) * Z.card) :
    1 - β₀ < 1 / ((4 / 29 : ℝ) * Z.card - 2) := by
  have hβpos : 0 < β₀ := by linarith
  have hex := selberg_ledger_exclusion hh hpos hβpos hβ₀' hsupp Z hZ hint hcontra
  have hb : 1 / β₀ ≤ 2 := by
    rw [div_le_iff₀ hβpos]
    linarith
  have h1 : (4 / 29 : ℝ) * Z.card - 2 < 1 / (1 - β₀) := by linarith
  have h1β : 0 < 1 - β₀ := sub_pos.mpr hβ₀'
  rw [lt_div_iff₀ (by linarith)]
  rw [lt_div_iff₀ h1β] at h1
  linarith

end

end GaloisForLFunctions.RHTower
