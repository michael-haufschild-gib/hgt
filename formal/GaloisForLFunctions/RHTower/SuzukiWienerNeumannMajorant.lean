import Mathlib
import GaloisForLFunctions.HTGeometry.DiscreteL1Convolution

/-!
# The uniform coefficient domination theorem for the high-pass Wiener symbol

Above the high-pass threshold, Suzuki's frequency symbol has the coefficient form
`h = L δ₀ + q δ₀ + t` with `|q| ≤ C`, `t ∈ ℓ¹` of mass `M`, and `L ≥ L₀`.  Its relative kernel
`r = (q δ₀ + t)/L` is dominated coefficientwise by the fixed frequency-independent majorant
`r_* = (C δ₀ + |t|)/L₀`, whose mass is exactly `(C + M)/L₀`.  Convolution powers inherit the
domination, so the Neumann inverse `h⁻¹ = L⁻¹ ∑ₖ (-r)^{⋆k}` — proved here to be an actual
two-sided convolution inverse — has coefficients bounded by the fixed kernel
`K = L₀⁻¹ ∑ₖ r_*^{⋆k}`, of mass exactly `L₀⁻¹ (1 - (C+M)/L₀)⁻¹`.

Every bound is frequency-independent: this is the uniform coefficientwise `ℓ¹` majorant that
repairs the false `L²(ℓ¹)` Plancherel interface.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry
open scoped ENNReal

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- The high-pass symbol coefficients: `h = (L + q) δ₀ + t`. -/
def wienerHighPassSymbol (L q : ℂ) (t : G → ℂ) : G → ℂ := fun ν =>
  (L + q) * discreteDelta ν + t ν

/-- The relative kernel `r = (q δ₀ + t)/L`. -/
def wienerRelativeKernel (L q : ℂ) (t : G → ℂ) : G → ℂ := fun ν =>
  (q * discreteDelta ν + t ν) / L

/-- The fixed frequency-independent majorant `r_* = (C δ₀ + |t|)/L₀`. -/
def wienerStarKernel (C L0 : ℝ) (t : G → ℂ) : G → ℝ≥0∞ := fun ν =>
  (ENNReal.ofReal C * discreteEDelta ν + ‖t ν‖ₑ) / ENNReal.ofReal L0

/-- The symbol factors through its relative kernel: `h = L (δ₀ + r)`. -/
theorem wienerHighPassSymbol_eq {L : ℂ} (hL : L ≠ 0) (q : ℂ) (t : G → ℂ) :
    wienerHighPassSymbol L q t
      = fun ν => L * (discreteDelta ν + wienerRelativeKernel L q t ν) := by
  funext ν
  rw [wienerHighPassSymbol, wienerRelativeKernel]
  field_simp
  ring

/-- **The coefficientwise domination** — the card's `(15)` input: `|r| ≤ r_*` whenever
`|q| ≤ C` and `L₀ ≤ |L|`. -/
theorem enorm_wienerRelativeKernel_le {L q : ℂ} {t : G → ℂ} {C L0 : ℝ}
    (hq : ‖q‖ₑ ≤ ENNReal.ofReal C) (hL : ENNReal.ofReal L0 ≤ ‖L‖ₑ) (ν : G) :
    ‖wienerRelativeKernel L q t ν‖ₑ ≤ wienerStarKernel C L0 t ν := by
  by_cases hL0 : L = 0
  · simp [wienerRelativeKernel, hL0]
  rw [wienerRelativeKernel, wienerStarKernel]
  have hnum : ‖q * discreteDelta ν + t ν‖ₑ
      ≤ ENNReal.ofReal C * discreteEDelta ν + ‖t ν‖ₑ := by
    refine le_trans (enorm_add_le _ _) ?_
    refine add_le_add ?_ le_rfl
    rw [enorm_mul, enorm_discreteDelta]
    exact mul_le_mul' hq le_rfl
  calc ‖(q * discreteDelta ν + t ν) / L‖ₑ
      = ‖q * discreteDelta ν + t ν‖ₑ / ‖L‖ₑ := by
        rw [enorm_eq_nnnorm, enorm_eq_nnnorm, enorm_eq_nnnorm, nnnorm_div,
          ENNReal.coe_div (nnnorm_ne_zero_iff.mpr hL0)]
    _ ≤ (ENNReal.ofReal C * discreteEDelta ν + ‖t ν‖ₑ) / ENNReal.ofReal L0 :=
        ENNReal.div_le_div hnum hL

/-- **The exact mass of the fixed majorant** — the card's `(14)`:
`‖r_*‖₁ = (C + M)/L₀`. -/
theorem discreteMass_wienerStarKernel (C L0 : ℝ) (t : G → ℂ) :
    discreteMass (wienerStarKernel C L0 t)
      = (ENNReal.ofReal C + discreteMass fun ν => ‖t ν‖ₑ) / ENNReal.ofReal L0 := by
  rw [discreteMass]
  calc ∑' ν, (ENNReal.ofReal C * discreteEDelta ν + ‖t ν‖ₑ) / ENNReal.ofReal L0
      = (∑' ν, (ENNReal.ofReal C * discreteEDelta ν + ‖t ν‖ₑ)) / ENNReal.ofReal L0 := by
        simp only [div_eq_mul_inv]
        rw [ENNReal.tsum_mul_right]
    _ = (ENNReal.ofReal C * discreteMass (discreteEDelta (G := G))
          + discreteMass fun ν => ‖t ν‖ₑ) / ENNReal.ofReal L0 := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_left]
        rfl
    _ = (ENNReal.ofReal C + discreteMass fun ν => ‖t ν‖ₑ) / ENNReal.ofReal L0 := by
        rw [discreteMass_eDelta, mul_one]

/-- Below half the threshold, the majorant mass is below one half — the card's `(14)`. -/
theorem discreteMass_wienerStarKernel_lt_half {C L0 : ℝ} {t : G → ℂ}
    (hL0 : ENNReal.ofReal C + (discreteMass fun ν => ‖t ν‖ₑ)
      < ENNReal.ofReal L0 / 2) :
    discreteMass (wienerStarKernel C L0 t) < 1 / 2 := by
  rw [discreteMass_wienerStarKernel]
  have hL0pos : ENNReal.ofReal L0 ≠ 0 := by
    intro h0
    rw [h0, ENNReal.zero_div] at hL0
    exact absurd hL0 ENNReal.not_lt_zero
  have hL0top : ENNReal.ofReal L0 ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [ENNReal.div_lt_iff (Or.inl hL0pos) (Or.inl hL0top)]
  calc ENNReal.ofReal C + (discreteMass fun ν => ‖t ν‖ₑ)
      < ENNReal.ofReal L0 / 2 := hL0
    _ = 1 / 2 * ENNReal.ofReal L0 := by
        rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul, mul_one]

/-- The Neumann inverse `h⁻¹ = L⁻¹ ∑ₖ (-r)^{⋆k}` — the card's `(16)`. -/
def wienerNeumannInverse (L q : ℂ) (t : G → ℂ) : G → ℂ := fun ν =>
  L⁻¹ * discreteNeumannSeries (wienerRelativeKernel L q t) ν

omit [DecidableEq G] in
theorem discreteConv_const_mul_left (c : ℂ) (α β : G → ℂ) :
    discreteConv (fun ν => c * α ν) β = fun ν => c * discreteConv α β ν := by
  funext ν
  rw [discreteConv, discreteConv, ← tsum_mul_left]
  exact tsum_congr fun μ => by ring

omit [DecidableEq G] in
theorem discreteConv_mul_right (c : ℂ) (α β : G → ℂ) :
    discreteConv α (fun ν => c * β ν) = fun ν => c * discreteConv α β ν := by
  rw [discreteConv_comm, discreteConv_const_mul_left]
  funext ν
  congr 1
  exact congrFun (discreteConv_comm β α) ν

/-- **The Neumann inverse is an actual two-sided convolution inverse** of the high-pass
symbol, for every strictly submassive relative kernel. -/
theorem discreteConv_wienerHighPassSymbol_neumannInverse {L q : ℂ} {t : G → ℂ}
    (hL : L ≠ 0)
    (hr : discreteMass (fun ν => ‖wienerRelativeKernel L q t ν‖ₑ) < 1) :
    discreteConv (wienerHighPassSymbol L q t) (wienerNeumannInverse L q t)
      = discreteDelta := by
  rw [wienerHighPassSymbol_eq hL]
  have h1 : (fun ν => L * (discreteDelta ν + wienerRelativeKernel L q t ν)) =
      fun ν => L * ((fun σ => discreteDelta σ + wienerRelativeKernel L q t σ) ν) := rfl
  rw [h1, discreteConv_const_mul_left]
  have h2 : wienerNeumannInverse L q t
      = fun ν => L⁻¹ * discreteNeumannSeries (wienerRelativeKernel L q t) ν := rfl
  rw [h2]
  funext ν
  rw [discreteConv_mul_right]
  rw [discreteConv_delta_add_neumannSeries hr]
  field_simp

/-- **The uniform coefficient bound** — the card's `(17)`: the Neumann inverse is dominated
coefficientwise by the fixed kernel `L₀⁻¹ K_*`, frequency-independently. -/
theorem enorm_wienerNeumannInverse_le {L q : ℂ} {t : G → ℂ} {C L0 : ℝ}
    (hq : ‖q‖ₑ ≤ ENNReal.ofReal C) (hL : ENNReal.ofReal L0 ≤ ‖L‖ₑ) (ν : G) :
    ‖wienerNeumannInverse L q t ν‖ₑ
      ≤ (ENNReal.ofReal L0)⁻¹
          * discreteNeumannKernel (wienerStarKernel C L0 t) ν := by
  by_cases hL0 : L = 0
  · rw [wienerNeumannInverse]
    simp [hL0]
  rw [wienerNeumannInverse, enorm_mul]
  refine mul_le_mul' ?_
    (enorm_discreteNeumannSeries_le (enorm_wienerRelativeKernel_le hq hL) ν)
  have h1 : ‖L⁻¹‖ₑ = ‖L‖ₑ⁻¹ := by
    rw [enorm_eq_nnnorm, enorm_eq_nnnorm, nnnorm_inv,
      ENNReal.coe_inv (nnnorm_ne_zero_iff.mpr hL0)]
  rw [h1]
  exact ENNReal.inv_le_inv' hL

/-- **The mass of the fixed inverse kernel** — the card's `(18)`:
`‖K‖₁ = L₀⁻¹ (1 - (C+M)/L₀)⁻¹`. -/
theorem discreteMass_wienerInverseKernel (C L0 : ℝ) (t : G → ℂ) :
    discreteMass (fun ν => (ENNReal.ofReal L0)⁻¹
        * discreteNeumannKernel (wienerStarKernel C L0 t) ν)
      = (ENNReal.ofReal L0)⁻¹
          * (1 - (ENNReal.ofReal C + discreteMass fun ν => ‖t ν‖ₑ)
              / ENNReal.ofReal L0)⁻¹ := by
  rw [discreteMass, ENNReal.tsum_mul_left]
  congr 1
  rw [← discreteMass_wienerStarKernel]
  exact discreteMass_neumannKernel _

end GaloisForLFunctions.RHTower
