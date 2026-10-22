import GaloisForLFunctions.RHTower.FieldOnePadicMultiplicativeHaarDecomposition
import GaloisForLFunctions.RHTower.FieldOnePadicBruhatFourierSelfMap
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

/-!
# Dilation covariance of the `p`-adic Fourier transform

On `ℚ_p` with additive Haar measure normalized by `μ(ℤ_p) = 1`, multiplication by a unit `a`
scales the measure by the Haar modulus `distribHaarChar ℚ_p a`, which equals `|a|_p`. This
module defines the dilation `f ↦ f(a ·)` of compactly supported locally constant functions and
proves the scaling rule `∫ h(a x) dx = |a|_p^(-1) ∫ h(x) dx`. It deduces the Fourier dilation law
`(f(a ·))^(y) = |a|_p^(-1) f̂(a^(-1) y)`, and for `a = p^m` the explicit form
`(f(p^m ·))^(y) = p^m f̂(p^(-m) y)`.

## Main results

- `fieldOnePadicBruhatDilation`: the dilation `x ↦ f(a x)` on Bruhat–Schwartz functions.
- `fieldOnePadicUnitBallNormalizedHaar_domSMul`: dilating the Haar measure by `a` multiplies it
  by `distribHaarChar ℚ_p a`.
- `fieldOnePadic_integral_mul_left`: `∫ h(a x) dx = (distribHaarChar a)^(-1) ∫ h(x) dx`.
- `fieldOnePadicBruhatFourier_dilation`: the Fourier transform of `f(a ·)` at `y` is
  `(distribHaarChar a)^(-1) f̂(a^(-1) y)`.
- `fieldOnePadicBruhatFourier_primeZPowDilation`: for `a = p^m`, `m ∈ ℤ`, it is `p^m f̂(p^(-m) y)`.

## Hypotheses

All results are unconditional; `p` is a prime (`[Fact p.Prime]`), `a` a unit of `ℚ_p`, and
`h : ℚ_p → ℂ` arbitrary.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open MeasureTheory MeasureTheory.Measure Set TopologicalSpace
open scoped ENNReal NNReal Pointwise

variable (p : ℕ) [Fact p.Prime]


/-- Dilation of a compactly supported locally constant function on `ℚ_p` by a unit `a`: `x ↦ f(a x)`. -/
def fieldOnePadicBruhatDilation (a : ℚ_[p]ˣ)
    (f : compactlySupportedLocallyConstant ℚ_[p]) :
    compactlySupportedLocallyConstant ℚ_[p] :=
  let h := Homeomorph.smul a (α := ℚ_[p])
  ⟨LocallyConstant.comap ⟨h, h.continuous⟩ f.1,
    f.2.comp_homeomorph h⟩

@[simp] theorem fieldOnePadicBruhatDilation_apply
    (a : ℚ_[p]ˣ) (f : compactlySupportedLocallyConstant ℚ_[p])
    (x : ℚ_[p]) :
    (fieldOnePadicBruhatDilation p a f).1 x = f.1 ((a : ℚ_[p]) * x) :=
  rfl

/-- Pulling back the normalized Haar measure of `ℚ_p` along multiplication by `a` multiplies it by the
Haar modulus `distribHaarChar ℚ_p a`. -/
theorem fieldOnePadicUnitBallNormalizedHaar_domSMul
    (a : ℚ_[p]ˣ) :
    DomMulAct.mk a • fieldOnePadicUnitBallNormalizedHaar p =
      (distribHaarChar ℚ_[p] a) •
        fieldOnePadicUnitBallNormalizedHaar p := by
  let μ := fieldOnePadicUnitBallNormalizedHaar p
  calc
    DomMulAct.mk a • μ =
        addHaarScalarFactor (DomMulAct.mk a • μ) μ • μ :=
      isAddLeftInvariant_eq_smul_of_regular (DomMulAct.mk a • μ) μ
    _ = (distribHaarChar ℚ_[p] a) • μ := by
      rw [addHaarScalarFactor_smul_eq_distribHaarChar]

/-- Change of variables for dilations of `ℚ_p`: `∫ h(a x) dx = (distribHaarChar a)^(-1) ∫ h(x) dx` for any
`h : ℚ_p → ℂ`. -/
theorem fieldOnePadic_integral_mul_left
    (a : ℚ_[p]ˣ) (h : ℚ_[p] → ℂ) :
    ∫ x, h ((a : ℚ_[p]) * x)
        ∂fieldOnePadicUnitBallNormalizedHaar p =
      ((distribHaarChar ℚ_[p] a)⁻¹ : ℝ≥0) •
        ∫ x, h x ∂fieldOnePadicUnitBallNormalizedHaar p := by
  let μ := fieldOnePadicUnitBallNormalizedHaar p
  calc
    ∫ x, h ((a : ℚ_[p]) * x) ∂μ =
        ∫ x, h x ∂(DomMulAct.mk a⁻¹ • μ) := by
      rw [integral_domSMul]
      congr 1
    _ = ∫ x, h x ∂((distribHaarChar ℚ_[p] a⁻¹) • μ) := by
      rw [fieldOnePadicUnitBallNormalizedHaar_domSMul]
    _ = (distribHaarChar ℚ_[p] a⁻¹ : ℝ≥0) • ∫ x, h x ∂μ := by
      rw [integral_smul_nnreal_measure]
    _ = ((distribHaarChar ℚ_[p] a)⁻¹ : ℝ≥0) • ∫ x, h x ∂μ := by
      rw [map_inv]

/-- Fourier dilation law on `ℚ_p`: the Fourier transform of `x ↦ f(a x)` at `y` equals
`(distribHaarChar a)^(-1) f̂(a^(-1) y)`. -/
theorem fieldOnePadicBruhatFourier_dilation
    (a : ℚ_[p]ˣ) (f : compactlySupportedLocallyConstant ℚ_[p])
    (y : ℚ_[p]) :
    fieldOnePadicBruhatFourier p (fieldOnePadicBruhatDilation p a f) y =
      ((distribHaarChar ℚ_[p] a)⁻¹ : ℝ≥0) •
        fieldOnePadicBruhatFourier p f ((a⁻¹ : ℚ_[p]ˣ) * y) := by
  let h : ℚ_[p] → ℂ := fun t =>
    fieldOnePadicStandardAddChar p
      (-(((a⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) * t * y)) * f.1 t
  have hscale (x : ℚ_[p]) :
      h ((a : ℚ_[p]) * x) =
        fieldOnePadicStandardAddChar p (-(x * y)) *
          (fieldOnePadicBruhatDilation p a f).1 x := by
    dsimp [h]
    congr 2
    have ha0 : (a : ℚ_[p]) ≠ 0 := Units.ne_zero a
    rw [Units.val_inv_eq_inv_val,
      ← mul_assoc ((a : ℚ_[p])⁻¹) (a : ℚ_[p]) x,
      inv_mul_cancel₀ ha0, one_mul]
  rw [fieldOnePadicBruhatFourier]
  simp_rw [← hscale]
  rw [fieldOnePadic_integral_mul_left]
  congr 1
  unfold fieldOnePadicBruhatFourier
  apply integral_congr_ae
  filter_upwards [] with t
  dsimp [h]
  congr 2
  ring

/-- The Haar modulus of `p^m` on `ℚ_p` is `p^(-m)`. -/
theorem fieldOnePadicPrimeZPowUnit_distribHaarChar (m : ℤ) :
    distribHaarChar ℚ_[p] ((fieldOnePadicPrimeUnit p) ^ m) =
      (p : ℝ≥0) ^ (-m) := by
  rw [map_zpow, fieldOnePadicPrimeUnit_distribHaarChar]
  rw [inv_zpow, zpow_neg]

/-- Fourier dilation by a power of `p`: the Fourier transform of `x ↦ f(p^m x)` at `y` equals
`p^m f̂(p^(-m) y)`, for every `m ∈ ℤ`. -/
theorem fieldOnePadicBruhatFourier_primeZPowDilation
    (m : ℤ) (f : compactlySupportedLocallyConstant ℚ_[p])
    (y : ℚ_[p]) :
    fieldOnePadicBruhatFourier p
        (fieldOnePadicBruhatDilation p ((fieldOnePadicPrimeUnit p) ^ m) f) y =
      ((p : ℝ≥0) ^ m) •
        fieldOnePadicBruhatFourier p f
          (((fieldOnePadicPrimeUnit p) ^ (-m) : ℚ_[p]ˣ) * y) := by
  rw [fieldOnePadicBruhatFourier_dilation,
    fieldOnePadicPrimeZPowUnit_distribHaarChar]
  simp only [zpow_neg, inv_inv]

end
end GaloisForLFunctions.RHTower

