import GaloisForLFunctions.HTGeometry.HalfLineSteinRobertson

/-!
# Fourth-curvature mixing and the exact variance excess

Suppose a positive mixture has local zeroth, second, and fourth jets represented as

`p₀ = f²`, `p₂ = f g`, `p₄ = g² + r`.

Then its fourth Hankel curvature is the sum of two independent nonnegative mechanisms: the
Cauchy--Schwarz variance of the quadratic score `g / f`, and the integrated local fourth
curvature `r`.  A pointwise gap `r ≥ κ f²` therefore survives arbitrary positive mixing with
the same normalized gap `κ`.

The theorem is measure- and source-independent.  Its theta-source specialization is used in the
Riemann-hypothesis tower to transport a pointwise reflection-curvature estimate through the
Hedenmalm center mixture.
-/

open MeasureTheory

namespace GaloisForLFunctions.HilbertMetric

noncomputable section

/-- Exact fourth-curvature decomposition for a positive mixture.  The first bracket is the
Cauchy--Schwarz variance defect; the second is the mixed local fourth-curvature residual. -/
theorem fourthCurvatureMixture_decomposition
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f g r : α → ℝ)
    (hgSq : Integrable (fun x => g x ^ 2) μ)
    (hr : Integrable r μ) :
    (∫ x, f x ^ 2 ∂μ) * (∫ x, g x ^ 2 + r x ∂μ) -
        (∫ x, f x * g x ∂μ) ^ 2 =
      ((∫ x, f x ^ 2 ∂μ) * (∫ x, g x ^ 2 ∂μ) -
        (∫ x, f x * g x ∂μ) ^ 2) +
      (∫ x, f x ^ 2 ∂μ) * (∫ x, r x ∂μ) := by
  rw [integral_add hgSq hr]
  ring

/-- **Fourth-curvature mixing law.**  A uniform pointwise residual gap survives arbitrary
positive mixing.  No normalization of the measure is required. -/
theorem fourthCurvatureMixture_gap_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f g r : α → ℝ) (κ : ℝ)
    (hfMeas : AEStronglyMeasurable f μ)
    (hgMeas : AEStronglyMeasurable g μ)
    (hfSq : Integrable (fun x => f x ^ 2) μ)
    (hgSq : Integrable (fun x => g x ^ 2) μ)
    (hr : Integrable r μ)
    (hgap : ∀ᵐ x ∂μ, κ * f x ^ 2 ≤ r x) :
    κ * (∫ x, f x ^ 2 ∂μ) ^ 2 ≤
      (∫ x, f x ^ 2 ∂μ) * (∫ x, g x ^ 2 + r x ∂μ) -
        (∫ x, f x * g x ∂μ) ^ 2 := by
  let A := ∫ x, f x ^ 2 ∂μ
  let B := ∫ x, g x ^ 2 ∂μ
  let C := ∫ x, f x * g x ∂μ
  let R := ∫ x, r x ∂μ
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact integral_nonneg fun x => sq_nonneg (f x)
  have hcs : C ^ 2 ≤ A * B := by
    dsimp only [A, B, C]
    exact HTGeometry.sq_integral_mul_le_integral_sq_mul_integral_sq
      hfMeas hgMeas hfSq hgSq
  have hκf : Integrable (fun x => κ * f x ^ 2) μ := hfSq.const_mul κ
  have hR : κ * A ≤ R := by
    dsimp only [A, R]
    rw [← integral_const_mul]
    exact integral_mono_ae hκf hr hgap
  have hscaled : κ * A ^ 2 ≤ A * R := by
    nlinarith [mul_le_mul_of_nonneg_left hR hA]
  rw [fourthCurvatureMixture_decomposition f g r hgSq hr]
  dsimp only [A, B, C, R] at hcs hscaled ⊢
  linarith

/-- Strict form of the universal mixing law.  A positive local gap and nonzero mixed mass force
a strict fourth Hankel curvature after mixing. -/
theorem fourthCurvatureMixture_pos
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f g r : α → ℝ) (κ : ℝ)
    (hfMeas : AEStronglyMeasurable f μ)
    (hgMeas : AEStronglyMeasurable g μ)
    (hfSq : Integrable (fun x => f x ^ 2) μ)
    (hgSq : Integrable (fun x => g x ^ 2) μ)
    (hr : Integrable r μ)
    (hgap : ∀ᵐ x ∂μ, κ * f x ^ 2 ≤ r x)
    (hκ : 0 < κ)
    (hmass : 0 < ∫ x, f x ^ 2 ∂μ) :
    0 < (∫ x, f x ^ 2 ∂μ) * (∫ x, g x ^ 2 + r x ∂μ) -
      (∫ x, f x * g x ∂μ) ^ 2 := by
  have hbound := fourthCurvatureMixture_gap_le
    f g r κ hfMeas hgMeas hfSq hgSq hr hgap
  have hstrict : 0 < κ * (∫ x, f x ^ 2 ∂μ) ^ 2 :=
    mul_pos hκ (sq_pos_of_pos hmass)
  exact hstrict.trans_le hbound

end

end GaloisForLFunctions.HilbertMetric
