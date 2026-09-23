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

The strict theorem does not need a uniform quantitative gap.  If the local `2 x 2` Hankel field is
strictly positive almost everywhere and its mixed zeroth mass is positive, integration preserves
strict positive definiteness.  This is the exact qualitative interface used by the theta source.
-/

open MeasureTheory

namespace GaloisForLFunctions.HilbertMetric

noncomputable section

/-- Sylvester's criterion in quadratic-form coordinates for a real symmetric `2 x 2` matrix. -/
theorem twoByTwoQuadratic_pos_of_first_det
    {p0 p2 p4 x y : ℝ} (hp0 : 0 < p0) (hdet : 0 < p0 * p4 - p2 ^ (2 : ℕ))
    (hy : y ≠ 0) :
    0 < p0 * x ^ (2 : ℕ) + 2 * p2 * x * y + p4 * y ^ (2 : ℕ) := by
  have hgap : 0 < p4 - p2 ^ (2 : ℕ) / p0 := by
    apply (sub_pos).2
    apply (div_lt_iff₀ hp0).2
    nlinarith
  have hid :
      p0 * x ^ (2 : ℕ) + 2 * p2 * x * y + p4 * y ^ (2 : ℕ) =
        p0 * (x + p2 / p0 * y) ^ (2 : ℕ) + (p4 - p2 ^ (2 : ℕ) / p0) * y ^ (2 : ℕ) := by
    field_simp [hp0.ne']
    ring
  rw [hid]
  exact add_pos_of_nonneg_of_pos
    (mul_nonneg hp0.le (sq_nonneg _))
    (mul_pos hgap (sq_pos_of_ne_zero hy))

/-- **Strict positive-matrix mixing law.**  An integrable `2 x 2` Hankel field which is strictly
positive almost everywhere has strictly positive integrated determinant whenever its integrated
first diagonal entry has positive mass.  No uniform pointwise determinant gap is required. -/
theorem integral_twoByTwo_det_pos
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (p0 p2 p4 : α → ℝ)
    (hp0Int : Integrable p0 μ) (hp2Int : Integrable p2 μ)
    (hp4Int : Integrable p4 μ)
    (hmass : 0 < ∫ x, p0 x ∂μ)
    (hpoint : ∀ᵐ x ∂μ, 0 < p0 x ∧ 0 < p0 x * p4 x - p2 x ^ (2 : ℕ)) :
    0 < (∫ x, p0 x ∂μ) * (∫ x, p4 x ∂μ) - (∫ x, p2 x ∂μ) ^ (2 : ℕ) := by
  let A := ∫ x, p0 x ∂μ
  let B := ∫ x, p2 x ∂μ
  let C := ∫ x, p4 x ∂μ
  let Q : α → ℝ := fun x =>
    p0 x * (-B) ^ (2 : ℕ) + 2 * p2 x * (-B) * A + p4 x * A ^ (2 : ℕ)
  have hA : 0 < A := hmass
  have hQint : Integrable Q μ := by
    have h := ((hp0Int.const_mul ((-B) ^ (2 : ℕ))).add
      (hp2Int.const_mul (2 * (-B) * A))).add
      (hp4Int.const_mul (A ^ (2 : ℕ)))
    exact h.congr (ae_of_all _ fun x => by
      dsimp only [Q, Pi.add_apply]
      ring)
  have hQpos : ∀ᵐ x ∂μ, 0 < Q x := by
    filter_upwards [hpoint] with x hx
    exact twoByTwoQuadratic_pos_of_first_det hx.1 hx.2 hA.ne'
  have hQnonneg : 0 ≤ᵐ[μ] Q := hQpos.mono fun _ hx => hx.le
  have hμ : μ ≠ 0 := by
    intro hzero
    apply hmass.ne'
    simp [hzero]
  have hsupport : μ Set.univ ≤ μ (Function.support Q) := by
    apply measure_mono_ae
    filter_upwards [hQpos] with x hx
    intro _
    exact hx.ne'
  have hQintegralPos : 0 < ∫ x, Q x ∂μ := by
    rw [integral_pos_iff_support_of_nonneg_ae hQnonneg hQint]
    exact (MeasureTheory.Measure.measure_univ_pos.mpr hμ).trans_le hsupport
  have hQvalue : (∫ x, Q x ∂μ) = A * (A * C - B ^ (2 : ℕ)) := by
    calc
      (∫ x, Q x ∂μ) =
          ∫ x, (((-B) ^ (2 : ℕ) * p0 x + (2 * (-B) * A) * p2 x) +
            A ^ (2 : ℕ) * p4 x) ∂μ := by
        apply integral_congr_ae
        filter_upwards with x
        dsimp only [Q]
        ring
      _ = (∫ x, ((-B) ^ (2 : ℕ) * p0 x + (2 * (-B) * A) * p2 x) ∂μ) +
          ∫ x, A ^ (2 : ℕ) * p4 x ∂μ :=
        integral_add
          ((hp0Int.const_mul ((-B) ^ (2 : ℕ))).add
            (hp2Int.const_mul (2 * (-B) * A)))
          (hp4Int.const_mul (A ^ (2 : ℕ)))
      _ = ((∫ x, (-B) ^ (2 : ℕ) * p0 x ∂μ) +
            ∫ x, (2 * (-B) * A) * p2 x ∂μ) +
          ∫ x, A ^ (2 : ℕ) * p4 x ∂μ := by
        rw [integral_add (hp0Int.const_mul ((-B) ^ (2 : ℕ)))
          (hp2Int.const_mul (2 * (-B) * A))]
      _ = A * (A * C - B ^ (2 : ℕ)) := by
        rw [integral_const_mul, integral_const_mul, integral_const_mul]
        dsimp only [A, B, C]
        ring
  rw [hQvalue] at hQintegralPos
  dsimp only [A, B, C] at hA hQintegralPos ⊢
  nlinarith

/-- Exact fourth-curvature decomposition for a positive mixture.  The first bracket is the
Cauchy--Schwarz variance defect; the second is the mixed local fourth-curvature residual. -/
theorem fourthCurvatureMixture_decomposition
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f g r : α → ℝ)
    (hgSq : Integrable (fun x => g x ^ (2 : ℕ)) μ)
    (hr : Integrable r μ) :
    (∫ x, f x ^ (2 : ℕ) ∂μ) * (∫ x, g x ^ (2 : ℕ) + r x ∂μ) -
        (∫ x, f x * g x ∂μ) ^ (2 : ℕ) =
      ((∫ x, f x ^ (2 : ℕ) ∂μ) * (∫ x, g x ^ (2 : ℕ) ∂μ) -
        (∫ x, f x * g x ∂μ) ^ (2 : ℕ)) +
      (∫ x, f x ^ (2 : ℕ) ∂μ) * (∫ x, r x ∂μ) := by
  rw [integral_add hgSq hr]
  ring

/-- **Fourth-curvature mixing law.**  A uniform pointwise residual gap survives arbitrary
positive mixing.  No normalization of the measure is required. -/
theorem fourthCurvatureMixture_gap_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f g r : α → ℝ) (κ : ℝ)
    (hfMeas : AEStronglyMeasurable f μ)
    (hgMeas : AEStronglyMeasurable g μ)
    (hfSq : Integrable (fun x => f x ^ (2 : ℕ)) μ)
    (hgSq : Integrable (fun x => g x ^ (2 : ℕ)) μ)
    (hr : Integrable r μ)
    (hgap : ∀ᵐ x ∂μ, κ * f x ^ (2 : ℕ) ≤ r x) :
    κ * (∫ x, f x ^ (2 : ℕ) ∂μ) ^ (2 : ℕ) ≤
      (∫ x, f x ^ (2 : ℕ) ∂μ) * (∫ x, g x ^ (2 : ℕ) + r x ∂μ) -
        (∫ x, f x * g x ∂μ) ^ (2 : ℕ) := by
  let A := ∫ x, f x ^ (2 : ℕ) ∂μ
  let B := ∫ x, g x ^ (2 : ℕ) ∂μ
  let C := ∫ x, f x * g x ∂μ
  let R := ∫ x, r x ∂μ
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact integral_nonneg fun x => sq_nonneg (f x)
  have hcs : C ^ (2 : ℕ) ≤ A * B := by
    dsimp only [A, B, C]
    exact HTGeometry.sq_integral_mul_le_integral_sq_mul_integral_sq
      hfMeas hgMeas hfSq hgSq
  have hκf : Integrable (fun x => κ * f x ^ (2 : ℕ)) μ := hfSq.const_mul κ
  have hR : κ * A ≤ R := by
    dsimp only [A, R]
    rw [← integral_const_mul]
    exact integral_mono_ae hκf hr hgap
  have hscaled : κ * A ^ (2 : ℕ) ≤ A * R := by
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
    (hfSq : Integrable (fun x => f x ^ (2 : ℕ)) μ)
    (hgSq : Integrable (fun x => g x ^ (2 : ℕ)) μ)
    (hr : Integrable r μ)
    (hgap : ∀ᵐ x ∂μ, κ * f x ^ (2 : ℕ) ≤ r x)
    (hκ : 0 < κ)
    (hmass : 0 < ∫ x, f x ^ (2 : ℕ) ∂μ) :
    0 < (∫ x, f x ^ (2 : ℕ) ∂μ) * (∫ x, g x ^ (2 : ℕ) + r x ∂μ) -
      (∫ x, f x * g x ∂μ) ^ (2 : ℕ) := by
  have hbound := fourthCurvatureMixture_gap_le
    f g r κ hfMeas hgMeas hfSq hgSq hr hgap
  have hstrict : 0 < κ * (∫ x, f x ^ (2 : ℕ) ∂μ) ^ (2 : ℕ) :=
    mul_pos hκ (sq_pos_of_pos hmass)
  exact hstrict.trans_le hbound

end

end GaloisForLFunctions.HilbertMetric
