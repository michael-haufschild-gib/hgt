import GaloisForLFunctions.HTGeometry.HalfLineSteinRobertson

/-!
# Fidelity bound for opposite observation channels

Let `ρ` be a nonnegative observable density and let `φ` be a real observation coordinate.
The two static channels obtained by multiplying `ρ` by `exp φ` and `exp (-φ)` obey

`(integral ρ)^(2 : ℕ) ≤ (integral exp(φ) ρ) (integral exp(-φ) ρ)`.

The proof factors `ρ` into the geometric mean of the two channel amplitudes and applies
integral Cauchy--Schwarz.  This is the classical Hellinger/Bhattacharyya core of fidelity
bounds; it is an observability relation and assumes no temporal evolution.
-/

open Real MeasureTheory

namespace HTGeometry

noncomputable section

/-- A nonnegative density is the geometric mean of its two opposite exponential observation
channels.  Integral Cauchy--Schwarz therefore bounds the unweighted observation by their
product. -/
theorem sq_integral_le_exponential_tilt_product
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {φ ρ : α → ℝ}
    (hφ : AEStronglyMeasurable φ μ)
    (hρ : AEStronglyMeasurable ρ μ)
    (hρnonneg : ∀ᵐ x ∂μ, 0 ≤ ρ x)
    (hplus : Integrable (fun x => Real.exp (φ x) * ρ x) μ)
    (hminus : Integrable (fun x => Real.exp (-φ x) * ρ x) μ) :
    (∫ x, ρ x ∂μ) ^ (2 : ℕ) ≤
      (∫ x, Real.exp (φ x) * ρ x ∂μ) *
        ∫ x, Real.exp (-φ x) * ρ x ∂μ := by
  let f : α → ℝ := fun x => Real.exp (φ x / 2) * Real.sqrt (ρ x)
  let g : α → ℝ := fun x => Real.exp (-φ x / 2) * Real.sqrt (ρ x)
  have hsqrt : AEStronglyMeasurable (fun x => Real.sqrt (ρ x)) μ :=
    hρ.aemeasurable.sqrt.aestronglyMeasurable
  have hfmeas : AEStronglyMeasurable f μ := by
    exact ((hφ.aemeasurable.div_const 2).exp.aestronglyMeasurable.mul hsqrt)
  have hgmeas : AEStronglyMeasurable g μ := by
    exact ((hφ.aemeasurable.neg.div_const 2).exp.aestronglyMeasurable.mul hsqrt)
  have hf : Integrable (fun x => f x ^ (2 : ℕ)) μ := by
    apply hplus.congr
    filter_upwards [hρnonneg] with x hx
    dsimp only [f]
    rw [mul_pow, Real.sq_sqrt hx, pow_two, ← Real.exp_add]
    congr 1
    ring
  have hg : Integrable (fun x => g x ^ (2 : ℕ)) μ := by
    apply hminus.congr
    filter_upwards [hρnonneg] with x hx
    dsimp only [g]
    rw [mul_pow, Real.sq_sqrt hx, pow_two, ← Real.exp_add]
    congr 1
    ring
  have hcs := sq_integral_mul_le_integral_sq_mul_integral_sq
    hfmeas hgmeas hf hg
  have hfg : (∫ x, f x * g x ∂μ) = ∫ x, ρ x ∂μ := by
    apply integral_congr_ae
    filter_upwards [hρnonneg] with x hx
    dsimp only [f, g]
    rw [show Real.exp (φ x / 2) * Real.sqrt (ρ x) *
          (Real.exp (-φ x / 2) * Real.sqrt (ρ x)) =
        (Real.exp (φ x / 2) * Real.exp (-φ x / 2)) *
          Real.sqrt (ρ x) ^ (2 : ℕ) by ring,
      Real.sq_sqrt hx, ← Real.exp_add]
    rw [show φ x / 2 + -φ x / 2 = 0 by ring]
    simp
  have hfsq : (∫ x, f x ^ (2 : ℕ) ∂μ) =
      ∫ x, Real.exp (φ x) * ρ x ∂μ := by
    apply integral_congr_ae
    filter_upwards [hρnonneg] with x hx
    dsimp only [f]
    rw [mul_pow, Real.sq_sqrt hx, pow_two, ← Real.exp_add]
    congr 1
    ring
  have hgsq : (∫ x, g x ^ (2 : ℕ) ∂μ) =
      ∫ x, Real.exp (-φ x) * ρ x ∂μ := by
    apply integral_congr_ae
    filter_upwards [hρnonneg] with x hx
    dsimp only [g]
    rw [mul_pow, Real.sq_sqrt hx, pow_two, ← Real.exp_add]
    congr 1
    ring
  rwa [hfg, hfsq, hgsq] at hcs

end

end HTGeometry
