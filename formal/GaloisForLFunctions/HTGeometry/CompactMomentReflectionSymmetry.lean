import GaloisForLFunctions.HTGeometry.CarriedConclusion

/-!
# Reflection symmetry from compact moments

A finite measure carried by a symmetric compact interval is reflection-invariant as soon as all
of its reflected moments agree with its original moments.  Compact determinacy turns this purely
moment-level certificate into equality of measures.
-/

open MeasureTheory Set

namespace HTGeometry

/-- Compact support and reflection-invariant moments force reflection invariance of the measure. -/
theorem map_neg_eq_self_of_compact_moments
    {μ : Measure ℝ} [IsFiniteMeasure μ] {R : ℝ} (hR : 0 < R)
    (hcarried : μ (Icc (-R) R)ᶜ = 0)
    (hint : ∀ k : ℕ, Integrable (fun x : ℝ => x ^ k) μ)
    (hmom : ∀ k : ℕ,
      (∫ x : ℝ, (-x) ^ k ∂μ) = ∫ x : ℝ, x ^ k ∂μ) :
    Measure.map (fun x : ℝ => -x) μ = μ := by
  let ν : Measure ℝ := Measure.map (fun x : ℝ => -x) μ
  have hpres : MeasurePreserving (fun x : ℝ => -x) μ ν :=
    ⟨measurable_neg, rfl⟩
  have hintν : ∀ k : ℕ, Integrable (fun x : ℝ => x ^ k) ν := by
    intro k
    apply (hpres.integrable_comp (continuous_pow k).aestronglyMeasurable).mp
    have hneg : Integrable (fun x : ℝ => (-1 : ℝ) ^ k * x ^ k) μ :=
      (hint k).const_mul ((-1 : ℝ) ^ k)
    convert hneg using 1
    funext x
    change (-x) ^ k = (-1 : ℝ) ^ k * x ^ k
    rw [show -x = (-1 : ℝ) * x by ring, mul_pow]
  have heq : μ = ν := measure_eq_of_moments_eq_of_one_carried
    (s := fun k => ∫ x : ℝ, x ^ k ∂μ) (c := 0) (r := R) hR
    (by simpa using hcarried)
    (fun _ => rfl) hint
    (fun k => by
      calc
        (∫ x : ℝ, x ^ k ∂μ) = ∫ x : ℝ, (-x) ^ k ∂μ := (hmom k).symm
        _ = ∫ x : ℝ, x ^ k ∂ν := by
          rw [integral_map measurable_neg.aemeasurable
            (continuous_pow k).aestronglyMeasurable])
    hintν
  exact heq.symm

/-- An odd real integrand has zero integral against a reflection-invariant measure. -/
theorem integral_eq_zero_of_map_neg_eq_self
    {μ : Measure ℝ} {f : ℝ → ℝ}
    (hmap : Measure.map (fun x : ℝ => -x) μ = μ)
    (hf : AEStronglyMeasurable f μ) (hodd : ∀ x, f (-x) = -f x) :
    (∫ x, f x ∂μ) = 0 := by
  have hfmap : AEStronglyMeasurable f (Measure.map (fun x : ℝ => -x) μ) := by
    rw [hmap]
    exact hf
  have hreflect : (∫ x, f (-x) ∂μ) = ∫ x, f x ∂μ := by
    calc
      (∫ x, f (-x) ∂μ) = ∫ x, f x ∂Measure.map (fun x : ℝ => -x) μ := by
        simpa [Function.comp_apply] using
          (integral_map measurable_neg.aemeasurable hfmap).symm
      _ = ∫ x, f x ∂μ := by rw [hmap]
  have hneg : (∫ x, f (-x) ∂μ) = -(∫ x, f x ∂μ) := by
    rw [integral_congr_ae (ae_of_all μ hodd), integral_neg]
  linarith

end HTGeometry
