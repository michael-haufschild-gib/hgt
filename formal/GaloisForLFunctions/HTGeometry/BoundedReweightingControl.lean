import GaloisForLFunctions.HTGeometry.FlattenedCauchyJetRigidity

/-!
# Bounded reweightings as a control space

The comeagerness statement lives in the Banach space `L^∞(μ;ℝ)` of bounded reweightings.  This
module supplies the analytic facts needed to realize the Cauchy-jet map on that space.

Mathlib records that an almost-everywhere bound implies an `L^∞` norm bound; the direction needed
here is the converse, that an `L^∞` element is almost everywhere bounded by its norm.  It follows
from the essential-supremum characterization once finiteness of the essential supremum is used to
move across `ENNReal.toReal`.

Against a finite measure this makes the product of a bounded reweighting with the uniformly bounded
Cauchy kernel integrable, with an explicit bound linear in the reweighting norm — exactly what a
continuous control map requires.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

open scoped ENNReal

noncomputable section

instance factOneLeTop : Fact ((1 : ℝ≥0∞) ≤ ⊤) := ⟨le_top⟩

/-- An `L^∞` element is almost everywhere bounded by its norm. -/
theorem ae_norm_le_norm_Lp_top {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : Lp ℝ ⊤ μ) :
    ∀ᵐ t ∂μ, ‖f t‖ ≤ ‖f‖ := by
  have hess := enorm_ae_le_eLpNormEssSup (f : α → ℝ) μ
  have htop : eLpNorm (f : α → ℝ) ⊤ μ = eLpNormEssSup (f : α → ℝ) μ :=
    eLpNorm_exponent_top
  have hfin : eLpNormEssSup (f : α → ℝ) μ ≠ ⊤ := by
    rw [← htop]
    exact (Lp.eLpNorm_lt_top f).ne
  have hnorm : ‖f‖ = (eLpNormEssSup (f : α → ℝ) μ).toReal := by
    rw [Lp.norm_def, htop]
  filter_upwards [hess] with t ht
  rw [hnorm]
  have hle := ENNReal.toReal_mono hfin ht
  simpa using hle

/-- A bounded reweighting multiplied by a uniformly bounded kernel is integrable against a finite
measure. -/
theorem integrable_Lp_top_mul {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (f : Lp ℝ ⊤ μ)
    (g : α → ℂ) (hg : AEStronglyMeasurable g μ) {B : ℝ} (hB : ∀ t, ‖g t‖ ≤ B) :
    Integrable (fun t => ((f t : ℝ) : ℂ) * g t) μ := by
  have hmeas : AEStronglyMeasurable (fun t => ((f t : ℝ) : ℂ) * g t) μ := by
    exact (Complex.continuous_ofReal.comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable f)).mul hg
  refine Integrable.mono' (integrable_const (‖f‖ * B)) hmeas ?_
  filter_upwards [ae_norm_le_norm_Lp_top μ f] with t ht
  have hBnonneg : 0 ≤ B := le_trans (norm_nonneg (g t)) (hB t)
  have hfnonneg : 0 ≤ ‖f‖ := norm_nonneg f
  calc ‖((f t : ℝ) : ℂ) * g t‖
      = ‖f t‖ * ‖g t‖ := by
        rw [norm_mul, Complex.norm_real]
    _ ≤ ‖f‖ * B := by
        exact mul_le_mul ht (hB t) (norm_nonneg _) hfnonneg

/-- The explicit norm bound carried by the pairing of a bounded reweighting with a uniformly
bounded kernel. -/
theorem norm_integral_Lp_top_mul_le {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (f : Lp ℝ ⊤ μ)
    (g : α → ℂ) {B : ℝ} (hB : ∀ t, ‖g t‖ ≤ B) :
    ‖∫ t, ((f t : ℝ) : ℂ) * g t ∂μ‖ ≤ (B * μ.real Set.univ) * ‖f‖ := by
  have hbound : ∀ᵐ t ∂μ, ‖((f t : ℝ) : ℂ) * g t‖ ≤ ‖f‖ * B := by
    filter_upwards [ae_norm_le_norm_Lp_top μ f] with t ht
    calc ‖((f t : ℝ) : ℂ) * g t‖
        = ‖f t‖ * ‖g t‖ := by rw [norm_mul, Complex.norm_real]
      _ ≤ ‖f‖ * B := mul_le_mul ht (hB t) (norm_nonneg _) (norm_nonneg f)
  have := norm_integral_le_of_norm_le_const (C := ‖f‖ * B) hbound
  calc ‖∫ t, ((f t : ℝ) : ℂ) * g t ∂μ‖
      ≤ ‖f‖ * B * μ.real Set.univ := by
        simpa [mul_comm, mul_assoc, mul_left_comm] using this
    _ = (B * μ.real Set.univ) * ‖f‖ := by ring

end

end GaloisForLFunctions.HTGeometry
