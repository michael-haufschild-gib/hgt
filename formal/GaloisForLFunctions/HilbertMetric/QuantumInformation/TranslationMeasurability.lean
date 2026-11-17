import GaloisForLFunctions.HilbertMetric.QuantumInformation.TranslationWeakAverage
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner


/-!
# Weak and strong measurability of counting-measure translations

Each scalar translation coefficient is integrable and vanishes almost
everywhere. A nonzero orbit nevertheless fails almost-everywhere strong
measurability, even on the averaging interval: separable essential range
would place a nonzero orbit vector in a subspace orthogonal to itself.
This distinguishes weak averaging from Bochner averaging in the
singularising-channel construction.
-/

noncomputable section
open MeasureTheory
namespace GaloisForLFunctions.HilbertMetric.ShiftAverage

/-- Every fixed-vector translation coefficient is genuinely integrable. -/
theorem shift_inner_integrable (u v : Space) :
    Integrable (fun t : ℝ => inner ℂ (shift t u) v) :=
  (integrable_congr (shift_inner_ae_zero u v)).mpr (integrable_zero ℝ ℂ volume)

private theorem zero_of_stronglyMeasurable_weak_zero
    (μ : Measure ℝ) [NeZero μ] (u : Space)
    (hm : AEStronglyMeasurable (fun t : ℝ => shift t u) μ)
    (hw : ∀ v : Space, (fun t : ℝ => inner ℂ (shift t u) v) =ᵐ[μ] 0) : u = 0 := by
  obtain ⟨S, hS, hmem⟩ := hm.isSeparable_ae_range
  obtain ⟨C, hC, hSC⟩ := hS
  letI : Countable C := hC.to_subtype
  have hc : ∀ᵐ t ∂μ, ∀ v : C, inner ℂ (shift t u) v.val = 0 :=
    ae_all_iff.mpr fun v => hw v.val
  have hz : ∀ᵐ t ∂μ, inner ℂ (shift t u) (shift t u) = 0 := by
    filter_upwards [hc, hmem] with t ht hs
    have hclosed : IsClosed {v : Space | inner ℂ (shift t u) v = 0} :=
      isClosed_eq (continuous_const.inner continuous_id) continuous_const
    have hclosure : closure C ⊆ {v : Space | inner ℂ (shift t u) v = 0} :=
      hclosed.closure_subset_iff.mpr fun v hv => ht ⟨v, hv⟩
    exact hclosure (hSC hs)
  obtain ⟨t, ht⟩ := hz.exists
  rw [inner_self_eq_norm_sq_to_K, norm_shift] at ht
  have hnorm := congrArg Complex.re ht
  simp only [← Complex.ofReal_pow, Complex.ofReal_re, Complex.zero_re] at hnorm
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm)

/-- A translation orbit is almost everywhere strongly measurable exactly when its vector is zero. -/
theorem shift_aestronglyMeasurable_iff (u : Space) :
    AEStronglyMeasurable (fun t : ℝ => shift t u) volume ↔ u = 0 := by
  constructor
  · intro h
    exact zero_of_stronglyMeasurable_weak_zero volume u h (shift_inner_ae_zero u)
  · rintro rfl
    simpa only [map_zero] using
      (aestronglyMeasurable_const : AEStronglyMeasurable (fun _ : ℝ => (0 : Space)) volume)

/-- Restricting to the normalized averaging interval does not restore strong measurability. -/
theorem shift_interval_aestronglyMeasurable_iff (u : Space) :
    AEStronglyMeasurable (fun t : ℝ => shift t u)
      (volume.restrict (Set.Ioc 0 1)) ↔ u = 0 := by
  haveI : NeZero (volume.restrict (Set.Ioc (0 : ℝ) 1)) := ⟨by
    intro h
    have he := congrArg (fun μ : Measure ℝ => μ Set.univ) h
    simp at he⟩
  constructor
  · intro h
    exact zero_of_stronglyMeasurable_weak_zero _ u h
      (fun v => ae_restrict_of_ae (shift_inner_ae_zero u v))
  · rintro rfl
    simpa only [map_zero] using (aestronglyMeasurable_const :
      AEStronglyMeasurable (fun _ : ℝ => (0 : Space)) (volume.restrict (Set.Ioc 0 1)))

/-- Weak coefficient integrability does not imply Bochner integrability of a nonzero orbit. -/
theorem shift_interval_integrable_iff (u : Space) :
    IntegrableOn (fun t : ℝ => shift t u) (Set.Ioc 0 1) ↔ u = 0 := by
  constructor
  · intro h
    exact (shift_interval_aestronglyMeasurable_iff u).mp h.aestronglyMeasurable
  · rintro rfl
    simp only [map_zero]
    exact ⟨aestronglyMeasurable_const, by simp [HasFiniteIntegral]⟩

#print axioms shift_inner_integrable
#print axioms shift_aestronglyMeasurable_iff
#print axioms shift_interval_aestronglyMeasurable_iff
#print axioms shift_interval_integrable_iff
end GaloisForLFunctions.HilbertMetric.ShiftAverage
