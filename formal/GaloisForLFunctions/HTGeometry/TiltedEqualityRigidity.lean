import Mathlib.MeasureTheory.Measure.Tilted

/-! Equality of exponential tilts is precisely an almost-everywhere additive gauge. -/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

theorem tilted_eq_iff_sub_ae_const {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (f g : X → ℝ)
    (hf : Integrable (fun x => Real.exp (f x)) μ)
    (hg : Integrable (fun x => Real.exp (g x)) μ) :
    μ.tilted f = μ.tilted g ↔ ∃ c : ℝ, ∀ᵐ x ∂μ, f x - g x = c := by
  constructor
  · intro heq
    refine ⟨Real.log (∫ x, Real.exp (f x) ∂μ) -
      Real.log (∫ x, Real.exp (g x) ∂μ), ?_⟩
    have hleft := log_rnDeriv_tilted_left_self hf
    rw [heq] at hleft
    filter_upwards [hleft, log_rnDeriv_tilted_left_self hg] with x hx hy
    linarith
  · rintro ⟨c, hc⟩
    letI := isProbabilityMeasure_tilted hg
    have hfg : f =ᵐ[μ] g + (fun _ => c) := by
      filter_upwards [hc] with x hx
      change f x = g x + c
      linarith
    calc
      μ.tilted f = μ.tilted (g + (fun _ => c)) := tilted_congr hfg
      _ = (μ.tilted g).tilted (fun _ => c) := (tilted_tilted hg _).symm
      _ = μ.tilted g := tilted_const _ c

end GaloisForLFunctions.HTGeometry
