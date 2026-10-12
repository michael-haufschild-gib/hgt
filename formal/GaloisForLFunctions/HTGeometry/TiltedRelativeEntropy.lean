import Mathlib.InformationTheory.KullbackLeibler.Basic

/-! Exact relative entropy between two exponential tilts of one probability law. -/

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
  (f g : X → ℝ)

omit [IsProbabilityMeasure μ] in
theorem tilted_absolutelyContinuous_tilted
    (hg : Integrable (fun x => Real.exp (g x)) μ) :
    μ.tilted f ≪ μ.tilted g :=
  (tilted_absolutelyContinuous μ f).trans (absolutelyContinuous_tilted hg)

theorem llr_tilted_tilted
    (hf : Integrable (fun x => Real.exp (f x)) μ)
    (hg : Integrable (fun x => Real.exp (g x)) μ) :
    llr (μ.tilted f) (μ.tilted g) =ᵐ[μ.tilted f]
      fun x => f x - g x - Real.log (∫ z, Real.exp (f z) ∂μ) +
        Real.log (∫ z, Real.exp (g z) ∂μ) := by
  letI := isProbabilityMeasure_tilted hf
  have hleft := (tilted_absolutelyContinuous μ f).ae_le
    (log_rnDeriv_tilted_left_self hf)
  have hright := llr_tilted_right (tilted_absolutelyContinuous μ f) hg
  filter_upwards [hleft, hright] with x hx hy
  change llr (μ.tilted f) μ x = _ at hx
  rw [hy, hx]
  ring

theorem integrable_llr_tilted_tilted
    (hf : Integrable (fun x => Real.exp (f x)) μ)
    (hg : Integrable (fun x => Real.exp (g x)) μ)
    (hfg : Integrable (fun x => f x - g x) (μ.tilted f)) :
    Integrable (llr (μ.tilted f) (μ.tilted g)) (μ.tilted f) := by
  letI := isProbabilityMeasure_tilted hf
  exact ((hfg.sub (integrable_const _)).add (integrable_const _)).congr
    (llr_tilted_tilted μ f g hf hg).symm

theorem integral_llr_tilted_tilted
    (hf : Integrable (fun x => Real.exp (f x)) μ)
    (hg : Integrable (fun x => Real.exp (g x)) μ)
    (hfg : Integrable (fun x => f x - g x) (μ.tilted f)) :
    (∫ x, llr (μ.tilted f) (μ.tilted g) x ∂(μ.tilted f)) =
      (∫ x, f x - g x ∂(μ.tilted f)) - Real.log (∫ z, Real.exp (f z) ∂μ) +
        Real.log (∫ z, Real.exp (g z) ∂μ) := by
  letI := isProbabilityMeasure_tilted hf
  have hsub : Integrable
      (fun x => f x - g x - Real.log (∫ z, Real.exp (f z) ∂μ)) (μ.tilted f) :=
    hfg.sub (integrable_const _)
  rw [integral_congr_ae (llr_tilted_tilted μ f g hf hg),
    integral_add hsub
      (integrable_const (Real.log (∫ z, Real.exp (g z) ∂μ))),
    integral_sub hfg (integrable_const (Real.log (∫ z, Real.exp (f z) ∂μ)))]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]

theorem klDiv_tilted_tilted_eq
    (hf : Integrable (fun x => Real.exp (f x)) μ)
    (hg : Integrable (fun x => Real.exp (g x)) μ)
    (hfg : Integrable (fun x => f x - g x) (μ.tilted f)) :
    klDiv (μ.tilted f) (μ.tilted g) = ENNReal.ofReal
      ((∫ x, f x - g x ∂(μ.tilted f)) - Real.log (∫ z, Real.exp (f z) ∂μ) +
        Real.log (∫ z, Real.exp (g z) ∂μ)) := by
  letI := isProbabilityMeasure_tilted hf
  letI := isProbabilityMeasure_tilted hg
  rw [klDiv_of_ac_of_integrable (tilted_absolutelyContinuous_tilted μ f g hg)
    (integrable_llr_tilted_tilted μ f g hf hg hfg),
    integral_llr_tilted_tilted μ f g hf hg hfg]
  simp only [probReal_univ, add_sub_cancel_right]

theorem toReal_klDiv_tilted_tilted_eq
    (hf : Integrable (fun x => Real.exp (f x)) μ)
    (hg : Integrable (fun x => Real.exp (g x)) μ)
    (hfg : Integrable (fun x => f x - g x) (μ.tilted f)) :
    (klDiv (μ.tilted f) (μ.tilted g)).toReal =
      (∫ x, f x - g x ∂(μ.tilted f)) - Real.log (∫ z, Real.exp (f z) ∂μ) +
        Real.log (∫ z, Real.exp (g z) ∂μ) := by
  letI := isProbabilityMeasure_tilted hf
  letI := isProbabilityMeasure_tilted hg
  rw [toReal_klDiv (tilted_absolutelyContinuous_tilted μ f g hg)
    (integrable_llr_tilted_tilted μ f g hf hg hfg),
    integral_llr_tilted_tilted μ f g hf hg hfg]
  simp only [probReal_univ, add_sub_cancel_right]

end GaloisForLFunctions.HTGeometry
