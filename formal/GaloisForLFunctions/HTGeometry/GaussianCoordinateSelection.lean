import GaloisForLFunctions.HTGeometry.GaussianSignedPermutationInvariance
import GaloisForLFunctions.HTGeometry.PiMeasureAbsoluteContinuity

/-!
# Selecting and rescaling coordinates of a centred product Gaussian

Restricting a product of probability measures to a subfamily of coordinates is the product of that
subfamily, and rescaling each coordinate by a nonzero constant rescales the variance.  A finite
selection of distinct coordinates of a centred product Gaussian, each multiplied by a nonzero
constant, therefore has a law absolutely continuous with respect to Lebesgue measure.
-/

open MeasureTheory ProbabilityTheory

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

section Marginal

variable {ι : Type*} [Fintype ι]

/-- **Marginalizing a product of probability measures.** -/
theorem map_pi_restrict_subtype (p : ι → Prop) [DecidablePred p]
    (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] :
    (Measure.pi μ).map (fun x : ι → ℝ => fun i : {i // p i} => x i.1)
      = Measure.pi fun i : {i // p i} => μ i.1 := by
  classical
  have hMP := measurePreserving_piEquivPiSubtypeProd μ p
  have hfun : (fun x : ι → ℝ => fun i : {i // p i} => x i.1) =
      Prod.fst ∘ (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℝ) p) := by
    funext x i
    rfl
  rw [hfun, ← Measure.map_map measurable_fst
      (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℝ) p).measurable, hMP.map_eq]
  exact Measure.fst_prod

end Marginal

section Scaling

variable {κ : Type*} [Fintype κ]

/-- Rescaling each coordinate of a centred product Gaussian rescales the variances. -/
theorem map_pi_gaussian_scale (c : κ → ℝ) (ν : κ → NNReal) :
    (Measure.pi fun t => gaussianReal 0 (ν t)).map (fun y : κ → ℝ => fun t => c t * y t)
      = Measure.pi fun t => gaussianReal 0 (⟨(c t) ^ 2, sq_nonneg _⟩ * ν t) := by
  classical
  rw [Measure.pi_map_pi fun t => (measurable_const_mul (c t)).aemeasurable]
  refine congrArg Measure.pi (funext fun t => ?_)
  have h := gaussianReal_map_const_mul (μ := (0 : ℝ)) (v := ν t) (c t)
  rw [h, mul_zero]
  congr 1

end Scaling

section Selection

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- **The law of a rescaled selection of distinct coordinates.**  Selecting the coordinates named
by an equivalence with a subtype and rescaling each by a constant produces a centred product
Gaussian with the rescaled variances. -/
theorem map_selection_centredProductGaussian (p : ι → Prop) [DecidablePred p]
    (φ : κ ≃ {i // p i}) (c : κ → ℝ) (v : NNReal) :
    (centredProductGaussian ι v).map
        (fun x : ι → ℝ => fun t : κ => c t * x ((φ t).1))
      = Measure.pi fun t : κ => gaussianReal 0 (⟨(c t) ^ 2, sq_nonneg _⟩ * v) := by
  classical
  have hfun : (fun x : ι → ℝ => fun t : κ => c t * x ((φ t).1)) =
      (fun y : κ → ℝ => fun t => c t * y t) ∘
        ((fun z : {i // p i} → ℝ => fun t : κ => z (φ t)) ∘
          (fun x : ι → ℝ => fun i : {i // p i} => x i.1)) := by
    funext x t
    rfl
  rw [centredProductGaussian, hfun, ← Measure.map_map]
  · rw [← Measure.map_map]
    · rw [map_pi_restrict_subtype p fun _ => gaussianReal 0 v]
      have hperm : ((Measure.pi fun _ : {i // p i} => gaussianReal 0 v).map
          fun z : {i // p i} → ℝ => fun t : κ => z (φ t)) =
          Measure.pi fun _ : κ => gaussianReal 0 v := by
        have hMP := MeasurePreserving.symm
          (MeasurableEquiv.piCongrLeft (fun _ : {i // p i} => ℝ) φ)
          (measurePreserving_piCongrLeft (fun _ : {i // p i} => gaussianReal 0 v) φ)
        have hsymmfun : ⇑(MeasurableEquiv.piCongrLeft (fun _ : {i // p i} => ℝ) φ).symm =
            fun z : {i // p i} → ℝ => fun t : κ => z (φ t) := by
          funext z t
          rfl
        rw [hsymmfun] at hMP
        exact hMP.map_eq
      rw [hperm, map_pi_gaussian_scale c fun _ => v]
    · fun_prop
    · fun_prop
  · fun_prop
  · fun_prop

end Selection

end GaloisForLFunctions.HTGeometry
