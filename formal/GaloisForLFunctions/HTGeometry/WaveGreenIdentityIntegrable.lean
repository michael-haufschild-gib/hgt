import GaloisForLFunctions.HTGeometry.WaveEnergyGreenIdentity

/-!
# The Green identity without compact support

The Green identity of the energy layer was proved for compactly supported fields, which is what a
cut-off potential supplies but *not* what a Fourier synthesis supplies: the probes the corpus
constructs decay, they do not vanish outside a compact set. mathlib's integration by parts asks only
for the three relevant products to be integrable, so the identity holds in that generality, with the
differentiability supplied by smoothness alone.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

open scoped ContDiff

section Integrable

variable {d : ℕ} {f g : (Fin d → ℝ) → ℝ}

/-- **Integration by parts on a spatial slice, for integrable data.** -/
theorem integral_mul_coordPartial_of_integrable (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (i : Fin d)
    (h1 : Integrable (fun x : Fin d → ℝ => coordPartial i f x * g x)
      (volume : Measure (Fin d → ℝ)))
    (h2 : Integrable (fun x : Fin d → ℝ => f x * coordPartial i g x)
      (volume : Measure (Fin d → ℝ)))
    (h3 : Integrable (fun x : Fin d → ℝ => f x * g x) (volume : Measure (Fin d → ℝ))) :
    (∫ x : Fin d → ℝ, f x * coordPartial i g x)
      = -∫ x : Fin d → ℝ, coordPartial i f x * g x := by
  have hmain : (∫ x : Fin d → ℝ, f x * fderiv ℝ g x (Pi.single i (1 : ℝ)))
      = -∫ x : Fin d → ℝ, fderiv ℝ f x (Pi.single i (1 : ℝ)) * g x :=
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (μ := (volume : Measure (Fin d → ℝ))) (v := Pi.single i (1 : ℝ)) h1 h2 h3
      (fun x _ => differentiableAt_of_contDiff_infty hf x)
      (fun x _ => differentiableAt_of_contDiff_infty hg x)
  exact hmain

/-- **The Green identity for integrable data.** -/
theorem integral_laplacian_mul_of_integrable (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (h1 : ∀ i : Fin d, Integrable
      (fun x : Fin d → ℝ => coordPartial i (coordPartial i f) x * g x)
      (volume : Measure (Fin d → ℝ)))
    (h2 : ∀ i : Fin d, Integrable
      (fun x : Fin d → ℝ => coordPartial i f x * coordPartial i g x)
      (volume : Measure (Fin d → ℝ)))
    (h3 : ∀ i : Fin d, Integrable
      (fun x : Fin d → ℝ => coordPartial i f x * g x) (volume : Measure (Fin d → ℝ))) :
    (∫ x : Fin d → ℝ, (∑ i : Fin d, coordPartial i (coordPartial i f) x) * g x)
      = -∑ i : Fin d, ∫ x : Fin d → ℝ, coordPartial i f x * coordPartial i g x := by
  have hterm : ∀ i : Fin d,
      (∫ x : Fin d → ℝ, coordPartial i (coordPartial i f) x * g x)
        = -∫ x : Fin d → ℝ, coordPartial i f x * coordPartial i g x := by
    intro i
    have hcomm₁ : (fun x : Fin d → ℝ => coordPartial i (coordPartial i f) x * g x)
        = fun x : Fin d → ℝ => g x * coordPartial i (coordPartial i f) x := by
      funext x
      ring
    have hcomm₂ : (fun x : Fin d → ℝ => coordPartial i g x * coordPartial i f x)
        = fun x : Fin d → ℝ => coordPartial i f x * coordPartial i g x := by
      funext x
      ring
    have h := integral_mul_coordPartial_of_integrable (f := g) (g := coordPartial i f) hg
      (contDiff_coordPartial hf i) i
      (by
        have := h2 i
        refine this.congr (Filter.Eventually.of_forall fun x => ?_)
        ring)
      (by
        have := h1 i
        refine this.congr (Filter.Eventually.of_forall fun x => ?_)
        ring)
      (by
        have := h3 i
        refine this.congr (Filter.Eventually.of_forall fun x => ?_)
        ring)
    rw [hcomm₁]
    rw [h, hcomm₂]
  have hsum : (∫ x : Fin d → ℝ, (∑ i : Fin d, coordPartial i (coordPartial i f) x) * g x)
      = ∑ i : Fin d, ∫ x : Fin d → ℝ, coordPartial i (coordPartial i f) x * g x := by
    have hexp : (fun x : Fin d → ℝ => (∑ i : Fin d, coordPartial i (coordPartial i f) x) * g x)
        = fun x : Fin d → ℝ => ∑ i : Fin d, coordPartial i (coordPartial i f) x * g x := by
      funext x
      rw [Finset.sum_mul]
    rw [hexp]
    exact integral_finsetSum Finset.univ fun i _ => h1 i
  rw [hsum, Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_neg_distrib]

end Integrable

end GaloisForLFunctions.HTGeometry
