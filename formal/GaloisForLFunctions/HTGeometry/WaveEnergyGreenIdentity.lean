import GaloisForLFunctions.HTGeometry.ConformalMetricDalembertian
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# The Green identity on a spatial slice

The energy estimate for the clock equation rests on one integral identity: for compactly supported
fields the Laplacian may be moved off one factor and onto the other, at the price of a sign,

`∫ (∑ᵢ ∂ᵢ∂ᵢ f) · g = -∑ᵢ ∫ ∂ᵢ f · ∂ᵢ g`.

This file proves it from mathlib's directional integration by parts, together with the support and
integrability facts it consumes: a partial derivative of a compactly supported function is again
compactly supported, and a continuous function with compact support is integrable.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

open scoped ContDiff

section Green

variable {d : ℕ}

/-! ## Supports -/

theorem coordPartial_eq_zero_of_eventually {f : (Fin d → ℝ) → ℝ} {x : Fin d → ℝ}
    (h : f =ᶠ[nhds x] fun _ => (0 : ℝ)) (i : Fin d) : coordPartial i f x = 0 := by
  rw [coordPartial, h.fderiv_eq]
  simp

theorem hasCompactSupport_coordPartial {f : (Fin d → ℝ) → ℝ} (hf : HasCompactSupport f)
    (i : Fin d) : HasCompactSupport (coordPartial i f) := by
  refine HasCompactSupport.intro hf.isCompact (K := tsupport f) fun x hx => ?_
  refine coordPartial_eq_zero_of_eventually ?_ i
  exact Filter.eventually_of_mem ((isClosed_tsupport f).isOpen_compl.mem_nhds hx)
    fun y hy => image_eq_zero_of_notMem_tsupport hy

theorem integrable_of_continuous_compactSupport {f : (Fin d → ℝ) → ℝ} (hf : Continuous f)
    (hs : HasCompactSupport f) : Integrable f (volume : Measure (Fin d → ℝ)) :=
  hf.integrable_of_hasCompactSupport hs

/-! ## Integration by parts in one coordinate direction -/

/-- **Integration by parts on a spatial slice.** -/
theorem integral_mul_coordPartial {f g : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (hfs : HasCompactSupport f) (i : Fin d) :
    (∫ x : Fin d → ℝ, f x * coordPartial i g x)
      = -∫ x : Fin d → ℝ, coordPartial i f x * g x := by
  have hfc : Continuous f := hf.continuous
  have hgc : Continuous g := hg.continuous
  have hdf : Continuous (coordPartial i f) := (contDiff_coordPartial hf i).continuous
  have hdg : Continuous (coordPartial i g) := (contDiff_coordPartial hg i).continuous
  have h1 : Integrable (fun x : Fin d → ℝ => fderiv ℝ f x (Pi.single i (1 : ℝ)) * g x)
      (volume : Measure (Fin d → ℝ)) :=
    integrable_of_continuous_compactSupport (hdf.mul hgc)
      ((hasCompactSupport_coordPartial hfs i).mul_right)
  have h2 : Integrable (fun x : Fin d → ℝ => f x * fderiv ℝ g x (Pi.single i (1 : ℝ)))
      (volume : Measure (Fin d → ℝ)) :=
    integrable_of_continuous_compactSupport (hfc.mul hdg) hfs.mul_right
  have h3 : Integrable (fun x : Fin d → ℝ => f x * g x) (volume : Measure (Fin d → ℝ)) :=
    integrable_of_continuous_compactSupport (hfc.mul hgc) hfs.mul_right
  have hmain : (∫ x : Fin d → ℝ, f x * fderiv ℝ g x (Pi.single i (1 : ℝ)))
      = -∫ x : Fin d → ℝ, fderiv ℝ f x (Pi.single i (1 : ℝ)) * g x :=
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (μ := (volume : Measure (Fin d → ℝ))) (v := Pi.single i (1 : ℝ)) h1 h2 h3
      (fun x _ => differentiableAt_of_contDiff_infty hf x)
      (fun x _ => differentiableAt_of_contDiff_infty hg x)
  exact hmain

/-- **The Green identity on a spatial slice.** -/
theorem integral_laplacian_mul {f g : (Fin d → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (hfs : HasCompactSupport f) (hgs : HasCompactSupport g) :
    (∫ x : Fin d → ℝ, (∑ i : Fin d, coordPartial i (coordPartial i f) x) * g x)
      = -∑ i : Fin d, ∫ x : Fin d → ℝ, coordPartial i f x * coordPartial i g x := by
  have hterm : ∀ i : Fin d,
      (∫ x : Fin d → ℝ, coordPartial i (coordPartial i f) x * g x)
        = -∫ x : Fin d → ℝ, coordPartial i f x * coordPartial i g x := by
    intro i
    have h := integral_mul_coordPartial (f := g) (g := coordPartial i f) hg
      (contDiff_coordPartial hf i) hgs i
    have hcomm : ∀ x : Fin d → ℝ,
        coordPartial i (coordPartial i f) x * g x
          = g x * coordPartial i (coordPartial i f) x := fun x => mul_comm _ _
    calc (∫ x : Fin d → ℝ, coordPartial i (coordPartial i f) x * g x)
        = ∫ x : Fin d → ℝ, g x * coordPartial i (coordPartial i f) x := by
          exact integral_congr_ae (Filter.Eventually.of_forall hcomm)
      _ = -∫ x : Fin d → ℝ, coordPartial i g x * coordPartial i f x := h
      _ = -∫ x : Fin d → ℝ, coordPartial i f x * coordPartial i g x := by
          congr 1
          exact integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)
  have hsum : (∫ x : Fin d → ℝ, (∑ i : Fin d, coordPartial i (coordPartial i f) x) * g x)
      = ∑ i : Fin d, ∫ x : Fin d → ℝ, coordPartial i (coordPartial i f) x * g x := by
    have hexp : (fun x : Fin d → ℝ => (∑ i : Fin d, coordPartial i (coordPartial i f) x) * g x)
        = fun x : Fin d → ℝ => ∑ i : Fin d, coordPartial i (coordPartial i f) x * g x := by
      funext x
      rw [Finset.sum_mul]
    rw [hexp]
    refine integral_finsetSum Finset.univ fun i _ => ?_
    exact integrable_of_continuous_compactSupport
      (((contDiff_coordPartial (contDiff_coordPartial hf i) i).continuous).mul hg.continuous)
      ((hasCompactSupport_coordPartial (hasCompactSupport_coordPartial hfs i) i).mul_right)
  rw [hsum, Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_neg_distrib]

end Green

end GaloisForLFunctions.HTGeometry
