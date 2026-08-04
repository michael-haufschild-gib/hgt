import GaloisForLFunctions.HTGeometry.WienerSynthesisLaplacian
import Mathlib.Analysis.Convolution

/-!
# Convolution on the frequency side is multiplication in space

The potential enters the evolution as a convolution of frequency densities. This file identifies what
that convolution is on the physical side: the synthesis of a convolution is the product of the
syntheses,

`∫ 𝐞⟪ξ,x⟫ (a ⋆ w)(ξ) dξ = (∫ 𝐞⟪η,x⟫ a(η) dη) · (∫ 𝐞⟪ζ,x⟫ w(ζ) dζ)`,

which is Fubini together with the translation invariance of the measure and the character property
`𝐞(A+B) = 𝐞(A)𝐞(B)`. The first factor is the potential; the second is the field. So the source term
of the evolution is exactly the pointwise product of the potential with the field.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

open scoped RealInnerProductSpace FourierTransform

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **The character turns addition into multiplication.** -/
theorem kgChar_add (x ζ η : E) : kgChar x (ζ + η) = kgChar x ζ * kgChar x η := by
  rw [kgChar, kgChar, kgChar, inner_add_left, AddChar.map_add_eq_mul, Circle.coe_mul]

/-- **The synthesis of a convolution is the product of the syntheses.** -/
theorem integral_kgChar_mul_convolution {a w : E → ℂ} (ha : Integrable a (volume : Measure E))
    (hw : Integrable w (volume : Measure E)) (x : E) :
    (∫ ξ, kgChar x ξ * ∫ η, a η * w (ξ - η))
      = (∫ η, kgChar x η * a η) * ∫ ζ, kgChar x ζ * w ζ := by
  have hprod : Integrable (fun p : E × E => a p.2 * w (p.1 - p.2))
      ((volume : Measure E).prod (volume : Measure E)) := by
    have h := ha.convolution_integrand (L := ContinuousLinearMap.mul ℝ ℂ)
      (μ := (volume : Measure E)) hw
    exact h
  have hcharCont : Continuous fun p : E × E => kgChar x p.1 :=
    (continuous_kgChar' x).comp continuous_fst
  have hprod' : Integrable (fun p : E × E => kgChar x p.1 * (a p.2 * w (p.1 - p.2)))
      ((volume : Measure E).prod (volume : Measure E)) := by
    refine hprod.bdd_mul (c := 1) hcharCont.aestronglyMeasurable ?_
    filter_upwards with p
    exact le_of_eq (norm_kgChar x p.1)
  have hstep1 : (∫ ξ, kgChar x ξ * ∫ η, a η * w (ξ - η))
      = ∫ ξ, ∫ η, kgChar x ξ * (a η * w (ξ - η)) :=
    integral_congr_ae (Filter.Eventually.of_forall fun ξ => (integral_const_mul _ _).symm)
  rw [hstep1, integral_integral_swap hprod', ← integral_mul_const]
  refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
  show (∫ ξ, kgChar x ξ * (a η * w (ξ - η)))
      = kgChar x η * a η * ∫ ζ, kgChar x ζ * w ζ
  have hinner : (∫ ξ, kgChar x ξ * (a η * w (ξ - η)))
      = a η * ∫ ξ, kgChar x ξ * w (ξ - η) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    show kgChar x ξ * (a η * w (ξ - η)) = a η * (kgChar x ξ * w (ξ - η))
    ring
  have htrans : (∫ ξ, kgChar x ξ * w (ξ - η)) = kgChar x η * ∫ ζ, kgChar x ζ * w ζ := by
    have h := integral_sub_right_eq_self (μ := (volume : Measure E))
      (fun ζ : E => kgChar x (ζ + η) * w ζ) η
    simp only [sub_add_cancel] at h
    rw [h, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
    show kgChar x (ζ + η) * w ζ = kgChar x η * (kgChar x ζ * w ζ)
    rw [kgChar_add]
    ring
  rw [hinner, htrans]
  ring

end GaloisForLFunctions.HTGeometry
