import GaloisForLFunctions.HTGeometry.BuresWasserstein.GeometricMeanLipschitz
import GaloisForLFunctions.HTGeometry.BuresWasserstein.WassersteinFieldDerivative

/-!
# The Wasserstein vector field takes Hilbert–Schmidt values on `Σ₂`

Since `a # a⁻¹ = 1`, the `i`-th summand of `Φ(X) = ∑ wᵢ (1 - Aᵢ # X⁻¹)` is the difference of two
geometric means with the same first argument, `Aᵢ # Aᵢ⁻¹ - Aᵢ # X⁻¹`.  By the Sylvester Lipschitz
theory this is Hilbert–Schmidt as soon as `Aᵢ⁻¹ - X⁻¹` is, and `Aᵢ⁻¹ - X⁻¹ = Aᵢ⁻¹ (X - Aᵢ) X⁻¹`
is Hilbert–Schmidt as soon as `X - Aᵢ` is.  Hence `Φ` maps `Σ₂` into the extended
Hilbert–Schmidt class, which is what makes the Wasserstein equation an equation on `Σ₂`.
-/

open scoped NNReal Ring BigOperators
open ContinuousLinearMap

namespace GaloisForLFunctions.HTGeometry.BuresWasserstein

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- **The geometric mean of an element and its inverse is the unit.** -/
@[simp] theorem gm_ringInverse_self' {a : A} (ha : IsStrictlyPositive a) :
    gm a a⁻¹ʳ = 1 := by
  refine (gm_unique ha zero_le_one ?_).symm
  rw [one_mul, mul_one]

/-- The lower Loewner bound for `a # b` on a Loewner interval. -/
theorem smul_one_le_gm {a b : A} (ha : IsStrictlyPositive a) (_hb : IsStrictlyPositive b)
    {α δ : ℝ} (hα : 0 < α) (hδ : 0 < δ)
    (haα : α • (1 : A) ≤ a) (hbδ : δ • (1 : A) ≤ b) :
    (Real.sqrt (α * δ)) • (1 : A) ≤ gm a b := by
  have h := gm_mono (IsStrictlyPositive.smul hα isStrictlyPositive_one) ha
    (IsStrictlyPositive.smul hδ isStrictlyPositive_one) haα hbδ
  rwa [gm_smul hα hδ isStrictlyPositive_one isStrictlyPositive_one, gm_one_left,
    CFC.sqrt_one] at h

end

section HilbertSchmidt

open GaloisForLFunctions.HTGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [PartialOrder (E →L[ℂ] E)] [StarOrderedRing (E →L[ℂ] E)]

omit [StarOrderedRing (E →L[ℂ] E)] in
/-- The difference of inverses is Hilbert–Schmidt when the difference is. -/
theorem isHilbertSchmidt_ringInverse_sub {a X : E →L[ℂ] E} (ha : IsStrictlyPositive a)
    (hX : IsStrictlyPositive X) (h : IsHilbertSchmidt (X - a)) :
    IsHilbertSchmidt ((a⁻¹ʳ : E →L[ℂ] E) - X⁻¹ʳ) := by
  have hid : (a⁻¹ʳ : E →L[ℂ] E) - X⁻¹ʳ = a⁻¹ʳ * (X - a) * X⁻¹ʳ := by
    have h1 : (a⁻¹ʳ : E →L[ℂ] E) * (X - a) * X⁻¹ʳ
        = a⁻¹ʳ * (X * X⁻¹ʳ) - (a⁻¹ʳ * a) * X⁻¹ʳ := by noncomm_ring
    rw [h1, Ring.mul_inverse_cancel _ hX.isUnit, Ring.inverse_mul_cancel _ ha.isUnit,
      mul_one, one_mul]
  rw [hid]
  exact (h.comp_left _).comp_right _

/-- **The summand of the Wasserstein vector field is Hilbert–Schmidt.** -/
theorem isHilbertSchmidt_one_sub_gm {a X : E →L[ℂ] E} (ha : IsStrictlyPositive a)
    (hX : IsStrictlyPositive X) {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (haα : α • (1 : E →L[ℂ] E) ≤ a) (haβ : a ≤ β • (1 : E →L[ℂ] E))
    (hXβ : X ≤ β • (1 : E →L[ℂ] E))
    (h : IsHilbertSchmidt (X - a)) :
    IsHilbertSchmidt ((1 : E →L[ℂ] E) - gm a X⁻¹ʳ) := by
  have hainv : IsStrictlyPositive (a⁻¹ʳ : E →L[ℂ] E) := ha.ringInverse
  have hXinv : IsStrictlyPositive (X⁻¹ʳ : E →L[ℂ] E) := hX.ringInverse
  have hlow : β⁻¹ • (1 : E →L[ℂ] E) ≤ (a⁻¹ʳ : E →L[ℂ] E) :=
    smul_one_le_ringInverse_of_le_smul_one ha hβ haβ
  have hlowX : β⁻¹ • (1 : E →L[ℂ] E) ≤ (X⁻¹ʳ : E →L[ℂ] E) :=
    smul_one_le_ringInverse_of_le_smul_one hX hβ hXβ
  have hγ : (0 : ℝ) < Real.sqrt (α * β⁻¹) := Real.sqrt_pos.mpr (by positivity)
  have hg1 : (Real.sqrt (α * β⁻¹)) • (1 : E →L[ℂ] E) ≤ gm a a⁻¹ʳ :=
    smul_one_le_gm ha hainv hα (inv_pos.mpr hβ) haα hlow
  have hg2 : (Real.sqrt (α * β⁻¹)) • (1 : E →L[ℂ] E) ≤ gm a X⁻¹ʳ :=
    smul_one_le_gm ha hXinv hα (inv_pos.mpr hβ) haα hlowX
  have hsub := isHilbertSchmidt_gm_sub ha hainv hXinv hγ hβ haβ hg1 hg2
    (isHilbertSchmidt_ringInverse_sub ha hX h)
  rwa [gm_ringInverse_self' ha] at hsub

variable {ι : Type*} {s : Finset ι} {w : ι → ℝ} {Av : ι → E →L[ℂ] E} {X : E →L[ℂ] E}

/-- **The Wasserstein vector field is Hilbert–Schmidt valued on `Σ₂`.** -/
theorem isHilbertSchmidt_wassField {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hA : ∀ i ∈ s, IsStrictlyPositive (Av i)) (hX : IsStrictlyPositive X)
    (hAα : ∀ i ∈ s, α • (1 : E →L[ℂ] E) ≤ Av i)
    (hAβ : ∀ i ∈ s, Av i ≤ β • (1 : E →L[ℂ] E))
    (hXβ : X ≤ β • (1 : E →L[ℂ] E))
    (h : ∀ i ∈ s, IsHilbertSchmidt (X - Av i)) :
    IsHilbertSchmidt (wassField s w Av X) := by
  unfold wassField
  refine IsHilbertSchmidt.sum s fun i hi => ?_
  refine IsHilbertSchmidt.real_smul ?_ _
  have hval : (1 : E →L[ℂ] E) - gmInvMap (Av i) X = (1 : E →L[ℂ] E) - gm (Av i) X⁻¹ʳ := by
    rw [gmInvMap_eq_gm hX]
  rw [hval]
  exact isHilbertSchmidt_one_sub_gm (hA i hi) hX hα hβ (hAα i hi) (hAβ i hi) hXβ (h i hi)

end HilbertSchmidt

end GaloisForLFunctions.HTGeometry.BuresWasserstein
