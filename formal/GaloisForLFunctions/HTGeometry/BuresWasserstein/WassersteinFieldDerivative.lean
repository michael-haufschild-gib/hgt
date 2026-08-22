import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.Operations
import GaloisForLFunctions.HTGeometry.BuresWasserstein.GeometricMeanDerivative
import GaloisForLFunctions.HTGeometry.BuresWasserstein.WassersteinEquation

/-!
# The Wasserstein vector field and its Fréchet derivative

Kim–Mer–Pálfia (arXiv:2607.29142) study the vector field

`Φ(X) = ∑ᵢ wᵢ (1 - (Aᵢ # X⁻¹))`,

whose zeros are exactly the Wasserstein barycentres.  This file assembles its strict Fréchet
derivative from the chain rule: `Ring.inverse` is `C¹` on units, `Z ↦ a # Z` is strictly
differentiable at strictly positive `Z` by `hasStrictFDerivAt_gmMap`, and the outer structure is a
finite weighted sum.
-/

open scoped NNReal Ring

namespace GaloisForLFunctions.HTGeometry.BuresWasserstein

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {ι : Type*}

omit [PartialOrder A] [StarOrderedRing A] in
/-- **Strict** differentiability of ring inversion at a unit. -/
theorem hasStrictFDerivAt_ringInverse (x : Aˣ) :
    HasStrictFDerivAt (Ring.inverse : A → A)
      (-ContinuousLinearMap.mulLeftRight ℝ A (↑x⁻¹ : A) (↑x⁻¹ : A)) (↑x : A) := by
  have h1 : ContDiffAt ℝ 1 (Ring.inverse : A → A) (↑x : A) := contDiffAt_ringInverse ℝ x
  have h2 := h1.hasStrictFDerivAt (by norm_num)
  rwa [(hasFDerivAt_ringInverse (𝕜 := ℝ) x).fderiv] at h2

/-- The map `X ↦ a # X⁻¹`, extended to all of `A`. -/
noncomputable def gmInvMap (a X : A) : A := gmMap a (Ring.inverse X)

lemma gmInvMap_eq_gm {a X : A} (hX : IsStrictlyPositive X) : gmInvMap a X = gm a X⁻¹ʳ :=
  gmMap_eq_gm a hX.ringInverse.isSelfAdjoint

/-- **Strict differentiability of `X ↦ a # X⁻¹`** at a strictly positive `X`. -/
theorem hasStrictFDerivAt_gmInvMap {a X : A} (hX : IsStrictlyPositive X)
    (hc : IsStrictlyPositive (conjMap (a ^ (-(1/2) : ℝ)) X⁻¹ʳ))
    {u : (A →L[ℝ] A)ˣ}
    (hu : (↑u : A →L[ℝ] A)
      = (lyapunov (CFC.sqrt (conjMap (a ^ (-(1/2) : ℝ)) X⁻¹ʳ))).comp (saProj : A →L[ℝ] A)
        + ((1 : A →L[ℝ] A) - saProj)) :
    HasStrictFDerivAt (gmInvMap a)
      (((conjMap (a ^ (1/2 : ℝ))).comp
          ((↑u⁻¹ : A →L[ℝ] A).comp (conjMap (a ^ (-(1/2) : ℝ))))).comp
        (-ContinuousLinearMap.mulLeftRight ℝ A X⁻¹ʳ X⁻¹ʳ)) X := by
  have hinv : HasStrictFDerivAt (Ring.inverse : A → A)
      (-ContinuousLinearMap.mulLeftRight ℝ A X⁻¹ʳ X⁻¹ʳ) X := by
    have h := hasStrictFDerivAt_ringInverse hX.isUnit.unit
    rw [hX.isUnit.unit_spec] at h
    rwa [show ((↑(hX.isUnit.unit⁻¹) : A)) = X⁻¹ʳ by
      rw [← Ring.inverse_unit hX.isUnit.unit, hX.isUnit.unit_spec]] at h
  have hgm : HasStrictFDerivAt (gmMap a)
      ((conjMap (a ^ (1/2 : ℝ))).comp
        ((↑u⁻¹ : A →L[ℝ] A).comp (conjMap (a ^ (-(1/2) : ℝ))))) (Ring.inverse X) :=
    hasStrictFDerivAt_gmMap hc hu
  exact HasStrictFDerivAt.comp (f := (Ring.inverse : A → A)) (g := gmMap a) X hgm hinv

/-- The **Wasserstein vector field** `Φ(X) = ∑ wᵢ (1 - Aᵢ # X⁻¹)`. -/
noncomputable def wassField (s : Finset ι) (w : ι → ℝ) (Av : ι → A) (X : A) : A :=
  ∑ i ∈ s, w i • ((1 : A) - gmInvMap (Av i) X)

variable {s : Finset ι} {w : ι → ℝ} {Av : ι → A} {X : A}

/-- Zeros of the Wasserstein field are exactly the Wasserstein points. -/
theorem wassField_eq_zero_iff (hsum : ∑ i ∈ s, w i = 1) (hX : IsStrictlyPositive X) :
    wassField s w Av X = 0 ↔ IsWassersteinPoint s w Av X := by
  have hexp : wassField s w Av X = 1 - ∑ i ∈ s, w i • gm (Av i) X⁻¹ʳ := by
    unfold wassField
    rw [Finset.sum_congr rfl fun i hi => by rw [gmInvMap_eq_gm hX]]
    simp only [smul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_smul, hsum, one_smul]
  rw [hexp]
  unfold IsWassersteinPoint
  constructor
  · intro h
    exact ⟨hX, (sub_eq_zero.mp h).symm⟩
  · rintro ⟨-, h⟩
    rw [h, sub_self]

/-- **Strict differentiability of the Wasserstein vector field.** -/
theorem hasStrictFDerivAt_wassField (hX : IsStrictlyPositive X)
    (hc : ∀ i ∈ s, IsStrictlyPositive (conjMap ((Av i) ^ (-(1/2) : ℝ)) X⁻¹ʳ))
    {u : ι → (A →L[ℝ] A)ˣ}
    (hu : ∀ i ∈ s, (↑(u i) : A →L[ℝ] A)
      = (lyapunov (CFC.sqrt (conjMap ((Av i) ^ (-(1/2) : ℝ)) X⁻¹ʳ))).comp (saProj : A →L[ℝ] A)
        + ((1 : A →L[ℝ] A) - saProj)) :
    HasStrictFDerivAt (wassField s w Av)
      (∑ i ∈ s, w i • (-((((conjMap ((Av i) ^ (1/2 : ℝ))).comp
          ((↑(u i)⁻¹ : A →L[ℝ] A).comp (conjMap ((Av i) ^ (-(1/2) : ℝ))))).comp
        (-ContinuousLinearMap.mulLeftRight ℝ A X⁻¹ʳ X⁻¹ʳ))))) X := by
  refine HasStrictFDerivAt.fun_sum fun i hi => ?_
  exact ((hasStrictFDerivAt_gmInvMap hX (hc i hi) (hu i hi)).const_sub 1).const_smul (w i)

end

end GaloisForLFunctions.HTGeometry.BuresWasserstein
