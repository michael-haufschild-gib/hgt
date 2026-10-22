import GaloisForLFunctions.RHTower.Deninger.DeningerWeylCriterion

/-!
# Completeness of the phase characters

A continuous function on the phase torus orthogonal to every exponential monomial vanishes.  The
monomials form a Hilbert basis of the `L²` space, so all Fourier coefficients vanishing forces the
`L²` class to be zero, and Haar measure is positive on nonempty open sets, so a continuous
representative of the zero class is identically zero.

This is the completeness half of the mode decomposition: no square-integrable datum on the leaf
cylinder is invisible to the character modes.

* `deningerTorusCompleteness` : orthogonality to every character forces vanishing.
* `deningerTorusEq_of_coeffs` : two continuous functions with the same coefficients agree.
-/

namespace RHTower

open UnitAddTorus MeasureTheory Set

/-- The circle is normalised to total mass one, as in the multivariate Fourier theory. -/
noncomputable local instance deningerTorusCompletenessMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance deningerTorusCompletenessIsAddHaarMeasure :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance deningerTorusCompletenessIsProbabilityMeasure :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

section Completeness

variable {d : Type*} [Fintype d]

/-- **A continuous function orthogonal to every character vanishes.** -/
theorem deningerTorusCompleteness {f : C(UnitAddTorus d, ℂ)}
    (hf : ∀ n : d → ℤ, (∫ η : UnitAddTorus d, f η * (starRingEnd ℂ) (mFourier n η)) = 0) :
    f = 0 := by
  have hcoe : ∀ n : d → ℤ, (∫ η : UnitAddTorus d, mFourier (-n) η • f η) = 0 := by
    intro n
    have hpt : ∀ η : UnitAddTorus d,
        mFourier (-n) η • f η = f η * (starRingEnd ℂ) (mFourier n η) := by
      intro η
      rw [mFourier_neg, smul_eq_mul]
      ring
    rw [funext hpt]
    exact hf n
  set F : Lp ℂ 2 (volume : Measure (UnitAddTorus d)) := ContinuousMap.toLp 2 volume ℂ f with hF
  have hae : (F : UnitAddTorus d → ℂ) =ᵐ[volume] fun η => f η :=
    ContinuousMap.coeFn_toLp volume f
  have hrepr : ∀ n : d → ℤ, mFourierBasis.repr F n = 0 := by
    intro n
    rw [mFourierBasis_repr, mFourierCoeff]
    rw [integral_congr_ae (hae.mono fun η hη => by rw [hη])]
    exact hcoe n
  have hzero : mFourierBasis.repr F = 0 := by
    refine lp.ext ?_
    funext n
    rw [hrepr n]
    rfl
  have hFzero : F = 0 := by
    have h := congrArg (mFourierBasis.repr).symm hzero
    rwa [LinearIsometryEquiv.symm_apply_apply, map_zero] at h
  refine ContinuousMap.toLp_injective (𝕜 := ℂ) (p := 2) volume ?_
  rw [map_zero]
  exact hFzero

/-- **Two continuous functions with the same character coefficients agree.** -/
theorem deningerTorusEq_of_coeffs {f g : C(UnitAddTorus d, ℂ)}
    (h : ∀ n : d → ℤ, (∫ η : UnitAddTorus d, f η * (starRingEnd ℂ) (mFourier n η))
      = ∫ η : UnitAddTorus d, g η * (starRingEnd ℂ) (mFourier n η)) : f = g := by
  have hsub : f - g = 0 := by
    refine deningerTorusCompleteness fun n => ?_
    have hint : (∫ η : UnitAddTorus d, (f - g) η * (starRingEnd ℂ) (mFourier n η))
        = (∫ η : UnitAddTorus d, f η * (starRingEnd ℂ) (mFourier n η))
          - ∫ η : UnitAddTorus d, g η * (starRingEnd ℂ) (mFourier n η) := by
      rw [← integral_sub]
      · refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
        show (f η - g η) * (starRingEnd ℂ) (mFourier n η)
          = f η * (starRingEnd ℂ) (mFourier n η) - g η * (starRingEnd ℂ) (mFourier n η)
        ring
      · exact deningerTorusIntegrable
          ⟨fun η => f η * (starRingEnd ℂ) (mFourier n η), by fun_prop⟩
      · exact deningerTorusIntegrable
          ⟨fun η => g η * (starRingEnd ℂ) (mFourier n η), by fun_prop⟩
    rw [hint, h n, sub_self]
  exact sub_eq_zero.mp hsub

end Completeness

end RHTower
