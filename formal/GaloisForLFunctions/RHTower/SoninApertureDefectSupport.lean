import GaloisForLFunctions.RHTower.SoninApertureCurvatureTrace

/-!
# The layer coupling vanishes exactly when the defect is carried by the outer aperture

The aperture defect is the Gram square of the lost-layer transition, and the successive-layer
coupling is that transition cut by the complement of the outer carrier.  Consequently the coupling
vanishes exactly when the defect is annihilated by that complement, that is, exactly when the
defect is supported on the aperture-`c` carrier.

This replaces the question "is the coupling nonzero?" by the geometric question "does the aperture
defect between `a` and `b` see anything outside the carrier at `c`?", which is an identity between
explicit operators rather than a statement about a compact error.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open ContinuousLinearMap
open scoped InnerProduct InnerProductSpace

/-- An operator whose Gram square vanishes is itself zero. -/
theorem eq_zero_of_adjoint_mul_self_eq_zero
    {S : evenSubspace →L[ℂ] evenSubspace}
    (h : ContinuousLinearMap.adjoint S * S = 0) : S = 0 := by
  apply ContinuousLinearMap.ext
  intro v
  have happ : ContinuousLinearMap.adjoint S (S v) = 0 := by
    have := congrArg (fun T : evenSubspace →L[ℂ] evenSubspace => T v) h
    simpa using this
  have hinner : inner ℂ (S v) (S v) = (0 : ℂ) := by
    have h1 : inner ℂ v (ContinuousLinearMap.adjoint S (S v)) =
        inner ℂ (S v) (S v) :=
      ContinuousLinearMap.adjoint_inner_right S v (S v)
    rw [← h1, happ, inner_zero_right]
  simpa using inner_self_eq_zero.mp hinner

/-- **Support characterization of the layer coupling.**  The successive-layer coupling vanishes
exactly when the aperture defect is annihilated by the complement of the outer carrier. -/
theorem evenSoninApertureSuccessiveLayerTransition_eq_zero_iff_defect_mul_complement
    {a b c r : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hr : 1 < r) :
    evenSoninApertureSuccessiveLayerTransition a b c r hr = 0 ↔
      evenSoninApertureRestrictionDefect a b r hr *
        (1 - evenCentralSoninProjection c) = 0 := by
  set Y := evenSoninApertureLostTransition a b r hr with hY
  set E : evenSubspace →L[ℂ] evenSubspace :=
    1 - evenCentralSoninProjection c with hE
  have hEadj : ContinuousLinearMap.adjoint E = E := by
    rw [hE, ContinuousLinearMap.adjoint.map_sub, ContinuousLinearMap.adjoint_one,
      adjoint_evenCentralSoninProjection]
  have hdef : evenSoninApertureRestrictionDefect a b r hr =
      ContinuousLinearMap.adjoint Y * Y := by
    simpa only [hY, evenSoninApertureRestrictionDefect] using
      evenCentralSoninQuadraticCorner_restrictionDefect_eq_adjoint_mul hab hr
  have hZ : evenSoninApertureSuccessiveLayerTransition a b c r hr = Y * E := by
    simpa only [hY, hE] using
      evenSoninApertureSuccessiveLayerTransition_eq_boundary hbc hr
  constructor
  · intro h
    rw [hdef, hZ] at *
    calc
      ContinuousLinearMap.adjoint Y * Y * E =
          ContinuousLinearMap.adjoint Y * (Y * E) := by rw [mul_assoc]
      _ = ContinuousLinearMap.adjoint Y * 0 := by rw [h]
      _ = 0 := by rw [mul_zero]
  · intro h
    rw [hZ]
    refine eq_zero_of_adjoint_mul_self_eq_zero ?_
    have hexpand : ContinuousLinearMap.adjoint (Y * E) * (Y * E) =
        E * (evenSoninApertureRestrictionDefect a b r hr * E) := by
      rw [hdef]
      change ContinuousLinearMap.adjoint (Y ∘L E) * (Y * E) = _
      rw [ContinuousLinearMap.adjoint_comp, hEadj]
      change E * ContinuousLinearMap.adjoint Y * (Y * E) = _
      noncomm_ring
    rw [hexpand, h, mul_zero]

end RHTower
