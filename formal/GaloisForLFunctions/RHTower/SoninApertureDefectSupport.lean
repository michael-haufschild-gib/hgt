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

namespace RHTower

open ContinuousLinearMap

/-! ## The defect already lives on the inner carrier -/

/-- The lost-layer transition is unchanged by the carrier it ends on. -/
theorem evenSoninApertureLostTransition_mul_evenCentralSoninProjection
    (a b r : ℝ) (hr : 1 < r) :
    evenSoninApertureLostTransition a b r hr * evenCentralSoninProjection b =
      evenSoninApertureLostTransition a b r hr := by
  have hQ : evenCentralSoninProjection b * evenCentralSoninProjection b =
      evenCentralSoninProjection b := by
    rw [evenCentralSoninProjection_eq_starProjection]
    exact (evenCentralSoninCarrier b).isIdempotentElem_starProjection
  unfold evenSoninApertureLostTransition
  rw [mul_assoc, hQ]

/-- **The aperture defect is carried by the inner aperture.**  It is unchanged on the right by the
projection at `b`. -/
theorem evenSoninApertureRestrictionDefect_mul_evenCentralSoninProjection
    {a b r : ℝ} (hab : a ≤ b) (hr : 1 < r) :
    evenSoninApertureRestrictionDefect a b r hr * evenCentralSoninProjection b =
      evenSoninApertureRestrictionDefect a b r hr := by
  have hdef : evenSoninApertureRestrictionDefect a b r hr =
      ContinuousLinearMap.adjoint (evenSoninApertureLostTransition a b r hr) *
        evenSoninApertureLostTransition a b r hr := by
    simpa only [evenSoninApertureRestrictionDefect] using
      evenCentralSoninQuadraticCorner_restrictionDefect_eq_adjoint_mul hab hr
  rw [hdef, mul_assoc,
    evenSoninApertureLostTransition_mul_evenCentralSoninProjection a b r hr]

/-- The same on the left, by self-adjointness of the Gram square. -/
theorem evenCentralSoninProjection_mul_evenSoninApertureRestrictionDefect
    {a b r : ℝ} (hab : a ≤ b) (hr : 1 < r) :
    evenCentralSoninProjection b * evenSoninApertureRestrictionDefect a b r hr =
      evenSoninApertureRestrictionDefect a b r hr := by
  have hdef : evenSoninApertureRestrictionDefect a b r hr =
      ContinuousLinearMap.adjoint (evenSoninApertureLostTransition a b r hr) *
        evenSoninApertureLostTransition a b r hr := by
    simpa only [evenSoninApertureRestrictionDefect] using
      evenCentralSoninQuadraticCorner_restrictionDefect_eq_adjoint_mul hab hr
  have hadj : evenCentralSoninProjection b *
      ContinuousLinearMap.adjoint (evenSoninApertureLostTransition a b r hr) =
        ContinuousLinearMap.adjoint (evenSoninApertureLostTransition a b r hr) := by
    have h := congrArg ContinuousLinearMap.adjoint
      (evenSoninApertureLostTransition_mul_evenCentralSoninProjection a b r hr)
    change ContinuousLinearMap.adjoint
        (evenSoninApertureLostTransition a b r hr ∘L
          evenCentralSoninProjection b) = _ at h
    rw [ContinuousLinearMap.adjoint_comp, adjoint_evenCentralSoninProjection] at h
    exact h
  rw [hdef, ← mul_assoc, hadj]

/-- **Sharpest form of the coupling question.**  The aperture defect always lives on the carrier at
`b`; its layer coupling vanishes exactly when it in fact lives on the smaller carrier at `c`. -/
theorem evenSoninApertureSuccessiveLayerTransition_eq_zero_iff_defect_mul_outer
    {a b c r : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hr : 1 < r) :
    evenSoninApertureSuccessiveLayerTransition a b c r hr = 0 ↔
      evenSoninApertureRestrictionDefect a b r hr *
          evenCentralSoninProjection c =
        evenSoninApertureRestrictionDefect a b r hr := by
  rw [evenSoninApertureSuccessiveLayerTransition_eq_zero_iff_defect_mul_complement
    hab hbc hr]
  constructor
  · intro h
    have hexp : evenSoninApertureRestrictionDefect a b r hr *
        (1 - evenCentralSoninProjection c) =
          evenSoninApertureRestrictionDefect a b r hr -
            evenSoninApertureRestrictionDefect a b r hr *
              evenCentralSoninProjection c := by
      rw [mul_sub, mul_one]
    rw [hexp] at h
    exact (sub_eq_zero.mp h).symm
  · intro h
    rw [mul_sub, mul_one, h, sub_self]

end RHTower
