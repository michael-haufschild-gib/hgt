import GaloisForLFunctions.RHTower.SoninApertureCurvatureTrace

/-!
# The coupling vanishes exactly when two aperture layers are dilation-orthogonal

The successive-layer coupling is a product of two self-adjoint layer projections with the dilation
sum between them, so it vanishes precisely when the dilation sum carries the inner layer into the
orthogonal complement of the outer one.

This is the coupling question with no algebra left in it: it is a statement about the relative
position of two Sonin layers under the dilation group.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open ContinuousLinearMap
open scoped InnerProduct InnerProductSpace

/-- **Orthogonality criterion for the successive-layer coupling.**  The coupling vanishes exactly
when every dilated inner-layer vector is orthogonal to every outer-layer vector. -/
theorem evenSoninApertureSuccessiveLayerTransition_eq_zero_iff_layers_orthogonal
    (a b c r : ℝ) (hr : 1 < r) :
    evenSoninApertureSuccessiveLayerTransition a b c r hr = 0 ↔
      ∀ u v : evenSubspace,
        ⟪evenSoninApertureLayer a b u,
          evenDilationSum r hr (evenSoninApertureLayer b c v)⟫_ℂ = 0 := by
  constructor
  · intro hzero u v
    have hval : evenSoninApertureSuccessiveLayerTransition a b c r hr v = 0 := by
      rw [hzero]; rfl
    unfold evenSoninApertureSuccessiveLayerTransition at hval
    rw [mul_apply_eq_comp, mul_apply_eq_comp] at hval
    have hadj := adjoint_evenSoninApertureLayer a b
    have hinner :
        ⟪evenSoninApertureLayer a b u,
            evenDilationSum r hr (evenSoninApertureLayer b c v)⟫_ℂ =
          ⟪u, evenSoninApertureLayer a b
            (evenDilationSum r hr (evenSoninApertureLayer b c v))⟫_ℂ := by
      rw [← ContinuousLinearMap.adjoint_inner_right (evenSoninApertureLayer a b), hadj]
    rw [hinner, hval, inner_zero_right]
  · intro horth
    apply ContinuousLinearMap.ext
    intro v
    have hzero : ∀ u : evenSubspace,
        ⟪u, evenSoninApertureSuccessiveLayerTransition a b c r hr v⟫_ℂ = 0 := by
      intro u
      have hadj := adjoint_evenSoninApertureLayer a b
      have hinner :
          ⟪evenSoninApertureLayer a b u,
              evenDilationSum r hr (evenSoninApertureLayer b c v)⟫_ℂ =
            ⟪u, evenSoninApertureLayer a b
              (evenDilationSum r hr (evenSoninApertureLayer b c v))⟫_ℂ := by
        rw [← ContinuousLinearMap.adjoint_inner_right (evenSoninApertureLayer a b), hadj]
      unfold evenSoninApertureSuccessiveLayerTransition
      rw [mul_apply_eq_comp, mul_apply_eq_comp, ← hinner]
      exact horth u v
    have := hzero (evenSoninApertureSuccessiveLayerTransition a b c r hr v)
    rw [inner_self_eq_zero] at this
    simpa using this

/-- The same criterion stated on the projection difference itself. -/
theorem evenSoninApertureSuccessiveLayerTransition_eq_zero_iff_projection_orthogonal
    (a b c r : ℝ) (hr : 1 < r) :
    evenSoninApertureSuccessiveLayerTransition a b c r hr = 0 ↔
      ∀ u v : evenSubspace,
        ⟪(evenCentralSoninProjection a - evenCentralSoninProjection b) u,
          evenDilationSum r hr
            ((evenCentralSoninProjection b - evenCentralSoninProjection c) v)⟫_ℂ = 0 :=
  evenSoninApertureSuccessiveLayerTransition_eq_zero_iff_layers_orthogonal a b c r hr

end RHTower
