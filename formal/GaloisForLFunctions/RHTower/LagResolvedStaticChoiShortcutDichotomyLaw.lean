import GaloisForLFunctions.RHTower.ScalarRecurrenceTracelessCircuitSplit
import GaloisForLFunctions.RHTower.StaticChoiForwardSpectralDimensionLaw

/-!
# Lag-resolved static-Choi shortcut dichotomy

A target is decomposed relative to an arbitrary spectral-orbit anchor, not
only the identity time.  Capture by any target then lies either in one return
tube through the permitted anchor set or in that target's anchor-orthogonal
residual channel.  Exact past-orbit targets have zero residual, so genuine
returns are charged before any target union.
-/

open scoped BigOperators ComplexConjugate

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- Component of a Choi target along the spectral orbit at `anchor`. -/
def staticChoiAnchorComponent
    {d : ℕ} (energy : Fin d → ℝ) (anchor : ℝ)
    (target : EuclideanSpace ℂ (Fin d × Fin d)) : ℂ :=
  inner ℂ (staticSpectralChoiVector d anchor energy) target

/-- Orthogonal residual after removing the component along the spectral
orbit at `anchor`. -/
def staticChoiAnchorResidual
    {d : ℕ} (energy : Fin d → ℝ) (anchor : ℝ)
    (target : EuclideanSpace ℂ (Fin d × Fin d)) :
    EuclideanSpace ℂ (Fin d × Fin d) :=
  target - staticChoiAnchorComponent energy anchor target •
    staticSpectralChoiVector d anchor energy

theorem staticChoiTarget_eq_anchor_add_residual
    {d : ℕ} (energy : Fin d → ℝ) (anchor : ℝ)
    (target : EuclideanSpace ℂ (Fin d × Fin d)) :
    staticChoiAnchorComponent energy anchor target •
          staticSpectralChoiVector d anchor energy +
        staticChoiAnchorResidual energy anchor target = target := by
  simp [staticChoiAnchorResidual]

theorem inner_staticChoiAnchorResidual_eq_zero
    {d : ℕ} (hd : 0 < d) (energy : Fin d → ℝ) (anchor : ℝ)
    (target : EuclideanSpace ℂ (Fin d × Fin d)) :
    inner ℂ (staticSpectralChoiVector d anchor energy)
      (staticChoiAnchorResidual energy anchor target) = 0 := by
  rw [staticChoiAnchorResidual, inner_sub_right, inner_smul_right]
  rw [inner_self_eq_norm_sq_to_K, staticSpectralChoiVector_norm hd]
  simp [staticChoiAnchorComponent]

theorem norm_staticChoiAnchorComponent_le_one
    {d : ℕ} (hd : 0 < d) (energy : Fin d → ℝ) (anchor : ℝ)
    {target : EuclideanSpace ℂ (Fin d × Fin d)}
    (htarget : ‖target‖ = 1) :
    ‖staticChoiAnchorComponent energy anchor target‖ ≤ 1 := by
  calc
    ‖staticChoiAnchorComponent energy anchor target‖ =
        ‖inner ℂ (staticSpectralChoiVector d anchor energy) target‖ := rfl
    _ ≤ ‖staticSpectralChoiVector d anchor energy‖ * ‖target‖ :=
      norm_inner_le_norm _ _
    _ = 1 := by rw [staticSpectralChoiVector_norm hd, htarget, one_mul]

theorem inner_staticChoiTarget_anchor_residual_decomposition
    {d : ℕ} (t : ℝ) (energy : Fin d → ℝ) (anchor : ℝ)
    (target : EuclideanSpace ℂ (Fin d × Fin d)) :
    inner ℂ (staticSpectralChoiVector d t energy) target =
      staticChoiAnchorComponent energy anchor target *
          inner ℂ (staticSpectralChoiVector d t energy)
            (staticSpectralChoiVector d anchor energy) +
        inner ℂ (staticSpectralChoiVector d t energy)
          (staticChoiAnchorResidual energy anchor target) := by
  nth_rewrite 1 [← staticChoiTarget_eq_anchor_add_residual
    energy anchor target]
  rw [inner_add_right, inner_smul_right]

/-- Capture of a normalized target forces either return to its chosen orbit
anchor or capture by the anchor-orthogonal residual. -/
theorem staticChoiTarget_capture_anchor_or_residual_budget
    {d : ℕ} (hd : 0 < d) (t : ℝ) (energy : Fin d → ℝ)
    (anchor : ℝ) {target : EuclideanSpace ℂ (Fin d × Fin d)}
    (htarget : ‖target‖ = 1) {theta eta : ℝ}
    (hlarge : theta ≤
      ‖inner ℂ (staticSpectralChoiVector d t energy) target‖) :
    eta ≤
        ‖inner ℂ (staticSpectralChoiVector d t energy)
          (staticSpectralChoiVector d anchor energy)‖ ∨
      theta - eta ≤
        ‖inner ℂ (staticSpectralChoiVector d t energy)
          (staticChoiAnchorResidual energy anchor target)‖ := by
  rw [inner_staticChoiTarget_anchor_residual_decomposition] at hlarge
  exact norm_common_or_residual_of_norm_linear_split_ge_budget
    (norm_staticChoiAnchorComponent_le_one hd energy anchor htarget) hlarge

/-- One lag-resolved return tube through an arbitrary set of permitted orbit
anchors. -/
def staticChoiAnchorReturnTube
    {d : ℕ} (energy : Fin d → ℝ) (anchors : Set ℝ) (eta : ℝ) : Set ℝ :=
  {t | ∃ u ∈ anchors,
    eta ≤ ‖inner ℂ (staticSpectralChoiVector d t energy)
      (staticSpectralChoiVector d u energy)‖}

/-- Capture by the residual orthogonal to a specified orbit anchor. -/
def staticChoiAnchorResidualCaptureSet
    {d : ℕ} (energy : Fin d → ℝ) (anchor : ℝ)
    (target : EuclideanSpace ℂ (Fin d × Fin d))
    (theta : ℝ) : Set ℝ :=
  staticChoiOverlapCaptureSet energy
    (staticChoiAnchorResidual energy anchor target) theta

/-- **Lag-resolved shortcut dichotomy.**  An arbitrary target union splits
into one return tube through the permitted anchor set and the union of
anchor-orthogonal residual captures.  The return branch is formed before the
target union, so it incurs no target-cardinality factor. -/
theorem iUnion_staticChoiOverlapCaptureSet_subset_anchorReturnTube_union_residual
    {d : ℕ} (hd : 0 < d) {W : Type*} (energy : Fin d → ℝ)
    (target : W → EuclideanSpace ℂ (Fin d × Fin d))
    (htarget : ∀ w, ‖target w‖ = 1)
    (anchor : W → ℝ) (anchors : Set ℝ)
    (hanchor : ∀ w, anchor w ∈ anchors) (theta eta : ℝ) :
    (⋃ w, staticChoiOverlapCaptureSet energy (target w) theta) ⊆
      staticChoiAnchorReturnTube energy anchors eta ∪
        ⋃ w, staticChoiAnchorResidualCaptureSet energy
          (anchor w) (target w) (theta - eta) := by
  intro t ht
  simp only [Set.mem_iUnion, staticChoiOverlapCaptureSet] at ht
  obtain ⟨w, hw⟩ := ht
  rcases staticChoiTarget_capture_anchor_or_residual_budget
      hd t energy (anchor w) (htarget w) hw with hreturn | hresidual
  · exact Set.mem_union_left _ ⟨anchor w, hanchor w, hreturn⟩
  · exact Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨w, hresidual⟩)

theorem staticChoiAnchorResidual_self_eq_zero
    {d : ℕ} (hd : 0 < d) (energy : Fin d → ℝ) (anchor : ℝ) :
    staticChoiAnchorResidual energy anchor
      (staticSpectralChoiVector d anchor energy) = 0 := by
  unfold staticChoiAnchorResidual staticChoiAnchorComponent
  rw [inner_self_eq_norm_sq_to_K, staticSpectralChoiVector_norm hd]
  simp

theorem staticChoiPhaseShift_sub
    {d : ℕ} (energy : Fin d → ℝ) (a : ℝ)
    (x y : EuclideanSpace ℂ (Fin d × Fin d)) :
    staticChoiPhaseShift energy a (x - y) =
      staticChoiPhaseShift energy a x - staticChoiPhaseShift energy a y := by
  ext ij
  simp only [staticChoiPhaseShift_apply, PiLp.sub_apply]
  ring

theorem staticChoiPhaseShift_smul
    {d : ℕ} (energy : Fin d → ℝ) (a : ℝ) (c : ℂ)
    (x : EuclideanSpace ℂ (Fin d × Fin d)) :
    staticChoiPhaseShift energy a (c • x) =
      c • staticChoiPhaseShift energy a x := by
  ext ij
  simp only [staticChoiPhaseShift_apply, PiLp.smul_apply]
  ring

theorem staticChoiScalarComponent_phaseShift_neg_eq_anchorComponent
    {d : ℕ} (energy : Fin d → ℝ) (anchor : ℝ)
    (target : EuclideanSpace ℂ (Fin d × Fin d)) :
    staticChoiScalarComponent energy
        (staticChoiPhaseShift energy (-anchor) target) =
      staticChoiAnchorComponent energy anchor target := by
  have h := inner_staticChoiPhaseShift energy (-anchor)
    (staticSpectralChoiVector d anchor energy) target
  rw [staticChoiPhaseShift_staticSpectralChoiVector] at h
  simpa [staticChoiScalarComponent, staticChoiAnchorComponent] using h

/-- Translating an anchored residual back to time zero produces exactly the
ordinary traceless residual of the translated target. -/
theorem staticChoiPhaseShift_anchorResidual_eq_tracelessResidual
    {d : ℕ} (energy : Fin d → ℝ) (anchor : ℝ)
    (target : EuclideanSpace ℂ (Fin d × Fin d)) :
    staticChoiPhaseShift energy (-anchor)
        (staticChoiAnchorResidual energy anchor target) =
      staticChoiTracelessResidual energy
        (staticChoiPhaseShift energy (-anchor) target) := by
  rw [staticChoiAnchorResidual, staticChoiTracelessResidual,
    staticChoiPhaseShift_sub, staticChoiPhaseShift_smul,
    staticChoiScalarComponent_phaseShift_neg_eq_anchorComponent,
    staticChoiPhaseShift_staticSpectralChoiVector]
  simp

/-- Orbit overlap depends only on the lag, exactly through the uniform
spectral survival amplitude. -/
theorem norm_inner_staticSpectralChoiVector_eq_survival_lag
    {d : ℕ} (hd : 0 < d) (energy : Fin d → ℝ) (t anchor : ℝ) :
    ‖inner ℂ (staticSpectralChoiVector d t energy)
        (staticSpectralChoiVector d anchor energy)‖ =
      ‖finiteSpectralSurvivalAmplitude (uniformSurvivalWeight d)
        (finiteObserverHamiltonianVertexPhase (t - anchor) energy)‖ := by
  rw [norm_inner_symm]
  have h := inner_staticChoiPhaseShift energy (-anchor)
    (staticSpectralChoiVector d anchor energy)
    (staticSpectralChoiVector d t energy)
  rw [staticChoiPhaseShift_staticSpectralChoiVector,
    staticChoiPhaseShift_staticSpectralChoiVector] at h
  have h' :
      inner ℂ (staticSpectralChoiVector d 0 energy)
          (staticSpectralChoiVector d (t - anchor) energy) =
        inner ℂ (staticSpectralChoiVector d anchor energy)
          (staticSpectralChoiVector d t energy) := by
    simpa [sub_eq_add_neg] using h
  rw [← h', inner_staticSpectralChoiVector_zero hd]

end RHTower

