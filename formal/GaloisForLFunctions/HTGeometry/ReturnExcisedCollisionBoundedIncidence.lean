import GaloisForLFunctions.HTGeometry.ReturnExcisedPhaseIncidenceLaw

/-!
# Return-excised incidence at a bounded spectral collision

The return-excised complete-target bound is monotone in the spectral collision of the source, so
any upper bound on the collision may be substituted for it.  This is the form in which the bound is
combined with a quenched collision estimate.
-/

open MeasureTheory Complex UnitAddTorus Set

noncomputable section

namespace GaloisForLFunctions.HTGeometry

local instance returnExcisedCollisionBoundedIncidenceMeasureSpace :
    MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance returnExcisedCollisionBoundedIncidenceIsAddHaarMeasure :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance returnExcisedCollisionBoundedIncidenceIsProbabilityMeasure :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

set_option linter.unusedSectionVars false

variable {d : Type*} [Fintype d] [DecidableEq d]
variable {C : Type*} [Fintype C] [Nonempty C]

/-- **Return-excised complete-target bound at a bounded collision.**  Substituting any upper bound
for the spectral collision keeps the estimate valid. -/
theorem measureReal_capture_le_return_add_replicaMoment_of_collision_le
    {p : d → ℝ} (hp : ∀ j, 0 ≤ p j) (hpsum : ∑ j, p j ≤ 1) {a : ℝ} (ha : 0 < a)
    (z : C → (d → ℂ)) (hz : ∀ c, finiteComplexInner (z c) (z c) = 1)
    (hznorm : ∀ c, ∑ j, ‖z c j‖ ^ (2 : ℕ) ≤ 1)
    {R Q : Set (d → ℝ)} (hR : MeasurableSet R)
    (hcap : ∀ x ∈ Q \ R, ∃ c, a ≤ finitePureStateFidelity (torusReplicaPhaseOrbit p x) (z c))
    (r : ℕ) {c₀ : ℝ} (hcoll : occupationCollision p ≤ c₀) :
    (volume.restrict (torusBox d)).real Q ≤
      (volume.restrict (torusBox d)).real R +
        (Module.finrank ℂ (replicaTargetSpan r z) : ℝ) * (r.factorial : ℝ) *
          (16 * c₀ / a ^ (2 : ℕ)) ^ r := by
  classical
  have hbase := measureReal_capture_le_return_add_replicaMoment hp hpsum ha z hz hznorm hR hcap r
  refine le_trans hbase (add_le_add le_rfl ?_)
  have hnn : (0 : ℝ) ≤ 16 * occupationCollision p / a ^ (2 : ℕ) := by
    have : (0 : ℝ) ≤ occupationCollision p := Finset.sum_nonneg fun j _ => sq_nonneg _
    positivity
  have hstep : (16 * occupationCollision p / a ^ (2 : ℕ)) ^ r ≤ (16 * c₀ / a ^ (2 : ℕ)) ^ r := by
    refine pow_le_pow_left₀ hnn ?_ r
    have ha2 : (0 : ℝ) < a ^ (2 : ℕ) := by positivity
    rw [div_le_div_iff_of_pos_right ha2]
    linarith
  refine mul_le_mul_of_nonneg_left hstep ?_
  have hrank : (0 : ℝ) ≤ (Module.finrank ℂ (replicaTargetSpan r z) : ℝ) := by positivity
  have hfact : (0 : ℝ) ≤ (r.factorial : ℝ) := by positivity
  positivity

end GaloisForLFunctions.HTGeometry
