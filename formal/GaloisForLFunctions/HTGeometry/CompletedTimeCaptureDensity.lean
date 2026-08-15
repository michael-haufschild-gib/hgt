import GaloisForLFunctions.HTGeometry.ReturnExcisedPhaseIncidenceLaw
import GaloisForLFunctions.HTGeometry.FiniteSpectralRecurrenceFrequencyLaw

/-!
# Completed-time density of the complete-target capture event

The fundamental-box projection onto the phase torus is measure preserving, so the Haar measure of a
capture event equals the phase-box measure of its preimage.  The capture event of a finite target
family is closed, and under a rationally independent frequency packet the completed-time upper
frequency of a closed target is at most its Haar measure.  The replica-moment bound on the box
therefore transfers verbatim into a long-time density bound.
-/

open MeasureTheory Complex UnitAddTorus Set Filter

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {d : Type*} [Fintype d] [DecidableEq d]
variable {C : Type*} [Fintype C] [Nonempty C]

section Projection

theorem torusBox_eq_univ_pi : torusBox d = Set.univ.pi fun _ : d => Ioc (0 : ℝ) 1 := by
  ext x
  simp [torusBox]

theorem continuous_torusProj : Continuous (torusProj : (d → ℝ) → UnitAddTorus d) :=
  continuous_pi fun j => (AddCircle.continuous_mk' (1 : ℝ)).comp (continuous_apply j)

/-- **The fundamental box projects onto the phase torus measure preservingly.** -/
theorem measurePreserving_torusProj :
    MeasurePreserving (torusProj : (d → ℝ) → UnitAddTorus d)
      ((volume : Measure (d → ℝ)).restrict (torusBox d)) volume := by
  classical
  have hpi := measurePreserving_pi
    (fun _ : d => (volume : Measure ℝ).restrict (Ioc (0 : ℝ) (0 + 1)))
    (fun _ : d => (volume : Measure UnitAddCircle))
    (fun _ : d => AddCircle.measurePreserving_mk 1 0)
  have hsrc : (Measure.pi fun _ : d => (volume : Measure ℝ).restrict (Ioc (0 : ℝ) (0 + 1)))
      = (volume : Measure (d → ℝ)).restrict (torusBox d) := by
    have h1 : ((0 : ℝ) + 1) = 1 := by norm_num
    simp only [h1]
    rw [← Measure.restrict_pi_pi, ← MeasureTheory.volume_pi, torusBox_eq_univ_pi]
  have htgt : (Measure.pi fun _ : d => (volume : Measure UnitAddCircle))
      = (volume : Measure (UnitAddTorus d)) := (MeasureTheory.volume_pi).symm
  rw [hsrc, htgt] at hpi
  exact hpi

end Projection

section Capture

/-- The spectral phase orbit as a function on the phase torus. -/
def torusPhaseOrbit (p : d → ℝ) (t : UnitAddTorus d) : d → ℂ :=
  fun j => ((Real.sqrt (p j) : ℝ) : ℂ) * UnitAddTorus.mFourier (Pi.single j 1) t

theorem torusPhaseOrbit_torusProj (p : d → ℝ) (x : d → ℝ) :
    torusPhaseOrbit p (torusProj x) = torusReplicaPhaseOrbit p x := by
  funext j
  rw [torusPhaseOrbit, torusReplicaPhaseOrbit, charLift_eq_mFourier]

theorem continuous_torusPhaseOrbit_apply (p : d → ℝ) (j : d) :
    Continuous fun t : UnitAddTorus d => torusPhaseOrbit p t j :=
  continuous_const.mul (UnitAddTorus.mFourier (Pi.single j 1)).continuous

theorem continuous_fidelity_torusPhaseOrbit (p : d → ℝ) (z : d → ℂ) :
    Continuous fun t : UnitAddTorus d => finitePureStateFidelity (torusPhaseOrbit p t) z := by
  refine (Continuous.norm ?_).pow 2
  refine continuous_finsetSum Finset.univ fun j _ => ?_
  exact (Complex.continuous_conj.comp (continuous_torusPhaseOrbit_apply p j)).mul continuous_const

/-- The complete-target capture event on the phase torus. -/
def torusCaptureTarget (p : d → ℝ) (a : ℝ) (z : C → (d → ℂ)) : Set (UnitAddTorus d) :=
  {t | ∃ c, a ≤ finitePureStateFidelity (torusPhaseOrbit p t) (z c)}

theorem isClosed_torusCaptureTarget (p : d → ℝ) (a : ℝ) (z : C → (d → ℂ)) :
    IsClosed (torusCaptureTarget p a z) := by
  have hunion : torusCaptureTarget p a z =
      ⋃ c : C, {t : UnitAddTorus d | a ≤ finitePureStateFidelity (torusPhaseOrbit p t) (z c)} := by
    ext t
    simp [torusCaptureTarget]
  rw [hunion]
  exact isClosed_iUnion_of_finite fun c =>
    isClosed_le continuous_const (continuous_fidelity_torusPhaseOrbit p (z c))

theorem measurableSet_torusCaptureTarget (p : d → ℝ) (a : ℝ) (z : C → (d → ℂ)) :
    MeasurableSet (torusCaptureTarget p a z) :=
  (isClosed_torusCaptureTarget p a z).measurableSet

/-- The box preimage of the torus capture event is the box capture event. -/
theorem preimage_torusCaptureTarget (p : d → ℝ) (a : ℝ) (z : C → (d → ℂ)) :
    torusProj ⁻¹' (torusCaptureTarget p a z) =
      {x : d → ℝ | ∃ c, a ≤ finitePureStateFidelity (torusReplicaPhaseOrbit p x) (z c)} := by
  ext x
  rw [Set.mem_preimage, torusCaptureTarget, Set.mem_setOf_eq, Set.mem_setOf_eq,
    torusPhaseOrbit_torusProj]

/-- **The Haar measure of the capture event is its phase-box measure.** -/
theorem measure_torusCaptureTarget (p : d → ℝ) (a : ℝ) (z : C → (d → ℂ)) :
    (volume : Measure (UnitAddTorus d)) (torusCaptureTarget p a z) =
      ((volume : Measure (d → ℝ)).restrict (torusBox d))
        {x : d → ℝ | ∃ c, a ≤ finitePureStateFidelity (torusReplicaPhaseOrbit p x) (z c)} := by
  rw [← preimage_torusCaptureTarget p a z]
  exact (measurePreserving_torusProj.measure_preimage
    (measurableSet_torusCaptureTarget p a z).nullMeasurableSet).symm

theorem measureReal_torusCaptureTarget (p : d → ℝ) (a : ℝ) (z : C → (d → ℂ)) :
    (volume : Measure (UnitAddTorus d)).real (torusCaptureTarget p a z) =
      ((volume : Measure (d → ℝ)).restrict (torusBox d)).real
        {x : d → ℝ | ∃ c, a ≤ finitePureStateFidelity (torusReplicaPhaseOrbit p x) (z c)} := by
  rw [measureReal_def, measureReal_def, measure_torusCaptureTarget p a z]

end Capture

section Density

/-- **Completed-time density of the complete-target capture event.**  Under a rationally
independent frequency packet the long-time density of the set of times at which the spectral orbit
reaches fidelity `a` with some member of a finite target family is at most the replica-moment
bound of the corresponding phase-box capture event. -/
theorem limsup_finiteTorusPhaseProbabilityMeasure_capture_le
    (frequency : d → ℝ) (hind : RationallyIndependentFrequency frequency)
    {p : d → ℝ} (hp : ∀ j, 0 ≤ p j) (hpsum : ∑ j, p j ≤ 1) {a : ℝ} (ha : 0 < a)
    (z : C → (d → ℂ)) (hz : ∀ c, finiteComplexInner (z c) (z c) = 1)
    (hznorm : ∀ c, ∑ j, ‖z c j‖ ^ 2 ≤ 1) (r : ℕ) :
    atTop.limsup (fun T => (finiteTorusPhaseProbabilityMeasure frequency T :
        Measure (UnitAddTorus d)) (torusCaptureTarget p a z)) ≤
      ENNReal.ofReal ((Module.finrank ℂ (replicaTargetSpan r z) : ℝ) * (r.factorial : ℝ) *
        (16 * occupationCollision p / a ^ 2) ^ r) := by
  classical
  refine le_trans (rationallyIndependent_closedTarget_limsup_le_volume frequency hind
    (isClosed_torusCaptureTarget p a z)) ?_
  have hbox := measureReal_capture_le_return_add_replicaMoment hp hpsum ha z hz hznorm
    (R := (∅ : Set (d → ℝ)))
    (Q := {x : d → ℝ | ∃ c, a ≤ finitePureStateFidelity (torusReplicaPhaseOrbit p x) (z c)})
    MeasurableSet.empty (fun x hx => hx.1) r
  rw [measureReal_empty, zero_add] at hbox
  have hle : (volume : Measure (UnitAddTorus d)).real (torusCaptureTarget p a z) ≤
      (Module.finrank ℂ (replicaTargetSpan r z) : ℝ) * (r.factorial : ℝ) *
        (16 * occupationCollision p / a ^ 2) ^ r := by
    rw [measureReal_torusCaptureTarget p a z]
    exact hbox
  have hfin : (volume : Measure (UnitAddTorus d)) (torusCaptureTarget p a z) ≠ ⊤ :=
    measure_ne_top _ _
  have hstep := ENNReal.ofReal_le_ofReal hle
  rwa [measureReal_def, ENNReal.ofReal_toReal hfin] at hstep

end Density

end GaloisForLFunctions.HTGeometry
