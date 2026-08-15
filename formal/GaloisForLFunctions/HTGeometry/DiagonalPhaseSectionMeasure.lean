import GaloisForLFunctions.HTGeometry.FiniteSpectralRecurrenceFrequencyLaw

/-!
# Common-phase quotients of the finite phase torus

A subset of the phase torus invariant under the diagonal circle action is determined by its
intersection with the section that anchors one coordinate at the origin.  Splitting the torus into
the anchored coordinate and its complement and translating each fibre by the anchored phase shows
that the Haar measure of such a set equals the Haar measure of the anchored slice.
-/

open MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {I : Type*} [Fintype I] [DecidableEq I]

instance isProbabilityMeasure_volume_unitAddTorus {K : Type*} [Fintype K] :
    IsProbabilityMeasure (volume : Measure (UnitAddTorus K)) := by
  rw [← finiteTorusHaarProbabilityMeasure_toMeasure_eq_volume]
  exact inferInstanceAs (IsProbabilityMeasure (Measure.pi fun _ : K => AddCircle.haarAddCircle))

section Section

/-- The section of the phase torus that anchors the reference coordinate at the origin. -/
def torusSection (ref : I) (g : UnitAddTorus {i : I // i ≠ ref}) : UnitAddTorus I :=
  fun i => if hi : i ≠ ref then g ⟨i, hi⟩ else 0

/-- Reassembly of a phase point from its nonreference and reference coordinates. -/
def torusCombine (ref : I) (g : UnitAddTorus {i : I // i ≠ ref})
    (h : UnitAddTorus {i : I // ¬ (i ≠ ref)}) : UnitAddTorus I :=
  fun i => if hi : i ≠ ref then g ⟨i, hi⟩ else h ⟨i, hi⟩

theorem continuous_torusSection (ref : I) :
    Continuous (torusSection ref : UnitAddTorus {i : I // i ≠ ref} → UnitAddTorus I) := by
  refine continuous_pi fun i => ?_
  by_cases hi : i ≠ ref
  · simpa [torusSection, hi] using continuous_apply (⟨i, hi⟩ : {i : I // i ≠ ref})
  · simpa [torusSection, hi] using continuous_const

theorem measurable_torusSection (ref : I) :
    Measurable (torusSection ref : UnitAddTorus {i : I // i ≠ ref} → UnitAddTorus I) :=
  (continuous_torusSection ref).measurable

/-- Reassembly is the anchored section of the recentred nonreference coordinates translated by the
reference phase. -/
theorem torusCombine_eq_torusSection_add (ref : I) (g : UnitAddTorus {i : I // i ≠ ref})
    (h : UnitAddTorus {i : I // ¬ (i ≠ ref)}) (hne : ¬ (ref ≠ ref)) :
    torusCombine ref g h =
      fun i => torusSection ref (fun j => g j - h ⟨ref, hne⟩) i + h ⟨ref, hne⟩ := by
  funext i
  by_cases hi : i ≠ ref
  · simp only [torusCombine, torusSection, dif_pos hi]
    abel
  · have hieq : (⟨i, hi⟩ : {i : I // ¬ (i ≠ ref)}) = ⟨ref, hne⟩ :=
      Subtype.ext (not_ne_iff.mp hi)
    simp only [torusCombine, torusSection, dif_neg hi, hieq, zero_add]

end Section

section Invariance

/-- A set of phase points invariant under the diagonal circle action. -/
def DiagonalPhaseInvariant (S : Set (UnitAddTorus I)) : Prop :=
  ∀ (c : UnitAddCircle) (x : UnitAddTorus I), ((fun i => x i + c) ∈ S ↔ x ∈ S)

/-- **The Haar measure of a diagonally invariant set is the Haar measure of its anchored slice.** -/
theorem measure_eq_measure_torusSection_preimage (ref : I) {S : Set (UnitAddTorus I)}
    (hS : MeasurableSet S) (hinv : DiagonalPhaseInvariant S) :
    (volume : Measure (UnitAddTorus I)) S =
      (volume : Measure (UnitAddTorus {i : I // i ≠ ref})) (torusSection ref ⁻¹' S) := by
  classical
  have hrefK : ¬ ((ref : I) ≠ ref) := by simp
  have hmp : MeasurePreserving
      (⇑(MeasurableEquiv.piEquivPiSubtypeProd (fun _ : I => UnitAddCircle) (fun i => i ≠ ref)))
      (volume : Measure (UnitAddTorus I))
      ((volume : Measure (UnitAddTorus {i : I // i ≠ ref})).prod
        (volume : Measure (UnitAddTorus {i : I // ¬ (i ≠ ref)}))) := by
    have h := measurePreserving_piEquivPiSubtypeProd
      (fun _ : I => (volume : Measure UnitAddCircle)) (fun i => i ≠ ref)
    rwa [← MeasureTheory.volume_pi, ← MeasureTheory.volume_pi, ← MeasureTheory.volume_pi] at h
  have hsymm := MeasurePreserving.symm
    (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : I => UnitAddCircle) (fun i => i ≠ ref)) hmp
  set E : Set (UnitAddTorus {i : I // i ≠ ref} × UnitAddTorus {i : I // ¬ (i ≠ ref)}) :=
    (⇑(MeasurableEquiv.piEquivPiSubtypeProd (fun _ : I => UnitAddCircle)
      (fun i => i ≠ ref)).symm) ⁻¹' S with hE
  have hEmeas : MeasurableSet E :=
    hS.preimage (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : I => UnitAddCircle)
      (fun i => i ≠ ref)).symm.measurable
  have hprod : (volume : Measure (UnitAddTorus I)) S =
      ((volume : Measure (UnitAddTorus {i : I // i ≠ ref})).prod
        (volume : Measure (UnitAddTorus {i : I // ¬ (i ≠ ref)}))) E :=
    (hsymm.measure_preimage hS.nullMeasurableSet).symm
  rw [hprod, Measure.prod_apply_symm hEmeas]
  have hslice : ∀ h : UnitAddTorus {i : I // ¬ (i ≠ ref)},
      ((fun g => (g, h)) ⁻¹' E) =
        (fun g : UnitAddTorus {i : I // i ≠ ref} =>
          (-(fun _ => h ⟨ref, hrefK⟩ : UnitAddTorus {i : I // i ≠ ref})) + g) ⁻¹'
            (torusSection ref ⁻¹' S) := by
    intro h
    ext g
    have hcomb : (⇑(MeasurableEquiv.piEquivPiSubtypeProd (fun _ : I => UnitAddCircle)
        (fun i => i ≠ ref)).symm) (g, h) = torusCombine ref g h := rfl
    have hrewrite : torusCombine ref g h =
        fun i => torusSection ref (fun j => g j - h ⟨ref, hrefK⟩) i + h ⟨ref, hrefK⟩ :=
      torusCombine_eq_torusSection_add ref g h hrefK
    have hshift : (-(fun _ => h ⟨ref, hrefK⟩ : UnitAddTorus {i : I // i ≠ ref})) + g =
        fun j => g j - h ⟨ref, hrefK⟩ := by
      funext j
      simp [sub_eq_neg_add]
    show (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : I => UnitAddCircle)
        (fun i => i ≠ ref)).symm (g, h) ∈ S ↔
      torusSection ref ((-(fun _ => h ⟨ref, hrefK⟩ : UnitAddTorus {i : I // i ≠ ref})) + g) ∈ S
    rw [hcomb, hrewrite, hshift]
    exact hinv (h ⟨ref, hrefK⟩) (torusSection ref fun j => g j - h ⟨ref, hrefK⟩)
  have hconst : ∀ h : UnitAddTorus {i : I // ¬ (i ≠ ref)},
      (volume : Measure (UnitAddTorus {i : I // i ≠ ref})) ((fun g => (g, h)) ⁻¹' E) =
        (volume : Measure (UnitAddTorus {i : I // i ≠ ref})) (torusSection ref ⁻¹' S) := by
    intro h
    rw [hslice h]
    exact measure_preimage_add _ _ _
  rw [lintegral_congr hconst, lintegral_const, measure_univ, mul_one]

end Invariance

end GaloisForLFunctions.HTGeometry
