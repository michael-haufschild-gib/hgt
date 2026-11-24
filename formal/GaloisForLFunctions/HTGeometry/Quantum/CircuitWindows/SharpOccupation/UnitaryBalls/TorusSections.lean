import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.UnitaryBalls.CircleSections
import Mathlib.Analysis.Fourier.AddCircleMulti

/-! # Measuring a phase target one coordinate section at a time -/
open MeasureTheory Set
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry.SharpOccupation.UnitaryBalls
noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]

omit [Fintype I] in
private theorem continuous_axis (i : I) : Continuous (Pi.single (M:=fun _ : I => UnitAddCircle) i) := by
  apply continuous_pi
  intro j
  by_cases h : j=i
  · subst j
    simp only [Pi.single_eq_same]
    exact continuous_id
  · simpa only [Pi.single_eq_of_ne h] using (continuous_const : Continuous (fun _ : UnitAddCircle => (0:UnitAddCircle)))

private theorem axis_average (i : I) {S : Set (UnitAddTorus I)} (hs : MeasurableSet S) :
    (∫⁻ x : UnitAddTorus I, volume {t : UnitAddCircle | x+Pi.single i t∈S})=volume S := by
  let A := {p : UnitAddTorus I × UnitAddCircle | p.1+Pi.single i p.2∈S}
  have hm : MeasurableSet A := hs.preimage (continuous_fst.add ((continuous_axis i).comp continuous_snd)).measurable
  change (∫⁻ x : UnitAddTorus I, volume ((Prod.mk x) ⁻¹' A))=_
  rw [←Measure.prod_apply hm,Measure.prod_apply_symm hm]
  have h (t : UnitAddCircle) : volume ((fun x : UnitAddTorus I => (x,t)) ⁻¹' A) = volume S :=
    by
      change volume ((fun x : UnitAddTorus I => x+Pi.single (M:=fun _ : I => UnitAddCircle) i t) ⁻¹' S)=volume S
      exact (measurePreserving_add_right volume (Pi.single (M:=fun _ : I => UnitAddCircle) i t)).measure_preimage hs.nullMeasurableSet
  simp only [h,lintegral_const,UnitAddCircle.measure_univ,mul_one]

/-- Eroding each proper coordinate section by a segment of length g
costs a factor of at least 1/(1-g) in product Haar measure. -/
theorem axis_section_bound (i : I) {A B : Set (UnitAddTorus I)} (hA : MeasurableSet A)
    (hB : MeasurableSet B) {g : ℝ} (hg : 0≤g) (hg' : g<1)
    (hcut : ∀ x : UnitAddTorus I, ∃ t : UnitAddCircle, x+Pi.single i t∉B)
    (hseg : ∀ x∈A, ∀ t∈Icc (0:ℝ) g, x+Pi.single i (t:UnitAddCircle)∈B) :
    volume A ≤ ENNReal.ofReal (1-g)*volume B := by
  let F (S : Set (UnitAddTorus I)) (x : UnitAddTorus I) :=
    {t : UnitAddCircle | x+Pi.single i t∈S}
  have hs (S : Set (UnitAddTorus I)) (h : MeasurableSet S) (x : UnitAddTorus I) :
      MeasurableSet (F S x) := h.preimage (continuous_const.add (continuous_axis i)).measurable
  have hp (x : UnitAddTorus I) : volume (F A x)≤ENNReal.ofReal (1-g)*volume (F B x) := by
    obtain ⟨c,hc⟩ := hcut x
    refine circle_section_bound (hs A hA x) (hs B hB x) hg hg' c hc ?_
    intro u hu t ht
    change x+Pi.single i (u+(t:UnitAddCircle)) ∈ B
    rw [Pi.single_add,←add_assoc]
    exact hseg _ hu _ ht
  rw [←axis_average i hA,←axis_average i hB,←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact lintegral_mono hp

#print axioms axis_section_bound
end
end GaloisForLFunctions.HTGeometry.SharpOccupation.UnitaryBalls
