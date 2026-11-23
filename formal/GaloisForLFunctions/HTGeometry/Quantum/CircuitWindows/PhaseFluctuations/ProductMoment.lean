import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseFluctuations.ConditionalMoment
import Mathlib.MeasureTheory.Constructions.Pi

/-! # Bounded differences for independent phase coordinates -/
open MeasureTheory ProbabilityTheory Set
namespace GaloisForLFunctions.HTGeometry.PhaseFluctuations
noncomputable section

/-- Revealing d independent coordinates of oscillation L gives
sub-Gaussian parameter d L²/4 for the centered observable. -/
theorem product_moment {X : Type*} [MeasurableSpace X] [Nonempty X]
    (μ : Measure X) [IsProbabilityMeasure μ] (L : NNReal) (d : ℕ)
    (f : (Fin d → X) → ℝ) (hf : Measurable f) {a b : ℝ} (hb : ∀ x, f x∈Icc a b)
    (hchange : ∀ i : Fin d, ∀ x y, (∀ j, j≠i → x j=y j) → f x-f y ≤ L) :
    let ν := Measure.pi (fun _ : Fin d => μ)
    HasSubgaussianMGF (fun x => f x-∫ y, f y ∂ν) (d*(L/2)^2) ν := by
  induction d with
  | zero =>
    have h := subgaussian_of_oscillation (Measure.pi (fun _ : Fin 0 => μ)) hf (fun x => (hb x).1)
      0 (fun x y => by rw [Subsingleton.elim x y,sub_self]; rfl)
    simpa using h
  | succ d ih =>
    let ν := Measure.pi (fun _ : Fin d => μ)
    let ρ := Measure.pi (fun _ : Fin (d+1) => μ)
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d+1) => X) 0
    have he : MeasurePreserving e ρ (μ.prod ν) := measurePreserving_piFinSuccAbove _ _
    let F (p : X × (Fin d → X)) := f (e.symm p)
    have hm : Measurable F := hf.comp e.symm.measurable
    have hcons (x : X) (y : Fin d → X) : e.symm (x,y)=Fin.cons x y := by
      simp [e,MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv]
    have hhead (x x' : X) (y : Fin d → X) : F (x,y)-F (x',y) ≤ L := by
      apply hchange 0
      rw [hcons,hcons]
      intro j
      refine Fin.cases (fun h => (h rfl).elim) (fun _ _ => rfl) j
    have htail (x : X) : HasSubgaussianMGF (fun y => F (x,y)-∫ z, F (x,z) ∂ν)
        (d*(L/2)^2) ν := by
      apply ih (fun y => F (x,y)) (hm.comp (measurable_const.prodMk measurable_id))
        (fun _ => hb _)
      intro i v w h
      apply hchange i.succ
      rw [hcons,hcons]
      intro j
      refine Fin.cases (fun _ => rfl) (fun k hne => ?_) j
      simpa only [Fin.cons_succ] using h k (fun hk => hne (congrArg Fin.succ hk))
    have h := subgaussian_product_step μ ν F hm (fun _ => hb _) L _ hhead htail
    have hmean : (∫ p, F p ∂(μ.prod ν))=∫ x, f x ∂ρ := he.symm.integral_comp' f
    rw [hmean,←he.map_eq] at h
    have hp := HasSubgaussianMGF.of_map he.measurable.aemeasurable h
    have hid (x) : F (e x)=f x := congrArg f (e.symm_apply_apply x)
    simpa only [Function.comp_def,hid,Nat.cast_succ,add_mul,one_mul] using hp

#print axioms product_moment
end
end GaloisForLFunctions.HTGeometry.PhaseFluctuations
