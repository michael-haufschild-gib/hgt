import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.Winding.Subperiods.Midpoint.GapLifts
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.Winding.Subperiods.Midpoint.Width

/-! # Spectral width halfway across an actual empty-circuit gap -/

open Set Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PrecisionReturns.Winding.Subperiods.Midpoint
open EmptyVisitFlux SharpOccupation
noncomputable section

/-- A bounded empty-circuit gap has an approximately semicircular midpoint
spectrum. Both endpoints use the same fixed physical approximation error. -/
theorem gap_midpoint_width {N : ℕ} (H : selfAdjoint (Register N)) {u v ε : ℝ}
    (he : ε∈Ioo (0:ℝ) (sqrt 2)) (hu : orbitCircuitDistance H 0 u≤ε)
    (hv : orbitCircuitDistance H 0 v≤ε) (hm : ε<orbitCircuitDistance H 0 ((u+v)/2)) :
    turnWidth H ((u+v)/2) ∈ Icc (1/2-physicalArc ε) (1/2+physicalArc ε) := by
  let r := physicalArc ε
  let m := (u+v)/2
  let w := fun j => -H.2.isHermitian.eigenvalues j/(2*π)
  have hr := (physicalArc_spec he.1 he.2).1
  have hfit (t : ℝ) : flow w t∈enclosingUnitArc r ↔ orbitCircuitDistance H 0 t≤ε :=
    (physical_visit H he.1 he.2 t).trans (hasProjectiveCircuitApproximation_iff_infDist _ 0 ε)
  obtain ⟨ht,hlo⟩ := midpoint_arc_alternative hr.1.le ((hfit u).mpr hu) ((hfit v).mpr hv)
  have hw := turnWidth_range H m
  constructor
  · by_contra! h
    apply hm.not_ge
    apply (hfit m).mp
    apply hlo (turnWidth H m) hw.1 (by
      change turnWidth H m<1/2-r at h
      linarith only [h])
    exact (arc_iff_width H m ⟨_,hw.1,hw.2.le⟩).mpr le_rfl
  · have hupper : 1/2+r ∈ Icc (0:ℝ) 1 := by
      change 0≤1/2+physicalArc ε ∧ 1/2+physicalArc ε≤1
      constructor <;> linarith only [hr.1,hr.2]
    exact (arc_iff_width H m ⟨_,hupper⟩).mp ht

/-- From any positive exterior observation time, take the last affordable
date on its left and the first on its right. The open interval is a single
excursion and its midpoint lies in the two-cluster width band. -/
theorem first_gap {N : ℕ} (H : selfAdjoint (Register N)) {a ε : ℝ}
    (ha : 0<a) (he : ε∈Ioo (0:ℝ) (sqrt 2)) (hout : ε<orbitCircuitDistance H 0 a) :
    let v := firstVisit H a 0 ε
    ∃ u : ℝ, IsGreatest {t : ℝ | 0≤t ∧ t≤a ∧ orbitCircuitDistance H 0 t≤ε} u ∧
      u<a ∧ a<v ∧ (∀ t∈Ioo u v, ε<orbitCircuitDistance H 0 t) ∧
      turnWidth H ((u+v)/2)∈Icc (1/2-physicalArc ε) (1/2+physicalArc ε) := by
  intro v
  let S := {t : ℝ | 0≤t ∧ t≤a ∧ orbitCircuitDistance H 0 t≤ε}
  have hclosed : IsClosed S := isClosed_Ici.inter (isClosed_Iic.inter
    (isClosed_le (orbitCircuitDistance_lipschitz H 0).continuous continuous_const))
  have hzero : orbitCircuitDistance H 0 0≤ε := by
    apply (hasProjectiveCircuitApproximation_iff_infDist _ 0 ε).mp
    refine ⟨1,norm_one,TwoQubitCircuit.one N,by rfl,?_⟩
    simpa [TwoQubitCircuit.one_eval,unitaryEvolution] using he.1.le
  have hu := hclosed.isGreatest_csSup (show S.Nonempty from ⟨0,le_rfl,ha.le,hzero⟩)
    (show BddAbove S from ⟨a,fun _ h => h.2.1⟩)
  let u := sSup S
  have hfitU : orbitCircuitDistance H 0 u≤ε := hu.1.2.2
  have hua : u<a := lt_of_le_of_ne hu.1.2.1 (fun h => hout.not_ge (h ▸ hfitU))
  have hV := firstVisit_isLeast H a 0 he.1
  have hv : orbitCircuitDistance H 0 v≤ε := (hasProjectiveCircuitApproximation_iff_infDist _ 0 ε).mp hV.1.2
  have hav : a<v := lt_of_le_of_ne hV.1.1 (fun h => hout.not_ge (h.symm ▸ hv))
  have hgap (t : ℝ) (ht : t∈Ioo u v) : ε<orbitCircuitDistance H 0 t := by
    by_contra! hfit
    by_cases hta : t≤a
    · exact ht.1.not_ge (hu.2 ⟨hu.1.1.trans ht.1.le,hta,hfit⟩)
    · exact ht.2.not_ge (hV.2 ⟨(not_le.mp hta).le,(hasProjectiveCircuitApproximation_iff_infDist _ 0 ε).mpr hfit⟩)
  refine ⟨u,hu,hua,hav,hgap,gap_midpoint_width H he hu.1.2.2 hv (hgap _ ?_)⟩
  constructor <;> linarith only [hua,hav]

#print axioms first_gap
end
end GaloisForLFunctions.HTGeometry.PrecisionReturns.Winding.Subperiods.Midpoint
