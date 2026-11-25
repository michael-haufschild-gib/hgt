import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.Winding.Subperiods.Midpoint.Width
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.FirstGate.FirstVisit
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.HarmonicRuns.ArcPowers

/-! # Exact harmonic rebound at an actual scalar entry -/

open Set Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PrecisionReturns.Winding.Harmonics
open Subperiods.Midpoint EmptyVisitFlux SharpOccupation
noncomputable section

private theorem flow_multiple {I : Type*} (w : I → ℝ) (t : ℝ) (m : ℕ) (i : I) :
    flow w ((m:ℝ)*t) i=m • flow w t i := by
  unfold flow
  rw [mul_assoc,←nsmul_eq_mul,AddCircle.coe_nsmul]

/-- At every multiple of a true entry the closing pair contributes exactly
the corresponding multiple of the prescribed closing angle, modulo one turn. -/
theorem closing_pair_at_multiple {N : ℕ} (H : selfAdjoint (Register N)) {a ε : ℝ}
    (he : ε∈Ioo (0:ℝ) (sqrt 2)) (hout : ε<orbitCircuitDistance H 0 a) (m : ℕ) :
    let v := firstVisit H a 0 ε
    let p := turnWidth H ((m:ℝ)*v)
    ∃ y∈Icc (-p) p, (y:UnitAddCircle)=(((m:ℝ)*physicalArc ε:ℝ):UnitAddCircle) := by
  intro v p
  let w := fun i => -H.2.isHermitian.eigenvalues i/(2*π)
  have hr := (physicalArc_spec he.1 he.2).1
  obtain ⟨_,hv⟩ := FirstGate.first_empty_entry_of_outside H he.1 he.2 hout
  obtain ⟨i,j,hface⟩ := (entry_iff_closed_face w hr.1.le hr.2).mp hv
  have hp := turnWidth_range H ((m:ℝ)*v)
  have hfit := (arc_iff_width H ((m:ℝ)*v) ⟨p,hp.1,hp.2.le⟩).mpr le_rfl
  obtain ⟨b,hb⟩ := HarmonicRuns.exists_anchor_lifts hp.1 hfit
  obtain ⟨u,hu,hi⟩ := hb i
  obtain ⟨s,hs,hj⟩ := hb j
  refine ⟨s-u,⟨by linarith only [hs.1,hu.2],by linarith only [hs.2,hu.1]⟩,?_⟩
  rw [AddCircle.coe_sub,hj,hi,sub_sub_sub_cancel_right]
  change flow w ((m:ℝ)*v) j-flow w ((m:ℝ)*v) i=_
  rw [flow_multiple,flow_multiple,←nsmul_sub,hface.2.1,←AddCircle.coe_nsmul,nsmul_eq_mul]

/-- Before the closing angle reaches half a turn, the shortest enclosing
arc grows exactly by the harmonic factor. This fixes the operator error
at every such multiple of the absolute first entry. -/
theorem first_entry_harmonic_distance {N : ℕ} (H : selfAdjoint (Register N)) {a ε : ℝ}
    (he : ε∈Ioo (0:ℝ) (sqrt 2)) (hout : ε<orbitCircuitDistance H 0 a)
    (m : ℕ) (hhalf : (m:ℝ)*physicalArc ε≤1/2) :
    orbitCircuitDistance H 0 ((m:ℝ)*firstVisit H a 0 ε)=2*sin ((m:ℝ)*arcsin (ε/2)) := by
  let v := firstVisit H a 0 ε
  let r := physicalArc ε
  let p := turnWidth H ((m:ℝ)*v)
  have hr := (physicalArc_spec he.1 he.2).1
  have hm : 0≤(m:ℝ)*r := mul_nonneg (Nat.cast_nonneg _) hr.1.le
  have hp := turnWidth_range H ((m:ℝ)*v)
  have hlo : (m:ℝ)*r≤p := by
    by_contra! hlt
    obtain ⟨y,hy,hy'⟩ := closing_pair_at_multiple H he hout m
    have h₀ : y∈Ico (-p) (-p+1) := ⟨hy.1,by linarith only [hy.2,hlt,hhalf]⟩
    have h₁ : (m:ℝ)*r∈Ico (-p) (-p+1) :=
      ⟨by linarith only [hp.1,hm],by linarith only [hlt,hhalf]⟩
    exact hlt.not_ge (((AddCircle.coe_eq_coe_iff_of_mem_Ico h₀ h₁).mp hy').symm.le.trans hy.2)
  have ht := (firstVisit_isLeast H a 0 he.1).1.2
  obtain ⟨b,z,hz⟩ := (anchored_iff hr.1.le).mp ((physical_visit H he.1 he.2 v).mpr ht)
  obtain ⟨y,hy⟩ := divide_turns (j:=m) (d:=1) hz (by decide) (fun _ => one_dvd _)
  simp only [Nat.cast_one,div_one] at hy
  have hhi : p≤(m:ℝ)*r := (arc_iff_width H ((m:ℝ)*v)
    ⟨(m:ℝ)*r,hm,hhalf.trans (by norm_num)⟩).mp ((anchored_iff hm).mpr ⟨b,y,hy⟩)
  rw [scalar_distance_eq_chord,show turnWidth H ((m:ℝ)*firstVisit H a 0 ε)=(m:ℝ)*r from le_antisymm hhi hlo]
  unfold zeroGateArcTolerance r physicalArc
  congr 2
  field_simp [pi_ne_zero]
  ring

#print axioms first_entry_harmonic_distance
end
end GaloisForLFunctions.HTGeometry.PrecisionReturns.Winding.Harmonics
