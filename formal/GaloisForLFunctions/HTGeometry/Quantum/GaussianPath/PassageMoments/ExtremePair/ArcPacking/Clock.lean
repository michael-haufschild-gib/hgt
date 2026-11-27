import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PassageMoments.ExtremePair.ArcPacking.Differences

/-! # A scalar return deadline from the Haar volume of phase packets -/
open MeasureTheory Set Finset
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry.PassageMoments.ExtremePair.ArcPacking
noncomputable section

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) := ⟨UnitAddCircle.measure_univ⟩

/-- More translates than the reciprocal arc mass force a pair to overlap.
Their positive index difference brings the unshifted clock into an arc of
twice the length. This applies even to a resonant clock. -/
theorem packed_tick {I : Type*} [Fintype I] [Nonempty I] (θ : I → UnitAddCircle)
    (r : Icc (0:ℝ) (1/2)) (N : ℕ)
    (hN : 1 < ((N:ℝ)+1)*((Fintype.card I:ℝ)*(r:ℝ)^(Fintype.card I-1))) :
    ∃ q : ℕ, 0<q ∧ q≤N ∧ q • θ∈enclosingUnitArc (2*(r:ℝ)) := by
  classical
  let A := enclosingUnitArc (ι:=I) r
  let C (k : Fin (N+1)) := (fun x : I → UnitAddCircle => x + k.val • θ) ⁻¹' A
  have hm : MeasurableSet A := (isClosed_enclosingUnitArc r).measurableSet
  have hC (k : Fin (N+1)) : volume.real (C k)=(Fintype.card I:ℝ)*(r:ℝ)^(Fintype.card I-1) := by
    have he := (measurePreserving_add_right (volume : Measure (I → UnitAddCircle)) (k.val • θ)).measure_preimage hm.nullMeasurableSet
    rw [Measure.real,show volume (C k)=volume A from he,volume_enclosingUnitArc r,
      ENNReal.toReal_mul,ENNReal.toReal_natCast,ENNReal.toReal_pow,ENNReal.toReal_ofReal r.2.1]
  by_contra! hn
  have hd : Pairwise fun k l => Disjoint (C k) (C l) := by
    suffices h : ∀ k l : Fin (N+1), k<l → Disjoint (C k) (C l) by
      intro k l hkl
      rcases lt_or_gt_of_ne hkl with h'|h'
      · exact h k l h'
      · exact (h l k h').symm
    intro k l hkl
    apply Set.disjoint_left.mpr
    intro x hk hl
    let q := l.val-k.val
    have hq : 0<q := Nat.sub_pos_of_lt hkl
    have hbound : q≤N := (Nat.sub_le ..).trans (Nat.lt_succ_iff.mp l.isLt)
    have he : l.val=q+k.val := (Nat.sub_add_cancel hkl.le).symm
    have h := arc_sub r.2.1 (x:=x+l.val • θ) (y:=x+k.val • θ) hl hk
    rw [he,add_nsmul] at h
    exact hn q hq hbound (by convert h using 1; abel)
  have hle := measureReal_mono (μ:=volume) (Set.subset_univ (⋃ k, C k))
  rw [measureReal_iUnion_fintype hd (fun k => hm.preimage (measurable_id.add_const _))
    (fun _ => measure_ne_top _ _),probReal_univ] at hle
  simp only [hC,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_one] at hle
  exact hN.not_ge hle

#print axioms packed_tick
end
end GaloisForLFunctions.HTGeometry.PassageMoments.ExtremePair.ArcPacking
