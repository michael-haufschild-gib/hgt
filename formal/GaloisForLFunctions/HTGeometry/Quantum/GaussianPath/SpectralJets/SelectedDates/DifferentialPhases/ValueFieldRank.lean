import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.DifferentialPhases.HorizontalDefects
import GaloisForLFunctions.HTGeometry.KaehlerRankTranscendenceDegree

/-! # Rank of a field containing the actions and their exponentials -/

namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.DifferentialPhases
open GaloisForLFunctions.RHTower
noncomputable section
variable {k L : Type} [Field k] [Field L] [Algebra k L] [CharZero k]

/-- Independent exponential defects descend to every field of values.
Evaluation on the ambient derivation detects an additional independent
action differential, even if the value field is not closed under differentiation. -/
theorem value_field_rank {n : ℕ} (K : IntermediateField k L) (x y : Fin n → K)
    (δ : Derivation k L L) (he : ∀ i, δ (y i:L)=(y i:L)*δ (x i:L)) (hy : ∀ i, (y i:L)≠0)
    (hi : LinearIndependent L (fun i => valueDefect (C:=k) (x i:L) (y i:L)))
    (j : Fin n) (hj : δ (x j:L)≠0) : ((n+1:ℕ):Cardinal)≤Algebra.trdeg k K := by
  classical
  let Φ := KaehlerDifferential.map k k K L
  let v (i : Fin n) := valueDefect (C:=k) (x i) (y i)
  have hΦ (i) : Φ (v i)=valueDefect (C:=k) (x i:L) (y i:L) := by
    simp only [Φ,v,valueDefect,map_sub,map_smul,KaehlerDifferential.map_D,IntermediateField.algebraMap_apply]
    rw [←IsScalarTower.algebraMap_smul (A:=L) (M:=KaehlerDifferential k L) ((y i)⁻¹),
      map_inv₀,IntermediateField.algebraMap_apply]
  have hk : LinearIndependent K v := by
    apply Fintype.linearIndependent_iff.mpr
    intro c hc
    have hh := congrArg Φ hc
    simp only [map_sum,map_smul,map_zero,hΦ] at hh
    simp_rw [←IsScalarTower.algebraMap_smul (R:=K) (A:=L) (M:=KaehlerDifferential k L)] at hh
    have hz := (Fintype.linearIndependent_iff.mp hi) (fun i => (c i:L)) hh
    exact fun i => Subtype.ext (hz i)
  let Z := (δ.liftKaehlerDifferential.restrictScalars K).comp Φ
  have hz (i) : Z (v i)=0 := by
    change δ.liftKaehlerDifferential (Φ (v i))=0
    rw [hΦ,valueDefect,map_sub,map_smul,δ.liftKaehlerDifferential_comp_D,δ.liftKaehlerDifferential_comp_D,
      he,smul_eq_mul,inv_mul_cancel_left₀ (hy i),sub_self]
  let u := KaehlerDifferential.D k K (x j)
  have hu : Z u≠0 := by
    change δ.liftKaehlerDifferential (KaehlerDifferential.map k k K L (KaehlerDifferential.D k K (x j)))≠0
    rwa [KaehlerDifferential.map_D,δ.liftKaehlerDifferential_comp_D]
  have hall : LinearIndependent K (Fin.cons u v) := by
    apply Fintype.linearIndependent_iff.mpr
    intro c hc
    rw [Fin.sum_univ_succ,Fin.cons_zero] at hc
    simp only [Fin.cons_succ] at hc
    have hh := congrArg Z hc
    simp only [map_add,map_sum,map_smul,hz,smul_zero,Finset.sum_const_zero,add_zero,map_zero] at hh
    have hc0 := (smul_eq_zero.mp hh).resolve_right hu
    rw [hc0,zero_smul,zero_add] at hc
    exact Fin.cases hc0 ((Fintype.linearIndependent_iff.mp hk) (fun i => c i.succ) hc)
  rw [←rank_kaehlerDifferential_eq_trdeg]
  simpa only [Cardinal.mk_fintype,Fintype.card_fin] using hall.cardinal_le_rank

#print axioms value_field_rank
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.DifferentialPhases
