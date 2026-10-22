import GaloisForLFunctions.HTGeometry.HypertranscendentalKaehlerClockSymbol
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

namespace GaloisForLFunctions.RHTower

noncomputable section

open TensorProduct

/-- A nonzero old Kähler direction and the differential of one new transcendental coordinate
are linearly independent in the absolute Kähler module of the generated rational field. -/
theorem linearIndependent_mapBaseChange_and_D_adjoin_transcendental
    {C F E : Type*} [Field C] [Field F] [Field E]
    [Algebra C F] [Algebra C E] [Algebra F E] [IsScalarTower C F E]
    {tau : E} (htau : Transcendental F tau)
    (epsilon : KaehlerDifferential C F) (hepsilon : epsilon ≠ 0) :
    let x : Fin 1 → E := ![tau]
    let P := IntermediateField.adjoin F (Set.range x)
    let tauP : P :=
      ⟨tau, IntermediateField.subset_adjoin F (Set.range x) ⟨0, rfl⟩⟩
    LinearIndependent P ![
      KaehlerDifferential.mapBaseChange C F P (1 ⊗ₜ[F] epsilon),
      KaehlerDifferential.D C P tauP] := by
  classical
  dsimp only
  let x : Fin 1 → E := ![tau]
  let P := IntermediateField.adjoin F (Set.range x)
  let tauP : P :=
    ⟨tau, IntermediateField.subset_adjoin F (Set.range x) ⟨0, rfl⟩⟩
  have hx : AlgebraicIndependent F x := by
    rw [algebraicIndependent_iff_transcendental]
    simpa [x] using htau
  have hrelative : KaehlerDifferential.D F P tauP ≠ 0 := by
    have hLI := GaloisForLFunctions.HTGeometry.kaehlerD_adjoin_coordinates_linearIndependent hx
    exact hLI.ne_zero 0
  have htensor : (1 : P) ⊗ₜ[F] epsilon ≠ 0 := by
    intro hzero
    exact hepsilon
      (Module.FaithfullyFlat.one_tmul_eq_zero_iff F (KaehlerDifferential C F) epsilon |>.mp hzero)
  have hold : KaehlerDifferential.mapBaseChange C F P (1 ⊗ₜ[F] epsilon) ≠ 0 := by
    intro hzero
    apply htensor
    apply GaloisForLFunctions.HTGeometry.kaehlerMapBaseChange_injective_adjoin_of_algebraicIndependent hx
    simpa using hzero
  rw [Fintype.linearIndependent_iff]
  intro q hq i
  rw [Fin.sum_univ_two] at hq
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hq
  have hrelativeRelation := congrArg (KaehlerDifferential.map C F P P) hq
  rw [map_add, map_smul, map_smul, map_zero,
    GaloisForLFunctions.HTGeometry.kaehlerMap_comp_mapBaseChange_eq_zero
      (C := C) (x := x),
    KaehlerDifferential.map_D, smul_zero, zero_add] at hrelativeRelation
  have hq1 : q 1 = 0 := (smul_eq_zero.mp hrelativeRelation).resolve_right hrelative
  have hq0 : q 0 = 0 := by
    rw [hq1, zero_smul, add_zero] at hq
    exact (smul_eq_zero.mp hq).resolve_right hold
  fin_cases i
  · exact hq0
  · exact hq1

end


end GaloisForLFunctions.RHTower

