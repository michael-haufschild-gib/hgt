import GaloisForLFunctions.RHTower.SelbergMaassDoubleCosetOperator

/-!
# Representative-based double-coset blocks

This module chooses literal relative-coset representatives for orbit classes
and writes each block trace as the corresponding finite orbit sum.
-/

namespace GaloisForLFunctions.RHTower

open Complex Set Filter Topology UpperHalfPlane ModularGroup
open Matrix SpecialLinearGroup GeneralLinearGroup OnePoint MulAction
open scoped MatrixGroups ContDiff Pointwise

noncomputable section

/-- The orbit--stabilizer equivalence based on literal relative-coset
representatives. -/
noncomputable def maassTraceRepresentativeEquiv
    {G H : Subgroup (GL (Fin 2) ℝ)} (J : Subgroup H) :
    H ⧸ (G.subgroupOf H) ≃
      Σ q : Quotient (orbitRel J (H ⧸ (G.subgroupOf H))),
        J ⧸ MulAction.stabilizer J
          (QuotientGroup.mk q.out.out : H ⧸ (G.subgroupOf H)) :=
  MulAction.selfEquivSigmaOrbitsQuotientStabilizer' J
    (H ⧸ (G.subgroupOf H)) (maassTrace_orbitRepresentative_leftInverse J)

/-- The original trace summands in one representative-based orbit. -/
def maassDoubleCosetRepresentativeOrbitSum
    (G H : Subgroup (GL (Fin 2) ℝ)) [G.IsFiniteRelIndex H] (J : Subgroup H)
    (q : Quotient (orbitRel J (H ⧸ (G.subgroupOf H))))
    (f : glUpperHalfPlaneInvariantFunctions G) (z : ℍ) : ℂ := by
  letI : (MulAction.stabilizer J
      (QuotientGroup.mk q.out.out : H ⧸ (G.subgroupOf H))).FiniteIndex :=
    maassTrace_stabilizer_finiteIndex_at G H J (QuotientGroup.mk q.out.out)
  letI : Fintype (J ⧸ MulAction.stabilizer J
      (QuotientGroup.mk q.out.out : H ⧸ (G.subgroupOf H))) := Fintype.ofFinite _
  exact ∑ c, maassTraceQuotientFunc f
    ((maassTraceRepresentativeEquiv (G := G) J).symm ⟨q, c⟩) z

/-- A representative block trace equals its finite orbit sum of original trace
summands. -/
theorem maassDoubleCosetBlockTraceFunction_eq_representativeOrbitSum
    (G H : Subgroup (GL (Fin 2) ℝ)) [G.IsFiniteRelIndex H] (J : Subgroup H)
    (q : Quotient (orbitRel J (H ⧸ (G.subgroupOf H))))
    (f : glUpperHalfPlaneInvariantFunctions G) (z : ℍ) :
    maassDoubleCosetBlockTraceFunction G H J q.out.out f z =
      maassDoubleCosetRepresentativeOrbitSum G H J q f z := by
  rw [maassDoubleCosetBlockTraceFunction_eq_orbitSum]
  unfold maassDoubleCosetRepresentativeOrbitSum
  apply Finset.sum_congr rfl
  intro c hc
  induction c using Quotient.inductionOn with
  | h j =>
    rw [maassTraceOrbitSummand_mk]
    change maassTraceQuotientFunc f
      (j • (QuotientGroup.mk q.out.out : H ⧸ (G.subgroupOf H))) z =
        maassTraceQuotientFunc f ((maassTraceRepresentativeEquiv (G := G) J).symm
          ⟨q, QuotientGroup.mk j⟩) z
    rw [show maassTraceRepresentativeEquiv (G := G) J =
      MulAction.selfEquivSigmaOrbitsQuotientStabilizer' J
        (H ⧸ (G.subgroupOf H)) (maassTrace_orbitRepresentative_leftInverse J) by rfl,
      maassTrace_repSelfEquiv_inverse_mk]

end

end GaloisForLFunctions.RHTower
