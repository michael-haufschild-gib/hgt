import GaloisForLFunctions.RHTower.SelbergMaassMackeyOrbitDoubleCoset

/-!
# Hecke-coset form of rational Mackey blocks

Each actual rational Mackey block is an explicit stabilizer-index multiple of
one descended positive-rational Hecke trace.  This is the summand identity
needed before finite orbit fibers can be aggregated into correspondence
coefficients.
-/

namespace GaloisForLFunctions.RHTower

open Complex Set Filter Topology UpperHalfPlane ModularGroup
open Matrix SpecialLinearGroup GeneralLinearGroup OnePoint MulAction Subgroup
open scoped MatrixGroups ContDiff Pointwise

noncomputable section

/-- A rational Mackey block is its exact relative-index multiplicity times the
positive-rational Hecke trace of any Hecke element whose real matrix is the
block's rational correspondence. -/
theorem rationalMackey_blockTrace_eq_card_smul_rationalHeckeTrace
    (N : ℕ) (g h b : GL (Fin 2) ℚ)
    (r : rationalConjugateGroup N h)
    (hb : b.map (algebraMap ℚ ℝ) = r.val)
    (d : positiveRationalGLRealImage)
    (hdu : (g * h * b⁻¹).map (algebraMap ℚ ℝ) = d.val)
    (f : glUpperHalfPlaneInvariantFunctions (principalCongruenceGL N)) :
    let P := principalCongruenceGL N
    let G := rationalPullbackConjugateGroup (rationalConjugateGroup N g) h
    let H := rationalConjugateGroup N h
    let J := P.subgroupOf H
    let R := rationalConjugateGroup N (g * h * b⁻¹)
    let M := R ⊓ P
    letI : (rationalConjugateGroup N g).IsFiniteRelIndex P :=
      rationalConjugateGroup_isFiniteRelIndex N g
    letI : G.IsFiniteRelIndex H :=
      rationalPullback_isFiniteRelIndex (rationalConjugateGroup N g) P h
    let L := (MulAction.stabilizer J
      (QuotientGroup.mk r : H ⧸ (G.subgroupOf H))).map
        (H.subtype.comp J.subtype)
    let fG := rationalMaassPullbackInvariant_general (rationalConjugateGroup N g) h
      (rationalMaassPullbackInvariant_general P g f)
    let fL := maassDoubleCosetBlockPullback G H J r fG
    letI : R.IsFiniteRelIndex P := rationalConjugateGroup_isFiniteRelIndex N (g * h * b⁻¹)
    letI : M.IsFiniteRelIndex P := by
      rw [Subgroup.isFiniteRelIndex_iff_finiteIndex]
      have hsub : M.subgroupOf P = R.subgroupOf P := by
        apply (Subgroup.map_subtype_inj).mp
        rw [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype]
        simp only [M]
        rw [inf_assoc, inf_idem]
      rw [hsub]
      exact Subgroup.finiteIndex_of_finite_quotient
    letI : L.IsFiniteRelIndex M :=
      rationalMackey_blockSource_isFiniteRelIndex_rationalDoubleCosetSource N g h b r hb
    letI : L.IsFiniteRelIndex P :=
      ⟨Subgroup.relIndex_ne_zero_trans
        (Subgroup.relIndex_ne_zero (H := L) (K := M))
        (Subgroup.relIndex_ne_zero (H := M) (K := P))⟩
    letI : Fintype (M ⧸ (L.subgroupOf M)) := Fintype.ofFinite _
    maassTraceFunction (H := P) fL =
      (Fintype.card (M ⧸ (L.subgroupOf M)) : ℂ) •
        rationalPrincipalHeckeTrace N d f := by
  dsimp only
  let P : Subgroup (GL (Fin 2) ℝ) := principalCongruenceGL N
  let G : Subgroup (GL (Fin 2) ℝ) :=
    rationalPullbackConjugateGroup (rationalConjugateGroup N g) h
  let H : Subgroup (GL (Fin 2) ℝ) := rationalConjugateGroup N h
  let J : Subgroup H := P.subgroupOf H
  let R : Subgroup (GL (Fin 2) ℝ) := rationalConjugateGroup N (g * h * b⁻¹)
  let M : Subgroup (GL (Fin 2) ℝ) := R ⊓ P
  letI : (rationalConjugateGroup N g).IsFiniteRelIndex P :=
    rationalConjugateGroup_isFiniteRelIndex N g
  letI : G.IsFiniteRelIndex H :=
    rationalPullback_isFiniteRelIndex (rationalConjugateGroup N g) P h
  let L : Subgroup (GL (Fin 2) ℝ) :=
    (MulAction.stabilizer J
      (QuotientGroup.mk r : H ⧸ (G.subgroupOf H))).map
        (H.subtype.comp J.subtype)
  let fG : glUpperHalfPlaneInvariantFunctions G :=
    rationalMaassPullbackInvariant_general (rationalConjugateGroup N g) h
      (rationalMaassPullbackInvariant_general P g f)
  let fL : glUpperHalfPlaneInvariantFunctions L :=
    maassDoubleCosetBlockPullback G H J r fG
  letI : R.IsFiniteRelIndex P := rationalConjugateGroup_isFiniteRelIndex N (g * h * b⁻¹)
  have hsub : M.subgroupOf P = R.subgroupOf P := by
    apply (Subgroup.map_subtype_inj).mp
    rw [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype]
    simp only [M]
    rw [inf_assoc, inf_idem]
  letI : M.IsFiniteRelIndex P := by
    rw [Subgroup.isFiniteRelIndex_iff_finiteIndex, hsub]
    exact Subgroup.finiteIndex_of_finite_quotient
  letI : L.IsFiniteRelIndex M := by
    simpa only [P, G, H, J, R, M, L] using
      rationalMackey_blockSource_isFiniteRelIndex_rationalDoubleCosetSource N g h b r hb
  letI : L.IsFiniteRelIndex P :=
    ⟨Subgroup.relIndex_ne_zero_trans
      (Subgroup.relIndex_ne_zero (H := L) (K := M))
      (Subgroup.relIndex_ne_zero (H := M) (K := P))⟩
  letI : Fintype (M ⧸ (L.subgroupOf M)) := Fintype.ofFinite _
  have htrace := rationalPrincipalHeckeTrace_eq_rationalTrace_of_map N d (g * h * b⁻¹) hdu f
  rw [rationalMackey_blockTrace_eq_card_smul_rationalTrace N g h b r hb f, ← htrace]

end

end GaloisForLFunctions.RHTower
