import GaloisForLFunctions.RHTower.SelbergMaassTraceCosetFactorization

/-!
# Multiplicity of a finite Maass trace on target-invariant data

When a source function is already invariant under the target subgroup, every
relative-coset summand agrees. The unnormalised finite trace is therefore the
relative quotient cardinality times that function. This is the coefficient
mechanism needed to turn Mackey stabilizer blocks into Hecke convolution
coefficients.
-/

namespace GaloisForLFunctions.RHTower

open Complex Set Filter Topology UpperHalfPlane ModularGroup
open Matrix SpecialLinearGroup GeneralLinearGroup OnePoint
open scoped MatrixGroups ContDiff

noncomputable section

/-- A finite trace of data which is already target-invariant is its relative
coset multiplicity times that data. -/
theorem maassTraceFunction_eq_card_smul_of_targetInvariant
    {G H : Subgroup (GL (Fin 2) ℝ)} [G.IsFiniteRelIndex H]
    (fG : glUpperHalfPlaneInvariantFunctions G)
    (fH : glUpperHalfPlaneInvariantFunctions H)
    (hfun : fG.1 = fH.1) :
    letI : Fintype (H ⧸ (G.subgroupOf H)) := Fintype.ofFinite _
    maassTraceFunction (H := H) fG =
      (Fintype.card (H ⧸ (G.subgroupOf H)) : ℂ) • fH.1 := by
  letI : Fintype (H ⧸ (G.subgroupOf H)) := Fintype.ofFinite _
  funext z
  unfold maassTraceFunction
  calc
    (∑ q : H ⧸ (G.subgroupOf H), maassTraceQuotientFunc fG q z) =
        ∑ _q : H ⧸ (G.subgroupOf H), fH.1 z := by
      apply Finset.sum_congr rfl
      intro q hq
      induction q using Quotient.inductionOn with
      | h h =>
        rw [maassTraceQuotientFunc_mk, hfun]
        exact fH.2 h⁻¹ z
    _ = (Fintype.card (H ⧸ (G.subgroupOf H)) : ℂ) • fH.1 z := by
      simp

/-- Along a nested finite-index chain, a source function already invariant
under the intermediate group contributes its relative-coset multiplicity to
the outer trace. -/
theorem maassTraceFunction_eq_card_smul_of_le_of_targetInvariant
    (L M K : Subgroup (GL (Fin 2) ℝ))
    [L.IsFiniteRelIndex M] [M.IsFiniteRelIndex K]
    (hLM : L ≤ M) (hMK : M ≤ K)
    (fL : glUpperHalfPlaneInvariantFunctions L)
    (fM : glUpperHalfPlaneInvariantFunctions M)
    (hfun : fL.1 = fM.1) :
    letI : L.IsFiniteRelIndex K :=
      ⟨Subgroup.relIndex_ne_zero_trans
        (Subgroup.relIndex_ne_zero (H := L) (K := M))
        (Subgroup.relIndex_ne_zero (H := M) (K := K))⟩
    letI : Fintype (M ⧸ (L.subgroupOf M)) := Fintype.ofFinite _
    maassTraceFunction (H := K) fL =
      (Fintype.card (M ⧸ (L.subgroupOf M)) : ℂ) •
        maassTraceFunction (H := K) fM := by
  letI : L.IsFiniteRelIndex K :=
    ⟨Subgroup.relIndex_ne_zero_trans
      (Subgroup.relIndex_ne_zero (H := L) (K := M))
      (Subgroup.relIndex_ne_zero (H := M) (K := K))⟩
  letI : Fintype (M ⧸ (L.subgroupOf M)) := Fintype.ofFinite _
  have hinner : maassTraceInvariant (H := M) fL =
      (Fintype.card (M ⧸ (L.subgroupOf M)) : ℂ) • fM := by
    apply Subtype.ext
    exact maassTraceFunction_eq_card_smul_of_targetInvariant fL fM hfun
  calc
    maassTraceFunction (H := K) fL =
        maassTraceFunction (H := K) (maassTraceInvariant (H := M) fL) :=
      maassTraceFunction_transitive hLM hMK fL
    _ = maassTraceFunction (H := K)
        ((Fintype.card (M ⧸ (L.subgroupOf M)) : ℂ) • fM) := by
      rw [hinner]
    _ = (Fintype.card (M ⧸ (L.subgroupOf M)) : ℂ) •
        maassTraceFunction (H := K) fM :=
      maassTraceFunction_smul _ fM

end

end GaloisForLFunctions.RHTower
