import GaloisForLFunctions.RHTower.CCM.CCMRationalFiniteAdeleNonarchimedean
import GaloisForLFunctions.RHTower.FieldOneFiniteAdeleIntegralBruhatTest
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.GroupTheory.OrderOfElement

/-!
# Positive integer periods inside finite-adele open subgroups

Every open additive subgroup of the rational finite adeles contains a positive
diagonal integer.  The proof intersects with the compact open subgroup of
integral finite adeles.  Its open quotient is finite, so the class of the
diagonal unit has finite positive additive order.

Consequently every finite-adele Bruhat function is periodic along the diagonal
integer lattice.  This is the arithmetic compactness law needed to replace an
infinite rational trace by finitely many residue weights.
-/

noncomputable section

open Filter Set Topology
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace GaloisForLFunctions
namespace RHTower

/-- **Integral period law for rational finite adeles.** Every open additive
subgroup contains a positive diagonal integer. -/
theorem ccmRationalFiniteAdele_openAddSubgroup_exists_positiveInteger
    (V : OpenAddSubgroup CCMRationalFiniteAdele) :
    ∃ M : ℕ, 0 < M ∧ (M : CCMRationalFiniteAdele) ∈ V := by
  let H := fieldOneFiniteAdeleIntegralAddSubgroup
  letI : CompactSpace H :=
    isCompact_iff_compactSpace.mp
      fieldOneFiniteAdeleIntegralAddSubgroup_isCompact
  let W : OpenAddSubgroup H :=
    V.comap H.subtype continuous_subtype_val
  let oneH : H := ⟨1, fun v =>
    coe_mem_adicCompletionIntegers (K := ℚ) v 1⟩
  let a : H ⧸ W.toAddSubgroup :=
    QuotientAddGroup.mk' W.toAddSubgroup oneH
  let M : ℕ := addOrderOf a
  refine ⟨M, addOrderOf_pos a, ?_⟩
  have hz : QuotientAddGroup.mk' W.toAddSubgroup (M • oneH) = 0 := by
    rw [map_nsmul]
    exact addOrderOf_nsmul_eq_zero a
  have hmem : M • oneH ∈ W.toAddSubgroup :=
    (QuotientAddGroup.eq_zero_iff (M • oneH)).mp hz
  change ((M • oneH : H) : CCMRationalFiniteAdele) ∈ V at hmem
  simpa [oneH, nsmul_one] using hmem

/-- Every rational finite-adele Bruhat function has a positive diagonal
integer period, uniformly at every finite adele. -/
theorem ccmRationalFiniteBruhat_exists_positiveIntegerPeriod
    (f : CCMRationalFiniteBruhatSchwartz) :
    ∃ M : ℕ, 0 < M ∧ ∀ x : CCMRationalFiniteAdele,
      f.1 (x + (M : CCMRationalFiniteAdele)) = f.1 x := by
  letI : NonarchimedeanAddGroup CCMRationalFiniteAdele :=
    ccmRationalFiniteAdele_nonarchimedeanAddGroup
  obtain ⟨V, hV⟩ :=
    ccmRationalFiniteBruhat_exists_openAddSubgroup_stabilizer f
  obtain ⟨M, hM, hMV⟩ :=
    ccmRationalFiniteAdele_openAddSubgroup_exists_positiveInteger V
  refine ⟨M, hM, fun x => ?_⟩
  exact hV x ⟨(M : CCMRationalFiniteAdele), hMV⟩

end RHTower
end GaloisForLFunctions
