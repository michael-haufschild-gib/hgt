import GaloisForLFunctions.HTGeometry.CohenMacaulayDepth
import GaloisForLFunctions.HTGeometry.GradeLeDim
import GaloisForLFunctions.HTGeometry.IdealGrade
import GaloisForLFunctions.HTGeometry.RegularSequenceBridge

/-!
# Full grade of maximal-primary ideals in a Cohen--Macaulay local ring

The project definition of Cohen--Macaulayness supplies a regular sequence whose length is the
Krull dimension.  Its entries lie in the maximal ideal.  Rees's radical-invariance theorem for
grade then replaces that maximal ideal by any ideal having the same radical.
-/

namespace GaloisForLFunctions.HTGeometry

open IsLocalRing RingTheory.Sequence
open scoped Pointwise

universe u

/-- **A maximal-primary ideal in a Cohen--Macaulay local ring has full grade.** -/
theorem hasGradeGE_of_isCohenMacaulay_of_radical_eq_maximalIdeal
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (I : Ideal R) (d : ℕ)
    (hI : I • (⊤ : Submodule R R) < ⊤)
    (hrad : I.radical = maximalIdeal R)
    (hcm : IsCohenMacaulayRing R)
    (hdim : ringKrullDim R = ((d : ℕ∞) : WithBot ℕ∞)) :
    HasGradeGE I (ModuleCat.of R R) d := by
  obtain ⟨rs, hrs, hrsdim⟩ := hcm
  have hlen : rs.length = d := by
    have hcast : (((rs.length : ℕ∞) : WithBot ℕ∞)) = ((d : ℕ∞) : WithBot ℕ∞) := by
      rw [hrsdim, hdim]
    exact_mod_cast hcast
  have hproper : Ideal.ofList rs ≠ ⊤ := hrs.proper
  have hmem : ∀ r ∈ rs, r ∈ maximalIdeal R := by
    intro r hr
    exact IsLocalRing.le_maximalIdeal hproper (Ideal.subset_span hr)
  have hgradeMax : HasGradeGE (maximalIdeal R) (ModuleCat.of R R) d := by
    refine ⟨rs, hlen, hmem, ?_⟩
    exact (isRingRegularSeq_iff_isRegular rs).mp hrs
  have hmaxlt : maximalIdeal R • (⊤ : Submodule R R) < ⊤ := by
    exact maximalIdeal_smul_top_lt_top R
  apply hasGradeGE_of_radical_eq (I := maximalIdeal R) (J := I)
      ((by infer_instance : (maximalIdeal R).IsPrime).radical.trans hrad.symm)
      d (ModuleCat.of R R) hmaxlt hI hgradeMax

end GaloisForLFunctions.HTGeometry
