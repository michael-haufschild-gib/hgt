import GaloisForLFunctions.RHTower.PositiveSchattenLogResidueTraceClassPerturbation
import GaloisForLFunctions.RHTower.ConnesConsaniTraceClassReduction

/-!
# Connes--Consani residue perturbation capstone

This module combines the trace-class modulus-square reduction with logarithmic-residue stability.
If a compact distinguished block has a weak Schatten-one measurable modulus square, then adding any
trace-class remainder preserves both weak Schatten-one membership and the exact logarithmic residue
of the modulus square.  No positivity, compactness, or ideal premise on the full modulus square is
left to the caller.
-/

namespace RHTower

open ContinuousLinearMap

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A trace-class perturbation of a compact block preserves weak trace-ideal membership and the
exact measurable logarithmic residue of its modulus square. -/
theorem weakAndHasSchattenLogResidue_modulusSq_add_traceClass
    {E R : H →L[ℂ] H} (hEcpt : IsCompactOperator E) (hR : IsTraceClass R) {Q : ℝ}
    (hweak : MemWeakSchattenClass 1 (ContinuousLinearMap.adjoint E ∘L E))
    (hres : HasSchattenLogResidue 1 (ContinuousLinearMap.adjoint E ∘L E) Q) :
    MemWeakSchattenClass 1
        (ContinuousLinearMap.adjoint (E + R) ∘L (E + R)) ∧
      HasSchattenLogResidue 1
        (ContinuousLinearMap.adjoint (E + R) ∘L (E + R)) Q := by
  have hRmem : MemSchattenClass 1 R := IsTraceClass.memSchattenClass_one hR
  have hRcpt : IsCompactOperator R := hRmem.isCompactOperator one_pos
  have hERcpt : IsCompactOperator (E + R) := hEcpt.add hRcpt
  have hBcpt : IsCompactOperator (ContinuousLinearMap.adjoint E ∘L E) :=
    energyOp_compact hEcpt
  have hAcpt : IsCompactOperator
      (ContinuousLinearMap.adjoint (E + R) ∘L (E + R)) :=
    energyOp_compact hERcpt
  have hBpos : 0 ≤ ContinuousLinearMap.adjoint E ∘L E := by
    apply CStarAlgebra.nonneg_iff_eq_star_mul_self.mpr
    exact ⟨E, rfl⟩
  have hApos : 0 ≤ ContinuousLinearMap.adjoint (E + R) ∘L (E + R) := by
    apply CStarAlgebra.nonneg_iff_eq_star_mul_self.mpr
    exact ⟨E + R, rfl⟩
  have hdiff : MemSchattenClass 1
      (ContinuousLinearMap.adjoint (E + R) ∘L (E + R) -
        ContinuousLinearMap.adjoint E ∘L E) :=
    memSchattenClass_one_modulusSq_sub hR
  exact weakAndHasSchattenLogResidue_one_of_nonneg_traceClass_sub
    hAcpt hBcpt hApos hBpos hdiff hweak hres

end

end RHTower
