import GaloisForLFunctions.RHTower.ConnesConsaniResiduePerturbationCapstone
import GaloisForLFunctions.RHTower.PrimeQuasiInnerResidueRigidity

/-!
# Sharp quasi-inner residue endpoint

Positive arithmetic residue turns trace-class perturbation invariance into the sharp weak
Schatten-one endpoint: the full positive energy remains measurable with the same residue and cannot
be trace class.  The prime specialization uses the literal one-prime residue scale.
-/

namespace RHTower

open ContinuousLinearMap

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A positive residue upgrades the perturbation capstone to the sharp endpoint exclusion. -/
theorem weakResidueAndNotTraceClass_modulusSq_add_traceClass
    {E R : H →L[ℂ] H} (hEcpt : IsCompactOperator E) (hR : IsTraceClass R) {Q : ℝ}
    (hQ : 0 < Q) (hweak : MemWeakSchattenClass 1 (adjoint E ∘L E))
    (hres : HasSchattenLogResidue 1 (adjoint E ∘L E) Q) :
    MemWeakSchattenClass 1 (adjoint (E + R) ∘L (E + R)) ∧
      HasSchattenLogResidue 1 (adjoint (E + R) ∘L (E + R)) Q ∧
      ¬ MemSchattenClass 1 (adjoint (E + R) ∘L (E + R)) := by
  obtain ⟨hfullWeak, hfullResidue⟩ :=
    weakAndHasSchattenLogResidue_modulusSq_add_traceClass hEcpt hR hweak hres
  exact ⟨hfullWeak, hfullResidue, hfullResidue.not_memSchattenClass hQ⟩

/-- The exact one-prime residue is positive, so every trace-class source completion of a compact
distinguished block with that residue remains weak Schatten one, measurable with the same literal
arithmetic value, and non-trace-class. -/
theorem primeQuasiInnerEnergy_weak_residue_not_traceClass_of_traceClassPerturbation
    (p : Nat.Primes) {E R : H →L[ℂ] H} (hEcpt : IsCompactOperator E) (hR : IsTraceClass R)
    (hweak : MemWeakSchattenClass 1 (adjoint E ∘L E))
    (hres : HasSchattenLogResidue 1 (adjoint E ∘L E)
      (primeQuasiInnerResidueScale (p : ℝ))) :
    MemWeakSchattenClass 1 (adjoint (E + R) ∘L (E + R)) ∧
      HasSchattenLogResidue 1 (adjoint (E + R) ∘L (E + R))
        (primeQuasiInnerResidueScale (p : ℝ)) ∧
      ¬ MemSchattenClass 1 (adjoint (E + R) ∘L (E + R)) := by
  have hp : (1 : ℝ) < (p : ℝ) := by
    exact_mod_cast p.2.two_le
  exact weakResidueAndNotTraceClass_modulusSq_add_traceClass
    hEcpt hR (primeQuasiInnerResidueScale_pos hp) hweak hres

end

end RHTower
