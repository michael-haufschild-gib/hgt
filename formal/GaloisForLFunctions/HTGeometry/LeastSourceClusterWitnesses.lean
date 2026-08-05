import GaloisForLFunctions.HTGeometry.PolynomialPhaseMomentGap
import GaloisForLFunctions.HTGeometry.PolynomialPhaseCluster

/-!
# The minimal cluster of the least source class is inhabited

The phase-lock arguments select the minimal signature cluster **inside** the least source class, and
the membership they consume is of that composite.  Both stages are nonempty for the corpus's own
reasons — each is the fibre of a minimum that is attained — so the composite is nonempty too.
-/

namespace GaloisForLFunctions

/-- **The minimal cluster of the least source class is nonempty.** -/
theorem polynomialPatternMinimalCluster_leastSourceClass_nonempty {M D R : ℕ}
    (S : Finset (Fin M → Fin (D + 1))) (hS : S.Nonempty) :
    (polynomialPatternMinimalCluster (R := R)
      (polynomialPatternLeastSourceClass S hS)
      (polynomialPatternLeastSourceClass_nonempty S hS)).Nonempty :=
  polynomialPatternMinimalCluster_nonempty _ _

/-- Existence form of the same membership. -/
theorem exists_mem_polynomialPatternMinimalCluster_leastSourceClass {M D R : ℕ}
    (S : Finset (Fin M → Fin (D + 1))) (hS : S.Nonempty) :
    ∃ p, p ∈ polynomialPatternMinimalCluster (R := R)
      (polynomialPatternLeastSourceClass S hS)
      (polynomialPatternLeastSourceClass_nonempty S hS) :=
  polynomialPatternMinimalCluster_leastSourceClass_nonempty S hS

end GaloisForLFunctions
