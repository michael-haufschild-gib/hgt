import GaloisForLFunctions.RHTower.ConnesConsaniArchimedeanPoleTraceClass
import GaloisForLFunctions.RHTower.TraceNormLimit

namespace RHTower

noncomputable section

/-- Trace-class residue contribution `E_infinity + E_0` in Theorem 4.4. -/
def connesConsaniPoleRemainder (p : Nat.Primes) : CCMCircleL2 →L[ℂ] CCMCircleL2 :=
  connesConsaniArchimedeanPoleOperator p + connesConsaniDoublePoleOperator p

/-- The complete pole remainder away from the distinguished finite-prime block is trace class. -/
theorem connesConsaniPoleRemainder_memSchattenClass_one (p : Nat.Primes) :
    MemSchattenClass 1 (connesConsaniPoleRemainder p) := by
  exact (connesConsaniArchimedeanPoleOperator_memSchattenClass_one p).one_add
    (connesConsaniDoublePoleOperator_memSchattenClass_one p)

end

end RHTower
