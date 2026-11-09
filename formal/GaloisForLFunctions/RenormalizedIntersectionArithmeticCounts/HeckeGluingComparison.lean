import GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts.HeckeArithmeticSections
import GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts.DivisorRelationGeometry
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Data.Nat.Prime.Infinite

/-!
# The original local-index sum inside the arithmetic section module

The integral gluing column embeds with its original conductor labels. Its
charge in the squarefree section quotient is exactly the determinant of the
original gluing presentation and the sum of the singular local indices.
Scalar multiplication of a divisor class and multiplication of its conductor
remain distinct operations.
-/

noncomputable section
open Finset ArithmeticFunction
namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
open ArithmeticDegenerationTheory

/-- The full arithmetic section module has the actual squarefree conductor basis. -/
def arithmeticSectionBasis :
    Module.Basis {n : ℕ // Squarefree n} ℤ ArithmeticSectionQuotient :=
  Finsupp.basisSingleOne.map arithmeticSectionQuotientEquiv.symm

/-- Retaining all conductor translates requires countably infinite integral rank. -/
theorem arithmeticSectionQuotient_rank :
    Module.rank ℤ ArithmeticSectionQuotient = Cardinal.aleph0 := by
  letI : Infinite {n : ℕ // Squarefree n} := Infinite.of_injective
    (fun p : Nat.Primes => (⟨p.val, p.property.squarefree⟩ : {n : ℕ // Squarefree n}))
    (fun p q h => Subtype.ext
      (congrArg (fun n : {n : ℕ // Squarefree n} => n.val) h))
  have h := arithmeticSectionBasis.mk_eq_rank
  simpa only [Cardinal.lift_id, Cardinal.mk_eq_aleph0] using h.symm

/-- Embed an actual finite integer conductor window by zero extension. -/
def arithmeticWindowProbe (N : ℕ) (v : Vertex N → ℤ) : ArithmeticSectionProbe :=
  ∑ n : Vertex N, Finsupp.single n.val (v n)

/-- Conductor dilation of an embedded window has the original arithmetic charge. -/
theorem arithmeticWindowProbe_dilated_charge (N a : ℕ) (v : Vertex N → ℤ) :
    arithmeticSectionCharge (arithmeticSectionDilation a (arithmeticWindowProbe N v)) =
      conductorDilatedCharge N a v := by
  simp only [arithmeticWindowProbe, map_sum, arithmeticSectionDilation_single,
    arithmeticSectionCharge, Finsupp.linearCombination_single, smul_eq_mul,
    conductorDilatedCharge]
  exact sum_congr rfl (fun n _ => mul_comm _ _)

/-- The global charge restricts to the actual integral divisor normal. -/
theorem arithmeticWindowProbe_charge (N : ℕ) (hN : 1 ≤ N) (v : Vertex N → ℤ) :
    arithmeticSectionCharge (arithmeticWindowProbe N v) = divisorNormal N hN v := by
  have h := arithmeticWindowProbe_dilated_charge N 1 v
  rw [arithmeticSectionDilation_one, LinearMap.id_apply] at h
  rw [h, divisorNormal_apply]
  simp only [conductorDilatedCharge, one_mul]

/-- The original negatively oriented gluing column, in the independent section quotient. -/
def arithmeticGluingSection (N : ℕ) : ArithmeticSectionQuotient :=
  Submodule.Quotient.mk (arithmeticWindowProbe N (integerGluingColumn N))

/-- The section charge is the original integer gluing determinant. -/
theorem arithmeticGluingSection_charge (N : ℕ) (hN : 1 ≤ N) :
    arithmeticSectionChargeOnQuotient (arithmeticGluingSection N) = integerGluingCharge N := by
  rw [arithmeticGluingSection, arithmeticSectionChargeOnQuotient_mk,
    arithmeticWindowProbe_charge N hN]
  exact integerMoebius_pole_row N hN

/-- The complete singular local-index sum survives in the Hecke-compatible section module. -/
theorem arithmeticGluingSection_localIndices (N : ℕ) (hN : 1 ≤ N) :
    arithmeticSectionChargeOnQuotient (arithmeticGluingSection N) =
      ∑ p, primeVertexRelativeIndex N N p := by
  rw [arithmeticGluingSection_charge N hN,
    primeVertexRelativeIndex_sum_mertens N N le_rfl hN]
  rfl

/-- Every conductor translate of the original gluing section retains its exact signed sum. -/
theorem arithmeticGluingSection_hecke_charge (N a : ℕ) :
    arithmeticSectionChargeOnQuotient (arithmeticSectionHecke a (arithmeticGluingSection N)) =
      ∑ n : Vertex N, moebius (a*n.val) * integerGluingColumn N n := by
  rw [arithmeticGluingSection, arithmeticSectionHecke_mk,
    arithmeticSectionChargeOnQuotient_mk, arithmeticWindowProbe_dilated_charge]
  rfl

#print axioms arithmeticSectionQuotient_rank
#print axioms arithmeticWindowProbe_dilated_charge
#print axioms arithmeticWindowProbe_charge
#print axioms arithmeticGluingSection_charge
#print axioms arithmeticGluingSection_localIndices
#print axioms arithmeticGluingSection_hecke_charge

end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
