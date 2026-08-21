import GaloisForLFunctions.HTGeometry.WittenAsymptoticExpansion
import GaloisForLFunctions.RHTower.Sieve.ConcreteRoot
import GaloisForLFunctions.RHTower.Sieve.RootsOfUnityFrequencies

/-!
# Exact abelian Chern--Simons asymptotics on cyclic linking data

For a rational homology three-manifold with cyclic torsion linking datum `q / p`, the finite
flat-sector part of the abelian Chern--Simons partition function is the Gaussian phase sum over
`Z / pZ`.  This file formalizes that finite-sector expression and proves its exact all-orders
phase expansion.  It is a calibration theorem for the abelian theory, not a claim about the
non-abelian `SU(2)` WRT invariant.
-/

open Filter Topology Asymptotics
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

open RHTower.Sieve

/-- Chern--Simons phase of a cyclic flat sector with quadratic linking action `q a² / p`. -/
noncomputable def cyclicChernSimonsPhase (p q : ℕ) (a : Fin p) : ℂ :=
  (rootOfUnity p) ^ (q * (a : ℕ) ^ 2)

/-- Finite flat-sector contribution of abelian Chern--Simons theory on cyclic linking data. -/
noncomputable def cyclicChernSimonsPartition (p q : ℕ) (n : ℕ) : ℂ :=
  ∑ a : Fin p, (cyclicChernSimonsPhase p q a) ^ n

/-- Constant amplitude assigned to every isolated abelian flat sector. -/
def cyclicChernSimonsCoefficient {p : ℕ} (_ : Fin p) (j : ℕ) : ℂ :=
  if j = 0 then 1 else 0

/-- The finite flat-sector formula is exactly a degree-zero Chern--Simons phase expansion. -/
theorem cyclicChernSimonsPartition_exactExpansion (p q : ℕ) :
    HasExactFinitePhasePolynomialExpansion (cyclicChernSimonsPartition p q) Finset.univ
      (cyclicChernSimonsPhase p q) cyclicChernSimonsCoefficient 0 := by
  funext n
  simp [cyclicChernSimonsPartition, finitePhasePolynomial, cyclicChernSimonsCoefficient]

/-- Every finite flat-sector phase is unimodular at positive torsion order. -/
theorem norm_cyclicChernSimonsPhase {p q : ℕ} (hp : 0 < p) (a : Fin p) :
    ‖cyclicChernSimonsPhase p q a‖ = 1 := by
  unfold cyclicChernSimonsPhase
  exact norm_pow_eq_one_of_isPrimitiveRoot hp
    (isPrimitiveRoot_rootOfUnity hp.ne') _

/-- Every cyclic flat-sector phase has torsion dividing the linking denominator. -/
theorem cyclicChernSimonsPhase_pow_linkingOrder {p q : ℕ} (hp : 0 < p) (a : Fin p) :
    (cyclicChernSimonsPhase p q a) ^ p = 1 := by
  change ((rootOfUnity p) ^ (q * (a : ℕ) ^ 2)) ^ p = 1
  calc
    ((rootOfUnity p) ^ (q * (a : ℕ) ^ 2)) ^ p =
        (rootOfUnity p) ^ ((q * (a : ℕ) ^ 2) * p) :=
      (pow_mul _ _ _).symm
    _ = (rootOfUnity p) ^ (p * (q * (a : ℕ) ^ 2)) := by rw [Nat.mul_comm]
    _ = ((rootOfUnity p) ^ p) ^ (q * (a : ℕ) ^ 2) := pow_mul _ p _
    _ = 1 := by rw [(isPrimitiveRoot_rootOfUnity hp.ne').pow_eq_one, one_pow]

/-- The finite abelian flat-sector partition function is exactly periodic in the level with
period the cyclic linking denominator. -/
theorem cyclicChernSimonsPartition_periodic {p q : ℕ} (hp : 0 < p) (n : ℕ) :
    cyclicChernSimonsPartition p q (n + p) = cyclicChernSimonsPartition p q n := by
  unfold cyclicChernSimonsPartition
  apply Finset.sum_congr rfl
  intro a _
  rw [pow_add, cyclicChernSimonsPhase_pow_linkingOrder hp a, mul_one]

/-- The cyclic abelian Chern--Simons finite-sector formula has zero remainder at every order. -/
theorem cyclicChernSimonsPartition_hasAllOrdersRemainder (p q : ℕ) :
    HasAllOrdersFinitePhasePolynomialRemainder (cyclicChernSimonsPartition p q) Finset.univ
      (cyclicChernSimonsPhase p q) cyclicChernSimonsCoefficient 0 :=
  (cyclicChernSimonsPartition_exactExpansion p q).hasAllOrdersRemainder

/-- Positive-order cyclic abelian Chern--Simons partition functions are uniformly bounded in
the level. -/
theorem cyclicChernSimonsPartition_isBigO {p q : ℕ} (hp : 0 < p) :
    cyclicChernSimonsPartition p q =O[atTop] fun _ : ℕ => (1 : ℂ) := by
  simpa using (cyclicChernSimonsPartition_exactExpansion p q).isBigO
    (fun a _ => norm_cyclicChernSimonsPhase hp a)

end GaloisForLFunctions.HTGeometry
