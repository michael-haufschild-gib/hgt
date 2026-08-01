import GaloisForLFunctions.HTGeometry.ProjectiveHorizonPostcriticalRigidity

/-!
# The postcritical reciprocal coefficient separates the critical fiber

Two states of the pure critical fiber have different constant terms of their left factors.  With no
new raw coefficient the first postcritical reciprocal coefficient is minus the inverse of that
constant term, and inversion is injective, so the two states receive different postcritical values.

So the postcritical reciprocal coefficient takes two values over one critical observation: it is not
a function of the critical data.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

/-- **The pure critical fiber is separated by the postcritical value.**  Two states with the same
critical observation receive different values of minus the inverse constant term, which is the
postcritical reciprocal coefficient at vanishing new raw coefficient. -/
theorem exists_pureCriticalRootFactorPairs_neg_inv_ne
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    ∃ S T : criticalHorizonOccupationStates m n,
      criticalHorizonLeftFactorFromRoots
          (pureCriticalRootLabeling (K := K) (by omega : 0 < m + n)) S *
        criticalHorizonRightFactorFromRoots
          (pureCriticalRootLabeling (K := K) (by omega : 0 < m + n)) S =
          pureCriticalCyclicPolynomial (K := K) (m + n) ∧
      criticalHorizonLeftFactorFromRoots
          (pureCriticalRootLabeling (K := K) (by omega : 0 < m + n)) T *
        criticalHorizonRightFactorFromRoots
          (pureCriticalRootLabeling (K := K) (by omega : 0 < m + n)) T =
          pureCriticalCyclicPolynomial (K := K) (m + n) ∧
      -((criticalHorizonLeftFactorFromRoots
          (pureCriticalRootLabeling (K := K) (by omega : 0 < m + n)) S).coeff 0)⁻¹ ≠
        -((criticalHorizonLeftFactorFromRoots
          (pureCriticalRootLabeling (K := K) (by omega : 0 < m + n)) T).coeff 0)⁻¹ := by
  obtain ⟨S, T, hS, hT, hne⟩ :=
    exists_pureCriticalRootFactorPairs_coeff_zero_ne (K := K) hm hn
  refine ⟨S, T, hS, hT, ?_⟩
  intro hcon
  exact hne (inv_inj.1 (neg_inj.1 hcon))

end GaloisForLFunctions.HTGeometry
