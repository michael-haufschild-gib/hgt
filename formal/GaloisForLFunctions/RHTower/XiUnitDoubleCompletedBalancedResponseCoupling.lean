import GaloisForLFunctions.RHTower.XiUnitDoubleCompletedOffDiagonalResponse
import GaloisForLFunctions.RHTower.XiAperturePhysicalEndpointResponseRenormalization

/-!
# Forced finite balanced coupling of the completed unit--double response

The completed seam response supplies a real-symmetric off-diagonal prime-ratio kernel.  The
physical pair weights dress that kernel, while the source-derived unit--double current fixes its
one-prime marginal.  On every finite packet these two requirements force the diagonal uniquely.

This is a signed response joining, not a positive Gram.  The module proves its symmetry, exact
marginals, and entrywise uniqueness.  It does not identify the joining with the corrected AC25
response or assert an RH estimate.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

/-- Real-symmetric completed response sampled at two actual prime-log nodes. -/
def xiUnitDoubleCompletedPrimeRatioRealKernel
    (p q : Nat.Primes) : ℝ :=
  (xiUnitDoubleCompletedOffDiagonalResponseKernel
    (Real.log (p : ℝ)) (Real.log (q : ℝ))).re

theorem xiUnitDoubleCompletedPrimeRatioRealKernel_symm
    (p q : Nat.Primes) :
    xiUnitDoubleCompletedPrimeRatioRealKernel p q =
      xiUnitDoubleCompletedPrimeRatioRealKernel q p := by
  have h := congrArg Complex.re
    (xiUnitDoubleCompletedOffDiagonalResponseKernel_swap
      (Real.log (p : ℝ)) (Real.log (q : ℝ)))
  change xiUnitDoubleCompletedPrimeRatioRealKernel q p =
    xiUnitDoubleCompletedPrimeRatioRealKernel p q at h
  exact h.symm

/-- Physical pair coefficient dressing of the real completed seam response. -/
def xiUnitDoubleCompletedPhysicalPairResponse
    (p q : Nat.Primes) : ℝ :=
  physicalPrimeEndpointWeight p * physicalPrimeEndpointWeight q *
    xiUnitDoubleCompletedPrimeRatioRealKernel p q

theorem xiUnitDoubleCompletedPhysicalPairResponse_symm
    (p q : Nat.Primes) :
    xiUnitDoubleCompletedPhysicalPairResponse p q =
      xiUnitDoubleCompletedPhysicalPairResponse q p := by
  rw [xiUnitDoubleCompletedPhysicalPairResponse,
    xiUnitDoubleCompletedPhysicalPairResponse,
    xiUnitDoubleCompletedPrimeRatioRealKernel_symm]
  ring

/-- The unique finite diagonal correction which retains the completed seam response off diagonal
and gives each row the source-forced unit--double current marginal. -/
def xiUnitDoubleCompletedBalancedResponseCoupling
    (P : Finset Nat.Primes) (p q : Nat.Primes) : ℝ :=
  if p = q then
    xiUnitDoubleFusedPrimeResponseCurrent p -
      ∑ r ∈ P.erase p, xiUnitDoubleCompletedPhysicalPairResponse p r
  else xiUnitDoubleCompletedPhysicalPairResponse p q

/-- The forced finite response joining is symmetric. -/
theorem xiUnitDoubleCompletedBalancedResponseCoupling_symm
    (P : Finset Nat.Primes) (p q : Nat.Primes) :
    xiUnitDoubleCompletedBalancedResponseCoupling P p q =
      xiUnitDoubleCompletedBalancedResponseCoupling P q p := by
  by_cases hpq : p = q
  · subst q
    rfl
  · rw [xiUnitDoubleCompletedBalancedResponseCoupling,
      xiUnitDoubleCompletedBalancedResponseCoupling,
      if_neg hpq, if_neg (fun h => hpq h.symm),
      xiUnitDoubleCompletedPhysicalPairResponse_symm]

/-- Every row of the balanced completed response has exactly the diagonal unit--double current
as its marginal. -/
theorem sum_xiUnitDoubleCompletedBalancedResponseCoupling
    (P : Finset Nat.Primes) (p : Nat.Primes) (hp : p ∈ P) :
    ∑ q ∈ P, xiUnitDoubleCompletedBalancedResponseCoupling P p q =
      xiUnitDoubleFusedPrimeResponseCurrent p := by
  have hoff :
      (∑ q ∈ P.erase p,
        xiUnitDoubleCompletedBalancedResponseCoupling P p q) =
      ∑ q ∈ P.erase p, xiUnitDoubleCompletedPhysicalPairResponse p q := by
    apply Finset.sum_congr rfl
    intro q hq
    have hqp : q ≠ p := (Finset.mem_erase.mp hq).1
    rw [xiUnitDoubleCompletedBalancedResponseCoupling,
      if_neg (fun h => hqp h.symm)]
  calc
    (∑ q ∈ P, xiUnitDoubleCompletedBalancedResponseCoupling P p q) =
        (∑ q ∈ P.erase p,
          xiUnitDoubleCompletedBalancedResponseCoupling P p q) +
          xiUnitDoubleCompletedBalancedResponseCoupling P p p :=
      (Finset.sum_erase_add P
        (fun q => xiUnitDoubleCompletedBalancedResponseCoupling P p q) hp).symm
    _ = (∑ q ∈ P.erase p, xiUnitDoubleCompletedPhysicalPairResponse p q) +
        (xiUnitDoubleFusedPrimeResponseCurrent p -
          ∑ q ∈ P.erase p, xiUnitDoubleCompletedPhysicalPairResponse p q) := by
      rw [hoff, xiUnitDoubleCompletedBalancedResponseCoupling, if_pos rfl]
    _ = xiUnitDoubleFusedPrimeResponseCurrent p := by ring

/-- **Finite uniqueness.**  Off-diagonal completed seam values together with the fused-current
marginals force the balanced response coupling entrywise; its diagonal is not an extra choice. -/
theorem xiUnitDoubleCompletedBalancedResponseCoupling_unique
    (P : Finset Nat.Primes) (C : Nat.Primes → Nat.Primes → ℝ)
    (hoff : ∀ p ∈ P, ∀ q ∈ P, p ≠ q →
      C p q = xiUnitDoubleCompletedPhysicalPairResponse p q)
    (hrow : ∀ p ∈ P, ∑ q ∈ P, C p q =
      xiUnitDoubleFusedPrimeResponseCurrent p) :
    ∀ p ∈ P, ∀ q ∈ P,
      C p q = xiUnitDoubleCompletedBalancedResponseCoupling P p q := by
  intro p hp q hq
  by_cases hpq : p = q
  · subst q
    have hsplit := Finset.sum_erase_add P (fun r => C p r) hp
    have hoffsum :
        (∑ r ∈ P.erase p, C p r) =
          ∑ r ∈ P.erase p, xiUnitDoubleCompletedPhysicalPairResponse p r := by
      apply Finset.sum_congr rfl
      intro r hr
      have hrp : r ≠ p := (Finset.mem_erase.mp hr).1
      exact hoff p hp r (Finset.mem_of_mem_erase hr) (fun h => hrp h.symm)
    rw [xiUnitDoubleCompletedBalancedResponseCoupling, if_pos rfl]
    have hrowp := hrow p hp
    rw [← hsplit, hoffsum] at hrowp
    linarith
  · rw [xiUnitDoubleCompletedBalancedResponseCoupling, if_neg hpq]
    exact hoff p hp q hq hpq

end

end RHTower
