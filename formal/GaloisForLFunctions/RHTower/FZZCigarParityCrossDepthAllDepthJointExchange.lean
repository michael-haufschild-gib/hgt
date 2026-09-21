import GaloisForLFunctions.RHTower.FZZCigarParityCrossDepthSymmetricKernelNoGo

/-!
# FZZ-P all-depth joint source exchange

The all-depth FZZ source has a distinguished exchange of its two screening
depth indices. This leaf packages that exact reindexing as an equivalence of
the joint `tsum` index. It is deliberately independent of a source kernel:
later source laws must prove whether their physical domain is this exchange-
stable joint sum or an ordered prescription.
-/

open scoped BigOperators

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Exchange of two natural-number screening depths. -/
def fzzRadialCouplingNatDepthExchange : ℕ × ℕ ≃ ℕ × ℕ where
  toFun ij := (ij.2, ij.1)
  invFun ij := (ij.2, ij.1)
  left_inv := by rintro ⟨i, j⟩; rfl
  right_inv := by rintro ⟨i, j⟩; rfl

/-- A joint all-depth sum is exactly invariant under exchange of screening
depth indices. This is an index law, not an assumption about convergence or
an ordering convention. -/
theorem tsum_fzzRadialCouplingNatDepthExchange
    (f : ℕ × ℕ → ℂ) :
    (∑' ij : ℕ × ℕ, f (ij.2, ij.1)) = ∑' ij : ℕ × ℕ, f ij := by
  change (∑' ij : ℕ × ℕ, f (fzzRadialCouplingNatDepthExchange ij)) =
    ∑' ij : ℕ × ℕ, f ij
  exact Equiv.tsum_eq fzzRadialCouplingNatDepthExchange f

end

end GaloisForLFunctions.RHTower
