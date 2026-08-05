import GaloisForLFunctions.HTGeometry.GammaIterationFirstJetAlgebraicIndependence

/-!
# Depth bounds on the infinite first-jet index

The first-jet independence layer is conditioned on an index whose depth is within a budget.  The
depth is zero on the base block and one more than the iteration order on the jet block, so the
bound is decidable on the spot: the base block always fits, and a jet block fits exactly when its
order is below the budget.
-/

namespace GaloisForLFunctions

/-- The base block has depth zero, so it fits under every budget. -/
@[simp] theorem gammaIterateInfiniteFirstJetDepth_inl (a : Unit) :
    gammaIterateInfiniteFirstJetDepth (Sum.inl a) = 0 := rfl

/-- The jet block at order `j` has depth `j + 1`. -/
@[simp] theorem gammaIterateInfiniteFirstJetDepth_inr (p : ℕ × Fin 2) :
    gammaIterateInfiniteFirstJetDepth (Sum.inr p) = p.1 + 1 := rfl

/-- **The base block fits under every depth budget.** -/
theorem gammaIterateInfiniteFirstJetDepth_inl_le (a : Unit) (k : ℕ) :
    gammaIterateInfiniteFirstJetDepth (Sum.inl a) ≤ k := by
  rw [gammaIterateInfiniteFirstJetDepth_inl]
  exact Nat.zero_le k

/-- **A jet block fits exactly when its order is below the budget.** -/
theorem gammaIterateInfiniteFirstJetDepth_inr_le_iff (p : ℕ × Fin 2) (k : ℕ) :
    gammaIterateInfiniteFirstJetDepth (Sum.inr p) ≤ k ↔ p.1 < k := by
  rw [gammaIterateInfiniteFirstJetDepth_inr]
  omega

/-- Every budget admits an index, so the depth hypothesis is never vacuous. -/
theorem exists_gammaIterateInfiniteFirstJetDepth_le (k : ℕ) :
    ∃ i : GammaIterateInfiniteFirstJetIndex, gammaIterateInfiniteFirstJetDepth i ≤ k :=
  ⟨Sum.inl (), gammaIterateInfiniteFirstJetDepth_inl_le () k⟩

end GaloisForLFunctions
