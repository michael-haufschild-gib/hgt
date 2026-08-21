import GaloisForLFunctions.HTGeometry.ChainRankStabilization
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# The stable image of a twisted chain

The images of an ordered product decrease, because each further factor is applied first.  In a
finite-dimensional space a decreasing chain of subspaces stabilises, so a twisted chain has a
**stable image**: a subspace reached from some index on and never left again.

That subspace is the object the slope filtration is built from — the part of the space on which the
accumulated leading matrices do not lose information — and it is nonzero exactly in the regime where
the chain never vanishes, which is the regime `matDeg_chainProd_eq` already settles.

* `range_chainProdK_antitone`, `range_chainProdK_antitone_le`;
* `exists_range_chainProdK_stabilize`.
-/

namespace GaloisForLFunctions.HTGeometry

namespace DiffOp

noncomputable section

variable {K : Type*} [Field K] [Differential K] {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Differential K] in
/-- **The images of an ordered product decrease.** -/
theorem range_chainProdK_antitone (C : ℕ → Matrix ι ι K) (n : ℕ) :
    LinearMap.range (Matrix.mulVecLin (chainProdK C (n + 1)))
      ≤ LinearMap.range (Matrix.mulVecLin (chainProdK C n)) := by
  rw [chainProdK_succ, Matrix.mulVecLin_mul]
  exact LinearMap.range_comp_le_range _ _

omit [Differential K] in
theorem range_chainProdK_antitone_le (C : ℕ → Matrix ι ι K) {m n : ℕ} (h : m ≤ n) :
    LinearMap.range (Matrix.mulVecLin (chainProdK C n))
      ≤ LinearMap.range (Matrix.mulVecLin (chainProdK C m)) := by
  induction n with
  | zero =>
      have hm : m = 0 := Nat.le_zero.mp h
      rw [hm]
  | succ n ih =>
      rcases Nat.lt_or_ge m (n + 1) with hlt | hge
      · exact le_trans (range_chainProdK_antitone C n) (ih (by omega))
      · have hm : m = n + 1 := by omega
        rw [hm]

omit [Differential K] in
/-- **The image stabilises.**  Beyond the index where the rank is minimal the image no longer
changes. -/
theorem exists_range_chainProdK_stabilize (C : ℕ → Matrix ι ι K) :
    ∃ N, ∀ n, N ≤ n →
      LinearMap.range (Matrix.mulVecLin (chainProdK C n))
        = LinearMap.range (Matrix.mulVecLin (chainProdK C N)) := by
  obtain ⟨N, hN⟩ := exists_rank_chainProdK_stabilize C
  refine ⟨N, fun n hn => ?_⟩
  refine (Submodule.eq_of_le_of_finrank_le (range_chainProdK_antitone_le C hn) ?_).symm ▸ rfl
  have h := hN n hn
  rw [Matrix.rank, Matrix.rank] at h
  omega

end

end DiffOp

end GaloisForLFunctions.HTGeometry
