import GaloisForLFunctions.HTGeometry.TwistedMatrixChain

/-!
# The accumulated leading matrices have a stable rank

The ranks of an ordered product of matrices are non-increasing, so they stabilise: the rank attains
its minimum at some index and stays there.  That index is where the accumulated leading matrix of a
twisted product stops losing information, and it is the entry point of the slope filtration — the
regime the degree dichotomy of `chainProdK_dichotomy` separates.

* `rank_chainProdK_antitone_le` — the antitonicity, iterated;
* `exists_rank_chainProdK_stabilize`;
* `rank_eq_zero_iff`, `chainProdK_ne_zero_iff_rank_pos`.
-/

namespace GaloisForLFunctions.HTGeometry

namespace DiffOp

noncomputable section

variable {K : Type*} [Field K] [Differential K] {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Differential K] in
/-- **The ranks of an ordered product are non-increasing.** -/
theorem rank_chainProdK_antitone_le (C : ℕ → Matrix ι ι K) {m n : ℕ} (h : m ≤ n) :
    Matrix.rank (chainProdK C n) ≤ Matrix.rank (chainProdK C m) := by
  induction n with
  | zero =>
      have : m = 0 := Nat.le_zero.mp h
      rw [this]
  | succ n ih =>
      rcases Nat.lt_or_ge m (n + 1) with hlt | hge
      · exact le_trans (rank_chainProdK_antitone C n) (ih (by omega))
      · have : m = n + 1 := by omega
        rw [this]

omit [Differential K] in
/-- **The rank stabilises.**  It attains its minimum at some index and stays there. -/
theorem exists_rank_chainProdK_stabilize (C : ℕ → Matrix ι ι K) :
    ∃ N, ∀ n, N ≤ n → Matrix.rank (chainProdK C n) = Matrix.rank (chainProdK C N) := by
  classical
  obtain ⟨N, hN⟩ := Nat.lt_wfRel.wf.has_min
    (Set.range fun n => Matrix.rank (chainProdK C n)) ⟨_, ⟨0, rfl⟩⟩
  obtain ⟨N₀, rfl⟩ := hN.1
  refine ⟨N₀, fun n hn => le_antisymm (rank_chainProdK_antitone_le C hn) ?_⟩
  by_contra hlt
  push Not at hlt
  exact hN.2 _ ⟨n, rfl⟩ hlt

omit [Differential K] in
/-- **A matrix has rank zero exactly when it vanishes.** -/
theorem rank_eq_zero_iff (M : Matrix ι ι K) : M.rank = 0 ↔ M = 0 := by
  rw [Matrix.rank, Submodule.finrank_eq_zero, LinearMap.range_eq_bot]
  constructor
  · intro h
    ext i j
    have hj := congrFun (congrFun (congrArg DFunLike.coe h) (Pi.single j 1)) i
    simpa [Matrix.mulVecLin, Matrix.mulVec, dotProduct, Pi.single_apply] using hj
  · intro h
    subst h
    ext v
    simp

omit [Differential K] in
/-- **The chain never vanishes exactly when its stable rank is positive.** -/
theorem chainProdK_ne_zero_iff_rank_pos (C : ℕ → Matrix ι ι K) {N : ℕ}
    (hN : ∀ n, N ≤ n → Matrix.rank (chainProdK C n) = Matrix.rank (chainProdK C N)) :
    (∀ n, chainProdK C n ≠ 0) ↔ 0 < Matrix.rank (chainProdK C N) := by
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos (Matrix.rank (chainProdK C N)) with hz | hp
    · exact absurd ((rank_eq_zero_iff _).mp hz) (h N)
    · exact hp
  · intro hp n h0
    have hzero : chainProdK C (max n N) = 0 :=
      chainProdK_eq_zero_of_le C h0 (le_max_left n N)
    have hrank := hN (max n N) (le_max_right n N)
    rw [hzero] at hrank
    rw [(rank_eq_zero_iff (0 : Matrix ι ι K)).mpr rfl] at hrank
    omega

end

end DiffOp

end GaloisForLFunctions.HTGeometry
