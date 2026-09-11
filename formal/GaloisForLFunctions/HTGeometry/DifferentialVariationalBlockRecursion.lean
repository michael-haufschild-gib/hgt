import GaloisForLFunctions.HTGeometry.DifferentialVariationalBlockSum

/-!
# The block sum satisfies the component recursion

The off-diagonal component of the orbit obeys `w_{n+1} = σ(wₙ) + aₙ`, while the closed form that the
rate estimate needs is the unrolled sum `Σ_{j<n} σ^{n-1-j}(a_j)`.  This leaf proves the two agree, so
the estimate of the previous leaf can be fed by the recursion.

Along the way it records two basic facts about the vector action that were not previously available:

* `DifferentialFieldAut.vecBuildingAction_injective` — the action is injective, because it is an
  invertible matrix action composed with a coordinatewise ring equivalence;
* `DifferentialFieldAut.vecBuildingAction_one` — hence the identity automorphism acts trivially,
  obtained from the cocycle law `(1·1)·v = 1·(1·v)` and injectivity rather than by unfolding the
  canonical matrix unit.

`variationalBlockSum_succ` is then a reindexing: pushing `σ` inside the sum raises every exponent
by one, `n-1-j` to `n-j`, and the new top summand is `σ⁰(aₙ) = aₙ`.
-/

open scoped Differential BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
  [IsConstantBase C K]

set_option maxHeartbeats 1000000 in
/-- The vector action is injective. -/
theorem DifferentialFieldAut.vecBuildingAction_injective (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K)) :
    Function.Injective (σ.vecBuildingAction b) := by
  intro v w hvw
  have he : (DiffOp.completedPseudoDiffOpMatrixLinearEquiv
        (variationalOreCompletedMatrixUnit σ.fixes σ.deriv_comm b))
        (DiffOp.mapCompletedPseudoVecLinearMap σ.toRingEquiv σ.deriv_comm v) =
      (DiffOp.completedPseudoDiffOpMatrixLinearEquiv
        (variationalOreCompletedMatrixUnit σ.fixes σ.deriv_comm b))
        (DiffOp.mapCompletedPseudoVecLinearMap σ.toRingEquiv σ.deriv_comm w) := hvw
  have hinj := (DiffOp.completedPseudoDiffOpMatrixLinearEquiv
    (variationalOreCompletedMatrixUnit σ.fixes σ.deriv_comm b)).injective he
  funext i
  exact (DiffOp.mapCompletedPseudoRingEquiv σ.toRingEquiv σ.deriv_comm).injective
    (congrFun hinj i)

/-- The identity automorphism acts trivially on vectors. -/
theorem DifferentialFieldAut.vecBuildingAction_one {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (v : Fin r → DiffOp.CompletedPseudoDiffOp K) :
    (1 : DifferentialFieldAut C K).vecBuildingAction b v = v := by
  have hmul := DifferentialFieldAut.vecBuildingAction_mul
    (1 : DifferentialFieldAut C K) (1 : DifferentialFieldAut C K) b v
  rw [one_mul] at hmul
  exact ((1 : DifferentialFieldAut C K).vecBuildingAction_injective b) hmul.symm

/-- Powers compose with the action in the forward direction. -/
theorem DifferentialFieldAut.vecBuildingAction_succ_left (σ : DifferentialFieldAut C K) (m : ℕ)
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (v : Fin r → DiffOp.CompletedPseudoDiffOp K) :
    σ.vecBuildingAction b ((σ ^ m).vecBuildingAction b v) =
      (σ ^ (m + 1)).vecBuildingAction b v := by
  rw [← DifferentialFieldAut.vecBuildingAction_mul, pow_succ]

/-- **Recursion for the unrolled block sum.** -/
theorem variationalBlockSum_succ (σ : DifferentialFieldAut C K) {r : ℕ}
    (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (a : ℕ → Fin r → DiffOp.CompletedPseudoDiffOp K) (n : ℕ) :
    variationalBlockSum σ b a (n + 1) =
      σ.vecBuildingAction b (variationalBlockSum σ b a n) + a n := by
  classical
  have hsum : σ.vecBuildingAction b (variationalBlockSum σ b a n) =
      ∑ j ∈ Finset.range n, (σ ^ (n - j)).vecBuildingAction b (a j) := by
    rw [variationalBlockSum]
    rw [show σ.vecBuildingAction b (∑ j ∈ Finset.range n,
        (σ ^ (n - 1 - j)).vecBuildingAction b (a j)) =
        ∑ j ∈ Finset.range n, σ.vecBuildingAction b
          ((σ ^ (n - 1 - j)).vecBuildingAction b (a j)) from
      map_sum (σ.vecBuildingActionMap b) _ _]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjn : j < n := Finset.mem_range.1 hj
    rw [DifferentialFieldAut.vecBuildingAction_succ_left]
    congr 2
    omega
  rw [variationalBlockSum, Finset.sum_range_succ, hsum]
  congr 1
  have hzero : n + 1 - 1 - n = 0 := by omega
  rw [hzero, pow_zero, DifferentialFieldAut.vecBuildingAction_one]

end

end GaloisForLFunctions.HTGeometry
