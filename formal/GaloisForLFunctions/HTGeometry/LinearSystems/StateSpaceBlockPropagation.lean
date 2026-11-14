import GaloisForLFunctions.HTGeometry.FiniteFieldStateSpaceHankelRank

/-!
# Exact propagation and finite memory of state-space responses

The recursion `x(n+1) = A x(n) + u(n) b` admits an exact decomposition into a
causal Toeplitz sum and the free response of its initial state. Splitting a
time interval at any index changes neither the state nor its observed output.
Past inputs act on future outputs through a rectangular Hankel matrix, whose
rank is bounded by the state dimension independently of both window lengths.
-/

open scoped BigOperators Matrix

namespace HTGeometry

noncomputable section

variable {K : Type*} [Field K] {d : ℕ}

/-- Driven state with initial value `x`, input direction `b`, and scalar forcing `u`. -/
def drivenState (A : Matrix (Fin d) (Fin d) K) (b : Fin d → K)
    (u : ℕ → K) (x : Fin d → K) : ℕ → (Fin d → K)
  | 0 => x
  | n + 1 => A *ᵥ drivenState A b u x n + u n • b

/-- Cutting the forcing history at any index gives exactly the same state. -/
theorem drivenState_add (A : Matrix (Fin d) (Fin d) K) (b : Fin d → K)
    (u : ℕ → K) (x : Fin d → K) (m n : ℕ) :
    drivenState A b u x (m + n) =
      drivenState A b (fun j => u (m + j)) (drivenState A b u x m) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change A *ᵥ drivenState A b u x (m + n) + u (m + n) • b =
        A *ᵥ drivenState A b (fun j => u (m + j)) (drivenState A b u x m) n +
          u (m + n) • b
      rw [ih]

/-- The dependence on the initial state is precisely the homogeneous response. -/
theorem drivenState_eq_free_add_zero (A : Matrix (Fin d) (Fin d) K)
    (b : Fin d → K) (u : ℕ → K) (x : Fin d → K) (n : ℕ) :
    drivenState A b u x n = (A ^ n) *ᵥ x + drivenState A b u 0 n := by
  induction n with
  | zero => simp [drivenState]
  | succ n ih =>
      rw [drivenState, ih, Matrix.mulVec_add, drivenState, pow_succ',
        ← Matrix.mulVec_mulVec, add_assoc]

/-- Variation of constants as a finite causal convolution, valid for every matrix. -/
theorem drivenState_eq_sum (A : Matrix (Fin d) (Fin d) K) (b : Fin d → K)
    (u : ℕ → K) (x : Fin d → K) (n : ℕ) :
    drivenState A b u x n =
      (A ^ n) *ᵥ x + ∑ j ∈ Finset.range n, u j • ((A ^ (n - 1 - j)) *ᵥ b) := by
  induction n with
  | zero => simp [drivenState]
  | succ n ih =>
      rw [drivenState, ih, Matrix.mulVec_add, Matrix.mulVec_sum,
        Finset.sum_range_succ, pow_succ', ← Matrix.mulVec_mulVec]
      have hsum :
          (∑ j ∈ Finset.range n, A *ᵥ (u j • ((A ^ (n - 1 - j)) *ᵥ b))) =
            ∑ j ∈ Finset.range n, u j • ((A ^ (n + 1 - 1 - j)) *ᵥ b) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← pow_succ']
        congr 3
        have hjn := Finset.mem_range.mp hj
        omega
      rw [hsum]
      simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, Matrix.one_mulVec]
      exact add_assoc _ _ _

/-- The observed response is Toeplitz convolution plus an initial-state correction. -/
theorem drivenState_output (A : Matrix (Fin d) (Fin d) K) (b c : Fin d → K)
    (u : ℕ → K) (x : Fin d → K) (n : ℕ) :
    c ⬝ᵥ drivenState A b u x n =
      c ⬝ᵥ (A ^ n) *ᵥ x +
        ∑ j ∈ Finset.range n, u j * algebraicStateSpaceResponse A b c (n - 1 - j) := by
  rw [drivenState_eq_sum, dotProduct_add, dotProduct_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  simp only [algebraicStateSpaceResponse, dotProduct, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Past inputs indexed backwards and future observations indexed forwards. -/
def stateSpacePastFuture (A : Matrix (Fin d) (Fin d) K) (b c : Fin d → K)
    (p q : ℕ) : Matrix (Fin p) (Fin q) K :=
  fun i j => algebraicStateSpaceResponse A b c (i.val + j.val)

/-- Observation covectors on an arbitrary finite future window. -/
def stateSpaceObservation (A : Matrix (Fin d) (Fin d) K) (c : Fin d → K)
    (p : ℕ) : Matrix (Fin p) (Fin d) K :=
  fun i k => ∑ l, c l * (A ^ i.val) l k

/-- Reachable vectors on an arbitrary finite past window. -/
def stateSpaceReachability (A : Matrix (Fin d) (Fin d) K) (b : Fin d → K)
    (q : ℕ) : Matrix (Fin d) (Fin q) K :=
  fun k j => ((A ^ j.val) *ᵥ b) k

/-- Every rectangular past-to-future block factors through the same `d` states. -/
theorem stateSpacePastFuture_factorization (A : Matrix (Fin d) (Fin d) K)
    (b c : Fin d → K) (p q : ℕ) :
    stateSpacePastFuture A b c p q =
      stateSpaceObservation A c p * stateSpaceReachability A b q := by
  ext i j
  rw [stateSpacePastFuture, algebraicStateSpaceResponse_add]
  simp only [Matrix.mul_apply, stateSpaceObservation, stateSpaceReachability,
    Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- A longer observation window cannot increase the required state dimension. -/
theorem rank_stateSpacePastFuture_le (A : Matrix (Fin d) (Fin d) K)
    (b c : Fin d → K) (p q : ℕ) :
    (stateSpacePastFuture A b c p q).rank ≤ d := by
  rw [stateSpacePastFuture_factorization]
  exact (Matrix.rank_mul_le_left _ _).trans (by
    simpa using Matrix.rank_le_card_width (stateSpaceObservation A c p))

end

end HTGeometry
