import GaloisForLFunctions.HTGeometry.TwoReplicaTensorHilbertSchmidt

/-!
# Fixed-orientation two-replica edge Hall expansion

A single Pauli orientation per graph edge already expands every subspace of the sitewise singlet
algebra modulo its global permutation line.  The mechanism is resolved edge incidence, not a
spectral gap:

* one fixed-orientation edge commutator sees only the endpoint mismatch coordinates,
* it is injective on the mismatch fibre of its own edge, and
* distinct edges produce Hilbert–Schmidt orthogonal defect sectors.

Stacking the mismatch projections is faithful exactly when the graph is connected, so the three
facts combine into `dim span_e A_e Ũ ≥ dim Ũ`.
-/

open Matrix Finset

open scoped Kronecker

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ### Positive definiteness of the Hilbert–Schmidt form -/

theorem eq_zero_of_trace_conjTranspose_mul_self {m : Type*} [Fintype m] {A : Matrix m m ℂ}
    (h : Matrix.trace (Aᴴ * A) = 0) : A = 0 := by
  have hsum : Matrix.trace (Aᴴ * A) = ((∑ i, ∑ j, Complex.normSq (A j i) : ℝ) : ℂ) := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
    push_cast
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      rw [Complex.normSq_eq_conj_mul_self]; rfl
  rw [hsum] at h
  have hreal : (∑ i, ∑ j, Complex.normSq (A j i) : ℝ) = 0 := by exact_mod_cast h
  ext j i
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg (A j i))).mp hreal i
    (Finset.mem_univ i)
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ => Complex.normSq_nonneg (A j i))).mp h1 j (Finset.mem_univ j)
  simpa using Complex.normSq_eq_zero.mp h2

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### The local output family of one fixed-orientation edge commutator -/

/-- The site-by-site output of the fixed-orientation edge commutator on a mismatched swap word:
a replica difference (possibly swap-translated) at each endpoint, and the original identity/swap
letter everywhere else. -/
def edgeOutputLocal (u v : V) (a b : Fin 3) (x : V → Bool) (w : V) :
    Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ :=
  if w = u then (if x u then twoReplicaSwap * twoReplicaLocalDiff a else twoReplicaLocalDiff a)
  else if w = v then
    (if x v then twoReplicaSwap * twoReplicaLocalDiff b else twoReplicaLocalDiff b)
  else twoReplicaLocalSwapRaw (x w)

omit [Fintype V] in
theorem edgeOutputLocal_self_left (u v : V) (a b : Fin 3) (x : V → Bool) :
    edgeOutputLocal u v a b x u =
      if x u then twoReplicaSwap * twoReplicaLocalDiff a else twoReplicaLocalDiff a := by
  simp [edgeOutputLocal]

omit [Fintype V] in
theorem edgeOutputLocal_self_right {u v : V} (huv : u ≠ v) (a b : Fin 3) (x : V → Bool) :
    edgeOutputLocal u v a b x v =
      if x v then twoReplicaSwap * twoReplicaLocalDiff b else twoReplicaLocalDiff b := by
  simp [edgeOutputLocal, huv.symm]

omit [Fintype V] in
theorem edgeOutputLocal_outside {u v : V} (a b : Fin 3) (x : V → Bool) {w : V}
    (hwu : w ≠ u) (hwv : w ≠ v) :
    edgeOutputLocal u v a b x w = twoReplicaLocalSwapRaw (x w) := by
  simp [edgeOutputLocal, hwu, hwv]

/-- The value of the fixed-orientation edge commutator on one identity/swap word. -/
def edgeOutput (u v : V) (a b : Fin 3) (x : V → Bool) : FiniteTwoReplicaMatrix V :=
  if x u = x v then 0 else -finiteTwoReplicaLocalMatrix (edgeOutputLocal u v a b x)

/-- The edge extension is odd in its edge block. -/
theorem finiteTwoReplicaEdgeExtension_neg (u v : V)
    (S : FiniteTwoReplicaEdgeOutside u v →
      Matrix TwoReplicaLocalIndex TwoReplicaLocalIndex ℂ)
    (A : Matrix TwoReplicaEdgeIndex TwoReplicaEdgeIndex ℂ) :
    finiteTwoReplicaEdgeExtension u v S (-A) =
      -finiteTwoReplicaEdgeExtension u v S A := by
  simpa using finiteTwoReplicaEdgeExtension_smul u v S (-1 : ℂ) A

/-- **Equation (7) on any register.**  The fixed-orientation edge commutator annihilates
endpoint-matched swap words and sends a mismatched word to the negated sitewise tensor product of
its local outputs. -/
theorem finiteTwoReplicaCollectiveCommutator_swapRaw_eq_edgeOutput
    {u v : V} (huv : u ≠ v) (a b : Fin 3) (x : V → Bool) :
    finiteTwoReplicaCollectiveCommutatorLinear (finiteEdgePauliLabel u v a b)
        (finiteTwoReplicaSwapRaw x) = edgeOutput u v a b x := by
  unfold edgeOutput
  by_cases hx : x u = x v
  · rw [if_pos hx]
    exact finiteTwoReplicaCollectiveCommutator_swapRaw_eq_zero_of_matched huv a b x hx
  · rw [if_neg hx]
    have hconv : finiteTwoReplicaLocalMatrix (edgeOutputLocal u v a b x)
        = finiteTwoReplicaEdgeExtension u v (fun w => twoReplicaLocalSwapRaw (x w.1))
            (edgeOutputLocal u v a b x u ⊗ₖ edgeOutputLocal u v a b x v) := by
      rw [finiteTwoReplicaLocalMatrix_eq_edgeExtension huv]
      congr 1
      funext w
      exact edgeOutputLocal_outside a b x w.2.1 w.2.2
    rcases hxu : x u with _ | _
    · have hxv : x v = true := by
        rcases hb : x v with _ | _
        · exact absurd (hxu.trans hb.symm) hx
        · rfl
      rw [finiteTwoReplicaCollectiveCommutator_swapRaw_of_mismatch_left huv a b x hxu hxv,
        hconv, edgeOutputLocal_self_left, edgeOutputLocal_self_right huv, hxu, hxv]
      simp [finiteTwoReplicaEdgeExtension_neg]
    · have hxv : x v = false := by
        rcases hb : x v with _ | _
        · rfl
        · exact absurd (hxu.trans hb.symm) hx
      rw [finiteTwoReplicaCollectiveCommutator_swapRaw_of_mismatch_right huv a b x hxu hxv,
        hconv, edgeOutputLocal_self_left, edgeOutputLocal_self_right huv, hxu, hxv]
      simp [finiteTwoReplicaEdgeExtension_neg]

end

end GaloisForLFunctions.HTGeometry
