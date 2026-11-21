import GaloisForLFunctions.HilbertMetric.QuantumInformation.Recovery.ReadyBranch

/-!
# Recovery from a prefix of the sequential qubit chain

A branch-one configuration is a string of ones followed by zeros. The
configurations whose run of ones ends within the accessible prefix share
the zero branch's lost label. Equation (7.26) of Kanno and Soda
(arXiv:2611.26368) follows by applying the ready-branch recovery theorem.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HilbertMetric.QuantumInformation.ReadyBranch

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- The amplitudes of the prefix and tail configurations, with split
indices for runs of ones of length at most k and strictly greater than k. -/
abbrev ChainAmplitudes (k r : ℕ) := {A : (Fin (k + 1) ⊕ Fin r) → ℂ // cnormSq A = 1}

private theorem cnormSq_basis {ι : Type*} [Fintype ι] [DecidableEq ι] (j : ι) (z : ℂ) :
    cnormSq (fun i : ι => if i = j then z else 0) = ‖z‖ ^ 2 := by
  unfold cnormSq
  rw [Finset.sum_eq_single j]
  · simp only [if_true]
  · intro i _ hij
    simp only [if_neg hij, norm_zero, zero_pow (Nat.succ_ne_zero 1)]
  · exact fun hj => (hj (Finset.mem_univ j)).elim

/-- The accessible register retains the prefix length. A run extending
into the tail leaves the accessible prefix all ones and has its own lost label. -/
def prefixEncoding {k r : ℕ} (A : ChainAmplitudes k r) :
    Encoding (Fin (k + 1)) (Option (Fin r)) where
  ready := none
  reference := fun i => if i = 0 then 1 else 0
  signal
    | none => fun j => A.1 (.inl j)
    | some l => fun j => if j = Fin.last k then A.1 (.inr l) else 0
  reference_norm := by
    rw [cnormSq_basis, norm_one, one_pow]
  signal_norm := by
    have h := A.2
    rw [cnormSq, Fintype.sum_sum_type] at h
    rw [Fintype.sum_option]
    change cnormSq (fun j => A.1 (.inl j)) +
      (∑ l, cnormSq (fun j => if j = Fin.last k then A.1 (.inr l) else 0)) = 1
    simpa only [cnormSq_basis, cnormSq] using h

/-- The squared mass of configurations whose ones all fit in the prefix. -/
def prefixMass {k r : ℕ} (A : ChainAmplitudes k r) : ℝ :=
  ∑ j, ‖A.1 (.inl j)‖ ^ 2

/-- Every deterministic finite recovery from the prefix satisfies the
closed fidelity bound, including empty prefixes and empty tails. -/
theorem prefix_fidelity_le {k r : ℕ} (A : ChainAmplitudes k r)
    {K : Type*} [Fintype K] (R : Recovery (Fin (k + 1)) K) :
    fidelity (prefixEncoding A) R ≤ (1 + Real.sqrt (prefixMass A)) / 2 :=
  fidelity_le (prefixEncoding A) R

/-- The prefix bound is attained. Each additional accessible configuration
contributes its squared amplitude to the mass under the square root. -/
theorem exists_optimal_prefix_recovery {k r : ℕ} (A : ChainAmplitudes k r) :
    ∃ R : Recovery (Fin (k + 1)) (Option (Fin (k + 1))),
      fidelity (prefixEncoding A) R = (1 + Real.sqrt (prefixMass A)) / 2 :=
  exists_optimal_recovery (prefixEncoding A)

#print axioms prefix_fidelity_le
#print axioms exists_optimal_prefix_recovery

end

end GaloisForLFunctions.HilbertMetric.QuantumInformation.ReadyBranch
