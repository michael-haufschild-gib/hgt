import GaloisForLFunctions.HTGeometry.SelectionSynthesisDivergence

/-!
# The chain rule for a discrete joint law

For a joint law of a finite request variable and a discrete word variable, conditional entropy and
mutual information are the two halves of the word entropy:

`H(W) = H(W | X) + I(X ; W)`.

Both halves are sums of the same summand `p log p - p log p_X` and `p log p - p log p_X -
p log p_W`, so adding them cancels everything except `-p log p_W`, and summing that over the
requests replaces the joint law by its word marginal.

The identity is exact -- no positivity or normalization is used, only summability of the two series
being combined.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

section JointLaw

variable {X W : Type*} [Fintype X]

/-- The request marginal of a joint law. -/
def marginalFst (p : X → W → ℝ) (x : X) : ℝ := ∑' w, p x w

/-- The word marginal of a joint law. -/
def marginalSnd (p : X → W → ℝ) (w : W) : ℝ := ∑ x, p x w

/-- Shannon entropy of the word marginal. -/
def entropySnd (p : X → W → ℝ) : ℝ :=
  ∑' w, -(marginalSnd p w * Real.log (marginalSnd p w))

/-- Conditional entropy of the word given the request. -/
def condEntropySnd (p : X → W → ℝ) : ℝ :=
  ∑ x, ∑' w, -(p x w * (Real.log (p x w) - Real.log (marginalFst p x)))

/-- Selection information: the mutual information of request and word. -/
def mutualInfo (p : X → W → ℝ) : ℝ :=
  ∑ x, ∑' w, p x w *
    (Real.log (p x w) - Real.log (marginalFst p x) - Real.log (marginalSnd p w))

/-- **The chain rule.**  The word entropy is the conditional entropy plus the selection
information. -/
theorem entropySnd_eq_condEntropySnd_add_mutualInfo (p : X → W → ℝ)
    (hcond : ∀ x, Summable fun w => -(p x w * (Real.log (p x w) - Real.log (marginalFst p x))))
    (hinfo : ∀ x, Summable fun w => p x w *
      (Real.log (p x w) - Real.log (marginalFst p x) - Real.log (marginalSnd p w)))
    (hmix : ∀ x, Summable fun w => -(p x w * Real.log (marginalSnd p w))) :
    entropySnd p = condEntropySnd p + mutualInfo p := by
  classical
  have hsum : condEntropySnd p + mutualInfo p
      = ∑ x, ∑' w, -(p x w * Real.log (marginalSnd p w)) := by
    rw [condEntropySnd, mutualInfo, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← (hcond x).tsum_add (hinfo x)]
    refine tsum_congr fun w => ?_
    ring
  rw [hsum]
  have hswap : (∑ x, ∑' w, -(p x w * Real.log (marginalSnd p w)))
      = ∑' w, ∑ x, -(p x w * Real.log (marginalSnd p w)) :=
    (Summable.tsum_finsetSum fun x _ => hmix x).symm
  rw [hswap, entropySnd]
  refine tsum_congr fun w => ?_
  rw [marginalSnd, Finset.sum_neg_distrib, ← Finset.sum_mul]

/-- **`(4)`.**  The gate cost is conditional entropy plus selection information plus synthesis
divergence, up to the killing constant. -/
theorem gateCost_eq_condEntropy_add_mutualInfo_add_relEntropy {Γ : Type*} [Fintype Γ]
    (p : X → List Γ → ℝ) (a : ℝ) (M : ℕ)
    (hcond : ∀ x, Summable fun w => -(p x w * (Real.log (p x w) - Real.log (marginalFst p x))))
    (hinfo : ∀ x, Summable fun w => p x w *
      (Real.log (p x w) - Real.log (marginalFst p x) - Real.log (marginalSnd p w)))
    (hmix : ∀ x, Summable fun w => -(p x w * Real.log (marginalSnd p w)))
    (hgate : Real.log ((M : ℝ) / a) * (∑' w : List Γ, marginalSnd p w * (w.length : ℝ))
      = entropySnd p + relEntropy (marginalSnd p) (wordPrior a) - Real.log (1 - a)) :
    Real.log ((M : ℝ) / a) * (∑' w : List Γ, marginalSnd p w * (w.length : ℝ))
      = condEntropySnd p + mutualInfo p
        + relEntropy (marginalSnd p) (wordPrior a) - Real.log (1 - a) := by
  rw [hgate, entropySnd_eq_condEntropySnd_add_mutualInfo p hcond hinfo hmix]

end JointLaw

end

end GaloisForLFunctions.HTGeometry
