import GaloisForLFunctions.RHTower.VonMangoldtAdditiveLogJetDirichlet
import GaloisForLFunctions.RHTower.PrimeArchHankelDeterminantCriterion

/-!
# The pointed-boundary obstruction for successor Dirichlet completion

The integral successor derivative annihilates the constant logarithmic jet.  Consequently the
uncompleted successor Gram has a zero zeroth row, while the normalized prime--archimedean Hankel
matrix has a strictly positive zeroth entry.  Thus the positive successor Gram cannot itself be
the RH moment matrix: a nontrivial pointed Gamma/polar boundary jet is logically necessary.
-/

namespace RHTower

noncomputable section

/-- The successor derivative kills the constant logarithmic jet. -/
theorem vonMangoldtAdditiveLogJetDifference_zero (n : ℕ) :
    vonMangoldtAdditiveLogJetDifference 0 n = 0 := by
  simp [vonMangoldtAdditiveLogJetDifference, vonMangoldtAdditiveLogJet]

/-- The order-zero edge feature consequently vanishes identically. -/
theorem vonMangoldtAdditiveLogJetFeature_zero (n : ℕ) :
    vonMangoldtAdditiveLogJetFeature 0 n = 0 := by
  simp [vonMangoldtAdditiveLogJetFeature,
    vonMangoldtAdditiveLogJetDifference_zero]

/-- Every nonempty successor Dirichlet Gram has a zero zeroth row. -/
theorem vonMangoldtAdditiveLogJetGram_zero_row
    (N : ℕ) (s : Fin (N + 1)) :
    vonMangoldtAdditiveLogJetGram (N + 1) 0 s = 0 := by
  rw [vonMangoldtAdditiveLogJetGram_apply]
  simp [vonMangoldtAdditiveLogJetFeature_zero]

/-- The unpointed successor Gram is never the normalized prime--archimedean Hankel section:
their zeroth entries are respectively zero and strictly positive. -/
theorem vonMangoldtAdditiveLogJetGram_ne_primeArchSourceMomentHankelMatrix
    (N : ℕ) :
    vonMangoldtAdditiveLogJetGram (N + 1) ≠
      primeArchSourceMomentHankelMatrix (N + 1) := by
  intro h
  have h00 := congrFun (congrFun h (0 : Fin (N + 1))) (0 : Fin (N + 1))
  rw [vonMangoldtAdditiveLogJetGram_zero_row,
    primeArchSourceMomentHankelMatrix_apply] at h00
  norm_num at h00
  exact normalizedPrimeArchMoment_zero_pos.ne' h00.symm

end

end RHTower
