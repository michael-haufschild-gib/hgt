import GaloisForLFunctions.AdelicKreinGeometry.Haar.CyclicGramLimit
import GaloisForLFunctions.AdelicKreinGeometry.Haar.PolynomialCorrection

/-!
# Continuous dilations force infinite index for Haar successors

The canonical polynomial correction preserves both axis readings while restoring
integer invariance. The cyclic Gram-limit obstruction therefore applies to every
Hermitian rational affine Haar kernel with continuous dilation reading.
-/

open Filter Topology Module
open GaloisForLFunctions.ArithmeticPositiveDuality
open GaloisForLFunctions.HeckeKreinToeplitz
noncomputable section
namespace GaloisForLFunctions.AdelicKreinGeometry

/-- Every Hermitian rational affine Haar kernel with continuous dilation reading has infinite index.
The canonical zero-axis correction removes its finite polynomial period defect; cyclic projection
Grams then produce arbitrarily many negative directions. -/
theorem negIndex_eq_top_of_haar_continuous_dilation {k : AffineGroupQ → ℂ}
    (hk : IsHermKernel k) (hs : HasIntegerSuccessor k) {f : ℝ → ℂ}
    (hf : ContinuousAt f 1)
    (hdil : ∀ u : ℚˣ, 0 < (u : ℚ) → k (dilation u) = f (u : ℚ)) :
    negIndex k = ⊤ := by
  have hno (r : ℕ) (hi : negIndex k ≤ r) : False := by
    obtain ⟨q, _, _, _, hqt, hqd, hrem, hindex, hperiod, _⟩ :=
      exists_zero_axis_polynomial_correction hk hi (hasIntegerSuccessor_translation_periodic hs)
    have hsrem : HasIntegerSuccessor (fun g => k g - q g) := by
      intro b
      change k (translation b) - q (translation b) = _
      rw [hqt, sub_zero]
      exact hs b
    have hdrem (u : ℚˣ) (hu : 0 < (u : ℚ)) :
        k (dilation u) - q (dilation u) = f (u : ℚ) := by
      rw [hqd, sub_zero, hdil u hu]
    have htop := negIndex_eq_top_of_integer_invariant_haar_continuous_dilation
      hrem hsrem hperiod hf hdrem
    rw [htop] at hindex
    simp at hindex
  refine ENat.eq_top_iff_forall_ge.mpr fun n => ?_
  by_contra hn
  exact hno n (le_of_lt (lt_of_not_ge hn))

#print axioms negIndex_eq_top_of_haar_continuous_dilation
end GaloisForLFunctions.AdelicKreinGeometry
