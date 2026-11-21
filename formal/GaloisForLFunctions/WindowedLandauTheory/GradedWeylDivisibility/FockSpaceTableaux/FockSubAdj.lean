import GaloisForLFunctions.WindowedLandauTheory.GradedWeylDivisibility.StatementA
import GaloisForLFunctions.WindowedLandauTheory.GradedWeylDivisibility.FockSpaceTableaux.LFocksLemmas



open MvPolynomial WindowedLandauTheory.REAL

noncomputable section

namespace WindowedLandauTheory.GradedWeylDivisibility

lemma LFocks_subAdj {σ : Type*} [Fintype σ] [DecidableEq σ] (U : Matrix σ σ ℂ)
    (f g : MvPolynomial σ ℂ) :
    fockF (sub U f) g = fockF f (sub U.conjTranspose g) := by
  induction f using MvPolynomial.induction_on generalizing g
  · rename_i a
    rw [LFocks_sub_C, LFocks_C_left, LFocks_C_left,
      LFocks_constantCoeff_sub]
  · rename_i p q hp hq
    rw [map_add, WindowedLandauTheory.REAL.fischerInner_add_left, WindowedLandauTheory.REAL.fischerInner_add_left, hp, hq]
  · rename_i p i hp
    rw [map_mul, LFocks_sub_X, mul_comm p (X i), WindowedLandauTheory.REAL.fischerInner_X_mul_left i p,
      LFocks_pderiv_sub, WindowedLandauTheory.REAL.fischerInner_sum_right, Finset.mul_sum, WindowedLandauTheory.REAL.fischerInner_sum_left]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [LFocks_C_mul_right, ← hp, Matrix.conjTranspose_apply, star_star,
      mul_comm (sub U p), mul_assoc, LFocks_C_mul_left,
      WindowedLandauTheory.REAL.fischerInner_X_mul_left]

theorem fischerInnerSubstitutionAdjoint : FockSubAdj :=
  fun _ _ _ U f g => LFocks_subAdj U f g

end WindowedLandauTheory.GradedWeylDivisibility

