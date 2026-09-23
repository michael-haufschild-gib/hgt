import GaloisForLFunctions.RHTower.Sieve.JointLadderProduct
import GaloisForLFunctions.RHTower.Sieve.HarmonicCauchySchwarz

/-!
# Splitting the joint ladder of products with harmonic weights

The harmonic split of `Sieve/LadderHarmonicSplit`, carried over to the ladder whose cofactor retains
the long designated weight.  Choosing `v_j` to be the reciprocal of the harmonic mass of the `j`-th
short prime range makes `∑_j 1/v_j` exactly the harmonic mass of the whole short range, for every
subdivision.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- **The harmonic split of the joint ladder, pointwise.** -/
theorem normSq_jointLadderProductPoly_le {P Q : Finset ℕ} (A₀ B₀ : ℕ) (R η : ℝ) {L : ℕ}
    (v : ℕ → ℝ) (hv : ∀ j ∈ Finset.range L, 0 < v j) (w : ℝ) :
    ‖jointLadderProductPoly P Q A₀ B₀ R η L w‖ ^ (2 : ℕ)
      ≤ (∑ j ∈ Finset.range L, 1 / v j)
        * ∑ j ∈ Finset.range L, v j
            * (‖primeBlockPoly (geomBlock P R (1 + η) j) w‖ ^ (2 : ℕ)
              * ‖logPoly (omegaQCoeff Q) (geomCofactorBlockAt A₀ B₀ R η j) w‖ ^ (2 : ℕ)) := by
  rw [jointLadderProductPoly]
  exact normSq_sum_mul_le_weighted (Finset.range L) v hv
    (fun j => primeBlockPoly (geomBlock P R (1 + η) j) w)
    (fun j => logPoly (omegaQCoeff Q) (geomCofactorBlockAt A₀ B₀ R η j) w)

/-- **The harmonic split of the joint ladder, in mean square.** -/
theorem integral_normSq_jointLadderProductPoly_le {P Q : Finset ℕ} (A₀ B₀ : ℕ) (R η : ℝ) {L : ℕ}
    (v : ℕ → ℝ) (hv : ∀ j ∈ Finset.range L, 0 < v j) (W : ℝ) :
    (∫ w in Set.Icc (-W) W, ‖jointLadderProductPoly P Q A₀ B₀ R η L w‖ ^ (2 : ℕ))
      ≤ (∑ j ∈ Finset.range L, 1 / v j)
        * ∑ j ∈ Finset.range L, v j
            * ∫ w in Set.Icc (-W) W,
                ‖primeBlockPoly (geomBlock P R (1 + η) j) w‖ ^ (2 : ℕ)
                  * ‖logPoly (omegaQCoeff Q) (geomCofactorBlockAt A₀ B₀ R η j) w‖ ^ (2 : ℕ) := by
  classical
  set G : ℕ → ℝ → ℝ := fun j w =>
    ‖primeBlockPoly (geomBlock P R (1 + η) j) w‖ ^ (2 : ℕ)
      * ‖logPoly (omegaQCoeff Q) (geomCofactorBlockAt A₀ B₀ R η j) w‖ ^ (2 : ℕ) with hG
  have hcontG : ∀ j : ℕ, Continuous (G j) := by
    intro j
    exact (((continuous_primeBlockPoly _).norm).pow 2).mul
      (((continuous_logPoly _ _).norm).pow 2)
  have hcontZ : Continuous fun w : ℝ => ‖jointLadderProductPoly P Q A₀ B₀ R η L w‖ ^ (2 : ℕ) := by
    refine ((continuous_finsetSum _ fun j _ => ?_).norm).pow 2
    exact (continuous_primeBlockPoly _).mul (continuous_logPoly _ _)
  have hcontR : Continuous fun w : ℝ =>
      (∑ j ∈ Finset.range L, 1 / v j) * ∑ j ∈ Finset.range L, v j * G j w :=
    (continuous_finsetSum _ fun j _ => (hcontG j).const_mul _).const_mul _
  have hintZ : IntegrableOn (fun w : ℝ => ‖jointLadderProductPoly P Q A₀ B₀ R η L w‖ ^ (2 : ℕ))
      (Set.Icc (-W) W) volume := hcontZ.integrableOn_Icc
  have hintR : IntegrableOn (fun w : ℝ =>
      (∑ j ∈ Finset.range L, 1 / v j) * ∑ j ∈ Finset.range L, v j * G j w)
      (Set.Icc (-W) W) volume := hcontR.integrableOn_Icc
  have hmono := setIntegral_mono_on hintZ hintR measurableSet_Icc
    (fun w _ => normSq_jointLadderProductPoly_le A₀ B₀ R η v hv w)
  refine hmono.trans (le_of_eq ?_)
  rw [MeasureTheory.integral_const_mul]
  congr 1
  rw [integral_finsetSum _ fun j _ => ((hcontG j).const_mul (v j)).integrableOn_Icc]
  exact Finset.sum_congr rfl fun j _ => MeasureTheory.integral_const_mul _ _

end

end RHTower.Sieve
