import GaloisForLFunctions.RHTower.Sieve.LadderProductDefect
import GaloisForLFunctions.RHTower.Sieve.HarmonicCauchySchwarz

/-!
# Splitting the ladder of products with harmonic weights

Cauchy--Schwarz over the steps of the ladder costs `∑_j 1/v_j` for whatever positive weights `v` one
chooses.  Taking `v_j` to be the reciprocal of the harmonic mass of the `j`-th prime range makes
that total exactly the harmonic mass of the whole designated set — independent of how finely the
range is subdivided.  This is what allows the ladder to be as thin as the cofactor comparison needs
without the split paying for the number of steps.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- The harmonic mass of one ladder step. -/
def stepMass (P : Finset ℕ) (Q η : ℝ) (j : ℕ) : ℝ :=
  ∑ p ∈ geomBlock P Q (1 + η) j, 1 / (p : ℝ)

/-- **The step masses add up to the harmonic mass of the designated set**, for every subdivision. -/
theorem sum_stepMass_eq {P : Finset ℕ} {Q η : ℝ} (hQ : 0 < Q) (hη : 0 ≤ η) {L : ℕ} (hL : 1 ≤ L)
    (hP : ∀ p ∈ P, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + η) ^ L) :
    ∑ j ∈ Finset.range L, stepMass P Q η j = ∑ p ∈ P, 1 / (p : ℝ) := by
  classical
  have hr1 : (1 : ℝ) ≤ 1 + η := by linarith
  rw [show (∑ p ∈ P, 1 / (p : ℝ))
      = ∑ p ∈ (Finset.range L).biUnion (geomBlock P Q (1 + η)), 1 / (p : ℝ) by
    rw [geomBlock_biUnion_eq P Q (1 + η) hL hP]]
  rw [Finset.sum_biUnion (geomBlock_pairwiseDisjoint P hQ hr1 L)]
  rfl

/-- **The harmonic split of the ladder of products, pointwise.** -/
theorem normSq_ladderProductPoly_le {P : Finset ℕ} (A₀ B₀ : ℕ) (Q η : ℝ) {L : ℕ}
    (v : ℕ → ℝ) (hv : ∀ j ∈ Finset.range L, 0 < v j) (w : ℝ) :
    ‖ladderProductPoly P A₀ B₀ Q η L w‖ ^ 2
      ≤ (∑ j ∈ Finset.range L, 1 / v j)
        * ∑ j ∈ Finset.range L, v j
            * (‖primeBlockPoly (geomBlock P Q (1 + η) j) w‖ ^ 2
              * ‖logPoly moebiusCoeff (geomCofactorBlockAt A₀ B₀ Q η j) w‖ ^ 2) := by
  rw [ladderProductPoly]
  exact normSq_sum_mul_le_weighted (Finset.range L) v hv
    (fun j => primeBlockPoly (geomBlock P Q (1 + η) j) w)
    (fun j => logPoly moebiusCoeff (geomCofactorBlockAt A₀ B₀ Q η j) w)

/-- **The harmonic split of the ladder of products, in mean square.** -/
theorem integral_normSq_ladderProductPoly_le {P : Finset ℕ} (A₀ B₀ : ℕ) (Q η : ℝ) {L : ℕ}
    (v : ℕ → ℝ) (hv : ∀ j ∈ Finset.range L, 0 < v j) (W : ℝ) :
    (∫ w in Set.Icc (-W) W, ‖ladderProductPoly P A₀ B₀ Q η L w‖ ^ 2)
      ≤ (∑ j ∈ Finset.range L, 1 / v j)
        * ∑ j ∈ Finset.range L, v j
            * ∫ w in Set.Icc (-W) W,
                ‖primeBlockPoly (geomBlock P Q (1 + η) j) w‖ ^ 2
                  * ‖logPoly moebiusCoeff (geomCofactorBlockAt A₀ B₀ Q η j) w‖ ^ 2 := by
  classical
  set G : ℕ → ℝ → ℝ := fun j w =>
    ‖primeBlockPoly (geomBlock P Q (1 + η) j) w‖ ^ 2
      * ‖logPoly moebiusCoeff (geomCofactorBlockAt A₀ B₀ Q η j) w‖ ^ 2 with hG
  have hcontG : ∀ j : ℕ, Continuous (G j) := by
    intro j
    exact (((continuous_primeBlockPoly _).norm).pow 2).mul
      (((continuous_logPoly _ _).norm).pow 2)
  have hcontZ : Continuous fun w : ℝ => ‖ladderProductPoly P A₀ B₀ Q η L w‖ ^ 2 := by
    refine ((continuous_finsetSum _ fun j _ => ?_).norm).pow 2
    exact (continuous_primeBlockPoly _).mul (continuous_logPoly _ _)
  have hcontR : Continuous fun w : ℝ =>
      (∑ j ∈ Finset.range L, 1 / v j) * ∑ j ∈ Finset.range L, v j * G j w :=
    (continuous_finsetSum _ fun j _ => (hcontG j).const_mul _).const_mul _
  have hintZ : IntegrableOn (fun w : ℝ => ‖ladderProductPoly P A₀ B₀ Q η L w‖ ^ 2)
      (Set.Icc (-W) W) volume := hcontZ.integrableOn_Icc
  have hintR : IntegrableOn (fun w : ℝ =>
      (∑ j ∈ Finset.range L, 1 / v j) * ∑ j ∈ Finset.range L, v j * G j w)
      (Set.Icc (-W) W) volume := hcontR.integrableOn_Icc
  have hmono := setIntegral_mono_on hintZ hintR measurableSet_Icc
    (fun w _ => normSq_ladderProductPoly_le A₀ B₀ Q η v hv w)
  refine hmono.trans (le_of_eq ?_)
  rw [MeasureTheory.integral_const_mul]
  congr 1
  rw [integral_finsetSum _ fun j _ => ((hcontG j).const_mul (v j)).integrableOn_Icc]
  exact Finset.sum_congr rfl fun j _ => MeasureTheory.integral_const_mul _ _

end

end RHTower.Sieve
