import GaloisForLFunctions.RHTower.Sieve.Section4ExceptionalMeasure

/-!
# One block of exposé §4, with every input discharged

Composing `Sieve/Section4Block.section4_block_bound` with Lemma 2.5
(`Sieve/Section4ExceptionalMeasure.volume_blockExceptional_le`) leaves a single inequality between
explicit quantities: the mean square of a prime block polynomial against an arbitrary cofactor
polynomial, over a symmetric window in the Gallagher variable, with no hypothesis beyond the
membership of the two index sets in initial segments.

The free parameters are the cancellation threshold `V` of `(35)` and the power `k` of Lemma 2.5.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- The trivial sup bound for a prime block polynomial, in Dirichlet form. -/
theorem norm_dirPoly_finCoeff_le_card {B : Finset ℕ} {NA : ℕ} (t : ℝ) :
    ‖dirPoly NA (finCoeff B moebiusCoeff NA) t‖ ≤ (B.card : ℝ) := by
  classical
  refine (norm_dirPoly_le_sum_norm NA (finCoeff B moebiusCoeff NA) t).trans ?_
  have hterm : ∀ n : Fin NA, ‖finCoeff B moebiusCoeff NA n‖
      ≤ (if ((n : ℕ) + 1) ∈ B then (1 : ℝ) else 0) := by
    intro n
    rw [finCoeff, restrictCoeff]
    by_cases h : ((n : ℕ) + 1) ∈ B
    · rw [if_pos h, if_pos h]
      exact norm_moebiusCoeff_le_one _
    · rw [if_neg h, if_neg h]
      simp
  refine (Finset.sum_le_sum fun n _ => hterm n).trans ?_
  rw [Finset.sum_boole]
  have hcard : ((Finset.univ.filter (fun n : Fin NA => ((n : ℕ) + 1) ∈ B)).card : ℕ) ≤ B.card := by
    refine Finset.card_le_card_of_injOn (fun n : Fin NA => (n : ℕ) + 1) ?_ ?_
    · intro n hn
      exact (Finset.mem_filter.1 hn).2
    · intro x _ y _ hxy
      have h : (x : ℕ) + 1 = (y : ℕ) + 1 := hxy
      exact Fin.ext (by omega)
  exact_mod_cast hcard

/-- **The §4 estimate for one prime block, closed.** -/
theorem section4_block_bound_prime (b : ℕ → ℂ) {B D : Finset ℕ} {NA NB k : ℕ}
    (hBprime : ∀ p ∈ B, p.Prime) (hBsub : B ⊆ Finset.Icc 1 NA) (hD : D ⊆ Finset.Icc 1 NB)
    (hNB : 1 ≤ NB) (hk : 1 ≤ k) {W V : ℝ} (hW : 0 ≤ W) (hV : 0 < V) :
    (∫ w in Set.Icc (-W) W, ‖primeBlockPoly B w‖ ^ (2 : ℕ) * ‖logPoly b D w‖ ^ (2 : ℕ))
      ≤ (2 * Real.pi)⁻¹
        * (V ^ (2 : ℕ) * (2 * (((2 * Real.pi * W) + 4 * (NB : ℝ) * (1 + Real.log NB))
              * ∑ n : Fin NB, ‖finCoeff D b NB n‖ ^ (2 : ℕ)))
          + (B.card : ℝ) ^ (2 : ℕ) * ((2 * (NB : ℝ)
              + (((Nat.log 2 NB : ℝ) + 1) * (214 * Real.sqrt (2 * (2 * Real.pi * W)))
                  + 3072 * (NB : ℝ))
                * (2 * (((2 * Real.pi * W)
                      + 4 * ((NA ^ k : ℕ) : ℝ) * (1 + Real.log ((NA ^ k : ℕ) : ℝ)))
                    * ((k : ℝ) ^ k * (B.card : ℝ) ^ k)) / V ^ (2 * k)))
              * ∑ n : Fin NB, ‖finCoeff D b NB n‖ ^ (2 : ℕ))) := by
  classical
  have hT0 : (0 : ℝ) ≤ 2 * Real.pi * W := by positivity
  have hEV := volume_blockExceptional_le (B := B) (NA := NA) (k := k) hBprime hk hT0 hV
  have hmain := section4_block_bound moebiusCoeff b hBsub hD hNB hW
    (fun t => norm_dirPoly_finCoeff_le_card t) hEV
  have hrw : ∀ w : ℝ, ‖primeBlockPoly B w‖ ^ (2 : ℕ) * ‖logPoly b D w‖ ^ (2 : ℕ)
      = ‖logPoly moebiusCoeff B w‖ ^ (2 : ℕ) * ‖logPoly b D w‖ ^ (2 : ℕ) := by
    intro w
    rw [primeBlockPoly_eq_logPoly]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun w _ => hrw w]
  exact hmain

end

end RHTower.Sieve
