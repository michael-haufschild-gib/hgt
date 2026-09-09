import GaloisForLFunctions.HTGeometry.FokasLenellsCutoffExponential
import GaloisForLFunctions.HTGeometry.FokasLenellsCutoffPhaseLimit

/-!
# Optimal stability at every cutoff derivative order

Every actual operator derivative has a sharp global Lipschitz constant.
All positive-order norms and all derivative stability constants diverge
when the reciprocal-frequency cutoff is removed.
-/

open MeasureTheory Filter Topology Set
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

/-- Every time derivative remains real analytic in operator norm. -/
theorem cutoffEvolutionDerivative_analyticAt (a t : ℝ) (n : ℕ) :
    AnalyticAt ℝ (cutoffEvolutionDerivative a n) t := by
  have h := cutoffEvolution_analyticAt a t
  change AnalyticAt ℝ (fun s => cutoffEvolutionTimeOperator a 0 ^ n * cutoffEvolution a s) t
  exact analyticAt_const.mul h

/-- The next exact generator norm bounds the variation of each actual derivative. -/
theorem norm_cutoffEvolutionDerivative_sub_le (a s t : ℝ) (n : ℕ) :
    ‖cutoffEvolutionDerivative a n s - cutoffEvolutionDerivative a n t‖ ≤
      cutoffPhaseBudget a ^ (n+1) * ‖s-t‖ := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := Set.univ) (f := cutoffEvolutionDerivative a n)
    (f' := cutoffEvolutionDerivative a (n+1)) (C := cutoffPhaseBudget a ^ (n+1))
    (fun s _ => (cutoffEvolutionDerivative_hasDerivAt a s n).hasDerivWithinAt)
    (fun s _ => (norm_cutoffEvolutionDerivative a s (n+1)).le)
    convex_univ (mem_univ t) (mem_univ s)
  exact h

/-- Every derivative's best global Lipschitz constant is exactly the next budget power. -/
theorem cutoffEvolutionDerivative_lipschitz_iff (a L : ℝ) (n : ℕ) :
    (∀ s t, ‖cutoffEvolutionDerivative a n s - cutoffEvolutionDerivative a n t‖ ≤ L * ‖s-t‖) ↔
      cutoffPhaseBudget a ^ (n+1) ≤ L := by
  constructor
  · intro h
    have hL : 0 ≤ L := by
      have h10 := (norm_nonneg (cutoffEvolutionDerivative a n 1 - cutoffEvolutionDerivative a n 0)).trans (h 1 0)
      simpa using h10
    have hb := norm_deriv_le_of_lip' hL (Eventually.of_forall fun s => h s 0)
    rw [(cutoffEvolutionDerivative_hasDerivAt a 0 n).deriv,norm_cutoffEvolutionDerivative] at hb
    exact hb
  · intro h s t
    exact (norm_cutoffEvolutionDerivative_sub_le a s t n).trans
      (mul_le_mul_of_nonneg_right h (norm_nonneg _))

/-- The exact norm of each positive derivative diverges as the cutoff shrinks. -/
theorem cutoffEvolutionDerivative_norm_tendsto_atBot (t : ℝ) (n : ℕ) :
    Tendsto (fun a => ‖cutoffEvolutionDerivative a (n+1) t‖) atBot atTop := by
  simp only [norm_cutoffEvolutionDerivative]
  exact (tendsto_pow_atTop (Nat.succ_ne_zero n)).comp cutoffPhaseBudget_tendsto_atBot

/-- No derivative order admits a global Lipschitz constant uniform in the cutoff. -/
theorem cutoffEvolutionDerivative_no_uniform_lipschitz_constant (L : ℝ) (n : ℕ) :
    ¬ ∀ a s t : ℝ, ‖cutoffEvolutionDerivative a n s - cutoffEvolutionDerivative a n t‖ ≤ L * ‖s-t‖ := by
  intro h
  have hb : ∀ a, cutoffPhaseBudget a ^ (n+1) ≤ L :=
    fun a => (cutoffEvolutionDerivative_lipschitz_iff a L n).1 (h a)
  have ht := cutoffEvolutionDerivative_norm_tendsto_atBot 0 n
  have he := (tendsto_atTop.1 ht (L+1)).exists
  obtain ⟨a,ha⟩ := he
  rw [norm_cutoffEvolutionDerivative] at ha
  linarith [hb a]

/-- The actual iterated derivatives satisfy the same sharp global stability classification. -/
theorem iteratedDeriv_cutoffEvolution_lipschitz_iff (a L : ℝ) (n : ℕ) :
    (∀ s t, ‖iteratedDeriv n (cutoffEvolution a) s - iteratedDeriv n (cutoffEvolution a) t‖ ≤ L * ‖s-t‖) ↔
      cutoffPhaseBudget a ^ (n+1) ≤ L := by
  rw [iteratedDeriv_cutoffEvolution]
  exact cutoffEvolutionDerivative_lipschitz_iff a L n

end
end GaloisForLFunctions.HTGeometry.FokasLenells
