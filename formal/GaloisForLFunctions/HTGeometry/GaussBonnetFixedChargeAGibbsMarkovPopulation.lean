import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeACriticalMarkovSemigroup
import GaloisForLFunctions.HTGeometry.FiniteKMSWightman

/-!
The critical Gibbs Markov dynamics from arXiv:2609.00025 acts on the corpus's
existing finite KMS/Gibbs probabilities. Inverse temperatures and energies are
arbitrary real data; all probability obligations are proved internally.
-/
namespace GaloisForLFunctions.HTGeometry

open Filter Topology
open scoped Matrix

noncomputable section

/-- Existing finite Gibbs probability after m critical-kernel Markov transitions. -/
def egbFixedChargeAGibbsMarkovPopulation (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) : Fin (2 ^ (n + 3)) → ℝ :=
  (egbFixedChargeACriticalMarkovIteratedKernel n m).toFinitePositiveKernel.applyReal
    (_root_.HTGeometry.finiteGibbsStateWeight β E)

/-- Every intermediate Gibbs population is nonnegative. -/
theorem egbFixedChargeAGibbsMarkovPopulation_nonneg
    (n m : ℕ) (β : ℝ) (E : Fin (2 ^ (n + 3)) → ℝ) (i : Fin (2 ^ (n + 3))) :
    0 ≤ egbFixedChargeAGibbsMarkovPopulation n m β E i := by
  exact FinitePositiveKernel.applyReal_nonneg _
    (fun j => (_root_.HTGeometry.finiteGibbsStateWeight_pos β E j).le) i

/-- Every intermediate Gibbs population has total mass one. -/
theorem egbFixedChargeAGibbsMarkovPopulation_mass
    (n m : ℕ) (β : ℝ) (E : Fin (2 ^ (n + 3)) → ℝ) :
    ∑ i : Fin (2 ^ (n + 3)), egbFixedChargeAGibbsMarkovPopulation n m β E i = 1 := by
  rw [egbFixedChargeAGibbsMarkovPopulation, FiniteMarkovKernel.sum_applyReal]
  exact _root_.HTGeometry.sum_finiteGibbsStateWeight_eq_one β E

/-- Strict positivity survives every number of transitions, including the initial state. -/
theorem egbFixedChargeAGibbsMarkovPopulation_pos
    (n m : ℕ) (β : ℝ) (E : Fin (2 ^ (n + 3)) → ℝ) (i : Fin (2 ^ (n + 3))) :
    0 < egbFixedChargeAGibbsMarkovPopulation n m β E i := by
  have hj : ∃ j : Fin (2 ^ (n + 3)), 0 < ((egbFixedChargeACriticalMarkovMatrix n ^ m) i j).re := by
    by_contra h
    have hz : ∀ j : Fin (2 ^ (n + 3)), ((egbFixedChargeACriticalMarkovMatrix n ^ m) i j).re = 0 := by
      intro j
      exact le_antisymm (le_of_not_gt (fun hj => h ⟨j, hj⟩))
        (egbFixedChargeACriticalMarkovMatrix_pow_nonneg n m i j)
    have hr := egbFixedChargeACriticalMarkovMatrix_pow_row_sum n m i
    simp only [hz, Finset.sum_const_zero] at hr
    norm_num at hr
  obtain ⟨j, hj⟩ := hj
  change 0 < ∑ k : Fin (2 ^ (n + 3)),
    ((egbFixedChargeACriticalMarkovMatrix n ^ m) i k).re *
      _root_.HTGeometry.finiteGibbsStateWeight β E k
  apply Finset.sum_pos'
  · intro k _
    exact mul_nonneg (egbFixedChargeACriticalMarkovMatrix_pow_nonneg n m i k)
      (_root_.HTGeometry.finiteGibbsStateWeight_pos β E k).le
  · exact ⟨j, Finset.mem_univ _, mul_pos hj (_root_.HTGeometry.finiteGibbsStateWeight_pos β E j)⟩

/-- Real population transport agrees exactly with the complex QFT operator. -/
theorem egbFixedChargeAGibbsMarkovPopulation_complex_identity
    (n m : ℕ) (β : ℝ) (E : Fin (2 ^ (n + 3)) → ℝ) (i : Fin (2 ^ (n + 3))) :
    egbFixedChargeAGibbsMarkovPopulation n m β E i =
      (((egbFixedChargeACriticalMarkovMatrix n ^ m) *ᵥ
        (fun j => (_root_.HTGeometry.finiteGibbsStateWeight β E j : ℂ))) i).re := by
  change (∑ j, ((egbFixedChargeACriticalMarkovMatrix n ^ m) i j).re *
    _root_.HTGeometry.finiteGibbsStateWeight β E j) =
      (∑ j, (egbFixedChargeACriticalMarkovMatrix n ^ m) i j *
        (_root_.HTGeometry.finiteGibbsStateWeight β E j : ℂ)).re
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]

/-- Every initial finite Gibbs probability converges to the uniform law. -/
theorem egbFixedChargeAGibbsMarkovPopulation_limit
    (n : ℕ) (β : ℝ) (E : Fin (2 ^ (n + 3)) → ℝ) :
    Tendsto (fun m : ℕ => egbFixedChargeAGibbsMarkovPopulation n m β E) atTop
      (𝓝 (fun _ : Fin (2 ^ (n + 3)) => ((2 : ℝ) ^ (n + 3))⁻¹)) := by
  have hp := egbFixedChargeACriticalMarkovMatrix_profile_limit n
    (fun j => (_root_.HTGeometry.finiteGibbsStateWeight β E j : ℂ))
  have hs : (∑ j : Fin (2 ^ (n + 3)),
      (_root_.HTGeometry.finiteGibbsStateWeight β E j : ℂ)) = 1 := by
    rw [← Complex.ofReal_sum, _root_.HTGeometry.sum_finiteGibbsStateWeight_eq_one]
    rfl
  rw [hs, mul_one] at hp
  refine tendsto_pi_nhds.mpr fun i => ?_
  have hi := tendsto_pi_nhds.mp hp i
  have hr := Complex.continuous_re.continuousAt.tendsto.comp hi
  simpa only [Function.comp_def, ← egbFixedChargeAGibbsMarkovPopulation_complex_identity,
    ← Complex.ofReal_pow, ← Complex.ofReal_inv, Complex.ofReal_re] using hr

end

end GaloisForLFunctions.HTGeometry
