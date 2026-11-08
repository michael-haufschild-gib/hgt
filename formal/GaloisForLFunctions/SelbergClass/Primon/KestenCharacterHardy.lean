import GaloisForLFunctions.SelbergClass.Primon.SemicircleCharacters
import GaloisForLFunctions.SelbergClass.Primon.KestenLikelihoodCompletion

/-!
# Hardy coordinates are even Chebyshev characters

Density of the prime kernels identifies every coordinate of the completed
likelihood unitary. The standard Hardy basis becomes the even Chebyshev
character family; every odd character is orthogonal to its entire range.
-/

open _root_.RHTower
namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

/-- The prime coefficient identity extends from a dense span to every Hardy vector. -/
private theorem inner_embedding_even (x : PrimeHardy) (n : ℕ) :
    inner ℝ (hardyLikelihoodEmbedding x) (spectralCharacterVector (2 * n)) =
      inner ℝ x (lp.single 2 n (1 : ℝ)) := by
  have hclosed : IsClosed {x : PrimeHardy |
      inner ℝ (hardyLikelihoodEmbedding x) (spectralCharacterVector (2 * n)) =
        inner ℝ x (lp.single 2 n (1 : ℝ))} :=
    isClosed_eq (hardyLikelihoodEmbedding.continuous.inner continuous_const)
      (continuous_id.inner continuous_const)
  have hsub : (primeHardyKernelMap.range : Set PrimeHardy) ⊆
      {x | inner ℝ (hardyLikelihoodEmbedding x) (spectralCharacterVector (2 * n)) =
        inner ℝ x (lp.single 2 n (1 : ℝ))} := by
    rintro _ ⟨c, rfl⟩
    change inner ℝ (hardyLikelihoodEmbedding (primeHardyKernelMap c))
      (spectralCharacterVector (2 * n)) = _
    rw [hardyLikelihoodEmbedding_map]
    induction c using Finsupp.induction with
    | zero => simp
    | single_add p a c hp ha ih =>
        simp only [map_add, inner_add_left, ih]
        congr 1
        simp only [kestenLikelihoodMap_single,
          primeHardyKernelMap_single, inner_smul_left, inner_likelihood_spectralCharacter_even]
        rw [lp.inner_single_right]
        simp only [RCLike.inner_apply, conj_trivial, one_mul, primeHardyKernel,
          hardyKernel_apply, primeReciprocal]
  have h := closure_minimal hsub hclosed
  rw [primeHardyKernelMap_dense.closure_eq] at h
  exact h (Set.mem_univ x)

/-- The even character coefficient of an embedded vector is its Hardy coordinate. -/
theorem inner_hardyLikelihoodEmbedding_evenCharacter (x : PrimeHardy) (n : ℕ) :
    inner ℝ (hardyLikelihoodEmbedding x) (spectralCharacterVector (2 * n)) = x n := by
  rw [inner_embedding_even, lp.inner_single_right]
  simp only [RCLike.inner_apply, conj_trivial, one_mul]

/-- The standard Hardy basis is sent to the even spectral characters. -/
theorem hardyLikelihoodEmbedding_single (n : ℕ) :
    hardyLikelihoodEmbedding (lp.single 2 n (1 : ℝ)) = spectralCharacterVector (2 * n) := by
  apply sub_eq_zero.mp
  rw [← inner_self_eq_zero (𝕜 := ℝ), inner_sub_sub_self,
    hardyLikelihoodEmbedding.inner_map_map, inner_embedding_even,
    real_inner_comm (hardyLikelihoodEmbedding (lp.single 2 n (1 : ℝ)))
      (spectralCharacterVector (2 * n)), inner_embedding_even,
    inner_spectralCharacterVector]
  simp

/-- Every odd character is orthogonal to the completed likelihood span. -/
theorem inner_hardyLikelihoodEmbedding_oddCharacter (x : PrimeHardy) (n : ℕ) :
    inner ℝ (hardyLikelihoodEmbedding x) (spectralCharacterVector (2 * n + 1)) = 0 := by
  have hclosed : IsClosed {x : PrimeHardy |
      inner ℝ (hardyLikelihoodEmbedding x) (spectralCharacterVector (2 * n + 1)) = 0} :=
    isClosed_eq (hardyLikelihoodEmbedding.continuous.inner continuous_const) continuous_const
  have hsub : (primeHardyKernelMap.range : Set PrimeHardy) ⊆
      {x | inner ℝ (hardyLikelihoodEmbedding x) (spectralCharacterVector (2 * n + 1)) = 0} := by
    rintro _ ⟨c, rfl⟩
    change inner ℝ (hardyLikelihoodEmbedding (primeHardyKernelMap c))
      (spectralCharacterVector (2 * n + 1)) = 0
    rw [hardyLikelihoodEmbedding_map]
    induction c using Finsupp.induction with
    | zero => simp
    | single_add p a c hp ha ih =>
        simp only [map_add, inner_add_left, ih, kestenLikelihoodMap_single,
          inner_smul_left, inner_likelihood_spectralCharacter_odd, mul_zero, add_zero]
  have h := closure_minimal hsub hclosed
  rw [primeHardyKernelMap_dense.closure_eq] at h
  exact h (Set.mem_univ x)

end
end GaloisForLFunctions.SelbergClass.Primon

