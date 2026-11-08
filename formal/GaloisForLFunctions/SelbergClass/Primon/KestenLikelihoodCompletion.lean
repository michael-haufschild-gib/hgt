import GaloisForLFunctions.SelbergClass.Primon.KestenLikelihoodHardy
import GaloisForLFunctions.RHTower.ArithmeticLogClockFiniteJetSaturation
import GaloisForLFunctions.HTGeometry.LinearIsometryCompletion

/-!
# Completing the likelihood Hardy model

Reciprocal-prime kernels are total in the real Hardy space. Consequently
the likelihood-span isometry extends to an isometric embedding of that
whole space into semicircle `L²`. Its closed range is exactly the closed
span of the actual prime likelihoods.
-/

open Filter Topology UniformSpace
open _root_.RHTower
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

/-- Reciprocal-prime kernels form a total family in the real Hardy space. -/
theorem primeHardyKernelMap_dense :
    Dense (primeHardyKernelMap.range : Set PrimeHardy) := by
  apply Submodule.dense_iff_topologicalClosure_eq_top.2
  have horth : primeHardyKernelMap.rangeᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    have hrel : PrimeTailLogRelation 0 x 0 := by
      intro p
      have hp := hx (primeHardyKernel p) ⟨Finsupp.single p 1, by simp⟩
      simpa only [inner_zero_right, mul_zero, add_zero] using hp
    exact (primeTailLogRelation_zero_eq_zero hrel).1
  rw [← Submodule.orthogonal_orthogonal_eq_closure, horth,
    Submodule.bot_orthogonal_eq_top]

private def hardyRangeCompletionEquiv :
    Completion primeHardyKernelMap.range ≃ₗᵢ[ℝ] PrimeHardy where
  toLinearEquiv := LinearEquiv.ofBijective
    (completionExtendₗᵢ (Submodule.subtypeₗᵢ primeHardyKernelMap.range)).toLinearMap
    ⟨(completionExtendₗᵢ _).injective,
      denseRange_completionExtendₗᵢ_of_denseRange _ (by
        change Dense (Set.range (Submodule.subtypeₗᵢ primeHardyKernelMap.range))
        apply primeHardyKernelMap_dense.mono
        intro x hx
        exact ⟨⟨x, hx⟩, rfl⟩)⟩
  norm_map' := (completionExtendₗᵢ _).norm_map

private theorem hardyRangeCompletionEquiv_coe (x : primeHardyKernelMap.range) :
    hardyRangeCompletionEquiv (x : Completion primeHardyKernelMap.range) = (x : PrimeHardy) :=
  completionExtendₗᵢ_coe _ x

private def likelihoodFromHardyRange : primeHardyKernelMap.range →ₗᵢ[ℝ] SemicircleL2 :=
  (Submodule.subtypeₗᵢ kestenLikelihoodMap.range).comp
    kestenLikelihoodHardyEquiv.symm.toLinearIsometry

/-- The complete Hardy space realized by actual semicircle likelihood observables. -/
def hardyLikelihoodEmbedding : PrimeHardy →ₗᵢ[ℝ] SemicircleL2 :=
  (completionExtendₗᵢ likelihoodFromHardyRange).comp
    hardyRangeCompletionEquiv.symm.toLinearIsometry

/-- Completion preserves every finite packet, with no analytic input beyond its Gram kernel. -/
theorem hardyLikelihoodEmbedding_map (c : Nat.Primes →₀ ℝ) :
    hardyLikelihoodEmbedding (primeHardyKernelMap c) = kestenLikelihoodMap c := by
  let x : primeHardyKernelMap.range := ⟨primeHardyKernelMap c, ⟨c, rfl⟩⟩
  have hx : hardyRangeCompletionEquiv.symm (primeHardyKernelMap c) =
      (x : Completion primeHardyKernelMap.range) := by
    apply hardyRangeCompletionEquiv.injective
    rw [hardyRangeCompletionEquiv.apply_symm_apply, hardyRangeCompletionEquiv_coe]
  change completionExtendₗᵢ likelihoodFromHardyRange
    (hardyRangeCompletionEquiv.symm (primeHardyKernelMap c)) = _
  rw [hx, completionExtendₗᵢ_coe]
  exact kestenLikelihoodHardyEquiv_symm_apply c

/-- The Hardy geometric vector at `p⁻¹` becomes the actual prime likelihood. -/
@[simp] theorem hardyLikelihoodEmbedding_kernel (p : Nat.Primes) :
    hardyLikelihoodEmbedding (primeHardyKernel p) = kestenLikelihoodVector p := by
  simpa using hardyLikelihoodEmbedding_map (Finsupp.single p 1)

/-- The completed likelihood realization has closed range in semicircle `L²`. -/
theorem isClosed_range_hardyLikelihoodEmbedding :
    IsClosed (Set.range hardyLikelihoodEmbedding) :=
  hardyLikelihoodEmbedding.isometry.isClosedEmbedding.isClosed_range

/-- The embedding fills exactly the closed span of prime likelihoods. -/
theorem range_hardyLikelihoodEmbedding :
    Set.range hardyLikelihoodEmbedding =
      closure (kestenLikelihoodMap.range : Set SemicircleL2) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, rfl⟩
    have hclosed : IsClosed {x : PrimeHardy |
        hardyLikelihoodEmbedding x ∈ closure (kestenLikelihoodMap.range : Set SemicircleL2)} :=
      isClosed_closure.preimage hardyLikelihoodEmbedding.continuous
    have hsub : (primeHardyKernelMap.range : Set PrimeHardy) ⊆
        {x | hardyLikelihoodEmbedding x ∈
          closure (kestenLikelihoodMap.range : Set SemicircleL2)} := by
      rintro _ ⟨c, rfl⟩
      change hardyLikelihoodEmbedding (primeHardyKernelMap c) ∈
        closure (kestenLikelihoodMap.range : Set SemicircleL2)
      rw [hardyLikelihoodEmbedding_map]
      exact subset_closure ⟨c, rfl⟩
    have h := closure_minimal hsub hclosed
    rw [primeHardyKernelMap_dense.closure_eq] at h
    exact h (Set.mem_univ x)
  · apply closure_minimal _ isClosed_range_hardyLikelihoodEmbedding
    rintro _ ⟨c, rfl⟩
    exact ⟨primeHardyKernelMap c, hardyLikelihoodEmbedding_map c⟩

/-- The closed semicircle Hilbert subspace generated by all prime likelihoods. -/
abbrev KestenLikelihoodHilbert := kestenLikelihoodMap.range.topologicalClosure

instance : CompleteSpace KestenLikelihoodHilbert :=
  Submodule.topologicalClosure.completeSpace _

private def hardyLikelihoodToClosedSpan : PrimeHardy →ₗᵢ[ℝ] KestenLikelihoodHilbert where
  toFun x := ⟨hardyLikelihoodEmbedding x, by
    change hardyLikelihoodEmbedding x ∈ closure (kestenLikelihoodMap.range : Set SemicircleL2)
    rw [← range_hardyLikelihoodEmbedding]
    exact ⟨x, rfl⟩⟩
  map_add' x y := Subtype.ext (map_add hardyLikelihoodEmbedding x y)
  map_smul' c x := Subtype.ext (map_smul hardyLikelihoodEmbedding c x)
  norm_map' x := hardyLikelihoodEmbedding.norm_map x

/-- A unitary identification of the entire real Hardy space with the closed likelihood span. -/
def hardyLikelihoodUnitary : PrimeHardy ≃ₗᵢ[ℝ] KestenLikelihoodHilbert where
  toLinearEquiv := LinearEquiv.ofBijective hardyLikelihoodToClosedSpan.toLinearMap
    ⟨hardyLikelihoodToClosedSpan.injective, by
      intro y
      have hy := y.property
      change (y : SemicircleL2) ∈ closure (kestenLikelihoodMap.range : Set SemicircleL2) at hy
      rw [← range_hardyLikelihoodEmbedding] at hy
      obtain ⟨x, hx⟩ := hy
      exact ⟨x, Subtype.ext hx⟩⟩
  norm_map' := hardyLikelihoodToClosedSpan.norm_map

/-- The completed unitary sends every prime Hardy kernel to its likelihood vector. -/
theorem hardyLikelihoodUnitary_kernel (p : Nat.Primes) :
    (hardyLikelihoodUnitary (primeHardyKernel p) : SemicircleL2) =
      kestenLikelihoodVector p :=
  hardyLikelihoodEmbedding_kernel p

end
end GaloisForLFunctions.SelbergClass.Primon

