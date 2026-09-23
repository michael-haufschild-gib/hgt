import GaloisForLFunctions.RHTower.GammaSewnPluckerNuclearRootIncidence
import GaloisForLFunctions.HTGeometry.ContractionCompressionExhaustion
import GaloisForLFunctions.RHTower.SuzukiCausalDepthGammaTraceClassFeatureRobinTraceNoGo

open Real Set Filter Topology ContinuousLinearMap
open scoped BigOperators InnerProductSpace ComplexOrder
noncomputable section
namespace RHTower.HedenmalmThetaSource

private abbrev H := GammaSewnCriticalPhysicalPluckerHilbert

local instance gammaSewnPluckerGlobalMeanNuclearRootInst1 : ContinuousFunctionalCalculus ℝ (H →L[ℂ] H) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

private def diagonal (u : ℕ × ℕ) : (H →L[ℂ] H) →L[ℝ] ℝ :=
  Complex.reCLM.comp (((innerSL ℂ (gammaSewnCriticalPhysicalPluckerBasis u)).comp
    (ContinuousLinearMap.apply ℂ H (gammaSewnCriticalPhysicalPluckerBasis u))).restrictScalars ℝ)

private theorem diagonal_rankOne (u : ℕ × ℕ) (c : ℝ) (v : H) :
    diagonal u ((c : ℂ) • InnerProductSpace.rankOne ℂ v v) = c * ‖v u‖ ^ (2 : ℕ) := by
  change (inner ℂ (gammaSewnCriticalPhysicalPluckerBasis u)
    (((c : ℂ) • InnerProductSpace.rankOne ℂ v v) (gammaSewnCriticalPhysicalPluckerBasis u))).re = _
  calc
    _ = (inner ℂ (((c : ℂ) • InnerProductSpace.rankOne ℂ v v)
        (gammaSewnCriticalPhysicalPluckerBasis u)) (gammaSewnCriticalPhysicalPluckerBasis u)).re :=
      inner_re_symm (𝕜 := ℂ) _ _
    _ = _ := by simpa [GaloisForLFunctions.HTGeometry.rankOneOp, InnerProductSpace.rankOne,
    gammaSewnCriticalPhysicalPluckerBasis, lp.inner_single_right, RCLike.inner_apply] using
    GaloisForLFunctions.HTGeometry.re_inner_rankOneOp c v (gammaSewnCriticalPhysicalPluckerBasis u)

private def squareBudget (u : ℕ × ℕ) : ℝ :=
  ∑' z : ℕ × ℕ, gammaSewnCriticalPluckerRootProfile z u ^ (2 : ℕ)

private theorem summable_squareProfile (u : ℕ × ℕ) :
    Summable (fun z : ℕ × ℕ => gammaSewnCriticalPluckerRootProfile z u ^ (2 : ℕ)) := by
  refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun z => ?_)
    ((summable_gammaSewnCriticalPluckerRootProfile_left u).mul_right
      (gammaSewnCriticalPluckerRootDiagonalBudget u))
  rw [pow_two]
  exact mul_le_mul_of_nonneg_left (gammaSewnCriticalPluckerRootProfile_le_budget z u)
    (gammaSewnCriticalPluckerRootProfile_nonneg z u)

private theorem squareBudget_le (u : ℕ × ℕ) :
    squareBudget u ≤ gammaSewnCriticalPluckerRootDiagonalBudget u ^ (2 : ℕ) := by
  have hle := Summable.tsum_le_tsum
    (fun z => show gammaSewnCriticalPluckerRootProfile z u ^ (2 : ℕ) ≤
      gammaSewnCriticalPluckerRootProfile z u * gammaSewnCriticalPluckerRootDiagonalBudget u by
      rw [pow_two]
      exact mul_le_mul_of_nonneg_left (gammaSewnCriticalPluckerRootProfile_le_budget z u)
        (gammaSewnCriticalPluckerRootProfile_nonneg z u))
    (summable_squareProfile u) ((summable_gammaSewnCriticalPluckerRootProfile_left u).mul_right _)
  simpa [squareBudget, tsum_mul_right, gammaSewnCriticalPluckerRootDiagonalBudget, pow_two] using hle

private theorem rootProfile_sq (z u : ℕ × ℕ) :
    gammaSewnCriticalPluckerRootProfile z u ^ (2 : ℕ) =
      gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z *
        gammaSewnCriticalPluckerCoordinateProfile z u ^ (2 : ℕ) := by
  rw [gammaSewnCriticalPluckerRootProfile, mul_pow,
    Real.sq_sqrt (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight_pos z).le]

private theorem diagonal_local_le (u : ℕ × ℕ) :
    diagonal u gammaSewnCriticalPhysicalPluckerSpectralOperator ≤ squareBudget u := by
  let f : (ℕ × ℕ) × Fin 6 → ℝ := fun zs =>
    diagonal u (gammaSewnCriticalPhysicalPluckerPositiveRankOneTerm zs)
  have hf : Summable f := (Summable.of_norm
    summable_norm_gammaSewnCriticalPhysicalPluckerPositiveRankOneTerm).mapL (diagonal u)
  have heq : diagonal u gammaSewnCriticalPhysicalPluckerSpectralOperator = ∑' zs, f zs := by
    exact ((diagonal u).map_tsum (Summable.of_norm
      summable_norm_gammaSewnCriticalPhysicalPluckerPositiveRankOneTerm))
  rw [heq, hf.tsum_prod]
  apply Summable.tsum_le_tsum _ hf.prod (summable_squareProfile u)
  intro z
  rw [tsum_fintype, rootProfile_sq]
  calc
    ∑ s : Fin 6, f (z, s) ≤ ∑ s : Fin 6,
        gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z *
          gammaSewnCriticalAdjacentPrime_PluckerProbability z s *
            gammaSewnCriticalPluckerCoordinateProfile z u ^ (2 : ℕ) := by
      apply Finset.sum_le_sum
      intro s _
      change diagonal u (((_ : ℝ) : ℂ) • InnerProductSpace.rankOne ℂ _ _) ≤ _
      rw [diagonal_rankOne]
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg
        (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight_pos z).le
        (gammaSewnCriticalAdjacentPrime_PluckerProbability_pos z s).le)
      exact (sq_le_sq₀ (norm_nonneg _)
        (gammaSewnCriticalPluckerCoordinateProfile_nonneg z u)).2
          (norm_gammaSewnCriticalPhysicalPluckerCenteredVector_apply_le_profile z u s)
    _ = _ := by
      rw [← Finset.sum_mul, ← Finset.mul_sum,
        sum_gammaSewnCriticalAdjacentPrime_PluckerProbability, mul_one]

private theorem diagonal_dispersion_le (u : ℕ × ℕ) :
    diagonal u gammaSewnCriticalPhysicalPluckerGlobalMeanDispersionOperator ≤ 2 * squareBudget u := by
  let f : (ℕ × ℕ) × (ℕ × ℕ) → ℝ := fun zw =>
    diagonal u (gammaSewnCriticalPhysicalPluckerMeanDispersionRankOneTerm zw)
  let g : (ℕ × ℕ) × (ℕ × ℕ) → ℝ := fun zw =>
    gammaSewnCriticalAdjacentPrime_PluckerBlockWeight zw.2 *
        gammaSewnCriticalPluckerRootProfile zw.1 u ^ (2 : ℕ) +
      gammaSewnCriticalAdjacentPrime_PluckerBlockWeight zw.1 *
        gammaSewnCriticalPluckerRootProfile zw.2 u ^ (2 : ℕ)
  have hf : Summable f := (Summable.of_norm
    summable_norm_gammaSewnCriticalPhysicalPluckerMeanDispersionRankOneTerm).mapL (diagonal u)
  have hright := summable_mul_of_summable_norm
    summable_gammaSewnCriticalAdjacentPrime_PluckerBlockWeight.norm (summable_squareProfile u).norm
  have hleft := (summable_mul_of_summable_norm
    (summable_squareProfile u).norm summable_gammaSewnCriticalAdjacentPrime_PluckerBlockWeight.norm)
  have hleft' : Summable (fun zw : (ℕ × ℕ) × (ℕ × ℕ) =>
      gammaSewnCriticalAdjacentPrime_PluckerBlockWeight zw.2 *
        gammaSewnCriticalPluckerRootProfile zw.1 u ^ (2 : ℕ)) :=
    hleft.congr fun zw => mul_comm _ _
  have hg : Summable g := hleft'.add hright
  have heq : diagonal u gammaSewnCriticalPhysicalPluckerGlobalMeanDispersionOperator = ∑' zw, f zw := by
    exact (diagonal u).map_tsum (Summable.of_norm
      summable_norm_gammaSewnCriticalPhysicalPluckerMeanDispersionRankOneTerm)
  rw [heq]
  calc
    ∑' zw, f zw ≤ ∑' zw, g zw := by
      apply Summable.tsum_le_tsum _ hf hg
      intro zw
      change diagonal u (((_ : ℝ) : ℂ) • InnerProductSpace.rankOne ℂ _ _) ≤ _
      rw [diagonal_rankOne]
      have ha := norm_gammaSewnCriticalPhysicalPluckerMeanVector_apply_le_profile zw.1 u
      have hb := norm_gammaSewnCriticalPhysicalPluckerMeanVector_apply_le_profile zw.2 u
      have hn : ‖gammaSewnCriticalPhysicalPluckerMeanDifference zw.1 zw.2 u‖ ≤
          gammaSewnCriticalPluckerCoordinateProfile zw.1 u +
            gammaSewnCriticalPluckerCoordinateProfile zw.2 u :=
        (norm_sub_le _ _).trans (add_le_add ha hb)
      have hn2 := (sq_le_sq₀ (norm_nonneg _)
        (add_nonneg (gammaSewnCriticalPluckerCoordinateProfile_nonneg _ _)
          (gammaSewnCriticalPluckerCoordinateProfile_nonneg _ _))).2 hn
      have hsum : ‖gammaSewnCriticalPhysicalPluckerMeanDifference zw.1 zw.2 u‖ ^ (2 : ℕ) ≤
          2 * (gammaSewnCriticalPluckerCoordinateProfile zw.1 u ^ (2 : ℕ) +
            gammaSewnCriticalPluckerCoordinateProfile zw.2 u ^ (2 : ℕ)) := by
        nlinarith [sq_nonneg (gammaSewnCriticalPluckerCoordinateProfile zw.1 u -
          gammaSewnCriticalPluckerCoordinateProfile zw.2 u)]
      have hm := mul_le_mul_of_nonneg_left hsum
        (show 0 ≤ (1 / 2 : ℝ) * gammaSewnCriticalAdjacentPrime_PluckerBlockWeight zw.1 *
          gammaSewnCriticalAdjacentPrime_PluckerBlockWeight zw.2 from
            mul_nonneg (mul_nonneg (by norm_num)
              (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight_pos zw.1).le)
              (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight_pos zw.2).le)
      unfold g
      rw [rootProfile_sq, rootProfile_sq]
      nlinarith only [hm]
    _ = 2 * squareBudget u := by
      rw [Summable.tsum_add hleft' hright, hleft'.tsum_prod, hright.tsum_prod]
      simp only [tsum_mul_left, tsum_mul_right,
        tsum_gammaSewnCriticalAdjacentPrime_PluckerBlockWeight, one_mul]
      change squareBudget u + squareBudget u = _
      ring

/-- Source-native diagonal bound before any Xi selection. -/
theorem gammaSewnCriticalPhysicalPluckerGlobalMeanPolarized_diagonal_le_rootBudget
    (u : ℕ × ℕ) :
    (inner ℂ (gammaSewnCriticalPhysicalPluckerBasis u)
      (gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedOperator
        (gammaSewnCriticalPhysicalPluckerBasis u))).re ≤
      3 * gammaSewnCriticalPluckerRootDiagonalBudget u ^ (2 : ℕ) := by
  change diagonal u gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedOperator ≤ _
  rw [gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedOperator_eq_add, map_add]
  linarith [diagonal_local_le u, diagonal_dispersion_le u, squareBudget_le u]

/-- The literal positive square root has a summable source-native column budget. -/
theorem norm_gammaSewnCriticalPhysicalPluckerGlobalMeanPolarized_sqrt_apply_le
    (u : ℕ × ℕ) :
    ‖CFC.sqrt gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedOperator
      (gammaSewnCriticalPhysicalPluckerBasis u)‖ ≤
        Real.sqrt 3 * gammaSewnCriticalPluckerRootDiagonalBudget u := by
  let T := gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedOperator
  let R := CFC.sqrt T
  let b := gammaSewnCriticalPhysicalPluckerBasis u
  have hT : (0 : H →L[ℂ] H) ≤ T :=
    (ContinuousLinearMap.nonneg_iff_isPositive _).2
      gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedOperator_isPositive
  have hR : IsSelfAdjoint R := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg T)
  have hRR : R ∘L R = T := CFC.sqrt_mul_sqrt_self T hT
  have hdiag : ‖R b‖ ^ (2 : ℕ) = (inner ℂ b (T b)).re := by
    have heq : inner ℂ (R b) (R b) = inner ℂ b (T b) := by
      calc
        _ = inner ℂ b (R (R b)) := hR.isSymmetric b (R b)
        _ = _ := congrArg (fun S : H →L[ℂ] H => inner ℂ b (S b)) hRR
    have heq' := congrArg Complex.re heq
    simpa [← Complex.ofReal_pow] using heq'
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _)
    (gammaSewnCriticalPluckerRootDiagonalBudget_nonneg u))).mp
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  change ‖R b‖ ^ (2 : ℕ) ≤ _
  rw [hdiag]
  exact gammaSewnCriticalPhysicalPluckerGlobalMeanPolarized_diagonal_le_rootBudget u

/-- C1's actual global-mean polarization is in the nuclear-root ideal. This is stronger than
trace class and is established before Xi selection, retaining the prime-depth incidence. -/
theorem gammaSewnCriticalPhysicalPluckerGlobalMeanPolarized_sqrt_memSchattenClass_one :
    MemSchattenClass 1
      (CFC.sqrt gammaSewnCriticalPhysicalPluckerGlobalMeanPolarizedOperator) := by
  apply DeningerIsNuclear.memSchattenClass_one
  apply deningerIsNuclear_of_summable_norm_apply_lp_single
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    norm_gammaSewnCriticalPhysicalPluckerGlobalMeanPolarized_sqrt_apply_le
    (summable_gammaSewnCriticalPluckerRootDiagonalBudget.mul_left (Real.sqrt 3))

end RHTower.HedenmalmThetaSource
