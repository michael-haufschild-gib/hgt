import GaloisForLFunctions.RHTower.SoninRegularizedMomentWeldNoGo
import GaloisForLFunctions.RHTower.TraceClassCyclicity
import GaloisForLFunctions.RHTower.SoninCoupledPrimeArchGramTransfer

/-!
# No fixed-aperture exact moment weld for the coupled regularized source

The rectangular common-source column retains all mixed prime words. Its exact Gram spectrum
still violates the Xi prefix-growth requirement. Projective and escaping-aperture variants
are not excluded by this theorem.
-/

open Filter Topology ContinuousLinearMap
open scoped BigOperators
namespace RHTower
noncomputable section

theorem summable_rectApproxNumber_sq_of_isHilbertSchmidt
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {A : E →L[ℂ] F} (hA : A.IsHilbertSchmidt) :
    Summable (fun n => rectApproxNumber A n ^ 2) := by
  have hAl : (rectangularLowerBlock A).IsHilbertSchmidt := (hA.comp_right _).comp_left _
  have hsum := (memSchattenClass_two_iff_isHilbertSchmidt _).mpr hAl
  simpa only [MemSchattenClass, Real.rpow_two,
    ← rectApproxNumber_eq_approxNumber_lowerBlock] using hsum

theorem opTrace_rectangularGram_pow_eq_rectApproxNumber_moments
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {A : E →L[ℂ] F} (hA : A.IsHilbertSchmidt) (r : ℕ) :
    opTrace ((A.adjoint ∘L A) ^ (r + 1)) =
      ∑' n : ℕ, (((rectApproxNumber A n ^ 2 : ℝ) : ℂ) ^ (r + 1)) := by
  let S := A.adjoint ∘L A
  have hpos : S.IsPositive := isPositive_adjoint_comp_self A
  have hS1 : MemSchattenClass 1 S := by
    have hs := summable_rectApproxNumber_sq_of_isHilbertSchmidt hA
    apply hs.congr
    intro n
    simp only [Real.rpow_one]
    exact rectApproxNumber_sq_eq_approxNumber_adjoint_comp_self A hA.isCompactOperator n
  obtain ⟨B, C, hB, hC, hfac⟩ := hS1.one_isTraceClass
  have hsplit : S ^ (r + 1) = B ∘L (C ∘L S ^ r) := by
    rw [pow_succ', hfac]
    rfl
  rw [opTrace_pow_eq_tsum_sgVal_pow (hS1.isCompactOperator one_pos)
    hpos.isSymmetric (Nat.succ_pos r) hB (hC.comp_right _) hsplit]
  apply tsum_congr
  intro n
  have hs : sgVal S n = rectApproxNumber A n ^ 2 := by
    rw [rectApproxNumber_sq_eq_approxNumber_adjoint_comp_self A hA.isCompactOperator,
      approxNumber_eq_singVal (hS1.isCompactOperator one_pos),
      ← abs_sgVal_eq_singVal (hS1.isCompactOperator one_pos) hpos.isSymmetric,
      abs_of_nonneg (sgVal_nonneg_of_isPositive hpos n)]
  rw [hs]

theorem soninAllPrimeColumnCoordinateOperator_eq_column_comp_synthesis
    (a : ℝ) (ha : 0 < a) :
    soninAllPrimeColumnCoordinateOperator a ha = soninAllPrimeColumnOperator a ha ∘L
      (hsBasis ℂ SoninL2).repr.symm.toContinuousLinearEquiv.toContinuousLinearMap := by
  ext x
  simp [soninAllPrimeColumnOperator]

theorem rectApproxNumber_soninColumnCoordinate_le_column
    (a : ℝ) (ha : 0 < a) (n : ℕ) :
    rectApproxNumber (soninAllPrimeColumnCoordinateOperator a ha) n ≤
      rectApproxNumber (soninAllPrimeColumnOperator a ha) n := by
  rw [soninAllPrimeColumnCoordinateOperator_eq_column_comp_synthesis]
  have hn : ‖(hsBasis ℂ SoninL2).repr.symm.toContinuousLinearEquiv.toContinuousLinearMap‖ ≤ 1 :=
    (hsBasis ℂ SoninL2).repr.symm.toLinearIsometry.norm_toContinuousLinearMap_le
  exact (rectApproxNumber_comp_le_right _ _ n).trans
    ((mul_le_mul_of_nonneg_left hn (rectApproxNumber_nonneg _ n)).trans_eq (mul_one _))

/-- The literal common-source assembly is also excluded at every fixed positive aperture;
retaining mixed prime words does not evade the coefficient-faithful spectral budget. -/
theorem not_soninAllPrimeCoupled_exact_positive_aperture_moments
    (a : SoninPositiveAperture) :
    ¬ (∀ r : ℕ, soninAllPrimeCoupledTraceMoment a r = (normalizedPrimeArchMoment r : ℂ)) := by
  intro hm
  have hRH : RiemannHypothesis := by
    apply riemannHypothesis_of_soninCoupledPrimeArchFiniteMomentCoupling
      (aperture := fun _ _ => a)
    intro N k hk
    simpa only [hm k] using tendsto_const_nhds
  let A := soninAllPrimeColumnCoordinateOperator a.1 a.2
  have hA : A.IsHilbertSchmidt :=
    HilbertSchmidt.isHilbertSchmidt_toOperatorRect (soninAllPrimeColumnKernel_isHSRect a.1 a.2)
  have hBsq : Summable (fun n => approxNumber xiOrderedSignedPrimeOperator n ^ 2) := by
    simpa [MemSchattenClass, Real.rpow_two] using xiOrderedSignedPrimeOperator_memSchattenClass_two
  have heq : rectApproxNumber A = approxNumber xiOrderedSignedPrimeOperator := by
    apply nonneg_sequence_eq_of_summable_square_moments
      (summable_rectApproxNumber_sq_of_isHilbertSchmidt hA) hBsq
      (rectApproxNumber_nonneg _) (approxNumber_nonneg _)
      (rectApproxNumber_antitone _) (approxNumber_antitone _)
    intro r
    rw [← opTrace_rectangularGram_pow_eq_rectApproxNumber_moments hA,
      ← normalizedPrimeArchMoment_eq_orderedXi_approxNumber_moments_of_rh hRH]
    exact hm r
  have hzero : Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, approxNumber xiOrderedSignedPrimeOperator n) /
        Real.log ((N : ℝ) + 1) ^ 2) atTop (nhds 0) := by
    apply squeeze_zero' _ _ (tendsto_rectApproxPrefix_soninAllPrimeColumn_div_logSq a.1 a.2)
    · exact Eventually.of_forall fun N => div_nonneg
        (Finset.sum_nonneg fun n _ => approxNumber_nonneg _ n) (sq_nonneg _)
    · apply Eventually.of_forall
      intro N
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      apply Finset.sum_le_sum
      intro n hn
      rw [← heq]
      exact rectApproxNumber_soninColumnCoordinate_le_column a.1 a.2 n
  have hbad := tendsto_nhds_unique hzero
    tendsto_xiOrderedSignedPrimeOperator_approxNumber_partialSum_div_logSq
  exact (show (0 : ℝ) < 1 / (2 * Real.pi) by positivity).ne hbad

end
end RHTower
