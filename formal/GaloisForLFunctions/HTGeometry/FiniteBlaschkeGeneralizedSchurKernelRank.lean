import GaloisForLFunctions.HTGeometry.ProjectedAdjointDefectRank
import GaloisForLFunctions.HTGeometry.FiniteBlaschkeGeneralizedSchurKernel

/-!
# Generalized-Schur kernel index with common-factor rank loss

The literal finite Gram kernel realizes the exact adjoint rank from
`ProjectedAdjointDefectRank`.  No coprimality or pointwise nonvanishing condition is imposed.
-/

open Complex
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open RHTower

/-- Exact negative-square count of a finite generalized-Schur kernel without coprimality: the
count is the rank of the numerator adjoint restricted to the denominator model space. -/
theorem finiteBlaschkeGeneralizedSchurKernel_exactNegativeSquares_rank
    (F : DiskMultiplier) (B : FiniteBlaschke) (hF : F.bd ≤ 1) :
    let n := Module.finrank ℂ (LinearMap.range
      ((ContinuousLinearMap.adjoint (hardyMul F)).toLinearMap.domRestrict
        (finiteBlaschkeModelSpace B)))
    (finiteBlaschkeGeneralizedSchurRealization F B).HasFiniteGramNegativeDimensionOn
        (Metric.ball 0 1) n ∧
      ∀ r : ℕ,
        (finiteBlaschkeGeneralizedSchurRealization F B).HasFiniteGramNegativeDimensionOn
          (Metric.ball 0 1) r → r ≤ n := by
  dsimp only
  let R := finiteBlaschkeGeneralizedSchurRealization F B
  let K := finiteBlaschkeModelSpace B
  let A : K →ₗ[ℂ] HardyDisk :=
    (ContinuousLinearMap.adjoint (hardyMul F)).toLinearMap.domRestrict K
  let n := Module.finrank ℂ (LinearMap.range A)
  obtain ⟨L, hcompl⟩ := (LinearMap.ker A).exists_isCompl
  have hfinrankL : Module.finrank ℂ L = n := by
    have hcompdim := Submodule.finrank_add_eq_of_isCompl hcompl
    have hranknull := LinearMap.finrank_range_add_finrank_ker A
    omega
  constructor
  · let b := Module.finBasis ℂ L
    let v : Fin n → HardyDisk := fun i =>
      ((b (Fin.cast hfinrankL.symm i) : L) : K)
    have hvneg : R.IsNegativeTuple v := by
      intro c hc
      let y : L := ∑ i, c i • b (Fin.cast hfinrankL.symm i)
      have hy0 : y ≠ 0 := by
        intro hzero
        have hLI : LinearIndependent ℂ (fun i : Fin n =>
            b (Fin.cast hfinrankL.symm i)) := by
          exact b.linearIndependent.comp _ (Fin.cast_injective hfinrankL.symm)
        have hall := Fintype.linearIndependent_iff.mp hLI c hzero
        have hc0 : c = 0 := funext hall
        rw [hc0, norm_zero] at hc
        norm_num at hc
      have hAy : A (y : K) ≠ 0 := by
        intro hzero
        have hyker : (y : K) ∈ LinearMap.ker A := hzero
        have hyL : (y : K) ∈ L := y.property
        have hybot : (y : K) ∈ (⊥ : Submodule ℂ K) := by
          rw [← hcompl.inf_eq_bot]
          exact ⟨hyker, hyL⟩
        exact hy0 (Subtype.ext hybot)
      have hyK : ((y : K) : HardyDisk) ∈ K := (y : K).property
      have hstar : K.starProjection ((y : K) : HardyDisk) = (y : K) :=
        Submodule.starProjection_eq_self_iff.mpr hyK
      have hq : finiteBlaschkeGeneralizedSchurForm F B ((y : K) : HardyDisk) < 0 := by
        rw [finiteBlaschkeGeneralizedSchurForm, projectedAdjointDefectForm, hstar]
        change ‖((y : K) : HardyDisk)‖ ^ (2 : ℕ) - ‖A (y : K)‖ ^ (2 : ℕ) -
          ‖((y : K) : HardyDisk)‖ ^ (2 : ℕ) < 0
        nlinarith [norm_pos_iff.mpr hAy]
      change (inner ℂ
        (RHTower.AnalyticHermitianKernelRealization.sectionSynthesis v c)
        (finiteBlaschkeGeneralizedSchurOperator F B
          (RHTower.AnalyticHermitianKernelRealization.sectionSynthesis v c))).re < 0
      rw [finiteBlaschkeGeneralizedSchurOperator_quadratic]
      have hsynth :
          RHTower.AnalyticHermitianKernelRealization.sectionSynthesis v c =
            ((y : K) : HardyDisk) := by
        have hydef :
            (∑ i, c i • b (Fin.cast hfinrankL.symm i) : L) = y := rfl
        simpa only [RHTower.AnalyticHermitianKernelRealization.sectionSynthesis, v,
          Submodule.coe_sum, Submodule.coe_smul] using
          congrArg (fun t : L => ((t : K) : HardyDisk)) hydef
      rw [hsynth]
      exact hq
    have hglobal : R.HasNegativeDimensionOn (Metric.ball 0 1) n := by
      refine ⟨v, ?_, hvneg⟩
      intro i
      change v i ∈ (Submodule.span ℂ (R.kernelSection '' R.domain)).topologicalClosure
      rw [R.global_total]
      trivial
    rw [R.hasFiniteGramNegativeDimensionOn_iff,
      R.hasFiniteSectionNegativeDimensionOn_iff]
    exact hglobal
  · intro r hgram
    have hsection := (R.hasFiniteGramNegativeDimensionOn_iff (Metric.ball 0 1) r).mp hgram
    obtain ⟨v, _, hvneg⟩ := hsection
    have hvLI : LinearIndependent ℂ v := R.isNegativeTuple_linearIndependent hvneg
    let W : Submodule ℂ HardyDisk := LinearMap.range (finiteTupleSynthesisLinear v)
    have hWrank : Module.finrank ℂ W = r :=
      finrank_range_finiteTupleSynthesisLinear hvLI
    have hWneg : ∀ x ∈ W, x ≠ 0 →
        finiteBlaschkeGeneralizedSchurForm F B x < 0 := by
      intro x hx hx0
      obtain ⟨c, rfl⟩ := hx
      have hc0 : c ≠ 0 := by
        intro hc
        apply hx0
        rw [hc, map_zero]
      have hq := R.isNegativeTuple_quadratic_neg hvneg hc0
      change (inner ℂ
        (RHTower.AnalyticHermitianKernelRealization.sectionSynthesis v c)
        (finiteBlaschkeGeneralizedSchurOperator F B
          (RHTower.AnalyticHermitianKernelRealization.sectionSynthesis v c))).re < 0 at hq
      rw [finiteBlaschkeGeneralizedSchurOperator_quadratic] at hq
      simpa only [finiteTupleSynthesisLinear_apply] using hq
    have hexact := finiteBlaschkeGeneralizedSchurForm_hasExactNegativeIndex_rank F B hF
    rw [← hWrank]
    exact hexact.2 W hWneg

end GaloisForLFunctions.HTGeometry
