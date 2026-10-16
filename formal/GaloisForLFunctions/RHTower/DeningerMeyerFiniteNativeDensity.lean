import GaloisForLFunctions.RHTower.DeningerMeyerXiContourGerms
import GaloisForLFunctions.RHTower.PaperThetaConvolutionFredholm
import GaloisForLFunctions.RHTower.XiOrdinateBandCopies

/-! # Finite native modes are dense in the original Meyer cohomology

Entire divided-difference contour blocks, good Xi heights and Gaussian source
removal close the original-topology approximation obstacle. Every approximant
is in an actual finite native range, with all zero multiplicities retained.
The conclusion concerns original source cohomology; it does not assert
convergence of arbitrary native BV amplitudes.
-/

open Complex Set Filter Topology

namespace RHTower
noncomputable section
open scoped DeningerMeyerNaturalTopology
open PaperThetaEndpoint

def deningerMeyerFiniteNativeModes : Set DeningerMeyerStrongLogCohomology :=
  {u | ∃ S : Finset XiDivisorSupport, u ∈ LinearMap.range (meyerFiniteHedenmalmSynthesis S)}

namespace DeningerMeyerXiContourSchedule

variable (S : DeningerMeyerXiContourSchedule)

theorem xiBlockSource_jet (F : ℂ → ℂ) (hF : Differentiable ℂ F)
    (n j : ℕ) (rho : ℂ) :
    deningerMeyerStrongLogMellinJetCLM j rho (S.xiBlockSource F hF n) =
      iteratedDeriv j (S.xiBlock F n) rho := by
  rw [deningerMeyerStrongLogMellinJetCLM_apply,
    deningerMeyerStrongLogMellinJetLM_eq_iteratedDeriv,
    show deningerMeyerStrongLogMellin (S.xiBlockSource F hF n) = S.xiBlock F n from
      funext (S.xiBlockSource_mellin F hF n)]

/-- The source-convergent block sum has precisely the original Gaussian class. -/
theorem gaussian_sum_class (g : DeningerMeyerStrongLogTarget) {ε : ℝ} (hε : 0 < ε) :
    (Submodule.Quotient.mk (∑' n, S.xiBlockSource
      (deningerGaussianMellinRegularization ε (deningerMeyerStrongLogMellin g))
      (deningerMeyerStrongLogMellin_gaussianRegular g hε).differentiable n) :
      DeningerMeyerStrongLogCohomology) =
    Submodule.Quotient.mk (deningerMeyerInverseMellinSource
      (deningerGaussianMellinRegularization ε (deningerMeyerStrongLogMellin g))
      (deningerMeyerStrongLogMellin_gaussianRegular g hε)) := by
  let F := deningerGaussianMellinRegularization ε (deningerMeyerStrongLogMellin g)
  have hreg := deningerMeyerStrongLogMellin_gaussianRegular g hε
  have hs := S.gaussian_xiBlockSource_summable g hε
  apply deningerMeyerCohomology_eq_of_XiJets_eq
  intro rho j
  simp only [deningerMeyerXiSupportJetEvaluationLM_mk]
  obtain ⟨b, hb, hsel⟩ := S.exists_xiBlockWindow rho
  have hinput : deningerMeyerStrongLogMellinJetLM j (rho : ℂ)
      (deningerMeyerInverseMellinSource F hreg) = iteratedDeriv j F (rho : ℂ) := by
    rw [deningerMeyerStrongLogMellinJetLM_eq_iteratedDeriv,
      show deningerMeyerStrongLogMellin (deningerMeyerInverseMellinSource F hreg) = F from
        funext (deningerMeyerInverseMellinSource_mellin hreg)]
  rw [hinput, ← deningerMeyerStrongLogMellinJetCLM_apply,
    (deningerMeyerStrongLogMellinJetCLM j (rho : ℂ)).map_tsum hs]
  rw [tsum_eq_single b]
  · rw [S.xiBlockSource_jet, S.xiBlock_jet hreg.differentiable, if_pos hb]
  · intro i hib
    rw [S.xiBlockSource_jet, S.xiBlock_jet hreg.differentiable,
      if_neg (fun hw => hib ((hsel i).mp hw))]

/-- Every finite head belongs to the actual native range of a finite full divisor. -/
theorem finite_head_native (F : ℂ → ℂ) (hF : Differentiable ℂ F) (N : ℕ) :
    (Submodule.Quotient.mk (∑ i ∈ Finset.range N, S.xiBlockSource F hF i) :
      DeningerMeyerStrongLogCohomology) ∈ deningerMeyerFiniteNativeModes := by
  classical
  let W := (xiSupportsUpTo_finite (S.height N)).toFinset
  refine ⟨W, (mem_meyerFiniteHedenmalmRange_iff W _).mpr ?_⟩
  intro rho hrho j
  have hout : S.height N < |(rho : ℂ).im| := by
    apply lt_of_not_ge
    intro h
    exact hrho (by simpa [W] using h)
  change ((deningerMeyerXiSupportJetEvaluationLM rho j).comp
    (LinearMap.range deningerMeyerStrongLogSumLM).mkQ)
      (∑ i ∈ Finset.range N, S.xiBlockSource F hF i) = 0
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  change deningerMeyerStrongLogMellinJetLM j (rho : ℂ) (S.xiBlockSource F hF i) = 0
  rw [← deningerMeyerStrongLogMellinJetCLM_apply, S.xiBlockSource_jet,
    S.xiBlock_jet hF]
  apply if_neg
  intro hwin
  have hiN := S.height_strictMono.monotone (Nat.le_of_lt (Finset.mem_range.mp hi))
  have hw := S.xiBlockWindow_upper hwin
  linarith

include S in
theorem gaussian_class_mem_closure (g : DeningerMeyerStrongLogTarget)
    {ε : ℝ} (hε : 0 < ε) :
    (Submodule.Quotient.mk (deningerMeyerInverseMellinSource
      (deningerGaussianMellinRegularization ε (deningerMeyerStrongLogMellin g))
      (deningerMeyerStrongLogMellin_gaussianRegular g hε)) :
      DeningerMeyerStrongLogCohomology) ∈ closure deningerMeyerFiniteNativeModes := by
  have hq : Continuous (fun x : DeningerMeyerStrongLogTarget =>
      (Submodule.Quotient.mk x : DeningerMeyerStrongLogCohomology)) := continuous_quot_mk
  have hlim := (hq.tendsto _).comp (S.gaussian_xiBlockSource_summable g hε).hasSum.tendsto_sum_nat
  have h := mem_closure_of_tendsto hlim (Eventually.of_forall (fun N =>
    S.finite_head_native _ (deningerMeyerStrongLogMellin_gaussianRegular g hε).differentiable N))
  rw [S.gaussian_sum_class g hε] at h
  exact h

end DeningerMeyerXiContourSchedule

/-- **Original-topology native density.** Actual finite native full-Xi modes
are dense in the literal Meyer quotient, unconditionally. -/
theorem deningerMeyerFiniteNativeModes_dense : Dense deningerMeyerFiniteNativeModes := by
  intro u
  obtain ⟨g, rfl⟩ := (LinearMap.range deningerMeyerStrongLogSumLM).mkQ_surjective u
  have hq : Continuous (fun x : DeningerMeyerStrongLogTarget =>
      (Submodule.Quotient.mk x : DeningerMeyerStrongLogCohomology)) := continuous_quot_mk
  apply isClosed_closure.mem_of_tendsto ((hq.tendsto g).comp (deningerMeyerGaussianSource_tendsto g))
  apply Eventually.of_forall
  intro m
  have h := deningerMeyerXiContourSchedule.gaussian_class_mem_closure g
    (ε := 1/((m : ℝ)+1)) (by positivity)
  exact h

/-- Every original forcing and its repaired convolution solution are limits
of exact solutions in actual finite native ranges, in the original topology. -/
theorem deningerMeyerOriginalConvolution_nativeApproximation
    (g : DeningerMeyerStrongLogTarget) (f : DeningerMeyerStrongLogCohomology) :
    ∃ (S : ℕ → Finset XiDivisorSupport)
      (fₙ uₙ : ℕ → DeningerMeyerStrongLogCohomology),
      (∀ n, fₙ n ∈ LinearMap.range (meyerFiniteHedenmalmSynthesis (S n)) ∧
        uₙ n ∈ LinearMap.range (meyerFiniteHedenmalmSynthesis (S n)) ∧
        deningerMeyerOriginalConvolutionRepair g (uₙ n) = fₙ n) ∧
      Tendsto fₙ atTop (𝓝 f) ∧
      Tendsto uₙ atTop (𝓝 (deningerMeyerOriginalConvolutionInverse g f)) := by
  classical
  obtain ⟨fₙ, hmem, hlim⟩ := mem_closure_iff_seq_limit.mp (deningerMeyerFiniteNativeModes_dense f)
  change ∀ n, ∃ S : Finset XiDivisorSupport,
    fₙ n ∈ LinearMap.range (meyerFiniteHedenmalmSynthesis S) at hmem
  choose S hS using hmem
  refine ⟨S, fₙ, (fun n => deningerMeyerOriginalConvolutionInverse g (fₙ n)), ?_, hlim, ?_⟩
  · intro n
    exact ⟨hS n, meyerFiniteConvolutionInverse_mem (S n) g ⟨fₙ n, hS n⟩,
      deningerMeyerOriginalConvolutionInverse_right g (fₙ n)⟩
  · exact ((deningerMeyerOriginalConvolutionInverse_continuous g).tendsto f).comp hlim

end
end RHTower
