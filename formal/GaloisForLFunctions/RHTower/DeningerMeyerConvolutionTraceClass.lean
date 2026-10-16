import GaloisForLFunctions.RHTower.DeningerMeyerHilbertConvolutionJets
import GaloisForLFunctions.RHTower.DeningerMeyerFlowLefschetz

/-! # Trace-class realization of the entire original convolution algebra

The source generator identity factors every convolution through two copies
of the actual Hasse resolvent. This retains all Jordan coefficients and
admits arbitrary original sources, including noncompact whole-line data.
-/

noncomputable section
open Complex MeasureTheory ContinuousLinearMap
open GaloisForLFunctions.HTGeometry
open scoped InnerProductSpace

namespace RHTower

def deningerMeyerCenteredSource (g : DeningerMeyerStrongLogTarget) :
    DeningerMeyerStrongLogTarget :=
  (-I) • (deningerMeyerStrongLogGenerator g - (1/2 : ℂ) • g)

theorem deningerMeyerCenteredSource_mellin (g : DeningerMeyerStrongLogTarget) (s : ℂ) :
    deningerMeyerStrongLogMellin (deningerMeyerCenteredSource g) s =
      (-I)*(s-1/2)*deningerMeyerStrongLogMellin g s := by
  change (deningerMeyerStrongLogMellinLM s)
    ((-I) • (deningerMeyerStrongLogGenerator g - (1/2 : ℂ) • g)) = _
  rw [map_smul, map_sub, map_smul]
  change (-I)*(deningerMeyerStrongLogMellin (deningerMeyerStrongLogGenerator g) s -
    (1/2)*deningerMeyerStrongLogMellin g s) = _
  rw [deningerMeyerStrongLogGenerator_mellin]
  ring

theorem deningerMeyerCenteredSource_mk (g : DeningerMeyerStrongLogTarget) :
    (Submodule.Quotient.mk (deningerMeyerCenteredSource g) : DeningerMeyerStrongLogCohomology) =
      deningerMeyerCenteredGenerator (Submodule.Quotient.mk g) := by
  simp only [deningerMeyerCenteredSource, deningerMeyerCenteredGenerator,
    LinearMap.smul_apply, deningerMeyerCohomologyShift_apply,
    deningerMeyerCohomologyGenerator_mk, Submodule.Quotient.mk_sub,
    Submodule.Quotient.mk_smul]

theorem deningerMeyerCenteredSource_convolution (g h : DeningerMeyerStrongLogTarget) :
    deningerMeyerSourceConvolution (deningerMeyerCenteredSource g) h =
      deningerMeyerCenteredSource (deningerMeyerSourceConvolution g h) := by
  apply deningerMeyerStrongLogMellin_injective
  funext s
  simp only [deningerMeyerSourceConvolution_mellin, deningerMeyerCenteredSource_mellin]
  ring

theorem deningerMeyerCenteredSource_cohomology (g : DeningerMeyerStrongLogTarget)
    (u : DeningerMeyerStrongLogCohomology) :
    deningerMeyerCohomologyConvolution (Submodule.Quotient.mk (deningerMeyerCenteredSource g)) u =
      deningerMeyerCenteredGenerator
        (deningerMeyerCohomologyConvolution (Submodule.Quotient.mk g) u) := by
  induction u using Submodule.Quotient.induction_on with
  | H h =>
    rw [deningerMeyerCohomologyConvolution_mk, deningerMeyerCohomologyConvolution_mk,
      deningerMeyerCenteredSource_convolution, deningerMeyerCenteredSource_mk]

theorem deningerMeyerHilbertConvolution_resolvent (g : DeningerMeyerStrongLogTarget) :
    deningerMeyerHilbertConvolution g = deningerMeyerHasseResolvent.comp
      (deningerMeyerHilbertConvolution (deningerMeyerCenteredSource g)) := by
  apply deningerHasseCLM_ext_source
  intro u
  rw [comp_apply, deningerMeyerHilbertConvolution_source, deningerMeyerHilbertConvolution_source,
    deningerMeyerCenteredSource_cohomology, deningerMeyerHasseResolvent_source_left]

/-- Every original source supplies two genuine Hilbert--Schmidt factors. -/
theorem deningerMeyerHilbertConvolution_factorization (g : DeningerMeyerStrongLogTarget) :
    deningerMeyerHilbertConvolution g = deningerMeyerHasseResolvent.comp
      (deningerMeyerHasseResolvent.comp (deningerMeyerHilbertConvolution
        (deningerMeyerCenteredSource (deningerMeyerCenteredSource g)))) := by
  rw [deningerMeyerHilbertConvolution_resolvent g,
    deningerMeyerHilbertConvolution_resolvent (deningerMeyerCenteredSource g)]

theorem deningerMeyerHilbertConvolution_mem_hsTraceIdeal (g : DeningerMeyerStrongLogTarget) :
    deningerMeyerHilbertConvolution g ∈ hsTraceIdeal DeningerArithmeticJetHilbert := by
  rw [deningerMeyerHilbertConvolution_factorization]
  exact comp_mem_hsTraceIdeal deningerMeyerHasseResolvent_isHilbertSchmidt
    (deningerMeyerHasseResolvent_isHilbertSchmidt.comp_right _)

theorem deningerMeyerHilbertConvolution_memSchattenClass_one (g : DeningerMeyerStrongLogTarget) :
    MemSchattenClass 1 (deningerMeyerHilbertConvolution g) := by
  rw [deningerMeyerHilbertConvolution_factorization]
  exact memSchattenClass_one_comp deningerMeyerHasseResolvent_isHilbertSchmidt
    (deningerMeyerHasseResolvent_isHilbertSchmidt.comp_right _)

theorem deningerMeyerHilbertConvolution_isCompact (g : DeningerMeyerStrongLogTarget) :
    IsCompactOperator (deningerMeyerHilbertConvolution g) :=
  (deningerMeyerHilbertConvolution_memSchattenClass_one g).isCompactOperator (by norm_num)

theorem deningerMeyerHilbertConvolution_basis_diagonal (g : DeningerMeyerStrongLogTarget)
    (q : DeningerArithmeticJetCoordinate) :
    ⟪xiDivisorHilbertBasis q, deningerMeyerHilbertConvolution g (xiDivisorHilbertBasis q)⟫_ℂ =
      deningerMeyerStrongLogMellin g (q.1 : ℂ) := by
  classical
  rw [xiDivisorHilbertBasis_apply, lp.inner_single_left]
  simp only [RCLike.inner_apply, map_one, mul_one]
  rw [← xiDivisorHilbertBasis_apply, deningerMeyerHilbertConvolution_coordinate]
  simp only [deningerMeyerHilbertFlow_basis_diagonal]
  apply integral_congr_ae
  filter_upwards with t
  simp only [deningerMeyerStrongLogMellinJet, pow_zero, one_mul]
  rw [mul_comm (t : ℂ) (q.1 : ℂ), mul_comm]

/-- The ordinary trace keeps every multiplicity copy, on the full original source domain. -/
theorem deningerMeyerHilbertConvolution_opTrace (g : DeningerMeyerStrongLogTarget) :
    opTrace (deningerMeyerHilbertConvolution g) =
      ∑' q : XiZeroCopy, deningerMeyerStrongLogMellin g (q.1 : ℂ) := by
  rw [opTrace_eq_tsum_basis_of_mem (deningerMeyerHilbertConvolution_mem_hsTraceIdeal g)
    xiDivisorHilbertBasis]
  exact tsum_congr (deningerMeyerHilbertConvolution_basis_diagonal g)

theorem deningerMeyerHilbertConvolution_summable_diagonal (g : DeningerMeyerStrongLogTarget) :
    Summable (fun q : XiZeroCopy => deningerMeyerStrongLogMellin g (q.1 : ℂ)) := by
  have h := summable_diag_basis_of_mem (deningerMeyerHilbertConvolution_mem_hsTraceIdeal g)
    xiDivisorHilbertBasis
  exact h.congr (deningerMeyerHilbertConvolution_basis_diagonal g)

end RHTower
