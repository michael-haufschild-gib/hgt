import GaloisForLFunctions.RHTower.Suzuki.SuzukiAffineMixtureTriangularCurvatureReduction
import GaloisForLFunctions.RHTower.Suzuki.SuzukiScrewFunctionCriterion
import GaloisForLFunctions.HTGeometry.SummableSpectrumScrewRecurrence

/-!
# RH classification of the signed Suzuki triangular-curvature transform

Under RH, Suzuki's literal source is a nonnegative screw series with summable reciprocal-square
Xi-zero weights.  Its relation hull therefore gives a uniform source bound.  The positive FU
rectangular measure has uniformly bounded mass, so this bound passes to the positive mixture and,
through the exact checkpoint reductions, to the signed third-grade triangular-curvature transform.

The converse was already supplied by the CCM--FU reduction.  Thus the remaining signed triangular
high-pass is exactly equivalent to RH; it is not an independent producer for CCM--FU.
-/

open Complex MeasureTheory Set
open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry
open HTGeometry

namespace RHTower

noncomputable section

/-- Uniform boundedness of Suzuki's literal source on the full real line. -/
def SuzukiPsiUniformBound : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |suzukiPsi t| ≤ C

/-- RH bounds the literal prime--Lerch Suzuki source by the maximal energy of its critical-zero
relation hull.  This is the formal RH-to-bounded-source direction of Suzuki's boundedness law. -/
theorem suzukiPsiUniformBound_of_riemannHypothesis
    (hRH : RiemannHypothesis) : SuzukiPsiUniformBound := by
  let M : ℝ := screwHullMax xiCriticalScrewWeight xiRealSpectralPoint
  refine ⟨M, ?_, ?_⟩
  · dsimp only [M]
    exact screwHullMax_nonneg xiCriticalScrewWeight_nonneg
      (summable_xiCriticalScrewWeight_of_rh hRH)
  · intro t
    rw [suzukiPsi_eq_xiCriticalScrewSeries_of_rh hRH]
    have hnonneg : 0 ≤ xiCriticalScrewSeries t := by
      exact screwSeries_nonneg xiCriticalScrewWeight_nonneg t
    rw [abs_of_nonneg hnonneg]
    dsimp only [xiCriticalScrewSeries, M]
    exact screwSeries_le_screwHullMax xiCriticalScrewWeight_nonneg
      (summable_xiCriticalScrewWeight_of_rh hRH) t

/-- At every positive lower wall, RH uniformly bounds the full marked positive FU mixture.  The
bound is the screw-hull maximum times the exact mass budget `96 / b^(4 : ℕ)`. -/
theorem ccmFUCentralXiScrewPositiveMixtureBound_of_riemannHypothesis
    {b : ℝ} (hb : 0 < b) (hRH : RiemannHypothesis) :
    GaloisForLFunctions.RHTower.CCMFUCentralXiScrewPositiveMixtureBound b := by
  obtain ⟨M, hM0, hM⟩ := suzukiPsiUniformBound_of_riemannHypothesis hRH
  refine ⟨(96 / b ^ (4 : ℕ)) * M, mul_nonneg (by positivity) hM0, ?_⟩
  intro H hbH
  have hbHle : b ≤ H := hbH.le
  have hH0 : 0 < H := hb.trans hbH
  let ρ : ℝ → ℝ :=
    GaloisForLFunctions.RHTower.ccmThirdGradeCesaroRectangularMixDensity H
  have hρcont : ContinuousOn ρ (Set.Icc b H) := by
    intro t ht
    have ht0 : t ≠ 0 := (hb.trans_le ht.1).ne'
    unfold ρ GaloisForLFunctions.RHTower.ccmThirdGradeCesaroRectangularMixDensity
    exact ((continuousAt_const.mul (continuousAt_const.sub continuousAt_id)).div
      (continuousAt_const.mul (continuousAt_id.pow 5))
      (mul_ne_zero hH0.ne' (pow_ne_zero 5 ht0))).continuousWithinAt
  have hρint : IntervalIntegrable ρ volume b H := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hbHle]
    exact hρcont
  have hρψint : IntervalIntegrable (fun t => ρ t * suzukiPsi t) volume b H := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hbHle]
    exact hρcont.mul continuous_suzukiPsi.continuousOn
  have hρMint : IntervalIntegrable (fun t => ρ t * M) volume b H :=
    hρint.mul_const M
  have hψnonneg := suzukiPsiPointwiseNonnegative_of_riemannHypothesis hRH
  have hbulk0 : 0 ≤ ∫ t in b..H, ρ t * suzukiPsi t := by
    apply intervalIntegral.integral_nonneg hbHle
    intro t ht
    exact mul_nonneg
      (GaloisForLFunctions.RHTower.ccmThirdGradeCesaroRectangularMixDensity_nonneg hH0
        (hb.trans_le ht.1) ht.2)
      (hψnonneg t (hb.le.trans ht.1))
  have hbulkLe : (∫ t in b..H, ρ t * suzukiPsi t) ≤
      M * ∫ t in b..H, ρ t := by
    calc
      (∫ t in b..H, ρ t * suzukiPsi t) ≤
          ∫ t in b..H, ρ t * M := by
            apply intervalIntegral.integral_mono_on hbHle hρψint hρMint
            intro t ht
            apply mul_le_mul_of_nonneg_left
              ((le_abs_self (suzukiPsi t)).trans (hM t))
            exact GaloisForLFunctions.RHTower.ccmThirdGradeCesaroRectangularMixDensity_nonneg hH0
              (hb.trans_le ht.1) ht.2
      _ = M * ∫ t in b..H, ρ t := by
        rw [intervalIntegral.integral_mul_const]
        ring
  have hcoeff0 : 0 ≤ 32 / H ^ (4 : ℕ) := by positivity
  have hendpoint0 : 0 ≤ (32 / H ^ (4 : ℕ)) * suzukiPsi H :=
    mul_nonneg hcoeff0 (hψnonneg H hH0.le)
  have hendpointLe : (32 / H ^ (4 : ℕ)) * suzukiPsi H ≤
      (32 / H ^ (4 : ℕ)) * M :=
    mul_le_mul_of_nonneg_left ((le_abs_self (suzukiPsi H)).trans (hM H)) hcoeff0
  have hmass := GaloisForLFunctions.RHTower.rectangularMixDensity_totalMass_le
    (b := b) (H := H) hb hbHle
  have hmixture0 : 0 ≤
      GaloisForLFunctions.RHTower.ccmFUCentralXiScrewPositiveMixture b H := by
    unfold GaloisForLFunctions.RHTower.ccmFUCentralXiScrewPositiveMixture
    exact add_nonneg hbulk0 hendpoint0
  rw [abs_of_nonneg hmixture0]
  unfold GaloisForLFunctions.RHTower.ccmFUCentralXiScrewPositiveMixture
  change (∫ t in b..H, ρ t * suzukiPsi t) +
      (32 / H ^ (4 : ℕ)) * suzukiPsi H ≤ (96 / b ^ (4 : ℕ)) * M
  calc
    (∫ t in b..H, ρ t * suzukiPsi t) +
        (32 / H ^ (4 : ℕ)) * suzukiPsi H ≤
      M * (∫ t in b..H, ρ t) + (32 / H ^ (4 : ℕ)) * M :=
        add_le_add hbulkLe hendpointLe
    _ = M * ((∫ t in b..H, ρ t) + 32 / H ^ (4 : ℕ)) := by ring
    _ ≤ M * (96 / b ^ (4 : ℕ)) := by
      exact mul_le_mul_of_nonneg_left hmass hM0
    _ = (96 / b ^ (4 : ℕ)) * M := by ring

/-- RH supplies the formerly open signed triangular-curvature bound.  The passage uses no
weighted-first-moment estimate: that stronger shortcut is known to fail under RH. -/
theorem ccmFUSuzukiTriangularCurvatureTransformBound_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    CCMFUSuzukiTriangularCurvatureTransformBound := by
  have hpositive :
      GaloisForLFunctions.RHTower.CCMFUCentralXiScrewPositiveMixtureBound 1 :=
    ccmFUCentralXiScrewPositiveMixtureBound_of_riemannHypothesis zero_lt_one hRH
  have hlog2 : Real.log 2 ≤ (1 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hcheckpoint :
      GaloisForLFunctions.RHTower.CCMFUSuzukiCheckpointAffineMixtureBound 1 :=
    (GaloisForLFunctions.RHTower.ccmFUCentralXiScrewPositiveMixtureBound_iff_checkpointAffineMixtureBound
      hlog2).mp hpositive
  obtain ⟨C, hC0, hC⟩ := hcheckpoint
  apply ccmFUSuzukiCanonicalCheckpointAffineTailBound_iff_triangularCurvatureTransformBound.mp
  exact ⟨C, hC0, fun H hH => hC H (by linarith)⟩

/-- **Signed triangular-curvature classification.**  Uniform control of the exact third-grade
Suzuki triangular transform is equivalent to RH.  Hence this common CCM--FU/CFI/SP-E high-pass
cannot be an independent source-side route to RH. -/
theorem ccmFUSuzukiTriangularCurvatureTransformBound_iff_riemannHypothesis :
    CCMFUSuzukiTriangularCurvatureTransformBound ↔ RiemannHypothesis := by
  constructor
  · exact riemannHypothesis_of_suzukiCheckpointTriangularCurvatureTransformBound
  · exact ccmFUSuzukiTriangularCurvatureTransformBound_of_riemannHypothesis

end

end RHTower
