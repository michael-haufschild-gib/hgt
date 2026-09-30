import GaloisForLFunctions.RHTower.LiEvenCrossActualClockPairedEtaSource
import GaloisForLFunctions.RHTower.LiClockPairedEtaCentralDisk
import GaloisForLFunctions.RHTower.RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaFiniteApproximation
import GaloisForLFunctions.RHTower.RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaCompletedSymmetry
import GaloisForLFunctions.HTGeometry.ReflectedDigammaAnomaly
import Mathlib.Analysis.Calculus.DiffContOnCl

/-!
# Finite paired eta with the full central completion

The finite eta quotient retains every elementary, rational and Gamma connection of the
completed central source. Conjugation of the finite eta pairs gives anti-Schwarz reflection
of the trace without a finite functional equation. The trace is analytic wherever its
finite eta denominator is nonzero in the open critical strip.
-/

open Complex Filter Function Set Topology Metric
open GaloisForLFunctions
open scoped ComplexConjugate

namespace RiemannGaussian

noncomputable section

/-- Every finite eta prefix respects complex conjugation. -/
theorem pairedEtaCorePartialSum_conj (N : ℕ) (s : ℂ) :
    pairedEtaCorePartialSum N (conj s) = conj (pairedEtaCorePartialSum N s) := by
  simp only [pairedEtaCorePartialSum, pairedEtaCoreSummand_conj, map_sum]

/-- Differentiating a finite eta prefix preserves its conjugation symmetry. -/
theorem pairedEtaCoreDerivativePartialSum_conj (N : ℕ) (s : ℂ) :
    pairedEtaCoreDerivativePartialSum N (conj s) =
      conj (pairedEtaCoreDerivativePartialSum N s) := by
  have hfun : (conj ∘ pairedEtaCorePartialSum N ∘ conj) =
      pairedEtaCorePartialSum N := by
    funext w
    simp [Function.comp_apply, pairedEtaCorePartialSum_conj]
  have hd := deriv_conj_conj (f := pairedEtaCorePartialSum N)
  rw [hfun] at hd
  have h := congrFun hd (conj s)
  simpa only [Function.comp_apply, Complex.conj_conj,
    deriv_pairedEtaCorePartialSum] using h

/-- The totalized finite eta quotient respects conjugation, including at denominator zeros. -/
theorem pairedEtaArithmeticQuotientPartialSum_conj (N : ℕ) (s : ℂ) :
    pairedEtaArithmeticQuotientPartialSum N (conj s) =
      conj (pairedEtaArithmeticQuotientPartialSum N s) := by
  rw [pairedEtaArithmeticQuotientPartialSum, pairedEtaArithmeticQuotientPartialSum,
    pairedEtaCoreDerivativePartialSum_conj, pairedEtaCorePartialSum_conj, map_div₀]

end

end RiemannGaussian

namespace RHTower

noncomputable section

private theorem finiteEta_factorLogDerivative_conj (s : ℂ) :
    RiemannGaussian.pairedEtaFactorLogDerivative (conj s) =
      conj (RiemannGaussian.pairedEtaFactorLogDerivative s) := by
  have hlog : conj (Complex.log (2 : ℂ)) = Complex.log (2 : ℂ) := by
    have hlog2 : ((Real.log 2 : ℝ) : ℂ) = Complex.log (2 : ℂ) :=
      Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)
    rw [← hlog2]
    simp only [Complex.conj_ofReal]
  unfold RiemannGaussian.pairedEtaFactorLogDerivative RiemannGaussian.pairedEtaFactor
  rw [RiemannGaussian.two_cpow_neg_conj]
  simp only [map_div₀, map_mul, map_sub, map_ofNat, map_one, hlog]

private theorem finiteEta_gammaRealLogConnection_conj (s : ℂ) :
    gammaRealLogConnection (conj s) = conj (gammaRealLogConnection s) := by
  unfold gammaRealLogConnection
  rw [show conj s / 2 = conj (s / 2) by simp only [map_div₀, map_ofNat],
    ReflectedDigammaAnomaly.digamma_conj]
  simp only [map_add, map_neg, map_div₀, map_ofNat, Complex.conj_ofReal]

/-- The finite central source obtained by replacing only the eta quotient and retaining the
full elementary, rational and Gamma completion. -/
def liClockPairedEtaFiniteSourceTrace (N : ℕ) (z : ℂ) : ℂ :=
  let s : ℂ := 1 / 2 + z * I
  I *
    (RiemannGaussian.pairedEtaArithmeticQuotientPartialSum N s -
      RiemannGaussian.pairedEtaFactorLogDerivative s +
      1 / s + 1 / (s - 1) + gammaRealLogConnection s)

/-- The complete finite trace is anti-Schwarz under `z ↦ -conj z`. This identity holds for the
totalized source and imposes no finite functional equation. -/
theorem liClockPairedEtaFiniteSourceTrace_neg_conj (N : ℕ) (z : ℂ) :
    liClockPairedEtaFiniteSourceTrace N (-conj z) =
      -conj (liClockPairedEtaFiniteSourceTrace N z) := by
  have hs : (1 / 2 : ℂ) + -conj z * I = conj (1 / 2 + z * I) := by
    simp only [map_add, map_mul, map_div₀, map_one, map_ofNat, Complex.conj_I]
    ring
  dsimp only [liClockPairedEtaFiniteSourceTrace]
  rw [hs, RiemannGaussian.pairedEtaArithmeticQuotientPartialSum_conj,
    finiteEta_factorLogDerivative_conj, finiteEta_gammaRealLogConnection_conj]
  simp only [map_mul, map_add, map_sub, map_div₀, map_one, Complex.conj_I]
  ring

/-- At a regular source point, the finite trace is the logarithmic derivative of the finite
eta prefix multiplied by the exact polynomial--Gamma completion factor. -/
theorem liClockPairedEtaFiniteSourceTrace_eq_completion_logDeriv
    (N : ℕ) {z : ℂ} (hlower : 0 < (1 / 2 + z * I).re)
    (hupper : (1 / 2 + z * I).re < 1)
    (heta : RiemannGaussian.pairedEtaCorePartialSum N (1 / 2 + z * I) ≠ 0) :
    liClockPairedEtaFiniteSourceTrace N z = I *
      logDeriv (fun s : ℂ => RiemannGaussian.pairedEtaXiCompletionFactor s *
        RiemannGaussian.pairedEtaCorePartialSum N s) (1 / 2 + z * I) := by
  rw [logDeriv_mul (f := RiemannGaussian.pairedEtaXiCompletionFactor)
    (g := RiemannGaussian.pairedEtaCorePartialSum N) (1 / 2 + z * I)
    (RiemannGaussian.pairedEtaXiCompletionFactor_ne_zero hlower hupper) heta
    (RiemannGaussian.analyticAt_pairedEtaXiCompletionFactor hlower hupper).differentiableAt
    (RiemannGaussian.differentiable_pairedEtaCorePartialSum N (1 / 2 + z * I)),
    RiemannGaussian.logDeriv_pairedEtaXiCompletionFactor hlower hupper,
    logDeriv_apply, RiemannGaussian.deriv_pairedEtaCorePartialSum]
  dsimp only [liClockPairedEtaFiniteSourceTrace,
    RiemannGaussian.pairedEtaArithmeticQuotientPartialSum,
    RiemannGaussian.pairedEtaArithmeticXiRegularCorrection, gammaRealLogConnection]
  rw [Complex.ofReal_log Real.pi_pos.le]
  ring

/-- The finite completed trace is analytic at every nonvanishing finite eta source point
in the full strip `0 < Re(s) < 1`. -/
theorem analyticAt_liClockPairedEtaFiniteSourceTrace
    (N : ℕ) {z : ℂ} (hlower : 0 < (1 / 2 + z * I).re)
    (hupper : (1 / 2 + z * I).re < 1)
    (heta : RiemannGaussian.pairedEtaCorePartialSum N (1 / 2 + z * I) ≠ 0) :
    AnalyticAt ℂ (liClockPairedEtaFiniteSourceTrace N) z := by
  let c : ℂ → ℂ := fun w => 1 / 2 + w * I
  let H : ℂ → ℂ := fun s => RiemannGaussian.pairedEtaXiCompletionFactor s *
    RiemannGaussian.pairedEtaCorePartialSum N s
  have hcA : AnalyticAt ℂ c z :=
    analyticAt_const.add (analyticAt_id.mul analyticAt_const)
  have hc : ContinuousAt c z := hcA.continuousAt
  have hcre : ContinuousAt (fun w => (c w).re) z :=
    Complex.continuous_re.continuousAt.comp hc
  have hp : ∀ᶠ w in 𝓝 z, 0 < (c w).re :=
    hcre (Ioi_mem_nhds hlower)
  have hlt : ∀ᶠ w in 𝓝 z, (c w).re < 1 :=
    hcre (Iio_mem_nhds hupper)
  have hEN : ∀ᶠ w in 𝓝 z, RiemannGaussian.pairedEtaCorePartialSum N (c w) ≠ 0 :=
    ((RiemannGaussian.differentiable_pairedEtaCorePartialSum N (c z)).continuousAt.comp
      hc).eventually_ne heta
  have hHA : AnalyticAt ℂ H (c z) :=
    (RiemannGaussian.analyticAt_pairedEtaXiCompletionFactor hlower hupper).mul
      ((RiemannGaussian.differentiable_pairedEtaCorePartialSum N).analyticAt (c z))
  have hHne : H (c z) ≠ 0 :=
    mul_ne_zero (RiemannGaussian.pairedEtaXiCompletionFactor_ne_zero hlower hupper) heta
  have hlog : AnalyticAt ℂ (logDeriv H) (c z) := by
    change AnalyticAt ℂ (fun s => deriv H s / H s) (c z)
    exact hHA.deriv.div hHA hHne
  have hcomp : AnalyticAt ℂ (fun w => I * logDeriv H (c w)) z :=
    analyticAt_const.mul (hlog.comp hcA)
  apply hcomp.congr
  filter_upwards [hp, hlt, hEN] with w hwpos hwlt hweta
  exact (liClockPairedEtaFiniteSourceTrace_eq_completion_logDeriv N hwpos hwlt hweta).symm

/-- Analyticity gives continuity of the complete finite trace at every regular source point. -/
theorem continuousAt_liClockPairedEtaFiniteSourceTrace
    (N : ℕ) {z : ℂ} (hlower : 0 < (1 / 2 + z * I).re)
    (hupper : (1 / 2 + z * I).re < 1)
    (heta : RiemannGaussian.pairedEtaCorePartialSum N (1 / 2 + z * I) ≠ 0) :
    ContinuousAt (liClockPairedEtaFiniteSourceTrace N) z :=
  (analyticAt_liClockPairedEtaFiniteSourceTrace N hlower hupper heta).continuousAt

private theorem finiteEta_centralCoordinate_re_bounds {z : ℂ}
    (hz : ‖z‖ ≤ (1 / 128 : ℝ)) :
    0 < (1 / 2 + z * I).re ∧ (1 / 2 + z * I).re < 1 := by
  have hi := abs_le.mp ((Complex.abs_im_le_norm z).trans hz)
  have hs : (1 / 2 + z * I).re = (1 / 2 : ℝ) - z.im := by
    norm_num [Complex.add_re, Complex.mul_re]
    ring
  rw [hs]
  constructor <;> linarith

/-- The central norm bound supplies every rational and Gamma domain condition for analyticity;
finite eta nonvanishing remains explicit. -/
theorem analyticAt_liClockPairedEtaFiniteSourceTrace_of_norm_le
    (N : ℕ) {z : ℂ} (hz : ‖z‖ ≤ (1 / 128 : ℝ))
    (heta : RiemannGaussian.pairedEtaCorePartialSum N (1 / 2 + z * I) ≠ 0) :
    AnalyticAt ℂ (liClockPairedEtaFiniteSourceTrace N) z := by
  obtain ⟨hlower, hupper⟩ := finiteEta_centralCoordinate_re_bounds hz
  exact analyticAt_liClockPairedEtaFiniteSourceTrace N hlower hupper heta

/-- The central norm bound supplies every rational and Gamma domain condition for continuity;
finite eta nonvanishing remains explicit. -/
theorem continuousAt_liClockPairedEtaFiniteSourceTrace_of_norm_le
    (N : ℕ) {z : ℂ} (hz : ‖z‖ ≤ (1 / 128 : ℝ))
    (heta : RiemannGaussian.pairedEtaCorePartialSum N (1 / 2 + z * I) ≠ 0) :
    ContinuousAt (liClockPairedEtaFiniteSourceTrace N) z := by
  obtain ⟨hlower, hupper⟩ := finiteEta_centralCoordinate_re_bounds hz
  exact continuousAt_liClockPairedEtaFiniteSourceTrace N hlower hupper heta

/-- Nonvanishing of the finite eta prefix throughout the closed central disk gives continuity
of the full finite trace there. -/
theorem continuousOn_liClockPairedEtaFiniteSourceTrace_closedBall
    (N : ℕ)
    (heta : ∀ z ∈ closedBall (0 : ℂ) (1 / 128 : ℝ),
      RiemannGaussian.pairedEtaCorePartialSum N (1 / 2 + z * I) ≠ 0) :
    ContinuousOn (liClockPairedEtaFiniteSourceTrace N)
      (closedBall (0 : ℂ) (1 / 128 : ℝ)) := by
  intro z hz
  exact (continuousAt_liClockPairedEtaFiniteSourceTrace_of_norm_le N
    (by simpa only [Metric.mem_closedBall, dist_zero_right] using hz)
    (heta z hz)).continuousWithinAt

/-- Circle continuity requires finite eta nonvanishing only on that circle. -/
theorem continuousOn_liClockPairedEtaFiniteSourceTrace_sphere
    (N : ℕ) {r : ℝ} (hr : r ≤ (1 / 128 : ℝ))
    (heta : ∀ z ∈ sphere (0 : ℂ) r,
      RiemannGaussian.pairedEtaCorePartialSum N (1 / 2 + z * I) ≠ 0) :
    ContinuousOn (liClockPairedEtaFiniteSourceTrace N) (sphere (0 : ℂ) r) := by
  intro z hz
  have hn : ‖z‖ = r := by
    simpa only [Metric.mem_sphere, dist_zero_right] using hz
  exact (continuousAt_liClockPairedEtaFiniteSourceTrace_of_norm_le N
    (hn.le.trans hr) (heta z hz)).continuousWithinAt

/-- Nonvanishing of finite eta on the closed central disk supplies the differentiability and
boundary continuity required by the exact central contour functional. -/
theorem diffContOnCl_liClockPairedEtaFiniteSourceTrace_ball
    (N : ℕ) {r : ℝ} (hr : r ≤ (1 / 128 : ℝ))
    (heta : ∀ z ∈ closedBall (0 : ℂ) r,
      RiemannGaussian.pairedEtaCorePartialSum N (1 / 2 + z * I) ≠ 0) :
    DiffContOnCl ℂ (liClockPairedEtaFiniteSourceTrace N) (ball (0 : ℂ) r) := by
  have hA : AnalyticOnNhd ℂ (liClockPairedEtaFiniteSourceTrace N) (closedBall (0 : ℂ) r) := by
    intro z hz
    have hn : ‖z‖ ≤ r := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    exact analyticAt_liClockPairedEtaFiniteSourceTrace_of_norm_le N
      (hn.trans hr) (heta z hz)
  exact hA.differentiableOn.diffContOnCl_ball (Subset.refl _)

end

end RHTower
