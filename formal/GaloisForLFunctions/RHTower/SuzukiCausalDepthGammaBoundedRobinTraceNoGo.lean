import GaloisForLFunctions.RHTower.SuzukiCausalDepthGammaSchurTraceClassCompletion
import GaloisForLFunctions.RHTower.SuzukiTransitionCoreLinearCompensationNoGo
import GaloisForLFunctions.RHTower.RectangularSemilocalObserverTailSeparation
import GaloisForLFunctions.RHTower.TraceNormBound

/-!
# Bounded Robin observers cannot extract the CCM-FU correction from the Gamma-Schur trace carrier

The completed causal-depth Gamma-Schur kernel is the source block of one fixed positive
trace-class operator `K`.  A tempting final Robin comparison is to pair `K` with a family of
bounded boundary observers.  Trace duality gives

`|Re Tr(K B_N)| ≤ ‖K‖₁ ‖B_N‖`.

The exact Suzuki transition-core scaling law forces every correction capable of leaving a
lower-semibounded rectangular Ward defect to carry at least `n / 576` mass on apertures `8n`.
Therefore the observer norms themselves must have linear trace-weighted growth.  In particular,
no uniformly bounded Robin observer on the fixed trace-class carrier can close the Ward premise.

This kills the bounded Robin-trace branch of `SUZUKI-FE-REFLECTED-WALL-WARD-ASSEMBLY`.  The sharp
positive survivor is singular/unbounded Robin transport, a cutoff-growing carrier, or a
non-trace-class relative trace assembled before the Gram/cofinal limit.  No RH premise, Xi-zero
hypothesis, numerical computation, asymptotic interchange, or added axiom is used.
-/

open Complex Filter
open scoped Topology

namespace RHTower

noncomputable section

open GaloisForLFunctions.RHTower

/-- Trace response of one bounded observer against the fixed causal-depth Gamma-Schur energy. -/
def suzukiCausalDepthGammaBoundedObserverTraceCorrection
    (observer : ℕ → SuzukiCausalDepthGammaTraceL2 →L[ℂ]
      SuzukiCausalDepthGammaTraceL2) (N : ℕ) : ℝ :=
  (ContinuousLinearMap.opTrace
    (suzukiCanonicalCausalDepthGammaEnergyOperator ∘L observer N)).re

/-- Trace duality places every bounded-observer correction below trace norm times observer norm. -/
theorem suzukiCausalDepthGammaBoundedObserverTraceCorrection_le
    (observer : ℕ → SuzukiCausalDepthGammaTraceL2 →L[ℂ]
      SuzukiCausalDepthGammaTraceL2) (N : ℕ) :
    suzukiCausalDepthGammaBoundedObserverTraceCorrection observer N ≤
      traceNorm SuzukiCausalDepthGammaTraceL2
          suzukiCanonicalCausalDepthGammaEnergyOperator * ‖observer N‖ := by
  calc
    suzukiCausalDepthGammaBoundedObserverTraceCorrection observer N ≤
        |suzukiCausalDepthGammaBoundedObserverTraceCorrection observer N| :=
      le_abs_self _
    _ ≤ ‖ContinuousLinearMap.opTrace
        (suzukiCanonicalCausalDepthGammaEnergyOperator ∘L observer N)‖ :=
      Complex.abs_re_le_norm _
    _ ≤ traceNorm SuzukiCausalDepthGammaTraceL2
          suzukiCanonicalCausalDepthGammaEnergyOperator * ‖observer N‖ :=
      norm_opTrace_comp_le_norm_mul_traceNorm
        (IsTraceClass.memSchattenClass_one
          suzukiCanonicalCausalDepthGammaEnergyOperator_isTraceClass)
        (observer N)

/-- **Sharp positive survivor.**  Ward semiboundedness forces linear trace-weighted observer norm
on the cofinal aperture mesh. -/
theorem eventually_linear_le_causalDepthGammaTraceNorm_mul_observerNorm_of_Ward_bddBelow
    (L : ℝ)
    (observer : ℕ → SuzukiCausalDepthGammaTraceL2 →L[ℂ]
      SuzukiCausalDepthGammaTraceL2)
    (lower : ℝ)
    (hlower : ∀ᶠ n : ℕ in atTop,
      lower ≤ suzukiRectangularWardDefect L
        (fun N => suzukiNaturalApertureTransitionCoreCauchyEnergy N -
          suzukiCausalDepthGammaBoundedObserverTraceCorrection observer N)
        (8 * n)) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) / 576 ≤
      traceNorm SuzukiCausalDepthGammaTraceL2
          suzukiCanonicalCausalDepthGammaEnergyOperator * ‖observer (8 * n)‖ := by
  have hlinear :=
    eventually_linear_le_correction_of_transitionCoreWardDefect_bddBelow
      L (suzukiCausalDepthGammaBoundedObserverTraceCorrection observer) lower hlower
  filter_upwards [hlinear] with n hn
  exact hn.trans
    (suzukiCausalDepthGammaBoundedObserverTraceCorrection_le observer (8 * n))

/-- Uniformly bounded observer families make the corrected Ward defect tend to minus infinity. -/
theorem tendsto_suzukiRectangularWardDefect_transitionCore_sub_boundedGammaObserver_atBot
    (L : ℝ)
    (observer : ℕ → SuzukiCausalDepthGammaTraceL2 →L[ℂ]
      SuzukiCausalDepthGammaTraceL2)
    (M : ℝ) (hobserver : ∀ N, ‖observer N‖ ≤ M) :
    Tendsto (fun n : ℕ =>
      suzukiRectangularWardDefect L
        (fun N => suzukiNaturalApertureTransitionCoreCauchyEnergy N -
          suzukiCausalDepthGammaBoundedObserverTraceCorrection observer N)
        (8 * n)) atTop atBot := by
  apply tendsto_suzukiRectangularWardDefect_transitionCore_sub_bounded_atBot L
  intro N
  exact (suzukiCausalDepthGammaBoundedObserverTraceCorrection_le observer N).trans
    (mul_le_mul_of_nonneg_left (hobserver N)
      (traceNorm_nonneg suzukiCanonicalCausalDepthGammaEnergyOperator))

/-- **Closed producer-class kill.**  A uniformly bounded observer on the fixed positive
trace-class Gamma-Schur carrier cannot make the transition-core rectangular Ward defect
semibounded. -/
theorem no_uniformlyBounded_causalDepthGammaTrace_WardProducer :
    ¬ ∃ (L M lower : ℝ)
      (observer : ℕ → SuzukiCausalDepthGammaTraceL2 →L[ℂ]
        SuzukiCausalDepthGammaTraceL2),
      (∀ N, ‖observer N‖ ≤ M) ∧
      ∀ᶠ n : ℕ in atTop,
        lower ≤ suzukiRectangularWardDefect L
          (fun N => suzukiNaturalApertureTransitionCoreCauchyEnergy N -
            suzukiCausalDepthGammaBoundedObserverTraceCorrection observer N)
          (8 * n) := by
  rintro ⟨L, M, lower, observer, hobserver, hlower⟩
  have hfall :=
    tendsto_suzukiRectangularWardDefect_transitionCore_sub_boundedGammaObserver_atBot
      L observer M hobserver
  have hbelow : ∀ᶠ n : ℕ in atTop,
      suzukiRectangularWardDefect L
        (fun N => suzukiNaturalApertureTransitionCoreCauchyEnergy N -
          suzukiCausalDepthGammaBoundedObserverTraceCorrection observer N)
        (8 * n) ≤ lower - 1 :=
    (tendsto_atBot.1 hfall) (lower - 1)
  rcases (hlower.and hbelow).exists with ⟨n, hlow, hhigh⟩
  linarith

end


end RHTower
