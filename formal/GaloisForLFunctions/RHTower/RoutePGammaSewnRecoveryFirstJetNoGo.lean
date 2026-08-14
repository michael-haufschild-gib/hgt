import GaloisForLFunctions.RHTower.GammaSewnSynchronizedRecoveryContraction
import GaloisForLFunctions.RHTower.RoutePScalarUnitaryCompletionRegularityNoGo

/-!
# Route-P Gamma-sewn recovery first-jet no-go

Synchronized Gamma-sewn recovery is an actual source-side contraction carrying
squarefree Möbius parity.  Its recovery ratio is first-jet flat at the cofinal
boundary.  This module composes that source transport with the fixed-node Xi
phase and proves that the phase's linear radial defect survives unchanged.

Thus finite-support signed recovery is a passive carrier of the Ward tangent,
not the missing first-order cancellation mechanism.  Under false RH, any exact
Hilbert completion of the recovered scalar phase is still square-root scale.
-/

open Complex Filter Set Topology

namespace RHTower

noncomputable section

/-- Synchronized signed source recovery applied to the fixed critical Xi phase. -/
def gammaSewnRecoveredScalarXiPhase
    (nu : Nat.Primes → ℝ) (P : Finset Nat.Primes) (a : ℝ) : ℂ :=
  gammaSewnSynchronizedSignedRecoveryAmplitude nu a P *
    xiRightWardBoundarySourcePhaseCrossRatio
      (I * (1 / 2 : ℂ)) (a : ℂ)

/-- Unit-ball defect after synchronized recovery of the fixed critical Xi phase. -/
def gammaSewnRecoveredScalarXiPhaseDefect
    (nu : Nat.Primes → ℝ) (P : Finset Nat.Primes) (a : ℝ) : ℝ :=
  1 - Complex.normSq (gammaSewnRecoveredScalarXiPhase nu P a)

/-- Exact splitting into recovery loss and the Xi phase loss transported by the recovery ratio. -/
theorem gammaSewnRecoveredScalarXiPhaseDefect_eq
    (nu : Nat.Primes → ℝ) (hnu : ∀ p, 0 < nu p)
    (P : Finset Nat.Primes) {a : ℝ} (ha : 0 < a) :
    gammaSewnRecoveredScalarXiPhaseDefect nu P a =
      (1 - gammaSewnSynchronizedRecoveryRatio nu a P) +
        gammaSewnSynchronizedRecoveryRatio nu a P *
          xiWardBoundaryPhaseDefect (1 / 2 : ℂ) a := by
  rw [gammaSewnRecoveredScalarXiPhaseDefect,
    gammaSewnRecoveredScalarXiPhase, Complex.normSq_mul,
    normSq_gammaSewnSynchronizedSignedRecoveryAmplitude nu hnu ha P,
    xiWardBoundaryPhaseDefect]
  ring

/-- **First-jet transparency.**  Gamma-sewn source recovery does not alter the linear critical
Xi phase loss.  Its own loss is `o(a)`, so the recovered scalar defect has exactly the original
Ward density. -/
theorem tendsto_gammaSewnRecoveredScalarXiPhaseDefect_div_aperture
    (nu : Nat.Primes → ℝ) (hnu : ∀ p, 0 < nu p)
    (P : Finset Nat.Primes) :
    Tendsto
      (fun a : ℝ => gammaSewnRecoveredScalarXiPhaseDefect nu P a / a)
      (nhdsWithin 0 (Ioi 0))
      (nhds (2 *
        (continuedXiAntiCausalWardResponse (1 / 2 : ℂ)).re)) := by
  let ratio : ℝ → ℝ :=
    fun a => gammaSewnSynchronizedRecoveryRatio nu a P
  have hratio : Tendsto ratio (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
    simpa only [ratio] using
      tendsto_gammaSewnSynchronizedRecoveryRatio_zero nu hnu P
  have hratioLoss :
      Tendsto (fun a : ℝ => (1 - ratio a) / a)
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    have h :=
      (tendsto_gammaSewnSynchronizedRecoveryRatio_sub_one_div_zero
        nu hnu P).neg
    have h' :
        Tendsto
          (fun a : ℝ => -((ratio a - 1) / a))
          (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
      simpa only [ratio, neg_zero] using h
    apply h'.congr'
    filter_upwards with a
    ring
  have hhalf : 0 < ((1 / 2 : ℂ)).re := by norm_num
  have hzero : xiWardBoundaryPhaseDefect (1 / 2 : ℂ) 0 = 0 := by
    rw [xiWardBoundaryPhaseDefect_eq_transport hhalf]
    norm_num [mobiusGammaXiAntiCausalWardTransportV_zero hhalf]
  have hphase :
      Tendsto
        (fun a : ℝ => xiWardBoundaryPhaseDefect (1 / 2 : ℂ) a / a)
        (nhdsWithin 0 (Ioi 0))
        (nhds (2 *
          (continuedXiAntiCausalWardResponse (1 / 2 : ℂ)).re)) := by
    have h :=
      (hasDerivAt_xiWardBoundaryPhaseDefect_zero hhalf).tendsto_slope_zero_right
    convert h using 1
    ext a
    rw [zero_add, hzero, sub_zero]
    simp only [smul_eq_mul, div_eq_mul_inv]
    ring
  have hsum := hratioLoss.add (hratio.mul hphase)
  have hsum' :
      Tendsto
        (fun a : ℝ => (1 - ratio a) / a +
          ratio a * (xiWardBoundaryPhaseDefect (1 / 2 : ℂ) a / a))
        (nhdsWithin 0 (Ioi 0))
        (nhds (2 *
          (continuedXiAntiCausalWardResponse (1 / 2 : ℂ)).re)) := by
    simpa using hsum
  apply hsum'.congr'
  filter_upwards [self_mem_nhdsWithin] with a ha
  change 0 < a at ha
  rw [gammaSewnRecoveredScalarXiPhaseDefect_eq nu hnu P ha]
  dsimp only [ratio]
  ring

/-- Every exact Hilbert completion of the recovered scalar phase has the same first-order energy
density as the unrecovered phase. -/
theorem tendsto_norm_sq_div_aperture_gammaSewnRecoveredScalarXiPhase_unitaryDefect
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (nu : Nat.Primes → ℝ) (hnu : ∀ p, 0 < nu p)
    (P : Finset Nat.Primes) (c : ℝ → F)
    (hunit : ∀ a : ℝ,
      Complex.normSq (gammaSewnRecoveredScalarXiPhase nu P a) +
        ‖c a‖ ^ 2 = 1) :
    Tendsto (fun a : ℝ => ‖c a‖ ^ 2 / a)
      (nhdsWithin 0 (Ioi 0))
      (nhds (2 *
        (continuedXiAntiCausalWardResponse (1 / 2 : ℂ)).re)) := by
  have hdefect : ∀ a : ℝ,
      gammaSewnRecoveredScalarXiPhaseDefect nu P a = ‖c a‖ ^ 2 := by
    intro a
    rw [gammaSewnRecoveredScalarXiPhaseDefect]
    linarith [hunit a]
  convert
    tendsto_gammaSewnRecoveredScalarXiPhaseDefect_div_aperture
      nu hnu P using 1
  ext a
  rw [hdefect a]

/-- A differentiable exact unitary completion after actual Gamma-sewn source recovery forces RH.
The recovery channel therefore cannot produce the missing cancellation by itself. -/
theorem riemannHypothesis_of_differentiable_gammaSewnRecoveredScalarXiPhase_unitaryCompletion
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (nu : Nat.Primes → ℝ) (hnu : ∀ p, 0 < nu p)
    (P : Finset Nat.Primes) (c : ℝ → F) (c' : F)
    (hc0 : c 0 = 0) (hc : HasDerivAt c c' 0)
    (hunit : ∀ a : ℝ,
      Complex.normSq (gammaSewnRecoveredScalarXiPhase nu P a) +
        ‖c a‖ ^ 2 = 1) :
    RiemannHypothesis := by
  have henergy :=
    tendsto_norm_sq_div_aperture_gammaSewnRecoveredScalarXiPhase_unitaryDefect
      nu hnu P c hunit
  have hcNorm : HasDerivAt (fun a : ℝ => ‖c a‖ ^ 2) 0 0 := by
    have h := hc.norm_sq
    rw [hc0, inner_zero_left, mul_zero] at h
    exact h
  have hzeroEnergy :
      Tendsto (fun a : ℝ => ‖c a‖ ^ 2 / a)
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    have h := hcNorm.tendsto_slope_zero_right
    convert h using 1
    ext a
    rw [hc0]
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, sub_zero, zero_add, smul_eq_mul]
    rw [div_eq_mul_inv, mul_comm]
  have hreZero :
      2 * (continuedXiAntiCausalWardResponse (1 / 2 : ℂ)).re = 0 :=
    tendsto_nhds_unique henergy hzeroEnergy
  by_contra hRH
  have hpos := re_continuedXiAntiCausalWardResponse_half_pos_of_not_rh hRH
  linarith

/-- Under false RH, actual Gamma-sewn source recovery admits no finite-derivative Hilbert defect
completion of its recovered scalar Xi phase. -/
theorem no_differentiable_gammaSewnRecoveredScalarXiPhase_unitaryDefect_of_not_rh
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (hRH : ¬ RiemannHypothesis)
    (nu : Nat.Primes → ℝ) (hnu : ∀ p, 0 < nu p)
    (P : Finset Nat.Primes) (c : ℝ → F) (hc0 : c 0 = 0)
    (hunit : ∀ a : ℝ,
      Complex.normSq (gammaSewnRecoveredScalarXiPhase nu P a) +
        ‖c a‖ ^ 2 = 1) :
    ∀ c' : F, ¬ HasDerivAt c c' 0 := by
  intro c' hc
  exact hRH
    (riemannHypothesis_of_differentiable_gammaSewnRecoveredScalarXiPhase_unitaryCompletion
      nu hnu P c c' hc0 hc hunit)

end

end RHTower
