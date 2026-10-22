import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingSchwarzschildJostIncidenceNoGo
import GaloisForLFunctions.RHTower.ThetaCarrierHassePacket
import GaloisForLFunctions.RHTower.XiWeilCauchyCoreMultiplicity

/-!
# Theta EKG cubic triad incidence at a Jost dark frequency

The stationary Schwarzschild Jost/Evans incidence identifies a theta/Xi divisor point as a
source zero at real carrier frequency `w`, with the divisor height `a` retained as source tilt.
Einstein--Klein--Gordon backreaction is not frequency diagonal: scalar stress energy is quadratic,
and the scalar field rescattered by the second-order metric is cubic.  For a complex scalar the
frequency selection law is `nu₁ - nu₂ + nu₃ = w`.

This file proves a theta-specific kinematic incidence theorem for that genuine cubic channel.
At every divisor `alpha = w + i a` and at every requested frequency scale, the exact resonant
triad

`(nu₁, nu₂, nu₃) = (w + 2 epsilon, epsilon, -epsilon)`

obeys the cubic frequency law and has nonzero theta amplitude on all three legs, although the
target theta amplitude at `w` is zero.  The proof uses two source facts: every Xi zero is isolated,
and the positive theta source makes `XiC(i a)` strictly positive throughout the divisor strip.

Thus EKG kinematics can fill every theta dark frequency, on or off the critical line.  This does
not assert that the radial/angular second-order Teukolsky overlap is nonzero on the selected triad.
That coefficient-level no-dark-kernel statement is the remaining dynamical incidence; KMS and
passivity do not supply it.
-/

open Complex Real Set Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace RHTower

/-- Theta source amplitude on the physical real-frequency line at fixed modular tilt `a`. -/
def thetaCuspHawkingTiltedFrequencyAmplitude (a frequency : ℝ) : ℂ :=
  XiC ((frequency : ℂ) + (a : ℂ) * Complex.I)

/-- Local complex-scalar EKG cubic spectral monomial.  The middle leg is conjugated because it
comes from the quadratic stress-energy pairing. -/
def thetaCuspHawkingEKGCubicTriadAmplitude
    (a nu₁ nu₂ nu₃ : ℝ) : ℂ :=
  thetaCuspHawkingTiltedFrequencyAmplitude a nu₁ *
    starRingEnd ℂ (thetaCuspHawkingTiltedFrequencyAmplitude a nu₂) *
      thetaCuspHawkingTiltedFrequencyAmplitude a nu₃

/-- The physical theta line is dark at the real carrier coordinate of every Xi divisor point. -/
theorem thetaCuspHawkingTiltedFrequencyAmplitude_divisor_eq_zero
    (q : XiZeroCopy) :
    thetaCuspHawkingTiltedFrequencyAmplitude
      (xiSpectralPoint q).im (xiSpectralPoint q).re = 0 := by
  rw [thetaCuspHawkingTiltedFrequencyAmplitude, Complex.re_add_im]
  exact XiC_xiSpectralPoint_eq_zero q

/-- Exact frequency conservation for the near-divisor EKG cubic triad. -/
theorem thetaCuspHawkingEKGCubicTriad_frequency_balance
    (w epsilon : ℝ) :
    (w + 2 * epsilon) - epsilon + (-epsilon) = w := by
  ring

/-- **Every theta Jost dark frequency has arbitrarily local bright EKG cubic input triads.**
For every Xi divisor and every positive resolution `delta`, all three input legs are nonzero,
their maximal displacement from the target/centre is below `delta`, and they satisfy the exact
complex-scalar cubic selection rule. -/
theorem exists_thetaCuspHawkingEKGCubicBrightTriad_near_divisor
    (q : XiZeroCopy) {delta : ℝ} (hdelta : 0 < delta) :
    ∃ epsilon : ℝ,
      0 < epsilon ∧ 2 * epsilon < delta ∧
      ((xiSpectralPoint q).re + 2 * epsilon) - epsilon + (-epsilon) =
        (xiSpectralPoint q).re ∧
      thetaCuspHawkingTiltedFrequencyAmplitude
        (xiSpectralPoint q).im (xiSpectralPoint q).re = 0 ∧
      thetaCuspHawkingEKGCubicTriadAmplitude
        (xiSpectralPoint q).im
        ((xiSpectralPoint q).re + 2 * epsilon) epsilon (-epsilon) ≠ 0 := by
  let alpha : ℂ := xiSpectralPoint q
  let a : ℝ := alpha.im
  let w : ℝ := alpha.re
  have hzero : XiC alpha = 0 := by
    simpa only [alpha] using XiC_xiSpectralPoint_eq_zero q
  have haHalf : |a| < 1 / 2 := by
    exact abs_im_lt_half_of_XiC_eq_zero hzero
  have haOne : |a| ≤ 1 := haHalf.le.trans (by norm_num)
  have hcenterRe : 0 < (XiC (Complex.I * (a : ℂ))).re :=
    XiC_imaginary_pos haOne
  have hcenter : XiC (Complex.I * (a : ℂ)) ≠ 0 := by
    intro h
    rw [h] at hcenterRe
    simp at hcenterRe
  have hcenterEventually :
      ∀ᶠ z in 𝓝 (Complex.I * (a : ℂ)), XiC z ≠ 0 :=
    (XiC_analytic _ (Set.mem_univ _)).continuousAt.eventually_ne hcenter
  obtain ⟨rCenter, hrCenter, hCenterBall⟩ :=
    Metric.eventually_nhds_iff.mp hcenterEventually
  have hpunct := eventually_XiC_ne_zero_punctured alpha
  change {z : ℂ | XiC z ≠ 0} ∈ 𝓝[({alpha} : Set ℂ)ᶜ] alpha at hpunct
  obtain ⟨rAlpha, hrAlpha, hAlphaBall⟩ :=
    Metric.mem_nhdsWithin_iff.mp hpunct
  let epsilon : ℝ := min (delta / 4) (min (rAlpha / 4) (rCenter / 2))
  have hepsilon : 0 < epsilon := by
    dsimp only [epsilon]
    exact lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have htwiceDelta : 2 * epsilon < delta := by
    have hle : epsilon ≤ delta / 4 := min_le_left _ _
    linarith
  have htwiceAlpha : 2 * epsilon < rAlpha := by
    have hle : epsilon ≤ rAlpha / 4 :=
      le_trans (min_le_right _ _) (min_le_left _ _)
    linarith
  have hepsilonCenter : epsilon < rCenter := by
    have hle : epsilon ≤ rCenter / 2 :=
      le_trans (min_le_right _ _) (min_le_right _ _)
    linarith
  let pAlpha : ℂ := ((w + 2 * epsilon : ℝ) : ℂ) + (a : ℂ) * Complex.I
  have hpAlphaDist : dist pAlpha alpha = 2 * epsilon := by
    rw [dist_eq_norm]
    have hdiff : pAlpha - alpha = 2 * (epsilon : ℂ) := by
      dsimp only [pAlpha, w, a]
      push_cast
      calc
        (alpha.re : ℂ) + 2 * (epsilon : ℂ) +
              (alpha.im : ℂ) * Complex.I - alpha =
            ((alpha.re : ℂ) + (alpha.im : ℂ) * Complex.I - alpha) +
              2 * (epsilon : ℂ) := by ring
        _ = 2 * (epsilon : ℂ) := by
          rw [Complex.re_add_im]
          ring
    rw [hdiff, norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hepsilon]
    norm_num
  have hpAlphaBall : pAlpha ∈ Metric.ball alpha rAlpha := by
    rw [Metric.mem_ball, hpAlphaDist]
    exact htwiceAlpha
  have hpAlphaNe : pAlpha ≠ alpha := by
    intro h
    have : dist pAlpha alpha = 0 := by rw [h, dist_self]
    rw [hpAlphaDist] at this
    linarith
  have hpAlphaXi : XiC pAlpha ≠ 0 :=
    hAlphaBall ⟨hpAlphaBall, by simpa using hpAlphaNe⟩
  let pPlus : ℂ := (epsilon : ℂ) + (a : ℂ) * Complex.I
  have hpPlusDist : dist pPlus (Complex.I * (a : ℂ)) = epsilon := by
    rw [dist_eq_norm]
    have hdiff : pPlus - Complex.I * (a : ℂ) = (epsilon : ℂ) := by
      dsimp only [pPlus]
      ring
    rw [hdiff, norm_real, Real.norm_eq_abs, abs_of_pos hepsilon]
  have hpPlusXi : XiC pPlus ≠ 0 := by
    apply hCenterBall
    rw [hpPlusDist]
    exact hepsilonCenter
  let pMinus : ℂ := ((-epsilon : ℝ) : ℂ) + (a : ℂ) * Complex.I
  have hpMinusDist : dist pMinus (Complex.I * (a : ℂ)) = epsilon := by
    rw [dist_eq_norm]
    have hdiff : pMinus - Complex.I * (a : ℂ) = ((-epsilon : ℝ) : ℂ) := by
      dsimp only [pMinus]
      ring
    rw [hdiff, norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos hepsilon]
  have hpMinusXi : XiC pMinus ≠ 0 := by
    apply hCenterBall
    rw [hpMinusDist]
    exact hepsilonCenter
  have hpPlusConj : starRingEnd ℂ (XiC pPlus) ≠ 0 :=
    (map_ne_zero_iff (starRingEnd ℂ) star_injective).2 hpPlusXi
  refine ⟨epsilon, hepsilon, htwiceDelta,
    thetaCuspHawkingEKGCubicTriad_frequency_balance w epsilon, ?_, ?_⟩
  · simpa only [alpha, a, w] using
      thetaCuspHawkingTiltedFrequencyAmplitude_divisor_eq_zero q
  · rw [thetaCuspHawkingEKGCubicTriadAmplitude,
      thetaCuspHawkingTiltedFrequencyAmplitude,
      thetaCuspHawkingTiltedFrequencyAmplitude,
      thetaCuspHawkingTiltedFrequencyAmplitude]
    exact mul_ne_zero (mul_ne_zero hpAlphaXi hpPlusConj) hpMinusXi

end RHTower
