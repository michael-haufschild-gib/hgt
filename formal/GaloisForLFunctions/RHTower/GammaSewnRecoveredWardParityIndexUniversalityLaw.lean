import GaloisForLFunctions.RHTower.GammaSewnSynchronizedRecoveryContraction
import GaloisForLFunctions.RHTower.XiWardInfinitesimalDefectIndexQuantization
import GaloisForLFunctions.RHTower.XiWardZeroFreeMarginPrimeLogSampling

/-!
# Gamma-sewn recovered Ward parity-index universality

Synchronized Gamma-sewn recovery is strictly lossy at every positive aperture, but its loss is
quadratic at the cofinal endpoint.  Consequently it cannot alter the first-order Xi Ward charge:
it only multiplies the signed Julia-defect density by squarefree Möbius parity.  Absolute charge
therefore remains quantized in the same universal `8π` packets.

This joins finite-support Gamma-sewn recovery with the global Euler-edge Ward index.  Neither parent
law alone contains the recovered signed defect or its parity-invariant absolute index.
-/

open Complex Filter MeasureTheory Real Set Topology
open scoped Topology

namespace RHTower

noncomputable section

/-- Gamma-sewn squarefree recovery applied to the anti-causal Ward displacement. -/
def gammaSewnRecoveredWardAmplitude
    (nu : Nat.Primes → ℝ) (P : Finset Nat.Primes)
    (w : ℂ) (a : ℝ) : ℂ :=
  gammaSewnSynchronizedSignedRecoveryAmplitude nu a P *
    mobiusGammaXiAntiCausalWardTransportV w (a : ℂ)

/-- Signed Cayley/Julia defect of the recovered Ward displacement. -/
def gammaSewnRecoveredWardSignedDefect
    (nu : Nat.Primes → ℝ) (P : Finset Nat.Primes)
    (w : ℂ) (a : ℝ) : ℝ :=
  2 * (gammaSewnRecoveredWardAmplitude nu P w a).re -
    Complex.normSq (gammaSewnRecoveredWardAmplitude nu P w a)

private theorem tendsto_signedJuliaDefect_div_of_tendsto_quotient
    {A : ℝ → ℂ} {L : ℂ}
    (hAq : Tendsto (fun a : ℝ => A a / (a : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 L)) :
    Tendsto
      (fun a : ℝ =>
        (2 * (A a).re - Complex.normSq (A a)) / a)
      (𝓝[>] (0 : ℝ)) (𝓝 (2 * L.re)) := by
  have ha :
      Tendsto (fun a : ℝ => (a : ℂ))
        (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    Complex.continuous_ofReal.continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have hAprod :
      Tendsto (fun a : ℝ => (A a / (a : ℂ)) * (a : ℂ))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using hAq.mul ha
  have hA :
      Tendsto A (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    apply hAprod.congr'
    filter_upwards [self_mem_nhdsWithin] with a ha'
    change 0 < a at ha'
    field_simp [ha'.ne']
  have hnormAq :
      Tendsto (fun a : ℝ => ‖A a / (a : ℂ)‖)
        (𝓝[>] (0 : ℝ)) (𝓝 ‖L‖) :=
    (continuous_norm.tendsto L).comp hAq
  have hnormA :
      Tendsto (fun a : ℝ => ‖A a‖)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hcomp := (continuous_norm.tendsto (0 : ℂ)).comp hA
    have hcomp' : Tendsto (fun a : ℝ => ‖A a‖)
        (𝓝[>] (0 : ℝ)) (𝓝 ‖(0 : ℂ)‖) :=
      hcomp.congr' (Eventually.of_forall fun _ => rfl)
    simpa only [norm_zero] using hcomp'
  have hnormTerm :
      Tendsto (fun a : ℝ => Complex.normSq (A a) / a)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hprod :
        Tendsto (fun a : ℝ => ‖A a / (a : ℂ)‖ * ‖A a‖)
          (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa using hnormAq.mul hnormA
    apply hprod.congr'
    filter_upwards [self_mem_nhdsWithin] with a ha'
    change 0 < a at ha'
    rw [norm_div, norm_real, Real.norm_eq_abs, abs_of_pos ha',
      ← Complex.sq_norm]
    field_simp [ha'.ne']
  have hre :
      Tendsto (fun a : ℝ => (A a / (a : ℂ)).re)
        (𝓝[>] (0 : ℝ)) (𝓝 L.re) :=
    (Complex.continuous_re.tendsto L).comp hAq
  have hre' :
      Tendsto (fun a : ℝ => (A a).re / a)
        (𝓝[>] (0 : ℝ)) (𝓝 L.re) := by
    apply hre.congr'
    filter_upwards [self_mem_nhdsWithin] with a ha'
    change 0 < a at ha'
    rw [div_re, Complex.normSq_ofReal]
    simp only [ofReal_re, ofReal_im]
    field_simp [ha'.ne']
    ring_nf
  have hmain :=
    ((tendsto_const_nhds : Tendsto (fun _ : ℝ => (2 : ℝ))
      (𝓝[>] (0 : ℝ)) (𝓝 2)).mul hre').sub hnormTerm
  have hmain' :
      Tendsto
        (fun a : ℝ =>
          2 * ((A a).re / a) - Complex.normSq (A a) / a)
        (𝓝[>] (0 : ℝ)) (𝓝 (2 * L.re)) := by
    simpa using hmain
  apply hmain'.congr'
  filter_upwards [self_mem_nhdsWithin] with a ha'
  change 0 < a at ha'
  field_simp [ha'.ne']

/-- The recovered signed Ward defect vanishes at the cofinal endpoint. -/
theorem gammaSewnRecoveredWardSignedDefect_zero
    (nu : Nat.Primes → ℝ) (P : Finset Nat.Primes)
    {w : ℂ} (hw : 0 < w.re) :
    gammaSewnRecoveredWardSignedDefect nu P w 0 = 0 := by
  rw [gammaSewnRecoveredWardSignedDefect,
    gammaSewnRecoveredWardAmplitude]
  change
    2 * (gammaSewnSynchronizedSignedRecoveryAmplitude nu 0 P *
      mobiusGammaXiAntiCausalWardTransportV w 0).re -
      Complex.normSq
        (gammaSewnSynchronizedSignedRecoveryAmplitude nu 0 P *
          mobiusGammaXiAntiCausalWardTransportV w 0) = 0
  rw [mobiusGammaXiAntiCausalWardTransportV_zero hw]
  simp

/-- **Recovered Ward parity law.**  Every strict-right recovered signed defect has the original
Ward slope multiplied by squarefree Möbius parity. -/
theorem gammaSewnRecoveredWardSignedDefect_slope_zero_right
    (nu : Nat.Primes → ℝ) (hnu : ∀ p, 0 < nu p)
    (P : Finset Nat.Primes) {w : ℂ} (hw : 0 < w.re) :
    Tendsto
      (fun a : ℝ => gammaSewnRecoveredWardSignedDefect nu P w a / a)
      (𝓝[>] (0 : ℝ))
      (𝓝 (((-1 : ℝ) ^ P.card) *
        (2 * (continuedXiAntiCausalWardResponse w).re))) := by
  have hquotient :=
    gammaSewnSynchronizedSignedRecovery_preserves_antiCausalWardTangent
      nu hnu P hw
  have hdefect :=
    tendsto_signedJuliaDefect_div_of_tendsto_quotient
      (A := gammaSewnRecoveredWardAmplitude nu P w)
      (L := ((((-1 : ℝ) ^ P.card : ℝ) : ℂ)) *
        continuedXiAntiCausalWardResponse w) hquotient
  change Tendsto
    (fun a : ℝ =>
      (2 * (gammaSewnRecoveredWardAmplitude nu P w a).re -
        Complex.normSq (gammaSewnRecoveredWardAmplitude nu P w a)) / a)
    (𝓝[>] (0 : ℝ)) _
  have hlimit :
      2 * (((((-1 : ℝ) ^ P.card : ℝ) : ℂ)) *
          continuedXiAntiCausalWardResponse w).re =
        ((-1 : ℝ) ^ P.card) *
          (2 * (continuedXiAntiCausalWardResponse w).re) := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    ring
  rw [← hlimit]
  exact hdefect

/-- Euler-edge density of the recovered infinitesimal Ward defect. -/
def gammaSewnRecoveredWardInfinitesimalDensity
    (P : Finset Nat.Primes) (t : ℝ) : ℝ :=
  (-1 : ℝ) ^ P.card * xiWardInfinitesimalDefectDensity t

/-- Recovery changes only orientation, never absolute pointwise density. -/
theorem abs_gammaSewnRecoveredWardInfinitesimalDensity
    (P : Finset Nat.Primes) (t : ℝ) :
    |gammaSewnRecoveredWardInfinitesimalDensity P t| =
      xiWardInfinitesimalDefectDensity t := by
  have hw :
      0 < ((1 / 2 : ℂ) + I * (t : ℂ)).re := by
    norm_num [Complex.add_re, Complex.mul_re]
  have hnonneg : 0 ≤ xiWardInfinitesimalDefectDensity t := by
    exact mul_nonneg (by norm_num)
      (re_continuedXiAntiCausalWardResponse_nonneg hw)
  rw [gammaSewnRecoveredWardInfinitesimalDensity, abs_mul, abs_pow,
    abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg hnonneg]

/-- Euler-edge specialization of the recovered parity law. -/
theorem gammaSewnRecoveredWardSignedDefect_eulerEdge_slope_zero_right
    (nu : Nat.Primes → ℝ) (hnu : ∀ p, 0 < nu p)
    (P : Finset Nat.Primes) (t : ℝ) :
    Tendsto
      (fun a : ℝ =>
        gammaSewnRecoveredWardSignedDefect nu P
          ((1 / 2 : ℂ) + I * (t : ℂ)) a / a)
      (𝓝[>] (0 : ℝ))
      (𝓝 (gammaSewnRecoveredWardInfinitesimalDensity P t)) := by
  have hw :
      0 < ((1 / 2 : ℂ) + I * (t : ℂ)).re := by
    norm_num [Complex.add_re, Complex.mul_re]
  simpa [gammaSewnRecoveredWardInfinitesimalDensity,
    xiWardInfinitesimalDefectDensity] using
    gammaSewnRecoveredWardSignedDefect_slope_zero_right nu hnu P hw

/-- **Absolute recovered index law.**  Möbius parity cannot change total Euler-edge charge:
each strict-right upper Schwarz pair still contributes exactly `8π`. -/
theorem lintegral_abs_gammaSewnRecoveredWardInfinitesimalDensity
    (P : Finset Nat.Primes) :
    ∫⁻ t : ℝ,
        ENNReal.ofReal |gammaSewnRecoveredWardInfinitesimalDensity P t| =
      ∑' _ : XiRightUpperZeroCopy, ENNReal.ofReal (8 * π) := by
  simpa only [abs_gammaSewnRecoveredWardInfinitesimalDensity] using
    lintegral_xiWardInfinitesimalDefectDensity

/-- **Gamma-sewn recovered Ward parity-index universality.**  Non-vacuum recovery is strictly
contractive at every finite aperture, while its cofinal signed defect retains the full Ward tangent
up to Möbius parity and its absolute Euler-edge index retains all universal `8π` packets. -/
theorem gammaSewn_recoveredWardParityIndexUniversality
    (nu : Nat.Primes → ℝ) (hnu : ∀ p, 0 < nu p)
    (P : Finset Nat.Primes) (hP : P.Nonempty) :
    (∀ {a : ℝ}, 0 < a →
      ‖gammaSewnSynchronizedSignedRecoveryAmplitude nu a P‖ < 1) ∧
    (∀ {w : ℂ}, 0 < w.re →
      Tendsto
        (fun a : ℝ =>
          gammaSewnRecoveredWardSignedDefect nu P w a / a)
        (𝓝[>] (0 : ℝ))
        (𝓝 (((-1 : ℝ) ^ P.card) *
          (2 * (continuedXiAntiCausalWardResponse w).re)))) ∧
    (∀ t : ℝ,
      Tendsto
        (fun a : ℝ =>
          gammaSewnRecoveredWardSignedDefect nu P
            ((1 / 2 : ℂ) + I * (t : ℂ)) a / a)
        (𝓝[>] (0 : ℝ))
        (𝓝 (gammaSewnRecoveredWardInfinitesimalDensity P t))) ∧
    (∫⁻ t : ℝ,
        ENNReal.ofReal |gammaSewnRecoveredWardInfinitesimalDensity P t| =
      ∑' _ : XiRightUpperZeroCopy, ENNReal.ofReal (8 * π)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a ha
    exact norm_gammaSewnSynchronizedSignedRecoveryAmplitude_lt_one
      nu hnu ha hP
  · intro w hw
    exact gammaSewnRecoveredWardSignedDefect_slope_zero_right
      nu hnu P hw
  · exact gammaSewnRecoveredWardSignedDefect_eulerEdge_slope_zero_right
      nu hnu P
  · exact lintegral_abs_gammaSewnRecoveredWardInfinitesimalDensity P

end

end RHTower
