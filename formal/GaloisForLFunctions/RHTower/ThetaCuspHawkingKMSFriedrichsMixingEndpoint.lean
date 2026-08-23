import GaloisForLFunctions.RHTower.ThetaCuspHawkingTiltedMirrorOpticalTheoremEndpoint
import GaloisForLFunctions.RHTower.XiRealAxisNonvanishing

/-!
# Hawking--KMS Friedrichs on-shell width of the tilted theta resonance sector

The tilted moving mirror supplies the coefficient-correct positive-frequency shell density

`J_a(ω) = ω^4 |XiC(ω + a i)|^2 / (48 π^2)`.

This file applies the minimal Araki--Woods thermal dilation at Hawking inverse temperature
`β_H = 2π / κ`.  If `q = exp (-β_H ω)`, its positive- and negative-Liouville-frequency weights are

`J_a(ω) / (1-q)` and `q J_a(ω) / (1-q)`.

They obey exact KMS detailed balance.  Schwarz reflection identifies the negative-frequency
coefficient with the physical reflected tilt `-a`, so this is one doubled KMS channel rather than
two unrelated copies.  The sum of both weights is the decay width of the resonance block.

For a rank-one Friedrichs scattering model, choosing a real mass counterterm to cancel the
principal-value part leaves the on-shell boundary value `-i Γ/2`, formalized below.  This is the
second-order Fermi-golden-rule obstruction at one tuned energy.  By itself it is not a proof of
global mixing: an embedded eigenvalue also requires the real dispersion equation, while return to
equilibrium needs spectral regularity beyond a single boundary value.

Thus Hawking thermality supplies the actual KMS dilation and its coefficients, but does not make a
dark form factor positive.  The property named below is the historical on-shell non-dark proxy.  The
explicit Araki--Woods amplitudes, Davies generator, and genuine long-time sector mixing statement
are supplied by `ThetaCuspHawkingArakiWoodsDaviesMixingEndpoint`.
-/

open Complex Real

noncomputable section

namespace RHTower

/-- Unsquared shell form factor whose norm square is the exact tilted-mirror shell density. -/
def thetaCuspHawkingFriedrichsShellFormFactor (a omega : ℝ) : ℂ :=
  ((omega ^ 2 / (4 * Real.sqrt 3 * Real.pi) : ℝ) : ℂ) *
    XiC ((omega : ℂ) + (a : ℂ) * I)

theorem normSq_thetaCuspHawkingFriedrichsShellFormFactor
    (a omega : ℝ) :
    Complex.normSq (thetaCuspHawkingFriedrichsShellFormFactor a omega) =
      thetaCuspHawkingTiltedBornRightEnergyShellDensity a omega := by
  rw [thetaCuspHawkingFriedrichsShellFormFactor,
    thetaCuspHawkingTiltedBornRightEnergyShellDensity_eq]
  simp only [Complex.normSq_mul, Complex.normSq_ofReal]
  have hsqrt : Real.sqrt 3 ^ 2 = 3 := by norm_num
  have hsqrt0 : Real.sqrt 3 ≠ 0 := by positivity
  field_simp [Real.pi_ne_zero, hsqrt0]
  rw [hsqrt]
  ring

/-- The reflected physical tilt is exactly the conjugate unsquared shell coefficient. -/
theorem thetaCuspHawkingFriedrichsShellFormFactor_neg_tilt
    (a omega : ℝ) :
    thetaCuspHawkingFriedrichsShellFormFactor (-a) omega =
      (starRingEnd ℂ) (thetaCuspHawkingFriedrichsShellFormFactor a omega) := by
  rw [thetaCuspHawkingFriedrichsShellFormFactor,
    thetaCuspHawkingFriedrichsShellFormFactor]
  have harg :
      (omega : ℂ) + ((-a : ℝ) : ℂ) * I =
        (starRingEnd ℂ) ((omega : ℂ) + (a : ℂ) * I) := by
    apply Complex.ext <;> simp
  rw [harg, XiC_conj, map_mul]
  congr 1
  exact (Complex.conj_ofReal _).symm

/-- Hawking detailed-balance ratio `exp (-β_H ω)`, where `β_H = 2π / κ`. -/
def thetaCuspHawkingKMSBoltzmannRatio (kappa omega : ℝ) : ℝ :=
  Real.exp (-(2 * Real.pi * omega / kappa))

theorem thetaCuspHawkingKMSBoltzmannRatio_pos (kappa omega : ℝ) :
    0 < thetaCuspHawkingKMSBoltzmannRatio kappa omega :=
  Real.exp_pos _

theorem thetaCuspHawkingKMSBoltzmannRatio_lt_one
    {kappa omega : ℝ} (hkappa : 0 < kappa) (homega : 0 < omega) :
    thetaCuspHawkingKMSBoltzmannRatio kappa omega < 1 := by
  rw [thetaCuspHawkingKMSBoltzmannRatio, Real.exp_lt_one_iff]
  have hquot : 0 < 2 * Real.pi * omega / kappa := by positivity
  linarith

/-- Positive-Liouville-frequency Araki--Woods shell weight `(1+n_H) J_a`. -/
def thetaCuspHawkingKMSDownShell
    (kappa a omega : ℝ) : ℝ :=
  thetaCuspHawkingTiltedBornRightEnergyShellDensity a omega /
    (1 - thetaCuspHawkingKMSBoltzmannRatio kappa omega)

/-- Negative-Liouville-frequency Araki--Woods shell weight `n_H J_a`. -/
def thetaCuspHawkingKMSUpShell
    (kappa a omega : ℝ) : ℝ :=
  thetaCuspHawkingKMSBoltzmannRatio kappa omega *
    thetaCuspHawkingKMSDownShell kappa a omega

/-- Exact KMS detailed balance in the source-faithful theta shell. -/
theorem thetaCuspHawkingKMSUpShell_eq_ratio_mul_down
    (kappa a omega : ℝ) :
    thetaCuspHawkingKMSUpShell kappa a omega =
      thetaCuspHawkingKMSBoltzmannRatio kappa omega *
        thetaCuspHawkingKMSDownShell kappa a omega :=
  rfl

theorem thetaCuspHawkingKMSDownShell_nonneg
    {kappa a omega : ℝ} (hkappa : 0 < kappa) (homega : 0 < omega) :
    0 ≤ thetaCuspHawkingKMSDownShell kappa a omega := by
  apply div_nonneg
  · exact thetaCuspHawkingTiltedBornRightEnergyShellDensity_nonneg a omega
  · exact sub_nonneg.mpr
      (thetaCuspHawkingKMSBoltzmannRatio_lt_one hkappa homega).le

theorem thetaCuspHawkingKMSUpShell_nonneg
    {kappa a omega : ℝ} (hkappa : 0 < kappa) (homega : 0 < omega) :
    0 ≤ thetaCuspHawkingKMSUpShell kappa a omega := by
  exact mul_nonneg (thetaCuspHawkingKMSBoltzmannRatio_pos kappa omega).le
    (thetaCuspHawkingKMSDownShell_nonneg hkappa homega)

/-- Total two-sided thermal decay width of the exact KMS resonance block. -/
def thetaCuspHawkingKMSResonanceWidth
    (kappa a omega : ℝ) : ℝ :=
  2 * Real.pi *
    (thetaCuspHawkingKMSDownShell kappa a omega +
      thetaCuspHawkingKMSUpShell kappa a omega)

theorem thetaCuspHawkingKMSResonanceWidth_nonneg
    {kappa a omega : ℝ} (hkappa : 0 < kappa) (homega : 0 < omega) :
    0 ≤ thetaCuspHawkingKMSResonanceWidth kappa a omega := by
  exact mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le)
    (add_nonneg
      (thetaCuspHawkingKMSDownShell_nonneg hkappa homega)
      (thetaCuspHawkingKMSUpShell_nonneg hkappa homega))

theorem thetaCuspHawkingKMSResonanceWidth_pos_of_XiC_ne_zero
    {kappa a omega : ℝ} (hkappa : 0 < kappa) (homega : 0 < omega)
    (hXi : XiC ((omega : ℂ) + (a : ℂ) * I) ≠ 0) :
    0 < thetaCuspHawkingKMSResonanceWidth kappa a omega := by
  have hshellNe :
      thetaCuspHawkingTiltedBornRightEnergyShellDensity a omega ≠ 0 := by
    intro hshell
    exact hXi
      ((thetaCuspHawkingTiltedBornRightEnergyShellDensity_eq_zero_iff homega).1 hshell)
  have hshellPos :
      0 < thetaCuspHawkingTiltedBornRightEnergyShellDensity a omega :=
    lt_of_le_of_ne
      (thetaCuspHawkingTiltedBornRightEnergyShellDensity_nonneg a omega)
      (Ne.symm hshellNe)
  have hden :
      0 < 1 - thetaCuspHawkingKMSBoltzmannRatio kappa omega :=
    sub_pos.mpr (thetaCuspHawkingKMSBoltzmannRatio_lt_one hkappa homega)
  have hdown : 0 < thetaCuspHawkingKMSDownShell kappa a omega :=
    div_pos hshellPos hden
  have hup : 0 ≤ thetaCuspHawkingKMSUpShell kappa a omega :=
    thetaCuspHawkingKMSUpShell_nonneg hkappa homega
  unfold thetaCuspHawkingKMSResonanceWidth
  positivity

/-- The Hawking KMS width vanishes exactly at a nonkinematic theta/Xi dark frequency. -/
theorem thetaCuspHawkingKMSResonanceWidth_eq_zero_iff
    {kappa a omega : ℝ} (hkappa : 0 < kappa) (homega : 0 < omega) :
    thetaCuspHawkingKMSResonanceWidth kappa a omega = 0 ↔
      XiC ((omega : ℂ) + (a : ℂ) * I) = 0 := by
  constructor
  · intro hwidth
    by_contra hXi
    have hpos :=
      thetaCuspHawkingKMSResonanceWidth_pos_of_XiC_ne_zero hkappa homega hXi
    rw [hwidth] at hpos
    exact (lt_irrefl 0) hpos
  · intro hXi
    have hshell :
        thetaCuspHawkingTiltedBornRightEnergyShellDensity a omega = 0 :=
      (thetaCuspHawkingTiltedBornRightEnergyShellDensity_eq_zero_iff homega).2 hXi
    simp [thetaCuspHawkingKMSResonanceWidth,
      thetaCuspHawkingKMSDownShell, thetaCuspHawkingKMSUpShell, hshell]

/-- Schwarz reflection makes the physical tilts `a` and `-a` one KMS-reflected shell pair. -/
theorem thetaCuspHawkingTiltedBornRightEnergyShellDensity_neg_tilt
    (a omega : ℝ) :
    thetaCuspHawkingTiltedBornRightEnergyShellDensity (-a) omega =
      thetaCuspHawkingTiltedBornRightEnergyShellDensity a omega := by
  rw [thetaCuspHawkingTiltedBornRightEnergyShellDensity_eq,
    thetaCuspHawkingTiltedBornRightEnergyShellDensity_eq]
  have harg :
      (omega : ℂ) + ((-a : ℝ) : ℂ) * I =
        (starRingEnd ℂ) ((omega : ℂ) + (a : ℂ) * I) := by
    apply Complex.ext <;> simp
  rw [harg, XiC_conj, Complex.normSq_conj]

theorem thetaCuspHawkingKMSResonanceWidth_neg_tilt
    (kappa a omega : ℝ) :
    thetaCuspHawkingKMSResonanceWidth kappa (-a) omega =
      thetaCuspHawkingKMSResonanceWidth kappa a omega := by
  simp only [thetaCuspHawkingKMSResonanceWidth,
    thetaCuspHawkingKMSUpShell, thetaCuspHawkingKMSDownShell,
    thetaCuspHawkingTiltedBornRightEnergyShellDensity_neg_tilt]

/-- Boundary value of the real-counterterm-renormalized Friedrichs denominator at the resonance. -/
def thetaCuspHawkingKMSFriedrichsOnShellDeterminant
    (kappa a omega : ℝ) : ℂ :=
  -(I * (thetaCuspHawkingKMSResonanceWidth kappa a omega : ℂ)) / 2

theorem thetaCuspHawkingKMSFriedrichsOnShellDeterminant_eq_zero_iff
    {kappa a omega : ℝ} (hkappa : 0 < kappa) (homega : 0 < omega) :
    thetaCuspHawkingKMSFriedrichsOnShellDeterminant kappa a omega = 0 ↔
      XiC ((omega : ℂ) + (a : ℂ) * I) = 0 := by
  rw [thetaCuspHawkingKMSFriedrichsOnShellDeterminant]
  simp only [div_eq_zero_iff, OfNat.ofNat_ne_zero, or_false, neg_eq_zero,
    mul_eq_zero, I_ne_zero, false_or, Complex.ofReal_eq_zero]
  exact thetaCuspHawkingKMSResonanceWidth_eq_zero_iff hkappa homega

/-- Every positive-frequency, nonzero-tilt Friedrichs sector has nonzero tuned on-shell
Fermi-golden-rule denominator. -/
def ThetaCuspHawkingKMSFriedrichsResonanceMixing : Prop :=
  ∀ (kappa a omega : ℝ), 0 < kappa → 0 < omega → |a| < 1 → a ≠ 0 →
    thetaCuspHawkingKMSFriedrichsOnShellDeterminant kappa a omega ≠ 0

/-- **Source-faithful Hawking--KMS on-shell endpoint.**  Nonvanishing of every noncentral tilted
tuned Friedrichs denominator is equivalent to RH.  The theorem uses the derived moving-mirror Born
shell coefficient and exact Hawking detailed-balance weights; it does not infer a no-dark-mode law
from KMS alone, nor assert full interacting return to equilibrium. -/
theorem riemannHypothesis_iff_thetaCuspHawkingKMSFriedrichsResonanceMixing :
    RiemannHypothesis ↔ ThetaCuspHawkingKMSFriedrichsResonanceMixing := by
  rw [riemannHypothesis_iff_XiC_zeros_real]
  constructor
  · intro hreal kappa a omega hkappa homega _ha hane hdet
    have hXi :=
      (thetaCuspHawkingKMSFriedrichsOnShellDeterminant_eq_zero_iff
        hkappa homega).1 hdet
    have him := hreal ((omega : ℂ) + (a : ℂ) * I) hXi
    exact hane (by simpa using him)
  · intro hmix z hz
    by_contra hzim
    have hzre : z.re ≠ 0 := by
      intro hre
      have hform : z = (z.im : ℂ) * I := by
        apply Complex.ext <;> simp [hre]
      rw [hform] at hz
      exact XiC_ne_zero_of_imaginary z.im hz
    have hstrip := xiC_zero_im_mem_openHalf hz
    have ha : |z.im| < 1 := by
      rw [abs_lt]
      constructor <;> linarith
    rcases lt_or_gt_of_ne hzre with hneg | hpos
    · have hdet := hmix 1 (-z.im) (-z.re) (by norm_num) (by linarith)
          (by simpa using ha) (neg_ne_zero.mpr hzim)
      apply hdet
      apply (thetaCuspHawkingKMSFriedrichsOnShellDeterminant_eq_zero_iff
        (by norm_num) (by linarith)).2
      have harg :
          (((-z.re : ℝ) : ℂ) + ((-z.im : ℝ) : ℂ) * I) = -z := by
        apply Complex.ext <;> simp
      rw [harg, XiC_even]
      exact hz
    · have hdet := hmix 1 z.im z.re (by norm_num) hpos ha hzim
      apply hdet
      apply (thetaCuspHawkingKMSFriedrichsOnShellDeterminant_eq_zero_iff
        (by norm_num) hpos).2
      have harg : ((z.re : ℂ) + (z.im : ℂ) * I) = z := by
        apply Complex.ext <;> simp
      rwa [harg]

end RHTower
