import GaloisForLFunctions.RHTower.ThetaCuspHawkingBogoliubovCCRCompletionEndpoint
import GaloisForLFunctions.RHTower.ThetaCuspHawkingFullMirrorGenericCouplingMixingEndpoint
import GaloisForLFunctions.RHTower.ThetaCuspHawkingFullMirrorVanHoveSelectionEndpoint

/-!
# Exact full-mirror Bogoliubov completion and Hawking standard clock

The exact Davies--Fulling theta-mirror numerator is not a sectorwise `SU(2)` Cayley transition.
Its nonzero second coupling jet already rules out that identification.  More fundamentally, a
bosonic pair-creation block has `SU(1,1)` signature:

`gain^2 - |beta|^2 = 1`,

not the plus-sign conservation law of a beam splitter.  This file inserts the standard balanced
Bogoliubov prefactor into the complete eikonal numerator and performs its canonical minimal
two-mode squeeze completion.  The resulting block preserves the full Nambu signed Hermitian form
and has an explicit inverse.

This distinction changes the dynamics.  Against a fresh Hawking KMS partner mode, a nontrivial
squeeze strictly produces particles; it does not relax an exterior population to a Gibbs fixed
point.  Exact full scattering activates every fixed sector, and one common arbitrarily weak
coupling activates every countable tilted family, unconditionally.  Thus finite-coupling
Bogoliubov activity cannot prove RH.

The RH-sensitive survivor is the standard Davies clock.  Dividing the exact full-mirror pair
number by `lambda^2` selects the physical Born coefficient and kills every delayed nonlinear
channel.  Positivity of this no-Cayley limit in every noncentral tilted sector is equivalent to RH.

The `SU(1,1)` completion is the bosonic CCR structure of Hawking/dynamical-Casimir pair creation;
the KMS bath interpretation follows the microscopic moving-mirror open-system derivation of
Butera (`arXiv:2306.03813`).  Standard-clock selection is the weak-coupling regime of repeated
quantum interactions of Attal--Joye (`arXiv:math-ph/0501012`).
-/

open Complex Real Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace RHTower

/-! ## Exact full-mirror bosonic pair block -/

/-- Standard balanced Bogoliubov prefactor multiplying the complete Davies--Fulling numerator. -/
def thetaCuspHawkingFullMirrorBogoliubovBeta
    (a lambda omega : ℝ) : ℂ :=
  (((-1 / (2 * Real.pi * omega) : ℝ) : ℂ)) *
    thetaCuspHawkingBalancedFullMirrorAmplitude a lambda omega

/-- Exact pair number in one balanced full-mirror sector. -/
def thetaCuspHawkingFullMirrorBogoliubovNumber
    (a lambda omega : ℝ) : ℝ :=
  ‖thetaCuspHawkingFullMirrorBogoliubovBeta a lambda omega‖ ^ 2

/-- Minimal positive bosonic gain completing the exact pair block. -/
def thetaCuspHawkingFullMirrorBogoliubovGain
    (a lambda omega : ℝ) : ℝ :=
  Real.sqrt (1 +
    thetaCuspHawkingFullMirrorBogoliubovNumber a lambda omega)

theorem thetaCuspHawkingFullMirrorBogoliubovNumber_nonneg
    (a lambda omega : ℝ) :
    0 ≤ thetaCuspHawkingFullMirrorBogoliubovNumber a lambda omega := by
  exact sq_nonneg _

theorem thetaCuspHawkingFullMirrorBogoliubovGain_sq
    (a lambda omega : ℝ) :
    thetaCuspHawkingFullMirrorBogoliubovGain a lambda omega ^ 2 =
      1 + thetaCuspHawkingFullMirrorBogoliubovNumber a lambda omega := by
  rw [thetaCuspHawkingFullMirrorBogoliubovGain, Real.sq_sqrt]
  exact add_nonneg zero_le_one
    (thetaCuspHawkingFullMirrorBogoliubovNumber_nonneg a lambda omega)

theorem thetaCuspHawkingFullMirrorBogoliubovGain_pos
    (a lambda omega : ℝ) :
    0 < thetaCuspHawkingFullMirrorBogoliubovGain a lambda omega := by
  rw [thetaCuspHawkingFullMirrorBogoliubovGain]
  exact Real.sqrt_pos.2 <| lt_of_lt_of_le zero_lt_one
    (le_add_of_nonneg_right
      (thetaCuspHawkingFullMirrorBogoliubovNumber_nonneg a lambda omega))

/-- The complete eikonal pair numerator has its canonical bosonic `SU(1,1)` completion. -/
theorem thetaCuspHawkingFullMirrorBogoliubov_isTwoModeBosonicCCR
    (a lambda omega : ℝ) :
    IsTwoModeBosonicCCR
      (thetaCuspHawkingFullMirrorBogoliubovGain a lambda omega)
      (thetaCuspHawkingFullMirrorBogoliubovBeta a lambda omega) := by
  rw [IsTwoModeBosonicCCR,
    thetaCuspHawkingFullMirrorBogoliubovGain_sq,
    thetaCuspHawkingFullMirrorBogoliubovNumber]
  ring

/-- Exterior Nambu coordinate of the exact full-mirror squeeze. -/
def thetaCuspHawkingFullMirrorBogoliubovExteriorOutput
    (a lambda omega : ℝ) (x h : ℂ) : ℂ :=
  (thetaCuspHawkingFullMirrorBogoliubovGain a lambda omega : ℂ) * x +
    thetaCuspHawkingFullMirrorBogoliubovBeta a lambda omega * h

/-- Partner Nambu coordinate of the exact full-mirror squeeze. -/
def thetaCuspHawkingFullMirrorBogoliubovPartnerOutput
    (a lambda omega : ℝ) (x h : ℂ) : ℂ :=
  conj (thetaCuspHawkingFullMirrorBogoliubovBeta a lambda omega) * x +
    (thetaCuspHawkingFullMirrorBogoliubovGain a lambda omega : ℂ) * h

/-- Exact full-amplitude Bogoliubov scattering preserves the Nambu signed Hermitian form. -/
theorem thetaCuspHawkingFullMirrorBogoliubov_preserves_signedHermitian
    (a lambda omega : ℝ) (x h : ℂ) :
    conj (thetaCuspHawkingFullMirrorBogoliubovExteriorOutput
          a lambda omega x h) *
        thetaCuspHawkingFullMirrorBogoliubovExteriorOutput
          a lambda omega x h -
      conj (thetaCuspHawkingFullMirrorBogoliubovPartnerOutput
          a lambda omega x h) *
        thetaCuspHawkingFullMirrorBogoliubovPartnerOutput
          a lambda omega x h =
      conj x * x - conj h * h := by
  let gain : ℝ := thetaCuspHawkingFullMirrorBogoliubovGain a lambda omega
  let beta : ℂ := thetaCuspHawkingFullMirrorBogoliubovBeta a lambda omega
  have hgain := thetaCuspHawkingFullMirrorBogoliubovGain_sq a lambda omega
  rw [thetaCuspHawkingFullMirrorBogoliubovNumber] at hgain
  have hgainC := congrArg (fun r : ℝ => (r : ℂ)) hgain
  push_cast at hgainC
  change (gain : ℂ) ^ 2 = 1 + (‖beta‖ : ℂ) ^ 2 at hgainC
  have hnormC : (‖beta‖ : ℂ) ^ 2 = conj beta * beta := by
    rw [show (‖beta‖ : ℂ) ^ 2 = ((‖beta‖ ^ 2 : ℝ) : ℂ) by
      push_cast
      rfl]
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
  rw [hnormC] at hgainC
  change conj ((gain : ℂ) * x + beta * h) *
        ((gain : ℂ) * x + beta * h) -
      conj (conj beta * x + (gain : ℂ) * h) *
        (conj beta * x + (gain : ℂ) * h) =
      conj x * x - conj h * h
  simp only [map_add, map_mul, conj_ofReal, conj_conj]
  linear_combination (conj x * x - conj h * h) * hgainC

/-- First coordinate of the inverse full-mirror Bogoliubov block. -/
def thetaCuspHawkingFullMirrorBogoliubovInverseExterior
    (a lambda omega : ℝ) (x h : ℂ) : ℂ :=
  (thetaCuspHawkingFullMirrorBogoliubovGain a lambda omega : ℂ) * x -
    thetaCuspHawkingFullMirrorBogoliubovBeta a lambda omega * h

/-- Second coordinate of the inverse full-mirror Bogoliubov block. -/
def thetaCuspHawkingFullMirrorBogoliubovInversePartner
    (a lambda omega : ℝ) (x h : ℂ) : ℂ :=
  -conj (thetaCuspHawkingFullMirrorBogoliubovBeta a lambda omega) * x +
    (thetaCuspHawkingFullMirrorBogoliubovGain a lambda omega : ℂ) * h

/-- The displayed signed adjoint is an exact inverse of the full-amplitude squeeze. -/
theorem thetaCuspHawkingFullMirrorBogoliubov_inverse_after_scattering
    (a lambda omega : ℝ) (x h : ℂ) :
    thetaCuspHawkingFullMirrorBogoliubovInverseExterior a lambda omega
        (thetaCuspHawkingFullMirrorBogoliubovExteriorOutput
          a lambda omega x h)
        (thetaCuspHawkingFullMirrorBogoliubovPartnerOutput
          a lambda omega x h) = x ∧
      thetaCuspHawkingFullMirrorBogoliubovInversePartner a lambda omega
        (thetaCuspHawkingFullMirrorBogoliubovExteriorOutput
          a lambda omega x h)
        (thetaCuspHawkingFullMirrorBogoliubovPartnerOutput
          a lambda omega x h) = h := by
  let gain : ℝ := thetaCuspHawkingFullMirrorBogoliubovGain a lambda omega
  let beta : ℂ := thetaCuspHawkingFullMirrorBogoliubovBeta a lambda omega
  have hgain := thetaCuspHawkingFullMirrorBogoliubovGain_sq a lambda omega
  rw [thetaCuspHawkingFullMirrorBogoliubovNumber] at hgain
  have hgainC := congrArg (fun r : ℝ => (r : ℂ)) hgain
  push_cast at hgainC
  change (gain : ℂ) ^ 2 = 1 + (‖beta‖ : ℂ) ^ 2 at hgainC
  have hnormC : (‖beta‖ : ℂ) ^ 2 = conj beta * beta := by
    rw [show (‖beta‖ : ℂ) ^ 2 = ((‖beta‖ ^ 2 : ℝ) : ℂ) by
      push_cast
      rfl]
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
  rw [hnormC] at hgainC
  change
    (gain : ℂ) * ((gain : ℂ) * x + beta * h) -
        beta * (conj beta * x + (gain : ℂ) * h) = x ∧
      -conj beta * ((gain : ℂ) * x + beta * h) +
        (gain : ℂ) * (conj beta * x + (gain : ℂ) * h) = h
  constructor
  · linear_combination x * hgainC
  · linear_combination h * hgainC

/-! ## Signature obstruction to the Cayley identification -/

/-- A nontrivial two-mode block cannot obey both `SU(2)` lossless and bosonic `SU(1,1)` laws. -/
theorem pair_eq_zero_of_lossless_and_bosonicCCR
    {gain : ℝ} {pair : ℂ}
    (hlossless : gain ^ 2 + ‖pair‖ ^ 2 = 1)
    (hCCR : IsTwoModeBosonicCCR gain pair) :
    pair = 0 := by
  rw [IsTwoModeBosonicCCR] at hCCR
  have hnormSq : ‖pair‖ ^ 2 = 0 := by
    linarith
  have hnorm : ‖pair‖ = 0 := by
    nlinarith [norm_nonneg pair]
  exact norm_eq_zero.mp hnorm

/-- Every genuinely pair-producing full-mirror block violates the plus-sign Cayley law. -/
theorem thetaCuspHawkingFullMirrorBogoliubov_not_lossless_of_beta_ne_zero
    {a lambda omega : ℝ}
    (hbeta : thetaCuspHawkingFullMirrorBogoliubovBeta a lambda omega ≠ 0) :
    ¬(thetaCuspHawkingFullMirrorBogoliubovGain a lambda omega ^ 2 +
        ‖thetaCuspHawkingFullMirrorBogoliubovBeta a lambda omega‖ ^ 2 = 1) := by
  intro hlossless
  exact hbeta (pair_eq_zero_of_lossless_and_bosonicCCR hlossless
    (thetaCuspHawkingFullMirrorBogoliubov_isTwoModeBosonicCCR
      a lambda omega))

/-! ## Actual Hawking KMS pair production -/

/-- Bose--Einstein occupation of a Hawking KMS partner mode. -/
def thetaCuspHawkingFullMirrorBogoliubovKMSOccupation
    (kappa omega : ℝ) : ℝ :=
  thetaCuspHawkingKMSBoltzmannRatio kappa omega /
    (1 - thetaCuspHawkingKMSBoltzmannRatio kappa omega)

theorem thetaCuspHawkingFullMirrorBogoliubovKMSOccupation_nonneg
    {kappa omega : ℝ} (hkappa : 0 < kappa) (homega : 0 < omega) :
    0 ≤ thetaCuspHawkingFullMirrorBogoliubovKMSOccupation kappa omega := by
  unfold thetaCuspHawkingFullMirrorBogoliubovKMSOccupation
  exact div_nonneg
    (thetaCuspHawkingKMSBoltzmannRatio_pos kappa omega).le
    (sub_nonneg.mpr
      (thetaCuspHawkingKMSBoltzmannRatio_lt_one hkappa homega).le)

/-- Exterior occupation after one exact squeeze against an uncorrelated KMS partner. -/
def thetaCuspHawkingFullMirrorBogoliubovKMSOutputPopulation
    (kappa a lambda omega p : ℝ) : ℝ :=
  thetaCuspHawkingFullMirrorBogoliubovGain a lambda omega ^ 2 * p +
    thetaCuspHawkingFullMirrorBogoliubovNumber a lambda omega *
      (thetaCuspHawkingFullMirrorBogoliubovKMSOccupation kappa omega + 1)

/-- Exact stimulated-plus-spontaneous Hawking production law. -/
theorem thetaCuspHawkingFullMirrorBogoliubovKMSOutputPopulation_sub
    (kappa a lambda omega p : ℝ) :
    thetaCuspHawkingFullMirrorBogoliubovKMSOutputPopulation
        kappa a lambda omega p - p =
      thetaCuspHawkingFullMirrorBogoliubovNumber a lambda omega *
        (p + thetaCuspHawkingFullMirrorBogoliubovKMSOccupation kappa omega + 1) := by
  rw [thetaCuspHawkingFullMirrorBogoliubovKMSOutputPopulation]
  have hgain := thetaCuspHawkingFullMirrorBogoliubovGain_sq a lambda omega
  linear_combination p * hgain

/-- A nontrivial exact Hawking squeeze strictly increases every nonnegative exterior population. -/
theorem thetaCuspHawkingFullMirrorBogoliubovKMSOutputPopulation_gt
    {kappa a lambda omega p : ℝ}
    (hkappa : 0 < kappa) (homega : 0 < omega) (hp : 0 ≤ p)
    (hbeta : thetaCuspHawkingFullMirrorBogoliubovBeta a lambda omega ≠ 0) :
    p < thetaCuspHawkingFullMirrorBogoliubovKMSOutputPopulation
      kappa a lambda omega p := by
  have hnumber : 0 < thetaCuspHawkingFullMirrorBogoliubovNumber
      a lambda omega := by
    exact sq_pos_of_pos (norm_pos_iff.mpr hbeta)
  have hthermal :=
    thetaCuspHawkingFullMirrorBogoliubovKMSOccupation_nonneg hkappa homega
  rw [← sub_pos]
  rw [thetaCuspHawkingFullMirrorBogoliubovKMSOutputPopulation_sub]
  exact mul_pos hnumber (by linarith)

/-! ## Unconditional finite-coupling squeezing -/

/-- One balanced full-mirror sector genuinely produces a Bogoliubov pair. -/
def ThetaCuspHawkingFullMirrorBogoliubovSectorSqueezes
    (a lambda omega : ℝ) : Prop :=
  thetaCuspHawkingFullMirrorBogoliubovBeta a lambda omega ≠ 0

theorem thetaCuspHawkingFullMirrorBogoliubovSectorSqueezes_iff
    {a lambda omega : ℝ} (homega : 0 < omega) :
    ThetaCuspHawkingFullMirrorBogoliubovSectorSqueezes a lambda omega ↔
      thetaCuspHawkingBalancedFullMirrorAmplitude a lambda omega ≠ 0 := by
  have hprefactor :
      (((-1 / (2 * Real.pi * omega) : ℝ) : ℂ)) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr <| div_ne_zero (by norm_num)
      (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) homega.ne')
  constructor
  · intro hbeta hamplitude
    apply hbeta
    rw [thetaCuspHawkingFullMirrorBogoliubovBeta, hamplitude, mul_zero]
  · intro hamplitude
    exact mul_ne_zero hprefactor hamplitude

/-- One common arbitrarily weak physical coupling squeezes every member of a countable tilted
resonance family.  This is unconditional full-scattering activity, not an RH criterion. -/
theorem exists_arbitrarily_weak_common_thetaCuspHawkingFullMirrorBogoliubov_squeeze
    {ι : Type*} [Countable ι] [Nonempty ι]
    (a omega : ι → ℝ) (ha : ∀ i, |a i| < 1)
    (homega : ∀ i, 0 < omega i) (ε : ℝ) (hε : 0 < ε) :
    ∃ lambda : ℝ, 0 < |lambda| ∧ |lambda| < ε ∧
      ∀ i, ThetaCuspHawkingFullMirrorBogoliubovSectorSqueezes
        (a i) lambda (omega i) := by
  obtain ⟨lambda, hlambda0, hlambdaε, hall⟩ :=
    exists_arbitrarily_weak_common_thetaCuspHawkingFullMirror_mix
      a omega ha homega ε hε
  exact ⟨lambda, hlambda0, hlambdaε, fun i =>
    (thetaCuspHawkingFullMirrorBogoliubovSectorSqueezes_iff
      (homega i)).2 (hall i)⟩

/-! ## Cayley-free standard-clock endpoint -/

/-- Exact full-mirror Bogoliubov pair number per unit standard van-Hove time. -/
def thetaCuspHawkingFullMirrorBogoliubovVanHoveRate
    (a lambda omega : ℝ) : ℝ :=
  thetaCuspHawkingFullMirrorBogoliubovNumber a lambda omega / lambda ^ 2

/-- Standard balanced prefactor intensity. -/
def thetaCuspHawkingFullMirrorBogoliubovPrefactorNumber (omega : ℝ) : ℝ :=
  Complex.normSq (((-1 / (2 * Real.pi * omega) : ℝ) : ℂ))

/-- Exact rate selected from full Bogoliubov scattering by the common Davies clock. -/
def thetaCuspHawkingFullMirrorBogoliubovVanHoveLimitRate
    (a omega : ℝ) : ℝ :=
  thetaCuspHawkingFullMirrorBogoliubovPrefactorNumber omega *
    thetaCuspHawkingFullMirrorVanHoveLimitRate a omega

theorem thetaCuspHawkingFullMirrorBogoliubovVanHoveRate_eq
    (a lambda omega : ℝ) :
    thetaCuspHawkingFullMirrorBogoliubovVanHoveRate a lambda omega =
      thetaCuspHawkingFullMirrorBogoliubovPrefactorNumber omega *
        thetaCuspHawkingFullMirrorBornScaledPairProbability
          a lambda (omega / 2) (omega / 2) := by
  rw [thetaCuspHawkingFullMirrorBogoliubovVanHoveRate,
    thetaCuspHawkingFullMirrorBogoliubovNumber,
    thetaCuspHawkingFullMirrorBogoliubovBeta,
    thetaCuspHawkingFullMirrorBogoliubovPrefactorNumber,
    thetaCuspHawkingFullMirrorBornScaledPairProbability,
    ← Complex.normSq_eq_norm_sq, Complex.normSq_mul]
  rw [thetaCuspHawkingBalancedFullMirrorAmplitude]
  ring

/-- **Exact no-Cayley weak-coupling selection.**  The physical full-mirror Bogoliubov pair number
on the standard clock converges to the normalized theta/Xi Born rate. -/
theorem tendsto_thetaCuspHawkingFullMirrorBogoliubovVanHoveRate
    (a : ℝ) (ha : |a| < 1) (omega : ℝ) :
    Tendsto
      (fun lambda : ℝ =>
        thetaCuspHawkingFullMirrorBogoliubovVanHoveRate a lambda omega)
      (𝓝[≠] (0 : ℝ))
      (𝓝 (thetaCuspHawkingFullMirrorBogoliubovVanHoveLimitRate a omega)) := by
  have hraw :=
    tendsto_thetaCuspHawkingFullMirrorBornScaledPairProbability
      a ha (omega / 2) (omega / 2)
  have hprefactor : Tendsto
      (fun _ : ℝ => thetaCuspHawkingFullMirrorBogoliubovPrefactorNumber omega)
      (𝓝[≠] (0 : ℝ))
      (𝓝 (thetaCuspHawkingFullMirrorBogoliubovPrefactorNumber omega)) :=
    tendsto_const_nhds
  have hscaled := hprefactor.mul hraw
  have hborn :
      Complex.normSq
          (thetaCuspTiltedMovingMirrorBornRaw
            a ha (omega / 2) (omega / 2)) =
        thetaCuspHawkingFullMirrorVanHoveLimitRate a omega :=
    normSq_thetaCuspTiltedMovingMirrorBornRaw_balanced_eq_vanHoveLimitRate
      a ha omega
  simpa [thetaCuspHawkingFullMirrorBogoliubovVanHoveRate_eq,
    thetaCuspHawkingFullMirrorBogoliubovVanHoveLimitRate, hborn] using hscaled

theorem thetaCuspHawkingFullMirrorBogoliubovPrefactorNumber_pos
    {omega : ℝ} (homega : 0 < omega) :
    0 < thetaCuspHawkingFullMirrorBogoliubovPrefactorNumber omega := by
  rw [thetaCuspHawkingFullMirrorBogoliubovPrefactorNumber]
  apply Complex.normSq_pos.mpr
  exact Complex.ofReal_ne_zero.mpr <| div_ne_zero (by norm_num)
    (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) homega.ne')

theorem thetaCuspHawkingFullMirrorBogoliubovVanHoveLimitRate_pos_iff
    {a omega : ℝ} (homega : 0 < omega) :
    0 < thetaCuspHawkingFullMirrorBogoliubovVanHoveLimitRate a omega ↔
      XiC ((omega : ℂ) + (a : ℂ) * Complex.I) ≠ 0 := by
  have hprefactor :=
    thetaCuspHawkingFullMirrorBogoliubovPrefactorNumber_pos homega
  rw [thetaCuspHawkingFullMirrorBogoliubovVanHoveLimitRate]
  constructor
  · intro hpos
    have hraw : 0 < thetaCuspHawkingFullMirrorVanHoveLimitRate a omega :=
      pos_of_mul_pos_right hpos hprefactor.le
    exact (thetaCuspHawkingFullMirrorVanHoveLimitRate_pos_iff homega).1 hraw
  · intro hXi
    exact mul_pos hprefactor
      ((thetaCuspHawkingFullMirrorVanHoveLimitRate_pos_iff homega).2 hXi)

/-- Every noncentral tilted full-mirror sector produces pairs on the same standard Hawking clock. -/
def ThetaCuspHawkingFullMirrorBogoliubovStandardClockPairProduction : Prop :=
  ∀ (a omega : ℝ), 0 < omega → |a| < 1 → a ≠ 0 →
    0 < thetaCuspHawkingFullMirrorBogoliubovVanHoveLimitRate a omega

/-- **[BRIDGE] [NOVELTY UNVERIFIED] Full-mirror Bogoliubov endpoint.**  RH is equivalent to
nondegenerate pair production in every noncentral tilted sector on one physical Davies clock,
after the exact nonlinear theta-mirror amplitude has received its bosonic CCR completion.  No
sectorwise Cayley completion occurs in the statement or proof. -/
theorem riemannHypothesis_iff_thetaCuspHawkingFullMirrorBogoliubovStandardClockPairProduction :
    RiemannHypothesis ↔
      ThetaCuspHawkingFullMirrorBogoliubovStandardClockPairProduction := by
  rw [riemannHypothesis_iff_XiC_zeros_real]
  constructor
  · intro hreal a omega homega _ha hane
    rw [thetaCuspHawkingFullMirrorBogoliubovVanHoveLimitRate_pos_iff homega]
    intro hXi
    have him := hreal ((omega : ℂ) + (a : ℂ) * Complex.I) hXi
    exact hane (by simpa using him)
  · intro hproduction z hz
    by_contra hzim
    have hzre : z.re ≠ 0 := by
      intro hre
      have hform : z = (z.im : ℂ) * Complex.I := by
        apply Complex.ext <;> simp [hre]
      rw [hform] at hz
      exact XiC_ne_zero_of_imaginary z.im hz
    have hstrip := xiC_zero_im_mem_openHalf hz
    have ha : |z.im| < 1 := by
      rw [abs_lt]
      constructor <;> linarith
    rcases lt_or_gt_of_ne hzre with hneg | hpos
    · have hrate := hproduction (-z.im) (-z.re) (by linarith)
          (by simpa using ha) (neg_ne_zero.mpr hzim)
      have hXiNe :=
        (thetaCuspHawkingFullMirrorBogoliubovVanHoveLimitRate_pos_iff
          (by linarith)).1 hrate
      apply hXiNe
      have harg :
          (((-z.re : ℝ) : ℂ) + ((-z.im : ℝ) : ℂ) * Complex.I) = -z := by
        apply Complex.ext <;> simp
      rw [harg, XiC_even]
      exact hz
    · have hrate := hproduction z.im z.re hpos ha hzim
      have hXiNe :=
        (thetaCuspHawkingFullMirrorBogoliubovVanHoveLimitRate_pos_iff
          hpos).1 hrate
      apply hXiNe
      have harg : ((z.re : ℂ) + (z.im : ℂ) * Complex.I) = z := by
        apply Complex.ext <;> simp
      rwa [harg]

end RHTower
