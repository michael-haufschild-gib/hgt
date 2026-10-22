import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingKMSFriedrichsMixingEndpoint

/-!
# Hawking Araki--Woods/Davies mixing of a theta resonance sector

This file replaces a merely named "mixing width" by the exact two-state resonance block obtained
from the standard thermal dilation.

For one positive Bohr frequency `omega`, the source-derived unsquared shell coefficient is

`F_a(omega) = omega^(2 : ℕ) XiC(omega + a i) / (4 sqrt(3) pi)`.

At Hartle--Hawking inverse temperature `beta_H = 2 pi / kappa`, the Araki--Woods one-particle coupling has
two on-shell components

`sqrt(1+n_H) F_a` and `sqrt(n_H) conj(F_a)`.

Their norm squares are the down/up shell weights already derived from the tilted theta mirror.  The
Davies weak-coupling population generator therefore has rates

`gamma_down = 2 pi (1+n_H) |F_a|^(2 : ℕ)`,
`gamma_up   = 2 pi n_H |F_a|^(2 : ℕ)`.

It conserves population, fixes the Hawking Gibbs vector, satisfies detailed balance, and has exactly
one transverse population mode, with eigenvalue `-(gamma_down + gamma_up)`.  That mode converges
to equilibrium precisely when the theta coefficient is nonzero.

The theta input remains the exact coefficient of the preceding moving-mirror Born calculation; the
Araki--Woods dilation and Davies resonance block built from that form factor are exact at the
weak-coupling level.  This is not a claim that the full interacting Pauli--Fierz Liouvillean mixes
iff its second-order width is nonzero; that stronger statement needs regularity, small-coupling
spectral analysis, and can have higher-order channels.  Nor is the evaporating Unruh state being
identified with a global KMS state: this module uses the Hartle--Hawking thermal sector.
-/

open Complex Real Filter Topology

noncomputable section

namespace RHTower

/-- Positive-frequency component of the on-shell Hawking Araki--Woods coupling. -/
def thetaCuspHawkingArakiWoodsDownAmplitude
    (kappa a omega : ℝ) : ℂ :=
  ((Real.sqrt
      (1 / (1 - thetaCuspHawkingKMSBoltzmannRatio kappa omega)) : ℝ) : ℂ) *
    thetaCuspHawkingFriedrichsShellFormFactor a omega

/-- Negative-Liouville-frequency component of the on-shell Hawking Araki--Woods coupling. -/
def thetaCuspHawkingArakiWoodsUpAmplitude
    (kappa a omega : ℝ) : ℂ :=
  ((Real.sqrt
      (thetaCuspHawkingKMSBoltzmannRatio kappa omega /
        (1 - thetaCuspHawkingKMSBoltzmannRatio kappa omega)) : ℝ) : ℂ) *
    (starRingEnd ℂ) (thetaCuspHawkingFriedrichsShellFormFactor a omega)

/-- The positive-frequency Araki--Woods amplitude has norm square `(1+n_H)J_a`. -/
theorem normSq_thetaCuspHawkingArakiWoodsDownAmplitude
    {kappa a omega : ℝ} (hkappa : 0 < kappa) (homega : 0 < omega) :
    Complex.normSq (thetaCuspHawkingArakiWoodsDownAmplitude kappa a omega) =
      thetaCuspHawkingKMSDownShell kappa a omega := by
  have hden :
      0 ≤ 1 - thetaCuspHawkingKMSBoltzmannRatio kappa omega :=
    (sub_pos.mpr
      (thetaCuspHawkingKMSBoltzmannRatio_lt_one hkappa homega)).le
  rw [thetaCuspHawkingArakiWoodsDownAmplitude, Complex.normSq_mul,
    Complex.normSq_ofReal, Real.mul_self_sqrt (one_div_nonneg.mpr hden),
    normSq_thetaCuspHawkingFriedrichsShellFormFactor]
  rw [thetaCuspHawkingKMSDownShell]
  ring

/-- The negative-frequency Araki--Woods amplitude has norm square `n_H J_a`. -/
theorem normSq_thetaCuspHawkingArakiWoodsUpAmplitude
    {kappa a omega : ℝ} (hkappa : 0 < kappa) (homega : 0 < omega) :
    Complex.normSq (thetaCuspHawkingArakiWoodsUpAmplitude kappa a omega) =
      thetaCuspHawkingKMSUpShell kappa a omega := by
  have hq : 0 ≤ thetaCuspHawkingKMSBoltzmannRatio kappa omega :=
    (thetaCuspHawkingKMSBoltzmannRatio_pos kappa omega).le
  have hden :
      0 ≤ 1 - thetaCuspHawkingKMSBoltzmannRatio kappa omega :=
    (sub_pos.mpr
      (thetaCuspHawkingKMSBoltzmannRatio_lt_one hkappa homega)).le
  rw [thetaCuspHawkingArakiWoodsUpAmplitude, Complex.normSq_mul,
    Complex.normSq_ofReal, Real.mul_self_sqrt (div_nonneg hq hden),
    Complex.normSq_conj,
    normSq_thetaCuspHawkingFriedrichsShellFormFactor]
  rw [thetaCuspHawkingKMSUpShell, thetaCuspHawkingKMSDownShell]
  ring

/-- Davies down-transition rate selected by the positive Bohr frequency. -/
def thetaCuspHawkingDaviesDownRate (kappa a omega : ℝ) : ℝ :=
  2 * Real.pi * thetaCuspHawkingKMSDownShell kappa a omega

/-- Davies up-transition rate selected by the negative Bohr frequency. -/
def thetaCuspHawkingDaviesUpRate (kappa a omega : ℝ) : ℝ :=
  2 * Real.pi * thetaCuspHawkingKMSUpShell kappa a omega

/-- Exact two-state population generator of the Hawking Davies resonance block.
The first coordinate is ground population and the second is excited population. -/
def thetaCuspHawkingDaviesPopulationGenerator
    (kappa a omega : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (-thetaCuspHawkingDaviesUpRate kappa a omega * p.1 +
      thetaCuspHawkingDaviesDownRate kappa a omega * p.2,
    thetaCuspHawkingDaviesUpRate kappa a omega * p.1 -
      thetaCuspHawkingDaviesDownRate kappa a omega * p.2)

/-- Normalized Hawking Gibbs population at the selected Bohr frequency. -/
def thetaCuspHawkingDaviesGibbsPopulation
    (kappa omega : ℝ) : ℝ × ℝ :=
  let q := thetaCuspHawkingKMSBoltzmannRatio kappa omega
  (1 / (1 + q), q / (1 + q))

/-- Davies generator conserves total population. -/
theorem thetaCuspHawkingDaviesPopulationGenerator_mass
    (kappa a omega : ℝ) (p : ℝ × ℝ) :
    (thetaCuspHawkingDaviesPopulationGenerator kappa a omega p).1 +
        (thetaCuspHawkingDaviesPopulationGenerator kappa a omega p).2 = 0 := by
  simp only [thetaCuspHawkingDaviesPopulationGenerator]
  ring

/-- On-shell KMS detailed balance for the normalized Gibbs population. -/
theorem thetaCuspHawkingDavies_detailedBalance
    (kappa a omega : ℝ) :
    thetaCuspHawkingDaviesUpRate kappa a omega *
        (thetaCuspHawkingDaviesGibbsPopulation kappa omega).1 =
      thetaCuspHawkingDaviesDownRate kappa a omega *
        (thetaCuspHawkingDaviesGibbsPopulation kappa omega).2 := by
  simp only [thetaCuspHawkingDaviesUpRate, thetaCuspHawkingDaviesDownRate,
    thetaCuspHawkingDaviesGibbsPopulation,
    thetaCuspHawkingKMSUpShell_eq_ratio_mul_down]
  ring

/-- Hawking Gibbs population is stationary for the exact two-state level-shift generator. -/
theorem thetaCuspHawkingDaviesPopulationGenerator_gibbs
    (kappa a omega : ℝ) :
    thetaCuspHawkingDaviesPopulationGenerator kappa a omega
        (thetaCuspHawkingDaviesGibbsPopulation kappa omega) = 0 := by
  have hdb := thetaCuspHawkingDavies_detailedBalance kappa a omega
  apply Prod.ext
  · simp only [thetaCuspHawkingDaviesPopulationGenerator, Prod.fst_zero]
    linear_combination -hdb
  · simp only [thetaCuspHawkingDaviesPopulationGenerator, Prod.snd_zero]
    linear_combination hdb

/-- The unique mass-zero population direction has eigenvalue equal to minus the total KMS width. -/
theorem thetaCuspHawkingDaviesPopulationGenerator_imbalance :
    thetaCuspHawkingDaviesPopulationGenerator kappa a omega (1, -1) =
      (-thetaCuspHawkingKMSResonanceWidth kappa a omega,
        thetaCuspHawkingKMSResonanceWidth kappa a omega) := by
  apply Prod.ext <;>
    simp only [thetaCuspHawkingDaviesPopulationGenerator,
      thetaCuspHawkingDaviesDownRate, thetaCuspHawkingDaviesUpRate,
      thetaCuspHawkingKMSResonanceWidth]
  <;> ring

/-- Exact scalar flow of the transverse population mode. -/
def thetaCuspHawkingDaviesPopulationDeviationFlow
    (kappa a omega t c : ℝ) : ℝ :=
  Real.exp (-thetaCuspHawkingKMSResonanceWidth kappa a omega * t) * c

theorem thetaCuspHawkingDaviesPopulationDeviationFlow_zero
    (kappa a omega c : ℝ) :
    thetaCuspHawkingDaviesPopulationDeviationFlow kappa a omega 0 c = c := by
  simp [thetaCuspHawkingDaviesPopulationDeviationFlow]

/-- Transverse Davies evolution is a genuine one-parameter semigroup. -/
theorem thetaCuspHawkingDaviesPopulationDeviationFlow_add
    (kappa a omega t s c : ℝ) :
    thetaCuspHawkingDaviesPopulationDeviationFlow kappa a omega (t + s) c =
      thetaCuspHawkingDaviesPopulationDeviationFlow kappa a omega t
        (thetaCuspHawkingDaviesPopulationDeviationFlow kappa a omega s c) := by
  rw [thetaCuspHawkingDaviesPopulationDeviationFlow,
    thetaCuspHawkingDaviesPopulationDeviationFlow,
    thetaCuspHawkingDaviesPopulationDeviationFlow]
  rw [show -thetaCuspHawkingKMSResonanceWidth kappa a omega * (t + s) =
      -thetaCuspHawkingKMSResonanceWidth kappa a omega * t +
        -thetaCuspHawkingKMSResonanceWidth kappa a omega * s by ring,
    Real.exp_add]
  ring

/-- A resonance sector mixes when every transverse population deviation converges to zero. -/
def ThetaCuspHawkingDaviesSectorMixes
    (kappa a omega : ℝ) : Prop :=
  ∀ c : ℝ,
    Tendsto
      (fun t : ℝ =>
        thetaCuspHawkingDaviesPopulationDeviationFlow kappa a omega t c)
      atTop (𝓝 0)

/-- Exact mixing criterion for the Hawking Davies block: positive level-shift gap. -/
theorem thetaCuspHawkingDaviesSectorMixes_iff_width_pos
    {kappa a omega : ℝ} (hkappa : 0 < kappa) (homega : 0 < omega) :
    ThetaCuspHawkingDaviesSectorMixes kappa a omega ↔
      0 < thetaCuspHawkingKMSResonanceWidth kappa a omega := by
  constructor
  · intro hmix
    have hnonneg :=
      thetaCuspHawkingKMSResonanceWidth_nonneg (a := a) hkappa homega
    rcases hnonneg.eq_or_lt with hzero | hpos
    · have hzero' :
          thetaCuspHawkingKMSResonanceWidth kappa a omega = 0 := hzero.symm
      have hconst : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 0) := by
        simpa [thetaCuspHawkingDaviesPopulationDeviationFlow, hzero'] using hmix 1
      have hone : (1 : ℝ) = 0 := tendsto_const_nhds_iff.mp hconst
      norm_num at hone
    · exact hpos
  · intro hwidth c
    have hscale :
        Tendsto
          (fun t : ℝ => thetaCuspHawkingKMSResonanceWidth kappa a omega * t)
          atTop atTop :=
      Filter.Tendsto.const_mul_atTop hwidth tendsto_id
    have hexp := Real.tendsto_exp_neg_atTop_nhds_zero.comp hscale
    simpa [thetaCuspHawkingDaviesPopulationDeviationFlow] using hexp.mul_const c

/-- The actual Davies resonance sector mixes exactly away from a theta/Xi dark shell. -/
theorem thetaCuspHawkingDaviesSectorMixes_iff_XiC_ne_zero
    {kappa a omega : ℝ} (hkappa : 0 < kappa) (homega : 0 < omega) :
    ThetaCuspHawkingDaviesSectorMixes kappa a omega ↔
      XiC ((omega : ℂ) + (a : ℂ) * I) ≠ 0 := by
  rw [thetaCuspHawkingDaviesSectorMixes_iff_width_pos hkappa homega]
  constructor
  · intro hwidth hXi
    have hzero :=
      (thetaCuspHawkingKMSResonanceWidth_eq_zero_iff hkappa homega).2 hXi
    linarith
  · exact thetaCuspHawkingKMSResonanceWidth_pos_of_XiC_ne_zero hkappa homega

/-- Every positive-frequency, nonzero-tilt Hawking Davies resonance sector mixes. -/
def ThetaCuspHawkingArakiWoodsDaviesMixing : Prop :=
  ∀ (kappa a omega : ℝ), 0 < kappa → 0 < omega → |a| < 1 → a ≠ 0 →
    ThetaCuspHawkingDaviesSectorMixes kappa a omega

/-- **Source-faithful Hawking Araki--Woods/Davies endpoint.**  Mixing of every noncentral tilted
weak-coupling resonance sector is equivalent to RH.  Hawking thermality determines the doubled
couplings and detailed-balance generator; it does not supply strict positivity of the theta shell. -/
theorem riemannHypothesis_iff_thetaCuspHawkingArakiWoodsDaviesMixing :
    RiemannHypothesis ↔ ThetaCuspHawkingArakiWoodsDaviesMixing := by
  rw [riemannHypothesis_iff_XiC_zeros_real]
  constructor
  · intro hreal kappa a omega hkappa homega _ha hane
    rw [thetaCuspHawkingDaviesSectorMixes_iff_XiC_ne_zero hkappa homega]
    intro hXi
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
    · have hsector := hmix 1 (-z.im) (-z.re) (by norm_num) (by linarith)
          (by simpa using ha) (neg_ne_zero.mpr hzim)
      have hXiNe :=
        (thetaCuspHawkingDaviesSectorMixes_iff_XiC_ne_zero
          (by norm_num) (by linarith)).1 hsector
      apply hXiNe
      have harg :
          (((-z.re : ℝ) : ℂ) + ((-z.im : ℝ) : ℂ) * I) = -z := by
        apply Complex.ext <;> simp
      rw [harg, XiC_even]
      exact hz
    · have hsector := hmix 1 z.im z.re (by norm_num) hpos ha hzim
      have hXiNe :=
        (thetaCuspHawkingDaviesSectorMixes_iff_XiC_ne_zero
          (by norm_num) hpos).1 hsector
      apply hXiNe
      have harg : ((z.re : ℂ) + (z.im : ℂ) * I) = z := by
        apply Complex.ext <;> simp
      rwa [harg]

end RHTower
