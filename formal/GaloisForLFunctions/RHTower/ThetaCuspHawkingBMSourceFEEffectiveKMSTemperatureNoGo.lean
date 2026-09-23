import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSourceFELocalCylinderProductState
import GaloisForLFunctions.RHTower.ThetaCuspHawkingArakiWoodsDaviesMixingEndpoint

/-!
# Source-FE effective Hawking-KMS temperature no-go

HC84 leaves one sharp physical question: can ordinary Hawking KMS/Davies equilibrium force its
local pair-product state to be vacuum and hence force RH? This module proves the opposite.

The literal source recurrence ratio has squared norm strictly below `1/2`. Off wall it is positive,
so the explicit surface gravity `κ_eff = -2π / log ‖r‖²` is positive and its unit-frequency Hawking
Boltzmann ratio is exactly `‖r‖²`. The HC84 local population then equals the normalized Hawking Gibbs
population. It is stationary and detailed-balanced for every corpus Davies shell coupling.

Thus positive-temperature KMS equilibrium realizes every off-wall source local state; it cannot
select the wall. Conversely, every positive-temperature Gibbs state has strictly positive excited
population, so route-receiver zero/local vacuum is incompatible with finite-temperature Gibbs
identification. Viable producers require a ground-state limit, source-faithful same-sector
alignment, or a phase-sensitive Ward/centralizer law beyond ordinary detailed balance.

`[NEW] [KMS NO-GO] [EXACT EFFECTIVE TEMPERATURE] [DAVIES STATIONARY] [ROUTE KILL]`
-/

open Complex Real Filter Topology

namespace RHTower

noncomputable section

/-- Positive surface gravity whose unit-frequency Hawking ratio is `Q`. -/
def hawkingEffectiveKappa (Q : ℝ) : ℝ :=
  -(2 * Real.pi) / Real.log Q

theorem hawkingEffectiveKappa_pos
    {Q : ℝ} (hQ0 : 0 < Q) (hQ1 : Q < 1) :
    0 < hawkingEffectiveKappa Q := by
  rw [hawkingEffectiveKappa]
  exact div_pos_of_neg_of_neg (neg_neg_of_pos (by positivity))
    (Real.log_neg hQ0 hQ1)

theorem thetaCuspHawkingKMSBoltzmannRatio_effectiveKappa
    {Q : ℝ} (hQ0 : 0 < Q) (hQ1 : Q < 1) :
    thetaCuspHawkingKMSBoltzmannRatio (hawkingEffectiveKappa Q) 1 = Q := by
  rw [thetaCuspHawkingKMSBoltzmannRatio, hawkingEffectiveKappa]
  rw [show -(2 * Real.pi * 1 / (-(2 * Real.pi) / Real.log Q)) = Real.log Q by
    field_simp [Real.pi_ne_zero, (Real.log_neg hQ0 hQ1).ne]]
  exact Real.exp_log hQ0

/-- Exact squared recurrence ratio in terms of source orbit gain. -/
theorem norm_hbXiPeierlsUnitSourceFEFockVacuumPairRatio_sq
    (q : XiZeroCopy) :
    ‖hbXiPeierlsUnitSourceFEFockVacuumPairRatio q‖ ^ (2 : ℕ) =
      hbXiPeierlsUnitSourceFEOrbitPartnerNumber q /
        (2 * hbXiPeierlsUnitSourceFEOrbitExpandingGain q) := by
  rw [hbXiPeierlsUnitSourceFEFockVacuumPairRatio,
    norm_div, norm_neg, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg 2),
    abs_of_pos (hbXiPeierlsUnitSourceFEOrbitBogoliubovGain_pos q),
    div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
    hbXiPeierlsUnitSourceFEOrbitBogoliubovGain_sq,
    norm_hbXiPeierlsUnitSourceFEOrbitBogoliubovPair_sq]

theorem norm_hbXiPeierlsUnitSourceFEFockVacuumPairRatio_sq_nonneg
    (q : XiZeroCopy) :
    0 ≤ ‖hbXiPeierlsUnitSourceFEFockVacuumPairRatio q‖ ^ (2 : ℕ) :=
  sq_nonneg _

/-- Source normalization puts every effective thermal ratio strictly below one half. -/
theorem norm_hbXiPeierlsUnitSourceFEFockVacuumPairRatio_sq_lt_half
    (q : XiZeroCopy) :
    ‖hbXiPeierlsUnitSourceFEFockVacuumPairRatio q‖ ^ (2 : ℕ) < 1 / 2 := by
  rw [norm_hbXiPeierlsUnitSourceFEFockVacuumPairRatio_sq]
  have hgain : 0 < hbXiPeierlsUnitSourceFEOrbitExpandingGain q :=
    lt_of_lt_of_le zero_lt_one
      (hbXiPeierlsUnitSourceFEOrbitExpandingGain_ge_one q)
  apply (div_lt_iff₀ (by positivity :
    0 < 2 * hbXiPeierlsUnitSourceFEOrbitExpandingGain q)).2
  rw [hbXiPeierlsUnitSourceFEOrbitPartnerNumber]
  nlinarith

theorem norm_hbXiPeierlsUnitSourceFEFockVacuumPairRatio_sq_lt_one
    (q : XiZeroCopy) :
    ‖hbXiPeierlsUnitSourceFEFockVacuumPairRatio q‖ ^ (2 : ℕ) < 1 := by
  linarith [norm_hbXiPeierlsUnitSourceFEFockVacuumPairRatio_sq_lt_half q]

/-- Effective thermal ratio is strictly positive exactly off the critical wall. -/
theorem norm_hbXiPeierlsUnitSourceFEFockVacuumPairRatio_sq_pos_iff
    (q : XiZeroCopy) :
    0 < ‖hbXiPeierlsUnitSourceFEFockVacuumPairRatio q‖ ^ (2 : ℕ) ↔
      (q.1 : ℂ).re ≠ 1 / 2 := by
  constructor
  · intro hpos hline
    have hrzero : hbXiPeierlsUnitSourceFEFockVacuumPairRatio q = 0 :=
      (hbXiPeierlsUnitSourceFEFockVacuumPairRatio_eq_zero_iff_pair_eq_zero q).2
        ((hbXiPeierlsUnitSourceFEOrbitBogoliubovPair_eq_zero_iff_partnerNumber_eq_zero q).2
          ((hbXiPeierlsUnitSourceFEOrbitPartnerNumber_eq_zero_iff q).2 hline))
    rw [hrzero, norm_zero] at hpos
    norm_num at hpos
  · intro hline
    have hrne : hbXiPeierlsUnitSourceFEFockVacuumPairRatio q ≠ 0 :=
      (hbXiPeierlsUnitSourceFEFockVacuumPairRatio_eq_zero_iff_pair_eq_zero q).not.mpr
        ((hbXiPeierlsUnitSourceFEOrbitBogoliubovPair_eq_zero_iff_partnerNumber_eq_zero q).not.mpr
          ((hbXiPeierlsUnitSourceFEOrbitPartnerNumber_eq_zero_iff q).not.mpr hline))
    exact sq_pos_of_pos (norm_pos_iff.mpr hrne)

/-- Effective surface gravity of an off-wall source local product state. -/
def hbXiPeierlsUnitSourceFEEffectiveKMSKappa (q : XiZeroCopy) : ℝ :=
  hawkingEffectiveKappa
    (‖hbXiPeierlsUnitSourceFEFockVacuumPairRatio q‖ ^ (2 : ℕ))

theorem hbXiPeierlsUnitSourceFEEffectiveKMSKappa_pos
    (q : XiZeroCopy) (hq : (q.1 : ℂ).re ≠ 1 / 2) :
    0 < hbXiPeierlsUnitSourceFEEffectiveKMSKappa q := by
  exact hawkingEffectiveKappa_pos
    ((norm_hbXiPeierlsUnitSourceFEFockVacuumPairRatio_sq_pos_iff q).2 hq)
    (norm_hbXiPeierlsUnitSourceFEFockVacuumPairRatio_sq_lt_one q)

/-- At unit frequency the effective Hawking Boltzmann ratio is the exact source pair ratio. -/
theorem thetaCuspHawkingKMSBoltzmannRatio_sourceFE_effectiveKappa
    (q : XiZeroCopy) (hq : (q.1 : ℂ).re ≠ 1 / 2) :
    thetaCuspHawkingKMSBoltzmannRatio
        (hbXiPeierlsUnitSourceFEEffectiveKMSKappa q) 1 =
      ‖hbXiPeierlsUnitSourceFEFockVacuumPairRatio q‖ ^ (2 : ℕ) := by
  exact thetaCuspHawkingKMSBoltzmannRatio_effectiveKappa
    ((norm_hbXiPeierlsUnitSourceFEFockVacuumPairRatio_sq_pos_iff q).2 hq)
    (norm_hbXiPeierlsUnitSourceFEFockVacuumPairRatio_sq_lt_one q)

/-- A pair-product local population is the two-state Hawking Gibbs population whenever its squared
pair ratio is the KMS detailed-balance ratio. -/
theorem finitePairFockLocalPopulation_eq_hawkingDaviesGibbsPopulation
    (r : ℂ) (kappa omega : ℝ)
    (hthermal : thetaCuspHawkingKMSBoltzmannRatio kappa omega = ‖r‖ ^ (2 : ℕ)) :
    (1 - finitePairFockOccupationDensity r, finitePairFockOccupationDensity r) =
      thetaCuspHawkingDaviesGibbsPopulation kappa omega := by
  rw [finitePairFockOccupationDensity_eq_div]
  apply Prod.ext
  · simp only [thetaCuspHawkingDaviesGibbsPopulation]
    rw [hthermal]
    have hden : (1 + ‖r‖ ^ (2 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  · simp [thetaCuspHawkingDaviesGibbsPopulation, hthermal]

/-- Every off-wall source local population is exactly a positive-temperature Hawking Gibbs state. -/
theorem hbXiPeierlsUnitSourceFELocalPopulation_eq_effectiveHawkingDaviesGibbs
    (q : XiZeroCopy) (hq : (q.1 : ℂ).re ≠ 1 / 2) :
    (1 - hbXiPeierlsUnitSourceFELocalPairDensity q,
        hbXiPeierlsUnitSourceFELocalPairDensity q) =
      thetaCuspHawkingDaviesGibbsPopulation
        (hbXiPeierlsUnitSourceFEEffectiveKMSKappa q) 1 := by
  exact finitePairFockLocalPopulation_eq_hawkingDaviesGibbsPopulation
    (hbXiPeierlsUnitSourceFEFockVacuumPairRatio q)
    (hbXiPeierlsUnitSourceFEEffectiveKMSKappa q) 1
    (thetaCuspHawkingKMSBoltzmannRatio_sourceFE_effectiveKappa q hq)

/-- Every off-wall source local state is stationary for every exact Davies shell coupling. -/
theorem thetaCuspHawkingDaviesPopulationGenerator_sourceFELocalPopulation
    (q : XiZeroCopy) (hq : (q.1 : ℂ).re ≠ 1 / 2) (a : ℝ) :
    thetaCuspHawkingDaviesPopulationGenerator
        (hbXiPeierlsUnitSourceFEEffectiveKMSKappa q) a 1
        (1 - hbXiPeierlsUnitSourceFELocalPairDensity q,
          hbXiPeierlsUnitSourceFELocalPairDensity q) = 0 := by
  rw [hbXiPeierlsUnitSourceFELocalPopulation_eq_effectiveHawkingDaviesGibbs q hq]
  exact thetaCuspHawkingDaviesPopulationGenerator_gibbs _ _ _

/-- Every off-wall source local state obeys exact Hawking up/down detailed balance. -/
theorem thetaCuspHawkingDavies_sourceFELocalPopulation_detailedBalance
    (q : XiZeroCopy) (hq : (q.1 : ℂ).re ≠ 1 / 2) (a : ℝ) :
    thetaCuspHawkingDaviesUpRate
        (hbXiPeierlsUnitSourceFEEffectiveKMSKappa q) a 1 *
        (1 - hbXiPeierlsUnitSourceFELocalPairDensity q) =
      thetaCuspHawkingDaviesDownRate
        (hbXiPeierlsUnitSourceFEEffectiveKMSKappa q) a 1 *
        hbXiPeierlsUnitSourceFELocalPairDensity q := by
  have hpop :=
    hbXiPeierlsUnitSourceFELocalPopulation_eq_effectiveHawkingDaviesGibbs q hq
  have hdb := thetaCuspHawkingDavies_detailedBalance
    (hbXiPeierlsUnitSourceFEEffectiveKMSKappa q) a 1
  rw [Prod.ext_iff] at hpop
  have hfst : 1 - hbXiPeierlsUnitSourceFELocalPairDensity q =
      (thetaCuspHawkingDaviesGibbsPopulation
        (hbXiPeierlsUnitSourceFEEffectiveKMSKappa q) 1).1 := by
    simpa only [Prod.fst] using hpop.1
  have hsnd : hbXiPeierlsUnitSourceFELocalPairDensity q =
      (thetaCuspHawkingDaviesGibbsPopulation
        (hbXiPeierlsUnitSourceFEEffectiveKMSKappa q) 1).2 := by
    simpa only [Prod.snd] using hpop.2
  rw [hfst, hsnd]
  exact hdb

/-- Positive-temperature Gibbs equilibrium has strictly positive excited population. -/
theorem thetaCuspHawkingDaviesGibbsPopulation_snd_pos
    {kappa omega : ℝ} (_hkappa : 0 < kappa) (_homega : 0 < omega) :
    0 < (thetaCuspHawkingDaviesGibbsPopulation kappa omega).2 := by
  rw [thetaCuspHawkingDaviesGibbsPopulation]
  have hq := thetaCuspHawkingKMSBoltzmannRatio_pos kappa omega
  exact div_pos hq (by linarith)

/-- A source local vacuum cannot equal any finite positive-temperature Gibbs population. -/
theorem hbXiPeierlsUnitSourceFELocalVacuum_ne_hawkingDaviesGibbsPopulation
    (q : XiZeroCopy) (hq : hbXiPeierlsUnitSourceFELocalPairDensity q = 0)
    {kappa omega : ℝ} (hkappa : 0 < kappa) (homega : 0 < omega) :
    (1 - hbXiPeierlsUnitSourceFELocalPairDensity q,
        hbXiPeierlsUnitSourceFELocalPairDensity q) ≠
      thetaCuspHawkingDaviesGibbsPopulation kappa omega := by
  intro heq
  have hsnd := congrArg Prod.snd heq
  rw [hq] at hsnd
  linarith [thetaCuspHawkingDaviesGibbsPopulation_snd_pos hkappa homega]

/-- Positive-temperature identification of the source local population forces the copy off wall,
the opposite of the local-vacuum/RH endpoint. -/
theorem hbXiPeierlsUnitSourceFE_re_ne_half_of_localPopulation_eq_hawkingDaviesGibbs
    (q : XiZeroCopy) {kappa omega : ℝ}
    (hkappa : 0 < kappa) (homega : 0 < omega)
    (heq :
      (1 - hbXiPeierlsUnitSourceFELocalPairDensity q,
          hbXiPeierlsUnitSourceFELocalPairDensity q) =
        thetaCuspHawkingDaviesGibbsPopulation kappa omega) :
    (q.1 : ℂ).re ≠ 1 / 2 := by
  intro hline
  have hzero :=
    (hbXiPeierlsUnitSourceFELocalPairDensity_eq_zero_iff_re_eq_half q).2 hline
  exact (hbXiPeierlsUnitSourceFELocalVacuum_ne_hawkingDaviesGibbsPopulation
    q hzero hkappa homega) heq

/-- Every off-wall source state has one explicit positive-temperature Davies realization, with
stationarity and detailed balance at every shell coupling. -/
def HBXiPeierlsUnitSourceFEOffWallDaviesEquilibriumRealizable : Prop :=
  ∀ q : XiZeroCopy, (q.1 : ℂ).re ≠ 1 / 2 →
    0 < hbXiPeierlsUnitSourceFEEffectiveKMSKappa q ∧
      (1 - hbXiPeierlsUnitSourceFELocalPairDensity q,
          hbXiPeierlsUnitSourceFELocalPairDensity q) =
        thetaCuspHawkingDaviesGibbsPopulation
          (hbXiPeierlsUnitSourceFEEffectiveKMSKappa q) 1 ∧
      ∀ a : ℝ,
        thetaCuspHawkingDaviesPopulationGenerator
            (hbXiPeierlsUnitSourceFEEffectiveKMSKappa q) a 1
            (1 - hbXiPeierlsUnitSourceFELocalPairDensity q,
              hbXiPeierlsUnitSourceFELocalPairDensity q) = 0 ∧
          thetaCuspHawkingDaviesUpRate
              (hbXiPeierlsUnitSourceFEEffectiveKMSKappa q) a 1 *
              (1 - hbXiPeierlsUnitSourceFELocalPairDensity q) =
            thetaCuspHawkingDaviesDownRate
              (hbXiPeierlsUnitSourceFEEffectiveKMSKappa q) a 1 *
              hbXiPeierlsUnitSourceFELocalPairDensity q

theorem hbXiPeierlsUnitSourceFEOffWallDaviesEquilibriumRealizable :
    HBXiPeierlsUnitSourceFEOffWallDaviesEquilibriumRealizable := by
  intro q hq
  refine ⟨hbXiPeierlsUnitSourceFEEffectiveKMSKappa_pos q hq,
    hbXiPeierlsUnitSourceFELocalPopulation_eq_effectiveHawkingDaviesGibbs q hq, ?_⟩
  intro a
  exact ⟨thetaCuspHawkingDaviesPopulationGenerator_sourceFELocalPopulation q hq a,
    thetaCuspHawkingDavies_sourceFELocalPopulation_detailedBalance q hq a⟩

/-- HB optical darkness is incompatible with finite-positive-temperature Gibbs identification. -/
theorem hbXiPeierlsUnitSourceFE_opticalPower_zero_localPopulation_ne_hawkingDaviesGibbs
    (n : ℕ) (q : XiZeroCopy)
    (hopt : hbXiPeierlsFESchwarzCanonicalOrbitOpticalPower n q = 0)
    {kappa omega : ℝ} (hkappa : 0 < kappa) (homega : 0 < omega) :
    (1 - hbXiPeierlsUnitSourceFELocalPairDensity q,
        hbXiPeierlsUnitSourceFELocalPairDensity q) ≠
      thetaCuspHawkingDaviesGibbsPopulation kappa omega :=
  hbXiPeierlsUnitSourceFELocalVacuum_ne_hawkingDaviesGibbsPopulation q
    ((hbXiPeierlsUnitSourceFELocalPairDensity_eq_zero_iff_opticalPower_zero n q).2 hopt)
    hkappa homega

/-- Deninger Ward cancellation is incompatible with finite-positive-temperature Gibbs
identification. -/
theorem hbXiPeierlsUnitSourceFE_sharedWardCharge_zero_localPopulation_ne_hawkingDaviesGibbs
    (n : ℕ) (q : XiZeroCopy)
    (hward : fzzCigarParityDeningerReflectGaugeWardCharge q = 0)
    {kappa omega : ℝ} (hkappa : 0 < kappa) (homega : 0 < omega) :
    (1 - hbXiPeierlsUnitSourceFELocalPairDensity q,
        hbXiPeierlsUnitSourceFELocalPairDensity q) ≠
      thetaCuspHawkingDaviesGibbsPopulation kappa omega :=
  hbXiPeierlsUnitSourceFELocalVacuum_ne_hawkingDaviesGibbsPopulation q
    ((hbXiPeierlsUnitSourceFELocalPairDensity_eq_zero_iff_sharedWardCharge_zero n q).2 hward)
    hkappa homega

/-- FZZ-P information equilibrium is incompatible with finite-positive-temperature Gibbs
identification. -/
theorem hbXiPeierlsUnitSourceFE_informationForce_zero_localPopulation_ne_hawkingDaviesGibbs
    (n : ℕ) (q : XiZeroCopy)
    (hinfo : fzzCigarParityReflectedFermiInformationForce
      (deningerDivisorThetaEigen q).re = 0)
    {kappa omega : ℝ} (hkappa : 0 < kappa) (homega : 0 < omega) :
    (1 - hbXiPeierlsUnitSourceFELocalPairDensity q,
        hbXiPeierlsUnitSourceFELocalPairDensity q) ≠
      thetaCuspHawkingDaviesGibbsPopulation kappa omega :=
  hbXiPeierlsUnitSourceFELocalVacuum_ne_hawkingDaviesGibbsPopulation q
    ((hbXiPeierlsUnitSourceFELocalPairDensity_eq_zero_iff_informationForce_zero n q).2 hinfo)
    hkappa homega

/-- PW-B balance is incompatible with finite-positive-temperature Gibbs identification. -/
theorem hbXiPeierlsUnitSourceFE_pwBalance_zero_localPopulation_ne_hawkingDaviesGibbs
    (n : ℕ) (q : XiZeroCopy) (k : ℕ)
    (hpw : schwarzschildParikhWilczekBorelPartnerRealImbalance
      (deningerDivisorThetaEigen q) k = 0)
    {kappa omega : ℝ} (hkappa : 0 < kappa) (homega : 0 < omega) :
    (1 - hbXiPeierlsUnitSourceFELocalPairDensity q,
        hbXiPeierlsUnitSourceFELocalPairDensity q) ≠
      thetaCuspHawkingDaviesGibbsPopulation kappa omega :=
  hbXiPeierlsUnitSourceFELocalVacuum_ne_hawkingDaviesGibbsPopulation q
    ((hbXiPeierlsUnitSourceFELocalPairDensity_eq_zero_iff_pwBalance_zero n q k).2 hpw)
    hkappa homega

/-- Canonical-copy RBH balance is incompatible with finite-positive-temperature Gibbs
identification. -/
theorem hbXiPeierlsUnitSourceFE_rbhBalance_zero_localPopulation_ne_hawkingDaviesGibbs
    (n : ℕ) (rho : XiDivisorSupport)
    (hrbh : reflectedBiHeatMultiplicityLeadingJetNormImbalance rho = 0)
    {kappa omega : ℝ} (hkappa : 0 < kappa) (homega : 0 < omega) :
    (1 - hbXiPeierlsUnitSourceFELocalPairDensity
        (reflectedBiHeatFirstDivisorCopy rho),
      hbXiPeierlsUnitSourceFELocalPairDensity
        (reflectedBiHeatFirstDivisorCopy rho)) ≠
      thetaCuspHawkingDaviesGibbsPopulation kappa omega :=
  hbXiPeierlsUnitSourceFELocalVacuum_ne_hawkingDaviesGibbsPopulation
    (reflectedBiHeatFirstDivisorCopy rho)
    ((hbXiPeierlsUnitSourceFELocalPairDensity_firstCopy_eq_zero_iff_rbhBalance_zero n rho).2 hrbh)
    hkappa homega

end

end RHTower
