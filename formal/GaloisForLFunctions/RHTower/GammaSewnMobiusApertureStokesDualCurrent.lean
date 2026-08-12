import GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesKotheVectorLandingNoGo

/-!
# Gamma-sewn Stokes current in the Köthe dual

The actual Gamma-sewn aperture feature is not a rapid test vector.  It is instead a continuous
coefficient functional on the nuclear height-Köthe source.  The transpose of the P-G61 Stokes
connection sends this physical dual feature exactly to the von Mangoldt Euler current, coordinate
by coordinate on every prime-power axis.

This realizes the P-G60 cancellation inside the forced rigged-source direction `K_H -> K_H'`.
No Xi zero, target response, positivity premise, or RH-equivalent hypothesis enters the current.
-/

open Complex Filter Topology
open scoped BigOperators

noncomputable section

namespace RHTower

/-- Positive prime-power axis inside the Kummer lattice. -/
def gammaSewnMobiusApertureStokesPrimePowerAxis
    (pk : Nat.Primes × ℕ) : DeningerPrimeLattice :=
  Finsupp.single pk.1 (Int.ofNat (pk.2 + 1))

theorem gammaSewnMobiusApertureStokesPrimePowerAxis_injective :
    Function.Injective gammaSewnMobiusApertureStokesPrimePowerAxis := by
  rintro ⟨p, e⟩ ⟨q, f⟩ h
  simp only [gammaSewnMobiusApertureStokesPrimePowerAxis] at h
  rcases (Finsupp.single_eq_single_iff p q
      (Int.ofNat (e + 1)) (Int.ofNat (f + 1))).mp h with hmain | hzero
  · rcases hmain with ⟨hp, hef⟩
    subst q
    have hef' : e + 1 = f + 1 := Int.ofNat.inj hef
    congr
    exact Nat.add_right_cancel hef'
  · exfalso
    exact (Int.ofNat_ne_zero.mpr (Nat.succ_ne_zero e)) hzero.1

/-- The signed Kummer frequency restricts to valuation times the prime inverse tilt. -/
theorem gammaSewnMobiusApertureStokesKotheFrequency_primePowerAxis
    (s : ℝ) (pk : Nat.Primes × ℕ) :
    gammaSewnMobiusApertureStokesKotheFrequency s
        (gammaSewnMobiusApertureStokesPrimePowerAxis pk) =
      (pk.2 + 1 : ℝ) *
        gammaSewnMobiusApertureStokesInverseTilt s pk.1 := by
  rcases pk with ⟨p, e⟩
  rw [gammaSewnMobiusApertureStokesKotheFrequency,
    gammaSewnMobiusApertureStokesPrimePowerAxis,
    Finsupp.sum_single_index]
  · norm_cast
  · simp

/-- Physical pre-Gram dual coefficient.  Division by valuation compensates the additive Kummer
frequency so transpose multiplication recovers one coefficient, not `e+1` copies. -/
def gammaSewnMobiusApertureStokesDualFeatureCoefficient
    (s : ℝ) (pk : Nat.Primes × ℕ) : ℝ :=
  gammaSewnMobiusContinuousApertureFeature s pk.1 pk.2 / (pk.2 + 1)

/-- Physical dual coefficients are nonnegative and uniformly at most one on positive aperture. -/
theorem gammaSewnMobiusApertureStokesDualFeatureCoefficient_mem_unit
    {s : ℝ} (hs : 0 < s) (pk : Nat.Primes × ℕ) :
    0 ≤ gammaSewnMobiusApertureStokesDualFeatureCoefficient s pk ∧
      gammaSewnMobiusApertureStokesDualFeatureCoefficient s pk ≤ 1 := by
  rcases pk with ⟨p, e⟩
  let q := xiTransversePrimeApertureDiskNode 1 p
  let r := xiMobiusContinuousApertureDiskNode s p
  let c := gammaSewnMobiusValuationContractionMultiplier s p
  have hq0 : 0 < q := xiTransversePrimeApertureDiskNode_pos 1 p
  have hr0 : 0 < r := xiMobiusContinuousApertureDiskNode_pos s p
  have hr1 : r < 1 := xiMobiusContinuousApertureDiskNode_lt_one hs p
  have hc0 : 0 < c := gammaSewnMobiusValuationContractionMultiplier_pos s p
  have hc1 : c < 1 :=
    gammaSewnMobiusValuationContractionMultiplier_lt_one hs p
  have hqfrac : 0 < q / (1 + q) ∧ q / (1 + q) < 1 := by
    constructor
    · positivity
    · rw [div_lt_one (by linarith : 0 < 1 + q)]
      linarith
  have hrpow : 0 ≤ r ^ e ∧ r ^ e ≤ 1 := by
    exact ⟨pow_nonneg hr0.le _, pow_le_one₀ hr0.le hr1.le⟩
  have hfeature0 : 0 ≤ gammaSewnMobiusContinuousApertureFeature s p e := by
    rw [gammaSewnMobiusContinuousApertureFeature,
      xiMobiusPrimeSchurContinuousForwardDifference_eq_geometric]
    positivity
  have hfeature1 : gammaSewnMobiusContinuousApertureFeature s p e ≤ 1 := by
    rw [gammaSewnMobiusContinuousApertureFeature,
      xiMobiusPrimeSchurContinuousForwardDifference_eq_geometric]
    change c * (q / (1 + q) * (1 - r) * r ^ e) ≤ 1
    have hinner0 : 0 ≤ q / (1 + q) * (1 - r) * r ^ e := by positivity
    have hinner1 : q / (1 + q) * (1 - r) * r ^ e ≤ 1 := by
      calc
        q / (1 + q) * (1 - r) * r ^ e
            ≤ 1 * 1 * 1 := by gcongr <;> linarith
        _ = 1 := by ring
    nlinarith
  rw [gammaSewnMobiusApertureStokesDualFeatureCoefficient]
  constructor
  · positivity
  · rw [div_le_one (by positivity : (0 : ℝ) < e + 1)]
    exact hfeature1.trans (by norm_num)

/-- The actual aperture edge as a continuous dual pairing on the rapid test source. -/
def gammaSewnMobiusApertureStokesDualFeaturePairing
    (s : ℝ) (a : DeningerHeightKothe) : ℂ :=
  ∑' pk : Nat.Primes × ℕ,
    (gammaSewnMobiusApertureStokesDualFeatureCoefficient s pk : ℂ) *
      (a : DeningerPrimeLattice → ℂ)
        (gammaSewnMobiusApertureStokesPrimePowerAxis pk)

theorem summable_gammaSewnMobiusApertureStokesDualFeaturePairing
    {s : ℝ} (hs : 0 < s) (a : DeningerHeightKothe) :
    Summable (fun pk : Nat.Primes × ℕ =>
      (gammaSewnMobiusApertureStokesDualFeatureCoefficient s pk : ℂ) *
        (a : DeningerPrimeLattice → ℂ)
          (gammaSewnMobiusApertureStokesPrimePowerAxis pk)) := by
  have hbase : Summable (fun pk : Nat.Primes × ℕ =>
      ‖(a : DeningerPrimeLattice → ℂ)
        (gammaSewnMobiusApertureStokesPrimePowerAxis pk)‖) :=
    (deningerHeightKothe_summable_norm a).comp_injective
      gammaSewnMobiusApertureStokesPrimePowerAxis_injective
  refine Summable.of_norm_bounded hbase fun pk => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg
      (gammaSewnMobiusApertureStokesDualFeatureCoefficient_mem_unit hs pk).1]
  exact mul_le_of_le_one_left (norm_nonneg _)
    (gammaSewnMobiusApertureStokesDualFeatureCoefficient_mem_unit hs pk).2

/-- Continuity bound of the physical dual feature against the zeroth height seminorm. -/
theorem norm_gammaSewnMobiusApertureStokesDualFeaturePairing_le
    {s : ℝ} (hs : 0 < s) (a : DeningerHeightKothe) :
    ‖gammaSewnMobiusApertureStokesDualFeaturePairing s a‖ ≤
      deningerHeightSeminorm 0 a := by
  have hpair := summable_gammaSewnMobiusApertureStokesDualFeaturePairing hs a
  have haxis : Summable (fun pk : Nat.Primes × ℕ =>
      ‖(a : DeningerPrimeLattice → ℂ)
        (gammaSewnMobiusApertureStokesPrimePowerAxis pk)‖) :=
    (deningerHeightKothe_summable_norm a).comp_injective
      gammaSewnMobiusApertureStokesPrimePowerAxis_injective
  calc
    ‖gammaSewnMobiusApertureStokesDualFeaturePairing s a‖
        ≤ ∑' pk : Nat.Primes × ℕ,
          ‖(gammaSewnMobiusApertureStokesDualFeatureCoefficient s pk : ℂ) *
            (a : DeningerPrimeLattice → ℂ)
              (gammaSewnMobiusApertureStokesPrimePowerAxis pk)‖ :=
      norm_tsum_le_tsum_norm hpair.norm
    _ ≤ ∑' pk : Nat.Primes × ℕ,
        ‖(a : DeningerPrimeLattice → ℂ)
          (gammaSewnMobiusApertureStokesPrimePowerAxis pk)‖ := by
      refine Summable.tsum_le_tsum (fun pk => ?_) hpair.norm haxis
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg
          (gammaSewnMobiusApertureStokesDualFeatureCoefficient_mem_unit hs pk).1]
      exact mul_le_of_le_one_left (norm_nonneg _)
        (gammaSewnMobiusApertureStokesDualFeatureCoefficient_mem_unit hs pk).2
    _ ≤ ∑' m : DeningerPrimeLattice,
        ‖(a : DeningerPrimeLattice → ℂ) m‖ := by
      exact haxis.tsum_le_tsum_of_inj
        gammaSewnMobiusApertureStokesPrimePowerAxis
        gammaSewnMobiusApertureStokesPrimePowerAxis_injective
        (fun _ _ => norm_nonneg _) (fun _ => le_rfl)
        (deningerHeightKothe_summable_norm a)
    _ = deningerHeightSeminorm 0 a :=
      (deningerHeightSeminorm_zero_eq a).symm

/-- Safe Euler dual current, observed on a rapid Kummer test vector. -/
def gammaSewnMobiusApertureStokesEulerDualPairing
    (s : ℝ) (a : DeningerHeightKothe) : ℂ :=
  ∑' pk : Nat.Primes × ℕ,
    primePowerFluxTerm (s : ℂ) pk *
      (a : DeningerPrimeLattice → ℂ)
        (gammaSewnMobiusApertureStokesPrimePowerAxis pk)

/-- **Exact transpose Stokes law.**  Acting on tests and then evaluating the actual physical dual
feature is coefficientwise identical to the safe von Mangoldt Euler current. -/
theorem gammaSewnMobiusApertureStokesDualFeaturePairing_operator_eq_euler
    {s : ℝ} (hs : 1 ≤ s) (a : DeningerHeightKothe) :
    gammaSewnMobiusApertureStokesDualFeaturePairing s
        (gammaSewnMobiusApertureStokesKotheOperator s hs a) =
      gammaSewnMobiusApertureStokesEulerDualPairing s a := by
  rw [gammaSewnMobiusApertureStokesDualFeaturePairing,
    gammaSewnMobiusApertureStokesEulerDualPairing]
  refine tsum_congr fun pk => ?_
  rw [gammaSewnMobiusApertureStokesKotheOperator_coe hs,
    gammaSewnMobiusApertureStokesKotheFrequency_primePowerAxis]
  have hn : ((pk.2 + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hcancel :
      gammaSewnMobiusApertureStokesDualFeatureCoefficient s pk *
          ((pk.2 + 1 : ℝ) *
            gammaSewnMobiusApertureStokesInverseTilt s pk.1) =
        gammaSewnMobiusApertureStokesInverseTilt s pk.1 *
          (gammaSewnMobiusContinuousApertureFeature s pk.1 pk.2 -
            gammaSewnMobiusContinuousApertureFeature 0 pk.1 pk.2) := by
    rw [gammaSewnMobiusApertureStokesDualFeatureCoefficient,
      gammaSewnMobiusContinuousApertureFeature_zero, sub_zero]
    field_simp [hn]
  have hflux :
      ((gammaSewnMobiusApertureStokesDualFeatureCoefficient s pk *
          ((pk.2 + 1 : ℝ) *
            gammaSewnMobiusApertureStokesInverseTilt s pk.1) : ℝ) : ℂ) =
        primePowerFluxTerm (s : ℂ) pk := by
    rw [hcancel]
    exact gammaSewnMobiusApertureStokesFluxTerm_eq (by linarith) pk
  rw [← mul_assoc, ← ofReal_mul, hflux]

/-- The total mass of the transposed dual current is the complete Euler flux. -/
theorem tsum_gammaSewnMobiusApertureStokesEulerDualCoefficient
    {s : ℝ} (hs : 1 < s) :
    ∑' pk : Nat.Primes × ℕ, primePowerFluxTerm (s : ℂ) pk =
      infinitePrimeFlux (s : ℂ) :=
  tsum_primePowerFluxTerm (by simpa)

end RHTower
