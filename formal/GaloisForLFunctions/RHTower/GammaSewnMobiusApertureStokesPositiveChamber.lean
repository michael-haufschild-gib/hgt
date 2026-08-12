import GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesDualCurrent

/-!
# Gamma-sewn Stokes current across the full positive chamber

The Euler line `s = 1` is not a boundary of the nuclear source.  For every fixed real `s > 0`,
the inverse tilt has at most one extra prime factor of growth.  Its full Kummer frequency is
therefore a two-step height multiplier.  The transpose law continues the von Mangoldt current as a
continuous functional on rapid tests throughout the whole positive real chamber, even where its
total mass no longer converges.

No analytic continuation of zeta, Xi divisor, positivity premise, or RH-equivalent hypothesis is
used in this source continuation.
-/

open Complex Filter Topology
open scoped BigOperators

noncomputable section

namespace RHTower

open GaloisForLFunctions

/-- Aperture-dependent loss constant for the full positive chamber. -/
def gammaSewnMobiusApertureStokesPositiveChamberConstant (s : ℝ) : ℝ :=
  4 / (1 - Real.exp (-s * Real.log 2))

theorem gammaSewnMobiusApertureStokesPositiveChamberConstant_pos
    {s : ℝ} (hs : 0 < s) :
    0 < gammaSewnMobiusApertureStokesPositiveChamberConstant s := by
  rw [gammaSewnMobiusApertureStokesPositiveChamberConstant]
  apply div_pos (by norm_num)
  rw [sub_pos, Real.exp_lt_one_iff]
  nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]

/-- Below the Euler line the inverse tilt grows, but by at most one prime factor. -/
theorem gammaSewnMobiusApertureStokesInverseTilt_le_positiveChamber
    {s : ℝ} (hs : 0 < s) (p : Nat.Primes) :
    gammaSewnMobiusApertureStokesInverseTilt s p ≤
      gammaSewnMobiusApertureStokesPositiveChamberConstant s *
        (p : ℝ) * Real.log (p : ℝ) := by
  let q := xiMobiusContinuousApertureDiskNode 1 p
  let r := xiMobiusContinuousApertureDiskNode s p
  let c := gammaSewnMobiusValuationContractionMultiplier s p
  let L := Real.log (p : ℝ)
  let δ := 1 - Real.exp (-s * Real.log 2)
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.one_lt
  have hp0 : 0 < (p : ℝ) := by positivity
  have hL : 0 < L := Real.log_pos hp
  have hq0 : 0 < q := xiMobiusContinuousApertureDiskNode_pos 1 p
  have hr0 : 0 < r := xiMobiusContinuousApertureDiskNode_pos s p
  have hr1 : r < 1 := xiMobiusContinuousApertureDiskNode_lt_one hs p
  have hc0 : 0 < c := gammaSewnMobiusValuationContractionMultiplier_pos s p
  have hc : 1 / 2 < c :=
    one_half_lt_gammaSewnMobiusValuationContractionMultiplier s p
  have hδ : 0 < δ := by
    dsimp only [δ]
    rw [sub_pos, Real.exp_lt_one_iff]
    nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have hnode : xiTransversePrimeApertureDiskNode 1 p = q := by
    simp only [q, xiMobiusContinuousApertureDiskNode,
      xiTransversePrimeApertureDiskNode]
    congr 1
    ring
  have hqle : q ≤ 1 / 2 := by
    rw [← hnode, xiTransversePrimeApertureDiskNode_one_eq_inv]
    rw [inv_eq_one_div]
    apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
    exact_mod_cast p.2.two_le
  have hrδ : δ ≤ 1 - r := by
    dsimp only [δ, r, xiMobiusContinuousApertureDiskNode]
    apply sub_le_sub_left
    apply Real.exp_le_exp.mpr
    have hp2 : Real.log 2 ≤ Real.log (p : ℝ) := by
      apply Real.log_le_log (by norm_num)
      exact_mod_cast p.2.two_le
    nlinarith
  have hqinv : q = ((p : ℝ)⁻¹) := by
    rw [← hnode, xiTransversePrimeApertureDiskNode_one_eq_inv]
  have hratio : r / q ≤ (p : ℝ) := by
    rw [hqinv, div_inv_eq_mul]
    calc
      r * (p : ℝ) ≤ 1 * (p : ℝ) :=
        mul_le_mul_of_nonneg_right hr1.le hp0.le
      _ = (p : ℝ) := one_mul _
  have hfactor :
      (1 + q) / (c * (1 - r)) ≤ 4 / δ := by
    rw [div_le_iff₀ (mul_pos hc0 (sub_pos.mpr hr1))]
    rw [show 4 / δ * (c * (1 - r)) = 4 * c * (1 - r) / δ by ring]
    apply (le_div_iff₀ hδ).2
    have hleft := mul_le_mul_of_nonneg_right hqle hδ.le
    have hcδ := mul_le_mul_of_nonneg_right hc.le hδ.le
    calc
      (1 + q) * δ ≤ (3 / 2) * δ := by nlinarith
      _ ≤ 2 * δ := by nlinarith
      _ ≤ 4 * c * δ := by nlinarith
      _ ≤ 4 * c * (1 - r) := by gcongr
  have hrewrite :
      L * r / (c * (q / (1 + q)) * (1 - r)) =
        (L * (r / q)) * ((1 + q) / (c * (1 - r))) := by
    field_simp [hq0.ne', hc0.ne', sub_ne_zero.mpr hr1.ne']
  rw [gammaSewnMobiusApertureStokesInverseTilt, hnode]
  change L * r / (c * (q / (1 + q)) * (1 - r)) ≤
    gammaSewnMobiusApertureStokesPositiveChamberConstant s * (p : ℝ) * L
  rw [hrewrite, gammaSewnMobiusApertureStokesPositiveChamberConstant]
  change (L * (r / q)) * ((1 + q) / (c * (1 - r))) ≤
    (4 / δ) * (p : ℝ) * L
  calc
    (L * (r / q)) * ((1 + q) / (c * (1 - r)))
        ≤ (L * (p : ℝ)) * (4 / δ) := by gcongr
    _ = (4 / δ) * (p : ℝ) * L := by ring

/-- Every prime occurring in a Kummer character is bounded by its multiplicative height. -/
theorem prime_le_deningerHeight_of_mem_support
    (m : DeningerPrimeLattice) {p : Nat.Primes} (hp : p ∈ m.support) :
    (p : ℝ) ≤ deningerHeight m := by
  have hne : m p ≠ 0 := Finsupp.mem_support_iff.mp hp
  have habs : 1 ≤ (m p).natAbs :=
    Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hne)
  have hsingle : Finsupp.single p 1 ≤ deningerAbsExponent m :=
    Finsupp.single_le_iff.mpr habs
  have hprod := deningerPrimeProduct_mono hsingle
  have hprod' : (p : ℕ) ≤ deningerHeightNat m := by
    simpa [deningerHeightNat, primeProduct] using hprod
  simpa only [deningerHeight] using (Nat.cast_le.mpr hprod')

/-- Full positive-chamber Kummer frequency has two-step height growth. -/
theorem abs_gammaSewnMobiusApertureStokesKotheFrequency_le_positiveChamber
    {s : ℝ} (hs : 0 < s) (m : DeningerPrimeLattice) :
    |gammaSewnMobiusApertureStokesKotheFrequency s m| ≤
      gammaSewnMobiusApertureStokesPositiveChamberConstant s *
        deningerHeight m ^ 2 := by
  let K := gammaSewnMobiusApertureStokesPositiveChamberConstant s
  let H := deningerHeight m
  have hK : 0 < K :=
    gammaSewnMobiusApertureStokesPositiveChamberConstant_pos hs
  have hH : 0 < H := deningerHeight_pos m
  have hlog : Real.log H =
      m.sum fun p z => |(z : ℝ)| * Real.log (p : ℕ) := by
    dsimp only [H]
    rw [deningerHeight, deningerHeightNat, log_primeProduct]
    unfold deningerAbsExponent
    rw [Finsupp.sum_mapRange_index (by simp)]
    refine Finsupp.sum_congr ?_
    intro p _
    congr 1
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
  rw [gammaSewnMobiusApertureStokesKotheFrequency, Finsupp.sum]
  calc
    |∑ p ∈ m.support,
        (m p : ℝ) * gammaSewnMobiusApertureStokesInverseTilt s p|
        ≤ ∑ p ∈ m.support,
          |(m p : ℝ) * gammaSewnMobiusApertureStokesInverseTilt s p| :=
            Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ m.support,
        K * H * (|(m p : ℝ)| * Real.log (p : ℕ)) := by
      refine Finset.sum_le_sum fun p hp => ?_
      rw [abs_mul, abs_of_pos
        (gammaSewnMobiusApertureStokesInverseTilt_pos hs p)]
      have hW :=
        gammaSewnMobiusApertureStokesInverseTilt_le_positiveChamber hs p
      have hpH : (p : ℝ) ≤ H :=
        prime_le_deningerHeight_of_mem_support m hp
      have hz : 0 ≤ |(m p : ℝ)| := abs_nonneg _
      have hLp : 0 ≤ Real.log (p : ℕ) :=
        Real.log_natCast_nonneg (p : ℕ)
      change |(m p : ℝ)| *
          gammaSewnMobiusApertureStokesInverseTilt s p ≤
        K * H * (|(m p : ℝ)| * Real.log (p : ℕ))
      calc
        |(m p : ℝ)| * gammaSewnMobiusApertureStokesInverseTilt s p
            ≤ |(m p : ℝ)| * (K * (p : ℝ) * Real.log (p : ℝ)) :=
              mul_le_mul_of_nonneg_left hW hz
        _ ≤ |(m p : ℝ)| * (K * H * Real.log (p : ℝ)) := by
          gcongr
        _ = K * H * (|(m p : ℝ)| * Real.log (p : ℕ)) := by
          norm_cast
          ring
    _ = K * H * Real.log H := by
      rw [hlog, Finsupp.sum, Finset.mul_sum]
    _ ≤ K * H ^ 2 := by
      have hLH : Real.log H ≤ H := by
        simpa only [H] using log_deningerHeight_le_height m
      calc
        K * H * Real.log H ≤ K * H * H :=
          mul_le_mul_of_nonneg_left hLH (mul_nonneg hK.le hH.le)
        _ = K * H ^ 2 := by ring

/-- Normalized full-positive-chamber multiplier. -/
def gammaSewnMobiusApertureStokesPositiveChamberMultiplier
    (s : ℝ) (m : DeningerPrimeLattice) : ℂ :=
  ((gammaSewnMobiusApertureStokesKotheFrequency s m /
      gammaSewnMobiusApertureStokesPositiveChamberConstant s : ℝ) : ℂ)

theorem norm_gammaSewnMobiusApertureStokesPositiveChamberMultiplier_le
    {s : ℝ} (hs : 0 < s) (m : DeningerPrimeLattice) :
    ‖gammaSewnMobiusApertureStokesPositiveChamberMultiplier s m‖ ≤
      deningerHeight m ^ 2 := by
  have hK := gammaSewnMobiusApertureStokesPositiveChamberConstant_pos hs
  have h :=
    abs_gammaSewnMobiusApertureStokesKotheFrequency_le_positiveChamber hs m
  rw [gammaSewnMobiusApertureStokesPositiveChamberMultiplier,
    Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hK]
  exact (div_le_iff₀ hK).2 (by simpa [mul_comm] using h)

/-- Source Stokes operator on every fixed positive aperture. -/
def gammaSewnMobiusApertureStokesPositiveChamberOperator
    (s : ℝ) (hs : 0 < s) :
    DeningerHeightKothe →ₗ[ℂ] DeningerHeightKothe :=
  (gammaSewnMobiusApertureStokesPositiveChamberConstant s : ℂ) •
    deningerHeightMul
      (gammaSewnMobiusApertureStokesPositiveChamberMultiplier s) 2
      (norm_gammaSewnMobiusApertureStokesPositiveChamberMultiplier_le hs)

theorem gammaSewnMobiusApertureStokesPositiveChamberOperator_coe
    {s : ℝ} (hs : 0 < s) (a : DeningerHeightKothe)
    (m : DeningerPrimeLattice) :
    ((gammaSewnMobiusApertureStokesPositiveChamberOperator s hs a :
        DeningerHeightKothe) : DeningerPrimeLattice → ℂ) m =
      (gammaSewnMobiusApertureStokesKotheFrequency s m : ℂ) *
        (a : DeningerPrimeLattice → ℂ) m := by
  rw [gammaSewnMobiusApertureStokesPositiveChamberOperator]
  change (gammaSewnMobiusApertureStokesPositiveChamberConstant s : ℂ) *
      (gammaSewnMobiusApertureStokesPositiveChamberMultiplier s m *
        (a : DeningerPrimeLattice → ℂ) m) = _
  rw [gammaSewnMobiusApertureStokesPositiveChamberMultiplier]
  have hK : gammaSewnMobiusApertureStokesPositiveChamberConstant s ≠ 0 :=
    (gammaSewnMobiusApertureStokesPositiveChamberConstant_pos hs).ne'
  push_cast
  field_simp [hK]

theorem deningerHeightSeminorm_gammaSewnMobiusApertureStokesPositiveChamberOperator_le
    {s : ℝ} (hs : 0 < s) (k : ℕ) (a : DeningerHeightKothe) :
    deningerHeightSeminorm k
      (gammaSewnMobiusApertureStokesPositiveChamberOperator s hs a) ≤
        gammaSewnMobiusApertureStokesPositiveChamberConstant s *
          deningerHeightSeminorm (k + 2) a := by
  rw [gammaSewnMobiusApertureStokesPositiveChamberOperator]
  change deningerHeightSeminorm k
      ((gammaSewnMobiusApertureStokesPositiveChamberConstant s : ℂ) •
        deningerHeightMul
          (gammaSewnMobiusApertureStokesPositiveChamberMultiplier s) 2
          (norm_gammaSewnMobiusApertureStokesPositiveChamberMultiplier_le hs) a) ≤ _
  rw [map_smul_eq_mul]
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (gammaSewnMobiusApertureStokesPositiveChamberConstant_pos hs)]
  exact mul_le_mul_of_nonneg_left
    (deningerHeightSeminorm_mul_le
      (norm_gammaSewnMobiusApertureStokesPositiveChamberMultiplier_le hs) k a)
    (gammaSewnMobiusApertureStokesPositiveChamberConstant_pos hs).le

/-- **Full positive-chamber transpose law.** The sewn dual current produces the Euler current on
rapid tests for every `s>0`, including the non-absolutely-convergent total-mass chamber. -/
theorem gammaSewnMobiusApertureStokesDualFeaturePairing_positiveChamberOperator_eq_euler
    {s : ℝ} (hs : 0 < s) (a : DeningerHeightKothe) :
    gammaSewnMobiusApertureStokesDualFeaturePairing s
        (gammaSewnMobiusApertureStokesPositiveChamberOperator s hs a) =
      gammaSewnMobiusApertureStokesEulerDualPairing s a := by
  rw [gammaSewnMobiusApertureStokesDualFeaturePairing,
    gammaSewnMobiusApertureStokesEulerDualPairing]
  refine tsum_congr fun pk => ?_
  rw [gammaSewnMobiusApertureStokesPositiveChamberOperator_coe hs,
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
    exact gammaSewnMobiusApertureStokesFluxTerm_eq hs pk
  rw [← mul_assoc, ← ofReal_mul, hflux]

/-- Euler current is a continuous Köthe-dual functional throughout the positive chamber. -/
theorem norm_gammaSewnMobiusApertureStokesEulerDualPairing_le_positiveChamber
    {s : ℝ} (hs : 0 < s) (a : DeningerHeightKothe) :
    ‖gammaSewnMobiusApertureStokesEulerDualPairing s a‖ ≤
      gammaSewnMobiusApertureStokesPositiveChamberConstant s *
        deningerHeightSeminorm 2 a := by
  rw [← gammaSewnMobiusApertureStokesDualFeaturePairing_positiveChamberOperator_eq_euler hs]
  have hop :=
    deningerHeightSeminorm_gammaSewnMobiusApertureStokesPositiveChamberOperator_le
      (s := s) hs 0 a
  exact le_trans
    (norm_gammaSewnMobiusApertureStokesDualFeaturePairing_le hs
      (gammaSewnMobiusApertureStokesPositiveChamberOperator s hs a))
    (by simpa using hop)

end RHTower
