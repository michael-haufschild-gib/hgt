import GaloisForLFunctions.RHTower.HedenmalmThetaKakutaniFluxPolarization

/-!
# Cofinal harmonic coercivity of theta Kakutani polarization

The positive theta/Kakutani density has a quantitative off-neutral floor: at every prime it
dominates a grade-dependent strictly positive multiple of `1 / p`.  Thus no reflected pairing,
cofinal tail, or finite-stage rearrangement can hide a nonzero theta Green current.  A uniform
bound on all finite-prime polarization energies is already enough to force one Route P node to be
positive real.
-/

namespace RHTower.HedenmalmThetaSource

noncomputable section

/-- Exact prime-independent harmonic floor selected by one centered Xi grade. -/
def thetaKakutaniHarmonicFloor (q : XiZeroCopy) : ℝ :=
  (1 - (2 : ℝ) ^ (-|primeDepthBVWoldXiCenteredRate q.1|)) ^ 2

theorem thetaKakutaniHarmonicFloor_nonneg (q : XiZeroCopy) :
    0 ≤ thetaKakutaniHarmonicFloor q :=
  sq_nonneg _

/-- The harmonic floor is strictly positive exactly when the oriented theta current is nonzero. -/
theorem thetaKakutaniHarmonicFloor_pos_iff_boundaryFlux_ne_zero
    (q : XiZeroCopy) :
    0 < thetaKakutaniHarmonicFloor q ↔
      thetaXiRankTwoBoundaryFlux q ≠ 0 := by
  have hmassEnergy :
      -(thetaSource.mass * thetaXiRootEnergy q) ≠ 0 :=
    neg_ne_zero.mpr
      (mul_pos thetaSource.mass_pos (thetaXiRootEnergy_pos q)).ne'
  rw [thetaKakutaniHarmonicFloor,
    thetaXiRankTwoBoundaryFlux_eq_neg_massEnergy_mul_centeredRate]
  constructor
  · intro hfloor hflux
    have ha : primeDepthBVWoldXiCenteredRate q.1 = 0 :=
      (mul_eq_zero.mp hflux).resolve_left hmassEnergy
    simp [ha] at hfloor
  · intro hflux
    have ha : primeDepthBVWoldXiCenteredRate q.1 ≠ 0 := by
      intro ha
      apply hflux
      rw [ha, mul_zero]
    have habs : 0 < |primeDepthBVWoldXiCenteredRate q.1| := abs_pos.mpr ha
    have hpow : (2 : ℝ) ^ (-|primeDepthBVWoldXiCenteredRate q.1|) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
    exact sq_pos_of_pos (sub_pos.mpr hpow)

/-- **Harmonic coercivity.**  Every local theta polarization dominates its prime-harmonic atom
with an explicit grade-dependent coefficient. -/
theorem thetaKakutaniHarmonicFloor_mul_primeHarmonic_le_polarization
    (p : Nat.Primes) (q : XiZeroCopy) :
    thetaKakutaniHarmonicFloor q * (1 / (p : ℝ)) ≤
      thetaKakutaniFluxPositiveUnit p q *
        thetaXiRankTwoBoundaryFlux q ^ 2 := by
  rw [← primeValuationHellingerGap_eq_positiveUnit_mul_thetaFlux_sq]
  let d : ℝ := |primeDepthBVWoldXiCenteredRate q.1|
  have hd0 : 0 ≤ d := abs_nonneg _
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast p.2.two_le
  have hp1 : (1 : ℝ) ≤ p := one_le_two.trans hp2
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans_le hp1
  have hbase : (p : ℝ) ^ (-d) ≤ (2 : ℝ) ^ (-d) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (neg_nonpos.mpr hd0)
  have hpone : (p : ℝ) ^ (-d) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hp1 (neg_nonpos.mpr hd0)
  have htwoone : (2 : ℝ) ^ (-d) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (neg_nonpos.mpr hd0)
  have hfactorSq :
      (1 - (2 : ℝ) ^ (-d)) ^ 2 ≤
        (1 - (p : ℝ) ^ (-d)) ^ 2 := by
    exact (sq_le_sq₀ (sub_nonneg.mpr htwoone) (sub_nonneg.mpr hpone)).2
      (by linarith)
  have hsplit :
      (p : ℝ) ^ (-(1 / 2 - -d)) =
        (p : ℝ) ^ (-(1 / 2 : ℝ)) * (p : ℝ) ^ (-d) := by
    rw [← Real.rpow_add hp0]
    congr 1
    ring
  have hhalfSq :
      ((p : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = 1 / (p : ℝ) := by
    calc
      ((p : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = (p : ℝ) ^ (-1 : ℝ) := by
        rw [pow_two, ← Real.rpow_add hp0]
        congr 1
        ring
      _ = 1 / (p : ℝ) := by rw [Real.rpow_neg_one, one_div]
  rw [thetaKakutaniHarmonicFloor, primeValuationHellingerGap]
  change (1 - (2 : ℝ) ^ (-d)) ^ 2 * (1 / (p : ℝ)) ≤
    ((p : ℝ) ^ (-(1 / 2 : ℝ)) -
      (p : ℝ) ^ (-(1 / 2 - -d))) ^ 2
  rw [hsplit]
  calc
    (1 - (2 : ℝ) ^ (-d)) ^ 2 * (1 / (p : ℝ)) =
        ((p : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 *
          (1 - (2 : ℝ) ^ (-d)) ^ 2 := by rw [hhalfSq]; ring
    _ ≤ ((p : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 *
          (1 - (p : ℝ) ^ (-d)) ^ 2 :=
      mul_le_mul_of_nonneg_left hfactorSq (sq_nonneg _)
    _ = ((p : ℝ) ^ (-(1 / 2 : ℝ)) -
          (p : ℝ) ^ (-(1 / 2 : ℝ)) * (p : ℝ) ^ (-d)) ^ 2 := by
      ring

/-- Harmonic coercivity survives reflected pairing with doubled strength. -/
theorem two_mul_thetaKakutaniHarmonicFloor_mul_primeHarmonic_le_reflectionPair
    (p : Nat.Primes) (q : XiZeroCopy) :
    2 * thetaKakutaniHarmonicFloor q * (1 / (p : ℝ)) ≤
      thetaKakutaniFluxPositiveUnit p q * thetaXiRankTwoBoundaryFlux q ^ 2 +
        thetaKakutaniFluxPositiveUnit p (xiZeroCopyReflectEquiv q) *
          thetaXiRankTwoBoundaryFlux (xiZeroCopyReflectEquiv q) ^ 2 := by
  have h := thetaKakutaniHarmonicFloor_mul_primeHarmonic_le_polarization p q
  rw [← primeValuationHellingerGap_eq_positiveUnit_mul_thetaFlux_sq p q] at h
  rw [thetaKakutaniFluxPolarization_add_reflect_eq_two_gap]
  nlinarith

/-- The quantitative lower floor persists after summing over any finite set of primes. -/
theorem finset_thetaKakutaniHarmonicFloor_sum_le_polarization_sum
    (s : Finset Nat.Primes) (q : XiZeroCopy) :
    ∑ p ∈ s, thetaKakutaniHarmonicFloor q * (1 / (p : ℝ)) ≤
      ∑ p ∈ s, thetaKakutaniFluxPositiveUnit p q *
        thetaXiRankTwoBoundaryFlux q ^ 2 := by
  exact Finset.sum_le_sum fun p _ =>
    thetaKakutaniHarmonicFloor_mul_primeHarmonic_le_polarization p q

/-- Uniform boundedness of all finite-prime theta polarization energies forces same-fibre
boundary neutrality.  This is a finite-stage producer contract; no infinite sum is assumed. -/
theorem thetaXiRankTwoBoundaryFlux_eq_zero_of_uniform_finset_polarization_bound
    (q : XiZeroCopy) {C : ℝ}
    (hbound : ∀ s : Finset Nat.Primes,
      ∑ p ∈ s, thetaKakutaniFluxPositiveUnit p q *
        thetaXiRankTwoBoundaryFlux q ^ 2 ≤ C) :
    thetaXiRankTwoBoundaryFlux q = 0 := by
  have hnonneg : 0 ≤ fun p : Nat.Primes =>
      thetaKakutaniFluxPositiveUnit p q * thetaXiRankTwoBoundaryFlux q ^ 2 :=
    fun p => mul_nonneg (thetaKakutaniFluxPositiveUnit_pos p q).le (sq_nonneg _)
  have hsum : Summable (fun p : Nat.Primes =>
      thetaKakutaniFluxPositiveUnit p q * thetaXiRankTwoBoundaryFlux q ^ 2) :=
    summable_of_sum_le hnonneg hbound
  exact (summable_thetaKakutaniFluxPolarization_iff_boundaryFlux_zero q).1 hsum

/-- Finite-prime energy boundedness is equivalent to positivity of the individual Route P node. -/
theorem thetaXiReciprocalEigenvalue_sq_positiveReal_iff_uniform_finset_polarization_bound
    (q : XiZeroCopy) :
    (exists r : ℝ, 0 < r ∧ thetaXiReciprocalEigenvalue q ^ 2 = (r : ℂ)) ↔
      exists C : ℝ, ∀ s : Finset Nat.Primes,
        ∑ p ∈ s, thetaKakutaniFluxPositiveUnit p q *
          thetaXiRankTwoBoundaryFlux q ^ 2 ≤ C := by
  rw [thetaXiReciprocalEigenvalue_sq_positiveReal_iff_boundaryFlux_zero]
  constructor
  · intro hzero
    refine ⟨0, fun s => ?_⟩
    simp [hzero]
  · rintro ⟨C, hbound⟩
    exact thetaXiRankTwoBoundaryFlux_eq_zero_of_uniform_finset_polarization_bound q hbound

end

end RHTower.HedenmalmThetaSource
