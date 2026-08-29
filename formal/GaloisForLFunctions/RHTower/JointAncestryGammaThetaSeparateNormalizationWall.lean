import GaloisForLFunctions.RHTower.JointAncestryPrimeHaarPrefixCauchyReflectionDiscriminator

namespace RHTower

noncomputable section

/-- Fourth-power local factor after removing the aperture-independent Gamma boundary constant. -/
def jasGammaThetaLocalRenormalizedFourthFactor
    (x : ℝ) (p : Nat.Primes) : ℝ :=
  8 * (gammaSewnMobiusValuationContractionMultiplier x p *
    (1 - xiMobiusContinuousApertureDiskNode x p)) ^ 4

/-- Local loss of the separately normalized synchronized-lcm Gamma tensor factor. -/
def jasGammaThetaLocalRenormalizedDefect
    (x : ℝ) (p : Nat.Primes) : ℝ :=
  1 - jasGammaThetaLocalRenormalizedFourthFactor x p

/-- Exact first-order cancellation in the Gamma-sewn synchronized-lcm local factor. -/
theorem jasGammaThetaLocalRenormalizedFourthFactor_eq
    (x : ℝ) (p : Nat.Primes) :
    jasGammaThetaLocalRenormalizedFourthFactor x p =
      let q := xiMobiusContinuousApertureDiskNode x p
      (1 - q ^ 2) ^ 4 / (1 + q ^ 4) := by
  let q := xiMobiusContinuousApertureDiskNode x p
  have hden : 8 * (1 + q ^ 4) ≠ 0 := by positivity
  rw [jasGammaThetaLocalRenormalizedFourthFactor, mul_pow,
    gammaSewnMobiusValuationContractionMultiplier_pow_four]
  change 8 * ((1 + q) ^ 4 / (8 * (1 + q ^ 4)) * (1 - q) ^ 4) =
    (1 - q ^ 2) ^ 4 / (1 + q ^ 4)
  field_simp [hden]
  ring

/-- Gamma sewing cancels the entire first aperture order: the surviving local defect is exactly
quadratic in the true disk node. -/
theorem jasGammaThetaLocalRenormalizedDefect_eq
    (x : ℝ) (p : Nat.Primes) :
    jasGammaThetaLocalRenormalizedDefect x p =
      let q := xiMobiusContinuousApertureDiskNode x p
      q ^ 2 * (4 - 5 * q ^ 2 + 4 * q ^ 4 - q ^ 6) / (1 + q ^ 4) := by
  let q := xiMobiusContinuousApertureDiskNode x p
  have hden : 1 + q ^ 4 ≠ 0 := by positivity
  rw [jasGammaThetaLocalRenormalizedDefect,
    jasGammaThetaLocalRenormalizedFourthFactor_eq]
  change 1 - (1 - q ^ 2) ^ 4 / (1 + q ^ 4) =
    q ^ 2 * (4 - 5 * q ^ 2 + 4 * q ^ 4 - q ^ 6) / (1 + q ^ 4)
  field_simp [hden]
  ring

/-- The quadratic Gamma defect is uniformly comparable with the squared aperture node. -/
theorem xiMobiusContinuousApertureDiskNode_sq_le_jasGammaThetaLocalRenormalizedDefect
    {x : ℝ} (hx : 0 < x) (p : Nat.Primes) :
    xiMobiusContinuousApertureDiskNode x p ^ 2 ≤
      jasGammaThetaLocalRenormalizedDefect x p := by
  let q := xiMobiusContinuousApertureDiskNode x p
  have hq0 : 0 < q := xiMobiusContinuousApertureDiskNode_pos x p
  have hq1 : q < 1 := xiMobiusContinuousApertureDiskNode_lt_one hx p
  have hq2 : q ^ 2 < 1 := by
    nlinarith [mul_pos (sub_pos.mpr hq1) (add_pos hq0 zero_lt_one)]
  have hq4 : q ^ 4 < 1 := by
    nlinarith [mul_pos (sub_pos.mpr hq2) (add_pos (sq_pos_of_pos hq0) zero_lt_one)]
  have hG : 2 ≤ 4 - 5 * q ^ 2 + 4 * q ^ 4 - q ^ 6 := by
    nlinarith [mul_nonneg (sq_nonneg (1 - q ^ 2)) (by linarith : 0 ≤ 2 - q ^ 2)]
  rw [jasGammaThetaLocalRenormalizedDefect_eq]
  change q ^ 2 ≤ q ^ 2 * (4 - 5 * q ^ 2 + 4 * q ^ 4 - q ^ 6) / (1 + q ^ 4)
  rw [le_div_iff₀ (by positivity : 0 < 1 + q ^ 4)]
  calc
    q ^ 2 * (1 + q ^ 4) ≤ q ^ 2 * 2 :=
      mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg q)
    _ ≤ q ^ 2 * (4 - 5 * q ^ 2 + 4 * q ^ 4 - q ^ 6) :=
      mul_le_mul_of_nonneg_left hG (sq_nonneg q)

/-- The same local defect is at most four copies of the squared aperture node. -/
theorem jasGammaThetaLocalRenormalizedDefect_le_four_mul_sq
    {x : ℝ} (hx : 0 < x) (p : Nat.Primes) :
    jasGammaThetaLocalRenormalizedDefect x p ≤
      4 * xiMobiusContinuousApertureDiskNode x p ^ 2 := by
  let q := xiMobiusContinuousApertureDiskNode x p
  have hq0 : 0 < q := xiMobiusContinuousApertureDiskNode_pos x p
  have hq1 : q < 1 := xiMobiusContinuousApertureDiskNode_lt_one hx p
  have hq2 : q ^ 2 < 1 := by
    nlinarith [mul_pos (sub_pos.mpr hq1) (add_pos hq0 zero_lt_one)]
  have hG4 : 4 - 5 * q ^ 2 + 4 * q ^ 4 - q ^ 6 ≤ 4 := by
    nlinarith [mul_nonneg (sq_nonneg (q ^ 2 - 2)) (sq_nonneg q)]
  rw [jasGammaThetaLocalRenormalizedDefect_eq]
  change q ^ 2 * (4 - 5 * q ^ 2 + 4 * q ^ 4 - q ^ 6) / (1 + q ^ 4) ≤
    4 * q ^ 2
  rw [div_le_iff₀ (by positivity : 0 < 1 + q ^ 4)]
  calc
    q ^ 2 * (4 - 5 * q ^ 2 + 4 * q ^ 4 - q ^ 6) ≤ q ^ 2 * 4 :=
      mul_le_mul_of_nonneg_left hG4 (sq_nonneg q)
    _ ≤ 4 * q ^ 2 * (1 + q ^ 4) := by
      nlinarith [sq_nonneg q, sq_nonneg (q ^ 2)]

/-- Squared true aperture nodes have the same exact prime wall as prime-Poisson amplitudes. -/
theorem summable_xiMobiusContinuousApertureDiskNode_sq_iff
    (x : ℝ) (hx : 0 < x) :
    Summable (fun p : Nat.Primes =>
      xiMobiusContinuousApertureDiskNode x p ^ 2) ↔ 1 / 2 < x := by
  rw [← GaloisForLFunctions.HTGeometry.summable_normSq_primePoissonParameter_zero_iff
    x 0 hx]
  apply summable_congr
  intro p
  simp only [sub_zero, GaloisForLFunctions.HTGeometry.coe_primePoissonParameter,
    GaloisForLFunctions.HTGeometry.norm_primePoissonParameterValue,
    xiMobiusContinuousApertureDiskNode]

/-- Sharp square-tangency wall for the separately normalized Gamma tensor factors. -/
theorem summable_jasGammaThetaLocalRenormalizedDefect_iff
    (x : ℝ) (hx : 0 < x) :
    Summable (jasGammaThetaLocalRenormalizedDefect x) ↔ 1 / 2 < x := by
  rw [← summable_xiMobiusContinuousApertureDiskNode_sq_iff x hx]
  constructor
  · intro hdefect
    exact Summable.of_nonneg_of_le
      (fun p => sq_nonneg (xiMobiusContinuousApertureDiskNode x p))
      (fun p => xiMobiusContinuousApertureDiskNode_sq_le_jasGammaThetaLocalRenormalizedDefect
        hx p)
      hdefect
  · intro hnode
    have hfour : Summable (fun p : Nat.Primes =>
        4 * xiMobiusContinuousApertureDiskNode x p ^ 2) := hnode.mul_left 4
    exact Summable.of_nonneg_of_le
      (fun p => (sq_nonneg (xiMobiusContinuousApertureDiskNode x p)).trans
        (xiMobiusContinuousApertureDiskNode_sq_le_jasGammaThetaLocalRenormalizedDefect
          hx p))
      (fun p => jasGammaThetaLocalRenormalizedDefect_le_four_mul_sq hx p)
      hfour

/-- At an actual Xi divisor, separately normalized forward and reflected synchronized-lcm Gamma
tensor factors can never both converge. -/
theorem xiDivisorSupport_not_summable_jasGammaThetaLocalRenormalizedDefect_both
    (rho : XiDivisorSupport) :
    ¬ (Summable (jasGammaThetaLocalRenormalizedDefect (rho : ℂ).re) ∧
      Summable (jasGammaThetaLocalRenormalizedDefect (1 - (rho : ℂ).re))) := by
  intro hboth
  have hstrip := xi_divisor_support_re_mem_open_unit rho
  have hforward :=
    (summable_jasGammaThetaLocalRenormalizedDefect_iff _ hstrip.1).mp hboth.1
  have hreflected :=
    (summable_jasGammaThetaLocalRenormalizedDefect_iff _ (sub_pos.mpr hstrip.2)).mp hboth.2
  linarith

end

end RHTower
