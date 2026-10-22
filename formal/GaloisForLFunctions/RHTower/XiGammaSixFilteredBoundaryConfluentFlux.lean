import GaloisForLFunctions.RHTower.XiGammaSixFilteredBoundaryHarmonicResidue
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaPhysicalEndpointPrimeHardyGreenScaling

/-!
# Gamma-six confluent boundary-layer flux

The scalar harmonic residue cannot be removed continuously at the neutral wall.  This module
constructs the coefficientwise-continuous prime counterterm instead.  Its difference from the
literal Gamma-six second jet is a nonnegative summable radial defect, while its right-hand
derivative has a nonzero concentrated boundary flux.  The exact flux is a dyadic difference of
the physical Hardy--Green energy, so its depth-scaled wall limit is `log 2 / m^2`.
-/

open Complex Set Filter Topology
open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- Prime-dependent horizontal-gap counterterm. Unlike the scalar asymptotic residue, every prime
coefficient is continuous through neutral horizontal grade. -/
def gammaSixFilteredBoundaryConfluentCounterterm
    (m : ℕ) (t : ℝ) (p : Nat.Primes) : ℝ :=
  (Real.log 2 / (m : ℝ) ^ 2) * (1 / (p : ℝ)) *
    (1 - (p : ℝ) ^ (-|t|)) ^ 2

theorem continuous_gammaSixFilteredBoundaryConfluentCounterterm
    (m : ℕ) (p : Nat.Primes) :
    Continuous (fun t : ℝ =>
      gammaSixFilteredBoundaryConfluentCounterterm m t p) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast p.2.ne_zero
  unfold gammaSixFilteredBoundaryConfluentCounterterm
  fun_prop

@[simp] theorem gammaSixFilteredBoundaryConfluentCounterterm_zero
    (m : ℕ) (p : Nat.Primes) :
    gammaSixFilteredBoundaryConfluentCounterterm m 0 p = 0 := by
  simp [gammaSixFilteredBoundaryConfluentCounterterm]

/-- Finite radial part left between the confluent counterterm and the literal Gamma-six jet. -/
def gammaSixFilteredBoundaryConfluentDefect
    (m : ℕ) (q : XiZeroCopy) (p : Nat.Primes) : ℝ :=
  gammaSixFilteredBoundaryConfluentCounterterm m
      (primeDepthBVWoldXiCenteredRate q.1) p -
    gammaSixFilteredBoundarySecondJet m q p

theorem gammaSixFilteredBoundarySecondJet_eq_confluentCounterterm_mul
    {m : ℕ} (hm : 1 ≤ m) (q : XiZeroCopy) (p : Nat.Primes) :
    gammaSixFilteredBoundarySecondJet m q p =
      gammaSixFilteredBoundaryConfluentCounterterm m
          (primeDepthBVWoldXiCenteredRate q.1) p *
        (1 - (p : ℝ)⁻¹) ^ (2 * m) *
        (1 - (p : ℝ) ^ (-(m : ℝ))) ^ 2 *
        (1 / (1 + (p : ℝ)⁻¹) ^ 2) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast p.2.ne_zero
  rw [gammaSixFilteredBoundarySecondJet_eq_factorized hm q p,
    gammaSixFilteredBoundaryConfluentCounterterm,
    gaussLocalFactorWeight, primeActivationOccupancyFisherDensity_eq]
  field_simp [hp0]

theorem gammaSixFilteredBoundaryConfluentDefect_eq
    {m : ℕ} (hm : 1 ≤ m) (q : XiZeroCopy) (p : Nat.Primes) :
    gammaSixFilteredBoundaryConfluentDefect m q p =
      gammaSixFilteredBoundaryConfluentCounterterm m
          (primeDepthBVWoldXiCenteredRate q.1) p *
        (1 -
          (1 - (p : ℝ)⁻¹) ^ (2 * m) *
          (1 - (p : ℝ) ^ (-(m : ℝ))) ^ 2 *
          (1 / (1 + (p : ℝ)⁻¹) ^ 2)) := by
  rw [gammaSixFilteredBoundaryConfluentDefect,
    gammaSixFilteredBoundarySecondJet_eq_confluentCounterterm_mul hm q p]
  ring

private theorem one_sub_three_mul_le_sum_defects
    {a b c : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hc1 : c ≤ 1) :
    1 - a * b * c ≤ (1 - a) + (1 - b) + (1 - c) := by
  have hab0 : 0 ≤ a * b := mul_nonneg ha0 hb0
  have hab1 : a * b ≤ 1 := (mul_le_mul ha1 hb1 hb0 (by norm_num)).trans_eq (by ring)
  calc
    1 - a * b * c = (1 - a * b) + a * b * (1 - c) := by ring
    _ ≤ (1 - a * b) + 1 * (1 - c) := by gcongr
    _ = (1 - a) + a * (1 - b) + (1 - c) := by ring
    _ ≤ (1 - a) + 1 * (1 - b) + (1 - c) := by gcongr
    _ = (1 - a) + (1 - b) + (1 - c) := by ring

set_option maxHeartbeats 800000 in
theorem gammaSixFilteredBoundaryConfluentDefect_bounds
    {m : ℕ} (hm : 1 ≤ m) (q : XiZeroCopy) (p : Nat.Primes) :
    0 ≤ gammaSixFilteredBoundaryConfluentDefect m q p ∧
      gammaSixFilteredBoundaryConfluentDefect m q p ≤
        (Real.log 2 / (m : ℝ) ^ 2) *
          ((((2 * m : ℕ) : ℝ)) + 5) * (p : ℝ)⁻¹ ^ 2 := by
  let P : ℝ := p
  let z : ℝ := P⁻¹
  let a : ℝ := (1 - z) ^ (2 * m)
  let b : ℝ := (1 - P ^ (-(m : ℝ))) ^ 2
  let c : ℝ := 1 / (1 + z) ^ 2
  let K : ℝ := gammaSixFilteredBoundaryConfluentCounterterm m
    (primeDepthBVWoldXiCenteredRate q.1) p
  let C : ℝ := Real.log 2 / (m : ℝ) ^ 2
  have hP2 : (2 : ℝ) ≤ P := by dsimp [P]; exact_mod_cast p.2.two_le
  have hP0 : 0 < P := lt_of_lt_of_le (by norm_num) hP2
  have hP1 : 1 ≤ P := by linarith
  have hz0 : 0 ≤ z := by dsimp [z]; positivity
  have hzh : z ≤ 1 / 2 := by
    dsimp [z]
    simpa only [one_div] using
      (inv_le_inv₀ hP0 (by norm_num : (0 : ℝ) < 2)).2 hP2
  have hz1 : z ≤ 1 := hzh.trans (by norm_num)
  have hbase0 : 0 ≤ 1 - z := by linarith
  have hbase1 : 1 - z ≤ 1 := by linarith
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := by dsimp [a]; exact pow_le_one₀ hbase0 hbase1
  have hadefect : 1 - a ≤ (((2 * m : ℕ) : ℝ)) * z := by
    have hbern := one_add_mul_le_pow (show (-2 : ℝ) ≤ -z by linarith) (2 * m)
    have hbern' : 1 - (((2 * m : ℕ) : ℝ)) * z ≤ a := by
      simpa [a, sub_eq_add_neg] using hbern
    linarith
  have hv0 : 0 ≤ P ^ (-(m : ℝ)) := Real.rpow_nonneg hP0.le _
  have hv1 : P ^ (-(m : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hP1
      (neg_nonpos.mpr (Nat.cast_nonneg m))
  have hb0 : 0 ≤ b := by dsimp [b]; positivity
  have hb1 : b ≤ 1 := by
    dsimp [b]
    nlinarith [mul_nonneg hv0 (by linarith : 0 ≤ 2 - P ^ (-(m : ℝ)))]
  have hbdefect : 1 - b ≤ 2 * z := by
    have hvmz : P ^ (-(m : ℝ)) ≤ z := by
      dsimp [z]
      rw [← Real.rpow_neg_one]
      apply Real.rpow_le_rpow_of_exponent_le hP1
      have hmcast : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      linarith
    dsimp [b]
    nlinarith [sq_nonneg (P ^ (-(m : ℝ)))]
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  have hc1 : c ≤ 1 := by
    dsimp [c]
    have hden : 1 ≤ (1 + z) ^ 2 := by nlinarith [sq_nonneg z]
    exact (div_le_one (by positivity : 0 < (1 + z) ^ 2)).2 hden
  have hcdefect : 1 - c ≤ 3 * z := by
    have hF := (primeActivationOccupancyFisherDensity_harmonic_difference_bounds p).2
    have hcEq : c = P * primeActivationOccupancyFisherDensity p := by
      rw [primeActivationOccupancyFisherDensity_eq]
      dsimp only [c, z]
      change 1 / (1 + P⁻¹) ^ 2 = P * (P / (P + 1) ^ 2)
      field_simp [hP0.ne']
    rw [hcEq]
    change 1 / P - primeActivationOccupancyFisherDensity p ≤ 3 / P ^ 2 at hF
    have hmul := mul_le_mul_of_nonneg_left hF hP0.le
    change 1 - P * primeActivationOccupancyFisherDensity p ≤ 3 * P⁻¹
    calc
      1 - P * primeActivationOccupancyFisherDensity p =
          P * (1 / P - primeActivationOccupancyFisherDensity p) := by
        field_simp [hP0.ne']
      _ ≤ P * (3 / P ^ 2) := hmul
      _ = 3 * P⁻¹ := by field_simp [hP0.ne']
  have hprod0 : 0 ≤ a * b * c := mul_nonneg (mul_nonneg ha0 hb0) hc0
  have hprod1 : a * b * c ≤ 1 :=
    (mul_le_mul (mul_le_mul ha1 hb1 hb0 (by norm_num)) hc1 hc0
      (by positivity)).trans_eq (by ring)
  have hproddefect : 1 - a * b * c ≤
      ((((2 * m : ℕ) : ℝ)) + 5) * z := by
    calc
      1 - a * b * c ≤ (1 - a) + (1 - b) + (1 - c) :=
        one_sub_three_mul_le_sum_defects ha0 ha1 hb0 hb1 hc1
      _ ≤ (((2 * m : ℕ) : ℝ)) * z + 2 * z + 3 * z := by gcongr
      _ = ((((2 * m : ℕ) : ℝ)) + 5) * z := by ring
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have hH0 : 0 ≤
      (1 - (p : ℝ) ^ (-|primeDepthBVWoldXiCenteredRate q.1|)) ^ 2 := sq_nonneg _
  have hH1 :
      (1 - (p : ℝ) ^ (-|primeDepthBVWoldXiCenteredRate q.1|)) ^ 2 ≤ 1 := by
    have hw0 : 0 ≤ (p : ℝ) ^ (-|primeDepthBVWoldXiCenteredRate q.1|) :=
      Real.rpow_nonneg (by positivity) _
    have hw1 : (p : ℝ) ^ (-|primeDepthBVWoldXiCenteredRate q.1|) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos
        (by exact_mod_cast p.2.one_lt.le)
        (neg_nonpos.mpr (abs_nonneg _))
    nlinarith [mul_nonneg hw0 (by linarith :
      0 ≤ 2 - (p : ℝ) ^ (-|primeDepthBVWoldXiCenteredRate q.1|))]
  have hK0 : 0 ≤ K := by
    dsimp [K, gammaSixFilteredBoundaryConfluentCounterterm, C]
    positivity
  have hKle : K ≤ C * z := by
    dsimp [K, gammaSixFilteredBoundaryConfluentCounterterm, C, z]
    calc
      C * (1 / (p : ℝ)) *
          (1 - (p : ℝ) ^ (-|primeDepthBVWoldXiCenteredRate q.1|)) ^ 2 ≤
          C * (1 / (p : ℝ)) * 1 := by gcongr
      _ = C * P⁻¹ := by dsimp [P]; ring
  have hdefectEq : gammaSixFilteredBoundaryConfluentDefect m q p =
      K * (1 - a * b * c) := by
    rw [gammaSixFilteredBoundaryConfluentDefect_eq hm q p]
  rw [hdefectEq]
  constructor
  · exact mul_nonneg hK0 (sub_nonneg.mpr hprod1)
  · calc
      K * (1 - a * b * c) ≤
          (C * z) * (((((2 * m : ℕ) : ℝ)) + 5) * z) := by gcongr
      _ = C * ((((2 * m : ℕ) : ℝ)) + 5) * (p : ℝ)⁻¹ ^ 2 := by
        dsimp only [z]
        ring

theorem summable_gammaSixFilteredBoundaryConfluentDefect
    {m : ℕ} (hm : 1 ≤ m) (q : XiZeroCopy) :
    Summable (gammaSixFilteredBoundaryConfluentDefect m q) := by
  have hsq : Summable (fun p : Nat.Primes => (p : ℝ)⁻¹ ^ 2) := by
    have h := summable_prime_rpow_neg (show (1 : ℝ) < 2 by norm_num)
    refine h.congr fun p => ?_
    rw [← Real.rpow_neg_one, ← Real.rpow_natCast]
    rw [← Real.rpow_mul (by positivity : 0 ≤ (p : ℝ))]
    norm_num
  have hmajor := hsq.mul_left
    ((Real.log 2 / (m : ℝ) ^ 2) * ((((2 * m : ℕ) : ℝ)) + 5))
  apply Summable.of_nonneg_of_le
    (fun p => (gammaSixFilteredBoundaryConfluentDefect_bounds hm q p).1)
    (fun p => ?_) hmajor
  simpa only [mul_assoc] using
    (gammaSixFilteredBoundaryConfluentDefect_bounds hm q p).2

theorem gammaSixFilteredBoundarySecondJet_eq_confluentCounterterm_sub_defect
    (m : ℕ) (q : XiZeroCopy) (p : Nat.Primes) :
    gammaSixFilteredBoundarySecondJet m q p =
      gammaSixFilteredBoundaryConfluentCounterterm m
          (primeDepthBVWoldXiCenteredRate q.1) p -
        gammaSixFilteredBoundaryConfluentDefect m q p := by
  rw [gammaSixFilteredBoundaryConfluentDefect]
  ring

/-- Right-hand flux of the continuous prime-dependent boundary layer. -/
def gammaSixFilteredBoundaryConfluentFluxPrimeTerm
    (m : ℕ) (t : ℝ) (p : Nat.Primes) : ℝ :=
  2 * (Real.log 2 / (m : ℝ) ^ 2) *
    (xiMassPrimeSquareEulerWeight (t / 2) p -
      xiMassPrimeSquareEulerWeight t p)

theorem hasDerivAt_gammaSixFilteredBoundaryConfluentCounterterm
    (m : ℕ) (p : Nat.Primes) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ =>
      gammaSixFilteredBoundaryConfluentCounterterm m s p)
      (gammaSixFilteredBoundaryConfluentFluxPrimeTerm m t p) t := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.pos
  have hpow : HasDerivAt (fun s : ℝ => (p : ℝ) ^ (-s))
      (-Real.log (p : ℝ) * (p : ℝ) ^ (-t)) t := by
    have h := ((hasDerivAt_id (𝕜 := ℝ) t).neg.const_rpow hp0)
    convert h using 1 <;> simp only [id_eq, Pi.neg_apply, mul_neg, mul_one]
  have hgap : HasDerivAt (fun s : ℝ => 1 - (p : ℝ) ^ (-s))
      (Real.log (p : ℝ) * (p : ℝ) ^ (-t)) t := by
    apply HasDerivAt.congr_of_eventuallyEq
      (((hasDerivAt_const (x := t) (c := (1 : ℝ))).sub hpow).congr_deriv (by ring))
    exact Filter.Eventually.of_forall (fun s => rfl)
  have hsq := hgap.pow 2
  have habs : (fun s : ℝ => gammaSixFilteredBoundaryConfluentCounterterm m s p) =ᶠ[𝓝 t]
      fun s => (Real.log 2 / (m : ℝ) ^ 2) * (1 / (p : ℝ)) *
        (1 - (p : ℝ) ^ (-s)) ^ 2 := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    rw [gammaSixFilteredBoundaryConfluentCounterterm, abs_of_pos hs]
  have hmain := HasDerivAt.congr_of_eventuallyEq
    (hsq.const_mul ((Real.log 2 / (m : ℝ) ^ 2) * (1 / (p : ℝ)))) habs
  apply hmain.congr_deriv
  rw [gammaSixFilteredBoundaryConfluentFluxPrimeTerm,
    xiMassPrimeSquareEulerWeight_eq, xiMassPrimeSquareEulerWeight_eq]
  have hp := Real.rpow_add hp0
  rw [show -(1 + 2 * (t / 2)) = -1 + -t by ring,
    show -(1 + 2 * t) = -1 + (-t + -t) by ring,
    hp, hp, hp, Real.rpow_neg_one]
  norm_num
  ring

theorem summable_gammaSixFilteredBoundaryConfluentFluxPrimeTerm
    {m : ℕ} {t : ℝ} (ht : 0 < t) :
    Summable (gammaSixFilteredBoundaryConfluentFluxPrimeTerm m t) := by
  exact ((summable_xiMassPrimeSquareEulerWeight (half_pos ht)).sub
    (summable_xiMassPrimeSquareEulerWeight ht)).mul_left _

/-- Total right-hand flux of the coefficientwise-confluent boundary layer. -/
def gammaSixFilteredBoundaryConfluentFlux (m : ℕ) (t : ℝ) : ℝ :=
  ∑' p : Nat.Primes, gammaSixFilteredBoundaryConfluentFluxPrimeTerm m t p

theorem gammaSixFilteredBoundaryConfluentFlux_eq_hardyGreen_difference
    {m : ℕ} {t : ℝ} (ht : 0 < t) :
    gammaSixFilteredBoundaryConfluentFlux m t =
      (Real.log 2 / (4 * (m : ℝ) ^ 2)) *
        (HedenmalmThetaSource.thetaPhysicalEndpointPrimeHardyGreenEnergy (t / 2) -
          HedenmalmThetaSource.thetaPhysicalEndpointPrimeHardyGreenEnergy t) := by
  rw [gammaSixFilteredBoundaryConfluentFlux]
  simp only [gammaSixFilteredBoundaryConfluentFluxPrimeTerm]
  rw [tsum_mul_left,
    (summable_xiMassPrimeSquareEulerWeight (half_pos ht)).tsum_sub
      (summable_xiMassPrimeSquareEulerWeight ht),
    HedenmalmThetaSource.thetaPhysicalEndpointPrimeHardyGreenEnergy,
    HedenmalmThetaSource.thetaPhysicalEndpointPrimeHardyGreenEnergy]
  ring

theorem tendsto_depth_mul_gammaSixFilteredBoundaryConfluentFlux
    {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun t : ℝ => t * gammaSixFilteredBoundaryConfluentFlux m t)
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.log 2 / (m : ℝ) ^ 2)) := by
  have hmap : Tendsto (fun t : ℝ => t / 2)
      (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hbase : Tendsto (fun t : ℝ => t) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
        nhdsWithin_le_nhds
      simpa using hbase.div_const 2
    · filter_upwards [self_mem_nhdsWithin] with t ht
      change 0 < t at ht
      exact half_pos ht
  have hhalf :=
    HedenmalmThetaSource.tendsto_depth_mul_thetaPhysicalEndpointPrimeHardyGreenEnergy.comp hmap
  have hhalf' : Tendsto (fun t : ℝ =>
      t * HedenmalmThetaSource.thetaPhysicalEndpointPrimeHardyGreenEnergy (t / 2))
      (𝓝[>] (0 : ℝ)) (𝓝 8) := by
    change Tendsto (fun t : ℝ =>
      (t / 2) * HedenmalmThetaSource.thetaPhysicalEndpointPrimeHardyGreenEnergy (t / 2))
      (𝓝[>] (0 : ℝ)) (𝓝 4) at hhalf
    have h := hhalf.const_mul 2
    convert h using 1
    · funext t
      ring
    · norm_num
  have hfull :=
    HedenmalmThetaSource.tendsto_depth_mul_thetaPhysicalEndpointPrimeHardyGreenEnergy
  have hdiff := hhalf'.sub hfull
  have hscaled := hdiff.const_mul (Real.log 2 / (4 * (m : ℝ) ^ 2))
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have htarget : Tendsto (fun t : ℝ =>
      (Real.log 2 / (4 * (m : ℝ) ^ 2)) *
        (t * HedenmalmThetaSource.thetaPhysicalEndpointPrimeHardyGreenEnergy (t / 2) -
          t * HedenmalmThetaSource.thetaPhysicalEndpointPrimeHardyGreenEnergy t))
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.log 2 / (m : ℝ) ^ 2)) := by
    convert hscaled using 1
    congr 1
    field_simp [hm0]
    norm_num
  refine htarget.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 0 < t at ht
  rw [gammaSixFilteredBoundaryConfluentFlux_eq_hardyGreen_difference ht]
  ring

end

end RHTower
