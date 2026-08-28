import GaloisForLFunctions.RHTower.XiGammaSixFilteredBoundaryConfluentFlux

/-!
# Literal Gamma-six collision-current residue

The coefficientwise-confluent counterterm becomes the literal filtered Gamma-six jet after
multiplication by its three radial Gauss/Gamma/Fisher factors.  These factors preserve absolute
summability of the differentiated current at every positive depth.  Their loss from one is only
`O_m(1/p)`, so the lost flux has a uniform `log p / p^2` majorant and disappears after depth
scaling.  Consequently the literal current retains the complete nonzero wall residue
`log 2 / m^2`.

This is an unconditional HC source theorem.  It does not identify the filtered current with the
multiplicity-faithful Gauss--Hodge RH receiver; instead it gives a residue constraint that any
such identification must respect.
-/

open Complex Set Filter Topology
open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- Prime-local radial factor retained by the literal filtered Gamma-six jet. -/
def gammaSixFilteredBoundaryRadialFactor (m : ℕ) (p : Nat.Primes) : ℝ :=
  (1 - (p : ℝ)⁻¹) ^ (2 * m) *
    (1 - (p : ℝ) ^ (-(m : ℝ))) ^ 2 *
    (1 / (1 + (p : ℝ)⁻¹) ^ 2)

private theorem one_sub_three_mul_le_sum_defects'
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
theorem gammaSixFilteredBoundaryRadialFactor_bounds
    {m : ℕ} (hm : 1 ≤ m) (p : Nat.Primes) :
    0 ≤ gammaSixFilteredBoundaryRadialFactor m p ∧
      gammaSixFilteredBoundaryRadialFactor m p ≤ 1 ∧
      1 - gammaSixFilteredBoundaryRadialFactor m p ≤
        ((((2 * m : ℕ) : ℝ)) + 5) * (p : ℝ)⁻¹ := by
  let P : ℝ := p
  let z : ℝ := P⁻¹
  let a : ℝ := (1 - z) ^ (2 * m)
  let b : ℝ := (1 - P ^ (-(m : ℝ))) ^ 2
  let c : ℝ := 1 / (1 + z) ^ 2
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
        one_sub_three_mul_le_sum_defects' ha0 ha1 hb0 hb1 hc1
      _ ≤ (((2 * m : ℕ) : ℝ)) * z + 2 * z + 3 * z := by gcongr
      _ = ((((2 * m : ℕ) : ℝ)) + 5) * z := by ring
  change 0 ≤ a * b * c ∧ a * b * c ≤ 1 ∧
    1 - a * b * c ≤ ((((2 * m : ℕ) : ℝ)) + 5) * z
  exact ⟨hprod0, hprod1, hproddefect⟩

/-- Horizontal-depth interpolation whose specialization is the literal filtered second jet. -/
def gammaSixFilteredBoundaryInterpolatedSecondJet
    (m : ℕ) (t : ℝ) (p : Nat.Primes) : ℝ :=
  gammaSixFilteredBoundaryConfluentCounterterm m t p *
    gammaSixFilteredBoundaryRadialFactor m p

theorem gammaSixFilteredBoundaryInterpolatedSecondJet_specializes
    {m : ℕ} (hm : 1 ≤ m) (q : XiZeroCopy) (p : Nat.Primes) :
    gammaSixFilteredBoundaryInterpolatedSecondJet m
        (primeDepthBVWoldXiCenteredRate q.1) p =
      gammaSixFilteredBoundarySecondJet m q p := by
  rw [gammaSixFilteredBoundaryInterpolatedSecondJet,
    gammaSixFilteredBoundarySecondJet_eq_confluentCounterterm_mul hm]
  unfold gammaSixFilteredBoundaryRadialFactor
  ring

/-- Literal differentiated Gamma-six collision current. -/
def gammaSixFilteredBoundaryCollisionCurrentPrimeTerm
    (m : ℕ) (t : ℝ) (p : Nat.Primes) : ℝ :=
  gammaSixFilteredBoundaryConfluentFluxPrimeTerm m t p *
    gammaSixFilteredBoundaryRadialFactor m p

theorem hasDerivAt_gammaSixFilteredBoundaryInterpolatedSecondJet
    {m : ℕ} {t : ℝ} (ht : 0 < t) (p : Nat.Primes) :
    HasDerivAt (fun s : ℝ =>
      gammaSixFilteredBoundaryInterpolatedSecondJet m s p)
      (gammaSixFilteredBoundaryCollisionCurrentPrimeTerm m t p) t := by
  simpa [gammaSixFilteredBoundaryInterpolatedSecondJet,
    gammaSixFilteredBoundaryCollisionCurrentPrimeTerm] using
      (hasDerivAt_gammaSixFilteredBoundaryConfluentCounterterm m p ht).mul_const
        (gammaSixFilteredBoundaryRadialFactor m p)

theorem summable_gammaSixFilteredBoundaryCollisionCurrentPrimeTerm
    {m : ℕ} (hm : 1 ≤ m) {t : ℝ} (ht : 0 < t) :
    Summable (gammaSixFilteredBoundaryCollisionCurrentPrimeTerm m t) := by
  have hflux := summable_gammaSixFilteredBoundaryConfluentFluxPrimeTerm (m := m) ht
  apply Summable.of_norm_bounded hflux.norm
  intro p
  rw [gammaSixFilteredBoundaryCollisionCurrentPrimeTerm, norm_mul]
  have hA := gammaSixFilteredBoundaryRadialFactor_bounds hm p
  have hnormA : ‖gammaSixFilteredBoundaryRadialFactor m p‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hA.1]
    exact hA.2.1
  calc
    ‖gammaSixFilteredBoundaryConfluentFluxPrimeTerm m t p‖ *
        ‖gammaSixFilteredBoundaryRadialFactor m p‖ ≤
        ‖gammaSixFilteredBoundaryConfluentFluxPrimeTerm m t p‖ * 1 := by gcongr
    _ = ‖gammaSixFilteredBoundaryConfluentFluxPrimeTerm m t p‖ := by ring

private theorem xiMassPrimeSquareEulerWeight_nonneg
    (d : ℝ) (p : Nat.Primes) :
    0 ≤ xiMassPrimeSquareEulerWeight d p := by
  rw [xiMassPrimeSquareEulerWeight_eq]
  positivity

private theorem xiMassPrimeSquareEulerWeight_antitone
    {d₁ d₂ : ℝ} (h : d₁ ≤ d₂) (p : Nat.Primes) :
    xiMassPrimeSquareEulerWeight d₂ p ≤
      xiMassPrimeSquareEulerWeight d₁ p := by
  rw [xiMassPrimeSquareEulerWeight_eq, xiMassPrimeSquareEulerWeight_eq]
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.2.one_lt.le
  have hpow := Real.rpow_le_rpow_of_exponent_le hp1
    (show -(1 + 2 * d₂) ≤ -(1 + 2 * d₁) by linarith)
  exact mul_le_mul_of_nonneg_left hpow (Real.log_nonneg hp1)

theorem gammaSixFilteredBoundaryConfluentFluxPrimeTerm_nonneg
    {m : ℕ} (hm : 1 ≤ m) {t : ℝ} (ht : 0 < t) (p : Nat.Primes) :
    0 ≤ gammaSixFilteredBoundaryConfluentFluxPrimeTerm m t p := by
  rw [gammaSixFilteredBoundaryConfluentFluxPrimeTerm]
  have hmono := xiMassPrimeSquareEulerWeight_antitone
    (show t / 2 ≤ t by linarith) p
  have hC : 0 ≤ Real.log 2 / (m : ℝ) ^ 2 := by positivity
  positivity

theorem gammaSixFilteredBoundaryConfluentFluxPrimeTerm_le_zeroDepthWeight
    {m : ℕ} (hm : 1 ≤ m) {t : ℝ} (ht : 0 < t) (p : Nat.Primes) :
    gammaSixFilteredBoundaryConfluentFluxPrimeTerm m t p ≤
      2 * (Real.log 2 / (m : ℝ) ^ 2) *
        xiMassPrimeSquareEulerWeight 0 p := by
  rw [gammaSixFilteredBoundaryConfluentFluxPrimeTerm]
  have hC : 0 ≤ 2 * (Real.log 2 / (m : ℝ) ^ 2) := by positivity
  have hnonneg := xiMassPrimeSquareEulerWeight_nonneg t p
  have hsub : xiMassPrimeSquareEulerWeight (t / 2) p -
      xiMassPrimeSquareEulerWeight t p ≤
        xiMassPrimeSquareEulerWeight (t / 2) p := sub_le_self _ hnonneg
  have hmono := xiMassPrimeSquareEulerWeight_antitone
    (show (0 : ℝ) ≤ t / 2 by linarith) p
  exact mul_le_mul_of_nonneg_left (hsub.trans hmono) hC

/-- Differentiated radial loss between confluent and literal currents. -/
def gammaSixFilteredBoundaryCollisionCurrentLossPrimeTerm
    (m : ℕ) (t : ℝ) (p : Nat.Primes) : ℝ :=
  gammaSixFilteredBoundaryConfluentFluxPrimeTerm m t p *
    (1 - gammaSixFilteredBoundaryRadialFactor m p)

private theorem zeroDepthWeight_mul_inv_eq_halfDepthWeight
    (p : Nat.Primes) :
    xiMassPrimeSquareEulerWeight 0 p * (p : ℝ)⁻¹ =
      xiMassPrimeSquareEulerWeight (1 / 2) p := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.pos
  rw [xiMassPrimeSquareEulerWeight_eq, xiMassPrimeSquareEulerWeight_eq]
  rw [show -(1 + 2 * (0 : ℝ)) = -1 by norm_num,
    show -(1 + 2 * (1 / 2 : ℝ)) = -1 + -1 by norm_num,
    Real.rpow_add hp0, Real.rpow_neg_one]
  ring

theorem gammaSixFilteredBoundaryCollisionCurrentLossPrimeTerm_bounds
    {m : ℕ} (hm : 1 ≤ m) {t : ℝ} (ht : 0 < t) (p : Nat.Primes) :
    0 ≤ gammaSixFilteredBoundaryCollisionCurrentLossPrimeTerm m t p ∧
      gammaSixFilteredBoundaryCollisionCurrentLossPrimeTerm m t p ≤
        (2 * (Real.log 2 / (m : ℝ) ^ 2) *
          ((((2 * m : ℕ) : ℝ)) + 5)) *
            xiMassPrimeSquareEulerWeight (1 / 2) p := by
  have hflux0 := gammaSixFilteredBoundaryConfluentFluxPrimeTerm_nonneg hm ht p
  have hflux := gammaSixFilteredBoundaryConfluentFluxPrimeTerm_le_zeroDepthWeight hm ht p
  have hA := gammaSixFilteredBoundaryRadialFactor_bounds hm p
  have hloss0 : 0 ≤ 1 - gammaSixFilteredBoundaryRadialFactor m p :=
    sub_nonneg.mpr hA.2.1
  rw [gammaSixFilteredBoundaryCollisionCurrentLossPrimeTerm]
  constructor
  · exact mul_nonneg hflux0 hloss0
  · calc
      gammaSixFilteredBoundaryConfluentFluxPrimeTerm m t p *
          (1 - gammaSixFilteredBoundaryRadialFactor m p) ≤
        (2 * (Real.log 2 / (m : ℝ) ^ 2) *
          xiMassPrimeSquareEulerWeight 0 p) *
            (((((2 * m : ℕ) : ℝ)) + 5) * (p : ℝ)⁻¹) := by
        exact mul_le_mul hflux hA.2.2 hloss0
          (mul_nonneg (by positivity)
            (xiMassPrimeSquareEulerWeight_nonneg 0 p))
      _ = (2 * (Real.log 2 / (m : ℝ) ^ 2) *
          ((((2 * m : ℕ) : ℝ)) + 5)) *
            xiMassPrimeSquareEulerWeight (1 / 2) p := by
        rw [← zeroDepthWeight_mul_inv_eq_halfDepthWeight]
        ring

theorem summable_gammaSixFilteredBoundaryCollisionCurrentLossPrimeTerm
    {m : ℕ} (hm : 1 ≤ m) {t : ℝ} (ht : 0 < t) :
    Summable (gammaSixFilteredBoundaryCollisionCurrentLossPrimeTerm m t) := by
  have hmajor := (summable_xiMassPrimeSquareEulerWeight
    (show (0 : ℝ) < 1 / 2 by norm_num)).mul_left
      (2 * (Real.log 2 / (m : ℝ) ^ 2) * ((((2 * m : ℕ) : ℝ)) + 5))
  apply Summable.of_nonneg_of_le
    (fun p => (gammaSixFilteredBoundaryCollisionCurrentLossPrimeTerm_bounds hm ht p).1)
    (fun p => (gammaSixFilteredBoundaryCollisionCurrentLossPrimeTerm_bounds hm ht p).2)
    hmajor

/-- Total literal differentiated collision current. -/
def gammaSixFilteredBoundaryCollisionCurrent (m : ℕ) (t : ℝ) : ℝ :=
  ∑' p : Nat.Primes, gammaSixFilteredBoundaryCollisionCurrentPrimeTerm m t p

/-- Total differentiated loss caused by the radial local factors. -/
def gammaSixFilteredBoundaryCollisionCurrentLoss (m : ℕ) (t : ℝ) : ℝ :=
  ∑' p : Nat.Primes, gammaSixFilteredBoundaryCollisionCurrentLossPrimeTerm m t p

theorem gammaSixFilteredBoundaryConfluentFlux_eq_collision_add_loss
    {m : ℕ} (hm : 1 ≤ m) {t : ℝ} (ht : 0 < t) :
    gammaSixFilteredBoundaryConfluentFlux m t =
      gammaSixFilteredBoundaryCollisionCurrent m t +
        gammaSixFilteredBoundaryCollisionCurrentLoss m t := by
  have hcollision := summable_gammaSixFilteredBoundaryCollisionCurrentPrimeTerm hm ht
  have hloss := summable_gammaSixFilteredBoundaryCollisionCurrentLossPrimeTerm hm ht
  rw [gammaSixFilteredBoundaryConfluentFlux,
    gammaSixFilteredBoundaryCollisionCurrent,
    gammaSixFilteredBoundaryCollisionCurrentLoss, ← hcollision.tsum_add hloss]
  apply tsum_congr
  intro p
  rw [gammaSixFilteredBoundaryCollisionCurrentPrimeTerm,
    gammaSixFilteredBoundaryCollisionCurrentLossPrimeTerm]
  ring

theorem gammaSixFilteredBoundaryCollisionCurrentLoss_bounds
    {m : ℕ} (hm : 1 ≤ m) {t : ℝ} (ht : 0 < t) :
    0 ≤ gammaSixFilteredBoundaryCollisionCurrentLoss m t ∧
      gammaSixFilteredBoundaryCollisionCurrentLoss m t ≤
        (2 * (Real.log 2 / (m : ℝ) ^ 2) *
          ((((2 * m : ℕ) : ℝ)) + 5)) *
            (∑' p : Nat.Primes, xiMassPrimeSquareEulerWeight (1 / 2) p) := by
  have hloss := summable_gammaSixFilteredBoundaryCollisionCurrentLossPrimeTerm hm ht
  have hmajor := (summable_xiMassPrimeSquareEulerWeight
    (show (0 : ℝ) < 1 / 2 by norm_num)).mul_left
      (2 * (Real.log 2 / (m : ℝ) ^ 2) * ((((2 * m : ℕ) : ℝ)) + 5))
  rw [gammaSixFilteredBoundaryCollisionCurrentLoss]
  constructor
  · exact tsum_nonneg fun p =>
      (gammaSixFilteredBoundaryCollisionCurrentLossPrimeTerm_bounds hm ht p).1
  · calc
      (∑' p : Nat.Primes, gammaSixFilteredBoundaryCollisionCurrentLossPrimeTerm m t p) ≤
          ∑' p : Nat.Primes,
            (2 * (Real.log 2 / (m : ℝ) ^ 2) *
              ((((2 * m : ℕ) : ℝ)) + 5)) *
                xiMassPrimeSquareEulerWeight (1 / 2) p :=
        hloss.tsum_le_tsum
          (fun p => (gammaSixFilteredBoundaryCollisionCurrentLossPrimeTerm_bounds hm ht p).2)
          hmajor
      _ = (2 * (Real.log 2 / (m : ℝ) ^ 2) *
          ((((2 * m : ℕ) : ℝ)) + 5)) *
            (∑' p : Nat.Primes, xiMassPrimeSquareEulerWeight (1 / 2) p) := by
        rw [tsum_mul_left]

theorem tendsto_depth_mul_gammaSixFilteredBoundaryCollisionCurrentLoss
    {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun t : ℝ =>
      t * gammaSixFilteredBoundaryCollisionCurrentLoss m t)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let M : ℝ :=
    (2 * (Real.log 2 / (m : ℝ) ^ 2) * ((((2 * m : ℕ) : ℝ)) + 5)) *
      (∑' p : Nat.Primes, xiMassPrimeSquareEulerWeight (1 / 2) p)
  have hM0 : 0 ≤ M := by
    have hsum0 : 0 ≤ ∑' p : Nat.Primes,
        xiMassPrimeSquareEulerWeight (1 / 2) p :=
      tsum_nonneg fun p => xiMassPrimeSquareEulerWeight_nonneg (1 / 2) p
    dsimp [M]
    positivity
  have hbase : Tendsto (fun t : ℝ => t) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    nhdsWithin_le_nhds
  have hupper : Tendsto (fun t : ℝ => t * M)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using hbase.mul_const M
  refine squeeze_zero' ?_ ?_ hupper
  · filter_upwards [self_mem_nhdsWithin] with t ht
    change 0 < t at ht
    exact mul_nonneg ht.le (gammaSixFilteredBoundaryCollisionCurrentLoss_bounds hm ht).1
  · filter_upwards [self_mem_nhdsWithin] with t ht
    change 0 < t at ht
    exact mul_le_mul_of_nonneg_left
      (gammaSixFilteredBoundaryCollisionCurrentLoss_bounds hm ht).2 ht.le

/-- The literal differentiated Gamma-six collision current retains the complete wall residue. -/
theorem tendsto_depth_mul_gammaSixFilteredBoundaryCollisionCurrent
    {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun t : ℝ =>
      t * gammaSixFilteredBoundaryCollisionCurrent m t)
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.log 2 / (m : ℝ) ^ 2)) := by
  have hflux := tendsto_depth_mul_gammaSixFilteredBoundaryConfluentFlux hm
  have hloss := tendsto_depth_mul_gammaSixFilteredBoundaryCollisionCurrentLoss hm
  have hdiff := hflux.sub hloss
  have hdiff' : Tendsto (fun t : ℝ =>
      t * gammaSixFilteredBoundaryConfluentFlux m t -
        t * gammaSixFilteredBoundaryCollisionCurrentLoss m t)
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.log 2 / (m : ℝ) ^ 2)) := by
    simpa only [sub_zero] using hdiff
  refine hdiff'.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 0 < t at ht
  rw [gammaSixFilteredBoundaryConfluentFlux_eq_collision_add_loss hm ht]
  ring

end

end RHTower
