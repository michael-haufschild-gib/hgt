import GaloisForLFunctions.RHTower.BornTemperatureFactorType
import GaloisForLFunctions.RHTower.PrimeSeamDampingAperture
import GaloisForLFunctions.RHTower.XiMobiusSchurValuationIntertwiner
import GaloisForLFunctions.RHTower.XiRationalHurwitzDyadicRefinement

/-!
# The Möbius Schur metric sees the critical strip, not the critical line

This module inserts the normalized rational-Hurwitz reflection energy into the canonical all-prime
Möbius Schur RKHS.  The resulting positive energy is summable exactly at the unit damping aperture:

`rho.re = 1 / 2 ∨ |2 * rho.re - 1| < 1`.

Hence it is summable on every Xi zero unconditionally.  The canonical source metric solves Hilbert
membership, but it does not solve RH; a contraction or a cofinal zero-loss estimate remains the
irreducible interface.
-/

namespace RHTower

noncomputable section

/-- The residual local Schur factor after extracting the reciprocal-prime square. -/
def xiMobiusPrimeSchurLorentzApertureFactor (p : Nat.Primes) : ℝ :=
  let q := xiTransversePrimeApertureDiskNode 1 p
  (1 - q) / (1 + q) ^ 3

/-- The local Schur factor is positive. -/
theorem xiMobiusPrimeSchurLorentzApertureFactor_pos (p : Nat.Primes) :
    0 < xiMobiusPrimeSchurLorentzApertureFactor p := by
  let q := xiTransversePrimeApertureDiskNode 1 p
  have hq0 : 0 < q := xiTransversePrimeApertureDiskNode_pos 1 p
  have hq1 : q < 1 := xiTransversePrimeApertureDiskNode_lt_one (by norm_num) p
  exact div_pos (sub_pos.mpr hq1) (by positivity)

/-- The local Schur factor is at most one. -/
theorem xiMobiusPrimeSchurLorentzApertureFactor_le_one (p : Nat.Primes) :
    xiMobiusPrimeSchurLorentzApertureFactor p ≤ 1 := by
  let q := xiTransversePrimeApertureDiskNode 1 p
  have hq0 : 0 ≤ q := (xiTransversePrimeApertureDiskNode_pos 1 p).le
  have hq1 : q < 1 := xiTransversePrimeApertureDiskNode_lt_one (by norm_num) p
  have hden : 0 < (1 + q) ^ 3 := by positivity
  rw [xiMobiusPrimeSchurLorentzApertureFactor]
  change (1 - q) / (1 + q) ^ 3 ≤ 1
  rw [div_le_one hden]
  nlinarith [sq_nonneg q, mul_nonneg (sq_nonneg q) hq0]

/-- The prime-two channel gives a uniform positive lower bound for the local Schur factor. -/
theorem four_div_twenty_seven_le_xiMobiusPrimeSchurLorentzApertureFactor
    (p : Nat.Primes) :
    (4 : ℝ) / 27 ≤ xiMobiusPrimeSchurLorentzApertureFactor p := by
  let q := xiTransversePrimeApertureDiskNode 1 p
  have hq0 : 0 ≤ q := (xiTransversePrimeApertureDiskNode_pos 1 p).le
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.prop.two_le
  have hqhalf : q ≤ 1 / 2 := by
    rw [show q = ((p : ℝ))⁻¹ by
      exact xiTransversePrimeApertureDiskNode_one_eq_inv p]
    simpa only [one_div] using
      (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hp2)
  have hden : 0 < (1 + q) ^ 3 := by positivity
  have hpoly :
      0 ≤ (1 - 2 * q) * (2 * q ^ 2 + 7 * q + 23) := by
    exact mul_nonneg (by linarith) (by positivity)
  have hmain : 4 * (1 + q) ^ 3 ≤ 27 * (1 - q) := by
    have hid :
        27 * (1 - q) - 4 * (1 + q) ^ 3 =
          (1 - 2 * q) * (2 * q ^ 2 + 7 * q + 23) := by ring
    linarith
  rw [xiMobiusPrimeSchurLorentzApertureFactor]
  change (4 : ℝ) / 27 ≤ (1 - q) / (1 + q) ^ 3
  rw [le_div_iff₀ hden]
  nlinarith

/-- At a prime scale, the normalized seam energy is exactly `p / 4` times the real reflected
prime-clock amplitude. -/
theorem normalizedScaleSeamEnergy_prime_eq_primeClockReflectionEnergy
    (rho : ℂ) (p : Nat.Primes) :
    normalizedScaleSeamEnergy (p : ℕ) rho =
      (p : ℝ) / 4 * primeClockReflectionEnergy rho.re p := by
  have hlog : Real.log (p : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast p.prop.one_lt)).ne'
  rw [normalizedScaleSeamEnergy,
    norm_sq_orbitwiseNatPrimeSeamCharge_eq_log_sq_mul_primeClockReflectionEnergy]
  field_simp [hlog]

/-- The Möbius Schur metric applied to the normalized reflected finite-value transfer. -/
def xiMobiusPrimeSchurNormalizedReflectionEnergy
    (rho : ℂ) (p : Nat.Primes) : ℝ :=
  xiMobiusPrimeSchurDifferenceKernel p p *
    normalizedScaleSeamEnergy (p : ℕ) rho

/-- On the open strip, this is literally the Möbius metric applied to the finite
rational-Hurwitz reflection energy. -/
theorem xiMobiusPrimeSchurNormalizedReflectionEnergy_eq_rationalHurwitz
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1) (p : Nat.Primes) :
    xiMobiusPrimeSchurNormalizedReflectionEnergy rho p =
      xiMobiusPrimeSchurDifferenceKernel p p *
        normalizedRationalHurwitzReflectionEnergy (p : ℕ) rho := by
  rw [xiMobiusPrimeSchurNormalizedReflectionEnergy,
    normalizedRationalHurwitzReflectionEnergy_eq_scale hstrip]

/-- Exact source/value splice.  The Möbius metric is the unit-damped amplitude metric, multiplied
by its intrinsic local Schur factor and the universal normalization `1 / 4`. -/
theorem xiMobiusPrimeSchurNormalizedReflectionEnergy_eq_apertureFactor
    (rho : ℂ) (p : Nat.Primes) :
    xiMobiusPrimeSchurNormalizedReflectionEnergy rho p =
      xiMobiusPrimeSchurLorentzApertureFactor p / 4 *
        weightedPrimeClockReflectionEnergy 1 rho.re p := by
  let q := xiTransversePrimeApertureDiskNode 1 p
  let P : ℝ := p
  have hp0 : 0 < P := by
    dsimp only [P]
    exact_mod_cast p.prop.pos
  have hq : q = P⁻¹ := by
    exact xiTransversePrimeApertureDiskNode_one_eq_inv p
  have hqP : q * P = 1 := by
    rw [hq]
    exact inv_mul_cancel₀ hp0.ne'
  have hqSqP : q ^ 2 * P = q := by
    calc
      q ^ 2 * P = q * (q * P) := by ring
      _ = q := by rw [hqP, mul_one]
  have hcore : q ^ 2 * P = P⁻¹ := by rw [hqSqP, hq]
  rw [xiMobiusPrimeSchurNormalizedReflectionEnergy,
    xiMobiusPrimeSchurDifferenceKernel_self,
    normalizedScaleSeamEnergy_prime_eq_primeClockReflectionEnergy]
  change q ^ 2 * (1 - q) / (1 + q) ^ 3 *
      (P / 4 * primeClockReflectionEnergy rho.re p) = _
  rw [xiMobiusPrimeSchurLorentzApertureFactor,
    weightedPrimeClockReflectionEnergy]
  change q ^ 2 * (1 - q) / (1 + q) ^ 3 *
      (P / 4 * primeClockReflectionEnergy rho.re p) =
    ((1 - q) / (1 + q) ^ 3) / 4 *
      (P ^ (-1 : ℝ) * primeClockReflectionEnergy rho.re p)
  rw [Real.rpow_neg_one]
  calc
    q ^ 2 * (1 - q) / (1 + q) ^ 3 *
        (P / 4 * primeClockReflectionEnergy rho.re p) =
      ((1 - q) / (1 + q) ^ 3) / 4 *
        ((q ^ 2 * P) * primeClockReflectionEnergy rho.re p) := by ring
    _ = _ := by rw [hcore]

/-- The normalized Möbius/Lorentz energy is nonnegative. -/
theorem xiMobiusPrimeSchurNormalizedReflectionEnergy_nonneg
    (rho : ℂ) (p : Nat.Primes) :
    0 ≤ xiMobiusPrimeSchurNormalizedReflectionEnergy rho p := by
  rw [xiMobiusPrimeSchurNormalizedReflectionEnergy_eq_apertureFactor]
  exact mul_nonneg
    (div_nonneg (xiMobiusPrimeSchurLorentzApertureFactor_pos p).le (by norm_num))
    (mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (sq_nonneg _))

/-- Uniform lower comparison with the unit-damped reflected prime amplitude. -/
theorem one_div_twenty_seven_mul_weightedPrimeClockReflectionEnergy_le_mobius
    (rho : ℂ) (p : Nat.Primes) :
    (1 : ℝ) / 27 * weightedPrimeClockReflectionEnergy 1 rho.re p ≤
      xiMobiusPrimeSchurNormalizedReflectionEnergy rho p := by
  rw [xiMobiusPrimeSchurNormalizedReflectionEnergy_eq_apertureFactor]
  have hfactor : (1 : ℝ) / 27 ≤
      xiMobiusPrimeSchurLorentzApertureFactor p / 4 := by
    have h := four_div_twenty_seven_le_xiMobiusPrimeSchurLorentzApertureFactor p
    linarith
  exact mul_le_mul_of_nonneg_right hfactor
    (mul_nonneg (Real.rpow_nonneg (by positivity) _) (sq_nonneg _))

/-- Uniform upper comparison with the unit-damped reflected prime amplitude. -/
theorem xiMobiusPrimeSchurNormalizedReflectionEnergy_le_weightedPrimeClockReflectionEnergy
    (rho : ℂ) (p : Nat.Primes) :
    xiMobiusPrimeSchurNormalizedReflectionEnergy rho p ≤
      weightedPrimeClockReflectionEnergy 1 rho.re p := by
  rw [xiMobiusPrimeSchurNormalizedReflectionEnergy_eq_apertureFactor]
  have hfactor : xiMobiusPrimeSchurLorentzApertureFactor p / 4 ≤ 1 := by
    have h := xiMobiusPrimeSchurLorentzApertureFactor_le_one p
    linarith [xiMobiusPrimeSchurLorentzApertureFactor_pos p]
  exact mul_le_of_le_one_left
    (mul_nonneg (Real.rpow_nonneg (by positivity) _) (sq_nonneg _)) hfactor

/-- **Exact Möbius/Lorentz aperture.**  The canonical source metric sees precisely the open
critical strip; the critical line is included as the identically zero seam. -/
theorem summable_xiMobiusPrimeSchurNormalizedReflectionEnergy_iff
    (rho : ℂ) :
    Summable (xiMobiusPrimeSchurNormalizedReflectionEnergy rho) ↔
      rho.re = 1 / 2 ∨ |2 * rho.re - 1| < 1 := by
  rw [show xiMobiusPrimeSchurNormalizedReflectionEnergy rho = fun p =>
      xiMobiusPrimeSchurLorentzApertureFactor p / 4 *
        weightedPrimeClockReflectionEnergy 1 rho.re p by
    funext p
    exact xiMobiusPrimeSchurNormalizedReflectionEnergy_eq_apertureFactor rho p]
  exact summable_mul_weightedPrimeClockReflectionEnergy_iff
    1 rho.re (fun p => xiMobiusPrimeSchurLorentzApertureFactor p / 4)
    (c := (1 : ℝ) / 27) (C := 1)
    (by norm_num)
    (fun p => by
      have h := four_div_twenty_seven_le_xiMobiusPrimeSchurLorentzApertureFactor p
      linarith)
    (fun p => by
      have h := xiMobiusPrimeSchurLorentzApertureFactor_le_one p
      linarith)

/-- Every Xi fibre belongs to the normalized Möbius/Lorentz Hilbert sector unconditionally.  Thus
Hilbert membership in this canonical positive source metric is not an RH criterion. -/
theorem summable_xiMobiusPrimeSchurNormalizedReflectionEnergy_of_xi_zero
    {rho : ℂ} (hzero : xi rho = 0) :
    Summable (xiMobiusPrimeSchurNormalizedReflectionEnergy rho) := by
  have hstrip := xi_zero_re_mem_open_unit hzero
  apply (summable_xiMobiusPrimeSchurNormalizedReflectionEnergy_iff rho).mpr
  exact Or.inr (abs_lt.mpr ⟨by linarith, by linarith⟩)

/-- Unconditional global Prop interface for the canonical Möbius/Lorentz source metric. -/
def XiMobiusSchurNormalizedReflectionEnergySummable : Prop :=
  ∀ rho : ℂ, xi rho = 0 →
    Summable (xiMobiusPrimeSchurNormalizedReflectionEnergy rho)

/-- The global membership proposition is discharged outright, without RH. -/
theorem xiMobiusSchurNormalizedReflectionEnergySummable :
    XiMobiusSchurNormalizedReflectionEnergySummable :=
  fun _ hzero =>
    summable_xiMobiusPrimeSchurNormalizedReflectionEnergy_of_xi_zero hzero

end

end RHTower
