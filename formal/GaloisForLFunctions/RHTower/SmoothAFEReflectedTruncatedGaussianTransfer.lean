import GaloisForLFunctions.RHTower.SteinhausFullGaussianTruncation
import GaloisForLFunctions.RHTower.SmoothAFEReflectedCofactorTransfer


open Finset Complex
noncomputable section
namespace RHTower

/-- The actual reflected-primal channel with independently chosen polynomial cutoff and
smoothing scale is exactly a truncated full-Gaussian cofactor. Common height is absorbed by
one logarithmic phase shift; no floor-dependent smoothing approximation is used. -/
theorem reflectedPrimalChannel_eq_truncatedFullGaussianCofactor
    (d b tau : ℝ) (N L p : ℕ) (hN : 0 < N) (hp : 0 < p)
    (ω : SteinhausModel.Omega) :
    steinhausLargePrimeChannel
      (smoothAFEZetaRightReflectedPrimalPositiveCoefficient d (tau + b) 1 N) L p ω =
      (zetaChi (rightDisplacedLinePt d (tau + b)) *
        (p : ℂ) ^ (rightDisplacedLinePt d (tau + b) - 1)) *
      truncatedFullGaussianCofactor (rightDisplacedLinePt d b) ((N : ℝ) / p) (L / p)
        (steinhausLogPhaseShift ω tau) := by
  let s := rightDisplacedLinePt d b
  let z := rightDisplacedLinePt d (tau + b)
  have hz : z - 1 = (s - 1) + (tau : ℂ) * I := by
    simp only [s, z, rightDisplacedLinePt, Complex.ofReal_add]
    ring
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  unfold steinhausLargePrimeChannel
  rw [truncatedFullGaussianCofactor_eq_Icc, mul_sum]
  apply sum_congr rfl
  intro m hm
  have hmpos : 0 < m := lt_of_lt_of_le Nat.zero_lt_one (mem_Icc.mp hm).1
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hmpos.ne'
  have hmul : ((p * m : ℕ) : ℂ) ^ (z - 1) =
      (p : ℂ) ^ (z - 1) * (m : ℂ) ^ (z - 1) := by
    simpa only [Complex.ofReal_natCast, Nat.cast_mul] using
      Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg p) (Nat.cast_nonneg m) (z - 1)
  rw [reflectedPrimalPositiveCoefficient_eq_power_cutoff _ _ _ _ (Nat.mul_pos hp hmpos),
    X_steinhausLogPhaseShift ω tau hmpos.ne']
  change zetaChi z * ((p * m : ℕ) : ℂ) ^ (z - 1) *
    smoothAFECutoff (1 * (((p * m : ℕ) : ℝ) / N)) * SteinhausModel.X m ω =
    (zetaChi z * (p : ℂ) ^ (z - 1)) *
      ((SteinhausModel.X m ω * (m : ℂ) ^ ((tau : ℂ) * I)) * (m : ℂ) ^ (s - 1) *
        smoothAFECutoff ((m : ℝ) / ((N : ℝ) / p)))
  have hpow : (m : ℂ) ^ (z - 1) = (m : ℂ) ^ (s - 1) * (m : ℂ) ^ ((tau : ℂ) * I) := by
    rw [hz, Complex.cpow_add _ _ hmC]
  have hcut : (1 : ℝ) * (((p * m : ℕ) : ℝ) / N) = (m : ℝ) / ((N : ℝ) / p) := by
    push_cast
    field_simp [hNR, hpR]
  rw [hmul, hpow, hcut]
  ring

end RHTower
