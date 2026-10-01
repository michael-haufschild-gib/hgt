import GaloisForLFunctions.RHTower.CompactGaussianRetainedFirstMean
import GaloisForLFunctions.RHTower.CompactGaussianNormalizedChannel
import GaloisForLFunctions.RHTower.SmoothAFEReflectedWindowBoundedCentreEvent
import GaloisForLFunctions.RHTower.SteinhausFreePrimeWindow

open Complex Finset
noncomputable section
namespace RHTower
open SteinhausModel

/-- Removing the common spectral row gives precisely the power used by the
normalized carrier, with no residual phase or size factor. -/
theorem reflectedCompactGaussianRow_mul_normalization (s : ℂ) {N : ℝ}
    (hN : 0 < N) (tau : ℝ) :
    reflectedCompactGaussianRow s N tau * (N : ℂ) ^ ((1 / 2 : ℂ) - s) =
      zetaChi (s + (tau : ℂ) * I) := by
  have hNC : (N : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hN.ne'
  have hsqrt : (Real.sqrt N : ℂ) = (N : ℂ) ^ (1 / 2 : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hN.le]
    norm_num
  unfold reflectedCompactGaussianRow
  rw [hsqrt]
  calc
    _ = zetaChi (s + (tau : ℂ) * I) *
        ((N : ℂ) ^ (1 / 2 : ℂ) * (N : ℂ) ^ (s - 1) * (N : ℂ) ^ ((1 / 2 : ℂ) - s)) := by ring
    _ = _ := by
      rw [← Complex.cpow_add _ _ hNC, ← Complex.cpow_add _ _ hNC,
        show (1 / 2 : ℂ) + (s - 1) + (1 / 2 - s) = 0 by ring,
        Complex.cpow_zero, mul_one]

/-- The literal original retained background equals the exact normalized
arithmetic carrier after one common logarithmic phase rotation. -/
theorem reflectedPrimalRetainedBackground_eq_compactGaussianRetainedCarrier
    (d b tau : ℝ) {N : ℕ} (hN : 0 < N) (L : ℕ) (S : Finset ℕ) (ω : Omega) :
    reflectedPrimalRetainedBackground d (tau + b) N L S ω =
      reflectedCompactGaussianRow (rightDisplacedLinePt d b) N tau *
        compactGaussianRetainedCarrier (rightDisplacedLinePt d b) N L S
          (steinhausLogPhaseShift ω tau) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  let s := rightDisplacedLinePt d b
  have hz : rightDisplacedLinePt d (tau + b) = s + (tau : ℂ) * I := by
    dsimp only [s, rightDisplacedLinePt]
    push_cast
    ring
  unfold reflectedPrimalRetainedBackground compactGaussianRetainedCarrier
  rw [← mul_assoc, reflectedCompactGaussianRow_mul_normalization _ hNR, mul_sum]
  apply sum_congr rfl
  intro n hn
  have hnpos : 0 < n := (Sieve.mem_smoothUpTo.mp hn).1.1
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hnpos.ne'
  rw [reflectedPrimalPositiveCoefficient_eq_power_cutoff _ _ _ _ hnpos,
    X_steinhausLogPhaseShift ω tau hnpos.ne', one_mul, hz]
  change zetaChi (s + (tau : ℂ) * I) * (n : ℂ) ^ (s + (tau : ℂ) * I - 1) *
    smoothAFECutoff ((n : ℝ) / N) * X n ω = _
  rw [show s + (tau : ℂ) * I - 1 = (s - 1) + (tau : ℂ) * I by ring,
    Complex.cpow_add _ _ hnC]
  ring

/-- Complete exact frozen finite-carrier assembly into the retained normalized
background and actual free-window channels. -/
theorem reflectedPrimalFrozenWindow_eq_compactGaussian
    (d b tau : ℝ) (L N Y : ℕ) (hN : 0 < N)
    (hYN : Y ≤ N) (hNL : N ≤ L) (hLY : L < Y * Y) (ω ξ : Omega) :
    (∑ n ∈ Icc 1 L, smoothAFEZetaRightReflectedPrimalPositiveCoefficient d (tau + b) 1 N n *
      X n (freezeSteinhausPrefix (steinhausWindowRetainedPrimes L N Y) ω ξ)) =
      reflectedCompactGaussianRow (rightDisplacedLinePt d b) N tau *
        (compactGaussianRetainedCarrier (rightDisplacedLinePt d b) N L
          (steinhausWindowRetainedPrimes L N Y) (steinhausLogPhaseShift ω tau) +
          ∑ p ∈ largePrimes N Y, charFactor 1 (ξ p) *
            compactGaussianNormalizedPrimeChannel (rightDisplacedLinePt d b) N p tau (L / p)
              (steinhausLogPhaseShift ω tau)) := by
  rw [steinhausCarrier_freeze_window_eq_smooth_add_circleChannels _ L N Y hYN hNL hLY]
  change reflectedPrimalRetainedBackground d (tau + b) N L
    (steinhausWindowRetainedPrimes L N Y) ω + _ = _
  rw [reflectedPrimalRetainedBackground_eq_compactGaussianRetainedCarrier _ _ _ hN,
    mul_add, mul_sum]
  congr 1
  apply sum_congr rfl
  intro p hp
  have hppos : 0 < p := (mem_largePrimes.mp hp).1.2.pos
  rw [reflectedPrimalChannel_eq_compactGaussianNormalizedPrimeChannel _ _ _ _ _ _ hN hppos]
  ring

end RHTower
