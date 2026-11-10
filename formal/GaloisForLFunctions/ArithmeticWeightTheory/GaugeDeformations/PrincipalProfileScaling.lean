import GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations.CharacterProfilePrimeSums

/-!
# Exact renormalization of an analytic principal mean

The principal mean of unit profiles need not itself be unitary. Its raw
prime sum nevertheless has the same exact logarithmic renormalization:
endpoint coefficient mass minus two supplies the quadratic parameter scale.
-/

open Complex Filter Topology Metric Set
open GaloisForLFunctions.ArithmeticCorrelationGeometry
open GaloisForLFunctions.PrimeTorusTheory
open _root_.RHTower
noncomputable section
set_option autoImplicit false
namespace GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations

theorem weightedPrimeLog_one (s : ℂ) : weightedPrimeLog (fun _ => 1) s = coronaPrimeZeta s := by
  simp only [weightedPrimeLog, one_mul, coronaPrimeZeta, coronaPrimeEigenvalue]

private theorem summable_principalProfileLog {Φ : ℂ → ℂ} {R : NNReal}
    (hR : 1 < (R : ℝ)) (hΦ : AnalyticOnNhd ℂ Φ (closedBall 0 R))
    {w : ℂ} (hw : 0 < w.re) :
    Summable (fun n : ℕ => smoothingTaylorCoefficient Φ n * Complex.log (w + (n : ℂ))) := by
  let C := |Real.log w.re| + ‖w‖ + Real.pi - 1
  apply Summable.of_norm_bounded (summable_smoothingTaylorCoefficient_weight hR hΦ C)
  intro n
  have hl : w.re ≤ (w + (n : ℂ)).re := by
    simp only [Complex.add_re, Complex.natCast_re]
    exact le_add_of_nonneg_right (Nat.cast_nonneg n)
  have hu : ‖w + (n : ℂ)‖ ≤ ‖w‖ + (n : ℝ) := by
    simpa only [Complex.norm_natCast] using norm_add_le w (n : ℂ)
  have hh := norm_log_le_linear hw hl hu (by positivity)
  rw [norm_mul]
  apply (mul_le_mul_of_nonneg_left hh (norm_nonneg _)).trans_eq
  dsimp only [C]
  ring

private theorem principal_scaled_shift_re {t : ℝ} (ht : 0 < t) {w : ℂ}
    (hw : 0 < w.re) (n : ℕ) : 1 < (1 + (t : ℂ) * (w + (n : ℂ))).re := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hh : 0 < t * (w.re + (n : ℝ)) := mul_pos ht (by linarith only [hw, hn])
  simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.natCast_re, zero_mul, sub_zero]
  linarith only [hh]

/-- The raw prime sum of an analytic mean has an exact quadratic renormalization;
no unit-modulus condition is imposed on that mean. -/
theorem principalProfilePrimeSum_scaled {Φ : ℂ → ℂ} {R : NNReal}
    (hR : 1 < (R : ℝ)) (hΦ : AnalyticOnNhd ℂ Φ (closedBall 0 R)) (h1 : Φ 1 = -1)
    {t : ℝ} (ht : 0 < t) {w : ℂ} (hw : 0 < w.re) :
    weightedProfilePrimeSum (fun _ => 1) Φ t (1 + (t : ℂ) * w) =
      2 * (Real.log t : ℂ) - analyticSmoothingScalingLog Φ 0 w +
        analyticSmoothingScaledRemainder Φ 0 t w := by
  have hs : 1 < (1 + (t : ℂ) * w).re := by
    simpa only [Nat.cast_zero, add_zero] using principal_scaled_shift_re ht hw 0
  have ha (p : Nat.Primes) : ‖(1 : ℂ)‖ ≤ 1 := by norm_num
  have hP := summable_weightedProfilePrimeLog hR hΦ ha ht.le hs
  have hL := summable_principalProfileLog hR hΦ hw
  have hconst := (Summable.of_norm (summable_norm_smoothingTaylorCoefficient hR hΦ)).mul_right
    (Real.log t : ℂ)
  have hterm (n : ℕ) : smoothingTaylorCoefficient Φ n *
      regularizedPrimeLog (1 + (t : ℂ) * (w + (n : ℂ))) =
        smoothingTaylorCoefficient Φ n * weightedPrimeLog (fun _ => 1)
          (1 + (t : ℂ) * w + (n : ℂ) * (t : ℂ)) +
        smoothingTaylorCoefficient Φ n * Complex.log (w + (n : ℂ)) +
        smoothingTaylorCoefficient Φ n * (Real.log t : ℂ) := by
    have hre : 0 < (w + (n : ℂ)).re := by
      simp only [Complex.add_re, Complex.natCast_re]
      exact add_pos_of_pos_of_nonneg hw (Nat.cast_nonneg n)
    have hne : w + (n : ℂ) ≠ 0 := by
      intro he
      rw [he, Complex.zero_re] at hre
      exact lt_irrefl 0 hre
    rw [weightedPrimeLog_one,
      show 1 + (t : ℂ) * w + (n : ℂ) * (t : ℂ) = 1 + (t : ℂ) * (w + (n : ℂ)) by ring,
      regularizedPrimeLog_of_re_gt_one (principal_scaled_shift_re ht hw n),
      add_sub_cancel_left, Complex.log_ofReal_mul ht hne]
    ring
  have hE : Summable (fun n : ℕ => smoothingTaylorCoefficient Φ n *
      regularizedPrimeLog (1 + (t : ℂ) * (w + (n : ℂ)))) :=
    ((hP.add hL).add hconst).congr (fun n => (hterm n).symm)
  rw [weightedProfilePrimeSum_shifted hR hΦ ha ht.le hs]
  calc
    _ = ∑' n : ℕ, ((smoothingTaylorCoefficient Φ n *
        regularizedPrimeLog (1 + (t : ℂ) * (w + (n : ℂ))) -
          smoothingTaylorCoefficient Φ n * Complex.log (w + (n : ℂ))) -
            smoothingTaylorCoefficient Φ n * (Real.log t : ℂ)) := by
      apply tsum_congr
      intro n
      linear_combination -(hterm n)
    _ = _ := by
      rw [(hE.sub hL).tsum_sub hconst, hE.tsum_sub hL, tsum_mul_right,
        tsum_smoothingTaylorCoefficient hR hΦ h1]
      simp only [analyticSmoothingScaledRemainder, analyticSmoothingScalingLog, Nat.add_zero]
      ring

#print axioms principalProfilePrimeSum_scaled
end GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations
