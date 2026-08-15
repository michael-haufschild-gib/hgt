import GaloisForLFunctions.RHTower.RealTwistDeficitTransfer
import GaloisForLFunctions.RHTower.Sieve.ZetaShiftedLineRate

/-!
# The unconditional Littlewood deficit on the shifted line

Littlewood's rate, transported to the abscissa `1 + 1/log x`, is uniform over the whole
polynomial frequency horizon `1 ≤ |τ| ≤ x^B`:

```text
|ζ(1 + 1/log x + iτ)| ≤ C_B log x / log log x,
```

so the one-line deficit of `log|ζ|` below its trivial scale is at least

```text
log log x - log |ζ(1 + 1/log x + iτ)| ≥ log log log x - O_B(1).
```

Three regimes are combined: the compact frequency range, where the harmonic truncation suffices;
the range where the Littlewood scale `L = log(τ/2π)` is below `√log x`, where the numerator is
small; and the range where it is above, where the denominator is large.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- The frequency threshold past which the Littlewood order conditions hold. -/
def littlewoodFreqThreshold : ℝ :=
  max (16 * Real.pi)
    (max (2 * Real.pi * Real.exp (Sieve.orderThreshold 2))
      (2 * Real.pi * Real.exp 2211904))

theorem littlewoodFreqThreshold_pos : 0 < littlewoodFreqThreshold := by
  have hπ := Real.pi_pos
  refine lt_of_lt_of_le (by positivity : (0:ℝ) < 16 * Real.pi) ?_
  exact le_max_left _ _

theorem sixteen_pi_le_littlewoodFreqThreshold : 16 * Real.pi ≤ littlewoodFreqThreshold :=
  le_max_left _ _

/-- Past the threshold, the Littlewood scale is large. -/
theorem littlewoodScale_ge {t : ℝ} (ht : littlewoodFreqThreshold ≤ t) :
    (2211904 : ℝ) ≤ Real.log (t / (2 * Real.pi)) := by
  have hπ := Real.pi_pos
  have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
  have hle : 2 * Real.pi * Real.exp 2211904 ≤ t :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) ht
  have hquot : Real.exp 2211904 ≤ t / (2 * Real.pi) := by
    rw [le_div_iff₀ h2π]
    linarith
  have h := Real.log_le_log (Real.exp_pos 2211904) hquot
  rwa [Real.log_exp] at h

theorem orderThreshold_le_of_ge {t : ℝ} (ht : littlewoodFreqThreshold ≤ t) :
    Sieve.orderThreshold 2 ≤ Real.log (t / (2 * Real.pi)) := by
  have hπ := Real.pi_pos
  have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
  have hle : 2 * Real.pi * Real.exp (Sieve.orderThreshold 2) ≤ t :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) ht
  have hquot : Real.exp (Sieve.orderThreshold 2) ≤ t / (2 * Real.pi) := by
    rw [le_div_iff₀ h2π]
    linarith
  have h := Real.log_le_log (Real.exp_pos _) hquot
  rwa [Real.log_exp] at h

/-- Past the threshold the order lower bound clears `4/3` with room to spare. -/
theorem orderLowerBound_ge_of_ge {t : ℝ} (ht : littlewoodFreqThreshold ≤ t) :
    5 / 3 ≤ Sieve.orderLowerBound (Real.log (t / (2 * Real.pi))) := by
  have hL := littlewoodScale_ge ht
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hratio : (32 : ℝ) ≤ Real.log (t / (2 * Real.pi)) / 69122 := by
    rw [le_div_iff₀ (by norm_num)]
    linarith
  have hlog : 5 * Real.log 2 ≤ Real.log (Real.log (t / (2 * Real.pi)) / 69122) := by
    have h32 : Real.log 32 ≤ Real.log (Real.log (t / (2 * Real.pi)) / 69122) :=
      Real.log_le_log (by norm_num) hratio
    have hval : Real.log 32 = 5 * Real.log 2 := by
      rw [show (32 : ℝ) = 2 ^ (5 : ℕ) by norm_num, Real.log_pow]
      push_cast
      ring
    linarith [h32, hval.le, hval.ge]
  rw [Sieve.orderLowerBound, le_div_iff₀ (by positivity)]
  linarith

/-- **The shifted line bound at every admissible frequency past the threshold.** -/
theorem norm_riemannZeta_shifted_le_of_ge {t δ : ℝ} (ht : littlewoodFreqThreshold ≤ t)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    ‖riemannZeta (((1 + δ : ℝ) : ℂ) + Complex.I * (t : ℂ))‖
      ≤ 33 + 2 * Real.log (t / (2 * Real.pi))
          / (Sieve.orderLowerBound (Real.log (t / (2 * Real.pi))) - 4 / 3) := by
  refine Sieve.norm_riemannZeta_shifted_line_rate ?_ (orderThreshold_le_of_ge ht) ?_ hδ0 hδ1
  · exact le_trans sixteen_pi_le_littlewoodFreqThreshold ht
  · have := orderLowerBound_ge_of_ge ht
    linarith

/-- **The harmonic bound on the compact frequency range.** -/
theorem norm_riemannZeta_shifted_le_harmonic {t δ : ℝ} (ht : 1 ≤ |t|) (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1) :
    ‖riemannZeta (((1 + δ : ℝ) : ℂ) + Complex.I * (t : ℂ))‖ ≤ 4 + |t| := by
  obtain ⟨w, hwdef⟩ : ∃ w : ℂ, w = ((1 + δ : ℝ) : ℂ) + Complex.I * (t : ℂ) := ⟨_, rfl⟩
  have hwre : w.re = 1 + δ := by
    rw [hwdef]; simp
  have hwim : w.im = t := by
    rw [hwdef]; simp
  have hre : (1 : ℝ) ≤ w.re := by
    rw [hwre]; linarith
  have him : (1 : ℝ) ≤ |w.im| := by
    rw [hwim]; exact ht
  have hbase := Sieve.norm_riemannZeta_ge_one_le hre him (N := 1) le_rfl
  have hnormw : ‖w‖ ≤ 2 + |t| := by
    rw [hwdef]
    refine le_trans (norm_add_le _ _) ?_
    have h1 : ‖((1 + δ : ℝ) : ℂ)‖ ≤ 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      linarith
    have h2 : ‖Complex.I * (t : ℂ)‖ = |t| := by
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    linarith [h1, h2.le, h2.ge]
  rw [← hwdef]
  simp only [Nat.cast_one, Real.log_one, div_one] at hbase
  linarith

/-- The conjugate frequency has the same modulus. -/
theorem norm_riemannZeta_shifted_neg (δ t : ℝ) :
    ‖riemannZeta (((1 + δ : ℝ) : ℂ) + Complex.I * ((-t : ℝ) : ℂ))‖
      = ‖riemannZeta (((1 + δ : ℝ) : ℂ) + Complex.I * (t : ℂ))‖ := by
  have hconj : ((1 + δ : ℝ) : ℂ) + Complex.I * ((-t : ℝ) : ℂ)
      = (starRingEnd ℂ) (((1 + δ : ℝ) : ℂ) + Complex.I * (t : ℂ)) := by
    rw [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.conj_ofReal]
    push_cast
    ring
  rw [hconj, riemannZeta_conj, RCLike.norm_conj]

end

end RHTower
