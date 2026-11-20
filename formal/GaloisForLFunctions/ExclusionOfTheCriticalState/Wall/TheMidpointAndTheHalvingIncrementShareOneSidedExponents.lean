import GaloisForLFunctions.SquareRootThreshold.TheFiveSixthsFacesOfTheZeroAbscissa
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.ThePrimeMidpointInTwoAdjacentGcdHorizons
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.SharpPowerRecoveryFromOrdinaryPrimeMidpoints

/-!
# The prime midpoint and the halving increment share one-sided exponents

Two positive Green kernels recover the ordinary prime error `E = θ − id` from one-sided data:

* the halving kernel `E(n) = Σ_k ΔE(⌊n/2^k⌋)`, `ΔE(n) = E(n) − E(⌊n/2⌋)`, turns
  `s·ΔE(n) ≤ K n^b` into `s·E(n) ≤ K/(1 − 2^(−b)) · n^b` (`error_le_of_terminalOddHalf_le`);
* the midpoint kernel, with Mellin multiplier `1/(2·3^b − 2^b − 4^b)`, turns
  `D(n) = 2θ(3n) − θ(2n) − θ(4n) ≤ A n^b` into `E(x) ≤ A/(2·3^b − 2^b − 4^b) · x^b` plus
  a squared-logarithmic rounding term (`FactorialInterval.prime_error_from_integer_midpoint`).

Neither kernel inverts the other with a sign: the symbols `(1 − 2^(−s))/(2·3^s − 2^s − 4^s)` and
its reciprocal are signed dilation series. A one-sided bound on one observable therefore reaches the
other only through the zero abscissa. That passage loses nothing in the exponent:
for every `b ≥ ½` the upper midpoint spectrum, either sign of the halving increment and the terminal
joint height all read the same `Θ ≤ b` (`midpoint_halving_joint_spectra`).
-/

open Filter Finset

noncomputable section

namespace GaloisForLFunctions.ExclusionOfTheCriticalState

open _root_.RHTower ExceptionalLayerTheory.FactorialInterval

/-- **Halving Green kernel.** A one-sided power bound on every halving increment gives the same
one-sided bound on the prime error at every integer, with coefficient `1/(1 − 2^(−b))`. -/
theorem error_le_of_terminalOddHalf_le {s b K : ℝ} (hb : 0 < b) (hK : 0 ≤ K)
    (h : ∀ n : ℕ, 1 ≤ n → s * terminalOddHalf n ≤ K * (n:ℝ)^b) (n : ℕ) :
    s * (Chebyshev.theta n - n) ≤ K / (1 - (1/2:ℝ)^b) * (n:ℝ)^b := by
  let r := (1/2:ℝ)^b
  have rlt : r < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hb
  let D := K / (1 - r)
  have hD : 0 ≤ D := div_nonneg hK (sub_pos.mpr rlt).le
  have absorb : D * r + K = D := by
    have id : D * (1 - r) = K := div_mul_cancel₀ _ (sub_pos.mpr rlt).ne'
    linarith only [id]
  change s * (Chebyshev.theta n - n) ≤ D * (n:ℝ)^b
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [Chebyshev.theta_zero, Real.zero_rpow hb.ne']
    have prev := ih (n/2) (Nat.div_lt_self hn (by norm_num))
    have halved : (↑(n/2):ℝ) ≤ (n:ℝ) * (1/2:ℝ) := by
      have nat : (↑(n/2):ℝ) * 2 ≤ n := by exact_mod_cast Nat.div_mul_le_self n 2
      linarith only [nat]
    have power := Real.rpow_le_rpow (Nat.cast_nonneg (n/2)) halved hb.le
    rw [Real.mul_rpow (Nat.cast_nonneg n) (by norm_num : (0:ℝ) ≤ 1/2)] at power
    have increment : s * (Chebyshev.theta n - n) =
        s * (Chebyshev.theta (n/2:ℕ) - (↑(n/2):ℝ)) + s * terminalOddHalf n := by
      rw [terminal_odd_half_eq]; ring
    rw [increment]
    have step := add_le_add prev (h n hn)
    change (↑(n/2):ℝ)^b ≤ (n:ℝ)^b * r at power
    have hDr := mul_le_mul_of_nonneg_left power hD
    calc _ ≤ D * (↑(n/2):ℝ)^b + K * (n:ℝ)^b := step
      _ ≤ (D * r + K) * (n:ℝ)^b := by linarith only [hDr]
      _ = D * (n:ℝ)^b := by rw [absorb]

/-- The halving kernel at every real `x ≥ 0`: integer rounding costs at most one. -/
theorem error_le_of_terminalOddHalf_le_real {s b K : ℝ} (hs : s = 1 ∨ s = -1) (hb : 0 < b)
    (hK : 0 ≤ K) (h : ∀ n : ℕ, 1 ≤ n → s * terminalOddHalf n ≤ K * (n:ℝ)^b) {x : ℝ} (hx : 0 ≤ x) :
    s * (Chebyshev.theta x - x) ≤ K / (1 - (1/2:ℝ)^b) * x^b + 1 := by
  have hint := error_le_of_terminalOddHalf_le hb hK h ⌊x⌋₊
  have hfl := Nat.floor_le hx
  have hgap : |(⌊x⌋₊:ℝ) - x| ≤ 1 :=
    abs_le.mpr ⟨by linarith only [Nat.lt_floor_add_one x], by linarith only [hfl]⟩
  have hround : s * ((⌊x⌋₊:ℝ) - x) ≤ 1 := by
    rcases hs with rfl | rfl
    · linarith only [(abs_le.mp hgap).2]
    · linarith only [(abs_le.mp hgap).1]
  have hr : 0 < 1 - (1/2:ℝ)^b := sub_pos.mpr (Real.rpow_lt_one (by norm_num) (by norm_num) hb)
  have hmono := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hfl hb.le)
    (div_nonneg hK hr.le)
  rw [Chebyshev.theta_eq_theta_coe_floor x]
  linarith only [hint, hround, hmono]

/-- **One exponent for three observables.** For `b ≥ ½`, the upper spectrum of the prime midpoint
`D`, the spectrum of one fixed sign of the halving increment and the spectrum of the terminal joint
height all equal `Θ ≤ b`. A one-sided producer for any of them serves the other two at the same
exponent. -/
theorem midpoint_halving_joint_spectra {b s : ℝ} (hb : 1/2 ≤ b) (hs : s = 1 ∨ s = -1) :
    ((∀ t : ℝ, b < t → t < 1 → ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → primeMidpointPrice n ≤ C * (n:ℝ)^t) ↔
      zetaZeroAbscissa ≤ b) ∧
    (zetaZeroAbscissa ≤ b ↔ ∀ t : ℝ, b < t → ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ H : ℕ in atTop, s * terminalOddHalf H ≤ C * (H:ℝ)^t) ∧
    (zetaZeroAbscissa ≤ b ↔ ∀ e : ℝ, 2*b - 1 < e → ∃ K : ℝ, 0 ≤ K ∧
      ∀ᶠ H : ℕ in atTop, terminalJointHeight s H ≤ K * (H:ℝ)^e) :=
  ⟨prime_midpoint_upper_spectrum_iff hb,
    SquareRootThreshold.zetaZeroAbscissa_le_iff_terminalOddHalf_le hb hs,
    SquareRootThreshold.zetaZeroAbscissa_le_iff_terminalJointHeight_le hb hs⟩

/-- **Midpoint to halving increment.** An upper midpoint spectrum above `b` gives both signs of the
halving increment below `H^t` for every `t > b`. -/
theorem abs_terminalOddHalf_le_of_midpoint_upper {b : ℝ} (hb : 1/2 ≤ b)
    (h : ∀ t : ℝ, b < t → t < 1 → ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → primeMidpointPrice n ≤ C * (n:ℝ)^t)
    {t : ℝ} (ht : b < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ H : ℕ in atTop, |terminalOddHalf H| ≤ C * (H:ℝ)^t := by
  have hΘ := (prime_midpoint_upper_spectrum_iff hb).mp h
  exact terminal_odd_half_above_abscissa
    (((SquareRootThreshold.zeroReSup_le_iff_zetaZeroAbscissa_le hb).mpr hΘ).trans_lt ht)

/-- **Halving increment to midpoint.** One sign of the halving increment below `K n^b` at every
`n ≥ 1` gives the upper midpoint spectrum above `b`. -/
theorem midpoint_upper_of_terminalOddHalf_le {b s K : ℝ} (hb : 1/2 ≤ b) (hs : s = 1 ∨ s = -1)
    (hK : 0 ≤ K) (h : ∀ n : ℕ, 1 ≤ n → s * terminalOddHalf n ≤ K * (n:ℝ)^b) :
    ∀ t : ℝ, b < t → t < 1 → ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → primeMidpointPrice n ≤ C * (n:ℝ)^t := by
  refine (prime_midpoint_upper_spectrum_iff hb).mpr
    ((SquareRootThreshold.zetaZeroAbscissa_le_iff_terminalOddHalf_le hb hs).mpr fun t ht => ?_)
  refine ⟨K, hK, Eventually.of_forall fun H => ?_⟩
  rcases Nat.eq_zero_or_pos H with rfl | hH
  · have h0 : terminalOddHalf 0 = 0 := by simp [terminalOddHalf, oddQuotientPrimeExcess]
    simp [h0, Real.zero_rpow (by linarith : t ≠ 0)]
  · exact (h H hH).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr hH) ht.le) hK)

#print axioms error_le_of_terminalOddHalf_le
#print axioms error_le_of_terminalOddHalf_le_real
#print axioms midpoint_halving_joint_spectra
#print axioms abs_terminalOddHalf_le_of_midpoint_upper
#print axioms midpoint_upper_of_terminalOddHalf_le

end GaloisForLFunctions.ExclusionOfTheCriticalState
