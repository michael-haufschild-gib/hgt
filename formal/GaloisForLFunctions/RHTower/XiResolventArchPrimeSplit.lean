import GaloisForLFunctions.RHTower.VonMangoldtLogMomentHankel
import GaloisForLFunctions.RHTower.XiResolventLowRungVacuity

/-!
# The archimedean--prime split of the resolvent ladder's first entry

The resolvent ladder's entries are `R n X = sum_q (w q + X)^(-(n+1))`, and `R 0 (x^(2 : ℕ))` is the
Euler-ray response `logDeriv xi (1/2 + x) / x`.  On the convergence half-plane the completed
logarithmic derivative splits into an archimedean part and the von Mangoldt series, so

`R 0 (x^(2 : ℕ)) = (arch part) / x - (vonMangoldtWeightLogMoment 0 (1/2 + x)) / x`.

The subtracted term is the order-zero entry of the arithmetic moment array, which
`VonMangoldtLogMomentHankel` proves positive semidefinite.  So the prime contribution to the ladder
enters with a **minus** sign and is itself a positive semidefinite array; RH is the assertion that
the archimedean array dominates it.  This file records the split exactly at order zero.
-/

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

/-- On a real point of the convergence half-plane the von Mangoldt series is the real
order-zero logarithmic moment. -/
theorem lseries_vonMangoldt_ofReal {σ : ℝ} (hσ : 1 < σ) :
    LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ) =
      ((vonMangoldtWeightLogMoment 0 σ : ℝ) : ℂ) := by
  have hre : ((σ : ℂ)).re = σ := Complex.ofReal_re σ
  have hc := ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (σ : ℂ))
    (by rw [hre]; exact hσ)
  have hterm : ∀ n : ℕ,
      LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) (σ : ℂ) n =
        (((ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ) : ℝ) : ℂ) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [LSeries.term_of_ne_zero hn.ne']
      have hn0 : ((n : ℂ)) ≠ 0 := by
        simpa using (Nat.cast_ne_zero (R := ℂ)).mpr hn.ne'
      rw [div_eq_mul_inv, ← Complex.cpow_neg]
      have hcpow : ((n : ℂ)) ^ (-(σ : ℂ)) = (((n : ℝ) ^ (-σ) : ℝ) : ℂ) := by
        rw [← Complex.ofReal_natCast, ← Complex.ofReal_neg,
          ← Complex.ofReal_cpow (Nat.cast_nonneg n)]
      rw [hcpow, ← Complex.ofReal_mul]
  rw [LSeries, tsum_congr hterm, vonMangoldtWeightLogMoment,
    GaloisForLFunctions.HTGeometry.weightMoment]
  have hsum : Summable (fun n : ℕ =>
      (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ)) :=
    summable_vonMangoldt_rpow hσ
  rw [← Complex.ofReal_tsum]
  congr 1
  exact tsum_congr fun n => by rw [pow_zero, mul_one]

/-- **The order-zero entry of the resolvent ladder, split into archimedean and prime parts.**
The prime part is the order-zero entry of the von Mangoldt moment array and enters negatively. -/
theorem xiResolventMoment_zero_eq_arch_sub_prime {x : ℝ} (hx : 1 / 2 < x) :
    xiResolventMoment 0 (x ^ 2) =
      (((1 / 2 : ℂ) + (x : ℂ))⁻¹ + ((1 / 2 : ℂ) + (x : ℂ) - 1)⁻¹ +
          logDeriv Complex.Gammaℝ ((1 / 2 : ℂ) + (x : ℂ))) / (x : ℂ) -
        ((vonMangoldtWeightLogMoment 0 (1 / 2 + x) : ℝ) : ℂ) / (x : ℂ) := by
  have hxpos : 0 < x := lt_trans (by norm_num) hx
  have hre : ((1 / 2 : ℂ) + (x : ℂ)).re = 1 / 2 + x := by
    simp [Complex.add_re]
  have harith := logDeriv_xi_eq_arithmetic (s := (1 / 2 : ℂ) + (x : ℂ))
    (by rw [hre]; linarith)
  have hcast : ((1 / 2 : ℂ) + (x : ℂ)) = (((1 / 2 + x : ℝ)) : ℂ) := by
    push_cast
    ring
  have hprime : LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
      ((1 / 2 : ℂ) + (x : ℂ)) = ((vonMangoldtWeightLogMoment 0 (1 / 2 + x) : ℝ) : ℂ) := by
    rw [hcast]
    exact lseries_vonMangoldt_ofReal (by linarith)
  rw [xiResolventMoment_zero_eq_logDeriv hxpos, harith, hprime, sub_div]


/-- The order-zero logarithmic moment of the von Mangoldt weight is nonnegative. -/
theorem vonMangoldtWeightLogMoment_zero_nonneg (σ : ℝ) :
    0 ≤ vonMangoldtWeightLogMoment 0 σ := by
  rw [vonMangoldtWeightLogMoment, GaloisForLFunctions.HTGeometry.weightMoment]
  refine tsum_nonneg fun n => ?_
  have h1 : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) :=
    ArithmeticFunction.vonMangoldt_nonneg
  have h2 : 0 ≤ ((n : ℝ) ^ (-σ)) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  positivity

/-- **The archimedean side dominates at order zero, unconditionally.**  The Euler-ray response of
the Xi divisor never exceeds the purely archimedean quantity built from the two poles and the
archimedean factor, because the prime contribution is a nonnegative weight entering negatively.
This is the first instance of the domination question settled without any hypothesis. -/
theorem re_xiResolventMoment_zero_le_arch {x : ℝ} (hx : 1 / 2 < x) :
    (xiResolventMoment 0 (x ^ 2)).re ≤
      ((((1 / 2 : ℂ) + (x : ℂ))⁻¹ + ((1 / 2 : ℂ) + (x : ℂ) - 1)⁻¹ +
        logDeriv Complex.Gammaℝ ((1 / 2 : ℂ) + (x : ℂ))) / (x : ℂ)).re := by
  have hxpos : 0 < x := lt_trans (by norm_num) hx
  have hsplit := xiResolventMoment_zero_eq_arch_sub_prime hx
  have hprime : (((vonMangoldtWeightLogMoment 0 (1 / 2 + x) : ℝ) : ℂ) / (x : ℂ)).re =
      vonMangoldtWeightLogMoment 0 (1 / 2 + x) / x := by
    rw [← Complex.ofReal_div, Complex.ofReal_re]
  have hnn : 0 ≤ vonMangoldtWeightLogMoment 0 (1 / 2 + x) / x :=
    div_nonneg (vonMangoldtWeightLogMoment_zero_nonneg (1 / 2 + x)) hxpos.le
  rw [hsplit, Complex.sub_re, hprime]
  linarith


/-- The order-zero logarithmic moment is at least its prime-two atom. -/
theorem log_two_rpow_le_vonMangoldtLogMoment_zero {σ : ℝ} (hσ : 1 < σ) :
    Real.log 2 * (2 : ℝ) ^ (-σ) ≤ vonMangoldtWeightLogMoment 0 σ := by
  have hsum : Summable (fun n : ℕ =>
      (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ) * Real.log n ^ 0) := by
    simpa using summable_vonMangoldt_logPow hσ 0
  have hnn : ∀ j : ℕ, j ≠ 2 →
      0 ≤ (ArithmeticFunction.vonMangoldt j : ℝ) * (j : ℝ) ^ (-σ) * Real.log j ^ 0 := by
    intro j _
    have h1 : 0 ≤ (ArithmeticFunction.vonMangoldt j : ℝ) :=
      ArithmeticFunction.vonMangoldt_nonneg
    have h2 : 0 ≤ ((j : ℝ) ^ (-σ)) := Real.rpow_nonneg (Nat.cast_nonneg j) _
    positivity
  have hle := hsum.le_tsum 2 hnn
  rw [vonMangoldtWeightLogMoment, GaloisForLFunctions.HTGeometry.weightMoment]
  refine le_trans (le_of_eq ?_) hle
  rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  norm_num

/-- **Strict quantitative domination at order zero.**  The archimedean quantity exceeds the
Euler-ray response of the Xi divisor by at least the contribution of the single prime `2`. -/
theorem re_xiResolventMoment_zero_add_primeTwo_le_arch {x : ℝ} (hx : 1 / 2 < x) :
    (xiResolventMoment 0 (x ^ 2)).re +
        Real.log 2 * (2 : ℝ) ^ (-(1 / 2 + x)) / x ≤
      ((((1 / 2 : ℂ) + (x : ℂ))⁻¹ + ((1 / 2 : ℂ) + (x : ℂ) - 1)⁻¹ +
        logDeriv Complex.Gammaℝ ((1 / 2 : ℂ) + (x : ℂ))) / (x : ℂ)).re := by
  have hxpos : 0 < x := lt_trans (by norm_num) hx
  have hsplit := xiResolventMoment_zero_eq_arch_sub_prime hx
  have hprime : (((vonMangoldtWeightLogMoment 0 (1 / 2 + x) : ℝ) : ℂ) / (x : ℂ)).re =
      vonMangoldtWeightLogMoment 0 (1 / 2 + x) / x := by
    rw [← Complex.ofReal_div, Complex.ofReal_re]
  have hatom : Real.log 2 * (2 : ℝ) ^ (-(1 / 2 + x)) / x ≤
      vonMangoldtWeightLogMoment 0 (1 / 2 + x) / x :=
    div_le_div_of_nonneg_right
      (log_two_rpow_le_vonMangoldtLogMoment_zero (by linarith)) hxpos.le
  rw [hsplit, Complex.sub_re, hprime]
  linarith

end

end RHTower
