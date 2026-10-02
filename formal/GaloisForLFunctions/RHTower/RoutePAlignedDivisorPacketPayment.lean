import GaloisForLFunctions.RHTower.RoutePCompleteLogarithmicRampRows

/-!
# Exact payment inside an aligned complete divisor packet

At a time divisible by `L`, summing the complete logarithmic rows over all
divisors of `L` applies the zeta convolution to the literal Möbius-log weight.
It collapses to the endpoint weight and von Mangoldt coefficients. At `L^2`
the result is nonpositive, and every original hyperbola label is active.

This pays the positive individual rows inside this packet. Divisor completion
and time alignment are essential here: no bound on a moving clipped packet,
arbitrary residue phase, half-order time integral, or Route-P debt is asserted.
-/

noncomputable section
open Finset ArithmeticFunction HTGeometry
open scoped BigOperators
namespace RHTower

private def logRampCoefficient (c : ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => ((moebius n : ℤ) : ℝ) * (c - Real.log n), by simp⟩

private def birthRampCoefficient : ArithmeticFunction ℝ :=
  ⟨fun n => centeredModularRamp n 0, by simp [centeredModularRamp]⟩

private theorem logRampCoefficient_collapse (c : ℝ) :
    (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * logRampCoefficient c =
      c • (1 : ArithmeticFunction ℝ) + vonMangoldt := by
  ext n
  have hsum : (∑ d ∈ n.divisors, ((moebius d : ℤ) : ℝ)) =
      (1 : ArithmeticFunction ℝ) n := by
    have h := congrArg (fun f : ArithmeticFunction ℝ => f n)
      (coe_zeta_mul_coe_moebius (R := ℝ))
    simpa only [coe_zeta_mul_apply, intCoe_apply] using h
  rw [coe_zeta_mul_apply]
  change (∑ d ∈ n.divisors, ((moebius d : ℤ) : ℝ) * (c - Real.log d)) =
    c * (1 : ArithmeticFunction ℝ) n + vonMangoldt n
  simp_rw [mul_sub]
  have hlog : (∑ d ∈ n.divisors, ((moebius d : ℤ) : ℝ) * Real.log d) =
      -vonMangoldt n := sum_moebius_mul_log_eq
  rw [sum_sub_distrib, ← sum_mul, hsum, hlog]
  ring

private theorem ramp_at_quotient_multiple {m N d : ℕ}
    (hd : d ∈ m.divisors) (hmN : m ∣ N) :
    centeredModularRamp (m / d) (N / d) = centeredModularRamp (m / d) 0 := by
  have hd0 := Nat.pos_of_mem_divisors hd
  obtain ⟨j, hj⟩ := Nat.dvd_of_mem_divisors hd
  obtain ⟨t, ht⟩ := hmN
  rw [ht, hj, Nat.mul_assoc, Nat.mul_div_cancel_left _ hd0,
    Nat.mul_div_cancel_left _ hd0]
  simp [centeredModularRamp]

private theorem complete_row_aligned {m N : ℕ} (hmN : m ∣ N) :
    routePCompleteLogarithmicRampRow m N =
      (logRampCoefficient (Real.log N) * birthRampCoefficient) m := by
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun a b =>
      logRampCoefficient (Real.log N) a * birthRampCoefficient b)]
  unfold routePCompleteLogarithmicRampRow
  apply Finset.sum_congr rfl
  intro d hd
  change _ = ((moebius d : ℤ) : ℝ) * (Real.log N - Real.log d) *
    centeredModularRamp (m / d) 0
  rw [ramp_at_quotient_multiple hd hmN]

/-- Summing a complete divisor packet cancels the Möbius logarithmic coefficient
exactly, leaving only the original endpoint and von Mangoldt weights. -/
theorem routeP_complete_logarithmic_packet_aligned {L N : ℕ} (hLN : L ∣ N) :
    (∑ m ∈ L.divisors, routePCompleteLogarithmicRampRow m N) =
      Real.log N * centeredModularRamp L 0 +
        ∑ d ∈ L.divisors, vonMangoldt d * centeredModularRamp (L / d) 0 := by
  have hrows : (∑ m ∈ L.divisors, routePCompleteLogarithmicRampRow m N) =
      ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
        (logRampCoefficient (Real.log N) * birthRampCoefficient)) L := by
    rw [coe_zeta_mul_apply]
    exact sum_congr rfl (fun m hm => complete_row_aligned
      ((Nat.dvd_of_mem_divisors hm).trans hLN))
  rw [hrows, ← mul_assoc, logRampCoefficient_collapse, add_mul, smul_mul_assoc,
    one_mul, ArithmeticFunction.add_apply]
  change Real.log N * centeredModularRamp L 0 +
      (vonMangoldt * birthRampCoefficient) L = _
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun a b => vonMangoldt a * birthRampCoefficient b)]
  rfl

private theorem birthRamp_nonpositive (n : ℕ) : centeredModularRamp n 0 ≤ 0 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [centeredModularRamp]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
  simp only [centeredModularRamp, Nat.zero_mod, Nat.cast_zero, zero_div, zero_sub]
  exact neg_nonpos.mpr (div_nonneg (sub_nonneg.mpr hn1) (by positivity))

/-- Positive individual rows are paid after completing the full divisor packet
at the common square birth. No signed row or logarithmic coefficient is dropped. -/
theorem routeP_complete_logarithmic_packet_square_nonpositive (L : ℕ) :
    (∑ m ∈ L.divisors, routePCompleteLogarithmicRampRow m (L * L)) ≤ 0 := by
  rw [routeP_complete_logarithmic_packet_aligned (dvd_mul_right L L)]
  have hlog : 0 ≤ Real.log (L * L : ℕ) := by
    rcases eq_or_ne L 0 with rfl | hL
    · simp
    apply Real.log_nonneg
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (mul_ne_zero hL hL)
  apply add_nonpos (mul_nonpos_of_nonneg_of_nonpos hlog (birthRamp_nonpositive L))
  apply sum_nonpos
  intro d _
  exact mul_nonpos_of_nonneg_of_nonpos (vonMangoldt_nonneg) (birthRamp_nonpositive _)

/-- All rows in the square packet retain their original active hyperbola labels. -/
theorem routeP_complete_logarithmic_packet_square_active (L : ℕ) :
    ∀ m ∈ L.divisors, ∀ d ∈ m.divisors, (m / d) * (m / d) ≤ L * L / d := by
  intro m hm d hd
  have hmL : m ≤ L := Nat.le_of_dvd
    (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hm).2) (Nat.dvd_of_mem_divisors hm)
  exact (routeP_complete_logarithmic_ramp_birth_active m d hd).trans
    (Nat.div_le_div_right (Nat.mul_le_mul hmL hmL))

end RHTower
