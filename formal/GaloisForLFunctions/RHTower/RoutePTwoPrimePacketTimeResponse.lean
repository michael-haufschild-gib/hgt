import GaloisForLFunctions.RHTower.RoutePAlignedDivisorPacketPayment
import GaloisForLFunctions.RHTower.RoutePPeriodicLogWeightedAbel
import GaloisForLFunctions.HTGeometry.SecondCenteredModularAbel
import Mathlib.Data.Finset.NatDivisors

/-!
# Positive full-period responses of actual complete divisor packets

The quotient-ramp identity retains its smaller-period correction. It gives
an exact all-phase formula for the complete packet on two distinct primes:
the original time logarithm multiplies one periodic channel, and the fixed
logarithmic offset multiplies another. Both have zero period mean.

The first channel has a strictly positive primitive mean for primes at least
three. The full logarithmic half-order limit preserves this coefficient.
Consequently sufficiently late aligned full periods are strictly positive,
with every original quotient label already active. Thus the aligned birth
sign cannot be extended to a nonpositive full-period payment law.

This concerns actual divisor packets, not the complete growing native head.
It supplies no counterexample to the Route-P linear floor or to RH.
-/

noncomputable section
open Finset ArithmeticFunction HTGeometry Filter Topology
open scoped BigOperators
namespace RHTower

/-- Quotient lifting retains the smaller-period correction exactly. -/
theorem routeP_centeredModularRamp_quotient {d j : ℕ} (hd : 0 < d) (hj : 0 < j)
    (k : ℕ) :
    centeredModularRamp j (k / d) =
      centeredModularRamp (d * j) k - centeredModularRamp d k / j := by
  unfold centeredModularRamp
  rw [Nat.mod_mul]
  push_cast
  field_simp
  ring

private theorem sum_divisors_two_primes (F : ℕ → ℝ) {p q : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q) :
    (∑ d ∈ (p * q).divisors, F d) = F 1 + F p + F q + F (p * q) := by
  classical
  have hc : p.Coprime q := hp.coprime_iff_not_dvd.mpr
    (fun h => hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp h))
  rw [hc.divisors_mul]
  simp only [sum_map, Function.Embedding.coeFn_mk]
  trans ∑ x ∈ p.divisors ×ˢ q.divisors, F (x.1 * x.2)
  · exact Finset.sum_attach (p.divisors ×ˢ q.divisors) (fun x : ℕ × ℕ => F (x.1 * x.2))
  rw [sum_product, hp.divisors, hq.divisors]
  simp only [sum_pair hp.ne_one.symm, sum_pair hq.ne_one.symm, one_mul, mul_one]
  ring

private theorem complete_row_prime (p k : ℕ) (hp : Nat.Prime p) :
    routePCompleteLogarithmicRampRow p k = Real.log k * centeredModularRamp p k := by
  unfold routePCompleteLogarithmicRampRow
  rw [hp.divisors, sum_pair hp.ne_one.symm]
  simp [centeredModularRamp, Nat.mod_one, Nat.div_self hp.pos, moebius_apply_prime hp]

/-- The coefficient of the actual time logarithm in a complete two-prime packet. -/
def routePTwoPrimePacketSlope (p q k : ℕ) : ℝ :=
  (1 + 1 / (q : ℝ)) * centeredModularRamp p k +
    (1 + 1 / (p : ℝ)) * centeredModularRamp q k - centeredModularRamp (p * q) k

/-- The fixed logarithmic coefficient retained beside the time logarithm. -/
def routePTwoPrimePacketLogOffset (p q k : ℕ) : ℝ :=
  (Real.log p / q) * centeredModularRamp p k +
    (Real.log q / p) * centeredModularRamp q k -
      (Real.log p + Real.log q) * centeredModularRamp (p * q) k

/-- Complete packet identity at every residue phase, with the original forcing coefficients. -/
theorem routeP_two_prime_packet_at_any_time {p q : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q) (k : ℕ) :
    (∑ m ∈ (p * q).divisors, routePCompleteLogarithmicRampRow m k) =
      Real.log k * routePTwoPrimePacketSlope p q k - routePTwoPrimePacketLogOffset p q k := by
  have hc : p.Coprime q := hp.coprime_iff_not_dvd.mpr
    (fun h => hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp h))
  have hmu : ((moebius (p * q) : ℤ) : ℝ) = 1 := by
    rw [isMultiplicative_moebius.map_mul_of_coprime hc,
      moebius_apply_prime hp, moebius_apply_prime hq]
    norm_num
  rw [sum_divisors_two_primes _ hp hq hpq, complete_row_prime p k hp,
    complete_row_prime q k hq]
  have hone : routePCompleteLogarithmicRampRow 1 k = 0 := by
    simp [routePCompleteLogarithmicRampRow, centeredModularRamp, Nat.mod_one]
  rw [hone, zero_add]
  unfold routePCompleteLogarithmicRampRow
  rw [sum_divisors_two_primes _ hp hq hpq]
  simp only [moebius_apply_one, Int.cast_one, one_mul,
    Nat.div_one, moebius_apply_prime hp, moebius_apply_prime hq, Int.cast_neg,
    Nat.mul_div_cancel_left _ hp.pos, Nat.mul_div_cancel _ hq.pos,
    Nat.div_self (Nat.mul_pos hp.pos hq.pos), hmu]
  have h1 : centeredModularRamp 1 (k / (p * q)) = 0 := by simp [centeredModularRamp, Nat.mod_one]
  rw [h1, mul_zero, add_zero, routeP_centeredModularRamp_quotient hp.pos hq.pos,
    routeP_centeredModularRamp_quotient hq.pos hp.pos, Nat.mul_comm q p]
  unfold routePTwoPrimePacketSlope routePTwoPrimePacketLogOffset
  simp only [Nat.cast_one, Real.log_one, sub_zero]
  ring

/-- Periodic primitive of the time-logarithm coefficient. -/
def routePTwoPrimePacketPrimitive (p q k : ℕ) : ℝ :=
  (1 + 1 / (q : ℝ)) * centeredModularPrimitive p k +
    (1 + 1 / (p : ℝ)) * centeredModularPrimitive q k - centeredModularPrimitive (p * q) k

/-- Exact prefix of the full time-logarithm coefficient. -/
theorem routeP_two_prime_packet_primitive (p q N : ℕ) :
    (∑ k ∈ range N, routePTwoPrimePacketSlope p q k) = routePTwoPrimePacketPrimitive p q N := by
  unfold routePTwoPrimePacketSlope routePTwoPrimePacketPrimitive
  rw [sum_sub_distrib, sum_add_distrib, ← mul_sum, ← mul_sum]
  simp only [sum_centeredModularRamp]

private theorem modular_primitive_period_sum {d N : ℕ} (hd : 0 < d) (hdN : d ∣ N) :
    (∑ k ∈ range N, centeredModularPrimitive d (k + 1)) =
      -(N : ℝ) * centeredModularMeanMagnitude d := by
  have hpoint (k : ℕ) := centeredModularSecondPrimitive_succ hd k
  have hsum := congrArg (fun f : ℕ → ℝ => ∑ k ∈ range N, f k)
    (funext hpoint)
  simp only [sum_sub_distrib, sum_add_distrib, sum_const, card_range, nsmul_eq_mul] at hsum
  have htel := sum_range_sub (fun k => centeredModularSecondPrimitive d k) N
  have hzero : centeredModularSecondPrimitive d N = 0 := by
    simp [centeredModularSecondPrimitive, Nat.mod_eq_zero_of_dvd hdN]
  rw [hzero, centeredModularSecondPrimitive_zero, sub_zero] at htel
  have hz : (∑ k ∈ range N, centeredModularSecondPrimitive d (k + 1)) -
      (∑ k ∈ range N, centeredModularSecondPrimitive d k) = 0 := by
    simpa only [sum_sub_distrib] using htel
  rw [hz] at hsum
  linarith

/-- Exact primitive mean: the signed Euler factor survives complete time summation. -/
theorem routeP_two_prime_packet_primitive_mean {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    (∑ k ∈ range (p * q), routePTwoPrimePacketPrimitive p q (k + 1)) =
      (p * q : ℕ) *
        (((1 - (p : ℝ) + 1 / p) * (1 - (q : ℝ) + 1 / q) - 1) / 12) := by
  unfold routePTwoPrimePacketPrimitive
  rw [sum_sub_distrib, sum_add_distrib, ← mul_sum, ← mul_sum,
    modular_primitive_period_sum hp (dvd_mul_right p q),
    modular_primitive_period_sum hq (dvd_mul_left q p),
    modular_primitive_period_sum (Nat.mul_pos hp hq) (dvd_refl _)]
  unfold centeredModularMeanMagnitude
  push_cast
  field_simp
  ring

/-- Above the small-prime edge, a complete two-prime packet has strictly positive mean primitive. -/
theorem routeP_two_prime_packet_primitive_mean_positive {p q : ℕ}
    (hp : 3 ≤ p) (hq : 3 ≤ q) :
    0 < ∑ k ∈ range (p * q), routePTwoPrimePacketPrimitive p q (k + 1) := by
  rw [routeP_two_prime_packet_primitive_mean (by omega) (by omega)]
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hp0 : (0 : ℝ) < p := by linarith
  have hq0 : (0 : ℝ) < q := by linarith
  have hpInv : 1 / (p : ℝ) < 1 := (div_lt_one hp0).2 (by linarith)
  have hqInv : 1 / (q : ℝ) < 1 := (div_lt_one hq0).2 (by linarith)
  have hpa : 1 - (p : ℝ) + 1 / p < -1 := by linarith
  have hqa : 1 - (q : ℝ) + 1 / q < -1 := by linarith
  have hprod : 1 < (1 - (p : ℝ) + 1 / p) * (1 - (q : ℝ) + 1 / q) := by
    nlinarith [mul_pos (by linarith : 0 < -(1 - (p : ℝ) + 1 / p) - 1)
      (by linarith : 0 < -(1 - (q : ℝ) + 1 / q) - 1)]
  exact mul_pos (by positivity) (div_pos (sub_pos.mpr hprod) (by positivity))

/-- The literal complete divisor packet integrated over one half-order time period. -/
def routePCompletePacketHalfOrderWindow (L B : ℕ) : ℝ :=
  ∑ k ∈ range L, halfOrderAbelStep B k *
    (∑ m ∈ L.divisors, routePCompleteLogarithmicRampRow m (B + k))

private theorem modular_ramp_add_multiple {d B : ℕ} (hdB : d ∣ B) (k : ℕ) :
    centeredModularRamp d (B + k) = centeredModularRamp d k := by
  unfold centeredModularRamp
  rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hdB, zero_add, Nat.mod_mod]

private theorem packet_window_eq {p q B : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q) (hB : p * q ∣ B) :
    routePCompletePacketHalfOrderWindow (p * q) B =
      ∑ k ∈ range (p * q),
        (Real.log (B + k : ℕ) * routePTwoPrimePacketSlope p q k -
          routePTwoPrimePacketLogOffset p q k) * halfOrderAbelStep B k := by
  have hpB := (dvd_mul_right p q).trans hB
  have hqB := (dvd_mul_left q p).trans hB
  unfold routePCompletePacketHalfOrderWindow
  apply sum_congr rfl
  intro k _
  rw [routeP_two_prime_packet_at_any_time hp hq hpq]
  simp only [routePTwoPrimePacketSlope, routePTwoPrimePacketLogOffset,
    modular_ramp_add_multiple hpB, modular_ramp_add_multiple hqB, modular_ramp_add_multiple hB]
  ring

private theorem two_prime_offset_period_zero (p q : ℕ) :
    (∑ k ∈ range (p * q), routePTwoPrimePacketLogOffset p q k) = 0 := by
  unfold routePTwoPrimePacketLogOffset
  rw [sum_sub_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, ← mul_sum]
  simp only [sum_centeredModularRamp, centeredModularPrimitive,
    Nat.mod_eq_zero_of_dvd (dvd_mul_right p q),
    Nat.mod_eq_zero_of_dvd (dvd_mul_left q p), Nat.mod_self,
    Nat.cast_zero, zero_mul, zero_div, mul_zero, add_zero, sub_zero]

/-- Full logarithmic time response has the exact positive primitive mean as leading coefficient. -/
theorem routeP_two_prime_log_time_response_limit (p q : ℕ) :
    Tendsto (fun B : ℕ =>
      (∑ k ∈ range (p * q),
        (Real.log (B + k : ℕ) * routePTwoPrimePacketSlope p q k -
          routePTwoPrimePacketLogOffset p q k) * halfOrderAbelStep B k) /
        (Real.log B * (halfOrderAbelStep B 0 - halfOrderAbelStep B 1))) atTop
      (𝓝 (∑ k ∈ range (p * q), routePTwoPrimePacketPrimitive p q (k + 1))) := by
  let Q : ℕ → ℝ := fun N => ∑ k ∈ range N, routePTwoPrimePacketLogOffset p q k
  apply routeP_finite_log_halfOrder_response_limit
    (routePTwoPrimePacketSlope p q) (routePTwoPrimePacketLogOffset p q)
    (routePTwoPrimePacketPrimitive p q) Q (p * q)
  · simp [routePTwoPrimePacketPrimitive, centeredModularPrimitive]
  · intro k
    rw [← routeP_two_prime_packet_primitive p q (k + 1),
      ← routeP_two_prime_packet_primitive p q k, sum_range_succ]
    ring
  · simp [routePTwoPrimePacketPrimitive, centeredModularPrimitive,
      Nat.mod_eq_zero_of_dvd (dvd_mul_right p q), Nat.mod_eq_zero_of_dvd (dvd_mul_left q p)]
  · simp [Q]
  · intro k
    simp [Q, sum_range_succ]
  · exact two_prime_offset_period_zero p q

/-- Every sufficiently late aligned full period of this actual two-prime packet has
strictly positive half-order response, with every original quotient label already active. -/
theorem routeP_two_prime_packet_eventually_positive_period
    {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q)
    (hp3 : 3 ≤ p) (hq3 : 3 ≤ q) :
    ∀ᶠ B : ℕ in atTop, p * q ∣ B →
      (p * q) * (p * q) ≤ B ∧ 0 < routePCompletePacketHalfOrderWindow (p * q) B := by
  have hlim := routeP_two_prime_log_time_response_limit p q
  have hmean := routeP_two_prime_packet_primitive_mean_positive hp3 hq3
  have hpos := hlim.eventually (Ioi_mem_nhds hmean)
  filter_upwards [hpos, eventually_ge_atTop (2 : ℕ),
    eventually_ge_atTop ((p * q) * (p * q))] with B hBpos hB2 hBB
  intro hdiv
  refine ⟨hBB, ?_⟩
  have hlog : 0 < Real.log (B : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < B by omega))
  have hgap : 0 < halfOrderAbelStep B 0 - halfOrderAbelStep B 1 := by
    rw [show halfOrderAbelStep B 1 = halfOrderAbelStep B (0 + 1) by rfl,
      halfOrderAbelStep_gap_eq]
    positivity
  rw [packet_window_eq hp hq hpq hdiv]
  exact (div_pos_iff_of_pos_right (mul_pos hlog hgap)).mp hBpos

/-- Unconditional cofinally late positive full-period packet responses on actual prime labels. -/
theorem routeP_positive_full_period_packets_cofinal (N : ℕ) :
    ∃ p q B : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p < q ∧ N < B ∧
      (p * q) * (p * q) ≤ B ∧ p * q ∣ B ∧
        0 < routePCompletePacketHalfOrderWindow (p * q) B := by
  obtain ⟨p, hp3, hp⟩ := Nat.exists_infinite_primes 3
  obtain ⟨q, hqp, hq⟩ := Nat.exists_infinite_primes (p + 1)
  have hpq : p < q := by omega
  have hq3 : 3 ≤ q := by omega
  obtain ⟨M, hM⟩ := eventually_atTop.mp
    (routeP_two_prime_packet_eventually_positive_period hp hq hpq.ne hp3 hq3)
  let B := (p * q) * (M + N + 1)
  have hL1 : 1 ≤ p * q := Nat.one_le_iff_ne_zero.mpr (mul_ne_zero hp.ne_zero hq.ne_zero)
  have hlarge : M + N + 1 ≤ B := by
    dsimp [B]
    nlinarith
  have hdiv : p * q ∣ B := dvd_mul_right _ _
  obtain ⟨hborn, hpos⟩ := hM B (by omega) hdiv
  exact ⟨p, q, B, hp, hq, hpq, by omega, hborn, hdiv, hpos⟩

/-- The complete-period nonpositive payment conjecture fails even on fully active packets. -/
theorem not_routeP_full_period_packets_eventually_nonpositive :
    ¬ ∃ N : ℕ, ∀ L B : ℕ, N ≤ B → L * L ≤ B → L ∣ B →
      routePCompletePacketHalfOrderWindow L B ≤ 0 := by
  rintro ⟨N, h⟩
  obtain ⟨p, q, B, _, _, _, hNB, hborn, hdiv, hpos⟩ :=
    routeP_positive_full_period_packets_cofinal N
  exact (not_lt_of_ge (h (p * q) B hNB.le hborn hdiv)) hpos

end RHTower
