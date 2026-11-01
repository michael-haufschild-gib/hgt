import GaloisForLFunctions.ArithmeticDegenerationTheory.TheLimitingMixedStructure
import GaloisForLFunctions.ArithmeticDegenerationTheory.TheDilationsLowerTheConductor

/-!
# The weight strings of the rescaled limit

The rescaled limit of the complete Weil family is diagonal in the conductor basis with
coefficients `J(m) = K · J_{β+1}(m)/φ(m)` (`TheLimitingMixedStructure`), and the dilation by a prime
lowers the conductor (`TheDilationsLowerTheConductor`). This file computes how the limiting
polarization changes along each `p`-tower `{m'p^a}`: the tower is a **weight string**.

* **Möbius lowering** (`sum_divisors_moebius_lowering`): every Möbius transform
  `Σ_{d∣m} μ(m/d) g(d)` of a function homogeneous along the `p`-tower (`g(pd) = a h(d)`,
  `g(d) = h(d)` for `p ∤ d`) lowers the conductor: it equals `a` (if `p² ∣ m`) or `a − 1`
  (if `p ∥ m`) times the transform of `h` at `m/p`. The dilation law of Ramanujan sums and the
  tower law of Jordan's totient are two instances.
* **Jordan totients along a tower** (`jordanTotient_prime_mul_of_dvd`): `J_k(m) = p^k J_k(m/p)` if
  `p² ∣ m`, `(p^k − 1) J_k(m/p)` if `p ∥ m`.
* **The weight string** (`jordanCoefficient_tower`): for the tilted spline (`β = 7`),
  `J(m) = p⁷ J(m/p)` if `p² ∣ m` and `J(m) = [8]_p J(m/p)` if `p ∥ m`, with
  `[8]_p = (p⁸ − 1)/(p − 1) = 1 + p + ⋯ + p⁷`. Inside a string the monodromy lowers the weight by
  exactly `β log p`; at the bottom of the string the step is the `p`-integer `[β + 1]_p`.
* **The deep part is pure** (`jordanCoefficient_deep`): along the deep part of a tower the
  dilation is an isometric lowering of the normalized packets (`dilationFactor_eq_one_of_sq_dvd`)
  and a homothety of ratio `p^{-7}` of the limiting polarization.
-/

noncomputable section

open Finset ArithmeticFunction

namespace GaloisForLFunctions.ArithmeticDegenerationTheory

open BezoutValuationIncidence

/-- **Möbius lowering.** If `g(pd) = a h(d)` and `g(d) = h(d)` for the divisors `d` of `m/p`
with `p ∤ d`, then `Σ_{d∣m} μ(m/d) g(d) = w · Σ_{d∣m/p} μ(m/p/d) h(d)` with `w = a` if `p² ∣ m` and
`w = a − 1` if `p ∥ m`. -/
theorem sum_divisors_moebius_lowering {p m : ℕ} (hp : p.Prime) (hm : 0 < m) (hpm : p ∣ m)
    (g h : ℕ → ℝ) (a : ℝ) (hg1 : ∀ d ∈ (m / p).divisors, g (p * d) = a * h d)
    (hg2 : ∀ d ∈ (m / p).divisors, ¬p ∣ d → g d = h d) :
    ∑ d ∈ m.divisors, moebiusReal (m / d) * g d =
      (if p ∣ m / p then a else a - 1) * ∑ d ∈ (m / p).divisors, moebiusReal (m / p / d) * h d := by
  have hsplit := sum_filter_add_sum_filter_not m.divisors (p ∣ ·)
    (fun d => moebiusReal (m / d) * g d)
  rw [← hsplit, sum_divisors_filter_prime_dvd hp hm hpm]
  set m' := m / p with hm'
  have hmm : m = p * m' := (Nat.mul_div_cancel' hpm).symm
  have hdvd : ∑ d ∈ m'.divisors, moebiusReal (m / (p * d)) * g (p * d) =
      a * ∑ d ∈ m'.divisors, moebiusReal (m' / d) * h d := by
    rw [mul_sum]
    refine sum_congr rfl fun d hd => ?_
    rw [show m / (p * d) = m' / d from (Nat.div_div_eq_div_mul m p d).symm, hg1 d hd]
    ring
  rw [hdvd]
  split_ifs with hpm'
  · have hzero : ∑ d ∈ m.divisors.filter (fun d => ¬p ∣ d), moebiusReal (m / d) * g d = 0 := by
      refine sum_eq_zero fun d hd => ?_
      simp only [mem_filter, Nat.mem_divisors] at hd
      have hcop : Nat.Coprime (p * p) d :=
        Nat.Coprime.mul ((Nat.Prime.coprime_iff_not_dvd hp).mpr hd.2)
          ((Nat.Prime.coprime_iff_not_dvd hp).mpr hd.2)
      have hpp : p * p ∣ m / d * d := by
        rw [Nat.div_mul_cancel hd.1.1, hmm]
        exact Nat.mul_dvd_mul_left p hpm'
      have hsq : ¬Squarefree (m / d) := fun hsf =>
        hp.not_isUnit (hsf p (hcop.dvd_of_dvd_mul_right hpp))
      simp [moebiusReal, moebius_eq_zero_of_not_squarefree hsq]
    rw [hzero, add_zero]
  · have hset : m.divisors.filter (fun d => ¬p ∣ d) = m'.divisors := by
      ext d
      simp only [mem_filter, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨hdm, -⟩, hpd⟩
        refine ⟨?_, (Nat.div_pos (Nat.le_of_dvd hm hpm) hp.pos).ne'⟩
        have hcop : Nat.Coprime d p :=
          Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpd)
        rw [hmm] at hdm
        exact hcop.dvd_of_dvd_mul_left hdm
      · rintro ⟨hdm', -⟩
        exact ⟨⟨hdm'.trans (hmm ▸ dvd_mul_left m' p), hm.ne'⟩, fun h => hpm' (h.trans hdm')⟩
    have hpart : ∑ d ∈ m.divisors.filter (fun d => ¬p ∣ d), moebiusReal (m / d) * g d =
        -∑ d ∈ m'.divisors, moebiusReal (m' / d) * h d := by
      rw [hset, ← sum_neg_distrib]
      refine sum_congr rfl fun d hd => ?_
      have hdm' := Nat.dvd_of_mem_divisors hd
      have hpd : ¬p ∣ d := fun h => hpm' (h.trans hdm')
      have hq : m / d = p * (m' / d) := by rw [hmm, Nat.mul_div_assoc p hdm']
      have hpq : Nat.Coprime p (m' / d) :=
        (Nat.Prime.coprime_iff_not_dvd hp).mpr fun h => hpm' (h.trans (Nat.div_dvd_of_dvd hdm'))
      have hmu : moebiusReal (m / d) = -moebiusReal (m' / d) := by
        rw [hq, moebiusReal, moebiusReal, isMultiplicative_moebius.map_mul_of_coprime hpq,
          moebius_apply_prime hp]
        push_cast
        ring
      rw [hmu, hg2 d hd hpd]
      ring
    rw [hpart]
    ring

/-- `J_k` as a Möbius transform. -/
theorem jordanTotient_eq_moebius (k : ℝ) (m : ℕ) :
    jordanTotient k m = ∑ d ∈ m.divisors, moebiusReal (m / d) * (d : ℝ) ^ k := by
  unfold jordanTotient moebiusReal
  rfl

/-- **Jordan totients along a tower.** `J_k(m) = p^k J_k(m/p)` if `p² ∣ m` and
`(p^k − 1) J_k(m/p)` if `p ∥ m`. -/
theorem jordanTotient_prime_mul_of_dvd {p m : ℕ} (hp : p.Prime) (hm : 0 < m) (hpm : p ∣ m)
    (k : ℝ) :
    jordanTotient k m =
      (if p ∣ m / p then (p : ℝ) ^ k else (p : ℝ) ^ k - 1) * jordanTotient k (m / p) := by
  rw [jordanTotient_eq_moebius, jordanTotient_eq_moebius]
  exact sum_divisors_moebius_lowering hp hm hpm (fun d => (d : ℝ) ^ k) (fun d => (d : ℝ) ^ k)
    ((p : ℝ) ^ k) (fun d _ => by push_cast; rw [Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)])
    (fun _ _ _ => rfl)

/-- Euler's totient along a tower: `φ(m) = p φ(m/p)` if `p² ∣ m`, `(p − 1) φ(m/p)` if `p ∥ m`. -/
theorem totient_prime_mul_of_dvd {p m : ℕ} (hp : p.Prime) (hpm : p ∣ m) :
    (m.totient : ℝ) = (if p ∣ m / p then (p : ℝ) else (p : ℝ) - 1) * (m / p).totient := by
  conv_lhs => rw [← Nat.mul_div_cancel' hpm]
  split_ifs with h
  · exact_mod_cast Nat.totient_mul_of_prime_of_dvd hp h
  · rw [Nat.totient_mul_of_prime_of_not_dvd hp h]
    push_cast [Nat.cast_sub hp.one_le]
    ring

/-- The `p`-integer `[8]_p = (p⁸ − 1)/(p − 1)`. -/
def pInteger (p : ℕ) : ℝ := ((p : ℝ) ^ (8 : ℝ) - 1) / ((p : ℝ) - 1)

theorem pInteger_eq_geom {p : ℕ} (hp : p.Prime) :
    pInteger p = ∑ i ∈ range 8, (p : ℝ) ^ i := by
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    linarith
  have hne : (p : ℝ) ≠ 1 := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    exact (by linarith : (1 : ℝ) < p).ne'
  rw [pInteger, geom_sum_eq hne]
  norm_cast

/-- **The weight string of the rescaled limit.** Along the `p`-tower, the Jordan coefficient of the
tilted spline is multiplied by `p⁷` at every deep step (`p² ∣ m`) and by `[8]_p` at the bottom
step (`p ∥ m`). -/
theorem jordanCoefficient_tower {p m : ℕ} (hp : p.Prime) (hm : 0 < m) (hpm : p ∣ m) :
    jordanCoefficient m =
      (if p ∣ m / p then (p : ℝ) ^ (7 : ℝ) else pInteger p) * jordanCoefficient (m / p) := by
  have hm' : 0 < m / p := Nat.div_pos (Nat.le_of_dvd hm hpm) hp.pos
  have ht : (0 : ℝ) < (m / p).totient := by exact_mod_cast Nat.totient_pos.mpr hm'
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    linarith
  unfold jordanCoefficient
  rw [jordanTotient_prime_mul_of_dvd hp hm hpm, totient_prime_mul_of_dvd hp hpm]
  split_ifs with h
  · have e : (p : ℝ) ^ (8 : ℝ) = p * p ^ (7 : ℝ) := by
      rw [show (8 : ℝ) = 1 + 7 by norm_num, Real.rpow_add hp0, Real.rpow_one]
    rw [e]
    field_simp
  · unfold pInteger
    field_simp

/-- **The deep part of a tower is pure.** If `p² ∣ m`, the dilation by `p` lowers the normalized
conductor packet isometrically and scales the limiting polarization by exactly `p^{-7}`. -/
theorem jordanCoefficient_deep {p m : ℕ} (hp : p.Prime) (hm : 0 < m) (hpm : p ∣ m)
    (hpm' : p ∣ m / p) :
    dilationFactor p m = 1 ∧ jordanCoefficient (conductorLower p m) =
      (p : ℝ) ^ (-(7 : ℝ)) * jordanCoefficient m := by
  refine ⟨dilationFactor_eq_one_of_sq_dvd hpm hpm', ?_⟩
  rw [conductorLower_of_dvd hpm, jordanCoefficient_tower hp hm hpm, if_pos hpm', ← mul_assoc,
    ← Real.rpow_add (by exact_mod_cast hp.pos)]
  simp

/-- At the bottom of a tower the step is the `p`-integer, which exceeds the deep step `p⁷`. -/
theorem pow_seven_lt_pInteger {p : ℕ} (hp : p.Prime) : (p : ℝ) ^ (7 : ℝ) < pInteger p := by
  rw [pInteger_eq_geom hp, show (7 : ℝ) = (7 : ℕ) by norm_num, Real.rpow_natCast,
    Finset.sum_range_succ]
  have : 0 < ∑ i ∈ range 7, (p : ℝ) ^ i :=
    sum_pos (fun i _ => pow_pos (by exact_mod_cast hp.pos) i) ⟨0, by simp⟩
  linarith

end GaloisForLFunctions.ArithmeticDegenerationTheory
