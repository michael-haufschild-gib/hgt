import GaloisForLFunctions.RHTower.RouteEFixedOrderTwoGradeOverpayment

/-!
# Parity of completed adjacent numerator pairs

Completing every denominator cofactor and pairing an odd squarefree numerator `a`
with `2a` preserves the parity of `a`. In the far cone the oriented pair has a
uniform positive margin. Thus the negative prime-pair payment reverses at every
positive-Möbius odd core; it does not extend as a common negative sign to all grades.
-/

namespace RHTower
noncomputable section

/-- Uniform parity margin for an adjacent pair of complete physical fibres. -/
theorem routeE_completed_double_pair_margin
    {r : ℝ} (hr : 1 ≤ r) (hr2 : r ≤ 2)
    {a : ℕ} (ha : 0 < a) (haOdd : Odd a) (haSq : Squarefree a)
    (q : Nat.Primes) (hqfar : 2048 * a ≤ (q : ℕ)) :
    (1 / 64 : ℝ) * (a : ℝ) * (q : ℝ) ^ (-(r + 1)) ≤
      (ArithmeticFunction.moebius a : ℝ) *
        (routeEFixedOrderIntegerNumeratorFibre r a q +
          routeEFixedOrderIntegerNumeratorFibre r (2 * a) q) := by
  let m : ℝ := (ArithmeticFunction.moebius a : ℝ)
  let t : ℝ := (q : ℝ) ^ (-(r + 1))
  let u : ℝ := (q : ℝ) ^ (-(r + 2))
  let A : ℝ := r * (a : ℝ) * t * routeE_coprimeMobiusMoment (r + 1) a (q : ℕ)
  let B : ℝ := r * (2 * (a : ℝ)) * t *
    routeE_coprimeMobiusMoment (r + 1) (2 * a) (q : ℕ)
  have hm : m ^ 2 = 1 := by
    dsimp [m]
    exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree haSq
  have hmabs : |m| = 1 := by
    dsimp [m]
    exact_mod_cast ArithmeticFunction.abs_moebius_eq_one_of_squarefree haSq
  have hdouble : (ArithmeticFunction.moebius (2 * a) : ℝ) = -m := by
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
      haOdd.coprime_two_left, ArithmeticFunction.moebius_apply_prime Nat.prime_two]
    simp [m]
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg _
  have hq0 : (0 : ℝ) < q := by exact_mod_cast q.property.pos
  have ht : 0 ≤ t := Real.rpow_nonneg hq0.le _
  have hu : 0 ≤ u := Real.rpow_nonneg hq0.le _
  have hqR : 2048 * (a : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqfar
  have hpow : u * (q : ℝ) = t := by
    dsimp [u, t]
    calc
      (q : ℝ) ^ (-(r + 2)) * (q : ℝ) =
          (q : ℝ) ^ (-(r + 2)) * (q : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = (q : ℝ) ^ (-(r + 2) + 1) := (Real.rpow_add hq0 _ _).symm
      _ = (q : ℝ) ^ (-(r + 1)) := by congr 1; ring
  have hfirst := routeE_integer_fibre_linearization hr hr2 a q
  have hsecond := routeE_integer_fibre_linearization hr hr2 (2 * a) q
  rw [hdouble] at hsecond
  have hfirst' : |routeEFixedOrderIntegerNumeratorFibre r a q + m * A| ≤
      24 * (a : ℝ) ^ 2 * u := by
    convert hfirst using 1
    dsimp [m, A, t, u]
    congr 1
    ring
  have hsecond' : |routeEFixedOrderIntegerNumeratorFibre r (2 * a) q - m * B| ≤
      96 * (a : ℝ) ^ 2 * u := by
    convert hsecond using 1 <;> dsimp [B, t, u] <;> push_cast <;> congr 1 <;> ring
  have hfirstOrient : |m * routeEFixedOrderIntegerNumeratorFibre r a q + A| ≤
      24 * (a : ℝ) ^ 2 * u := by
    calc
      _ = |m * (routeEFixedOrderIntegerNumeratorFibre r a q + m * A)| := by
        congr 1
        linear_combination -A * hm
      _ = |routeEFixedOrderIntegerNumeratorFibre r a q + m * A| := by
        rw [abs_mul, hmabs, one_mul]
      _ ≤ _ := hfirst'
  have hsecondOrient : |m * routeEFixedOrderIntegerNumeratorFibre r (2 * a) q - B| ≤
      96 * (a : ℝ) ^ 2 * u := by
    calc
      _ = |m * (routeEFixedOrderIntegerNumeratorFibre r (2 * a) q - m * B)| := by
        congr 1
        linear_combination B * hm
      _ = |routeEFixedOrderIntegerNumeratorFibre r (2 * a) q - m * B| := by
        rw [abs_mul, hmabs, one_mul]
      _ ≤ _ := hsecond'
  have hpay := routeE_coprimeMobiusMoment_payment
    (by linarith : 2 ≤ r + 1) a (q : ℕ) (by omega)
  have hmain : (7 / 90 : ℝ) * (r * (a : ℝ) * t) ≤ B - A := by
    have hscaled := mul_le_mul_of_nonneg_left hpay
      (show 0 ≤ r * (a : ℝ) * t by positivity)
    dsimp [A, B]
    nlinarith only [hscaled]
  have herror : 120 * (a : ℝ) ^ 2 * u ≤ (15 / 256 : ℝ) * (a : ℝ) * t := by
    have hscaled := mul_le_mul_of_nonneg_right hqR (mul_nonneg ha0 hu)
    nlinarith only [hscaled, hpow]
  have hrt : (a : ℝ) * t ≤ r * (a : ℝ) * t := by
    have h := mul_nonneg (sub_nonneg.mpr hr) (mul_nonneg ha0 ht)
    linarith
  change (1 / 64 : ℝ) * (a : ℝ) * t ≤ _
  change (1 / 64 : ℝ) * (a : ℝ) * t ≤ m * _
  nlinarith only [(abs_le.mp hfirstOrient).1, (abs_le.mp hsecondOrient).1,
    hmain, herror, hrt, mul_nonneg ha0 ht]

/-- The sign of the completed pair is the Möbius sign of its odd core. -/
theorem routeE_completed_double_pair_parity
    {r : ℝ} (hr : 1 ≤ r) (hr2 : r ≤ 2)
    {a : ℕ} (ha : 0 < a) (haOdd : Odd a) (haSq : Squarefree a)
    (q : Nat.Primes) (hqfar : 2048 * a ≤ (q : ℕ)) :
    0 < (ArithmeticFunction.moebius a : ℝ) *
      (routeEFixedOrderIntegerNumeratorFibre r a q +
        routeEFixedOrderIntegerNumeratorFibre r (2 * a) q) := by
  have hap : (0 : ℝ) < a := by exact_mod_cast ha
  have hqp : (0 : ℝ) < q := by exact_mod_cast q.property.pos
  exact lt_of_lt_of_le (by positivity)
    (routeE_completed_double_pair_margin hr hr2 ha haOdd haSq q hqfar)


/-- At arbitrarily large numerator scales, one common prime denominator supports
both positive and negative completed adjacent pairs, uniformly in `1 ≤ r ≤ 2`. -/
theorem routeE_completed_double_pairs_both_signs (N : ℕ) :
    ∃ a b : ℕ, ∃ q : Nat.Primes,
      N < a ∧ N < b ∧ Odd a ∧ Odd b ∧ Squarefree a ∧ Squarefree b ∧
      2048 * a ≤ (q : ℕ) ∧ 2048 * b ≤ (q : ℕ) ∧
      ∀ r : ℝ, 1 ≤ r → r ≤ 2 →
        (routeEFixedOrderIntegerNumeratorFibre r a q +
            routeEFixedOrderIntegerNumeratorFibre r (2 * a) q < 0) ∧
        (0 < routeEFixedOrderIntegerNumeratorFibre r b q +
            routeEFixedOrderIntegerNumeratorFibre r (2 * b) q) := by
  obtain ⟨p, hpLarge, hp⟩ := Nat.exists_infinite_primes (max (N + 1) 3)
  obtain ⟨l, hlLarge, hl⟩ := Nat.exists_infinite_primes (p + 1)
  have hp3 : 3 ≤ p := le_trans (le_max_right _ _) hpLarge
  have hNp : N < p := by have := le_trans (le_max_left _ _) hpLarge; omega
  have hpl : p < l := by omega
  have hpOdd : Odd p := hp.odd_of_ne_two (by omega)
  have hlOdd : Odd l := hl.odd_of_ne_two (by omega)
  have hcop : p.Coprime l := (Nat.coprime_primes hp hl).mpr (by omega)
  have hsquare : Squarefree (p * l) :=
    Nat.squarefree_mul_iff.mpr ⟨hcop, hp.squarefree, hl.squarefree⟩
  have hp_le : p ≤ p * l := by nlinarith [hl.one_lt]
  obtain ⟨q, hqLarge, hq⟩ := Nat.exists_infinite_primes (2048 * (p * l))
  let Q : Nat.Primes := ⟨q, hq⟩
  have hqP : 2048 * p ≤ (Q : ℕ) :=
    (Nat.mul_le_mul_left 2048 hp_le).trans hqLarge
  have hqB : 2048 * (p * l) ≤ (Q : ℕ) := hqLarge
  refine ⟨p, p * l, Q, hNp, hNp.trans_le hp_le, hpOdd, hpOdd.mul hlOdd,
    hp.squarefree, hsquare, hqP, hqB, ?_⟩
  intro r hr hr2
  have hneg := routeE_completed_double_pair_parity hr hr2 hp.pos hpOdd hp.squarefree Q hqP
  have hpos := routeE_completed_double_pair_parity hr hr2
    (Nat.mul_pos hp.pos hl.pos) (hpOdd.mul hlOdd) hsquare Q hqB
  have hmup : (ArithmeticFunction.moebius p : ℝ) = -1 := by
    rw [ArithmeticFunction.moebius_apply_prime hp]
    simp
  have hmub : (ArithmeticFunction.moebius (p * l) : ℝ) = 1 := by
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
      ArithmeticFunction.moebius_apply_prime hp, ArithmeticFunction.moebius_apply_prime hl]
    simp
  rw [hmup] at hneg
  rw [hmub, one_mul] at hpos
  exact ⟨by linarith, hpos⟩

end
end RHTower
