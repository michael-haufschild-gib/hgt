import GaloisForLFunctions.RHTower.RouteEFixedOrderTwoGradeMomentPayment

/-!
The first adjacent numerator-grade payment at real receiver order. After completing
every physical denominator cofactor below a prime `q`, the `2p` numerator channel
more than pays the `p` channel in a far cone. This is a signed source statement;
it does not estimate the complete covariance over all numerator grades.
-/

open Finset
namespace RHTower
noncomputable section

/-- Exact first-order signed Möbius moment of a literal completed cofactor fibre. -/
theorem routeE_main_eq_moment
    (r : ℝ) (a : ℕ) (q : Nat.Primes) :
    routeEFixedOrderCofactorLinearMain r (a : ℝ) (q : ℕ)
      (fun d => if Nat.Coprime a d then
        (ArithmeticFunction.moebius a : ℝ) *
          (ArithmeticFunction.moebius ((q : ℕ) * d) : ℝ) else 0) =
      -(ArithmeticFunction.moebius a : ℝ) * r * (a : ℝ) *
        (q : ℝ) ^ (-(r + 1)) *
        routeE_coprimeMobiusMoment (r + 1) a (q : ℕ) := by
  unfold routeEFixedOrderCofactorLinearMain routeE_coprimeMobiusMoment
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdq : d < (q : ℕ) := (Finset.mem_Ioo.mp hd).2
  have hnot : ¬ (q : ℕ) ∣ d := by
    intro hdiv
    exact (Nat.not_le_of_gt hdq) (Nat.le_of_dvd (Finset.mem_Ioo.mp hd).1 hdiv)
  have hcop : Nat.Coprime (q : ℕ) d :=
    q.property.coprime_iff_not_dvd.mpr hnot
  have hmul := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop
  have hqmu : ArithmeticFunction.moebius (q : ℕ) = -1 :=
    ArithmeticFunction.moebius_apply_prime q.property
  have hqpos : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  have hdpos : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hrpow : ((q : ℝ) * (d : ℝ)) ^ (-(r + 1)) =
      (q : ℝ) ^ (-(r + 1)) * (d : ℝ) ^ (-(r + 1)) :=
    Real.mul_rpow hqpos hdpos
  by_cases hca : Nat.Coprime a d
  · simp only [if_pos hca, routeE_momentTerm]
    rw [hmul, hqmu, hrpow]
    push_cast
    ring
  · simp [hca, routeE_momentTerm]

theorem routeE_integer_coeff_bound (a : ℕ) (q : Nat.Primes) (d : ℕ) :
    |if Nat.Coprime a d then
      (ArithmeticFunction.moebius a : ℝ) *
        (ArithmeticFunction.moebius ((q : ℕ) * d) : ℝ) else 0| ≤ 1 := by
  split_ifs with h
  · rw [abs_mul]
    have ha : |(ArithmeticFunction.moebius a : ℝ)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := a)
    have hqd : |(ArithmeticFunction.moebius ((q : ℕ) * d) : ℝ)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := (q : ℕ) * d)
    nlinarith [abs_nonneg (ArithmeticFunction.moebius a : ℝ),
      abs_nonneg (ArithmeticFunction.moebius ((q : ℕ) * d) : ℝ)]
  · norm_num

/-- Quadratic kernel error after the exact arithmetic linearization. -/
theorem routeE_integer_fibre_linearization
    {r : ℝ} (hr : 1 ≤ r) (hr2 : r ≤ 2) (a : ℕ) (q : Nat.Primes) :
    |routeEFixedOrderIntegerNumeratorFibre r a q -
      (-(ArithmeticFunction.moebius a : ℝ) * r * (a : ℝ) *
        (q : ℝ) ^ (-(r + 1)) *
        routeE_coprimeMobiusMoment (r + 1) a (q : ℕ))| ≤
      24 * (a : ℝ) ^ (2 : ℕ) * (q : ℝ) ^ (-(r + 2)) := by
  have h := abs_routeEFixedOrderCofactorFibre_sub_linearMain_le
    hr hr2 (Nat.cast_nonneg a) q.property.pos
    (fun d => if Nat.Coprime a d then
      (ArithmeticFunction.moebius a : ℝ) *
        (ArithmeticFunction.moebius ((q : ℕ) * d) : ℝ) else 0)
    (routeE_integer_coeff_bound a q)
  rw [routeE_main_eq_moment] at h
  exact h

/-- The composite `2p` source overpays the prime `p` source uniformly throughout
the receiver interval `1 ≤ r ≤ 2`, once the prime denominator is far enough. -/
theorem routeE_prime_double_overpayment
    {r : ℝ} (hr : 1 ≤ r) (hr2 : r ≤ 2)
    (p q : Nat.Primes) (hp3 : 3 ≤ (p : ℕ))
    (hqfar : 2048 * (p : ℕ) ≤ (q : ℕ)) :
    routeEFixedOrderIntegerNumeratorFibre r (p : ℕ) q +
      routeEFixedOrderIntegerNumeratorFibre r (2 * (p : ℕ)) q ≤
        -(1 / 64 : ℝ) * (p : ℝ) * (q : ℝ) ^ (-(r + 1)) := by
  have hq6 : 6 ≤ (q : ℕ) := by omega
  have hqp : (0 : ℝ) < q := by exact_mod_cast q.property.pos
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg _
  have hqR : 2048 * (p : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqfar
  have hpneq2 : (p : ℕ) ≠ 2 := by omega
  have hcop : Nat.Coprime 2 (p : ℕ) := by
    exact Nat.coprime_two_left.mpr (p.property.odd_of_ne_two hpneq2)
  have hmup : ArithmeticFunction.moebius (p : ℕ) = -1 :=
    ArithmeticFunction.moebius_apply_prime p.property
  have hmu2p : ArithmeticFunction.moebius (2 * (p : ℕ)) = 1 := by
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
      ArithmeticFunction.moebius_apply_prime Nat.prime_two, hmup]
    norm_num
  have hpLin := routeE_integer_fibre_linearization hr hr2 (p : ℕ) q
  have h2pLin := routeE_integer_fibre_linearization hr hr2 (2 * (p : ℕ)) q
  rw [hmup] at hpLin
  rw [hmu2p] at h2pLin
  norm_num only [Int.cast_neg, Int.cast_one, neg_neg, one_mul] at hpLin h2pLin
  have hpay := routeE_coprimeMobiusMoment_payment
    (by linarith : 2 ≤ r + 1) (p : ℕ) (q : ℕ) hq6
  let x : ℝ := p
  let y : ℝ := q
  let t : ℝ := y ^ (-(r + 1))
  let u : ℝ := y ^ (-(r + 2))
  have ht : 0 ≤ t := Real.rpow_nonneg hqp.le _
  have hu : 0 ≤ u := Real.rpow_nonneg hqp.le _
  have hpow : u * y = t := by
    dsimp [u, t, y]
    calc
      (q : ℝ) ^ (-(r + 2)) * (q : ℝ) =
          (q : ℝ) ^ (-(r + 2)) * (q : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = (q : ℝ) ^ (-(r + 2) + 1) := (Real.rpow_add hqp _ _).symm
      _ = (q : ℝ) ^ (-(r + 1)) := by congr 1; ring
  have hpayScaled : r * x * t *
      (routeE_coprimeMobiusMoment (r + 1) (p : ℕ) (q : ℕ) -
        2 * routeE_coprimeMobiusMoment (r + 1) (2 * (p : ℕ)) (q : ℕ)) ≤
        -(7 / 90 : ℝ) * (r * x * t) := by
    calc
      _ ≤ (r * x * t) * (-(7 / 90 : ℝ)) :=
        mul_le_mul_of_nonneg_left hpay (by positivity)
      _ = _ := by ring
  have herror : 120 * x ^ (2 : ℕ) * u ≤ (15 / 256 : ℝ) * x * t := by
    have hmul := mul_le_mul_of_nonneg_right hqR
      (mul_nonneg hp0 hu)
    dsimp [x, y] at hmul ⊢
    nlinarith [hpow]
  have hprime := (abs_le.mp hpLin).2
  have hcomposite := (abs_le.mp h2pLin).2
  have hpair : routeEFixedOrderIntegerNumeratorFibre r (p : ℕ) q +
      routeEFixedOrderIntegerNumeratorFibre r (2 * (p : ℕ)) q ≤
        r * x * t *
          (routeE_coprimeMobiusMoment (r + 1) (p : ℕ) (q : ℕ) -
            2 * routeE_coprimeMobiusMoment (r + 1) (2 * (p : ℕ)) (q : ℕ)) +
          120 * x ^ (2 : ℕ) * u := by
    dsimp [x, t, u]
    push_cast at hcomposite
    nlinarith [hprime, hcomposite]
  have hrt : x * t ≤ r * x * t := by
    have h := mul_nonneg (sub_nonneg.mpr hr) (mul_nonneg hp0 ht)
    nlinarith
  calc
    routeEFixedOrderIntegerNumeratorFibre r (p : ℕ) q +
        routeEFixedOrderIntegerNumeratorFibre r (2 * (p : ℕ)) q ≤
          r * x * t *
            (routeE_coprimeMobiusMoment (r + 1) (p : ℕ) (q : ℕ) -
              2 * routeE_coprimeMobiusMoment (r + 1) (2 * (p : ℕ)) (q : ℕ)) +
            120 * x ^ (2 : ℕ) * u := hpair
    _ ≤ -(7 / 90 : ℝ) * (r * x * t) + 120 * x ^ (2 : ℕ) * u := by
      linarith [hpayScaled]
    _ ≤ -(7 / 90 : ℝ) * (x * t) + (15 / 256 : ℝ) * x * t := by
      linarith [hrt, herror]
    _ ≤ -(1 / 64 : ℝ) * x * t := by nlinarith [mul_nonneg hp0 ht]
    _ = -(1 / 64 : ℝ) * (p : ℝ) * (q : ℝ) ^ (-(r + 1)) := by
      dsimp [x, t, y]

end
end RHTower
