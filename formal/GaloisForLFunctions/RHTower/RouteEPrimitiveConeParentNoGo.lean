import GaloisForLFunctions.RHTower.RouteEQuotientParentLoad
import GaloisForLFunctions.RHTower.Sieve.MoebiusScaledReindex
import Mathlib.Data.Nat.Prime.Infinite

/-!
# Why the one-dimensional parent flow stops at primitive ratios

For a primitive paired ratio `(a,b)` with `0 < 2a < b`, the positive kernel
left after pairing the two small endpoints is
`1/(a+b) - 1/(2a+b) = a/((a+b)(2a+b))`.  Unlike the integer-ratio
quotient kernel, this weight is *strictly increasing* in the small endpoint
throughout the physical paired cone.  Reducing a positive pair's numerator
to a negative parent preserves support but makes that parent lighter.

The concrete `(3,7)` Möbius pair is positive, and its only numerator parent
`(1,7)` has insufficient negative weight even before any other children are
charged.  Reducing the denominator from prime `7` to `1` exits the paired
cone.  Even the neighboring signed `2×2` rectangle with denominator labels
`7,10` is positive.  This refutes direct coordinatewise and one-rectangle
extensions of the quotient parent proof; it does not refute nonlocal
cancellation of the full covariance.
-/

open ArithmeticFunction

namespace RHTower

noncomputable section

/-- Positive kernel of a primitive two-edge Gamma--Hankel pair at exponent one. -/
def routeEPrimitiveConeWeight (a b : ℝ) : ℝ :=
  a / ((a + b) * (2 * a + b))

theorem routeEPrimitiveConeWeight_eq_diff {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    routeEPrimitiveConeWeight a b =
      1 / (a + b) - 1 / (2 * a + b) := by
  unfold routeEPrimitiveConeWeight
  have h1 : 0 < a + b := by positivity
  have h2 : 0 < 2 * a + b := by positivity
  field_simp
  ring

/-- Numerator descent loses weight everywhere inside the paired ratio cone. -/
theorem routeEPrimitiveConeWeight_strictMono_num {x y b : ℝ}
    (hx : 0 < x) (hxy : x < y) (hcone : 2 * y < b) :
    routeEPrimitiveConeWeight x b < routeEPrimitiveConeWeight y b := by
  have hy : 0 < y := lt_trans hx hxy
  have hb : 0 < b := by linarith
  have hdenx : 0 < (x + b) * (2 * x + b) := by positivity
  have hdeny : 0 < (y + b) * (2 * y + b) := by positivity
  have hgap1 : 0 < (b - 2 * y) * (b + 2 * y) :=
    mul_pos (by linarith) (by linarith)
  have hgap2 : x * y < y * y := mul_lt_mul_of_pos_right hxy hy
  have hgap : 0 < b ^ 2 - 2 * x * y := by
    nlinarith [hgap1, hgap2, sq_nonneg y]
  have hprod : 0 < (y - x) * (b ^ 2 - 2 * x * y) :=
    mul_pos (by linarith) hgap
  unfold routeEPrimitiveConeWeight
  apply (div_lt_div_iff₀ hdenx hdeny).2
  nlinarith [hprod]

/-- The positive `(3,7)` child exceeds its negative `(1,7)` parent. -/
theorem routeEPrimitive_three_seven_one_parent_deficit_pos :
    0 < (moebius 3 : ℝ) * (moebius 7 : ℝ) * routeEPrimitiveConeWeight 3 7 +
        (moebius 1 : ℝ) * (moebius 7 : ℝ) * routeEPrimitiveConeWeight 1 7 := by
  have h3 : moebius 3 = -1 := by
    simpa using ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3)
  have h7 : moebius 7 = -1 := by
    simpa using ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 7)
  have h1 : moebius 1 = 1 := by simp
  rw [h3, h7, h1]
  norm_num at *
  exact routeEPrimitiveConeWeight_strictMono_num
    (by norm_num) (by norm_num) (by norm_num)

/-- The denominator parent of `(3,7)` is outside `2a < b`. -/
theorem routeEPrimitive_three_seven_denominator_parent_exits :
    ¬ (2 * (3 : ℕ) < 1) := by omega

/-- One nearest-neighbor signed rectangle still has positive net weight. -/
theorem routeEPrimitive_local_two_by_two_rectangle_positive :
    0 < (moebius 1 : ℝ) * (moebius 7 : ℝ) * routeEPrimitiveConeWeight 1 7 +
        (moebius 3 : ℝ) * (moebius 7 : ℝ) * routeEPrimitiveConeWeight 3 7 +
        (moebius 1 : ℝ) * (moebius 10 : ℝ) * routeEPrimitiveConeWeight 1 10 +
        (moebius 3 : ℝ) * (moebius 10 : ℝ) * routeEPrimitiveConeWeight 3 10 := by
  have h3 : moebius 3 = -1 := by
    simpa using ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3)
  have h7 : moebius 7 = -1 := by
    simpa using ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 7)
  have h2 : moebius 2 = -1 := by
    simpa using ArithmeticFunction.moebius_apply_prime Nat.prime_two
  have h5 : moebius 5 = -1 := by
    simpa using ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 5)
  have h10 : moebius 10 = 1 := by
    rw [show (10 : ℕ) = 2 * 5 by norm_num,
      RHTower.Sieve.moebius_mul_of_coprime (by norm_num : Nat.Coprime 2 5), h2, h5]
    norm_num
  have h1 : moebius 1 = 1 := by simp
  rw [h1, h3, h7, h10]
  norm_num [routeEPrimitiveConeWeight]

/-! ## Capacity and forward-insertion tests -/

/-- Far inside the cone, a prime numerator child can outweigh its root
parent by an arbitrarily large factor. -/
private theorem primitive_root_parent_ratio_large {a b C : ℝ}
    (ha : 0 < a) (hC : 0 ≤ C) (hlarge : 3 * C < a) (hb : 2 * a < b) :
    C * routeEPrimitiveConeWeight 1 b < routeEPrimitiveConeWeight a b := by
  have hb0 : 0 < b := by linarith
  have hd0 : 0 < (a + b) * (2 * a + b) := by positivity
  have hp0 : 0 < (1 + b) * (2 + b) := by positivity
  have hden : (a + b) * (2 * a + b) ≤ 3 * b ^ 2 := by
    have hh : 0 ≤ (b - 2 * a) * (2 * b + a) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hnum : b ^ 2 ≤ (1 + b) * (2 + b) := by nlinarith
  have hleft : C * ((a + b) * (2 * a + b)) ≤ C * (3 * b ^ 2) :=
    mul_le_mul_of_nonneg_left hden hC
  have hmiddle : C * (3 * b ^ 2) < a * b ^ 2 := by
    have hh := mul_pos (sub_pos.mpr hlarge) (sq_pos_of_pos hb0)
    nlinarith
  have hright : a * b ^ 2 ≤ a * ((1 + b) * (2 + b)) :=
    mul_le_mul_of_nonneg_left hnum ha.le
  unfold routeEPrimitiveConeWeight
  have hquot : C / ((1 + b) * (2 + b)) < a / ((a + b) * (2 * a + b)) := by
    apply (div_lt_div_iff₀ hp0 hd0).2
    exact lt_of_le_of_lt hleft (lt_of_lt_of_le hmiddle hright)
  simpa [div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc] using hquot

/-- No fixed-capacity root-parent map can pay all positive prime--prime
primitive pairs. Both labels are genuine coprime primes in the physical cone. -/
theorem routeEPrimitive_no_uniform_root_parent_capacity :
    ¬ ∃ C : ℝ, 0 ≤ C ∧ ∀ p q : ℕ,
      Nat.Prime p → Nat.Prime q → Nat.Coprime p q → 2 * p < q →
      routeEPrimitiveConeWeight p q ≤ C * routeEPrimitiveConeWeight 1 q := by
  rintro ⟨C, hC, hbound⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (3 * C)
  obtain ⟨p, hpn, hp⟩ := Nat.exists_infinite_primes (n + 1)
  obtain ⟨q, hq, hqprime⟩ := Nat.exists_infinite_primes (2 * p + 1)
  have hpC : 3 * C < (p : ℝ) := by
    have hpn' : (n : ℝ) < (p : ℝ) := by exact_mod_cast (show n < p by omega)
    exact lt_trans hn hpn'
  have hpq : 2 * p < q := by omega
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hqprime).mpr (by omega)
  have hstrict : C * routeEPrimitiveConeWeight 1 q < routeEPrimitiveConeWeight p q :=
    primitive_root_parent_ratio_large (by exact_mod_cast hp.pos) hC hpC
      (by exact_mod_cast hpq)
  exact (not_le_of_gt hstrict) (hbound p q hp hqprime hcop hpq)

/-- Reversing the local flow works for one admissible prime insertion:
a source-positive numerator becomes source-negative with larger weight. -/
theorem routeEPrimitive_forward_prime_signed {a b ell : ℕ}
    (hell : Nat.Prime ell) (ha : 0 < a) (hcop : Nat.Coprime ell a)
    (hcone : 2 * (ell * a) < b)
    (hsign : (moebius a : ℝ) * (moebius b : ℝ) = 1) :
    (moebius a : ℝ) * (moebius b : ℝ) * routeEPrimitiveConeWeight a b +
      (moebius (ell * a) : ℝ) * (moebius b : ℝ) *
        routeEPrimitiveConeWeight (ell * a) b < 0 := by
  have hmu : (moebius (ell * a) : ℝ) = -(moebius a : ℝ) := by
    rw [RHTower.Sieve.moebius_mul_of_coprime hcop]
    have he : moebius ell = -1 := ArithmeticFunction.moebius_apply_prime hell
    rw [he]
    norm_num
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hlt : (a : ℝ) < ell * a := by
    have hellR : (1 : ℝ) < ell := by exact_mod_cast hell.one_lt
    simpa only [one_mul] using mul_lt_mul_of_pos_right hellR haR
  have hconeR : (2 : ℝ) * (ell * a) < b := by exact_mod_cast hcone
  have hweight := routeEPrimitiveConeWeight_strictMono_num haR hlt hconeR
  rw [hmu]
  calc
    _ = ((moebius a : ℝ) * (moebius b : ℝ)) *
        (routeEPrimitiveConeWeight a b - routeEPrimitiveConeWeight (ell * a) b) := by ring
    _ = routeEPrimitiveConeWeight a b - routeEPrimitiveConeWeight (ell * a) b := by
      rw [hsign, one_mul]
    _ < 0 := sub_neg.mpr hweight

private theorem primitive_cone_upper {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    routeEPrimitiveConeWeight a b ≤ a / b ^ 2 := by
  have hd : 0 < (a + b) * (2 * a + b) := by positivity
  have hb2 : 0 < b ^ 2 := sq_pos_of_pos hb
  have hden : b ^ 2 ≤ (a + b) * (2 * a + b) := by
    nlinarith [mul_nonneg ha (by linarith : 2 * a + 3 * b ≥ 0)]
  unfold routeEPrimitiveConeWeight
  apply (div_le_div_iff₀ hd hb2).2
  exact mul_le_mul_of_nonneg_left hden ha

private theorem primitive_cone_fifteen_lower {a b : ℝ} (ha : 0 < a) (hb : 60 * a ≤ b) :
    8 * a / b ^ 2 ≤ routeEPrimitiveConeWeight (15 * a) b := by
  have hb0 : 0 < b := lt_of_lt_of_le (by positivity : 0 < 60 * a) hb
  have hd : 0 < (15 * a + b) * (2 * (15 * a) + b) := by positivity
  have hb2 : 0 < b ^ 2 := sq_pos_of_pos hb0
  have hden : 8 * ((15 * a + b) * (2 * (15 * a) + b)) ≤ 15 * b ^ 2 := by
    have hh : 0 ≤ (b - 60 * a) * (7 * b + 60 * a) :=
      mul_nonneg (sub_nonneg.mpr hb) (by positivity)
    nlinarith
  have hprod := mul_le_mul_of_nonneg_left hden ha.le
  unfold routeEPrimitiveConeWeight
  apply (div_le_div_iff₀ hb2 hd).2
  nlinarith only [hprod]

/-- The two-prime Boolean square reverses the one-prime negative sign
throughout a uniform far-cone region. -/
theorem routeEPrimitive_two_prime_cube_positive {a b : ℝ}
    (ha : 0 < a) (hb : 60 * a ≤ b) :
    0 < routeEPrimitiveConeWeight a b - routeEPrimitiveConeWeight (3 * a) b -
      routeEPrimitiveConeWeight (5 * a) b + routeEPrimitiveConeWeight (15 * a) b := by
  have hb0 : 0 < b := lt_of_lt_of_le (by positivity : 0 < 60 * a) hb
  have hbase : 0 < routeEPrimitiveConeWeight a b := by
    unfold routeEPrimitiveConeWeight
    positivity
  have h3 := primitive_cone_upper (a := 3 * a) (b := b) (by positivity) hb0
  have h5 := primitive_cone_upper (a := 5 * a) (b := b) (by positivity) hb0
  have h15 := primitive_cone_fifteen_lower ha hb
  have hsum : routeEPrimitiveConeWeight (3 * a) b +
      routeEPrimitiveConeWeight (5 * a) b ≤ 8 * a / b ^ 2 := by
    calc
      _ ≤ 3 * a / b ^ 2 + 5 * a / b ^ 2 := add_le_add h3 h5
      _ = 8 * a / b ^ 2 := by ring
  have hcancel := le_trans hsum h15
  linarith

/-- An actual prime--prime primitive-ratio square has the positive sign:
numerators 7, 21, 35, 105 carry Möbius signs -, +, +, -. -/
theorem routeEPrimitive_two_prime_source_cube_positive {q : ℕ}
    (hq : Nat.Prime q) (hqbound : 420 ≤ q) :
    Nat.Coprime 105 q ∧
    0 < (moebius 7 : ℝ) * (moebius q : ℝ) * routeEPrimitiveConeWeight 7 q +
      (moebius 21 : ℝ) * (moebius q : ℝ) * routeEPrimitiveConeWeight 21 q +
      (moebius 35 : ℝ) * (moebius q : ℝ) * routeEPrimitiveConeWeight 35 q +
      (moebius 105 : ℝ) * (moebius q : ℝ) * routeEPrimitiveConeWeight 105 q := by
  have h3 : moebius 3 = -1 := ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3)
  have h5 : moebius 5 = -1 := ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 5)
  have h7 : moebius 7 = -1 := ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 7)
  have hqmu : moebius q = -1 := ArithmeticFunction.moebius_apply_prime hq
  have h21 : moebius 21 = 1 := by
    rw [show (21 : ℕ) = 3 * 7 by norm_num,
      RHTower.Sieve.moebius_mul_of_coprime (by norm_num : Nat.Coprime 3 7), h3, h7]
    norm_num
  have h35 : moebius 35 = 1 := by
    rw [show (35 : ℕ) = 5 * 7 by norm_num,
      RHTower.Sieve.moebius_mul_of_coprime (by norm_num : Nat.Coprime 5 7), h5, h7]
    norm_num
  have h105 : moebius 105 = -1 := by
    rw [show (105 : ℕ) = 3 * 35 by norm_num,
      RHTower.Sieve.moebius_mul_of_coprime (by norm_num : Nat.Coprime 3 35), h3, h35]
    norm_num
  have hcop : Nat.Coprime 105 q :=
    (Nat.coprime_of_lt_prime (by norm_num : 105 ≠ 0) (by omega : 105 < q) hq).symm
  refine ⟨hcop, ?_⟩
  rw [h7, hqmu, h21, h35, h105]
  have hweight := routeEPrimitive_two_prime_cube_positive (a := (7 : ℝ)) (b := (q : ℝ))
    (by norm_num) (by exact_mod_cast hqbound)
  convert hweight using 1
  ring_nf

end
end RHTower
