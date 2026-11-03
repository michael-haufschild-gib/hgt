import GaloisForLFunctions.DimensionZeroGeometryOfSpecZ.TheTateFamilyChangesSignAtDimensionZero

/-!
# The wall is a Dirichlet inversion

The Jordan family is positive for `k > 0` and parity-signed for `k < 0`
(`TheTateFamilyChangesSignAtDimensionZero`). This module gives the exact identity across the wall
`k = 0`.

* **Reflection formula** (`jordanTotient_neg`): for `n ≥ 1`,
  `J_{−k}(n) = (−1)^{ω(n)} rad(n)^k n^{−2k} J_k(n)`, `rad(n) = ∏_{p∣n} p` (`radical`). Negative
  dimension is positive dimension times the parity of the number of prime factors and a positive
  weight.
* **The centred family** `K_k(n) = n^{−k/2}J_k(n)` (`centredTate`), the coefficients of
  `ζ(s − k/2)/ζ(s + k/2)`, has `∂_kK_k|₀ = Λ` like `J_k`, and **the reflection `k ↦ −k` is Dirichlet
  inversion** (`centredTate_neg_mul`): `K_{−k} * K_k = 1`. Pointwise the inverse is
  `K_{−k}(n) = (−1)^{ω(n)}(rad n/n)^k K_k(n)` (`centredTate_neg_apply`).
* **On squarefree integers the wall acts by the Möbius function** (`centredTate_neg_of_squarefree`):
  `K_{−k}(n) = μ(n)K_k(n)`. The centred count of a squarefree `n` is even or odd in the dimension
  according to the parity of `ω(n)`.

So crossing dimension zero is inverting the Tate family, and the inversion is diagonal: it multiplies
the count of `n` by `μ(n)` (squarefree `n`). The first jet at `k = 0` is carried by the odd part of the
family, and among squarefree integers only the primes (`ω = 1`) contribute to it; Weil's term is the
part of the arithmetic on which the reflection acts by `−1` to first order. This is the identity
across the wall asked for in DZG §7.4, in exact form.
-/

noncomputable section

namespace GaloisForLFunctions.DimensionZeroGeometryOfSpecZ

open WindowTowerOfSpecZ ArithmeticDegenerationTheory
open scoped ArithmeticFunction.omega ArithmeticFunction.Moebius ArithmeticFunction.Omega

/-- The **radical** `rad n = ∏_{p∣n} p`. -/
def radical (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

theorem radical_mul {a b : ℕ} (hab : a.Coprime b) : radical (a * b) = radical a * radical b := by
  rw [radical, Nat.Coprime.primeFactors_mul hab, Finset.prod_union hab.disjoint_primeFactors]
  rfl

theorem radical_prime_pow {p a : ℕ} (hp : p.Prime) (ha : a ≠ 0) : radical (p ^ a) = p := by
  rw [radical, Nat.primeFactors_prime_pow ha hp, Finset.prod_singleton]

theorem radical_pos (n : ℕ) : 0 < radical n :=
  Finset.prod_pos fun _ hp => (Nat.prime_of_mem_primeFactors hp).pos

/-- **The reflection formula across the wall**:
`J_{−k}(n) = (−1)^{ω(n)} rad(n)^k n^{−2k} J_k(n)` for `n ≥ 1`. -/
theorem jordanTotient_neg (k : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    jordanTotient (-k) n =
      (-1 : ℝ) ^ ω n * (radical n : ℝ) ^ k * (n : ℝ) ^ (-2 * k) * jordanTotient k n := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p a hp ha =>
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    rw [ArithmeticFunction.cardDistinctFactors_apply_prime_pow hp ha.ne', radical_prime_pow hp ha.ne',
      jordanTotient_prime_pow hp (-k) ha, jordanTotient_prime_pow hp k ha, pow_one]
    have hcast : ((a - 1 : ℕ) : ℝ) = (a : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
    have hpa : ((p ^ a : ℕ) : ℝ) ^ (-2 * k) = (p : ℝ) ^ ((a : ℝ) * (-2 * k)) := by
      rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
    rw [hpa, hcast]
    have e1 : (p : ℝ) ^ k * (p : ℝ) ^ ((a : ℝ) * (-2 * k)) * (p : ℝ) ^ (k * ((a : ℝ) - 1)) =
        (p : ℝ) ^ (-k * a) := by
      rw [← Real.rpow_add hp0, ← Real.rpow_add hp0]; congr 1; ring
    have e2 : (p : ℝ) ^ (-k * ((a : ℝ) - 1)) * (p : ℝ) ^ (-k) = (p : ℝ) ^ (-k * a) := by
      rw [← Real.rpow_add hp0]; congr 1; ring
    have e3 : (p : ℝ) ^ (-k * ((a : ℝ) - 1)) = (p : ℝ) ^ (-k * a) * (p : ℝ) ^ k := by
      rw [← Real.rpow_add hp0]; congr 1; ring
    calc (p : ℝ) ^ (-k * ((a : ℝ) - 1)) * ((p : ℝ) ^ (-k) - 1)
        = (p : ℝ) ^ (-k * ((a : ℝ) - 1)) * (p : ℝ) ^ (-k) - (p : ℝ) ^ (-k * ((a : ℝ) - 1)) := by ring
      _ = (p : ℝ) ^ (-k * a) - (p : ℝ) ^ (-k * a) * (p : ℝ) ^ k := by rw [e2, e3]
      _ = -1 * ((p : ℝ) ^ k * (p : ℝ) ^ ((a : ℝ) * (-2 * k)) * (p : ℝ) ^ (k * ((a : ℝ) - 1))) *
            ((p : ℝ) ^ k - 1) := by rw [e1]; ring
      _ = _ := by ring
  | zero => omega
  | one =>
    simp [jordanTotient_one, radical]
  | coprime a b ha hb hab iha ihb =>
    have hm := (isMultiplicative_jordanFun (-k)).map_mul_of_coprime hab
    have hm' := (isMultiplicative_jordanFun k).map_mul_of_coprime hab
    simp only [jordanFun_apply] at hm hm'
    rw [hm, hm', iha (by omega), ihb (by omega), ArithmeticFunction.cardDistinctFactors_mul hab,
      radical_mul hab, pow_add, Nat.cast_mul, Nat.cast_mul,
      Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _),
      Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    ring

/-- The **centred Tate family** `K_k(n) = n^{−k/2}J_k(n)`: the coefficients of `ζ(s − k/2)/ζ(s + k/2)`. -/
def centredTate (k : ℝ) : ArithmeticFunction ℝ := tateTwist (k / 2) (jordanFun k)

theorem centredTate_apply (k : ℝ) (n : ℕ) :
    centredTate k n = jordanTotient k n * (n : ℝ) ^ (-(k / 2)) := by
  rw [centredTate, tateTwist_apply, jordanFun_apply]

/-- `K_k = twist_{−k/2}ζ * twist_{k/2}μ`. -/
theorem centredTate_eq (k : ℝ) :
    centredTate k = tateTwist (-(k / 2)) (ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
      tateTwist (k / 2) (ArithmeticFunction.moebius : ArithmeticFunction ℝ) := by
  rw [centredTate, jordanFun_eq, tateTwist_mul, tateTwist_tateTwist,
    show k / 2 + -k = -(k / 2) by ring]

/-- **The reflection across the wall is Dirichlet inversion**: `K_{−k} * K_k = 1`. -/
theorem centredTate_neg_mul (k : ℝ) : centredTate (-k) * centredTate k = 1 := by
  rw [centredTate_eq, centredTate_eq, show -(-k / 2) = k / 2 by ring, show -k / 2 = -(k / 2) by ring]
  have h1 : tateTwist (k / 2) (ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
      tateTwist (k / 2) (ArithmeticFunction.moebius : ArithmeticFunction ℝ) = 1 := by
    rw [← tateTwist_mul, ArithmeticFunction.coe_zeta_mul_coe_moebius, tateTwist_one]
  have h2 : tateTwist (-(k / 2)) (ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
      tateTwist (-(k / 2)) (ArithmeticFunction.moebius : ArithmeticFunction ℝ) = 1 := by
    rw [← tateTwist_mul, ArithmeticFunction.coe_zeta_mul_coe_moebius, tateTwist_one]
  calc tateTwist (k / 2) (ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
        tateTwist (-(k / 2)) (ArithmeticFunction.moebius : ArithmeticFunction ℝ) *
        (tateTwist (-(k / 2)) (ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
          tateTwist (k / 2) (ArithmeticFunction.moebius : ArithmeticFunction ℝ))
      = (tateTwist (k / 2) (ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
          tateTwist (k / 2) (ArithmeticFunction.moebius : ArithmeticFunction ℝ)) *
        (tateTwist (-(k / 2)) (ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
          tateTwist (-(k / 2)) (ArithmeticFunction.moebius : ArithmeticFunction ℝ)) := by ring
    _ = 1 := by rw [h1, h2, one_mul]

/-- **Pointwise, the inverse is the parity-signed family**:
`K_{−k}(n) = (−1)^{ω(n)}(rad n/n)^k K_k(n)` for `n ≥ 1`. -/
theorem centredTate_neg_apply (k : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    centredTate (-k) n = (-1 : ℝ) ^ ω n * ((radical n : ℝ) / n) ^ k * centredTate k n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hr0 : (0 : ℝ) ≤ radical n := Nat.cast_nonneg _
  rw [centredTate_apply, centredTate_apply, jordanTotient_neg k hn,
    Real.div_rpow hr0 hn0.le]
  have e : (n : ℝ) ^ (-2 * k) * (n : ℝ) ^ (-(-k / 2)) = (n : ℝ) ^ (-(k / 2)) / (n : ℝ) ^ k := by
    rw [← Real.rpow_add hn0, eq_div_iff (Real.rpow_pos_of_pos hn0 k).ne', ← Real.rpow_add hn0]
    congr 1; ring
  calc (-1 : ℝ) ^ ω n * (radical n : ℝ) ^ k * (n : ℝ) ^ (-2 * k) * jordanTotient k n *
        (n : ℝ) ^ (-(-k / 2))
      = (-1 : ℝ) ^ ω n * (radical n : ℝ) ^ k * jordanTotient k n *
          ((n : ℝ) ^ (-2 * k) * (n : ℝ) ^ (-(-k / 2))) := by ring
    _ = _ := by rw [e]; field_simp

/-- **On squarefree integers the wall acts by the Möbius function**: `K_{−k}(n) = μ(n)K_k(n)`. -/
theorem centredTate_neg_of_squarefree (k : ℝ) {n : ℕ} (hsq : Squarefree n) :
    centredTate (-k) n = (μ n : ℝ) * centredTate k n := by
  have hn0 : n ≠ 0 := hsq.ne_zero
  rw [centredTate_neg_apply k (Nat.one_le_iff_ne_zero.mpr hn0), radical,
    Nat.prod_primeFactors_of_squarefree hsq,
    div_self (by exact_mod_cast hn0 : (n : ℝ) ≠ 0), Real.one_rpow, mul_one,
    ArithmeticFunction.moebius_apply_of_squarefree hsq,
    ← (ArithmeticFunction.cardDistinctFactors_eq_cardFactors_iff_squarefree hn0).mpr hsq]
  push_cast
  ring

end GaloisForLFunctions.DimensionZeroGeometryOfSpecZ
