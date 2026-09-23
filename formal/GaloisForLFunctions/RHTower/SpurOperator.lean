/-
Doc 28 §1 (task #143): the pair-as-operator identity, machine-checked.

For a polynomial `A` of degree ≤ d with polar-chain companions `B₁ = d·A − X·A′` and
`B₂ = (d−1)·B₁ − X·B₁′` (the denominator-cleared `A_{d−1}`, `A_{d−2}` of doc 23's
three-term identity), reflection at degree `d` intertwines the pair three-term
combination with a constant-coefficient second-order operator:

  `reflect d (u·A − v·X·B₁ + X²·B₂) = Â″ − v·Â′ + u·Â`,  `Â = reflect d A`.

With `u = τ·τ̄`, `v = τ + τ̄` this is `Ĵ = (D−τ)(D−τ̄)Â`: multiplying the carrier by the
pair `(x−τ)(x−τ̄)` acts on reversed sections as the damped-oscillator operator — the
algebraic engine behind the winding formula and theorem-m's transfer (doc 28).

Supporting API: `reflect_polarStep` (reflection sends the polar derivative to the plain
derivative — the polar/derivative duality of doc 26 §0), plus small reflect lemmas.
-/
import Mathlib

namespace RHTower

open Polynomial

variable {R : Type*} [CommRing R]

/-- The denominator-cleared polar-derivative companion `n·A − X·A′`
(equal to `n·A_{n−1}` when `A = A_n` is a Jensen section, by the polar chain). -/
noncomputable def polarStep (n : ℕ) (A : R[X]) : R[X] :=
  C (n : R) * A - X * derivative A

theorem coeff_polarStep (n : ℕ) (A : R[X]) (k : ℕ) :
    (polarStep n A).coeff k = A.coeff k * ((n : R) - (k : R)) := by
  rcases k with _ | k
  · rw [polarStep, coeff_sub, coeff_C_mul, mul_coeff_zero, coeff_X_zero, zero_mul]
    push_cast
    ring
  · rw [polarStep, coeff_sub, coeff_C_mul, coeff_X_mul, coeff_derivative]
    push_cast
    ring

theorem natDegree_polarStep_le (A : R[X]) {n : ℕ} (hA : A.natDegree ≤ n) :
    (polarStep n A).natDegree ≤ n - 1 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro m hm
  rw [coeff_polarStep]
  rcases Nat.lt_or_ge n m with h | h
  · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hA h), zero_mul]
  · have hmn : m = n := by omega
    subst hmn
    simp

/-- **Polar/derivative duality**: reflection sends the polar derivative at the top
degree to the plain derivative of the reflected polynomial (doc 26 §0, doc 28 §1). -/
theorem reflect_polarStep (A : R[X]) {n : ℕ} (hn : 1 ≤ n) (hA : A.natDegree ≤ n) :
    reflect (n - 1) (polarStep n A) = derivative (reflect n A) := by
  ext i
  rw [coeff_reflect, coeff_derivative, coeff_reflect]
  rcases Nat.lt_or_ge (n - 1) i with h | h
  · -- outer range: both sides vanish
    rw [revAt_eq_self_of_lt h, coeff_polarStep,
      revAt_eq_self_of_lt (show n < i + 1 by omega)]
    rcases Nat.lt_or_ge n i with h3 | h3
    · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hA h3),
        coeff_eq_zero_of_natDegree_lt (show A.natDegree < i + 1 by omega)]
      ring
    · have : i = n := by omega
      subst this
      rw [coeff_eq_zero_of_natDegree_lt (show A.natDegree < i + 1 by omega)]
      simp
  · -- inner range: `(i+1)·a_{n−1−i}` on both sides
    have hi1 : i + 1 ≤ n := by omega
    rw [revAt_le h, coeff_polarStep, revAt_le hi1,
      show n - 1 - i = n - (i + 1) by omega, Nat.cast_sub hi1]
    push_cast
    ring

theorem reflect_zero_eq (p : R[X]) : reflect 0 p = p := by
  ext i
  rw [coeff_reflect]
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rw [revAt_zero]
  · rw [revAt_eq_self_of_lt hi]

theorem reflect_X_pow_self (n : ℕ) : reflect n ((X : R[X]) ^ n) = 1 := by
  ext i
  rw [coeff_reflect, coeff_X_pow, Polynomial.coeff_one]
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rw [revAt_zero, if_pos rfl, if_pos rfl]
  · rcases Nat.lt_or_ge n i with h | h
    · rw [revAt_eq_self_of_lt h, if_neg (by omega), if_neg (by omega)]
    · rw [revAt_le h, if_neg (by omega), if_neg (by omega)]

theorem reflect_C_mul' (r : R) (p : R[X]) (N : ℕ) (hp : p.natDegree ≤ N) :
    reflect N (C r * p) = C r * reflect N p := by
  have h := reflect_mul (C r) p (F := 0) (G := N) (by simp) hp
  rw [zero_add] at h
  rw [h, reflect_zero_eq]

/-- **The pair as an operator** (doc 28 §1). Reflection at degree `d` sends the
three-term pair combination `u·A − v·X·B₁ + X²·B₂` (polar-chain companions
`B₁ = polarStep d A`, `B₂ = polarStep (d−1) B₁`) to the damped-oscillator operator
`Â″ − v·Â′ + u·Â` applied to `Â = reflect d A`. With `u = τ·τ̄`, `v = τ + τ̄`:
`Ĵ = (D−τ)(D−τ̄)Â`. -/
theorem reflect_pair_operator (u v : R) (A : R[X]) {d : ℕ}
    (hd : 2 ≤ d) (hA : A.natDegree ≤ d) :
    reflect d (C u * A - C v * (X * polarStep d A)
        + X ^ (2 : ℕ) * polarStep (d - 1) (polarStep d A))
      = derivative (derivative (reflect d A)) - C v * derivative (reflect d A)
        + C u * reflect d A := by
  set B₁ := polarStep d A with hB₁
  set B₂ := polarStep (d - 1) B₁ with hB₂
  have hB₁deg : B₁.natDegree ≤ d - 1 := natDegree_polarStep_le A hA
  have hB₂deg : B₂.natDegree ≤ d - 2 := by
    have h := natDegree_polarStep_le B₁ hB₁deg
    have : d - 1 - 1 = d - 2 := by omega
    rwa [this] at h
  -- reflection is additive
  have refl_sub : ∀ f g : R[X], reflect d (f - g) = reflect d f - reflect d g := by
    intro f g; ext i; simp [coeff_reflect]
  have refl_add : ∀ f g : R[X], reflect d (f + g) = reflect d f + reflect d g := by
    intro f g; ext i; simp [coeff_reflect]
  -- piece 1: `C u * A`
  have h1 : reflect d (C u * A) = C u * reflect d A :=
    reflect_C_mul' u A d hA
  -- piece 2: `C v * (X * B₁)` reflects to `C v * Â′`
  have hXB₁ : reflect d (X * B₁) = derivative (reflect d A) := by
    have h := reflect_mul (X : R[X]) B₁ (F := 1) (G := d - 1) natDegree_X_le hB₁deg
    rw [show 1 + (d - 1) = d by omega] at h
    rw [h, show (X : R[X]) = X ^ (1 : ℕ) by rw [pow_one], reflect_X_pow_self, one_mul,
      reflect_polarStep A (by omega) hA]
  have h2 : reflect d (C v * (X * B₁)) = C v * derivative (reflect d A) := by
    have hdeg : (X * B₁).natDegree ≤ d := by
      calc (X * B₁).natDegree ≤ X.natDegree + B₁.natDegree := natDegree_mul_le
        _ ≤ 1 + (d - 1) := by
            have := natDegree_X_le (R := R)
            omega
        _ = d := by omega
    rw [reflect_C_mul' v (X * B₁) d hdeg, hXB₁]
  -- piece 3: `X² * B₂` reflects to `Â″`
  have h3 : reflect d (X ^ (2 : ℕ) * B₂) = derivative (derivative (reflect d A)) := by
    have hX2 : ((X : R[X]) ^ (2 : ℕ)).natDegree ≤ 2 := by
      have h1 := natDegree_X_le (R := R)
      have h2 : ((X : R[X]) ^ (2 : ℕ)).natDegree ≤ 2 * (X : R[X]).natDegree := natDegree_pow_le
      omega
    have h := reflect_mul ((X : R[X]) ^ (2 : ℕ)) B₂ (F := 2) (G := d - 2) hX2 hB₂deg
    rw [show 2 + (d - 2) = d by omega] at h
    have hstep : reflect (d - 2) B₂ = derivative (derivative (reflect d A)) := by
      have hk := reflect_polarStep B₁ (n := d - 1) (by omega) hB₁deg
      rw [show d - 1 - 1 = d - 2 by omega] at hk
      rw [hB₂] at *
      rw [hk, reflect_polarStep A (by omega) hA]
    rw [h, reflect_X_pow_self, one_mul, hstep]
  rw [refl_add, refl_sub, h1, h2, h3]
  ring

/-- ℂ-specialization: with `u = τ·τ̄` and `v = τ + τ̄` the reflected pair section is
`(D − τ)(D − τ̄)` applied to `Â` — the damped oscillator at frequency `Im τ`. -/
theorem reflect_pair_operator_complex (τ : ℂ) (A : ℂ[X]) {d : ℕ}
    (hd : 2 ≤ d) (hA : A.natDegree ≤ d) :
    reflect d (C (τ * (starRingEnd ℂ) τ) * A - C (τ + (starRingEnd ℂ) τ) * (X * polarStep d A)
        + X ^ (2 : ℕ) * polarStep (d - 1) (polarStep d A))
      = derivative (derivative (reflect d A) - C ((starRingEnd ℂ) τ) * reflect d A)
        - C τ * (derivative (reflect d A) - C ((starRingEnd ℂ) τ) * reflect d A) := by
  rw [reflect_pair_operator (τ * (starRingEnd ℂ) τ) (τ + (starRingEnd ℂ) τ) A hd hA,
    derivative_sub, derivative_mul, derivative_C, zero_mul, zero_add, map_add, map_mul]
  ring

end RHTower
