import Mathlib

/-!
# Integrality of a fractional exponent from divisor data

If `G` is meromorphic and `G^c` is single-valued, then `c · ord_ρ(G) ∈ ℤ` at every point, because the
monodromy of `G^c` around `ρ` is `exp(2πi c · ord_ρ G)`.  Two zeros whose orders are coprime
therefore force `c ∈ ℤ`; a single simple zero already does.

The arithmetic core is elementary and is what is recorded here: a real number whose products with two
coprime positive integers are both integers is itself an integer.

This is the obstruction to building an element of the Selberg class as a fractional power product
`∏ Gᵢ^{cᵢ}` with non-integral exponents: unless the factors share zeros, each `cᵢ` must clear the
orders of all zeros of `Gᵢ`, so a factor with a simple zero — or with two zeros of coprime orders —
forces its exponent to be an integer.
-/

namespace HTGeometry

/-- **Coprime orders force an integral exponent.**  If `c * m` and `c * n` are integers for coprime
positive `m, n`, then `c` is an integer. -/
theorem exponent_int_of_coprime_orders {c : ℝ} {m n : ℕ} (hm : 0 < m)
    (hcop : Nat.Coprime m n) {a b : ℤ} (ha : c * m = a) (hb : c * n = b) :
    ∃ z : ℤ, c = z := by
  have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  have key : a * n = b * m := by
    have h1 : (a : ℝ) * n = b * m := by
      rw [← ha, ← hb]; ring
    exact_mod_cast h1
  have hdvd : (m : ℤ) ∣ a := by
    have h2 : (m : ℤ) ∣ a * n := ⟨b, by linarith [key]⟩
    have hcop' : IsCoprime (m : ℤ) (n : ℤ) := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      simpa using hcop
    exact (hcop'.dvd_of_dvd_mul_right h2)
  obtain ⟨k, hk⟩ := hdvd
  refine ⟨k, ?_⟩
  have : c * m = (k : ℝ) * m := by
    rw [ha, hk]; push_cast; ring
  exact mul_right_cancel₀ hmR this

/-- A simple zero already forces an integral exponent: `c * 1 ∈ ℤ` gives `c ∈ ℤ`. -/
theorem exponent_int_of_simple_zero {c : ℝ} {a : ℤ} (ha : c * 1 = a) : ∃ z : ℤ, c = z :=
  ⟨a, by simpa using ha⟩

end HTGeometry
