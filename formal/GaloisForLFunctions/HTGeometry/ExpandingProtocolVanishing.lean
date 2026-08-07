import Mathlib

/-!
# Degree laws under an expanding protocol

A protocol of rational maps of degree at least two composes to degree at least `2^n` after `n`
steps.  Two consequences are purely arithmetic, and both are steps of the orbifold classification
of nonautonomous tails.

* A compatible family of rational functions whose degrees satisfy `deg a_0 = deg P_n · deg a_n` at
  every depth must have `deg a_0 = 0`: there is no nonconstant order-zero tail.
* A family of zero multiplicities satisfying `deg P_n · Z_n ≤ Z_0` vanishes from some depth on:
  transient zeros of the tensor chain disappear.

Both are the statement that a fixed natural number cannot dominate `2^n` for every `n`.
-/

namespace GaloisForLFunctions.HTGeometry

/-- **No nonconstant order-zero tail.**  If the degree of `a 0` factors through a degree that grows
at least like `2^n`, it is zero. -/
theorem eq_zero_of_expanding_degree_law {a P : ℕ → ℕ} (hP : ∀ n, 2 ^ n ≤ P n)
    (hlaw : ∀ n, a 0 = P n * a n) : a 0 = 0 := by
  by_contra h0
  obtain ⟨n, hn⟩ : ∃ n : ℕ, a 0 < 2 ^ n := ⟨a 0, Nat.lt_two_pow_self⟩
  have han : a n ≠ 0 := by
    intro hz
    exact h0 (by rw [hlaw n, hz, mul_zero])
  have hge : 2 ^ n ≤ a 0 := by
    calc 2 ^ n = 2 ^ n * 1 := (mul_one _).symm
      _ ≤ P n * a n := Nat.mul_le_mul (hP n) (Nat.one_le_iff_ne_zero.mpr han)
      _ = a 0 := (hlaw n).symm
  omega

/-- **Transient zeros disappear.**  A multiplicity dominated by `2^n` times a later multiplicity
forces that later multiplicity to vanish from some depth on. -/
theorem eventually_eq_zero_of_expanding_bound {Z : ℕ → ℕ}
    (h : ∀ n : ℕ, 2 ^ n * Z n ≤ Z 0) : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Z n = 0 := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, Z 0 < 2 ^ N := ⟨Z 0, Nat.lt_two_pow_self⟩
  refine ⟨N, fun n hn => ?_⟩
  by_contra hz
  have h1 : 1 ≤ Z n := Nat.one_le_iff_ne_zero.mpr hz
  have h2 : 2 ^ N ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h3 : 2 ^ n ≤ 2 ^ n * Z n := Nat.le_mul_of_pos_right _ (by omega)
  have h4 := h n
  omega

/-- **Quantization of late cone weights.**  A weight that is negative, or positive without dividing
the tensor order, is confined to a finite exceptional support and therefore obeys
`deg(P)·|a| ≤ B`.  Once the prefix degree exceeds `B`, neither alternative is possible, so every
weight is zero or a positive divisor of the tensor order. -/
theorem weight_quantization {B l d : ℕ} {a : ℤ} (hd : B < d)
    (hneg : a < 0 → d * a.natAbs ≤ B)
    (hpos : 0 < a → ¬ (a.natAbs ∣ l) → d * a.natAbs ≤ B) :
    a = 0 ∨ (0 < a ∧ a.natAbs ∣ l) := by
  rcases lt_trichotomy a 0 with hlt | heq | hgt
  · exfalso
    have h1 : 1 ≤ a.natAbs := by omega
    have h2 := hneg hlt
    have h3 : d * 1 ≤ d * a.natAbs := Nat.mul_le_mul_left d h1
    omega
  · exact Or.inl heq
  · by_cases hdvd : a.natAbs ∣ l
    · exact Or.inr ⟨hgt, hdvd⟩
    · exfalso
      have h1 : 1 ≤ a.natAbs := by omega
      have h2 := hpos hgt hdvd
      have h3 : d * 1 ≤ d * a.natAbs := Nat.mul_le_mul_left d h1
      omega

/-! ### The Riemann–Hurwitz trapping bound -/

/-- **Three trapped fibres force a large exceptional set.**  Riemann–Hurwitz for three distinct
target fibres of a degree-`D` map gives `3D - (r₁+r₂+r₃) ≤ 2D - 2`; if those fibres are disjoint
subsets of the exceptional set, its cardinality is at least `D + 2`. -/
theorem le_card_of_riemannHurwitz {D r₁ r₂ r₃ B : ℤ}
    (hrh : 3 * D - (r₁ + r₂ + r₃) ≤ 2 * D - 2) (hsum : r₁ + r₂ + r₃ ≤ B) :
    D + 2 ≤ B := by linarith

/-- **At large degree no three fibres can be trapped.**  Once the degree exceeds the exceptional
budget, the previous bound is contradictory, so at most two exceptional worldlines survive. -/
theorem not_three_trapped_fibres {D r₁ r₂ r₃ B : ℤ} (hD : B < D + 2)
    (hrh : 3 * D - (r₁ + r₂ + r₃) ≤ 2 * D - 2) (hsum : r₁ + r₂ + r₃ ≤ B) : False := by
  linarith

end GaloisForLFunctions.HTGeometry
