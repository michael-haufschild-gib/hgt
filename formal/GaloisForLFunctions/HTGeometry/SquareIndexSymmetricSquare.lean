import Mathlib

/-!
# Even-index coefficients of a degree-two local factor

A local factor of degree two is `((1 - a X)(1 - b X))⁻¹`, whose coefficients are the complete
homogeneous symmetric functions `h_n(a,b) = ∑_{i+j=n} a^i b^j`.  Selecting the even indices produces
the local factor of the symmetric square, corrected by the determinant `ab`:

```text
h_{2k}(a,b) = h_k(a², b²) + a b · h_{k-1}(a², b²) ,
```

equivalently, as generating functions,

```text
∑_k h_{2k}(a,b) X^k = (1 + a b X) / ((1 - a² X)(1 - b² X)) .
```

The first display is proved here by induction, over an arbitrary commutative ring, using only the
recurrence `h_{n+1}(x,y) = x^{n+1} + y · h_n(x,y)`.  The generating-function form is recorded as the
rational identity `(1 + aX)(1 + bX) + (1 - aX)(1 - bX) = 2(1 + abX²)` together with
`(1 - aX)(1 + aX) = 1 - a²X²`, which is what turns the even part of a degree-two local factor into a
degree-three one.
-/

namespace HTGeometry

variable {R : Type*} [CommRing R]

/-- The complete homogeneous symmetric function of degree `n` in two variables. -/
def hSym (x y : R) (n : ℕ) : R := ∑ i ∈ Finset.range (n + 1), x ^ i * y ^ (n - i)

@[simp] theorem hSym_zero (x y : R) : hSym x y 0 = 1 := by
  simp [hSym]

/-- The defining recurrence: peeling off the top power of `x`. -/
theorem hSym_succ (x y : R) (n : ℕ) : hSym x y (n + 1) = x ^ (n + 1) + y * hSym x y n := by
  unfold hSym
  rw [Finset.sum_range_succ, Finset.mul_sum]
  have hcong : ∀ i ∈ Finset.range (n + 1),
      x ^ i * y ^ (n + 1 - i) = y * (x ^ i * y ^ (n - i)) := by
    intro i hi
    have hle : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hsub : n + 1 - i = (n - i) + 1 := by omega
    rw [hsub, pow_succ]
    ring
  rw [Finset.sum_congr rfl hcong]
  simp [add_comm]

/-- **Even-index selection.**  The even-index complete homogeneous symmetric functions of `(a,b)` are
those of `(a², b²)`, corrected by the determinant `a b`. -/
theorem hSym_two_mul (a b : R) : ∀ k : ℕ,
    hSym a b (2 * k + 2) = hSym (a ^ 2) (b ^ 2) (k + 1) + a * b * hSym (a ^ 2) (b ^ 2) k
  | 0 => by
    simp [hSym, Finset.sum_range_succ]
    ring
  | (k + 1) => by
    have ih := hSym_two_mul a b k
    have hL : hSym a b (2 * (k + 1) + 2) =
        a ^ (2 * k + 4) + b * a ^ (2 * k + 3) + b ^ 2 * hSym a b (2 * k + 2) := by
      have h1 : 2 * (k + 1) + 2 = (2 * k + 2) + 1 + 1 := by ring
      rw [h1, hSym_succ, hSym_succ]
      ring
    have hS : hSym (a ^ 2) (b ^ 2) (k + 2) = (a ^ 2) ^ (k + 2) + b ^ 2 * hSym (a ^ 2) (b ^ 2) (k + 1) :=
      hSym_succ _ _ _
    have hS' : hSym (a ^ 2) (b ^ 2) (k + 1) = (a ^ 2) ^ (k + 1) + b ^ 2 * hSym (a ^ 2) (b ^ 2) k :=
      hSym_succ _ _ _
    have hp1 : (a ^ 2) ^ (k + 2) = a ^ (2 * k + 4) := by
      rw [← pow_mul]; ring_nf
    have hp2 : (a ^ 2) ^ (k + 1) = a ^ (2 * k + 2) := by
      rw [← pow_mul]; ring_nf
    have hp3 : b * a ^ (2 * k + 3) = a * b * a ^ (2 * k + 2) := by ring
    rw [show 2 * (k + 1) + 2 = 2 * (k + 1) + 2 from rfl, hL, ih, hS, hS', hp1, hp2, hp3]
    ring

/-- **Generating-function form.**  Averaging the local factor at `X` and at `-X` selects the even
part, and the numerator of the result is `1 + a b X²`. -/
theorem evenPart_numerator (a b X : R) :
    (1 + a * X) * (1 + b * X) + (1 - a * X) * (1 - b * X) = 2 * (1 + a * b * X ^ 2) := by
  ring

/-- The denominator of the even part factors through the squared roots. -/
theorem evenPart_denominator (a X : R) : (1 - a * X) * (1 + a * X) = 1 - a ^ 2 * X ^ 2 := by
  ring

/-- **Newton's relation at a degree-two local factor.**  The determinant is recovered from the first
two coefficients: `a b = h_1² - h_2`. -/
theorem det_eq_hSym_sq_sub (a b : R) : a * b = hSym a b 1 ^ 2 - hSym a b 2 := by
  simp [hSym, Finset.sum_range_succ]
  ring

end HTGeometry
