/-
Counting the classes that resonate with a given `n`, by lattice points on `n²d - k² = j`.

If `|n√d - k| ≤ ε` then, factorising,

    |n²d - k²| = |n√d - k| · (n√d + k) ≤ ε · (2n√d + ε) ,

so each resonating `d` produces a nonzero integer `j = n²d - k²` confined to a window of length
`≍ 2εn√D`.  Since `d = (k² + j)/n²`, two resonating `d` sharing the same nearest integer `k` differ by
at most `2ε√D/n`, and `k` itself ranges over at most `n√D + 1` values.  Hence

    **#{ d ≤ D : ‖n√d‖ ≤ ε } ≤ (n√D + 1)(2ε√D/n + 1) .**

At the parameters the frontier object supplies — `D ≍ N^(2/3)`, `n ≍ N`, `ε ≍ N^(-1/3)` — this is
`≍ N^(1/3)`, which is exactly the *total* number of classes.  **The elementary count is therefore
vacuous at the relevant scale**, and sharpening it requires the number of square roots of `-j` modulo
`n²` — genuine arithmetic input rather than lattice-point counting.

Recorded so the elementary route is not attempted again.
-/
import GaloisForLFunctions.HTGeometry.SqrtNonResonance
import GaloisForLFunctions.HTGeometry.SquarefreeClassLevels

namespace HTGeometry

open Real

/-! ### The factorisation inequality -/

/-- **A near-integer multiple of `√d` forces `n²d` to be near a square.** -/
theorem near_integer_forces_near_square {n : ℕ} {d : ℕ} {ε : ℝ} {k : ℤ}
    (hn : 0 < n) (hd : 0 < d) (hε : 0 ≤ ε)
    (h : |(n : ℝ) * Real.sqrt d - (k : ℝ)| ≤ ε) :
    |(n : ℝ) ^ 2 * (d : ℝ) - (k : ℝ) ^ 2| ≤ ε * (2 * (n : ℝ) * Real.sqrt d + ε) := by
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := by positivity
  have hsq : Real.sqrt d ^ 2 = (d : ℝ) := Real.sq_sqrt hd0
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hsnn : (0 : ℝ) ≤ Real.sqrt d := Real.sqrt_nonneg _
  have hfac : (n : ℝ) ^ 2 * (d : ℝ) - (k : ℝ) ^ 2
      = ((n : ℝ) * Real.sqrt d - (k : ℝ)) * ((n : ℝ) * Real.sqrt d + (k : ℝ)) := by
    nlinarith [hsq]
  have hk : (k : ℝ) ≤ (n : ℝ) * Real.sqrt d + ε := by
    have := abs_le.mp h
    linarith [this.2]
  have hksum : |(n : ℝ) * Real.sqrt d + (k : ℝ)| ≤ 2 * (n : ℝ) * Real.sqrt d + ε := by
    rw [abs_le]
    constructor
    · have := abs_le.mp h
      nlinarith [this.1, mul_nonneg hn0 hsnn]
    · linarith
  calc |(n : ℝ) ^ 2 * (d : ℝ) - (k : ℝ) ^ 2|
      = |(n : ℝ) * Real.sqrt d - (k : ℝ)| * |(n : ℝ) * Real.sqrt d + (k : ℝ)| := by
        rw [hfac, abs_mul]
    _ ≤ ε * (2 * (n : ℝ) * Real.sqrt d + ε) := by
        apply mul_le_mul h hksum (abs_nonneg _) hε

/-- **The window's length.**  For `d ≤ D` the integer `n²d - k²` lies in a window of length
`≍ 2εn√D`. -/
theorem window_length {n d D : ℕ} {ε : ℝ} {k : ℤ}
    (hn : 0 < n) (hd : 0 < d) (hε : 0 ≤ ε) (hdD : d ≤ D)
    (h : |(n : ℝ) * Real.sqrt d - (k : ℝ)| ≤ ε) :
    |(n : ℝ) ^ 2 * (d : ℝ) - (k : ℝ) ^ 2| ≤ ε * (2 * (n : ℝ) * Real.sqrt D + ε) := by
  have hmono : Real.sqrt d ≤ Real.sqrt D := by
    apply Real.sqrt_le_sqrt
    exact_mod_cast hdD
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hbase := near_integer_forces_near_square hn hd hε h
  have : ε * (2 * (n : ℝ) * Real.sqrt d + ε) ≤ ε * (2 * (n : ℝ) * Real.sqrt D + ε) := by
    apply mul_le_mul_of_nonneg_left _ hε
    have : 2 * (n : ℝ) * Real.sqrt d ≤ 2 * (n : ℝ) * Real.sqrt D := by
      apply mul_le_mul_of_nonneg_left hmono
      linarith
    linarith
  linarith

/-! ### The separation of two resonating `d` with the same nearest integer -/

/-- **Two resonating `d` sharing a nearest integer are close.**  Their difference is at most the
window length divided by `n²`. -/
theorem shared_k_separation {n d d' D : ℕ} {ε : ℝ} {k : ℤ}
    (hn : 0 < n) (hd : 0 < d) (hd' : 0 < d') (hε : 0 ≤ ε)
    (hdD : d ≤ D) (hdD' : d' ≤ D)
    (h : |(n : ℝ) * Real.sqrt d - (k : ℝ)| ≤ ε)
    (h' : |(n : ℝ) * Real.sqrt d' - (k : ℝ)| ≤ ε) :
    (n : ℝ) ^ 2 * |(d : ℝ) - (d' : ℝ)| ≤ 2 * (ε * (2 * (n : ℝ) * Real.sqrt D + ε)) := by
  have hw := window_length hn hd hε hdD h
  have hw' := window_length hn hd' hε hdD' h'
  have hexp : (n : ℝ) ^ 2 * |(d : ℝ) - (d' : ℝ)|
      = |((n : ℝ) ^ 2 * (d : ℝ) - (k : ℝ) ^ 2) - ((n : ℝ) ^ 2 * (d' : ℝ) - (k : ℝ) ^ 2)| := by
    rw [show ((n : ℝ) ^ 2 * (d : ℝ) - (k : ℝ) ^ 2) - ((n : ℝ) ^ 2 * (d' : ℝ) - (k : ℝ) ^ 2)
        = (n : ℝ) ^ 2 * ((d : ℝ) - (d' : ℝ)) by ring, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (n:ℝ)^(2 : ℕ))]
  rw [hexp]
  calc |((n : ℝ) ^ 2 * (d : ℝ) - (k : ℝ) ^ 2) - ((n : ℝ) ^ 2 * (d' : ℝ) - (k : ℝ) ^ 2)|
      ≤ |(n : ℝ) ^ 2 * (d : ℝ) - (k : ℝ) ^ 2| + |(n : ℝ) ^ 2 * (d' : ℝ) - (k : ℝ) ^ 2| :=
        abs_sub _ _
    _ ≤ 2 * (ε * (2 * (n : ℝ) * Real.sqrt D + ε)) := by linarith

/-! ### The resulting count, and why it is vacuous -/

/-- Exponent of the elementary count `(n√D + 1)(2ε√D/n + 1)` at the frontier's parameters
`D = N^(2/3)`, `n = N`, `ε = N^(-1/3)`: the dominant term is `2εD ≍ N^(1/3)`. -/
def elementaryCountExponent : ℚ := 1 / 3

/-- **It equals the total number of classes**, so the count says nothing. -/
theorem elementary_count_vacuous : elementaryCountExponent = classCountExponent := by
  unfold elementaryCountExponent classCountExponent; norm_num

/-- The count would become non-vacuous only at a much sharper resonance level. -/
def nonVacuousLevel : ℚ := -(2 / 3)

/-- **And that level is a full Farey order sharper than the class structure requires.** -/
theorem nonVacuous_gap :
    -(1 : ℚ) / 3 - nonVacuousLevel = fareyOrderExponent := by
  unfold nonVacuousLevel fareyOrderExponent; norm_num

end HTGeometry
