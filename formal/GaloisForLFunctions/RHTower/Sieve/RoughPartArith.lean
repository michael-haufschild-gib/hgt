import GaloisForLFunctions.RHTower.Sieve.RoughDivBound

/-!
# Normalising the discarded part with explicit crude bounds

The closed form of the discarded part of the fibre mean square carries five quantities: the sieve
saving `L`, the Mertens correction `E`, the shift correction `c`, the Selberg remainder `R` and the
window length `h`.  Once `L ≤ 1`, `E ≤ 3` and `c ≥ 1/2` the normalised bound collapses to a sum of
four terms, each of which is manifestly small for the intended parameters.
-/

namespace RHTower.Sieve

open Finset

/-- **The diagonal term, crudely bounded.** -/
theorem roughPart_diag_le {h s L E R : ℝ} (hh1 : 1 ≤ h) (hs0 : 0 < s)
    (hL1 : L ≤ 1) (hE1 : 1 ≤ E) (hE3 : E ≤ 3) (hR0 : 0 ≤ R) :
    12 * (2 * (s + h) * L * E + R) / (h * s) ≤ 72 / h + 72 / s + 12 * R / s := by
  have hh0 : (0 : ℝ) < h := by linarith
  have hprod : (0 : ℝ) < h * s := by positivity
  rw [div_le_iff₀ hprod]
  have hrhs : (72 / h + 72 / s + 12 * R / s) * (h * s) = 72 * s + 72 * h + 12 * R * h := by
    field_simp
  rw [hrhs]
  have hLE : L * E ≤ 3 := by
    calc L * E ≤ 1 * E := mul_le_mul_of_nonneg_right hL1 (by linarith)
      _ = E := one_mul E
      _ ≤ 3 := hE3
  have hstep : 24 * (s + h) * (L * E) ≤ 24 * (s + h) * 3 :=
    mul_le_mul_of_nonneg_left hLE (by linarith)
  have hRh : (0 : ℝ) ≤ (12 * R) * (h - 1) :=
    mul_nonneg (by linarith) (by linarith)
  linarith [hstep, hRh]

/-- **The off-diagonal term, crudely bounded.** -/
theorem roughPart_offDiag_le {h s L E c R : ℝ} (hhs : h ≤ s) (hs0 : 0 < s)
    (hE1 : 1 ≤ E) (hE3 : E ≤ 3) (hc : 1 / 2 ≤ c) :
    12 * (2 * (s + h) * L ^ (2 : ℕ) * E ^ (2 : ℕ) / c + R) / s ≤ 864 * L ^ (2 : ℕ) + 12 * R / s := by
  have hc0 : (0 : ℝ) < c := by linarith
  have hL2 : (0 : ℝ) ≤ L ^ (2 : ℕ) := sq_nonneg L
  rw [div_le_iff₀ hs0]
  have hrhs : (864 * L ^ (2 : ℕ) + 12 * R / s) * s = 864 * L ^ (2 : ℕ) * s + 12 * R := by
    field_simp
  rw [hrhs]
  have hexp : 12 * (2 * (s + h) * L ^ (2 : ℕ) * E ^ (2 : ℕ) / c + R)
      = 24 * (s + h) * L ^ (2 : ℕ) * E ^ (2 : ℕ) / c + 12 * R := by
    rw [mul_add, mul_div_assoc']
    have hnum : 12 * (2 * (s + h) * L ^ (2 : ℕ) * E ^ (2 : ℕ)) = 24 * (s + h) * L ^ (2 : ℕ) * E ^ (2 : ℕ) := by ring
    rw [hnum]
  rw [hexp]
  have hE2 : E ^ (2 : ℕ) ≤ 9 := by nlinarith
  have hstepB : 24 * (s + h) * (L ^ (2 : ℕ) * E ^ (2 : ℕ)) ≤ 48 * s * (L ^ (2 : ℕ) * 9) := by
    refine mul_le_mul (by linarith) (mul_le_mul_of_nonneg_left hE2 hL2) (by positivity)
      (by linarith)
  have hlow : (432 : ℝ) * s * L ^ (2 : ℕ) ≤ 864 * L ^ (2 : ℕ) * s * c := by
    nlinarith [mul_nonneg (mul_nonneg hL2 hs0.le) (by linarith : (0:ℝ) ≤ c - 1 / 2)]
  have hkey : 24 * (s + h) * L ^ (2 : ℕ) * E ^ (2 : ℕ) / c ≤ 864 * L ^ (2 : ℕ) * s := by
    rw [div_le_iff₀ hc0]
    linarith [hstepB, hlow]
  linarith [hkey]

/-- **The normalised discarded part, with the corrections bounded crudely.** -/
theorem roughPart_div_le {h s Y L E c R S : ℝ}
    (hh1 : 1 ≤ h) (hhs : h ≤ s) (hs0 : 0 < s) (hY : Y = s + h)
    (hL0 : 0 ≤ L) (hL1 : L ≤ 1) (hE1 : 1 ≤ E) (hE3 : E ≤ 3) (hc : 1 / 2 ≤ c) (hR0 : 0 ≤ R)
    (hS : S ≤ (2 * h + 1)
      * (2 * ((2 * Y * L * E + R) + ((⌊h⌋₊ : ℕ) : ℝ) * (2 * Y * L ^ (2 : ℕ) * E ^ (2 : ℕ) / c + R)))) :
    (2 * S) / (h ^ (2 : ℕ) * s) ≤ 72 / h + 72 / s + 864 * L ^ (2 : ℕ) + 24 * R / s := by
  subst hY
  have hh0 : (0 : ℝ) < h := by linarith
  have hden : (0 : ℝ) < h ^ (2 : ℕ) * s := by positivity
  have hc0 : (0 : ℝ) < c := by linarith
  have hE0 : (0 : ℝ) < E := by linarith
  have hL2 : (0 : ℝ) ≤ L ^ (2 : ℕ) := sq_nonneg L
  set A : ℝ := 2 * (s + h) * L * E + R with hAdef
  set B : ℝ := 2 * (s + h) * L ^ (2 : ℕ) * E ^ (2 : ℕ) / c + R with hBdef
  have hA0 : (0 : ℝ) ≤ A := by
    have hpos : (0 : ℝ) ≤ 2 * (s + h) * L * E := by positivity
    rw [hAdef]
    linarith
  have hB0 : (0 : ℝ) ≤ B := by
    have hpos : (0 : ℝ) ≤ 2 * (s + h) * L ^ (2 : ℕ) * E ^ (2 : ℕ) / c := by positivity
    rw [hBdef]
    linarith
  have h1 : (2 * S) / (h ^ (2 : ℕ) * s)
      ≤ (2 * ((2 * h + 1) * (2 * (A + ((⌊h⌋₊ : ℕ) : ℝ) * B)))) / (h ^ (2 : ℕ) * s) :=
    (div_le_div_iff_of_pos_right hden).mpr (by linarith)
  have h2 := rough_div_bound (h := h) (s := s) hh1 hs0 hA0 hB0
  have h3 : (2 * ((2 * h + 1) * (2 * (A + ((⌊h⌋₊ : ℕ) : ℝ) * B)))) / (h ^ (2 : ℕ) * s)
      = 2 * (((2 * h + 1) * (2 * (A + ((⌊h⌋₊ : ℕ) : ℝ) * B))) / (h ^ (2 : ℕ) * s)) := by
    ring
  rw [h3] at h1
  have hdiag : 2 * (6 * A / (h * s)) ≤ 72 / h + 72 / s + 12 * R / s := by
    have hrw : 2 * (6 * A / (h * s)) = 12 * A / (h * s) := by ring
    rw [hrw, hAdef]
    exact roughPart_diag_le hh1 hs0 hL1 hE1 hE3 hR0
  have hoff : 2 * (6 * B / s) ≤ 864 * L ^ (2 : ℕ) + 12 * R / s := by
    have hrw : 2 * (6 * B / s) = 12 * B / s := by ring
    rw [hrw, hBdef]
    exact roughPart_offDiag_le hhs hs0 hE1 hE3 hc
  clear_value A B
  refine h1.trans ((by linarith [h2] :
    2 * (((2 * h + 1) * (2 * (A + ((⌊h⌋₊ : ℕ) : ℝ) * B))) / (h ^ (2 : ℕ) * s))
      ≤ 2 * (6 * A / (h * s) + 6 * B / s)).trans ?_)
  have hsplit : 2 * (6 * A / (h * s) + 6 * B / s) = 2 * (6 * A / (h * s)) + 2 * (6 * B / s) := by
    ring
  rw [hsplit]
  calc 2 * (6 * A / (h * s)) + 2 * (6 * B / s)
      ≤ (72 / h + 72 / s + 12 * R / s) + (864 * L ^ (2 : ℕ) + 12 * R / s) := add_le_add hdiag hoff
    _ = 72 / h + 72 / s + 864 * L ^ (2 : ℕ) + 24 * R / s := by ring

end RHTower.Sieve
