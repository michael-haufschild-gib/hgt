import GaloisForLFunctions.RHTower.Sieve.CircleDistance

/-!
# Rationals are separated on the circle by their denominators

A rational with denominator `D` is either an integer or at distance at least `D^{-1}` from every
integer: writing `m/D - round(m/D) = (m - D·round(m/D))/D`, the numerator is an integer, and it
vanishes exactly when `D ∣ m`.

Applied to a difference `a/q - a'/q' = (aq' - a'q)/(qq')` this is the separation hypothesis a sieve
over rationals needs:

`‖a/q - a'/q'‖ ≥ (qq')^{-1} ≥ Q^{-2}`  for denominators at most `Q`,

whenever the two fractions are distinct modulo one.
-/

namespace RHTower.Sieve

open Finset

/-- **A non-integral rational is far from the integers.** -/
theorem one_div_le_toIntDist_of_not_dvd {D : ℕ} (hD : 0 < D) {m : ℤ} (h : ¬ ((D : ℤ) ∣ m)) :
    1 / (D : ℝ) ≤ toIntDist ((m : ℝ) / (D : ℝ)) := by
  have hDR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  set r : ℤ := round ((m : ℝ) / (D : ℝ)) with hr
  have hne : m - (D : ℤ) * r ≠ 0 := by
    intro hzero
    exact h ⟨r, by linarith⟩
  have h1 : (1 : ℤ) ≤ |m - (D : ℤ) * r| := Int.one_le_abs hne
  have h1R : (1 : ℝ) ≤ |((m - (D : ℤ) * r : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast h1
  have hval : (m : ℝ) / (D : ℝ) - (r : ℝ) = ((m - (D : ℤ) * r : ℤ) : ℝ) / (D : ℝ) := by
    push_cast
    field_simp
  rw [toIntDist, ← hr, hval, abs_div, abs_of_pos hDR]
  gcongr

/-- **Farey separation.**  Two rationals distinct modulo one are separated on the circle by the
reciprocal of the product of their denominators. -/
theorem one_div_le_toIntDist_farey {q q' : ℕ} (hq : 0 < q) (hq' : 0 < q') {a a' : ℤ}
    (h : ¬ (((q * q' : ℕ) : ℤ) ∣ (a * (q' : ℤ) - a' * (q : ℤ)))) :
    1 / ((q : ℝ) * (q' : ℝ)) ≤ toIntDist ((a : ℝ) / (q : ℝ) - (a' : ℝ) / (q' : ℝ)) := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hq'R : (0 : ℝ) < (q' : ℝ) := by exact_mod_cast hq'
  have hval : (a : ℝ) / (q : ℝ) - (a' : ℝ) / (q' : ℝ)
      = ((a * (q' : ℤ) - a' * (q : ℤ) : ℤ) : ℝ) / ((q : ℝ) * (q' : ℝ)) := by
    push_cast
    field_simp
  rw [hval]
  have hmain := one_div_le_toIntDist_of_not_dvd (D := q * q') (by positivity) h
  have hcast : (((q * q' : ℕ)) : ℝ) = (q : ℝ) * (q' : ℝ) := by push_cast; ring
  rw [hcast] at hmain
  exact hmain

end RHTower.Sieve
