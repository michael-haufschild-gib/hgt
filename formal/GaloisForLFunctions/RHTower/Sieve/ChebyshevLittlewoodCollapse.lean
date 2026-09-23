import GaloisForLFunctions.RHTower.Sieve.ChebyshevFinalCollapse
import GaloisForLFunctions.RHTower.Sieve.ChebyshevLittlewoodPowers

/-!
# The final collapse at a general saving rate

`cheb_final_collapse` absorbs the factor `log Z = s²` into the saving `exp(-s/240000)`, leaving
`exp(-s/480000)` and the constant `4·480000²`.  Both numbers are the exponent-one rate `1/480000`
in disguise: the general statement is that a saving `exp(-2rs)` absorbs `s²` at the cost of
`4/r²`, since `s²·exp(-rs) ≤ 4/r²` for every `r > 0`.

At depth `A` the rate is `r = √A/4`, so the constant is `64/A` and the surviving saving is
`exp(-√A·s/4) = exp(-√(A log Z)/4)`.  The rate *improves* with depth, which is the point.
-/

namespace RHTower.Sieve

/-- `s²e^{-rs} ≤ 4/r²`: a quadratic is absorbed by any exponential saving. -/
theorem sq_mul_exp_neg_le_gen {r s : ℝ} (hr : 0 < r) (hs : 0 ≤ s) :
    s ^ (2 : ℕ) * Real.exp (-(r * s)) ≤ 4 / r ^ (2 : ℕ) := by
  have hhalf : (1 : ℝ) + r * s / 2 ≤ Real.exp (r * s / 2) := by
    have h := Real.add_one_le_exp (r * s / 2)
    linarith
  have hpos : (0 : ℝ) ≤ 1 + r * s / 2 := by positivity
  have hsplit : Real.exp (r * s) = Real.exp (r * s / 2) * Real.exp (r * s / 2) := by
    rw [← Real.exp_add]; ring_nf
  have hquad : (r * s) ^ (2 : ℕ) / 4 ≤ Real.exp (r * s) := by
    rw [hsplit]
    nlinarith [hhalf, hpos]
  have hexppos : (0 : ℝ) < Real.exp (r * s) := Real.exp_pos _
  have hneg : Real.exp (-(r * s)) = (Real.exp (r * s))⁻¹ := by
    rw [← Real.exp_neg]
  rw [hneg, mul_inv_le_iff₀ hexppos, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  nlinarith [hquad, hs, hr, sq_nonneg s, sq_nonneg r]

/-- **The final collapse at a general saving rate.**  The absorbed factor is an abstract `Q = s²`,
so the depth may sit inside it: at depth `A` the factor is `A log Z` and `s = √(A log Z)`.
`cheb_final_collapse` is the case `Q = log Z`, `r = 1/480000`. -/
theorem cheb_final_collapse_lw {Cr Cm Z s r Q Wb E : ℝ}
    (hCr : 0 ≤ Cr) (hCm : 0 ≤ Cm) (hZ0 : 0 ≤ Z) (hs : 0 ≤ s) (hr : 0 < r)
    (hQ : Q = s ^ (2 : ℕ))
    (hWbE : (1 + Wb) * E ≤ (3 + 27 * Cm) * Real.exp (-(2 * r * s))) :
    250000 * (1 + Cr) * (1 + Wb) * (4 * Q) * (Z * E)
      ≤ 250000 * (1 + Cr) * (3 + 27 * Cm) * (4 * (4 / r ^ (2 : ℕ))) * Z
          * Real.exp (-(r * s)) := by
  rw [hQ]
  have hA : (0 : ℝ) ≤ 250000 * (1 + Cr) * 4 * s ^ (2 : ℕ) * Z :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by norm_num))
      (sq_nonneg s)) hZ0
  have step1 : 250000 * (1 + Cr) * (1 + Wb) * (4 * s ^ (2 : ℕ)) * (Z * E)
      ≤ 250000 * (1 + Cr) * 4 * s ^ (2 : ℕ) * Z * ((3 + 27 * Cm) * Real.exp (-(2 * r * s))) := by
    have h := mul_le_mul_of_nonneg_left hWbE hA
    nlinarith [h]
  -- absorb the quadratic into half of the saving
  have habsorb : s ^ (2 : ℕ) * Real.exp (-(2 * r * s)) ≤ 4 / r ^ (2 : ℕ) * Real.exp (-(r * s)) := by
    have hkey := sq_mul_exp_neg_le_gen hr hs
    have hsplit : Real.exp (-(2 * r * s)) = Real.exp (-(r * s)) * Real.exp (-(r * s)) := by
      rw [← Real.exp_add]; ring_nf
    rw [hsplit]
    have hexppos : (0 : ℝ) < Real.exp (-(r * s)) := Real.exp_pos _
    nlinarith [hkey, hexppos]
  have hB : (0 : ℝ) ≤ 250000 * (1 + Cr) * (3 + 27 * Cm) * 4 * Z :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith))
      (by linarith)) (by norm_num)) hZ0
  have step2 := mul_le_mul_of_nonneg_left habsorb hB
  nlinarith [step1, step2]

end RHTower.Sieve
