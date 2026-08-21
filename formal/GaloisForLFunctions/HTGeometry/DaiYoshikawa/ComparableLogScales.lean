import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Corollary 0.4: comparable power scales have comparable logarithms

Corollary 0.4 of Dai–Yoshikawa, *Degeneration of Riemann surfaces and small eigenvalues of the
Laplacian* (arXiv:2509.06151v2), restates Theorem 0.2 in terms of the length `l(s)` of a vanishing
cycle rather than the deformation parameter `s`.  The only input is that `l(s)` is trapped between
two powers of `|s|`,

```text
C' |s|^{ν'} ≤ l(s) ≤ C |s|^{ν} ,
```

from which `log l(s)^{-1}` and `log |s|^{-1}` differ by bounded factors and additive constants, so a
two-sided bound `K/log|s|^{-1} ≤ λ ≤ K'/log|s|^{-1}` becomes a two-sided bound in `log l(s)^{-1}`.

The logarithmic comparison is proved here.
-/

open Real

namespace GaloisForLFunctions.HTGeometry.DaiYoshikawa

/-- **Two-sided logarithmic comparison.**

If `A s^{ν'} ≤ l ≤ B s^{ν}` with everything positive, then
`ν log(1/s) − log B ≤ log(1/l) ≤ ν' log(1/s) − log A`. -/
theorem log_inv_le_and_le_of_rpow_bounds {A B ν ν' s l : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hs : 0 < s) (hl : 0 < l)
    (hlow : A * s ^ ν' ≤ l) (hhigh : l ≤ B * s ^ ν) :
    ν * Real.log (1 / s) - Real.log B ≤ Real.log (1 / l)
      ∧ Real.log (1 / l) ≤ ν' * Real.log (1 / s) - Real.log A := by
  have hsν : (0 : ℝ) < s ^ ν := Real.rpow_pos_of_pos hs ν
  have hsν' : (0 : ℝ) < s ^ ν' := Real.rpow_pos_of_pos hs ν'
  have hlogs : Real.log (1 / s) = -Real.log s := by rw [one_div, Real.log_inv]
  have hlogl : Real.log (1 / l) = -Real.log l := by rw [one_div, Real.log_inv]
  constructor
  · have h := Real.log_le_log hl hhigh
    rw [Real.log_mul (ne_of_gt hB) (ne_of_gt hsν), Real.log_rpow hs] at h
    rw [hlogl, hlogs]
    linarith
  · have h := Real.log_le_log (by positivity) hlow
    rw [Real.log_mul (ne_of_gt hA) (ne_of_gt hsν'), Real.log_rpow hs] at h
    rw [hlogl, hlogs]
    linarith

/-- **Corollary 0.4, transfer of an upper bound.**

If the two logarithmic scales satisfy `L ≤ ν' S + c` with `S ≥ 1` and `c ≥ 0` — which the previous
theorem supplies with `c` any nonnegative number at least `−log A` — then a bound `lam ≤ K/S`
becomes `lam ≤ K(ν'+c)/L`.  So a quantity comparable to `1/log|s|⁻¹` is comparable to
`1/log l(s)⁻¹`. -/
theorem le_div_of_le_mul_add {S L c ν' K lam : ℝ}
    (hK : 0 ≤ K) (hc : 0 ≤ c)
    (hS : 1 ≤ S) (hL : 0 < L)
    (hcomp : L ≤ ν' * S + c)
    (hlam : lam ≤ K / S) :
    lam ≤ K * (ν' + c) / L := by
  have hS0 : (0 : ℝ) < S := lt_of_lt_of_le zero_lt_one hS
  have hcS : c ≤ c * S := le_mul_of_one_le_right hc hS
  have hLS : L ≤ (ν' + c) * S := by nlinarith [hcomp, hcS]
  have hsum : 0 < ν' + c := by nlinarith [hL, hLS, hS0]
  have hstep : K / S ≤ K * (ν' + c) / L := by
    rw [div_le_div_iff₀ hS0 hL]
    nlinarith [mul_le_mul_of_nonneg_left hLS hK, hK, hS0]
  exact hlam.trans hstep

end GaloisForLFunctions.HTGeometry.DaiYoshikawa
