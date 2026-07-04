/-
# ReversalPositivity — the `(POS₂) → (POS_c)` lift of Lemma P (doc 41 §1; task #143)

`LedgerReversalConstants` banks the `c = 2` base point of the reversal positivity Lemma P
(`posTwo_algebraic_criterion`: `(POS₂) ⟺ cosh m ≥ 1`) and flags one analytic step as still open
on the Lean side:

> the `(POS₂) → (POS_c)` lift for all `c ≥ 2` needs `sinh x < x·cosh x` (the `y/sinh(cy)`
> monotonicity) — a multi-derivative analysis lemma left to the #143 stack.

This file closes exactly that gap. Doc 41 §1's monotonicity argument is:
`∂_c log[tanh(cr/2)·coth(cm/2)] = r/sinh(cr) − m/sinh(cm) ≥ 0`, because `y ↦ y/sinh(cy)` is strictly
decreasing on `(0,∞)` (its derivative has the sign of `sinh(cy) − cy·cosh(cy) < 0`, i.e.
`tanh(cy) < cy`) and `r < m`. Hence `c ↦ tanh(cr/2)·coth(cm/2)` is nondecreasing, so `(POS_c)` for
all `c ≥ 2` follows from `(POS₂)`.

The three bricks, all Mathlib-absent and reusable:

* `sinh_lt_mul_cosh` — `sinh x < x·cosh x` for `x > 0` (the atomic driver; `= tanh x < x`).
  Proof: `x·cosh x − sinh x` has derivative `x·sinh x > 0` and value `0` at `0`.
* `div_sinh_strictAntiOn` — `y ↦ y/sinh y` is strictly decreasing on `(0,∞)`
  (its derivative `(sinh y − y·cosh y)/sinh²y` is negative by the first brick).
* `tanh_div_tanh_monotoneOn` — for `0 < a < b`, `c ↦ tanh(ca)/tanh(cb)` is monotone on `(0,∞)`.
  Proof: the log surrogate `Φ(c) = log sinh(ca) − log cosh(ca) − log sinh(cb) + log cosh(cb)` has
  derivative `a/(sinh(ca)cosh(ca)) − b/(sinh(cb)cosh(cb)) > 0`, the sign coming from the second
  brick applied at `2ca < 2cb` (`sinh(2u) = 2 sinh u cosh u`); `exp ∘ Φ` recovers the ratio.

Capstone:

* `posC_of_posTwo` — given the `c = 2` base `tanh(m/2) ≤ tanh r / tanh m` (the tanh form of
  `(POS₂)`, `r = log cosh m`), the lift `tanh(m/2) ≤ tanh(c·r/2)/tanh(c·m/2)` holds for every
  `c ≥ 2`. Instantiate `a = r/2, b = m/2` in the monotone lemma and compose at `c = 2`.
-/
import Mathlib

open Real Set

namespace RHTower

/-- **(A)** `sinh x < x·cosh x` for `x > 0` — equivalently `tanh x < x`, the atomic driver of
Lemma P's monotonicity. `t·cosh t − sinh t` is `0` at `0` and strictly increasing on `[0,∞)`
(derivative `t·sinh t > 0`). -/
theorem sinh_lt_mul_cosh {x : ℝ} (hx : 0 < x) : Real.sinh x < x * Real.cosh x := by
  have key : StrictMonoOn (fun t : ℝ => t * Real.cosh t - Real.sinh t) (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    · exact Continuous.continuousOn (by fun_prop)
    · intro t ht
      rw [interior_Ici] at ht
      have htp : (0:ℝ) < t := ht
      have hderiv : HasDerivAt (fun t : ℝ => t * Real.cosh t - Real.sinh t)
          (t * Real.sinh t) t := by
        have h1 : HasDerivAt (fun t : ℝ => t * Real.cosh t)
            (1 * Real.cosh t + t * Real.sinh t) t :=
          (hasDerivAt_id t).mul (Real.hasDerivAt_cosh t)
        have h2 := h1.sub (Real.hasDerivAt_sinh t)
        convert h2 using 1
        ring
      rw [hderiv.deriv]
      exact mul_pos htp (Real.sinh_pos_iff.mpr htp)
  have h := key (self_mem_Ici) (mem_Ici.mpr hx.le) hx
  simp only [Real.cosh_zero, Real.sinh_zero, mul_one, sub_zero] at h
  linarith

/-- **(B)** `y ↦ y/sinh y` is strictly decreasing on `(0,∞)`. Its derivative
`(sinh y − y·cosh y)/sinh²y` is negative by `sinh_lt_mul_cosh`. -/
theorem div_sinh_strictAntiOn :
    StrictAntiOn (fun y : ℝ => y / Real.sinh y) (Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
  · apply ContinuousOn.div (continuous_id.continuousOn) (Real.continuous_sinh.continuousOn)
    intro y hy
    exact ne_of_gt (Real.sinh_pos_iff.mpr hy)
  · intro y hy
    rw [interior_Ioi] at hy
    have hyp : (0:ℝ) < y := hy
    have hsp : 0 < Real.sinh y := Real.sinh_pos_iff.mpr hyp
    have hderiv : HasDerivAt (fun y : ℝ => y / Real.sinh y)
        ((1 * Real.sinh y - y * Real.cosh y) / (Real.sinh y)^2) y :=
      (hasDerivAt_id y).div (Real.hasDerivAt_sinh y) (ne_of_gt hsp)
    rw [hderiv.deriv]
    have hnum : 1 * Real.sinh y - y * Real.cosh y < 0 := by
      have := sinh_lt_mul_cosh hyp
      linarith
    have hden : 0 < (Real.sinh y)^2 := by positivity
    exact div_neg_of_neg_of_pos hnum hden

/-- **(C)** For `0 < a < b`, the ratio `c ↦ tanh(ca)/tanh(cb)` is monotone on `(0,∞)`.
Its log `Φ(c) = log sinh(ca) − log cosh(ca) − log sinh(cb) + log cosh(cb)` has positive
derivative `a/(sinh(ca)cosh(ca)) − b/(sinh(cb)cosh(cb))`, the sign supplied by
`div_sinh_strictAntiOn` at `2ca < 2cb`. -/
theorem tanh_div_tanh_monotoneOn {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    MonotoneOn (fun c : ℝ => Real.tanh (c*a) / Real.tanh (c*b)) (Ioi 0) := by
  have hb : 0 < b := ha.trans hab
  have hderiv : ∀ c ∈ Ioi (0:ℝ),
      HasDerivAt (fun c : ℝ => Real.log (Real.sinh (c*a)) - Real.log (Real.cosh (c*a))
          - Real.log (Real.sinh (c*b)) + Real.log (Real.cosh (c*b)))
        (Real.cosh (c*a)*a/Real.sinh (c*a) - Real.sinh (c*a)*a/Real.cosh (c*a)
          - Real.cosh (c*b)*b/Real.sinh (c*b) + Real.sinh (c*b)*b/Real.cosh (c*b)) c := by
    intro c hc
    have hcp : (0:ℝ) < c := hc
    have hca : (0:ℝ) < c*a := mul_pos hcp ha
    have hcb : (0:ℝ) < c*b := mul_pos hcp hb
    have hsa : Real.sinh (c*a) ≠ 0 := ne_of_gt (Real.sinh_pos_iff.mpr hca)
    have hsb : Real.sinh (c*b) ≠ 0 := ne_of_gt (Real.sinh_pos_iff.mpr hcb)
    have hcca : Real.cosh (c*a) ≠ 0 := ne_of_gt (Real.cosh_pos _)
    have hccb : Real.cosh (c*b) ≠ 0 := ne_of_gt (Real.cosh_pos _)
    have hlin_a : HasDerivAt (fun c : ℝ => c*a) a c := by
      simpa using (hasDerivAt_id c).mul_const a
    have hlin_b : HasDerivAt (fun c : ℝ => c*b) b c := by
      simpa using (hasDerivAt_id c).mul_const b
    have d1 := (hlin_a.sinh).log hsa
    have d2 := (hlin_a.cosh).log hcca
    have d3 := (hlin_b.sinh).log hsb
    have d4 := (hlin_b.cosh).log hccb
    exact (((d1.sub d2).sub d3).add d4)
  have hΦmono : StrictMonoOn (fun c : ℝ => Real.log (Real.sinh (c*a)) - Real.log (Real.cosh (c*a))
          - Real.log (Real.sinh (c*b)) + Real.log (Real.cosh (c*b))) (Ioi 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
    · exact fun x hx => ((hderiv x hx).continuousAt).continuousWithinAt
    · intro c hc
      rw [interior_Ioi] at hc
      have hcp : (0:ℝ) < c := hc
      have hca : (0:ℝ) < c*a := mul_pos hcp ha
      have hcb : (0:ℝ) < c*b := mul_pos hcp hb
      have hsa0 : 0 < Real.sinh (c*a) := Real.sinh_pos_iff.mpr hca
      have hsb0 : 0 < Real.sinh (c*b) := Real.sinh_pos_iff.mpr hcb
      have hCa0 : 0 < Real.cosh (c*a) := Real.cosh_pos _
      have hCb0 : 0 < Real.cosh (c*b) := Real.cosh_pos _
      rw [(hderiv c hc).deriv]
      have hA : Real.cosh (c*a)*a/Real.sinh (c*a) - Real.sinh (c*a)*a/Real.cosh (c*a)
            = a/(Real.sinh (c*a)*Real.cosh (c*a)) := by
        rw [div_sub_div _ _ hsa0.ne' hCa0.ne']
        congr 1
        linear_combination a * Real.cosh_sq_sub_sinh_sq (c*a)
      have hB : Real.cosh (c*b)*b/Real.sinh (c*b) - Real.sinh (c*b)*b/Real.cosh (c*b)
            = b/(Real.sinh (c*b)*Real.cosh (c*b)) := by
        rw [div_sub_div _ _ hsb0.ne' hCb0.ne']
        congr 1
        linear_combination b * Real.cosh_sq_sub_sinh_sq (c*b)
      have hgroup : Real.cosh (c*a)*a/Real.sinh (c*a) - Real.sinh (c*a)*a/Real.cosh (c*a)
              - Real.cosh (c*b)*b/Real.sinh (c*b) + Real.sinh (c*b)*b/Real.cosh (c*b)
            = (Real.cosh (c*a)*a/Real.sinh (c*a) - Real.sinh (c*a)*a/Real.cosh (c*a))
              - (Real.cosh (c*b)*b/Real.sinh (c*b) - Real.sinh (c*b)*b/Real.cosh (c*b)) := by
        ring
      rw [hgroup, hA, hB]
      have hkey : b*(Real.sinh (c*a)*Real.cosh (c*a)) < a*(Real.sinh (c*b)*Real.cosh (c*b)) := by
        have hlt : (2*(c*b))/Real.sinh (2*(c*b)) < (2*(c*a))/Real.sinh (2*(c*a)) :=
          div_sinh_strictAntiOn (mem_Ioi.mpr (by positivity)) (mem_Ioi.mpr (by positivity))
            (by nlinarith [hab, hcp])
        rw [Real.sinh_two_mul, Real.sinh_two_mul,
            div_lt_div_iff₀ (by positivity) (by positivity)] at hlt
        nlinarith [hlt, hcp]
      rw [sub_pos, div_lt_div_iff₀ (by positivity) (by positivity)]
      exact hkey
  have hΦlog : ∀ c ∈ Ioi (0:ℝ),
      Real.exp (Real.log (Real.sinh (c*a)) - Real.log (Real.cosh (c*a))
        - Real.log (Real.sinh (c*b)) + Real.log (Real.cosh (c*b)))
        = Real.tanh (c*a) / Real.tanh (c*b) := by
    intro c hc
    have hcp : (0:ℝ) < c := hc
    have hca : (0:ℝ) < c*a := mul_pos hcp ha
    have hcb : (0:ℝ) < c*b := mul_pos hcp hb
    have hsa0 : 0 < Real.sinh (c*a) := Real.sinh_pos_iff.mpr hca
    have hsb0 : 0 < Real.sinh (c*b) := Real.sinh_pos_iff.mpr hcb
    have hCa0 : 0 < Real.cosh (c*a) := Real.cosh_pos _
    have hCb0 : 0 < Real.cosh (c*b) := Real.cosh_pos _
    rw [show Real.log (Real.sinh (c*a)) - Real.log (Real.cosh (c*a))
          - Real.log (Real.sinh (c*b)) + Real.log (Real.cosh (c*b))
        = (Real.log (Real.sinh (c*a)) - Real.log (Real.cosh (c*a)))
          - (Real.log (Real.sinh (c*b)) - Real.log (Real.cosh (c*b))) from by ring,
        Real.exp_sub, Real.exp_sub, Real.exp_sub,
        Real.exp_log hsa0, Real.exp_log hCa0, Real.exp_log hsb0, Real.exp_log hCb0,
        Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh]
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hxy with h | h
  · rw [h]
  · have hΦxy := hΦmono hx hy h
    simp only [] at hΦxy
    have hex := hΦlog x hx
    have hey := hΦlog y hy
    have hlt := Real.exp_lt_exp.mpr hΦxy
    rw [hex, hey] at hlt
    exact hlt.le

/-- **The `(POS₂) → (POS_c)` lift (doc 41 §1; task #143).** Given the `c = 2` base
`tanh(m/2) ≤ tanh r / tanh m` (the tanh form of `(POS₂)`, `r = log cosh m`), the positivity
criterion `tanh(c·r/2) / tanh(c·m/2) ≥ tanh(m/2)` holds for every `c ≥ 2`. This is the one
analytic step doc 41 §5(a) flagged as still open on the Lean side; the base itself is
`LedgerReversalConstants.posTwo_algebraic_criterion`. -/
theorem posC_of_posTwo {r m : ℝ} (hr : 0 < r) (hrm : r < m)
    (hbase : Real.tanh (m/2) ≤ Real.tanh r / Real.tanh m)
    {c : ℝ} (hc : 2 ≤ c) :
    Real.tanh (m/2) ≤ Real.tanh (c*(r/2)) / Real.tanh (c*(m/2)) := by
  have ha : 0 < r/2 := by linarith
  have hab : r/2 < m/2 := by linarith
  have hmono := tanh_div_tanh_monotoneOn ha hab
  have h2 : (2:ℝ) ∈ Ioi (0:ℝ) := by norm_num
  have hcIoi : c ∈ Ioi (0:ℝ) := mem_Ioi.mpr (by linarith)
  have hFmono := hmono h2 hcIoi hc
  simp only [] at hFmono
  rw [show (2:ℝ)*(r/2) = r from by ring, show (2:ℝ)*(m/2) = m from by ring] at hFmono
  exact le_trans hbase hFmono

end RHTower
