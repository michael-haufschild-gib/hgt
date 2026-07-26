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

* `sinh_lt_mul_cosh` (in `CothInfra`) — `sinh x < x·cosh x` for `x > 0` (the atomic
  driver; `= tanh x < x`).
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
import GaloisForLFunctions.RHTower.CothInfra

open Real Set

namespace RHTower

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

/-- At the reversal source value `r = log (cosh m)`, the `c = 2` tanh inequality is
unconditional.  Clearing the positive hyperbolic denominators reduces it exactly to
`1 ≤ cosh m`. -/
theorem tanh_half_le_tanh_log_cosh_div_tanh
    {m : ℝ} (hm : 0 < m) :
    Real.tanh (m / 2) ≤
      Real.tanh (Real.log (Real.cosh m)) / Real.tanh m := by
  let C : ℝ := Real.cosh m
  let S : ℝ := Real.sinh m
  have hC : 1 < C := by
    dsimp [C]
    exact Real.one_lt_cosh.mpr hm.ne'
  have hCpos : 0 < C := lt_trans (by norm_num) hC
  have hSpos : 0 < S := by
    dsimp [S]
    exact Real.sinh_pos_iff.mpr hm
  have hhalfC : 0 < Real.cosh (m / 2) := Real.cosh_pos _
  have htanhHalf :
      Real.tanh (m / 2) = S / (C + 1) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    have hs := Real.sinh_two_mul (m / 2)
    have hc := Real.cosh_two_mul (m / 2)
    have hid := Real.cosh_sq_sub_sinh_sq (m / 2)
    rw [show 2 * (m / 2) = m by ring] at hs hc
    dsimp [S, C]
    rw [hs, hc]
    field_simp [hhalfC.ne']
    nlinarith
  have htanhLog :
      Real.tanh (Real.log C) = (C ^ 2 - 1) / (C ^ 2 + 1) := by
    rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_log hCpos,
      Real.cosh_log hCpos]
    field_simp [hCpos.ne']
  have htanhM : Real.tanh m = S / C := by
    rw [Real.tanh_eq_sinh_div_cosh]
  have hhyper : C ^ 2 - S ^ 2 = 1 := by
    dsimp [C, S]
    exact Real.cosh_sq_sub_sinh_sq m
  rw [htanhHalf, htanhLog, htanhM]
  have hden1 : 0 < C + 1 := by linarith
  have hden2 : 0 < C ^ 2 + 1 := by positivity
  have hSC : 0 < S / C := div_pos hSpos hCpos
  rw [div_div]
  apply (div_le_div_iff₀ hden1 (mul_pos hden2 hSC)).2
  field_simp [hCpos.ne', hSpos.ne']
  nlinarith

/-- **Unconditional reversal-positivity lift.**  The source relation
`r = log (cosh m)` supplies the formerly explicit base inequality, and monotonicity then
propagates it to every `c ≥ 2`. -/
theorem posC_log_cosh
    {m c : ℝ} (hm : 0 < m) (hc : 2 ≤ c) :
    Real.tanh (m / 2) ≤
      Real.tanh (c * (Real.log (Real.cosh m) / 2)) /
        Real.tanh (c * (m / 2)) := by
  have hcoshOne : 1 < Real.cosh m :=
    Real.one_lt_cosh.mpr hm.ne'
  have hcoshPos : 0 < Real.cosh m :=
    lt_trans (by norm_num) hcoshOne
  have hr : 0 < Real.log (Real.cosh m) :=
    Real.log_pos hcoshOne
  have hcoshExp : Real.cosh m < Real.exp m := by
    rw [Real.cosh_eq]
    have hneg : Real.exp (-m) < Real.exp m :=
      Real.exp_lt_exp.mpr (by linarith)
    nlinarith
  have hrm : Real.log (Real.cosh m) < m :=
    (Real.log_lt_iff_lt_exp hcoshPos).2 hcoshExp
  exact posC_of_posTwo hr hrm
    (tanh_half_le_tanh_log_cosh_div_tanh hm) hc

end RHTower
