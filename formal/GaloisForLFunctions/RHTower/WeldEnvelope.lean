/-
# WeldEnvelope — the creation/survival weld (docs 50–52; census weld of doc 52 §10)

Formalizes the ALGEBRAIC STRUCTURE of the census weld: ONE modulus `M θ = |cos θ|`
carries BOTH the creation depth envelope and the survival dip-phase envelope, as
functions of the shared slip `slip p = 2π p²`, differing ONLY by the metaplectic
offset `π/8`:

    creation p = M (slip p),   survival p = M (slip p − π/8).

This is the structural skeleton. The EMPIRICAL identification — that the MEASURED
off-line birth depth tracks `creation` (peak at p = 0, no π/8) and the survival
window tracks `survival` (peak at p = ¼, with π/8) — is the labelled conjecture in
`docs/drafts/rh-monodromy-weight-mismatch/{50 §5, 51 §10, 52 §9–10}`, NOT claimed
here. What is PROVED:

* `weld` — both envelopes are the one modulus of the shared slip, shifted by `π/8`.
* `creation_zero = 1`, `survival_quarter = 1` — the peaks are displaced by exactly
  the metaplectic shift (creation at p = 0, survival at p = ¼ where slip = π/8).
* `survival_zero = creation_quarter = cos(π/8)` — at each other's peak the envelope
  is only `cos(π/8) < 1` (the peaks are genuinely separate).
* `creation_half = 0` vs `survival_half = sin(π/8)` — creation VANISHES at the
  half-integer (total suppression); survival stays finite.
* `survival_suppression : survival 0 / survival ½ = 1 + √2` — the census's measured
  "2.4× suppression" is EXACTLY `cot(π/8) = 1 + √2` (with `_sq` the rational form
  `3 + 2√2`). The metaplectic constant fixes the survival cap; the creation cap is
  a full zero.
-/
import Mathlib

namespace RHTower.Weld

open Real

/-- Shared second-order phase (the "slip", doc 51 §9a): `slip p = 2π p²`. -/
noncomputable def slip (p : ℝ) : ℝ := 2 * Real.pi * p ^ 2

/-- The single weld modulus `M θ = |cos θ|` carried by both envelopes. -/
noncomputable def M (θ : ℝ) : ℝ := |Real.cos θ|

/-- Creation depth envelope: the bare frozen-max modulus (offset 0). -/
noncomputable def creation (p : ℝ) : ℝ := M (slip p)

/-- Survival dip-phase envelope: the modulus shifted by the metaplectic `π/8`. -/
noncomputable def survival (p : ℝ) : ℝ := M (slip p - Real.pi / 8)

/-- **The weld.** Both envelopes are the SAME modulus of the shared slip, differing
by exactly the metaplectic offset `π/8`. -/
theorem weld (p : ℝ) :
    creation p = M (slip p) ∧ survival p = M (slip p - Real.pi / 8) := ⟨rfl, rfl⟩

theorem slip_zero : slip 0 = 0 := by simp [slip]
theorem slip_quarter : slip (1/4) = Real.pi / 8 := by unfold slip; ring
theorem slip_half : slip (1/2) = Real.pi / 2 := by unfold slip; ring

/-- `cos(π/8) ≥ 0` (reused at the peaks and in the suppression constant). -/
theorem cos_pi_div_eight_nonneg : 0 ≤ Real.cos (Real.pi / 8) := by
  apply Real.cos_nonneg_of_mem_Icc; constructor <;> nlinarith [Real.pi_pos]

/-- `sin(π/8) > 0` (the finite survival value at the half-integer). -/
theorem sin_pi_div_eight_pos : 0 < Real.sin (Real.pi / 8) := by
  apply Real.sin_pos_of_pos_of_lt_pi <;> [positivity; (nlinarith [Real.pi_pos])]

/-- Creation peaks (= 1) at `p = 0`. -/
theorem creation_zero : creation 0 = 1 := by
  unfold creation M; rw [slip_zero, Real.cos_zero, abs_one]

/-- Survival peaks (= 1) at `p = 1/4` (where slip = π/8): the peak is displaced from
creation's by exactly the metaplectic shift. -/
theorem survival_quarter : survival (1/4) = 1 := by
  unfold survival M; rw [slip_quarter, sub_self, Real.cos_zero, abs_one]

/-- At creation's peak, survival is only `cos(π/8) < 1`. -/
theorem survival_zero : survival 0 = Real.cos (Real.pi / 8) := by
  unfold survival M; rw [slip_zero, zero_sub, Real.cos_neg]
  exact abs_of_nonneg cos_pi_div_eight_nonneg

/-- At survival's peak, creation is only `cos(π/8) < 1`. -/
theorem creation_quarter : creation (1/4) = Real.cos (Real.pi / 8) := by
  unfold creation M; rw [slip_quarter]
  exact abs_of_nonneg cos_pi_div_eight_nonneg

/-- Creation VANISHES at `p = 1/2` (total suppression at the half-integer). -/
theorem creation_half : creation (1/2) = 0 := by
  unfold creation M; rw [slip_half, Real.cos_pi_div_two, abs_zero]

/-- Survival at `p = 1/2` is `sin(π/8)` (finite, unlike creation). -/
theorem survival_half : survival (1/2) = Real.sin (Real.pi / 8) := by
  unfold survival M; rw [slip_half, Real.cos_pi_div_two_sub]
  exact abs_of_nonneg (le_of_lt sin_pi_div_eight_pos)

/-- `cos²(π/8) = (2 + √2)/4` (half-angle). -/
theorem cos_sq_pi_div_eight : Real.cos (Real.pi / 8) ^ 2 = (2 + Real.sqrt 2) / 4 := by
  have h := Real.cos_two_mul (Real.pi / 8)
  rw [show 2 * (Real.pi / 8) = Real.pi / 4 by ring, Real.cos_pi_div_four] at h
  linarith

/-- `sin²(π/8) = (2 − √2)/4` (half-angle). -/
theorem sin_sq_pi_div_eight : Real.sin (Real.pi / 8) ^ 2 = (2 - Real.sqrt 2) / 4 := by
  have hp := Real.sin_sq_add_cos_sq (Real.pi / 8)
  rw [cos_sq_pi_div_eight] at hp; linarith

/-- **The exact suppression (rational form).** `(survival 0 / survival ½)² = 3 + 2√2`. -/
theorem survival_suppression_sq :
    (survival 0 / survival (1/2)) ^ 2 = 3 + 2 * Real.sqrt 2 := by
  rw [survival_zero, survival_half, div_pow, cos_sq_pi_div_eight, sin_sq_pi_div_eight]
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hlt : Real.sqrt 2 < 2 := by nlinarith [Real.sqrt_nonneg 2, h2]
  have hne : (2 - Real.sqrt 2) / 4 ≠ 0 := by
    have : (0:ℝ) < (2 - Real.sqrt 2) / 4 := by linarith
    exact ne_of_gt this
  rw [div_eq_iff hne]; nlinarith [h2]

/-- **The exact suppression.** `survival 0 / survival ½ = 1 + √2 = cot(π/8)` — the
census's measured "2.4×" is exactly `1 + √2`. -/
theorem survival_suppression :
    survival 0 / survival (1/2) = 1 + Real.sqrt 2 := by
  have hsq := survival_suppression_sq
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hrhs : (1 + Real.sqrt 2) ^ 2 = 3 + 2 * Real.sqrt 2 := by nlinarith [h2]
  have hx : 0 ≤ survival 0 / survival (1/2) := by
    rw [survival_zero, survival_half]
    exact div_nonneg cos_pi_div_eight_nonneg (le_of_lt sin_pi_div_eight_pos)
  have hy : (0:ℝ) ≤ 1 + Real.sqrt 2 := by positivity
  rw [← Real.sqrt_sq hx, hsq, ← hrhs, Real.sqrt_sq hy]

end RHTower.Weld
