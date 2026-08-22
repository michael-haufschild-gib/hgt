import Mathlib

/-!
# DQPT: the state-preparation error estimates

Supplementary Notes 4–5 of arXiv:2511.11199 (published Supplementary Notes 5–6) control four
error propagations in the quantum-state constructions.  These are the determinate mathematical
cores; the surrounding gate counts are resource estimates in an unspecified cost model.

Formalised items:
* `dqpt_chord_sq_eq`, `dqpt_chord_sq_le` — the chord identity
  `(cos a − cos b)² + (sin a − sin b)² = 4 sin²((a−b)/2) ≤ (a−b)²`;
* `dqpt_angle_perturbation` — **(4.13)**: a rotation-angle error at most `M` moves a normalised
  amplitude-split state by at most `M`;
* `dqpt_arctan_lipschitz`, `dqpt_normalized_pair_dist` — **(4.76)**: the LCU mixing-angle error
  bound (with the sharper constant `1` in place of the paper's `√2`);
* `dqpt_normalize_dist_le`, `dqpt_postselection_error`, `dqpt_postselection_prob` —
  **(4.86)–(4.91)**: post-selection error propagation;
* `dqpt_phase_error` — **(5.8)**: a phase error at most `ξ` moves a normalised state by at
  most `2 sin(ξ/2) ≤ ξ`.
-/

namespace RHTower.DQPT

open Filter Topology Set

noncomputable section

/-! ## The chord identity -/

theorem dqpt_chord_sq_eq (a b : ℝ) :
    (Real.cos a - Real.cos b) ^ 2 + (Real.sin a - Real.sin b) ^ 2
      = 4 * Real.sin ((a - b) / 2) ^ 2 := by
  have hcos : Real.cos (a - b) = Real.cos a * Real.cos b + Real.sin a * Real.sin b :=
    Real.cos_sub a b
  have hhalf : Real.cos (a - b) = 1 - 2 * Real.sin ((a - b) / 2) ^ 2 := by
    have h := Real.cos_two_mul' ((a - b) / 2)
    have hpy := Real.sin_sq_add_cos_sq ((a - b) / 2)
    have harg : 2 * ((a - b) / 2) = a - b := by ring
    rw [harg] at h
    linarith
  have hpa := Real.sin_sq_add_cos_sq a
  have hpb := Real.sin_sq_add_cos_sq b
  nlinarith [hcos, hhalf, hpa, hpb]

theorem dqpt_chord_sq_le (a b : ℝ) :
    (Real.cos a - Real.cos b) ^ 2 + (Real.sin a - Real.sin b) ^ 2 ≤ (a - b) ^ 2 := by
  rw [dqpt_chord_sq_eq]
  have h := Real.abs_sin_le_abs (x := (a - b) / 2)
  have habs : |(a - b) / 2| = |a - b| / 2 := by
    rw [abs_div]
    norm_num
  rw [habs] at h
  have hsq : Real.sin ((a - b) / 2) ^ 2 ≤ (|a - b| / 2) ^ 2 := by
    have h0 : (0 : ℝ) ≤ |a - b| / 2 := by positivity
    nlinarith [h, abs_nonneg (Real.sin ((a - b) / 2)), sq_abs (Real.sin ((a - b) / 2))]
  have hab : (|a - b| / 2) ^ 2 = (a - b) ^ 2 / 4 := by
    rw [div_pow, sq_abs]
    norm_num
  rw [hab] at hsq
  linarith

/-! ## Supplementary Note 4 (4.13): the amplitude-split angle error -/

/-- **(4.13).**  With normalised weights `∑ c_w² = 1`, replacing every rotation angle `θ_w` by
`θ'_w` moves the split state by at most `maxᵂ |θ'_w − θ_w|` in squared norm. -/
theorem dqpt_angle_perturbation {ι : Type*} [Fintype ι] (c θ θ' : ι → ℝ)
    (hnorm : ∑ w, c w ^ 2 = 1) {M : ℝ} (hM : ∀ w, |θ' w - θ w| ≤ M) :
    ∑ w, c w ^ 2 * ((Real.cos (θ' w) - Real.cos (θ w)) ^ 2
        + (Real.sin (θ' w) - Real.sin (θ w)) ^ 2) ≤ M ^ 2 := by
  have hstep : ∀ w : ι, c w ^ 2 * ((Real.cos (θ' w) - Real.cos (θ w)) ^ 2
      + (Real.sin (θ' w) - Real.sin (θ w)) ^ 2) ≤ c w ^ 2 * M ^ 2 := by
    intro w
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    refine (dqpt_chord_sq_le (θ' w) (θ w)).trans ?_
    have h := hM w
    nlinarith [h, abs_nonneg (θ' w - θ w), sq_abs (θ' w - θ w)]
  calc ∑ w, c w ^ 2 * ((Real.cos (θ' w) - Real.cos (θ w)) ^ 2
          + (Real.sin (θ' w) - Real.sin (θ w)) ^ 2)
      ≤ ∑ w, c w ^ 2 * M ^ 2 := Finset.sum_le_sum (fun w _ => hstep w)
    _ = M ^ 2 := by rw [← Finset.sum_mul, hnorm, one_mul]

/-! ## Supplementary Note 4 (4.76): the LCU mixing angle -/

/-- The arctangent is `1`-Lipschitz. -/
theorem dqpt_arctan_lipschitz (x y : ℝ) : |Real.arctan x - Real.arctan y| ≤ |x - y| := by
  rcases le_total x y with hxy | hxy
  · have hderiv : ∀ z ∈ Icc x y, HasDerivWithinAt Real.arctan (1 / (1 + z ^ 2)) (Icc x y) z :=
      fun z _ => (Real.hasDerivAt_arctan z).hasDerivWithinAt
    have hbound : ∀ z ∈ Ico x y, ‖1 / (1 + z ^ 2)‖ ≤ 1 := by
      intro z _
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      rw [div_le_one (by positivity)]
      nlinarith [sq_nonneg z]
    have key := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound y
      (right_mem_Icc.2 hxy)
    rw [Real.norm_eq_abs] at key
    calc |Real.arctan x - Real.arctan y| = |Real.arctan y - Real.arctan x| := abs_sub_comm _ _
      _ ≤ 1 * (y - x) := key
      _ = -(x - y) := by ring
      _ = |x - y| := (abs_of_nonpos (by linarith : x - y ≤ 0)).symm
  · have hderiv : ∀ z ∈ Icc y x, HasDerivWithinAt Real.arctan (1 / (1 + z ^ 2)) (Icc y x) z :=
      fun z _ => (Real.hasDerivAt_arctan z).hasDerivWithinAt
    have hbound : ∀ z ∈ Ico y x, ‖1 / (1 + z ^ 2)‖ ≤ 1 := by
      intro z _
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      rw [div_le_one (by positivity)]
      nlinarith [sq_nonneg z]
    have key := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound x
      (right_mem_Icc.2 hxy)
    rw [Real.norm_eq_abs] at key
    calc |Real.arctan x - Real.arctan y| ≤ 1 * (x - y) := key
      _ = x - y := by ring
      _ = |x - y| := (abs_of_nonneg (by linarith : (0 : ℝ) ≤ x - y)).symm

/-- **(4.76).**  The two normalised mixing vectors `(1, γ)/√(1+γ²)` differ by at most `|γ − γ'|`
— sharper than the paper's `√2 |γ − γ'|`. -/
theorem dqpt_normalized_pair_dist (γ γ' : ℝ) :
    (1 / Real.sqrt (1 + γ ^ 2) - 1 / Real.sqrt (1 + γ' ^ 2)) ^ 2
        + (γ / Real.sqrt (1 + γ ^ 2) - γ' / Real.sqrt (1 + γ' ^ 2)) ^ 2
      ≤ (γ - γ') ^ 2 := by
  have hc : Real.cos (Real.arctan γ) = 1 / Real.sqrt (1 + γ ^ 2) := Real.cos_arctan γ
  have hc' : Real.cos (Real.arctan γ') = 1 / Real.sqrt (1 + γ' ^ 2) := Real.cos_arctan γ'
  have hs : Real.sin (Real.arctan γ) = γ / Real.sqrt (1 + γ ^ 2) := Real.sin_arctan γ
  have hs' : Real.sin (Real.arctan γ') = γ' / Real.sqrt (1 + γ' ^ 2) := Real.sin_arctan γ'
  rw [← hc, ← hc', ← hs, ← hs']
  refine (dqpt_chord_sq_le (Real.arctan γ) (Real.arctan γ')).trans ?_
  have hlip := dqpt_arctan_lipschitz γ γ'
  nlinarith [hlip, abs_nonneg (Real.arctan γ - Real.arctan γ'), abs_nonneg (γ - γ'),
    sq_abs (Real.arctan γ - Real.arctan γ'), sq_abs (γ - γ')]

/-! ## Supplementary Note 4 (4.86)–(4.91): post-selection -/

/-- Normalisation is Lipschitz away from the origin: `‖x/‖x‖ − y/‖y‖‖ ≤ 2‖x−y‖/‖x‖`. -/
theorem dqpt_normalize_dist_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x y : E} (hx : x ≠ 0) (hy : y ≠ 0) :
    ‖(‖x‖)⁻¹ • x - (‖y‖)⁻¹ • y‖ ≤ 2 * ‖x - y‖ / ‖x‖ := by
  have hxn : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx
  have hyn : (0 : ℝ) < ‖y‖ := norm_pos_iff.mpr hy
  have hdecomp : (‖x‖)⁻¹ • x - (‖y‖)⁻¹ • y
      = (‖x‖)⁻¹ • (x - y) + ((‖x‖)⁻¹ - (‖y‖)⁻¹) • y := by
    rw [smul_sub, sub_smul]
    abel
  have hterm2 : ‖((‖x‖)⁻¹ - (‖y‖)⁻¹) • y‖ ≤ ‖x - y‖ / ‖x‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    have hval : ((‖x‖)⁻¹ - (‖y‖)⁻¹) = (‖y‖ - ‖x‖) / (‖x‖ * ‖y‖) := by
      field_simp
    rw [hval, abs_div, abs_of_pos (by positivity : (0 : ℝ) < ‖x‖ * ‖y‖)]
    have hnum : |‖y‖ - ‖x‖| ≤ ‖x - y‖ := by
      rw [abs_sub_comm]
      exact abs_norm_sub_norm_le x y
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hxn]
    have : |‖y‖ - ‖x‖| * ‖y‖ * ‖x‖ ≤ ‖x - y‖ * ‖y‖ * ‖x‖ := by
      have h1 : |‖y‖ - ‖x‖| * ‖y‖ ≤ ‖x - y‖ * ‖y‖ :=
        mul_le_mul_of_nonneg_right hnum (le_of_lt hyn)
      nlinarith [h1, hxn]
    nlinarith [this]
  have hterm1 : ‖(‖x‖)⁻¹ • (x - y)‖ = ‖x - y‖ / ‖x‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hxn), inv_mul_eq_div]
  rw [hdecomp]
  refine (norm_add_le _ _).trans ?_
  rw [hterm1]
  have : ‖x - y‖ / ‖x‖ + ‖x - y‖ / ‖x‖ = 2 * ‖x - y‖ / ‖x‖ := by ring
  linarith [hterm2, this]

/-- **(4.86)–(4.90).**  Post-selection error propagation. -/
theorem dqpt_postselection_error {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x y : E} {ε : ℝ} (hε : 0 ≤ ε) (hx : Real.sqrt 2 / 2 ≤ ‖x‖) (hxy : ‖x - y‖ ≤ ε / 6)
    (hy : y ≠ 0) :
    ‖(‖x‖)⁻¹ • x - (‖y‖)⁻¹ • y‖ ≤ ε := by
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hxn : (0 : ℝ) < ‖x‖ := lt_of_lt_of_le (by positivity) hx
  have hx0 : x ≠ 0 := norm_pos_iff.mp hxn
  refine (dqpt_normalize_dist_le hx0 hy).trans ?_
  rw [div_le_iff₀ hxn]
  have hnum : 2 * ‖x - y‖ ≤ 2 * (ε / 6) := by linarith
  have hlow : Real.sqrt 2 / 2 * ε ≤ ‖x‖ * ε := mul_le_mul_of_nonneg_right hx hε
  have hs2ge : (1 : ℝ) ≤ Real.sqrt 2 := by nlinarith [hs2, hs2sq]
  nlinarith [hnum, hlow, hs2ge, hε]

/-- **(4.91).**  The post-selection success probability is at least `1/2 − ε/3`. -/
theorem dqpt_postselection_prob {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x y : E} {ε : ℝ} (hε : 0 ≤ ε) (hx : (1 : ℝ) / 2 ≤ ‖x‖ ^ 2) (hx1 : ‖x‖ ≤ 1)
    (hxy : ‖x - y‖ ≤ ε / 6) :
    (1 : ℝ) / 2 - ε / 3 ≤ ‖y‖ ^ 2 := by
  have hxn : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
  have hyn : (0 : ℝ) ≤ ‖y‖ := norm_nonneg y
  have hdiff : ‖x‖ - ‖y‖ ≤ ε / 6 := le_trans (norm_sub_norm_le x y) hxy
  have hge : ‖x‖ - ε / 6 ≤ ‖y‖ := by linarith
  rcases le_total (‖x‖ - ε / 6) 0 with h | h
  · nlinarith [hyn, hx, hxn, hε]
  · nlinarith [hge, h, hx, hx1, hε]

/-! ## Supplementary Note 5 (5.8): the phase error -/

theorem dqpt_norm_sq_eq_re_im (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  simp only [Complex.norm_def, Complex.normSq_apply]
  rw [Real.sq_sqrt (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _))]
  ring

theorem dqpt_exp_neg_I_mul (t : ℝ) :
    Complex.exp (-Complex.I * (t : ℂ))
      = ((Real.cos t : ℝ) : ℂ) - ((Real.sin t : ℝ) : ℂ) * Complex.I := by
  have h : (-Complex.I * (t : ℂ)) = ((-t : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [h, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg,
    Real.sin_neg]
  push_cast
  ring

theorem dqpt_norm_sq_exp_sub_exp (a b : ℝ) :
    ‖Complex.exp (-Complex.I * (a : ℂ)) - Complex.exp (-Complex.I * (b : ℂ))‖ ^ 2
      = 4 * Real.sin ((a - b) / 2) ^ 2 := by
  rw [dqpt_exp_neg_I_mul a, dqpt_exp_neg_I_mul b, dqpt_norm_sq_eq_re_im]
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  have hchord := dqpt_chord_sq_eq a b
  nlinarith [hchord]

/-- **(5.8).**  A phase error at most `ξ` moves a normalised superposition by at most `ξ`. -/
theorem dqpt_phase_error {ι : Type*} [Fintype ι] (α : ι → ℂ) (a a' : ι → ℝ)
    (hnorm : ∑ w, ‖α w‖ ^ 2 = 1) {ξ : ℝ} (hξ : ∀ w, |a' w - a w| ≤ ξ) :
    ∑ w, ‖α w‖ ^ 2 * ‖Complex.exp (-Complex.I * ((a' w : ℝ) : ℂ))
        - Complex.exp (-Complex.I * ((a w : ℝ) : ℂ))‖ ^ 2 ≤ ξ ^ 2 := by
  have hstep : ∀ w : ι, ‖α w‖ ^ 2 * ‖Complex.exp (-Complex.I * ((a' w : ℝ) : ℂ))
      - Complex.exp (-Complex.I * ((a w : ℝ) : ℂ))‖ ^ 2 ≤ ‖α w‖ ^ 2 * ξ ^ 2 := by
    intro w
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    rw [dqpt_norm_sq_exp_sub_exp]
    have habs : |Real.sin ((a' w - a w) / 2)| ≤ |a' w - a w| / 2 := by
      have h := Real.abs_sin_le_abs (x := (a' w - a w) / 2)
      rw [abs_div] at h
      simpa using h
    have h3 := hξ w
    nlinarith [habs, h3, abs_nonneg (Real.sin ((a' w - a w) / 2)), abs_nonneg (a' w - a w),
      sq_abs (Real.sin ((a' w - a w) / 2)), sq_abs (a' w - a w)]
  calc ∑ w, ‖α w‖ ^ 2 * ‖Complex.exp (-Complex.I * ((a' w : ℝ) : ℂ))
          - Complex.exp (-Complex.I * ((a w : ℝ) : ℂ))‖ ^ 2
      ≤ ∑ w, ‖α w‖ ^ 2 * ξ ^ 2 := Finset.sum_le_sum (fun w _ => hstep w)
    _ = ξ ^ 2 := by rw [← Finset.sum_mul, hnorm, one_mul]

end

end RHTower.DQPT
