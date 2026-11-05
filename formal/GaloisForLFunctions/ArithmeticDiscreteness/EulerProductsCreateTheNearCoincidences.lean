import GaloisForLFunctions.ArithmeticDiscreteness.ANearCoincidenceFlattensZeta
import GaloisForLFunctions.ArithmeticDiscreteness.TheRankOfTheFrequencyModuleDecidesRepulsion

/-!
# Euler products create the near-coincidences

Rank two does not by itself force near-coincidences. Compare two integral carriers over the primes
`2, 3`:

* the Euler product `(1 − 2^{−s})(1 − 3^{−s})` has distinct zeros at every positive distance
  (`twoPrime_no_uniform_repulsion`);
* the carrier `D(s) = 1 + 2^{−s} + 3^{−s}` repels uniformly (`trinomial_uniform_repulsion`):
  distinct zeros are at distance at least `min(1/4, (log 3 − log 2)/224)`.

Mechanism. Two close zeros of `D` force `D'` small at one of them
(`norm_deriv_mul_le_of_two_zeros`), i.e. `x = 2^{−s}, y = 3^{−s}` nearly solve the tangency system
`1 + x + y = 0`, `x log 2 + y log 3 = 0`. Its solution has `|x| > |y| > 1`
(`trinomial_tangency_gap`), which no point with `|x| = 2^{−σ}`, `|y| = 3^{−σ}` can have: for
`σ < 0`, `3^{−σ} > 2^{−σ}`, and for `σ ≥ 0`, `2^{−σ} ≤ 1`. The tangency of the Bohr lift is
inconsistent with the moduli, so the Kronecker flow never brings two zeros together. For the Euler
product the tangency point `x = y = 1` is consistent (`σ = 0`), and the flow approaches it.
-/

open Complex Metric

noncomputable section

namespace GaloisForLFunctions.ArithmeticDiscreteness

/-- The carrier `1 + 2^{−s} + 3^{−s}`. -/
def trinomial (s : ℂ) : ℂ := 1 + (2 : ℂ) ^ (-s) + (3 : ℂ) ^ (-s)

theorem norm_two_cpow_neg (s : ℂ) : ‖(2 : ℂ) ^ (-s)‖ = (2 : ℝ) ^ (-s.re) := by
  have := Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2) (-s)
  simpa using this

theorem norm_three_cpow_neg (s : ℂ) : ‖(3 : ℂ) ^ (-s)‖ = (3 : ℝ) ^ (-s.re) := by
  have := Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 3) (-s)
  simpa using this

theorem hasDerivAt_cpow_neg {c : ℂ} (hc : c ≠ 0) (s : ℂ) :
    HasDerivAt (fun z : ℂ => c ^ (-z)) (-(Complex.log c * c ^ (-s))) s := by
  have := (hasDerivAt_neg s).const_cpow (c := c) (Or.inl hc)
  rw [show c ^ (-s) * Complex.log c * -1 = -(Complex.log c * c ^ (-s)) by ring] at this
  exact this

theorem hasDerivAt_trinomial (s : ℂ) :
    HasDerivAt trinomial (-(Complex.log 2 * (2 : ℂ) ^ (-s) + Complex.log 3 * (3 : ℂ) ^ (-s))) s := by
  have h := ((hasDerivAt_const s (1 : ℂ)).add (hasDerivAt_cpow_neg two_ne_zero s)).add
    (hasDerivAt_cpow_neg three_ne_zero s)
  unfold trinomial
  exact h.congr_deriv (by ring)

/-- The zeros of the carrier lie in `Re s ≥ −1`: for `Re s < −1`, `3^{−σ} > 1 + 2^{−σ}`. -/
theorem neg_one_le_re_of_trinomial_eq_zero {s : ℂ} (hs : trinomial s = 0) : -1 ≤ s.re := by
  by_contra hlt
  push Not at hlt
  set u := -s.re with hu
  have hu1 : 1 < u := by linarith
  have hy : (3 : ℂ) ^ (-s) = -(1 + (2 : ℂ) ^ (-s)) := by
    unfold trinomial at hs; linear_combination hs
  have hle : (3 : ℝ) ^ u ≤ 1 + (2 : ℝ) ^ u := by
    have := congrArg norm hy
    rw [norm_neg, norm_three_cpow_neg] at this
    rw [hu, this]
    refine (norm_add_le _ _).trans ?_
    rw [norm_one, norm_two_cpow_neg]
  -- `3^u − 2^u ≥ 2^{u−1} > 1` for `u > 1`
  have h23 : (2 : ℝ) ^ (u - 1) ≤ (3 : ℝ) ^ (u - 1) :=
    Real.rpow_le_rpow (by norm_num) (by norm_num) (by linarith)
  have h3 : (3 : ℝ) ^ u = 3 * (3 : ℝ) ^ (u - 1) := by
    rw [← Real.rpow_one_add' (by norm_num) (by linarith)]; congr 1; ring
  have h2 : (2 : ℝ) ^ u = 2 * (2 : ℝ) ^ (u - 1) := by
    rw [← Real.rpow_one_add' (by norm_num) (by linarith)]; congr 1; ring
  have hgt : 1 < (2 : ℝ) ^ (u - 1) := Real.one_lt_rpow (by norm_num) (by linarith)
  linarith

/-- **The tangency of the Bohr lift is inconsistent.** At a zero of the carrier,
`‖x log 2 + y log 3‖ ≥ (log 3 − log 2)/2` for `x = 2^{−s}, y = 3^{−s}`. -/
theorem trinomial_tangency_gap {s : ℂ} (hs : trinomial s = 0) :
    (Real.log 3 - Real.log 2) / 2 ≤
      ‖Complex.log 2 * (2 : ℂ) ^ (-s) + Complex.log 3 * (3 : ℂ) ^ (-s)‖ := by
  set x := (2 : ℂ) ^ (-s) with hx
  set y := (3 : ℂ) ^ (-s) with hy
  set u := Complex.log 2 * x + Complex.log 3 * y with hu
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl32 : Real.log 2 < Real.log 3 := Real.log_lt_log (by norm_num) (by norm_num)
  set D := Real.log 3 - Real.log 2 with hD
  have hD0 : 0 < D := by linarith
  -- `3 log 2 > log 3`
  have h8 : Real.log 3 < 3 * Real.log 2 := by
    have : Real.log 3 < Real.log 8 := Real.log_lt_log (by norm_num) (by norm_num)
    rwa [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow, Nat.cast_ofNat] at this
  by_contra hsmall
  push Not at hsmall
  have hc2 : Complex.log 2 = ((Real.log 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_log (by norm_num)]; norm_num
  have hc3 : Complex.log 3 = ((Real.log 3 : ℝ) : ℂ) := by
    rw [Complex.ofReal_log (by norm_num)]; norm_num
  have hxy : y = -1 - x := by unfold trinomial at hs; rw [← hx, ← hy] at hs; linear_combination hs
  -- solve the tangency system: `x = −(u + log 3)/D`, `y = (u + log 2)/D`
  have hxsol : x = -(u + (Real.log 3 : ℂ)) / (D : ℂ) := by
    have hDc : (D : ℂ) ≠ 0 := by exact_mod_cast hD0.ne'
    rw [eq_div_iff hDc, hu, hxy, hc2, hc3, hD]; push_cast; ring
  have hysol : y = (u + (Real.log 2 : ℂ)) / (D : ℂ) := by
    have hDc : (D : ℂ) ≠ 0 := by exact_mod_cast hD0.ne'
    rw [eq_div_iff hDc, hu, hxy, hc2, hc3, hD]; push_cast; ring
  set b : ℝ := (Real.log 2 + D / 2) / D with hb
  have hb1 : 1 < b := by rw [hb, lt_div_iff₀ hD0, hD]; linarith
  have hxb : b ≤ ‖x‖ := by
    rw [hxsol, norm_div, norm_neg, norm_real, Real.norm_eq_abs, abs_of_pos hD0, hb]
    refine div_le_div_of_nonneg_right ?_ hD0.le
    have := norm_sub_norm_le ((Real.log 3 : ℂ)) (-u)
    rw [sub_neg_eq_add, add_comm, norm_neg, norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith : (0 : ℝ) < Real.log 3)] at this
    linarith
  have hyb : ‖y‖ ≤ b := by
    rw [hysol, norm_div, norm_real, Real.norm_eq_abs, abs_of_pos hD0, hb]
    refine div_le_div_of_nonneg_right ?_ hD0.le
    have := norm_add_le u ((Real.log 2 : ℂ))
    rw [norm_real, Real.norm_eq_abs, abs_of_pos hl2] at this
    linarith
  -- the moduli `2^{−σ}`, `3^{−σ}` cannot satisfy `‖x‖ ≥ b ≥ ‖y‖`, `b > 1`
  rw [hx, norm_two_cpow_neg] at hxb
  rw [hy, norm_three_cpow_neg] at hyb
  rcases le_or_gt 0 s.re with hσ | hσ
  · have : (2 : ℝ) ^ (-s.re) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    linarith
  · have : (2 : ℝ) ^ (-s.re) < (3 : ℝ) ^ (-s.re) :=
      Real.rpow_lt_rpow (by norm_num) (by norm_num) (by linarith)
    linarith

/-- **The trinomial carrier repels uniformly.** Distinct zeros of `1 + 2^{−s} + 3^{−s}` are at
distance at least `min(1/4, (log 3 − log 2)/224)`. -/
theorem trinomial_uniform_repulsion {s s' : ℂ} (hs : trinomial s = 0) (hs' : trinomial s' = 0)
    (hne : s' ≠ s) : min (1 / 4) ((Real.log 3 - Real.log 2) / 224) ≤ ‖s' - s‖ := by
  by_cases hfar : 1 / 4 < ‖s' - s‖
  · exact (min_le_left _ _).trans hfar.le
  push Not at hfar
  have hre := neg_one_le_re_of_trinomial_eq_zero hs
  have hdiffU : DifferentiableOn ℂ trinomial Set.univ := fun z _ =>
    (hasDerivAt_trinomial z).differentiableAt.differentiableWithinAt
  -- `|D| ≤ 14` on the unit disc around `s`
  have hM : ∀ z ∈ closedBall s 1, ‖trinomial z‖ ≤ 14 := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz
    have hzre : -2 ≤ z.re := by
      have := (abs_re_le_norm (z - s)).trans hz
      rw [sub_re] at this
      linarith [(abs_le.mp this).1]
    have h2 : (2 : ℝ) ^ (-z.re) ≤ 4 := by
      calc (2 : ℝ) ^ (-z.re) ≤ (2 : ℝ) ^ (2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 4 := by norm_num
    have h3 : (3 : ℝ) ^ (-z.re) ≤ 9 := by
      calc (3 : ℝ) ^ (-z.re) ≤ (3 : ℝ) ^ (2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 9 := by norm_num
    unfold trinomial
    calc ‖1 + (2 : ℂ) ^ (-z) + (3 : ℂ) ^ (-z)‖ ≤ ‖(1 : ℂ) + (2 : ℂ) ^ (-z)‖ + ‖(3 : ℂ) ^ (-z)‖ :=
          norm_add_le _ _
      _ ≤ ‖(1 : ℂ)‖ + ‖(2 : ℂ) ^ (-z)‖ + ‖(3 : ℂ) ^ (-z)‖ := by gcongr; exact norm_add_le _ _
      _ ≤ 14 := by rw [norm_one, norm_two_cpow_neg, norm_three_cpow_neg]; linarith
  have h := norm_deriv_mul_le_of_two_zeros isOpen_univ hdiffU (by norm_num : (0 : ℝ) < 1)
    (Set.subset_univ _) hM (by linarith : ‖s' - s‖ ≤ 1 / 4) hs hs'
  rw [(hasDerivAt_trinomial s).deriv, norm_neg] at h
  have hgap := trinomial_tangency_gap hs
  have hpos : 0 < ‖s' - s‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have h2 : (Real.log 3 - Real.log 2) / 2 * ‖s' - s‖ ≤ 112 * ‖s' - s‖ ^ 2 := by
    have := (mul_le_mul_of_nonneg_right hgap hpos.le).trans h
    linarith
  have h3 : (Real.log 3 - Real.log 2) / 2 ≤ 112 * ‖s' - s‖ := by
    rw [sq, ← mul_assoc] at h2
    exact le_of_mul_le_mul_right h2 hpos
  refine (min_le_right _ _).trans ?_
  linarith

end GaloisForLFunctions.ArithmeticDiscreteness
