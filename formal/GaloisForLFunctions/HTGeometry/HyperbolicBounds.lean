import GaloisForLFunctions.HTGeometry.TanhSubstitution

/-!
# Elementary hyperbolic bounds

Reusable exact and quadratic bounds for `sinh` and `cosh`.  They live in HTGeometry so analytic
and RHTower modules can share one proof without reversing dependency direction.
-/

open Real

namespace HTGeometry

noncomputable section

/-- `sinh²(u/2) = (cosh u - 1)/2`. -/
theorem sinh_half_sq (u : ℝ) :
    Real.sinh (u / 2) ^ 2 = (Real.cosh u - 1) / 2 := by
  have h := Real.cosh_two_mul (u / 2)
  have hs := Real.cosh_sq_sub_sinh_sq (u / 2)
  have e : 2 * (u / 2) = u := by ring
  rw [e] at h
  linarith

/-- `sinh x ≤ x cosh x` for `x ≥ 0`. -/
theorem sinh_le_self_mul_cosh {x : ℝ} (hx : 0 ≤ x) :
    Real.sinh x ≤ x * Real.cosh x := by
  have hmono : MonotoneOn (fun t : ℝ => t * Real.cosh t - Real.sinh t)
      (Set.Ici (0 : ℝ)) := by
    have hderiv : ∀ t : ℝ, HasDerivAt
        (fun t : ℝ => t * Real.cosh t - Real.sinh t) (t * Real.sinh t) t := by
      intro t
      have h := ((hasDerivAt_id t).mul (Real.hasDerivAt_cosh t)).sub
        (Real.hasDerivAt_sinh t)
      convert! h using 1
      simp
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop)
      (fun t _ => (hderiv t).differentiableAt.differentiableWithinAt) ?_
    intro t ht
    rw [interior_Ici] at ht
    rw [(hderiv t).deriv]
    have h1 : (0 : ℝ) ≤ t := ht.le
    have h2 : (0 : ℝ) ≤ Real.sinh t := Real.sinh_nonneg_iff.mpr h1
    positivity
  have h0 : (0 : ℝ) * Real.cosh 0 - Real.sinh 0 = 0 := by simp
  have h := hmono Set.self_mem_Ici hx hx
  simp only [h0] at h
  linarith

/-- Quadratic smallness: `cosh t - 1 ≤ (t²/2) cosh t` for `t ≥ 0`. -/
theorem cosh_sub_one_le {t : ℝ} (ht : 0 ≤ t) :
    Real.cosh t - 1 ≤ t ^ 2 / 2 * Real.cosh t := by
  have hs : Real.sinh (t / 2) ^ 2 = (Real.cosh t - 1) / 2 := sinh_half_sq t
  have hhalf : (0 : ℝ) ≤ t / 2 := by linarith
  have hb := sinh_le_self_mul_cosh hhalf
  have hsn : (0 : ℝ) ≤ Real.sinh (t / 2) := Real.sinh_nonneg_iff.mpr hhalf
  have hsq : Real.sinh (t / 2) ^ 2 ≤
      (t / 2) ^ 2 * Real.cosh (t / 2) ^ 2 := by
    have hcn : (0 : ℝ) ≤ (t / 2) * Real.cosh (t / 2) := by positivity
    nlinarith [hb, hsn, hcn]
  have hdouble : Real.cosh t = 2 * Real.cosh (t / 2) ^ 2 - 1 := by
    have h := Real.cosh_two_mul (t / 2)
    have hss := Real.cosh_sq_sub_sinh_sq (t / 2)
    have e : 2 * (t / 2) = t := by ring
    rw [e] at h
    linarith
  have hone : (1 : ℝ) ≤ Real.cosh (t / 2) ^ 2 := by
    have h := Real.one_le_cosh (t / 2)
    nlinarith
  nlinarith [hs, hsq, hdouble, hone]

end

end HTGeometry

namespace HTGeometry

noncomputable section

/-- `x ≤ sinh x` for `x ≥ 0`. -/
theorem self_le_sinh_of_nonneg {x : ℝ} (hx : 0 ≤ x) : x ≤ Real.sinh x := by
  have hderiv : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Real.sinh t - t) (Real.cosh t - 1) t := by
    intro t
    have h := (Real.hasDerivAt_sinh t).sub (hasDerivAt_id t)
    convert! h using 1
  have hmono : MonotoneOn (fun t : ℝ => Real.sinh t - t) (Set.Ici (0 : ℝ)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop)
      (fun t _ => (hderiv t).differentiableAt.differentiableWithinAt) ?_
    intro t ht
    rw [(hderiv t).deriv]
    linarith [Real.one_le_cosh t]
  have h := hmono Set.self_mem_Ici hx hx
  simp only [Real.sinh_zero, sub_zero] at h
  linarith

/-- `cosh x ≤ exp x` for `x ≥ 0`. -/
theorem cosh_le_exp_of_nonneg {x : ℝ} (hx : 0 ≤ x) : Real.cosh x ≤ Real.exp x := by
  rw [Real.cosh_eq]
  have h : Real.exp (-x) ≤ Real.exp x := Real.exp_le_exp.mpr (by linarith)
  linarith

/-- Even global bound: the centered cosh defect is dominated by `u sinh u`. -/
theorem two_cosh_sub_two_le_self_mul_sinh (u : ℝ) :
    2 * Real.cosh u - 2 ≤ u * Real.sinh u := by
  have haux : ∀ v : ℝ, 0 ≤ v → 2 * Real.cosh v - 2 ≤ v * Real.sinh v := by
    intro v hv
    have hhalf : (0 : ℝ) ≤ v / 2 := by linarith
    have hs : (0 : ℝ) ≤ Real.sinh (v / 2) := Real.sinh_nonneg_iff.mpr hhalf
    have hb : Real.sinh (v / 2) ≤ v / 2 * Real.cosh (v / 2) := sinh_le_self_mul_cosh hhalf
    have hsq : Real.sinh (v / 2) ^ 2 = (Real.cosh v - 1) / 2 := sinh_half_sq v
    have hdouble : Real.sinh v = 2 * Real.sinh (v / 2) * Real.cosh (v / 2) := by
      have h := Real.sinh_two_mul (v / 2)
      have e : 2 * (v / 2) = v := by ring
      rw [e] at h
      exact h
    nlinarith [mul_nonneg hs (sub_nonneg.mpr hb)]
  rcases le_total 0 u with hu | hu
  · exact haux u hu
  · have h := haux (-u) (by linarith)
    rw [Real.cosh_neg, Real.sinh_neg, neg_mul_neg] at h
    exact h

/-- Even window bound: on `|u| ≤ L`, `u sinh u ≤ exp (L/2) · (2 cosh u - 2)`. -/
theorem self_mul_sinh_le_exp_half_mul {u L : ℝ} (hL : |u| ≤ L) :
    u * Real.sinh u ≤ Real.exp (L / 2) * (2 * Real.cosh u - 2) := by
  have haux : ∀ v : ℝ, 0 ≤ v → v ≤ L →
      v * Real.sinh v ≤ Real.exp (L / 2) * (2 * Real.cosh v - 2) := by
    intro v hv hvL
    have hhalf : (0 : ℝ) ≤ v / 2 := by linarith
    have hs : (0 : ℝ) ≤ Real.sinh (v / 2) := Real.sinh_nonneg_iff.mpr hhalf
    have hself : v / 2 ≤ Real.sinh (v / 2) := self_le_sinh_of_nonneg hhalf
    have hcpos : (0 : ℝ) < Real.cosh (v / 2) := Real.cosh_pos _
    have hcoshE : Real.cosh (v / 2) ≤ Real.exp (L / 2) := by
      calc Real.cosh (v / 2) ≤ Real.exp (v / 2) := cosh_le_exp_of_nonneg hhalf
        _ ≤ Real.exp (L / 2) := Real.exp_le_exp.mpr (by linarith)
    have hsq : Real.sinh (v / 2) ^ 2 = (Real.cosh v - 1) / 2 := sinh_half_sq v
    have hdouble : Real.sinh v = 2 * Real.sinh (v / 2) * Real.cosh (v / 2) := by
      have h := Real.sinh_two_mul (v / 2)
      have e : 2 * (v / 2) = v := by ring
      rw [e] at h
      exact h
    have h2 : v * (Real.sinh (v / 2) * Real.cosh (v / 2)) ≤
        (2 * Real.sinh (v / 2)) * (Real.sinh (v / 2) * Real.cosh (v / 2)) :=
      mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hs hcpos.le)
    have h4 : (2 * Real.sinh (v / 2) ^ 2) * Real.cosh (v / 2) ≤
        (2 * Real.sinh (v / 2) ^ 2) * Real.exp (L / 2) :=
      mul_le_mul_of_nonneg_left hcoshE (by positivity)
    nlinarith [h2, h4]
  rcases le_total 0 u with hu | hu
  · exact haux u hu (le_of_abs_le hL)
  · rw [abs_of_nonpos hu] at hL
    have h := haux (-u) (by linarith) hL
    rw [Real.cosh_neg, Real.sinh_neg, neg_mul_neg] at h
    exact h

/-- rpow dictionary: `s^t - s^{-t} = 2 sinh (t log s)` for positive base. -/
theorem rpow_sub_rpow_neg_eq_two_sinh {s : ℝ} (hs : 0 < s) (t : ℝ) :
    s ^ t - s ^ (-t) = 2 * Real.sinh (t * Real.log s) := by
  rw [Real.rpow_def_of_pos hs t, Real.rpow_def_of_pos hs (-t), Real.sinh_eq,
    mul_comm (Real.log s) t, show Real.log s * -t = -(t * Real.log s) by ring]
  ring

/-- rpow dictionary: `s^t + s^{-t} - 2 = 2 cosh (t log s) - 2` for positive base. -/
theorem rpow_add_rpow_neg_sub_two_eq {s : ℝ} (hs : 0 < s) (t : ℝ) :
    s ^ t + s ^ (-t) - 2 = 2 * Real.cosh (t * Real.log s) - 2 := by
  rw [Real.rpow_def_of_pos hs t, Real.rpow_def_of_pos hs (-t), Real.cosh_eq,
    mul_comm (Real.log s) t, show Real.log s * -t = -(t * Real.log s) by ring]
  ring

/-- The centered cosh defect of a positive base is nonnegative. -/
theorem rpow_add_rpow_neg_sub_two_nonneg {s : ℝ} (hs : 0 < s) (t : ℝ) :
    0 ≤ s ^ t + s ^ (-t) - 2 := by
  rw [rpow_add_rpow_neg_sub_two_eq hs t]
  linarith [Real.one_le_cosh (t * Real.log s)]

/-- The centered cosh defect of a base `> 1` vanishes only at rate zero. -/
theorem rpow_add_rpow_neg_sub_two_eq_zero_iff {s : ℝ} (hs : 1 < s) (t : ℝ) :
    s ^ t + s ^ (-t) - 2 = 0 ↔ t = 0 := by
  have hs0 : (0 : ℝ) < s := lt_trans one_pos hs
  have hlog : 0 < Real.log s := Real.log_pos hs
  rw [rpow_add_rpow_neg_sub_two_eq hs0 t]
  constructor
  · intro h
    have hcosh : Real.cosh (t * Real.log s) = 1 := by linarith
    have hhalf : Real.sinh (t * Real.log s / 2) ^ 2 = 0 := by
      rw [sinh_half_sq, hcosh]
      norm_num
    have hzero : Real.sinh (t * Real.log s / 2) = 0 := sq_eq_zero_iff.mp hhalf
    have harg : t * Real.log s / 2 = 0 :=
      Real.sinh_strictMono.injective (by rw [Real.sinh_zero]; exact hzero)
    have hmul : t * Real.log s = 0 := by linarith
    rcases mul_eq_zero.mp hmul with h1 | h1
    · exact h1
    · exact absurd h1 hlog.ne'
  · rintro rfl
    simp

/-- The cosh defect is dominated by `(log s / 2)` times the odd-square mass shape
`t (s^t - s^{-t})`, at every rate. -/
theorem rpow_add_rpow_neg_sub_two_le_shape {s : ℝ} (hs : 1 < s) (t : ℝ) :
    s ^ t + s ^ (-t) - 2 ≤ Real.log s / 2 * (t * (s ^ t - s ^ (-t))) := by
  have hs0 : (0 : ℝ) < s := lt_trans one_pos hs
  rw [rpow_add_rpow_neg_sub_two_eq hs0 t, rpow_sub_rpow_neg_eq_two_sinh hs0 t]
  have h := two_cosh_sub_two_le_self_mul_sinh (t * Real.log s)
  nlinarith [h]

/-- On the window `|t| ≤ 1` the odd-square mass shape is dominated by
`2 s^{1/2} / log s` times the cosh defect. -/
theorem shape_le_rpow_defect {s : ℝ} (hs : 1 < s) {t : ℝ} (ht : |t| ≤ 1) :
    t * (s ^ t - s ^ (-t)) ≤
      2 * s ^ ((1 : ℝ) / 2) / Real.log s * (s ^ t + s ^ (-t) - 2) := by
  have hs0 : (0 : ℝ) < s := lt_trans one_pos hs
  have hlog : 0 < Real.log s := Real.log_pos hs
  rw [rpow_add_rpow_neg_sub_two_eq hs0 t, rpow_sub_rpow_neg_eq_two_sinh hs0 t]
  have hu : |t * Real.log s| ≤ Real.log s := by
    rw [abs_mul, abs_of_pos hlog]
    calc |t| * Real.log s ≤ 1 * Real.log s := mul_le_mul_of_nonneg_right ht hlog.le
      _ = Real.log s := one_mul _
  have h := self_mul_sinh_le_exp_half_mul hu
  have hsq : s ^ ((1 : ℝ) / 2) = Real.exp (Real.log s / 2) := by
    rw [Real.rpow_def_of_pos hs0]
    congr 1
    ring
  rw [hsq]
  have h2 := mul_le_mul_of_nonneg_left h
    (le_of_lt (show (0 : ℝ) < 2 / Real.log s by positivity))
  calc t * (2 * Real.sinh (t * Real.log s))
      = 2 / Real.log s * (t * Real.log s * Real.sinh (t * Real.log s)) := by
        field_simp
    _ ≤ 2 / Real.log s *
        (Real.exp (Real.log s / 2) * (2 * Real.cosh (t * Real.log s) - 2)) := h2
    _ = 2 * Real.exp (Real.log s / 2) / Real.log s *
        (2 * Real.cosh (t * Real.log s) - 2) := by
        ring

end

end HTGeometry
