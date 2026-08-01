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
      convert! h using 1 <;> simp
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
