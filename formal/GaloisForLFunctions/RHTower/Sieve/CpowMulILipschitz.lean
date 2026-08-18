import GaloisForLFunctions.RHTower.Sieve.PerronKernelIntegralForm
import GaloisForLFunctions.HTGeometry.HalfPlaneMellinRepresentation

/-!
# The unimodular power is Lipschitz to the right of its base point
-/

namespace RHTower.Sieve

open Complex

/-- **Lipschitz bound for `u ↦ u^{it}`.**  For `0 < x ≤ u`,
`‖u^{it} − x^{it}‖ ≤ |t|(u−x)/x`: the chord of the unit circle is at most the arc, whose length is
`|t|·log(u/x) ≤ |t|(u−x)/x`.  The chord step is mathlib's
`Real.norm_exp_I_mul_ofReal_sub_one_le`; the corpus's
`HTGeometry.TorsionPolygonRecurrenceShadowing.norm_exp_ofReal_mul_I_sub_le` is the same fact in
two-point form, but its import chain is too heavy for this lane. -/
theorem norm_cpow_mul_I_sub_le {x u t : ℝ} (hx : 0 < x) (hu : x ≤ u) :
    ‖((u : ℝ) : ℂ) ^ (((t : ℝ) : ℂ) * Complex.I)
        - ((x : ℝ) : ℂ) ^ (((t : ℝ) : ℂ) * Complex.I)‖
      ≤ |t| * (u - x) / x := by
  have hu0 : 0 < u := lt_of_lt_of_le hx hu
  have hcu := GaloisForLFunctions.HTGeometry.cpow_ofReal_mul_I hu0 t
  have hcx := GaloisForLFunctions.HTGeometry.cpow_ofReal_mul_I hx t
  rw [hcu, hcx]
  -- factor out the base phase
  have hfac : Complex.exp (((t : ℝ) : ℂ) * Complex.I * ((Real.log u : ℝ) : ℂ))
        - Complex.exp (((t : ℝ) : ℂ) * Complex.I * ((Real.log x : ℝ) : ℂ))
      = Complex.exp (((t : ℝ) : ℂ) * Complex.I * ((Real.log x : ℝ) : ℂ))
        * (Complex.exp (Complex.I * ((t * (Real.log u - Real.log x) : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [hfac, norm_mul]
  have hunit : ‖Complex.exp (((t : ℝ) : ℂ) * Complex.I * ((Real.log x : ℝ) : ℂ))‖ = 1 := by
    rw [show ((t : ℝ) : ℂ) * Complex.I * ((Real.log x : ℝ) : ℂ)
        = (((t * Real.log x : ℝ)) : ℂ) * Complex.I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  rw [hunit, one_mul]
  have hchord := Real.norm_exp_I_mul_ofReal_sub_one_le
    (x := t * (Real.log u - Real.log x))
  have hlog : Real.log u - Real.log x = Real.log (u / x) := (Real.log_div hu0.ne' hx.ne').symm
  have hlogle : Real.log (u / x) ≤ (u - x) / x := by
    have h1 : Real.log (u / x) ≤ u / x - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have h2 : u / x - 1 = (u - x) / x := by field_simp
    linarith [h1, h2]
  have hnn : (0 : ℝ) ≤ Real.log (u / x) := by
    refine Real.log_nonneg ?_
    rw [le_div_iff₀ hx]
    linarith
  have habs : ‖t * (Real.log u - Real.log x)‖ = |t| * Real.log (u / x) := by
    rw [Real.norm_eq_abs, abs_mul, hlog, abs_of_nonneg hnn]
  rw [habs] at hchord
  have hfin : |t| * Real.log (u / x) ≤ |t| * ((u - x) / x) :=
    mul_le_mul_of_nonneg_left hlogle (abs_nonneg t)
  have hval : |t| * ((u - x) / x) = |t| * (u - x) / x := by ring
  linarith [hchord, hfin, hval]

end RHTower.Sieve
