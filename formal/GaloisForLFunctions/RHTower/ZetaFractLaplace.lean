import GaloisForLFunctions.RHTower.FractionalPartZeta

/-!
# The Laplace representation of zeta through the fractional part

Substituting `t = e^x` in the Mellin integral of the fractional part turns it into a Laplace
integral on the half-line:

`∫_0^∞ {e^x} e^{-s x} dx = 1/(s-1) - ζ(s)/s`,     `0 < Re s`,  `s ≠ 1`.

This is the representation on which Putnam's non-periodicity argument rests: the integrand is a
bounded function of `x` with downward jumps exactly at `x = log m`, and its Laplace transform
carries the zeta values.
-/

open Complex Real MeasureTheory Set

noncomputable section

namespace RHTower

theorem image_Ioi_zero_exp : Real.exp '' Set.Ioi (0 : ℝ) = Set.Ioi (1 : ℝ) := by
  ext y
  simp only [Set.mem_image, Set.mem_Ioi]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using Real.exp_lt_exp.mpr hx
  · intro hy
    exact ⟨Real.log y, Real.log_pos hy, Real.exp_log (by linarith)⟩

theorem cpow_ofReal_exp (x : ℝ) (w : ℂ) :
    ((Real.exp x : ℝ) : ℂ) ^ w = Complex.exp (w * (x : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt (Real.exp_pos x))]
  congr 1
  rw [mul_comm]
  congr 1
  rw [← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp]

/-- **The Laplace representation.**  Substituting `t = e^x` in the Mellin integral of the fractional
part gives `∫_0^∞ {e^x} e^{-s x} dx = 1/(s-1) - ζ(s)/s`. -/
theorem integral_Ioi_zero_fract_exp {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    (∫ x in Set.Ioi (0 : ℝ),
        ((Int.fract (Real.exp x) : ℝ) : ℂ) * Complex.exp (-s * (x : ℂ)))
      = 1 / (s - 1) - riemannZeta s / s := by
  have hbase := integral_Ioi_one_fract_cpow_of_re_pos hs hs1
  have hderiv : ∀ x ∈ Set.Ioi (0 : ℝ),
      HasDerivWithinAt Real.exp (Real.exp x) (Set.Ioi (0 : ℝ)) x :=
    fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt
  have hinj : Set.InjOn Real.exp (Set.Ioi (0 : ℝ)) := fun u _ v _ huv => Real.exp_injective huv
  have hcov := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    (f := Real.exp) (f' := Real.exp) (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi hderiv hinj
    (fun t : ℝ => ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)))
  rw [image_Ioi_zero_exp] at hcov
  rw [hcov] at hbase
  rw [← hbase]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  rw [Complex.real_smul, abs_of_pos (Real.exp_pos x), cpow_ofReal_exp, Complex.ofReal_exp]
  have hcomb : Complex.exp ((x : ℂ)) *
      (((Int.fract (Real.exp x) : ℝ) : ℂ) * Complex.exp (-(s + 1) * (x : ℂ)))
      = ((Int.fract (Real.exp x) : ℝ) : ℂ) * Complex.exp ((x : ℂ) + -(s + 1) * (x : ℂ)) := by
    rw [Complex.exp_add]
    ring
  rw [hcomb]
  congr 2
  ring

end RHTower

end
