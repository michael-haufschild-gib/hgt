import GaloisForLFunctions.HTGeometry.SturmSelfAdjoint

/-!
# The prolate kernel is symmetric under the prolate operator

Applying `L_y g = (d/dy) ((1 - y^(2 : ℕ)) g') - c^(2 : ℕ) y^(2 : ℕ) g` to the finite Fourier kernel
`K (x, t) = exp (i c x t)` multiplies it by

`-2 i c x t - c^(2 : ℕ) x^(2 : ℕ) - c^(2 : ℕ) t^(2 : ℕ) + c^(2 : ℕ) x^(2 : ℕ) t^(2 : ℕ)`,

which is symmetric in `x` and `t`.  So `L_t K = L_x K`.

Together with `integral_mul_sturm_symm` -- which moves the Sturm operator across an integral when
the weight vanishes at both endpoints, as `1 - t^(2 : ℕ)` does at the ends of the band -- this is the
commuting-operator step: an eigenfunction of the finite Fourier transform satisfies the prolate
differential equation.
-/

open Complex

namespace HTGeometry

/-- The finite Fourier kernel of bandwidth `c`. -/
noncomputable def prolateKernel (c x t : ℝ) : ℂ := Complex.exp (Complex.I * c * x * t)

/-- The symbol produced by the prolate operator on the kernel. -/
noncomputable def prolateSymbol (c x t : ℝ) : ℂ :=
  -2 * Complex.I * c * x * t - (c : ℂ) ^ (2 : ℕ) * (x : ℂ) ^ (2 : ℕ) - (c : ℂ) ^ (2 : ℕ) * (t : ℂ) ^ (2 : ℕ)
    + (c : ℂ) ^ (2 : ℕ) * (x : ℂ) ^ (2 : ℕ) * (t : ℂ) ^ (2 : ℕ)

/-- **The symbol is symmetric.** -/
theorem prolateSymbol_symm (c x t : ℝ) : prolateSymbol c x t = prolateSymbol c t x := by
  rw [prolateSymbol, prolateSymbol]
  ring

/-- **The kernel is symmetric.** -/
theorem prolateKernel_symm (c x t : ℝ) : prolateKernel c x t = prolateKernel c t x := by
  rw [prolateKernel, prolateKernel]
  ring_nf

theorem hasDerivAt_prolateKernel (c x t : ℝ) :
    HasDerivAt (fun s : ℝ => prolateKernel c x s)
      (Complex.I * c * x * prolateKernel c x t) t := by
  have hlin : HasDerivAt (fun s : ℝ => Complex.I * c * x * (s : ℂ)) (Complex.I * c * x) t := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (Complex.I * c * x)
  have h := hlin.cexp
  refine h.congr_deriv ?_ |>.congr_of_eventuallyEq ?_
  · rw [prolateKernel]
    ring
  · filter_upwards with s
    rw [prolateKernel]

/-- **The prolate flux derivative of the kernel.**  Differentiating `(1 - t^(2 : ℕ))` times the kernel's
derivative produces the symbol plus the `c^(2 : ℕ) t^(2 : ℕ)` term that the operator subtracts. -/
theorem hasDerivAt_prolateFlux (c x t : ℝ) :
    HasDerivAt
      (fun s : ℝ => ((1 - s ^ (2 : ℕ) : ℝ) : ℂ) * (Complex.I * c * x * prolateKernel c x s))
      ((prolateSymbol c x t + (c : ℂ) ^ (2 : ℕ) * (t : ℂ) ^ (2 : ℕ)) * prolateKernel c x t) t := by
  have hw : HasDerivAt (fun s : ℝ => ((1 - s ^ (2 : ℕ) : ℝ) : ℂ)) (((-2 * t : ℝ) : ℂ)) t := by
    have : HasDerivAt (fun s : ℝ => (1 - s ^ (2 : ℕ) : ℝ)) (-2 * t) t := by
      simpa using ((hasDerivAt_pow 2 t).const_sub 1)
    exact this.ofReal_comp
  have hk := (hasDerivAt_prolateKernel c x t).const_mul (Complex.I * c * x)
  have h := hw.mul hk
  refine h.congr_deriv ?_
  rw [prolateSymbol]
  have hI : Complex.I ^ (2 : ℕ) = -1 := Complex.I_sq
  push_cast
  ring_nf
  rw [hI]
  ring

/-- The prolate operator applied to the kernel: the flux derivative minus the `c^(2 : ℕ) t^(2 : ℕ)` term is the
symbol times the kernel. -/
theorem prolateOperator_kernel (c x t : ℝ) :
    (prolateSymbol c x t + (c : ℂ) ^ (2 : ℕ) * (t : ℂ) ^ (2 : ℕ)) * prolateKernel c x t
        - (c : ℂ) ^ (2 : ℕ) * (t : ℂ) ^ (2 : ℕ) * prolateKernel c x t
      = prolateSymbol c x t * prolateKernel c x t := by
  ring

/-- **The prolate operator acts symmetrically on its kernel**: `L_t K = L_x K`.  Both are the
symmetric symbol times the kernel, so the operator may be moved from the integration variable to the
parameter. -/
theorem prolateOperator_kernel_symm (c x t : ℝ) :
    prolateSymbol c x t * prolateKernel c x t
      = prolateSymbol c t x * prolateKernel c t x := by
  rw [prolateSymbol_symm c x t, prolateKernel_symm c x t]

/-- The kernel is unimodular: its exponent is purely imaginary. -/
theorem norm_prolateKernel (c x t : ℝ) : ‖prolateKernel c x t‖ = 1 := by
  rw [prolateKernel, Complex.norm_exp]
  have hre : (Complex.I * c * x * t).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hre, Real.exp_zero]

/-- The kernel differentiated in its **first** variable. -/
theorem hasDerivAt_prolateKernel_fst (c x t : ℝ) :
    HasDerivAt (fun y : ℝ => prolateKernel c y t)
      (Complex.I * c * t * prolateKernel c x t) x := by
  have h := hasDerivAt_prolateKernel c t x
  refine h.congr_of_eventuallyEq ?_ |>.congr_deriv ?_
  · filter_upwards with y
    exact prolateKernel_symm c y t
  · rw [prolateKernel_symm c t x]

/-- The parameter derivative of the kernel is bounded by the bandwidth on the band. -/
theorem norm_prolateKernel_deriv_le {c t : ℝ} (ht : |t| ≤ 1) (y : ℝ) :
    ‖Complex.I * (c : ℂ) * (t : ℂ) * prolateKernel c y t‖ ≤ |c| := by
  rw [norm_mul, norm_prolateKernel, mul_one, norm_mul, norm_mul, Complex.norm_I, one_mul,
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  nlinarith [abs_nonneg c, abs_nonneg t, ht]

end HTGeometry
