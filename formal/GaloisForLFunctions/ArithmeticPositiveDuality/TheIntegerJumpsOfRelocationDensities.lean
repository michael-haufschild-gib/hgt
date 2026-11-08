import GaloisForLFunctions.ArithmeticPositiveDuality.TheUnitCellTraceOfZeroRelocation

/-!
# The integer lattice in a relocation density

Conjugate-pair densities glue continuously across consecutive unit cells.
Their cell derivatives jump by the inverse square of the integer endpoint.
The normalized quartet inherits exactly its quadratic trace as jump coefficient.
-/

noncomputable section
set_option autoImplicit false

open Complex Finset

namespace GaloisForLFunctions.ArithmeticPositiveDuality

/-- The derivative of the complex power-sum kernel inside a fixed cell. -/
def zeroPowerSumCellSlope (s : ℂ) (N : ℕ) (θ : ℝ) : ℂ :=
  (s - 1) * ((N : ℂ) + (θ : ℂ)) ^ (s - 2) *
    ((∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)) - riemannZeta s)

/-- Adding the next integer atom changes the complex kernel by `1/(N+1)`. -/
theorem zeroPowerSumCellKernel_jump (s : ℂ) (N : ℕ) :
    zeroPowerSumCellKernel s (N + 1) 0 - zeroPowerSumCellKernel s N 1 =
      1 / ((N : ℂ) + 1) := by
  have hn : (N : ℂ) + 1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero N)
  have hp : ((N : ℂ) + 1) ^ (s - 1) * ((N : ℂ) + 1) ^ (-s) =
      1 / ((N : ℂ) + 1) := by
    rw [← Complex.cpow_add _ _ hn, show s - 1 + -s = -(1 : ℂ) by ring,
      Complex.cpow_neg_one, one_div]
  simp only [zeroPowerSumCellKernel, Complex.ofReal_zero, add_zero, Complex.ofReal_one,
    Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1), Nat.cast_add, Nat.cast_one]
  linear_combination hp

/-- The derivative jump retains the exponent through `(s-1)/(N+1)²`. -/
theorem zeroPowerSumCellSlope_jump (s : ℂ) (N : ℕ) :
    zeroPowerSumCellSlope s (N + 1) 0 - zeroPowerSumCellSlope s N 1 =
      (s - 1) / ((N : ℂ) + 1) ^ 2 := by
  have hn : (N : ℂ) + 1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero N)
  have hp : ((N : ℂ) + 1) ^ (s - 2) * ((N : ℂ) + 1) ^ (-s) =
      1 / ((N : ℂ) + 1) ^ 2 := by
    rw [← Complex.cpow_add _ _ hn, show s - 2 + -s = -(2 : ℂ) by ring,
      Complex.cpow_neg, show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num,
      Complex.cpow_natCast, one_div]
  simp only [zeroPowerSumCellSlope, Complex.ofReal_zero, add_zero, Complex.ofReal_one,
    Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1), Nat.cast_add, Nat.cast_one]
  linear_combination (s - 1) * hp

/-- Taking the imaginary part removes the atom's real jump. -/
theorem criticalPairCellKernel_glue (γ : ℝ) (N : ℕ) :
    criticalPairCellKernel γ (N + 1) 0 = criticalPairCellKernel γ N 1 := by
  have he := congrArg Complex.im (zeroPowerSumCellKernel_jump (1 / 2 + (γ : ℂ) * I) N)
  simp only [Complex.sub_im] at he
  have him : (1 / ((N : ℂ) + 1)).im = 0 := by simp
  rw [him, sub_eq_zero] at he
  exact congrArg (fun x : ℝ => x / γ) he

/-- The quartet density also glues without a jump in value. -/
theorem quartetCellDefect_glue (γ₁ γ₂ c : ℝ) (N : ℕ) :
    quartetCellDefect γ₁ γ₂ c (N + 1) 0 = quartetCellDefect γ₁ γ₂ c N 1 := by
  simp only [quartetCellDefect, criticalPairCellKernel_glue]

/-- Inside a positive cell, the ordinary derivative is the imaginary part of the complex slope. -/
theorem hasDerivAt_criticalPairCellKernel (γ : ℝ) (N : ℕ) (θ : ℝ)
    (hθ : 0 < (N : ℝ) + θ) :
    HasDerivAt (criticalPairCellKernel γ N)
      ((zeroPowerSumCellSlope (1 / 2 + (γ : ℂ) * I) N θ).im / γ) θ := by
  let s : ℂ := 1 / 2 + (γ : ℂ) * I
  have hs : s - 1 ≠ 0 := by
    intro he
    have hre := congrArg Complex.re he
    norm_num [s] at hre
  have h := (hasDerivAt_ofReal_cpow_const hθ.ne' hs).scomp θ
    ((hasDerivAt_id θ).const_add (N : ℝ))
  have hsc : s - 1 - 1 = s - 2 := by ring
  have hc : HasDerivAt (zeroPowerSumCellKernel s N) (zeroPowerSumCellSlope s N θ) θ := by
    unfold zeroPowerSumCellKernel zeroPowerSumCellSlope
    simpa only [Function.comp_def, one_smul,
      Complex.ofReal_add, Complex.ofReal_natCast, hsc] using
        h.mul_const ((∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)) - riemannZeta s)
  have hi := Complex.imCLM.hasFDerivAt.comp_hasDerivAt θ hc
  unfold criticalPairCellKernel
  simpa only [Function.comp_def, Complex.imCLM_apply, s] using hi.div_const γ

/-- The pair density is continuous at the integer, but its two cell derivatives differ by `1/n²`. -/
theorem criticalPairCellKernel_derivative_jump {γ : ℝ} (hγ : γ ≠ 0) (N : ℕ) :
    deriv (criticalPairCellKernel γ (N + 1)) 0 -
        deriv (criticalPairCellKernel γ N) 1 = 1 / ((N : ℝ) + 1) ^ 2 := by
  rw [(hasDerivAt_criticalPairCellKernel γ (N + 1) 0 (by positivity)).deriv,
    (hasDerivAt_criticalPairCellKernel γ N 1 (by positivity)).deriv, ← sub_div]
  have he := congrArg Complex.im
    (zeroPowerSumCellSlope_jump (1 / 2 + (γ : ℂ) * I) N)
  rw [Complex.sub_im] at he
  rw [he, show ((N : ℂ) + 1) ^ 2 = (((N : ℝ) + 1) ^ 2 : ℝ) by push_cast; rfl,
    Complex.div_ofReal_im]
  rw [show (1 / 2 + (γ : ℂ) * I - 1).im = γ by simp]
  field_simp [hγ]

theorem deriv_quartetCellDefect_eq (γ₁ γ₂ c : ℝ) (N : ℕ) (θ : ℝ)
    (hθ : 0 < (N : ℝ) + θ) :
    deriv (quartetCellDefect γ₁ γ₂ c N) θ = c / (γ₂ ^ 2 - γ₁ ^ 2) *
      ((γ₂ ^ 2 + 1 / 4) * deriv (criticalPairCellKernel γ₂ N) θ -
        (γ₁ ^ 2 + 1 / 4) * deriv (criticalPairCellKernel γ₁ N) θ) := by
  have h₁ := hasDerivAt_criticalPairCellKernel γ₁ N θ hθ
  have h₂ := hasDerivAt_criticalPairCellKernel γ₂ N θ hθ
  rw [h₁.deriv, h₂.deriv]
  unfold quartetCellDefect
  exact (((h₂.const_mul (γ₂ ^ 2 + 1 / 4)).sub
    (h₁.const_mul (γ₁ ^ 2 + 1 / 4))).const_mul (c / (γ₂ ^ 2 - γ₁ ^ 2))).deriv

/-- The exact derivative jump recovers the same coefficient as the Bernoulli and vertical traces. -/
theorem quartetCellDefect_derivative_jump {γ₁ γ₂ : ℝ}
    (hγ₁ : 0 < γ₁) (hγ₂ : γ₁ < γ₂) (c : ℝ) (N : ℕ) :
    deriv (quartetCellDefect γ₁ γ₂ c (N + 1)) 0 -
        deriv (quartetCellDefect γ₁ γ₂ c N) 1 = c / ((N : ℝ) + 1) ^ 2 := by
  have hd : γ₂ ^ 2 - γ₁ ^ 2 ≠ 0 := by
    have hp := mul_pos (sub_pos.mpr hγ₂) (add_pos (hγ₁.trans hγ₂) hγ₁)
    nlinarith only [hp]
  rw [deriv_quartetCellDefect_eq γ₁ γ₂ c (N + 1) 0 (by positivity),
    deriv_quartetCellDefect_eq γ₁ γ₂ c N 1 (by positivity)]
  calc
    _ = c / (γ₂ ^ 2 - γ₁ ^ 2) *
        ((γ₂ ^ 2 + 1 / 4) * (deriv (criticalPairCellKernel γ₂ (N + 1)) 0 -
          deriv (criticalPairCellKernel γ₂ N) 1) -
        (γ₁ ^ 2 + 1 / 4) * (deriv (criticalPairCellKernel γ₁ (N + 1)) 0 -
          deriv (criticalPairCellKernel γ₁ N) 1)) := by ring
    _ = _ := by
      rw [criticalPairCellKernel_derivative_jump (hγ₁.trans hγ₂).ne',
        criticalPairCellKernel_derivative_jump hγ₁.ne']
      field_simp [hd]
      ring

#print axioms quartetCellDefect_glue
#print axioms criticalPairCellKernel_derivative_jump
#print axioms quartetCellDefect_derivative_jump

end GaloisForLFunctions.ArithmeticPositiveDuality
