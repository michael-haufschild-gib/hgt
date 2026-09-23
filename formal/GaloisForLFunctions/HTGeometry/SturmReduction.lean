import GaloisForLFunctions.HTGeometry.ZeroSetCount

/-!
# The Sturm operator on exponential-polynomial data

Applying `D² + γ²` to an exponential polynomial multiplies each coefficient by `y² + γ²`, where `y`
is the corresponding exponent.  That factor vanishes exactly at `y = ± iγ`, so the operator deletes
one conjugate pair and rescales every other term by a nonzero constant.

Combined with `card_zeros_le_split`, this is the descent: the zero count of an exponential polynomial
is bounded by the interval length plus three times the zero count of the polynomial with one pair
removed, and the recursion terminates at a real exponential sum, counted by Laguerre's rule.
-/

open Set Filter Real

namespace GaloisForLFunctions.HTGeometry

variable {S : Finset ℂ} {C : ℂ → ℂ}

/-- The coefficient action of `D² + γ²`. -/
noncomputable def sturmCoeff (C : ℂ → ℂ) (γ : ℝ) : ℂ → ℂ :=
  fun y => C y * (y ^ (2 : ℕ) + ((γ : ℝ) : ℂ) ^ (2 : ℕ))

/-- **The Sturm expression of a real exponential polynomial is again one**, with coefficients acted
on by `y ↦ y² + γ²`. -/
theorem sturm_expr_expCombo
    (hreal : ∀ t : ℝ, (∑ y ∈ S, C y * Complex.exp (y * t)).im = 0) (γ : ℝ) (t : ℝ) :
    iteratedDeriv 2 (fun s : ℝ => (∑ y ∈ S, C y * Complex.exp (y * s)).re) t
        + γ ^ (2 : ℕ) * (∑ y ∈ S, C y * Complex.exp (y * t)).re
      = (∑ y ∈ S, sturmCoeff C γ y * Complex.exp (y * t)).re := by
  rw [iteratedDeriv_re_expCombo hreal 2 t]
  rw [← Complex.re_ofReal_mul, ← Complex.add_re]
  congr 1
  rw [Complex.ofReal_pow, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [sturmCoeff]
  ring

/-- The reduced polynomial is again real-valued. -/
theorem sturm_expCombo_real
    (hreal : ∀ t : ℝ, (∑ y ∈ S, C y * Complex.exp (y * t)).im = 0) (γ : ℝ) (t : ℝ) :
    (∑ y ∈ S, sturmCoeff C γ y * Complex.exp (y * t)).im = 0 := by
  have hsplit : (∑ y ∈ S, sturmCoeff C γ y * Complex.exp (y * t))
      = (∑ y ∈ S, C y * y ^ (2 : ℕ) * Complex.exp (y * t))
        + ((γ : ℝ) : ℂ) ^ (2 : ℕ) * (∑ y ∈ S, C y * Complex.exp (y * t)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [sturmCoeff]
    ring
  rw [hsplit, Complex.add_im, Complex.mul_im]
  rw [iteratedDeriv_expCombo_eq_ofReal hreal 2 t, Complex.ofReal_im, hreal t]
  rw [← Complex.ofReal_pow, Complex.ofReal_im]
  ring

/-! ## The operator kills exactly one conjugate pair -/

theorem sturmCoeff_eq_zero_of_mem {γ : ℝ} {y : ℂ} (hy : y = Complex.I * (γ : ℝ)) :
    sturmCoeff C γ y = 0 := by
  rw [sturmCoeff, hy]
  have : (Complex.I * ((γ : ℝ) : ℂ)) ^ (2 : ℕ) + ((γ : ℝ) : ℂ) ^ (2 : ℕ) = 0 := by
    rw [mul_pow, Complex.I_sq]
    ring
  rw [this, mul_zero]

theorem sturmCoeff_eq_zero_of_mem' {γ : ℝ} {y : ℂ} (hy : y = -(Complex.I * (γ : ℝ))) :
    sturmCoeff C γ y = 0 := by
  rw [sturmCoeff, hy]
  have : (-(Complex.I * ((γ : ℝ) : ℂ))) ^ (2 : ℕ) + ((γ : ℝ) : ℂ) ^ (2 : ℕ) = 0 := by
    rw [neg_pow, mul_pow, Complex.I_sq]
    ring
  rw [this, mul_zero]

/-- **Every other exponent survives.**  Away from `± iγ` the factor `y² + γ²` is nonzero, so a
nonzero coefficient stays nonzero. -/
theorem sturmCoeff_ne_zero {γ : ℝ} {y : ℂ} (hC : C y ≠ 0)
    (h1 : y ≠ Complex.I * (γ : ℝ)) (h2 : y ≠ -(Complex.I * (γ : ℝ))) :
    sturmCoeff C γ y ≠ 0 := by
  rw [sturmCoeff]
  refine mul_ne_zero hC (fun hcon => ?_)
  have hfac : (y - Complex.I * ((γ : ℝ) : ℂ)) * (y + Complex.I * ((γ : ℝ) : ℂ))
      = y ^ (2 : ℕ) + ((γ : ℝ) : ℂ) ^ (2 : ℕ) := by
    linear_combination (-(((γ : ℝ) : ℂ)) ^ (2 : ℕ)) * Complex.I_sq
  rcases mul_eq_zero.mp (hfac.trans hcon) with h | h
  · exact h1 (by linear_combination h)
  · exact h2 (by linear_combination h)


/-! ## The descent for exponential polynomials -/

/-- **The descent.**  For a real exponential polynomial `f`, the zeros in `[a,b]` are bounded by the
interval length plus three times the number of zeros of the reduced polynomial obtained by applying
`D² + γ²`, which deletes the conjugate pair `± iγ`. -/
theorem card_zeros_le_reduce {γ a b : ℝ} (hγ : 0 < γ) (hab : a < b)
    (hreal : ∀ t : ℝ, (∑ y ∈ S, C y * Complex.exp (y * t)).im = 0)
    (Z W : Finset ℝ) {M : ℕ} (hW : W.card ≤ M)
    (hWmem : ∀ x ∈ W, x ∈ Ioo a b)
    (hWall : ∀ x ∈ Ioo a b, (∑ y ∈ S, sturmCoeff C γ y * Complex.exp (y * x)).re = 0 → x ∈ W)
    (hZmem : ∀ x ∈ Z, x ∈ Icc a b)
    (hZzero : ∀ x ∈ Z, (∑ y ∈ S, C y * Complex.exp (y * x)).re = 0)
    (hZall : ∀ x ∈ Icc a b, (∑ y ∈ S, C y * Complex.exp (y * x)).re = 0 → x ∈ Z) :
    (Z.card : ℝ) ≤ 2 * ((b - a) * γ / π) + 3 * M + 2 := by
  set f : ℝ → ℝ := fun t => (∑ y ∈ S, C y * Complex.exp (y * t)).re with hf
  set fd : ℝ → ℝ := deriv f with hfd
  set fdd : ℝ → ℝ := deriv (deriv f) with hfdd
  set h : ℝ → ℝ := fun t => (∑ y ∈ S, sturmCoeff C γ y * Complex.exp (y * t)).re with hh
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) f :=
    Complex.reCLM.contDiff.comp (contDiff_expCombo S C)
  have hfderiv : ∀ t, HasDerivAt f (fd t) t := fun t =>
    (hsmooth.differentiable (by simp) t).hasDerivAt
  have hfdsmooth : ContDiff ℝ (⊤ : ℕ∞) fd := by
    rw [hfd]
    simpa using hsmooth.iterate_deriv 1
  have hfdderiv : ∀ t, HasDerivAt fd (fdd t) t := fun t =>
    (hfdsmooth.differentiable (by simp) t).hasDerivAt
  have hiter2 : ∀ t, iteratedDeriv 2 f t = fdd t := by
    intro t
    rw [hfdd, iteratedDeriv_succ, iteratedDeriv_one]
  have hhdef : ∀ t, h t = fdd t + γ ^ (2 : ℕ) * f t := by
    intro t
    rw [hh, ← hiter2 t]
    exact (sturm_expr_expCombo hreal γ t).symm
  have hhcont : Continuous h :=
    Complex.reCLM.continuous.comp (contDiff_expCombo S (sturmCoeff C γ)).continuous
  exact card_zeros_le_split hγ hfderiv hfdderiv hhdef hhcont M a b Z W hab hW hWmem hWall
    hZmem hZzero hZall

end GaloisForLFunctions.HTGeometry
