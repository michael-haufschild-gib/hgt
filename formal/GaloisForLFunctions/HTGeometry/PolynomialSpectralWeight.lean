import GaloisForLFunctions.HTGeometry.AbstractSpectralWeightedRigidity

/-!
# Polynomial spectral weights

A weight with a polynomial majorant on the admissible strip is subexponential at every rate: the
exponential series bounds `t^m` by `m!·e^t`, and rescaling `t` by the rate turns the polynomial
degree into a constant.  Every polynomial without a zero in the open right half plane is therefore
a spectral weight.
-/

open Complex
open scoped BigOperators

namespace HTGeometry

/-- `t^m ≤ m!·e^t` on the nonnegative axis: the `m`-th term of the exponential series. -/
theorem pow_le_factorial_mul_exp {t : ℝ} (ht : 0 ≤ t) (m : ℕ) :
    t ^ m ≤ (Nat.factorial m : ℝ) * Real.exp t := by
  have hser := Real.sum_le_exp_of_nonneg ht (m + 1)
  have hmem : t ^ m / (Nat.factorial m : ℝ)
      ≤ ∑ i ∈ Finset.range (m + 1), t ^ i / (Nat.factorial i : ℝ) := by
    refine Finset.single_le_sum (f := fun i => t ^ i / (Nat.factorial i : ℝ)) (fun i _ => ?_)
      (Finset.self_mem_range_succ m)
    positivity
  have hfac : (0 : ℝ) < (Nat.factorial m : ℝ) := by exact_mod_cast Nat.factorial_pos m
  rw [div_le_iff₀ hfac] at hmem
  nlinarith [hmem, hser, hfac, Real.exp_pos t]

/-- **A polynomial grows slower than every exponential.** -/
theorem one_add_pow_le_exp {r : ℝ} (hr : 0 ≤ r) {ε : ℝ} (hε : 0 < ε) (m : ℕ) :
    (1 + r) ^ m
      ≤ (Nat.factorial m : ℝ) / ε ^ m * Real.exp ε * Real.exp (ε * r) := by
  have ht : (0 : ℝ) ≤ ε * (1 + r) := by positivity
  have hkey := pow_le_factorial_mul_exp ht m
  have hsplit : Real.exp (ε * (1 + r)) = Real.exp ε * Real.exp (ε * r) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hsplit, mul_pow] at hkey
  have hεm : (0 : ℝ) < ε ^ m := by positivity
  rw [← le_div_iff₀' hεm] at hkey
  refine hkey.trans (le_of_eq ?_)
  field_simp

/-- The subexponential majorant of a polynomially bounded weight. -/
noncomputable def polyWeightConst (Cp : ℝ) (m : ℕ) (ε : ℝ) : ℝ :=
  |Cp| * |(Nat.factorial m : ℝ) / ε ^ m| * Real.exp ε

theorem polyWeightConst_nonneg (Cp : ℝ) (m : ℕ) (ε : ℝ) : 0 ≤ polyWeightConst Cp m ε := by
  rw [polyWeightConst]
  positivity

/-- **Every polynomially bounded, right-half-plane nonvanishing function is a spectral weight.** -/
noncomputable def SpectralWeight.ofPolyBound (f : ℂ → ℂ) (Cp : ℝ) (m : ℕ)
    (hne : ∀ z : ℂ, 0 < z.re → f z ≠ 0)
    (hf : ∀ z : ℂ, |z.im| ≤ 1 / 2 → 0 ≤ z.re → ‖f z‖ ≤ Cp * (1 + z.re) ^ m) :
    SpectralWeight where
  toFun := f
  ne_zero := hne
  const := polyWeightConst Cp m
  const_nonneg := polyWeightConst_nonneg Cp m
  le_const := by
    intro ε hε z hzim hzre
    have hpoly := hf z hzim hzre
    have hgrow := one_add_pow_le_exp hzre hε m
    have hCabs : Cp ≤ |Cp| := le_abs_self Cp
    have hone : (0 : ℝ) ≤ (1 + z.re) ^ m := by positivity
    have hstep : Cp * (1 + z.re) ^ m ≤ |Cp| * (1 + z.re) ^ m :=
      mul_le_mul_of_nonneg_right hCabs hone
    have hfacabs : |(Nat.factorial m : ℝ) / ε ^ m| = (Nat.factorial m : ℝ) / ε ^ m := by
      refine abs_of_nonneg (div_nonneg (by positivity) ?_)
      positivity
    refine hpoly.trans (hstep.trans ?_)
    rw [polyWeightConst, hfacabs, mul_assoc, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rw [← mul_assoc]
    exact hgrow

end HTGeometry
