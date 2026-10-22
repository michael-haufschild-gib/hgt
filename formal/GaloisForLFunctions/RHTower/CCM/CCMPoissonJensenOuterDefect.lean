import Mathlib

/-!
# The exact outer-entropy defect of the Poisson half-weight

Four exact mechanisms of the card are formalized.

*The elementary Blaschke defect.*  For a right half-plane zero `b = a + iγ` and a positive real
point `x`, the factor `(z-b)/(z+conj b)` has

```text
-log |b_b(x)| = ½ log ( ((x+a)² + γ²) / ((x-a)² + γ²) ) ,
```

which is `(10)`–`(11)`.

*Positivity and exact detection.*  Every such term is nonnegative, and strictly positive off the
degenerate point, so a finite defect sum vanishes exactly when the divisor is empty — `(12)` and the
finite form of `(13)`.

*The dephasing identity.*  A bounded-type factor `e^{-τ z} O(z)` has the same boundary logarithmic
modulus as its outer part and interior value shifted by exactly `-τ x`, which is the explicit term
`τ_N x` of `(20)`–`(21)`.

*The limit subtraction.*  If the interior and boundary logarithmic data converge and the defects
tend to zero, the limiting defect is zero — `(15)`–`(18)`.

The half-plane inner–outer factorization `(4)`, the Poisson representation `(9)` of the outer
factor, the Blaschke convergence condition and the analytic zeta multiplier `(2)` are cited parents
and stay outside the Lean statement.
-/

open Filter Topology

noncomputable section

namespace GaloisForLFunctions.RHTower

/-! ## The elementary half-plane Blaschke factor -/

/-- The elementary right half-plane Blaschke factor `(10)`. -/
def halfPlaneBlaschke (b z : ℂ) : ℂ := (z - b) / (z + (starRingEnd ℂ) b)

theorem normSq_ofReal_sub (x a γ : ℝ) :
    Complex.normSq ((x : ℂ) - ((a : ℂ) + Complex.I * (γ : ℂ))) = (x - a) ^ (2 : ℕ) + γ ^ (2 : ℕ) := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

theorem normSq_ofReal_add_conj (x a γ : ℝ) :
    Complex.normSq ((x : ℂ) + (starRingEnd ℂ) ((a : ℂ) + Complex.I * (γ : ℂ)))
      = (x + a) ^ (2 : ℕ) + γ ^ (2 : ℕ) := by
  simp only [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.normSq_apply,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- The squared modulus of the Blaschke factor at a positive real point. -/
theorem norm_sq_halfPlaneBlaschke (x a γ : ℝ) :
    ‖halfPlaneBlaschke ((a : ℂ) + Complex.I * (γ : ℂ)) (x : ℂ)‖ ^ (2 : ℕ)
      = ((x - a) ^ (2 : ℕ) + γ ^ (2 : ℕ)) / ((x + a) ^ (2 : ℕ) + γ ^ (2 : ℕ)) := by
  rw [halfPlaneBlaschke, norm_div, div_pow, ← Complex.normSq_eq_norm_sq,
    ← Complex.normSq_eq_norm_sq, normSq_ofReal_sub, normSq_ofReal_add_conj]

/-- The outer-entropy defect contributed by a single right half-plane zero, `(11)`. -/
def outerDefectTerm (x a γ : ℝ) : ℝ :=
  (1 / 2) * Real.log (((x + a) ^ (2 : ℕ) + γ ^ (2 : ℕ)) / ((x - a) ^ (2 : ℕ) + γ ^ (2 : ℕ)))

/-- **Equations (10)–(11).**  The negative logarithmic modulus of the elementary Blaschke factor is
exactly the defect term. -/
theorem neg_log_norm_halfPlaneBlaschke {x a γ : ℝ} (hx : 0 < x) (ha : 0 < a) :
    -Real.log ‖halfPlaneBlaschke ((a : ℂ) + Complex.I * (γ : ℂ)) (x : ℂ)‖
      = outerDefectTerm x a γ := by
  have hB : ((x + a) ^ (2 : ℕ) + γ ^ (2 : ℕ)) ≠ 0 := by positivity
  by_cases hA : ((x - a) ^ (2 : ℕ) + γ ^ (2 : ℕ)) = 0
  · have hzero : ‖halfPlaneBlaschke ((a : ℂ) + Complex.I * (γ : ℂ)) (x : ℂ)‖ = 0 := by
      have hsq := norm_sq_halfPlaneBlaschke x a γ
      rw [hA, zero_div] at hsq
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
    rw [hzero, outerDefectTerm, hA, div_zero, Real.log_zero]
    norm_num
  · have hlogsq : 2 * Real.log ‖halfPlaneBlaschke ((a : ℂ) + Complex.I * (γ : ℂ)) (x : ℂ)‖
        = Real.log (((x - a) ^ (2 : ℕ) + γ ^ (2 : ℕ)) / ((x + a) ^ (2 : ℕ) + γ ^ (2 : ℕ))) := by
      rw [← norm_sq_halfPlaneBlaschke x a γ, Real.log_pow]
      norm_num
    have hinv : ((x + a) ^ (2 : ℕ) + γ ^ (2 : ℕ)) / ((x - a) ^ (2 : ℕ) + γ ^ (2 : ℕ))
        = (((x - a) ^ (2 : ℕ) + γ ^ (2 : ℕ)) / ((x + a) ^ (2 : ℕ) + γ ^ (2 : ℕ)))⁻¹ := by
      field_simp
    rw [outerDefectTerm, hinv, Real.log_inv]
    linarith

/-! ## Positivity and exact detection -/

/-- **Equation (12).**  Every defect term is nonnegative. -/
theorem outerDefectTerm_nonneg {x a γ : ℝ} (hx : 0 < x) (ha : 0 < a) :
    0 ≤ outerDefectTerm x a γ := by
  by_cases hA : ((x - a) ^ (2 : ℕ) + γ ^ (2 : ℕ)) = 0
  · rw [outerDefectTerm, hA, div_zero, Real.log_zero]
    norm_num
  · have hApos : 0 < (x - a) ^ (2 : ℕ) + γ ^ (2 : ℕ) := lt_of_le_of_ne (by positivity) (Ne.symm hA)
    have hle : (x - a) ^ (2 : ℕ) + γ ^ (2 : ℕ) ≤ (x + a) ^ (2 : ℕ) + γ ^ (2 : ℕ) := by nlinarith
    have hratio : 1 ≤ ((x + a) ^ (2 : ℕ) + γ ^ (2 : ℕ)) / ((x - a) ^ (2 : ℕ) + γ ^ (2 : ℕ)) :=
      (one_le_div hApos).mpr hle
    have := Real.log_nonneg hratio
    rw [outerDefectTerm]
    linarith

/-- **Equation (12), strict form.**  Away from the degenerate point every defect term is strictly
positive: each off-line zero contributes with its horizontal displacement. -/
theorem outerDefectTerm_pos {x a γ : ℝ} (hx : 0 < x) (ha : 0 < a)
    (hA : (x - a) ^ (2 : ℕ) + γ ^ (2 : ℕ) ≠ 0) : 0 < outerDefectTerm x a γ := by
  have hApos : 0 < (x - a) ^ (2 : ℕ) + γ ^ (2 : ℕ) := lt_of_le_of_ne (by positivity) (Ne.symm hA)
  have hlt : (x - a) ^ (2 : ℕ) + γ ^ (2 : ℕ) < (x + a) ^ (2 : ℕ) + γ ^ (2 : ℕ) := by nlinarith
  have hratio : 1 < ((x + a) ^ (2 : ℕ) + γ ^ (2 : ℕ)) / ((x - a) ^ (2 : ℕ) + γ ^ (2 : ℕ)) :=
    (one_lt_div hApos).mpr hlt
  have := Real.log_pos hratio
  rw [outerDefectTerm]
  linarith

/-- **Equation (13), finite form.**  A finite outer-entropy defect vanishes exactly when the
divisor beyond the layer is empty. -/
theorem sum_outerDefect_eq_zero_iff {ι : Type*} {S : Finset ι} {a γ m : ι → ℝ} {x : ℝ}
    (hx : 0 < x) (ha : ∀ i ∈ S, 0 < a i) (hm : ∀ i ∈ S, 0 < m i)
    (hA : ∀ i ∈ S, (x - a i) ^ (2 : ℕ) + (γ i) ^ (2 : ℕ) ≠ 0) :
    (∑ i ∈ S, m i * outerDefectTerm x (a i) (γ i)) = 0 ↔ S = ∅ := by
  constructor
  · intro hsum
    by_contra hne
    obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have hpos : ∀ j ∈ S, 0 ≤ m j * outerDefectTerm x (a j) (γ j) := fun j hj =>
      mul_nonneg (le_of_lt (hm j hj)) (outerDefectTerm_nonneg hx (ha j hj))
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg hpos).mp hsum i hi
    have hstrict : 0 < m i * outerDefectTerm x (a i) (γ i) :=
      mul_pos (hm i hi) (outerDefectTerm_pos hx (ha i hi) (hA i hi))
    exact absurd hzero (ne_of_gt hstrict)
  · intro hS
    rw [hS, Finset.sum_empty]

/-! ## The dephasing identity -/

/-- **Equation (21), interior.**  The exponential mean type shifts the interior logarithmic modulus
by exactly `-τ x`.  The outer factor is zero-free in the right half-plane, which is the standing
hypothesis `O(x) ≠ 0`. -/
theorem log_norm_meanType_interior (τ x : ℝ) (O : ℂ → ℂ) (hO : O (x : ℂ) ≠ 0) :
    Real.log ‖Complex.exp (-(τ : ℂ) * (x : ℂ)) * O (x : ℂ)‖
      = Real.log ‖O (x : ℂ)‖ - τ * x := by
  rw [norm_mul, Complex.norm_exp]
  have hre : (-(τ : ℂ) * (x : ℂ)).re = -(τ * x) := by
    simp [Complex.mul_re]
  rw [hre, Real.log_mul (ne_of_gt (Real.exp_pos _)) (norm_ne_zero_iff.mpr hO), Real.log_exp]
  ring

/-- **Equation (21), boundary.**  The exponential mean type is unimodular on the imaginary axis, so
the boundary logarithmic modulus is that of the outer part. -/
theorem log_norm_meanType_boundary (τ t : ℝ) (O : ℂ → ℂ) :
    Real.log ‖Complex.exp (-(τ : ℂ) * (Complex.I * (t : ℂ))) * O (Complex.I * (t : ℂ))‖
      = Real.log ‖O (Complex.I * (t : ℂ))‖ := by
  rw [norm_mul, Complex.norm_exp]
  have hre : (-(τ : ℂ) * (Complex.I * (t : ℂ))).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hre, Real.exp_zero, one_mul]

/-! ## The limit subtraction -/

/-- **Equations (15)–(18).**  If the interior and the boundary logarithmic data converge and the
finite defects tend to zero, the limiting defect vanishes. -/
theorem defect_limit_eq_zero {P I E : ℕ → ℝ} {p i : ℝ}
    (hE : ∀ n, E n = P n - I n)
    (hP : Tendsto P atTop (nhds p)) (hI : Tendsto I atTop (nhds i))
    (h0 : Tendsto E atTop (nhds 0)) : p - i = 0 := by
  have hsub : Tendsto E atTop (nhds (p - i)) := by
    refine (hP.sub hI).congr fun n => (hE n).symm
  exact tendsto_nhds_unique hsub h0

end GaloisForLFunctions.RHTower

end
