import GaloisForLFunctions.RHTower.GL3PowerFunctionEigen
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv


/-!
# Complex power functions and their Laplace eigenvalue

For `α, β ∈ ℂ` the power function `y₁^α y₂^β = exp(α log y₁ + β log y₂)` (`pwC`) is smooth,
multiplicative for the Iwasawa group law (`pwC_mul`), and satisfies
`Δ(y₁^α y₂^β) = (2α² − 2αβ + 2β² − 2α − 2β) · y₁^α y₂^β` (`lap_pwC`).

Along each of the nine Frobenius unit directions the chart point has the coordinates computed in
`GL3PowerFunctionEigen` (read off by specialising the real power function to `(1,0)` and `(0,1)`),
so the power function along the line is `exp(At + B log cosh t)` with
`(A, B) ∈ {(β, 0), (α−β, 0), (−α, 0), (0, α/2−β), (0, −(α+β)/2), (0, β/2−α)}`. Its second derivative at
`0` is `A² + B` (`iteratedDeriv_two_exp_lin_logcosh`), and summing gives the eigenvalue.
-/

open Matrix Laplacian InnerProductSpace

namespace GaloisForLFunctions.RHTower.GL3
namespace H3

/-- **The complex power function** `y₁^α y₂^β = exp(α log y₁ + β log y₂)`, `α, β ∈ ℂ`. -/
noncomputable def pwC (α β : ℂ) (z : H3) : ℂ :=
  Complex.exp (α * (Real.log z.y1 : ℂ) + β * (Real.log z.y2 : ℂ))

theorem pwC_mul (α β : ℂ) (z w : H3) : pwC α β (z * w) = pwC α β z * pwC α β w := by
  simp only [pwC, mul_y1, mul_y2, Real.log_mul z.y1_pos.ne' w.y1_pos.ne',
    Real.log_mul z.y2_pos.ne' w.y2_pos.ne', ← Complex.exp_add]
  push_cast
  ring_nf

theorem isSmooth_pwC (α β : ℂ) : IsSmooth (pwC α β) := by
  have h : ContDiffOn ℝ ⊤ (fun p : Fin 5 → ℝ =>
      Complex.exp (α * (Real.log (p 3) : ℂ) + β * (Real.log (p 4) : ℂ))) dom := by
    refine Complex.contDiff_exp.comp_contDiffOn ?_
    have h3 : ContDiffOn ℝ ⊤ (fun p : Fin 5 → ℝ => (Real.log (p 3) : ℂ)) dom :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn
        ((contDiff_apply ℝ ℝ 3).contDiffOn.log fun p hp => hp.1.ne')
    have h4 : ContDiffOn ℝ ⊤ (fun p : Fin 5 → ℝ => (Real.log (p 4) : ℂ)) dom :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn
        ((contDiff_apply ℝ ℝ 4).contDiffOn.log fun p hp => hp.2.ne')
    exact (contDiffOn_const.mul h3).add (contDiffOn_const.mul h4)
  refine h.congr fun p hp => ?_
  simp [pwC, ofCoords_eq hp]

/-! ### The coordinates along the lines -/

theorem y1_eq_pwR (w : H3) : w.y1 = pwR 1 0 w := by simp [pwR]

theorem y2_eq_pwR (w : H3) : w.y2 = pwR 0 1 w := by simp [pwR]

/-- The second derivative of `exp(At + B log cosh t)` at `0` is `A² + B`. -/
theorem iteratedDeriv_two_exp_lin_logcosh (A B : ℂ) :
    iteratedDeriv 2 (fun t : ℝ => Complex.exp (A * t + B * Real.log (Real.cosh t))) 0 =
      A ^ 2 + B := by
  have hg : ∀ t : ℝ, HasDerivAt (fun t : ℝ => A * (t : ℂ) + B * (Real.log (Real.cosh t) : ℂ))
      (A + B * (Real.tanh t : ℂ)) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := (hasDerivAt_id t).ofReal_comp
    have h2 : HasDerivAt (fun t : ℝ => (Real.log (Real.cosh t) : ℂ)) (Real.tanh t : ℂ) t := by
      have := ((Real.hasDerivAt_cosh t).log (Real.cosh_pos t).ne').ofReal_comp
      rw [Real.tanh_eq_sinh_div_cosh]
      exact this
    exact ((h1.const_mul A).add (h2.const_mul B)).congr_deriv (by ring)
  have h1 : deriv (fun t : ℝ => Complex.exp (A * t + B * Real.log (Real.cosh t))) =
      fun t => (A + B * (Real.tanh t : ℂ)) * Complex.exp (A * t + B * Real.log (Real.cosh t)) := by
    funext t
    rw [((hg t).cexp).deriv]; ring
  have hth : HasDerivAt (fun t : ℝ => (Real.tanh t : ℂ)) 1 0 := by
    have hr : HasDerivAt (fun t => Real.sinh t / Real.cosh t)
        ((Real.cosh 0 * Real.cosh 0 - Real.sinh 0 * Real.sinh 0) / Real.cosh 0 ^ 2) 0 :=
      (Real.hasDerivAt_sinh 0).div (Real.hasDerivAt_cosh 0) (Real.cosh_pos 0).ne'
    simp only [Real.cosh_zero, Real.sinh_zero, mul_one, mul_zero, sub_zero, one_pow,
      div_one] at hr
    have e : (fun t => Real.sinh t / Real.cosh t) = Real.tanh := by
      funext t; rw [Real.tanh_eq_sinh_div_cosh]
    rw [e] at hr
    exact_mod_cast hr.ofReal_comp
  have h2 := ((hth.const_mul B).const_add A).mul (hg 0).cexp
  rw [iteratedDeriv_succ, iteratedDeriv_one, h1]
  rw [show (fun t : ℝ => (A + B * (Real.tanh t : ℂ)) *
      Complex.exp (A * t + B * Real.log (Real.cosh t))) =
      (fun t : ℝ => A + B * (Real.tanh t : ℂ)) *
        fun t => Complex.exp (A * t + B * Real.log (Real.cosh t)) from rfl, h2.deriv]
  simp [Real.tanh_zero]
  ring

theorem pwC_line_00 (α β : ℂ) (t : ℝ) :
    pwC α β (ofMat (symExp (t • eDir 0 0))) =
      Complex.exp (β * t + 0 * Real.log (Real.cosh t)) := by
  rw [pwC, y1_eq_pwR, y2_eq_pwR, pwR_line_00, pwR_line_00]
  simp only [Real.log_exp]
  congr 1
  push_cast
  ring

theorem pwC_line_11 (α β : ℂ) (t : ℝ) :
    pwC α β (ofMat (symExp (t • eDir 1 1))) =
      Complex.exp ((α - β) * t + 0 * Real.log (Real.cosh t)) := by
  rw [pwC, y1_eq_pwR, y2_eq_pwR, pwR_line_11, pwR_line_11]
  simp only [Real.log_exp]
  congr 1
  push_cast
  ring

theorem pwC_line_22 (α β : ℂ) (t : ℝ) :
    pwC α β (ofMat (symExp (t • eDir 2 2))) =
      Complex.exp ((-α) * t + 0 * Real.log (Real.cosh t)) := by
  rw [pwC, y1_eq_pwR, y2_eq_pwR, pwR_line_22, pwR_line_22]
  simp only [Real.log_exp]
  congr 1
  push_cast
  ring

theorem pwC_line_01 (α β : ℂ) (t : ℝ) :
    pwC α β (ofMat (symExp (t • eDir 0 1))) =
      Complex.exp (0 * t + (α / 2 - β) * Real.log (Real.cosh t)) := by
  have hc := Real.cosh_pos t
  rw [pwC, y1_eq_pwR, y2_eq_pwR, pwR_line_01, pwR_line_01]
  simp only [Real.log_rpow hc]
  congr 1
  push_cast
  ring

theorem pwC_line_10 (α β : ℂ) (t : ℝ) :
    pwC α β (ofMat (symExp (t • eDir 1 0))) =
      Complex.exp (0 * t + (α / 2 - β) * Real.log (Real.cosh t)) := by
  have hc := Real.cosh_pos t
  rw [pwC, y1_eq_pwR, y2_eq_pwR, pwR_line_10, pwR_line_10]
  simp only [Real.log_rpow hc]
  congr 1
  push_cast
  ring

theorem pwC_line_02 (α β : ℂ) (t : ℝ) :
    pwC α β (ofMat (symExp (t • eDir 0 2))) =
      Complex.exp (0 * t + (-(α + β) / 2) * Real.log (Real.cosh t)) := by
  have hc := Real.cosh_pos t
  rw [pwC, y1_eq_pwR, y2_eq_pwR, pwR_line_02, pwR_line_02]
  simp only [Real.log_rpow hc]
  congr 1
  push_cast
  ring

theorem pwC_line_20 (α β : ℂ) (t : ℝ) :
    pwC α β (ofMat (symExp (t • eDir 2 0))) =
      Complex.exp (0 * t + (-(α + β) / 2) * Real.log (Real.cosh t)) := by
  have hc := Real.cosh_pos t
  rw [pwC, y1_eq_pwR, y2_eq_pwR, pwR_line_20, pwR_line_20]
  simp only [Real.log_rpow hc]
  congr 1
  push_cast
  ring

theorem pwC_line_12 (α β : ℂ) (t : ℝ) :
    pwC α β (ofMat (symExp (t • eDir 1 2))) =
      Complex.exp (0 * t + (β / 2 - α) * Real.log (Real.cosh t)) := by
  have hc := Real.cosh_pos t
  rw [pwC, y1_eq_pwR, y2_eq_pwR, pwR_line_12, pwR_line_12]
  simp only [Real.log_rpow hc]
  congr 1
  push_cast
  ring

theorem pwC_line_21 (α β : ℂ) (t : ℝ) :
    pwC α β (ofMat (symExp (t • eDir 2 1))) =
      Complex.exp (0 * t + (β / 2 - α) * Real.log (Real.cosh t)) := by
  have hc := Real.cosh_pos t
  rw [pwC, y1_eq_pwR, y2_eq_pwR, pwR_line_21, pwR_line_21]
  simp only [Real.log_rpow hc]
  congr 1
  push_cast
  ring

theorem line_termC (α β : ℂ) (a b : Fin 3) {A B : ℂ}
    (hfun : ∀ t : ℝ, pwC α β (ofMat (symExp (t • eDir a b))) =
      Complex.exp (A * t + B * Real.log (Real.cosh t))) :
    iteratedFDeriv ℝ 2 (chart (pwC α β) 1) 0 ![EuclideanSpace.single (a, b) 1,
      EuclideanSpace.single (a, b) 1] = A ^ 2 + B := by
  rw [show EuclideanSpace.single (a, b) (1 : ℝ) = eDir a b from rfl,
    iteratedFDeriv_two_line (contDiff_chart (isSmooth_pwC α β) 1)]
  simp only [chart_one, hfun]
  exact iteratedDeriv_two_exp_lin_logcosh A B

/-- The Laplace eigenvalue `2α² − 2αβ + 2β² − 2α − 2β` of `y₁^α y₂^β`. -/
def lapEig (α β : ℂ) : ℂ := 2 * α ^ 2 - 2 * α * β + 2 * β ^ 2 - 2 * α - 2 * β

theorem lap_pwC_one (α β : ℂ) : lap (pwC α β) 1 = lapEig α β := by
  rw [lap, laplacian_eq_iteratedFDeriv_orthonormalBasis _ (EuclideanSpace.basisFun (Fin 3 × Fin 3) ℝ)]
  simp only [EuclideanSpace.basisFun_apply]
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_three]
  rw [line_termC α β 0 0 (pwC_line_00 α β), line_termC α β 0 1 (pwC_line_01 α β),
    line_termC α β 0 2 (pwC_line_02 α β), line_termC α β 1 0 (pwC_line_10 α β),
    line_termC α β 1 1 (pwC_line_11 α β), line_termC α β 1 2 (pwC_line_12 α β),
    line_termC α β 2 0 (pwC_line_20 α β), line_termC α β 2 1 (pwC_line_21 α β),
    line_termC α β 2 2 (pwC_line_22 α β), lapEig]
  ring

/-- **Complex power functions are eigenfunctions of the Laplacian**:
`Δ(y₁^α y₂^β) = (2α² − 2αβ + 2β² − 2α − 2β) · y₁^α y₂^β` for all `α, β ∈ ℂ`. -/
theorem lap_pwC (α β : ℂ) (z : H3) : lap (pwC α β) z = lapEig α β * pwC α β z := by
  have h := lap_comp_smul (pwC α β) (toGL z) 1
  rw [toGL_smul_one] at h
  rw [← h]
  have e : (fun w => pwC α β (toGL z • w)) = fun w => pwC α β z * pwC α β w := by
    funext w
    rw [toGL_smul, pwC_mul]
  have hc : chart (fun w => pwC α β z * pwC α β w) 1 = (pwC α β z) • chart (pwC α β) 1 := by
    funext v; simp [chart, smul_eq_mul]
  rw [e, lap, hc, laplacian_smul _ ((contDiff_chart (isSmooth_pwC α β) 1).contDiffAt.of_le
    (by exact_mod_cast le_top)), smul_eq_mul, ← lap, lap_pwC_one]
  ring

end H3
end GaloisForLFunctions.RHTower.GL3
