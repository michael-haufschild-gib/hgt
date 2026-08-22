import GaloisForLFunctions.RHTower.XiShiftPrimeExposure
import GaloisForLFunctions.RHTower.ScrewShiftFilterSource

/-!
# The even-shift filtered screw source is the completed xi shift defect
-/

namespace RHTower

open Complex MeasureTheory Set Filter
open scoped Topology BigOperators

noncomputable section

open GaloisForLFunctions

/-- The atomic multiplier of the even-shift filtered screw distribution, equation `(23)`. -/
def shiftedScrewAtomCoeff (m : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt m * (m : ℝ) ^ (-(1 / 2) : ℝ) *
    (1 - (m : ℝ) ^ (-(2 : ℝ)))

/-- Each atomic Laplace term is the corresponding filtered von Mangoldt Dirichlet term. -/
theorem shiftedScrewAtom_term (w : ℂ) (m : ℕ) :
    ((shiftedScrewAtomCoeff m : ℝ) : ℂ) * Complex.exp (-(w * (Real.log m : ℂ)))
      = LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ) *
          (1 - (n : ℂ) ^ (-(2 : ℂ)))) (1 / 2 + w) m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [shiftedScrewAtomCoeff, LSeries.term]
  have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  set L : ℂ := ((Real.log m : ℝ) : ℂ) with hL
  have hlog : Complex.log (m : ℂ) = L := Complex.natCast_log.symm
  have hpow : ((m : ℂ) ^ ((1 : ℂ) / 2 + w)) = Complex.exp (L * (1 / 2 + w)) := by
    rw [Complex.cpow_def_of_ne_zero hm0, hlog]
  have hrpow1 : (((m : ℝ) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) = Complex.exp (L * (-(1 / 2) : ℂ)) := by
    rw [Real.rpow_def_of_pos hmR, Complex.ofReal_exp, hL]
    push_cast
    ring_nf
  have hrpow2 : (((m : ℝ) ^ (-(2 : ℝ)) : ℝ) : ℂ) = (m : ℂ) ^ (-(2) : ℂ) := by
    rw [Complex.ofReal_cpow (le_of_lt hmR)]
    simp
  have hE : Complex.exp (L * (-(1 / 2) : ℂ)) * Complex.exp (-(w * L)) *
      Complex.exp (L * (1 / 2 + w)) = 1 := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    rw [show L * (-(1 / 2) : ℂ) + -(w * L) + L * (1 / 2 + w) = 0 by ring]
    exact Complex.exp_zero
  rw [LSeries.term_def, if_neg (by omega), shiftedScrewAtomCoeff, hpow]
  rw [Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one]
  rw [hrpow1, hrpow2, eq_div_iff (Complex.exp_ne_zero _)]
  linear_combination ((ArithmeticFunction.vonMangoldt m : ℂ) *
    (1 - (m : ℂ) ^ (-(2) : ℂ))) * hE

/-- The atomic Laplace transform of the filtered screw distribution is the filtered von Mangoldt
`L`-series. -/
theorem shiftedScrewAtom_laplace (w : ℂ) :
    ∑' m : ℕ, ((shiftedScrewAtomCoeff m : ℝ) : ℂ) * Complex.exp (-(w * (Real.log m : ℂ)))
      = LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ) * (1 - (n : ℂ) ^ (-(2 : ℂ))))
        (1 / 2 + w) := by
  simp only [LSeries]
  exact tsum_congr fun m => shiftedScrewAtom_term w m

/-- **Equation `(25)`, completed coordinate.**  The rational regular transform minus the filtered
von Mangoldt series is the completed even-shift defect of `xi'/xi`. -/
theorem shiftedScrewLaplace_eq_xi_shift_defect {s : ℂ} (hs : 1 < s.re) :
    (1 / (s - 1) - 1 / (s + 1) - 1 / (s + 2))
      - LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ) * (1 - (n : ℂ) ^ (-(2 : ℂ)))) s
      = logDeriv xi s - logDeriv xi (s + 2) := by
  have h := xi_logDeriv_shift_two_exposes_prime_source hs
  linear_combination h

/-- **Equation `(25)`.**  The full Laplace transform of the even-shift filtered screw
distribution — the regular three-exponential density minus its prime atoms — is exactly the
completed shift defect `logDeriv xi (s) - logDeriv xi (s+2)` at `s = 1/2 + w`. -/
theorem shiftedScrewSource_laplace_eq_xi_shift_defect {w : ℂ} (hw : 1 / 2 < w.re) :
    (∫ h in Ioi (0 : ℝ), Complex.exp (-(w * (h : ℂ))) * ((shiftedScrewDensity h : ℝ) : ℂ))
      - ∑' m : ℕ, ((shiftedScrewAtomCoeff m : ℝ) : ℂ) *
          Complex.exp (-(w * (Real.log m : ℂ)))
      = logDeriv xi (1 / 2 + w) - logDeriv xi ((1 / 2 + w) + 2) := by
  have hs : 1 < ((1 : ℂ) / 2 + w).re := by
    simp only [Complex.add_re, Complex.div_re]
    norm_num
    linarith
  rw [integral_Ioi_exp_neg_mul_shiftedScrewDensity hw, shiftedScrewAtom_laplace w]
  have hkey := shiftedScrewLaplace_eq_xi_shift_defect hs
  rw [← hkey]
  have e1 : ((1 : ℂ) / 2 + w) - 1 = w - 1 / 2 := by ring
  have e2 : ((1 : ℂ) / 2 + w) + 1 = w + 3 / 2 := by ring
  have e3 : ((1 : ℂ) / 2 + w) + 2 = w + 5 / 2 := by ring
  rw [e1, e2, e3]

end

end RHTower
