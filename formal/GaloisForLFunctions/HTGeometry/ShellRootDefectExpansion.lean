import GaloisForLFunctions.HTGeometry.ShellBinomialExpansion

/-!
# The root defect of the mass shell as a truncated expansion

The defect `√(t²+x²) - t`, written in the reciprocal spectral parameter `w = 1/t`, is
`((1+x²w²)^{1/2} - 1)/w`.  The shell binomial expansion has no constant term after subtracting one
and no linear term at all, so dividing by `w` is exact on polynomials and lowers the order by one.

The resulting expansion vanishes at the origin, which is what the exponential rule needs.
-/

open Polynomial

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

section RootDefect

theorem coeff_odd_shellBinomPoly (α : ℝ) (m : ℕ) (x : ℝ) {j : ℕ} (hj : ¬ 2 ∣ j) :
    (shellBinomPoly α m x).coeff j = 0 := by
  classical
  rw [shellBinomPoly, Polynomial.finsetSum_coeff]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  have hne : ¬ (j = 2 * k) := by
    intro h
    exact hj ⟨k, h⟩
  rw [if_neg hne, mul_zero]

/-- The reciprocal-parameter form of the mass-shell root defect. -/
def shellDefect (x : ℝ) (w : ℂ) : ℂ :=
  ((1 + (x : ℂ) ^ (2 : ℕ) * w ^ (2 : ℕ)) ^ (((1 : ℝ) / 2 : ℝ) : ℂ) - 1) / w

/-- Its truncated expansion. -/
def shellDefectPoly (m : ℕ) (x : ℝ) : Polynomial ℂ :=
  (shellBinomPoly ((1 : ℝ) / 2) (m + 1) x - 1).divX

theorem coeff_zero_shellBinomPoly_sub_one (α : ℝ) (m : ℕ) (x : ℝ) (hm : 0 < m) :
    (shellBinomPoly α m x - 1).coeff 0 = 0 := by
  classical
  have hc : (shellBinomPoly α m x).coeff 0 = 1 := by
    rw [shellBinomPoly, Polynomial.finsetSum_coeff]
    rw [Finset.sum_eq_single 0]
    · simp
    · intro k _ hk
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by omega), mul_zero]
    · intro h
      exact absurd (Finset.mem_range.mpr hm) h
  rw [Polynomial.coeff_sub, hc, Polynomial.coeff_one]
  simp

theorem eval_shellDefectPoly_mul (m : ℕ) (x : ℝ) (w : ℂ) :
    w * (shellDefectPoly m x).eval w
      = (shellBinomPoly ((1 : ℝ) / 2) (m + 1) x).eval w - 1 := by
  have hz := coeff_zero_shellBinomPoly_sub_one ((1 : ℝ) / 2) (m + 1) x (by omega)
  have hid := Polynomial.X_mul_divX_add (shellBinomPoly ((1 : ℝ) / 2) (m + 1) x - 1)
  rw [hz, map_zero, add_zero] at hid
  have := congrArg (fun P : Polynomial ℂ => P.eval w) hid
  simp only [Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_one]
    at this
  rw [shellDefectPoly]
  exact this

/-- **The root defect as a truncated expansion of one order lower.** -/
theorem hasPolyExpansion_shellDefect (m : ℕ) (x : ℝ) {r : ℝ}
    (hxr : x ^ (2 : ℕ) * r ^ (2 : ℕ) ≤ 1 / 2) :
    HasPolyExpansion r (2 * m + 1)
      (cbinomAbsCoeff ((1 : ℝ) / 2) (m + 1) * |x| ^ (2 * (m + 1)))
      (shellDefect x) (shellDefectPoly m x) := by
  intro w hw
  have hbase := hasPolyExpansion_shellBinom_succ (α := (1 : ℝ) / 2) (by norm_num) m x hxr w hw
  rcases eq_or_ne w 0 with rfl | hw0
  · have hzero : shellDefect x 0 = 0 := by
      rw [shellDefect]
      simp
    have hpz : (shellDefectPoly m x).eval 0 = 0 := by
      rw [shellDefectPoly, ← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_divX,
        Polynomial.coeff_sub, coeff_odd_shellBinomPoly _ _ _ (by omega), Polynomial.coeff_one]
      norm_num
    rw [hzero, hpz]
    simp
  · have hnorm0 : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hw0
    have hsplit : shellDefect x w - (shellDefectPoly m x).eval w
        = ((1 + (x : ℂ) ^ (2 : ℕ) * w ^ (2 : ℕ)) ^ (((1 : ℝ) / 2 : ℝ) : ℂ)
            - (shellBinomPoly ((1 : ℝ) / 2) (m + 1) x).eval w) / w := by
      have hmul := eval_shellDefectPoly_mul m x w
      rw [shellDefect]
      have hstep : ((1 + (x : ℂ) ^ (2 : ℕ) * w ^ (2 : ℕ)) ^ (((1 : ℝ) / 2 : ℝ) : ℂ) - 1) / w
            - (shellDefectPoly m x).eval w
          = (((1 + (x : ℂ) ^ (2 : ℕ) * w ^ (2 : ℕ)) ^ (((1 : ℝ) / 2 : ℝ) : ℂ) - 1)
              - w * (shellDefectPoly m x).eval w) / w := by
        field_simp
      rw [hstep, hmul]
      congr 1
      ring
    rw [hsplit, norm_div]
    rw [div_le_iff₀ hnorm0]
    refine le_trans hbase (le_of_eq ?_)
    rw [show 2 * (m + 1) = (2 * m + 1) + 1 by ring, pow_succ]
    ring

end RootDefect

end

end GaloisForLFunctions.HTGeometry
