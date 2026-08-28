import GaloisForLFunctions.RHTower.XiRealAxisGrowth
import GaloisForLFunctions.RHTower.XiShiftLoewnerCriticalGenerator

/-!
# Euler-orbit atom factorization of the centered completed transform

The centered completed transform factors over the Euler half-plane as the Riemann zeta value
times one archimedean atom factor

`xiCentEulerAtomFactor w = π^(-1/4-w/2) · Γ(w/2 + 5/4) · (w - 1/2)`,

the transform of the single `n = 1` orbit atom of the theta source.  The atom factor is entire
and carries a zero at `w = 1/2`: the shadow of the zeta pole, the exact reason a single orbit
atom cannot be positivity-complete.

Truncating the orbit at two atoms destroys the imaginary-axis confinement of the zero set: the
two-atom truncation `(1 + 2^(-1/2-w))·atom` has an explicit zero on the vertical line
`Re w = -1/2`, at `w = -1/2 + (π/log 2)·i`, where the atom factor itself does not vanish.  This
is the exact finite witness that source-side truncation of the Euler orbit is incompatible with
the centered zero geometry.
-/

open Complex

namespace RHTower

noncomputable section

/-- Archimedean atom factor: the transform of the single `n = 1` orbit atom. -/
def xiCentEulerAtomFactor (w : ℂ) : ℂ :=
  ((Real.pi : ℝ) : ℂ) ^ (-(1 / 4 : ℂ) - w / 2) * Complex.Gamma (w / 2 + 5 / 4) * (w - 1 / 2)

/-- Away from `w = -1/2` the atom factor is the completed archimedean factor of the shifted
argument, with both pole factors displayed. -/
theorem xiCentEulerAtomFactor_eq_Gammaℝ {w : ℂ} (hw : w ≠ -(1 / 2)) :
    xiCentEulerAtomFactor w =
      (w + 1 / 2) * (w - 1 / 2) / 2 * Complex.Gammaℝ (w + 1 / 2) := by
  have hhalf : (w + 1 / 2) / 2 ≠ 0 := by
    intro h
    apply hw
    have := (div_eq_zero_iff.mp h).resolve_right (by norm_num)
    linear_combination this
  have hgamma : Complex.Gamma (w / 2 + 5 / 4) =
      (w + 1 / 2) / 2 * Complex.Gamma ((w + 1 / 2) / 2) := by
    have h := Complex.Gamma_add_one ((w + 1 / 2) / 2) hhalf
    rw [show (w + 1 / 2) / 2 + 1 = w / 2 + 5 / 4 by ring] at h
    exact h
  rw [xiCentEulerAtomFactor, hgamma, Complex.Gammaℝ_def,
    show -(w + 1 / 2) / 2 = -(1 / 4 : ℂ) - w / 2 by ring]
  ring

/-- **Euler-orbit factorization.**  On the half-plane `Re w > -1/2`, away from the center
`w = 1/2`, the centered completed transform is the zeta value at the shifted point times the
archimedean atom factor. -/
theorem xiCent_eq_riemannZeta_mul_eulerAtomFactor {w : ℂ}
    (hw : -(1 / 2) < w.re) (hw1 : w ≠ 1 / 2) :
    xiCent w = riemannZeta (w + 1 / 2) * xiCentEulerAtomFactor w := by
  have hs0 : (1 / 2 : ℂ) + w ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.zero_re] at hre
    norm_num at hre
    linarith
  have hs1 : (1 / 2 : ℂ) + w ≠ 1 := by
    intro h
    apply hw1
    linear_combination h
  have hwneg : w ≠ -(1 / 2) := by
    intro h
    rw [h] at hw
    simp at hw
  have hspos : 0 < ((1 / 2 : ℂ) + w).re := by
    simp only [Complex.add_re]
    norm_num
    linarith
  rw [xiCent, xi_eq_mul_completedRiemannZeta hs0 hs1,
    completedRiemannZeta_eq_Gammaℝ_mul hspos,
    xiCentEulerAtomFactor_eq_Gammaℝ hwneg,
    show (1 / 2 : ℂ) + w = w + 1 / 2 by ring]
  ring

/-- **Pole shadow.**  The single-atom factor vanishes at the center `w = 1/2`: the zero that
cancels the zeta pole in the completed product. -/
theorem xiCentEulerAtomFactor_half : xiCentEulerAtomFactor (1 / 2) = 0 := by
  unfold xiCentEulerAtomFactor
  norm_num

/-- Two-atom truncation of the Euler orbit. -/
def xiCentTwoAtomTruncation (w : ℂ) : ℂ :=
  (1 + (2 : ℂ) ^ (-(1 / 2 : ℂ) - w)) * xiCentEulerAtomFactor w

/-- The explicit off-axis point of the two-atom truncation. -/
def xiCentTwoAtomWitness : ℂ :=
  ⟨-(1 / 2), Real.pi / Real.log 2⟩

theorem xiCentTwoAtomWitness_re : xiCentTwoAtomWitness.re = -(1 / 2) := rfl

theorem xiCentTwoAtomWitness_im : xiCentTwoAtomWitness.im = Real.pi / Real.log 2 := rfl

theorem xiCentTwoAtomWitness_eq :
    xiCentTwoAtomWitness =
      -(1 / 2 : ℂ) + ((Real.pi / Real.log 2 : ℝ) : ℂ) * Complex.I := by
  unfold xiCentTwoAtomWitness
  rw [Complex.mk_eq_add_mul_I]
  push_cast
  ring

private theorem pi_div_log_two_ne_zero : Real.pi / Real.log 2 ≠ 0 :=
  div_ne_zero (ne_of_gt Real.pi_pos) (ne_of_gt (Real.log_pos (by norm_num)))

/-- The Dirichlet factor of the two-atom truncation equals `-1` at the witness point. -/
theorem two_cpow_at_xiCentTwoAtomWitness :
    (2 : ℂ) ^ (-(1 / 2 : ℂ) - xiCentTwoAtomWitness) = -1 := by
  have hbase : Complex.log (2 : ℂ) = ((Real.log 2 : ℝ) : ℂ) := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
      Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)]
  have hexp : -(1 / 2 : ℂ) - xiCentTwoAtomWitness =
      -(((Real.pi / Real.log 2 : ℝ) : ℂ) * Complex.I) := by
    rw [xiCentTwoAtomWitness_eq]
    ring
  have hlog2 : (Real.log 2 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hreal : Real.log 2 * (Real.pi / Real.log 2) = Real.pi := by
    field_simp
  have hprod : ((Real.log 2 : ℝ) : ℂ) * -(((Real.pi / Real.log 2 : ℝ) : ℂ) * Complex.I) =
      -(((Real.pi : ℝ) : ℂ) * Complex.I) := by
    calc ((Real.log 2 : ℝ) : ℂ) * -(((Real.pi / Real.log 2 : ℝ) : ℂ) * Complex.I) =
        -((((Real.log 2 * (Real.pi / Real.log 2) : ℝ)) : ℂ) * Complex.I) := by
          push_cast
          ring
      _ = -(((Real.pi : ℝ) : ℂ) * Complex.I) := by rw [hreal]
  rw [Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0), hexp, hbase, hprod,
    Complex.exp_neg, Complex.exp_pi_mul_I]
  norm_num

/-- The atom factor does not vanish at the witness point. -/
theorem xiCentEulerAtomFactor_witness_ne_zero :
    xiCentEulerAtomFactor xiCentTwoAtomWitness ≠ 0 := by
  unfold xiCentEulerAtomFactor
  refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
  · rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)]
    exact Complex.exp_ne_zero _
  · apply Complex.Gamma_ne_zero
    intro m h
    have hw : xiCentTwoAtomWitness = -(2 * (m : ℂ)) - 5 / 2 := by
      linear_combination 2 * h
    have him : Real.pi / Real.log 2 = (-(2 * (m : ℂ)) - 5 / 2).im := by
      rw [← hw, xiCentTwoAtomWitness_im]
    rw [show (-(2 * (m : ℂ)) - 5 / 2).im = 0 by simp] at him
    exact pi_div_log_two_ne_zero him
  · intro h
    have hw : xiCentTwoAtomWitness = 1 / 2 := by linear_combination h
    have him : Real.pi / Real.log 2 = (1 / 2 : ℂ).im := by
      rw [← hw, xiCentTwoAtomWitness_im]
    rw [show (1 / 2 : ℂ).im = 0 by simp] at him
    exact pi_div_log_two_ne_zero him

/-- **Truncation no-go witness.**  The two-atom truncation of the Euler orbit has an explicit
zero on the off-axis vertical line `Re w = -1/2` at which the atom factor itself is nonzero:
finite source-side truncation destroys the imaginary-axis confinement of the zero set. -/
theorem xiCentTwoAtomTruncation_witness_zero :
    xiCentTwoAtomWitness.re = -(1 / 2) ∧
      xiCentEulerAtomFactor xiCentTwoAtomWitness ≠ 0 ∧
      xiCentTwoAtomTruncation xiCentTwoAtomWitness = 0 := by
  refine ⟨xiCentTwoAtomWitness_re, xiCentEulerAtomFactor_witness_ne_zero, ?_⟩
  unfold xiCentTwoAtomTruncation
  rw [two_cpow_at_xiCentTwoAtomWitness]
  ring

end

end RHTower
