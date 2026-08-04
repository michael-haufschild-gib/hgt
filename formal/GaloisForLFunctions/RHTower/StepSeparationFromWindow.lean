import GaloisForLFunctions.RHTower.FloorAndLargeSelection
import GaloisForLFunctions.HTGeometry.CircleComparisonSeparation

/-!
# A floor quantified over an annulus cannot carry a separation

A growth separation carries a floor `ε` for a polynomial in the earlier states, and the quantity it
must dominate contains `log⁺ ε⁻¹`.  In the separation itself the floor is produced together with the
point, so it may be taken to be the value of the polynomial there.  An interface that instead
quantifies the floor universally — "for every point of the annulus and every floor at it, the
comparison holds" — asks for the comparison with `log⁺ ε⁻¹` arbitrarily large and the right side
fixed, and is therefore satisfied by no family at all.

The exponential cascade witnesses this: on a circle centred at the origin the maximum of `‖exp‖` sits
at the positive real point, whose modulus is the radius itself, and every positive number below that
radius is an admissible floor for the coordinate there.

The usable interface is the one carrying the floor on a whole circle,
`GaloisForLFunctions.HTGeometry.CircleComparison`, where the floor is part of the datum.
-/

namespace RHTower

open GaloisForLFunctions GaloisForLFunctions.HTGeometry

/-- The cascade whose every edge is the exponential. -/
noncomputable def expFamily : ℕ → ℂ → ℂ := fun _ => Complex.exp

/-- **No family satisfies an annulus comparison with a freely quantified floor.**  Already at the
first edge of the exponential cascade the required inequality fails, because the floor may be taken
below every positive number while the point and the right-hand side stay fixed. -/
theorem not_window_comparison :
    ¬ ∀ (m : ℕ) (A : MvPolynomial (Fin m) ℂ), A ≠ 0 → ∀ c : ℝ, 0 ≤ c →
      ∃ r : ℝ, 0 < r ∧
        ∀ (cen z : ℂ) (ε : ℝ), r ≤ ‖z - cen‖ → ‖z - cen‖ ≤ r + 1 → 0 < ε →
          ε ≤ ‖MvPolynomial.eval
            (fun j => prefixFamily (entireCascade expFamily) m j z) A‖ →
          (∀ w : ℂ, ‖w - cen‖ ≤ r →
            ‖entireCascade expFamily m w‖ ≤ ‖entireCascade expFamily m z‖) →
          c * (1 + (∑ j : Fin m,
              Real.posLog ‖prefixFamily (entireCascade expFamily) m j z‖)
              + Real.posLog ε⁻¹)
            < Real.posLog ‖entireCascade expFamily m z‖ := by
  intro h
  obtain ⟨r, hr, hcomp⟩ :=
    h 1 (MvPolynomial.X 0) (MvPolynomial.X_ne_zero 0) 1 zero_le_one
  set z : ℂ := ((r : ℝ) : ℂ) with hzdef
  have hznorm : ‖z‖ = r := by
    rw [hzdef, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  have hzsub : ‖z - 0‖ = r := by rw [sub_zero, hznorm]
  set ε : ℝ := min r (Real.exp (-(r + 2 + Real.posLog r))) with hεdef
  have hε0 : 0 < ε := lt_min hr (Real.exp_pos _)
  have heval : MvPolynomial.eval
      (fun j => prefixFamily (entireCascade expFamily) 1 j z)
      (MvPolynomial.X (0 : Fin 1)) = z := by
    simp [prefixFamily]
  have hfloor : ε ≤ ‖MvPolynomial.eval
      (fun j => prefixFamily (entireCascade expFamily) 1 j z)
      (MvPolynomial.X (0 : Fin 1))‖ := by
    rw [heval, hznorm]
    exact min_le_left _ _
  have hexp1 : ∀ w : ℂ, ‖entireCascade expFamily 1 w‖ = Real.exp w.re := by
    intro w
    simp [expFamily, Complex.norm_exp]
  have hdom : ∀ w : ℂ, ‖w - 0‖ ≤ r →
      ‖entireCascade expFamily 1 w‖ ≤ ‖entireCascade expFamily 1 z‖ := by
    intro w hw
    have hw' : ‖w‖ ≤ r := by rwa [sub_zero] at hw
    rw [hexp1 w, hexp1 z]
    have hzre : z.re = r := by rw [hzdef, Complex.ofReal_re]
    rw [hzre]
    exact Real.exp_le_exp.mpr (le_trans (Complex.re_le_norm w) hw')
  have hkey := hcomp 0 z ε (le_of_eq hzsub.symm) (by rw [hzsub]; linarith) hε0 hfloor hdom
  -- the right-hand side is the radius
  have hrhs : Real.posLog ‖entireCascade expFamily 1 z‖ = r := by
    have hzre : z.re = r := by rw [hzdef, Complex.ofReal_re]
    rw [hexp1 z, hzre, Real.posLog_apply, Real.log_exp]
    exact max_eq_right hr.le
  -- the left-hand side already exceeds it through the floor term alone
  have hsum : (∑ j : Fin 1,
      Real.posLog ‖prefixFamily (entireCascade expFamily) 1 j z‖) = Real.posLog r := by
    rw [Fin.sum_univ_one]
    have : prefixFamily (entireCascade expFamily) 1 0 z = z := by simp [prefixFamily]
    rw [this, hznorm]
  have hlogε : Real.log ε ≤ -(r + 2 + Real.posLog r) := by
    have h1 : ε ≤ Real.exp (-(r + 2 + Real.posLog r)) := min_le_right _ _
    have h2 := Real.log_le_log hε0 h1
    rwa [Real.log_exp] at h2
  have hpl : r + 2 + Real.posLog r ≤ Real.posLog ε⁻¹ := by
    have h2 : Real.log ε⁻¹ ≤ Real.posLog ε⁻¹ := by
      rw [Real.posLog_apply]
      exact le_max_right _ _
    rw [Real.log_inv] at h2
    linarith
  rw [hsum, hrhs] at hkey
  have hp0 : (0 : ℝ) ≤ Real.posLog r := Real.posLog_nonneg
  linarith

end RHTower
