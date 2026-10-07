import GaloisForLFunctions.RHTower.XiLogDerivFarRight
import GaloisForLFunctions.RHTower.XiPolynomialLeftFactors
import GaloisForLFunctions.HTGeometry.HalfPlaneLogarithm
import GaloisForLFunctions.HTGeometry.HolomorphicExpandingInverse

/-!
# Logarithmic inverse disks arbitrarily far to the right of Xi

For every real exponential tilt and every bounded logarithmic disk, tilted
Xi admits a holomorphic exponential lift whose image lies beyond any given
real boundary. The real logarithmic derivative expands there; Schottky
value occurrence supplies a normalized center arbitrarily far right.
-/

open Complex Metric Set
open GaloisForLFunctions.HTGeometry

namespace RHTower

/-- Every logarithmic disk lifts holomorphically through tilted Xi beyond any real boundary. -/
theorem exists_xi_tilt_exp_lift_ball (a M R : ℝ) (hM : 0 < M) :
    ∃ h : ℂ → ℂ, DifferentiableOn ℂ h (ball 0 M) ∧
      ∀ w ∈ ball 0 M, R < (h w).re ∧
        xi (h w) * Complex.exp (-(a : ℂ) * h w) = Complex.exp w := by
  obtain ⟨B, hB2, hB⟩ := exists_re_logDeriv_xi_ge_halfPlane (a + 1)
  let T : ℝ := max B R
  let r : ℝ := 2 * M + 2
  have hr : 0 < r := by dsimp [r]; linarith
  have hT2 : 2 ≤ T := hB2.trans (le_max_left _ _)
  obtain ⟨b, hb, hfb⟩ := exists_xi_tilt_eq_of_nonzero a (T + r)
    (by linarith) (w := 1) one_ne_zero
  have hbT : T < b.re := by linarith
  let f : ℂ → ℂ := fun z => xi z * Complex.exp (-(a : ℂ) * z)
  let Φ : ℂ → ℂ := fun z => logDeriv xi z - (a : ℂ)
  have hnz : ∀ z : ℂ, T < z.re → xi z ≠ 0 :=
    fun z hz => xi_ne_zero_of_one_lt_re (by linarith)
  have hΦ : DifferentiableOn ℂ Φ {z : ℂ | T < z.re} := by
    intro z hz
    exact (((xi_differentiable.deriv z).div (xi_differentiable z) (hnz z hz)).sub_const
      (a : ℂ)).differentiableWithinAt
  have hfd : ∀ z : ℂ, T < z.re → HasDerivAt f (Φ z * f z) z := by
    intro z hz
    have hd := (xi_differentiable z).hasDerivAt.mul
      (((hasDerivAt_id z).const_mul (-(a : ℂ))).cexp)
    refine hd.congr_deriv ?_
    dsimp [Φ, f]
    rw [logDeriv_apply]
    field_simp [hnz z hz]
    ring
  obtain ⟨P, hPb, hPd, hPe⟩ := exists_halfPlane_exp_primitive hΦ hfd hbT hfb
  have hP : DifferentiableOn ℂ P {z : ℂ | T < z.re} :=
    fun z hz => (hPd z hz).differentiableAt.differentiableWithinAt
  have hPr : ∀ z ∈ {z : ℂ | T < z.re}, 1 ≤ (deriv P z).re := by
    intro z hz
    rw [(hPd z hz).deriv]
    change 1 ≤ (logDeriv xi z).re - a
    have := hB z ((le_max_left B R).trans hz.le)
    linarith
  have hball : closedBall b r ⊆ {z : ℂ | T < z.re} := by
    intro z hz
    have hnorm : ‖z - b‖ ≤ r := mem_closedBall_iff_norm.mp hz
    have hre := (Complex.abs_re_le_norm (z - b)).trans hnorm
    have hlow := (abs_le.mp hre).1
    simp only [Complex.sub_re] at hlow
    change T < z.re
    linarith
  obtain ⟨h, hhd, hh⟩ := exists_holomorphic_inverse_disk
    (isOpen_lt continuous_const Complex.continuous_re) (convex_halfSpace_re_gt T)
    hP hPr hr hball
  rw [hPb] at hhd hh
  have hsub : ball (0 : ℂ) M ⊆ ball 0 (r / 2) :=
    ball_subset_ball (by dsimp [r]; linarith)
  refine ⟨h, hhd.mono hsub, fun w hw => ?_⟩
  obtain ⟨hhT, hPh⟩ := hh w (hsub hw)
  refine ⟨(le_max_right B R).trans_lt hhT, ?_⟩
  change f (h w) = Complex.exp w
  rw [← hPe (h w) hhT, hPh]

end RHTower
