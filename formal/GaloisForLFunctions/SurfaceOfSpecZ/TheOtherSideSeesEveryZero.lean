import GaloisForLFunctions.SurfaceOfSpecZ.TheStepanovSideIsBlindToRealZeros
import GaloisForLFunctions.SquareRootThreshold.EveryWidthDecidesTheCriticalLine
import GaloisForLFunctions.SquareRootThreshold.OneParameterLagFamilyDeterminesTheConfiguration

/-!
# The other side sees every zero

`TheStepanovSideIsBlindToRealZeros`: a lower bound `2 Re S(u) ≥ −K`, an upper bound on the smoothed
point counts (Stepanov's side), cannot see a real zero; for `{¼, ¾}` it holds although the
configuration is off the line. The other side has no blind spot.

* `onLine_of_two_re_lagStructure_le`: for every tempered configuration in the open strip, an upper
  bound `2 Re S(u) ≤ K` for `u ≥ 0`, a lower bound on the smoothed point counts, puts every zero on
  the critical line.

A real zero `½ + x`, `x > 0`, enters `2 Re S` with the coefficient `2m B̂(−ix)² > 0`
(`evenCoeff_spline_pos_of_real`), so it can only push `S` up; the odd two-bump
`Re W(B − τ_v B) = 2 Re S(0) − 2 Re S(v)` then reads the width (`re_le_iff_lag_twoBump_ge_neg_exp_of_pos`).

On a curve over `𝔽_q` the asymmetry is the same: a bound `N_n ≥ qⁿ + 1 − Cq^{n/2}` for all `n` gives
RH by Pringsheim's theorem, since a real eigenvalue `α > √q` makes `Σ (Cq^{n/2} − a_n)Tⁿ` tend to
`−∞` at `T = 1/α`; a bound `N_n ≤ qⁿ + 1 + Cq^{n/2}` cannot exclude such an `α`. Stepanov's method
gives the blind side.
-/

open Complex
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri SquareRootThreshold Zeta23

/-- The spline transform is real on the imaginary axis. -/
theorem conj_paperFT_spline_imag (x : ℝ) :
    conj (paperFT (boxSpline 1 3) (-(I * x))) = paperFT (boxSpline 1 3) (-(I * x)) := by
  have h1 := conj_paperFT_boxSpline 1 3 (-(I * x))
  have hw : conj (-(I * (x : ℂ))) = -(-(I * (x : ℂ))) := by
    rw [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]; ring
  rw [hw, paperFT_boxSpline_neg] at h1
  exact h1

/-- **A real zero enters with a positive coefficient.** -/
theorem evenCoeff_spline_pos_of_real (Z : ZeroConfig) {x : ℂ} (hx : (1 / 2 + x) ∈ Z.carrier)
    (hxre : 0 < x.re) (him : x.im = 0) : 0 < (evenCoeff Z (boxSpline 1 3) x).re := by
  have hb := contDiff_boxSpline (r := 1) one_pos 2
  have hbc := hasCompactSupport_of_support_subset_abs (boxSpline_support (r := 1) one_pos 3)
  have hxr : x = (x.re : ℂ) := Complex.ext (by simp) (by simp [him])
  have hxc : conj x = x := by rw [hxr, Complex.conj_ofReal]
  have hlag := lagCoeff_eq_of_conj_symm Z hb.continuous hbc (conj_paperFT_boxSpline 1 3) hx
  set w := paperFT (boxSpline 1 3) (-(I * x)) with hwdef
  have hwreal : conj w = w := by rw [hwdef, hxr]; exact conj_paperFT_spline_imag x.re
  have hwim : w.im = 0 := by
    have := congrArg Complex.im hwreal
    simp only [Complex.conj_im] at this
    linarith
  have hw0 : w ≠ 0 := paperFT_boxSpline_ne_zero one_pos 3 (by simp; linarith)
  have hwre : w.re ≠ 0 := fun h => hw0 (Complex.ext h hwim)
  have hm : (0 : ℝ) < Z.mult (1 / 2 + x) := by
    have := Z.one_le_mult _ hx; exact_mod_cast (show 0 < Z.mult (1 / 2 + x) by omega)
  rw [evenCoeff, hxc, hlag]
  have hsq : (w ^ 2).re = w.re ^ 2 := by simp [sq, Complex.mul_re, hwim]
  have hsq_im : (w ^ 2).im = 0 := by simp [sq, Complex.mul_im, hwim]
  simp only [Complex.add_re, Complex.conj_re, Complex.mul_re, Complex.natCast_re,
    Complex.natCast_im, zero_mul, sub_zero, hsq]
  have : 0 < w.re ^ 2 := by positivity
  nlinarith

/-- **The other side sees every zero.** For every tempered configuration, an upper bound on the
spline lag structure puts every zero on the critical line, real zeros included. -/
theorem onLine_of_two_re_lagStructure_le (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hlt : ∀ ρ ∈ Z.carrier, ρ.re < 1) {K : ℝ}
    (hK : ∀ u : ℝ, 0 ≤ u → 2 * (lagStructure Z (boxSpline 1 3) u).re ≤ K) :
    ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2 := by
  have hb := contDiff_boxSpline (r := 1) one_pos 2
  have hbs := boxSpline_support (r := 1) one_pos 3
  have hbc := hasCompactSupport_of_support_subset_abs hbs
  have hsees : ∀ ρ ∈ Z.carrier, 1 / 2 < ρ.re → evenCoeff Z (boxSpline 1 3) (ρ - 1 / 2) ≠ 0 :=
    fun ρ hρ h => evenCoeff_sub_half_ne_zero_of_conj_symm Z hb.continuous hbc
      (conj_paperFT_boxSpline _ _) (paperFT_boxSpline_neg _ _) hρ
      (paperFT_boxSpline_ne_zero one_pos 3 (im_gammaOf_ne_zero (by linarith)))
  set A := 2 * (lagStructure Z (boxSpline 1 3) 0).re with hA
  have hrate : ∃ C V : ℝ, ∀ v : ℝ, V ≤ v → -(C * Real.exp (0 * v)) ≤
      (Z.W (twoBump (boxSpline 1 3) v (-1)) (twoBump (boxSpline 1 3) v (-1))).re := by
    refine ⟨|K| + |A|, 0, fun v hv => ?_⟩
    rw [re_W_lag_eq Z hZ hb hbs v, zero_mul, Real.exp_zero, mul_one, ← hA]
    have := hK v hv
    linarith [le_abs_self K, neg_abs_le A]
  have hre := (re_le_iff_lag_twoBump_ge_neg_exp_of_pos Z hZ hlt hb hbs
    (fun x hx hxre him => evenCoeff_spline_pos_of_real Z hx hxre him) hsees le_rfl).mpr hrate
  intro ρ hρ
  have h1 := hre ρ hρ
  have h2 := hre _ (Z.reflect_mem ρ hρ)
  have hrefl : (Zeta23.reflect ρ).re = 1 - ρ.re := by simp [Zeta23.reflect]
  rw [hrefl] at h2
  linarith

end GaloisForLFunctions.SurfaceOfSpecZ
