import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Uniqueness at the singular origin of the hyperbolic radial equation

For a positive real eigenvalue, a smooth zero-trace solution vanishes on the
nonnegative ray. The equation itself forces zero initial derivative. Its energy
has nonpositive derivative away from zero, and continuity closes the endpoint.
-/

open Set Topology
open scoped ContDiff
namespace GaloisForLFunctions.HTGeometry.HyperbolicRadialODE
noncomputable section

variable {u : ℝ → ℂ} {lam : ℝ}

private theorem deriv_initial (hu : ContDiff ℝ ∞ u)
    (hODE : ∀ r, 0 < r → (Real.sinh r : ℂ) * deriv (deriv u) r +
      (Real.cosh r : ℂ) * deriv u r + (lam : ℂ) * (Real.sinh r : ℂ) * u r = 0) :
    deriv u 0 = 0 := by
  have hu1 := (contDiff_infty_iff_deriv.mp hu).2
  have hu2 := (contDiff_infty_iff_deriv.mp hu1).2
  have hc : Continuous (fun r => (Real.sinh r : ℂ) * deriv (deriv u) r +
      (Real.cosh r : ℂ) * deriv u r + (lam : ℂ) * (Real.sinh r : ℂ) * u r) := by
    fun_prop
  have he : EqOn (fun r => (Real.sinh r : ℂ) * deriv (deriv u) r +
      (Real.cosh r : ℂ) * deriv u r + (lam : ℂ) * (Real.sinh r : ℂ) * u r)
      (fun _ => 0) (Ioi 0) := hODE
  have hz := he.closure hc continuous_const (by simp : (0 : ℝ) ∈ closure (Ioi (0 : ℝ)))
  simpa only [Real.sinh_zero, Real.cosh_zero, Complex.ofReal_zero, Complex.ofReal_one,
    zero_mul, one_mul, mul_zero, add_zero, zero_add] using hz

private theorem energy_deriv (hu : ContDiff ℝ ∞ u)
    (hODE : ∀ r, 0 < r → (Real.sinh r : ℂ) * deriv (deriv u) r +
      (Real.cosh r : ℂ) * deriv u r + (lam : ℂ) * (Real.sinh r : ℂ) * u r = 0)
    {r : ℝ} (hr : 0 < r) :
    deriv (fun t => ‖deriv u t‖^(2 : ℕ) + lam * ‖u t‖^(2 : ℕ)) r =
      -2 * (Real.cosh r / Real.sinh r) * ‖deriv u r‖^(2 : ℕ) := by
  have hu1 := (contDiff_infty_iff_deriv.mp hu).2
  have hs : (Real.sinh r : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sinh_pos_iff.mpr hr).ne'
  have hsecond : deriv (deriv u) r =
      (-(Real.cosh r / Real.sinh r)) • deriv u r - lam • u r := by
    apply mul_left_cancel₀ hs
    simp only [Complex.real_smul, Complex.ofReal_neg, Complex.ofReal_div]
    field_simp
    linear_combination hODE r hr
  have hh := ((hu1.differentiable (by simp) r).hasDerivAt.norm_sq).add
    (((hu.differentiable (by simp) r).hasDerivAt.norm_sq).const_mul lam)
  simp only [Pi.add_def] at hh
  rw [hh.deriv, hsecond]
  simp only [inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq]
  rw [real_inner_comm (u r) (deriv u r)]
  ring

/-- A regular solution of the positive radial eigen-equation is determined by its value at zero. -/
theorem eq_zero_of_initial (hlam : 0 < lam) (hu : ContDiff ℝ ∞ u)
    (hODE : ∀ r, 0 < r → (Real.sinh r : ℂ) * deriv (deriv u) r +
      (Real.cosh r : ℂ) * deriv u r + (lam : ℂ) * (Real.sinh r : ℂ) * u r = 0)
    (hzero : u 0 = 0) : ∀ r, 0 ≤ r → u r = 0 := by
  have hu1 := (contDiff_infty_iff_deriv.mp hu).2
  have hE : ContDiff ℝ ∞ (fun t => ‖deriv u t‖^(2 : ℕ) + lam * ‖u t‖^(2 : ℕ)) :=
    (hu1.norm_sq ℝ).add (contDiff_const.mul (hu.norm_sq ℝ))
  have hanti : AntitoneOn (fun t => ‖deriv u t‖^(2 : ℕ) + lam * ‖u t‖^(2 : ℕ)) (Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0) hE.continuous.continuousOn
      (hE.differentiable (by simp)).differentiableOn
    intro r hr
    have hr' : 0 < r := by simpa only [interior_Ici, mem_Ioi] using hr
    rw [energy_deriv hu hODE hr']
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (by norm_num)
        (div_nonneg (Real.cosh_pos r).le (Real.sinh_pos_iff.mpr hr').le)) (sq_nonneg _)
  intro r hr
  have hle := hanti (show (0 : ℝ) ∈ Ici 0 by simp) hr hr
  dsimp only at hle
  rw [deriv_initial hu hODE, hzero, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    mul_zero, zero_add] at hle
  have hsq : ‖u r‖^(2 : ℕ) ≤ 0 := (mul_le_mul_iff_left₀ hlam).mp (by
    nlinarith [sq_nonneg ‖deriv u r‖])
  have hn : ‖u r‖ = 0 := by nlinarith [norm_nonneg (u r)]
  exact norm_eq_zero.mp hn

end
end GaloisForLFunctions.HTGeometry.HyperbolicRadialODE
