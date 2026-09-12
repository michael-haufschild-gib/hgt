import GaloisForLFunctions.RHTower.MaassCircleDifferential
import GaloisForLFunctions.HTGeometry.SmoothAngularAverage
import GaloisForLFunctions.HTGeometry.HyperbolicRadialODE

/-!
# Scalar circular averaging of the actual Maass eigenform

The original Maass equation and the actual hyperbolic circle chart give
Darboux's radial ODE after compact angular integration. Positive radial energy
uniqueness then shows that equal eigenvalues have the same circular multiplier,
independently of the base point and of the eigenform. No scalar averaging law
is an input. The multiplier is smooth and equals one at radius zero.

This closes the circular-mean step of the proposed compact-kernel smooth-vector
construction. Haar polar integration, the Hilbert generator domains, and
arithmetic exclusion of complementary representations remain separate tasks.
-/

open UpperHalfPlane
open scoped ContDiff
namespace GaloisForLFunctions.RHTower.MaassCircle
open MaassSmooth HTGeometry.SmoothAngularAverage
noncomputable section

def mean (f : FunctionSpace) (z : ℍ) (r : ℝ) : ℂ :=
  average (fun theta => f (circlePoint r theta z))

theorem mean_smooth (f : FunctionSpace) (z : ℍ) : ContDiff ℝ ∞ (mean f z) :=
  average_smooth (circle_source_smooth f z)

@[simp] theorem mean_zero (f : FunctionSpace) (z : ℍ) : mean f z 0 = f z := by
  simp only [mean, circlePoint_zero, average_const]

private theorem radial_first_continuous {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ ∞ F) (r : ℝ) :
    Continuous (fun theta => deriv (fun t => F (t,theta)) r) := by
  have he : (fun theta => deriv (fun t => F (t,theta)) r) =
      fun theta => radialPartial F (r,theta) :=
    funext fun theta => (slice_hasDerivAt hF r theta).deriv
  rw [he]
  exact (partial_smooth hF).continuous.comp (continuous_const.prodMk continuous_id)

private theorem radial_second_continuous {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ ∞ F) (r : ℝ) :
    Continuous (fun theta => deriv (deriv (fun t => F (t,theta))) r) := by
  have he (theta : ℝ) : deriv (fun t => F (t,theta)) =
      fun t => radialPartial F (t,theta) :=
    funext fun t => (slice_hasDerivAt hF t theta).deriv
  simp only [he]
  exact radial_first_continuous (partial_smooth hF) r

/-- Darboux's equation for the circular mean of the specified original Maass form. -/
theorem mean_polar {Γ : Subgroup SL2R} {lam : ℝ}
    (f : MaassCuspEigenform Γ lam) (z : ℍ) (r : ℝ) :
    (Real.sinh r : ℂ)^2 * deriv (deriv (mean (ofMaass f) z)) r +
      (Real.sinh r : ℂ)*(Real.cosh r : ℂ)*deriv (mean (ofMaass f) z) r =
      -(Real.sinh r : ℂ)^2*(lam : ℂ)*mean (ofMaass f) z r := by
  let F : ℝ × ℝ → ℂ := fun p => f.1.1 (circlePoint p.1 p.2 z)
  have hF : ContDiff ℝ ∞ F := circle_source_smooth (ofMaass f) z
  have hA : ContDiff ℝ ∞ (fun theta => F (r,theta)) :=
    hF.comp (contDiff_const.prodMk contDiff_id)
  have hA1 := (contDiff_infty_iff_deriv.mp hA).2
  have hA2 := (contDiff_infty_iff_deriv.mp hA1).2
  have hp (theta : ℝ) : F (r,theta+2*Real.pi) = F (r,theta) := by
    simp only [F, circlePoint_periodic]
  have hang : average (deriv (deriv (fun theta => F (r,theta)))) = 0 :=
    average_periodic_deriv hA1 (periodic_deriv hA hp)
  have hpoint : (fun theta =>
      (Real.sinh r : ℂ)^2 * deriv (deriv (fun t => F (t,theta))) r +
      (Real.sinh r : ℂ)*(Real.cosh r : ℂ)*deriv (fun t => F (t,theta)) r +
      deriv (deriv (fun t => F (r,t))) theta) =
      fun theta => -(Real.sinh r : ℂ)^2*(lam : ℂ)*F (r,theta) :=
    funext fun theta => maass_circle_polar f r theta z
  have h := congrArg average hpoint
  have hc1 : Continuous (fun theta =>
      (Real.sinh r : ℂ)^2 * deriv (deriv (fun t => F (t,theta))) r) :=
    (radial_second_continuous hF r).const_mul _
  have hc2 : Continuous (fun theta =>
      (Real.sinh r : ℂ)*(Real.cosh r : ℂ)*deriv (fun t => F (t,theta)) r) :=
    (radial_first_continuous hF r).const_mul _
  have hav := average_add (hc1.add hc2) hA2.continuous
  have hav2 := average_add hc1 hc2
  simp only [Pi.add_def] at hav hav2
  rw [hav, hav2, hang, average_const_mul, average_const_mul, average_const_mul,
    add_zero, ← average_second hF r, ← average_deriv hF r] at h
  exact h

theorem mean_radial_equation {Γ : Subgroup SL2R} {lam : ℝ}
    (f : MaassCuspEigenform Γ lam) (z : ℍ) {r : ℝ} (hr : 0 < r) :
    (Real.sinh r : ℂ) * deriv (deriv (mean (ofMaass f) z)) r +
      (Real.cosh r : ℂ)*deriv (mean (ofMaass f) z) r +
      (lam : ℂ)*(Real.sinh r : ℂ)*mean (ofMaass f) z r = 0 := by
  have hs : (Real.sinh r : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sinh_pos_iff.mpr hr).ne'
  apply (mul_eq_zero.mp (show (Real.sinh r : ℂ) *
    ((Real.sinh r : ℂ) * deriv (deriv (mean (ofMaass f) z)) r +
      (Real.cosh r : ℂ)*deriv (mean (ofMaass f) z) r +
      (lam : ℂ)*(Real.sinh r : ℂ)*mean (ofMaass f) z r) = 0 from ?_)).resolve_left hs
  linear_combination mean_polar f z r

/-- Equal positive eigenvalues give the same circular multiplier on the actual sources. -/
theorem mean_cross_mul {Γ Γ' : Subgroup SL2R} {lam : ℝ} (hlam : 0 < lam)
    (f : MaassCuspEigenform Γ lam) (g : MaassCuspEigenform Γ' lam)
    (z w : ℍ) (r : ℝ) (hr : 0 ≤ r) :
    g.1.1 w * mean (ofMaass f) z r = f.1.1 z * mean (ofMaass g) w r := by
  let u : ℝ → ℂ := fun t =>
    g.1.1 w * mean (ofMaass f) z t - f.1.1 z * mean (ofMaass g) w t
  have hf := mean_smooth (ofMaass f) z
  have hg := mean_smooth (ofMaass g) w
  have hu : ContDiff ℝ ∞ u :=
    (contDiff_const.mul hf).sub (contDiff_const.mul hg)
  have hfirst : deriv u = fun t => g.1.1 w * deriv (mean (ofMaass f) z) t -
      f.1.1 z * deriv (mean (ofMaass g) w) t := by
    funext t
    exact (((hf.differentiable (by simp) t).hasDerivAt.const_mul _).sub
      ((hg.differentiable (by simp) t).hasDerivAt.const_mul _)).deriv
  have hsecond (t : ℝ) : deriv (deriv u) t =
      g.1.1 w * deriv (deriv (mean (ofMaass f) z)) t -
      f.1.1 z * deriv (deriv (mean (ofMaass g) w)) t := by
    rw [hfirst]
    exact ((((contDiff_infty_iff_deriv.mp hf).2.differentiable (by simp) t).hasDerivAt.const_mul _).sub
      (((contDiff_infty_iff_deriv.mp hg).2.differentiable (by simp) t).hasDerivAt.const_mul _)).deriv
  have hODE (t : ℝ) (ht : 0 < t) :
      (Real.sinh t : ℂ) * deriv (deriv u) t + (Real.cosh t : ℂ) * deriv u t +
      (lam : ℂ)*(Real.sinh t : ℂ)*u t = 0 := by
    rw [hsecond, hfirst]
    dsimp only [u]
    linear_combination g.1.1 w * mean_radial_equation f z ht -
      f.1.1 z * mean_radial_equation g w ht
  have hz : u 0 = 0 := by simp only [u, mean_zero, ofMaass_apply]; ring
  exact sub_eq_zero.mp (HTGeometry.HyperbolicRadialODE.eq_zero_of_initial hlam hu hODE hz r hr)

/-- The actual circular averaging operator acts by a scalar on the original eigenform. -/
theorem exists_mean_multiplier {Γ : Subgroup SL2R} {lam : ℝ} (hlam : 0 < lam)
    (f : MaassCuspEigenform Γ lam) :
    ∃ phi : ℝ → ℂ, ContDiff ℝ ∞ phi ∧ phi 0 = 1 ∧
      ∀ z r, 0 ≤ r → mean (ofMaass f) z r = phi r * f.1.1 z := by
  have hn : ∃ w : ℍ, f.1.1 w ≠ 0 := by
    by_contra h
    push Not at h
    apply f.2.1
    apply Subtype.ext
    funext w
    exact h w
  obtain ⟨w, hw⟩ := hn
  refine ⟨fun r => (f.1.1 w)⁻¹ * mean (ofMaass f) w r,
    contDiff_const.mul (mean_smooth (ofMaass f) w), ?_, ?_⟩
  · simp only [mean_zero, ofMaass_apply, inv_mul_cancel₀ hw]
  · intro z r hr
    apply mul_left_cancel₀ hw
    have h := mean_cross_mul hlam f f z w r hr
    calc
      f.1.1 w * mean (ofMaass f) z r = f.1.1 z * mean (ofMaass f) w r := h
      _ = f.1.1 w * ((f.1.1 w)⁻¹ * mean (ofMaass f) w r * f.1.1 z) := by
        field_simp

end
end GaloisForLFunctions.RHTower.MaassCircle
