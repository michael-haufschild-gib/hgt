import GaloisForLFunctions.HTGeometry.ComplexC2Laplacian
import GaloisForLFunctions.HTGeometry.ComplexLaplacianGreenIdentity
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Positive radial curvature and compact source testing

The regularized logarithmic potential has an explicit positive Laplacian.
Holomorphic pullback scales it by the squared derivative. Green's identity
needs compact support only on the test, so the source potential can be entire.
-/

open Complex MeasureTheory Filter Set Laplacian InnerProductSpace
open scoped Laplacian Topology

noncomputable section
namespace GaloisForLFunctions.ConjugateDiagonalGeometry

/-- Smooth logarithmic potential with a positive squared-amplitude regulator. -/
def radialLogPotential (ε : ℝ) (z : ℂ) : ℝ :=
  (1 / 2) * Real.log (z.re ^ 2 + z.im ^ 2 + ε)

private theorem radial_den_pos {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    0 < z.re ^ 2 + z.im ^ 2 + ε :=
  add_pos_of_nonneg_of_pos (add_nonneg (sq_nonneg _) (sq_nonneg _)) hε

theorem contDiff_radialLogPotential {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ 2 (radialLogPotential ε) := by
  exact contDiff_const.mul
    (((Complex.reCLM.contDiff.pow 2).add (Complex.imCLM.contDiff.pow 2)).add
      contDiff_const |>.log fun z => (radial_den_pos hε z).ne')

private theorem radial_first {ε : ℝ} (hε : 0 < ε) (z v : ℂ) :
    fderiv ℝ (radialLogPotential ε) z v =
      (z.re * v.re + z.im * v.im) / (z.re ^ 2 + z.im ^ 2 + ε) := by
  have hq := ((Complex.reCLM.hasFDerivAt (x := z)).pow 2).add
    ((Complex.imCLM.hasFDerivAt (x := z)).pow 2) |>.add_const ε
  have hd := (hq.log (radial_den_pos hε z).ne').const_mul (1 / 2)
  change HasFDerivAt (radialLogPotential ε) _ z at hd
  rw [hd.fderiv]
  norm_num only [smul_apply, add_apply, Pi.add_apply, Function.comp_apply,
    Complex.reCLM_apply, Complex.imCLM_apply, smul_eq_mul, nsmul_eq_mul, pow_one]
  ring

private theorem radial_second {ε : ℝ} (hε : 0 < ε) (z v : ℂ) :
    Bottcher.dderiv (radialLogPotential ε) v z =
      ((v.re ^ 2 + v.im ^ 2) * (z.re ^ 2 + z.im ^ 2 + ε) -
        2 * (z.re * v.re + z.im * v.im) ^ 2) /
          (z.re ^ 2 + z.im ^ 2 + ε) ^ 2 := by
  have he : (fun w => fderiv ℝ (radialLogPotential ε) w v) =
      fun w : ℂ => (w.re * v.re + w.im * v.im) /
        (w.re ^ 2 + w.im ^ 2 + ε) := by
    funext w
    exact radial_first hε w v
  have hn := ((Complex.reCLM.hasFDerivAt (x := z)).mul_const v.re).add
    ((Complex.imCLM.hasFDerivAt (x := z)).mul_const v.im)
  have hq := ((Complex.reCLM.hasFDerivAt (x := z)).pow 2).add
    ((Complex.imCLM.hasFDerivAt (x := z)).pow 2) |>.add_const ε
  have hi := (hasDerivAt_inv (radial_den_pos hε z).ne').comp_hasFDerivAt z hq
  rw [Bottcher.dderiv, he]
  simp_rw [div_eq_mul_inv]
  have hd := hn.mul hi
  change HasFDerivAt (fun w : ℂ => (w.re * v.re + w.im * v.im) *
    (w.re ^ 2 + w.im ^ 2 + ε)⁻¹) _ z at hd
  rw [hd.fderiv]
  norm_num only [smul_apply, add_apply, sub_apply, Pi.add_apply, Function.comp_apply,
    Complex.reCLM_apply, Complex.imCLM_apply,
    smul_eq_mul, nsmul_eq_mul, pow_one]
  field_simp [(radial_den_pos hε z).ne']
  ring

/-- The regulator produces nonnegative curvature even where the unregularized log is singular. -/
theorem laplacian_radialLogPotential {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    Δ (radialLogPotential ε) z =
      2 * ε / (Complex.normSq z + ε) ^ 2 := by
  rw [Bottcher.laplacian_eq_dderiv _ (contDiff_radialLogPotential hε),
    radial_second hε, radial_second hε]
  simp only [Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im,
    one_pow, zero_pow (by norm_num : 2 ≠ 0), mul_one, mul_zero,
    add_zero, zero_add, Complex.normSq_apply]
  ring

private theorem complex_laplacian_eq {f : ℂ → ℂ} (hf : ContDiff ℝ 2 f) (z : ℂ) :
    HTGeometry.ComplexC2Laplacian.laplacian f z = Δ f z := by
  rw [laplacian_eq_iteratedFDeriv_complexPlane]
  have key (v : ℂ) :
      fderiv ℝ (fun w => fderiv ℝ f w v) z v =
        iteratedFDeriv ℝ 2 f z ![v, v] := by
    rw [iteratedFDeriv_two_apply]
    have hd := ((hf.fderiv_right (m := 1) (by norm_num)).differentiable
      (by norm_num) z).hasFDerivAt
    simpa using congrArg (fun L => L v) (hd.clm_apply (hasFDerivAt_const v z)).fderiv
  exact congrArg₂ (· + ·) (key 1) (key Complex.I)

/-- Conformal pullback of a real source potential, in the standard planar Laplacian. -/
theorem laplacian_real_holomorphic_comp (u : ℂ → ℝ) (g : ℂ → ℂ)
    (hu : ContDiff ℝ 2 u) (hg : Differentiable ℂ g) (z : ℂ) :
    Δ (u ∘ g) z = Complex.normSq (deriv g z) * Δ u (g z) := by
  have hgc : ContDiff ℂ 2 g := hg.contDiff
  have hgr : ContDiff ℝ 2 g := hgc.restrict_scalars ℝ
  have huc : ContDiff ℝ 2 (Complex.ofRealCLM ∘ u) := Complex.ofRealCLM.contDiff.comp hu
  have hc := HTGeometry.ComplexC2Laplacian.laplacian_holomorphic_comp
    (f := Complex.ofRealCLM ∘ u) (g := g) (z := z) huc.contDiffAt hgc.contDiffAt
  rw [complex_laplacian_eq (huc.comp hgr), complex_laplacian_eq huc] at hc
  have hleft := (hu.comp hgr).contDiffAt.laplacian_CLM_comp_left
    (l := Complex.ofRealCLM) (x := z)
  have hright := hu.contDiffAt.laplacian_CLM_comp_left
    (l := Complex.ofRealCLM) (x := g z)
  change Δ (Complex.ofRealCLM ∘ (u ∘ g)) z = _ at hc
  rw [hleft, hright] at hc
  change ((Δ (u ∘ g) z : ℝ) : ℂ) =
    (Complex.normSq (deriv g z) : ℂ) * ((Δ u (g z) : ℝ) : ℂ) at hc
  exact_mod_cast hc

private theorem source_second_green (u φ : ℂ → ℝ)
    (hu : ContDiff ℝ 2 u) (hφ : ContDiff ℝ 2 φ)
    (hc : HasCompactSupport φ) (v : ℂ) :
    (∫ z, φ z * Bottcher.dderiv u v z) =
      ∫ z, Bottcher.dderiv φ v z * u z := by
  let Du := fun z => fderiv ℝ u z v
  let Dφ := fun z => fderiv ℝ φ z v
  have hDu : ContDiff ℝ 1 Du :=
    (hu.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hDφ : ContDiff ℝ 1 Dφ :=
    (hφ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hDDu : Continuous (fun z => fderiv ℝ Du z v) :=
    (hDu.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hDDφ : Continuous (fun z => fderiv ℝ Dφ z v) :=
    (hDφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hcD : HasCompactSupport Dφ := hc.fderiv_apply ℝ v
  have hcDD : HasCompactSupport (fun z => fderiv ℝ Dφ z v) := hcD.fderiv_apply ℝ v
  have hi : Integrable (fun z => Dφ z * Du z) :=
    (hDφ.continuous.mul hDu.continuous).integrable_of_hasCompactSupport
    hcD.mul_right
  have hfirst := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure ℂ)) (f := φ) (g := Du) (v := v) hi
    ((hφ.continuous.mul hDDu).integrable_of_hasCompactSupport hc.mul_right)
    ((hφ.continuous.mul hDu.continuous).integrable_of_hasCompactSupport hc.mul_right)
    (fun z _ => hφ.differentiable (by norm_num) z)
    (fun z _ => hDu.differentiable (by norm_num) z)
  have hsecond := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure ℂ)) (f := Dφ) (g := u) (v := v)
    ((hDDφ.mul hu.continuous).integrable_of_hasCompactSupport hcDD.mul_right) hi
    ((hDφ.continuous.mul hu.continuous).integrable_of_hasCompactSupport hcD.mul_right)
    (fun z _ => hDφ.differentiable (by norm_num) z)
    (fun z _ => hu.differentiable (by norm_num) z)
  change (∫ z, φ z * fderiv ℝ Du z v) = ∫ z, fderiv ℝ Dφ z v * u z
  rw [hfirst, hsecond, neg_neg]

/-- The test localizes both Green integrals; no decay condition is needed on the source. -/
theorem source_green_identity (u φ : ℂ → ℝ)
    (hu : ContDiff ℝ 2 u) (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
    (∫ z, φ z * Δ u z) = ∫ z, Δ φ z * u z := by
  have hcont (q : ℂ → ℝ) (hq : ContDiff ℝ 2 q) (v : ℂ) :
      Continuous (Bottcher.dderiv q v) := by
    have hd : ContDiff ℝ 1 (fun z => fderiv ℝ q z v) :=
      (hq.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
    exact (hd.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hi (v : ℂ) : Integrable (fun z => φ z * Bottcher.dderiv u v z) :=
    (hφ.continuous.mul (hcont u hu v)).integrable_of_hasCompactSupport hc.mul_right
  have hj (v : ℂ) : Integrable (fun z => Bottcher.dderiv φ v z * u z) :=
    ((hcont φ hφ v).mul hu.continuous).integrable_of_hasCompactSupport
      ((hc.fderiv_apply ℝ v).fderiv_apply ℝ v).mul_right
  simp_rw [Bottcher.laplacian_eq_dderiv _ hu,
    Bottcher.laplacian_eq_dderiv _ hφ, mul_add, add_mul]
  rw [integral_add (hi 1) (hi Complex.I), integral_add (hj 1) (hj Complex.I),
    source_second_green u φ hu hφ hc 1, source_second_green u φ hu hφ hc Complex.I]

end GaloisForLFunctions.ConjugateDiagonalGeometry
