import GaloisForLFunctions.HTGeometry.ComplexAnalysis.PureJetAlgebra
import GaloisForLFunctions.HTGeometry.GaussBonnetPlanarPartials

/-!
# Trace-free second derivative under weighted inversion

For the weight `|z|²`, the first-derivative terms cancel after two
antiholomorphic derivatives. The remaining factor is `z / conj(z)³`,
whose angular part has degree four.
-/

open Complex Filter Topology
open scoped ComplexConjugate ContDiff
namespace GaloisForLFunctions.HilbertMetric.Geometry.WeightedKelvinWirtinger
open _root_.HTGeometry
noncomputable section

/-- The antiholomorphic chain rule under a holomorphic change of coordinate. -/
theorem dzbar_comp_holomorphic {f g : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f (g z)) (hg : DifferentiableAt ℂ g z) :
    dzbar (fun w => f (g w)) z = conj (deriv g z) * dzbar f (g z) := by
  change wirtingerAntihol (fderiv ℝ (f ∘ g) z) = _
  rw [fderiv_comp z hf (hg.restrictScalars ℝ), wirtingerAntihol]
  simp only [ContinuousLinearMap.comp_apply]
  rw [fderiv_real_apply_of_differentiableAt hg 1,
    fderiv_real_apply_of_differentiableAt hg I, mul_one,
    wirtinger_decomp (fderiv ℝ f (g z)) (deriv g z),
    wirtinger_decomp (fderiv ℝ f (g z)) (deriv g z * I)]
  simp only [map_mul, Complex.conj_I, mul_neg, dzbar]
  linear_combination (deriv g z * wirtingerHol (fderiv ℝ f (g z)) -
    conj (deriv g z) * wirtingerAntihol (fderiv ℝ f (g z))) / 2 * Complex.I_sq

private theorem dzbar_inv_comp {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z⁻¹) (hz : z ≠ 0) :
    dzbar (fun w => f w⁻¹) z = -(conj z)⁻¹ ^ 2 * dzbar f z⁻¹ := by
  rw [dzbar_comp_holomorphic hf (differentiableAt_inv hz), (hasDerivAt_inv hz).deriv]
  simp only [map_neg, map_inv₀, map_pow, inv_pow]

private theorem dzbar_conj (z : ℂ) : dzbar (fun w : ℂ => conj w) z = 1 := by
  have hd : HasFDerivAt (fun w : ℂ => conj w) Complex.conjCLE.toContinuousLinearMap z :=
    Complex.conjCLE.hasFDerivAt
  rw [dzbar_eq_of_hasFDerivAt hd]
  change (conj (1 : ℂ) + I * conj I) / 2 = 1
  simp only [map_one, Complex.conj_I, mul_neg, Complex.I_mul_I]
  norm_num

private theorem dzbar_conj_inv {z : ℂ} (hz : z ≠ 0) :
    dzbar (fun w : ℂ => (conj w)⁻¹) z = -(conj z)⁻¹ ^ 2 := by
  have he : (fun w : ℂ => (conj w)⁻¹) = fun w => conj w⁻¹ := by
    funext w
    exact (map_inv₀ (starRingEnd ℂ) w).symm
  have hiC : DifferentiableAt ℂ (fun w : ℂ => w⁻¹) z := differentiableAt_inv hz
  rw [he, dzbar_conjugate_of_differentiable (hiC.restrictScalars ℝ),
    (dzbar_eq_zero_of_differentiableAt hiC).2,
    (hasDerivAt_inv hz).deriv]
  simp only [map_neg, map_inv₀, map_pow, inv_pow]

/-- The weight times inversion, with its canonical zero value at the origin. -/
def weightedKelvin (f : ℂ → ℂ) (z : ℂ) : ℂ := z * (conj z * f z⁻¹)

/-- Exact first derivative before the cancellation in the Hessian. -/
theorem dzbar_weightedKelvin {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z⁻¹) (hz : z ≠ 0) :
    dzbar (weightedKelvin f) z = z * f z⁻¹ - z * (conj z)⁻¹ * dzbar f z⁻¹ := by
  have hiC : DifferentiableAt ℂ (fun w : ℂ => w⁻¹) z := differentiableAt_inv hz
  have hi : DifferentiableAt ℝ (fun w : ℂ => w⁻¹) z := hiC.restrictScalars ℝ
  have hc : DifferentiableAt ℝ (fun w => f w⁻¹) z := hf.comp z hi
  have hconj : DifferentiableAt ℝ (fun w : ℂ => conj w) z := Complex.conjCLE.differentiableAt
  have hprod : DifferentiableAt ℝ (fun w => conj w * f w⁻¹) z := hconj.mul hc
  change dzbar (fun w : ℂ => w * (conj w * f w⁻¹)) z = _
  rw [dzbar_holomorphic_mul (h := fun w : ℂ => w) differentiableAt_id hprod,
    dzbar_mul_at hconj hc, dzbar_conj, dzbar_inv_comp hf hz]
  have hb : conj z ≠ 0 := (map_ne_zero (starRingEnd ℂ)).mpr hz
  field_simp
  ring

private theorem dzbar_sub {f g : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    dzbar (fun w => f w - g w) z = dzbar f z - dzbar g z := by
  change dzbar (f - g) z = _
  rw [dzbar_eq_of_hasFDerivAt (hf.hasFDerivAt.sub hg.hasFDerivAt)]
  simp only [dzbar, wirtingerAntihol, sub_apply]
  ring

/-- The exact weighted inversion law for the actual trace-free Hessian. -/
theorem dzbar_twice_weightedKelvin {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f)
    {z : ℂ} (hz : z ≠ 0) :
    dzbar (dzbar (weightedKelvin f)) z =
      z / conj z ^ 3 * dzbar (dzbar f) z⁻¹ := by
  have hd : Differentiable ℝ f := hf.differentiable (by simp)
  have hbd : Differentiable ℝ (dzbar f) :=
    (contDiff_infty_dzbar hf).differentiable (by simp)
  have hiC : DifferentiableAt ℂ (fun w : ℂ => w⁻¹) z := differentiableAt_inv hz
  have hi : DifferentiableAt ℝ (fun w : ℂ => w⁻¹) z := hiC.restrictScalars ℝ
  have hci : DifferentiableAt ℝ (fun w : ℂ => (conj w)⁻¹) z :=
    Complex.conjCLE.differentiableAt.inv ((map_ne_zero (starRingEnd ℂ)).mpr hz)
  have hc : DifferentiableAt ℝ (fun w => f w⁻¹) z := (hd _).comp z hi
  have hbc : DifferentiableAt ℝ (fun w => dzbar f w⁻¹) z := (hbd _).comp z hi
  have he : dzbar (weightedKelvin f) =ᶠ[𝓝 z]
      (fun w => w * f w⁻¹ - w * (conj w)⁻¹ * dzbar f w⁻¹) := by
    filter_upwards [eventually_ne_nhds hz] with w hw
    exact dzbar_weightedKelvin (hd _) hw
  have he' := (iteratedDzbar_eventuallyEq he 1).self_of_nhds
  change dzbar (dzbar (weightedKelvin f)) z =
    dzbar (fun w => w * f w⁻¹ - w * (conj w)⁻¹ * dzbar f w⁻¹) z at he'
  have hA : DifferentiableAt ℝ (fun w => w * f w⁻¹) z := differentiableAt_id.mul hc
  have hB : DifferentiableAt ℝ (fun w => w * (conj w)⁻¹ * dzbar f w⁻¹) z :=
    (differentiableAt_id.mul hci).mul hbc
  rw [he', dzbar_sub hA hB,
    dzbar_holomorphic_mul (h := fun w : ℂ => w) differentiableAt_id hc]
  have hfactor : (fun w : ℂ => w * (conj w)⁻¹ * dzbar f w⁻¹) =
      fun w => w * ((conj w)⁻¹ * dzbar f w⁻¹) := by funext w; ring
  have hprod : DifferentiableAt ℝ (fun w => (conj w)⁻¹ * dzbar f w⁻¹) z := hci.mul hbc
  rw [hfactor, dzbar_holomorphic_mul (h := fun w : ℂ => w) differentiableAt_id hprod,
    dzbar_mul_at hci hbc, dzbar_conj_inv hz,
    dzbar_inv_comp (hd _) hz, dzbar_inv_comp (hbd _) hz]
  have hb : conj z ≠ 0 := (map_ne_zero (starRingEnd ℂ)).mpr hz
  field_simp
  ring

open GaloisForLFunctions.HTGeometry.GaussBonnet

/-- A real planar function viewed as a complex-valued function of one complex variable. -/
def complexLift (U : ℝ × ℝ → ℝ) (z : ℂ) : ℂ := U (z.re, z.im)

private theorem complexLift_smooth {U : ℝ × ℝ → ℝ} (hU : ContDiff ℝ ∞ U) :
    ContDiff ℝ ∞ (complexLift U) :=
  Complex.ofRealCLM.contDiff.comp (hU.comp Complex.equivRealProdCLM.contDiff)

private theorem dzbar_complexLift {U : ℝ × ℝ → ℝ} (hU : ContDiff ℝ ∞ U) (z : ℂ) :
    dzbar (complexLift U) z =
      ((px U (z.re, z.im) : ℂ) + I * (py U (z.re, z.im) : ℂ)) / 2 := by
  have hU' := (hU.differentiable (by simp) (z.re, z.im)).hasFDerivAt
  have hd := Complex.ofRealCLM.hasFDerivAt.comp z
    (hU'.comp z Complex.equivRealProdCLM.hasFDerivAt)
  change HasFDerivAt (complexLift U) _ z at hd
  rw [dzbar_eq_of_hasFDerivAt hd]
  rfl

private theorem dzbar_add {f g : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    dzbar (fun w => f w + g w) z = dzbar f z + dzbar g z := by
  change dzbar (f + g) z = _
  rw [dzbar_eq_of_hasFDerivAt (hf.hasFDerivAt.add hg.hasFDerivAt), wirtingerAntihol_add]
  rfl

/-- Twice antiholomorphic differentiation is exactly the complex trace-free real Hessian. -/
theorem four_dzbar_twice_complexLift {U : ℝ × ℝ → ℝ} (hU : ContDiff ℝ ∞ U) (z : ℂ) :
    4 * dzbar (dzbar (complexLift U)) z =
      ((px (px U) (z.re, z.im) - py (py U) (z.re, z.im) : ℝ) : ℂ) +
        2 * (py (px U) (z.re, z.im) : ℂ) * I := by
  have hx := complexLift_smooth (contDiff_px hU)
  have hy := complexLift_smooth (contDiff_py hU)
  have hxd := hx.differentiable (by simp) z
  have hyd := hy.differentiable (by simp) z
  have hfirst : dzbar (complexLift U) = fun w =>
      (1 / 2 : ℂ) * complexLift (px U) w + (I / 2) * complexLift (py U) w := by
    funext w
    rw [dzbar_complexLift hU]
    unfold complexLift
    ring
  have hmix : px (py U) (z.re, z.im) = py (px U) (z.re, z.im) := by
    have hd : DifferentiableAt ℝ (fderiv ℝ U) (z.re, z.im) :=
      (hU.fderiv_right (m := ∞) (by simp)).differentiable (by simp) _
    unfold px py
    rw [fderiv_clm_apply hd (differentiableAt_const _),
      fderiv_clm_apply hd (differentiableAt_const _)]
    have hs : fderiv ℝ (fderiv ℝ U) (z.re, z.im) (1, 0) (0, 1) =
        fderiv ℝ (fderiv ℝ U) (z.re, z.im) (0, 1) (1, 0) :=
      hU.contDiffAt.isSymmSndFDerivAt
        (by norm_num; exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)) (1, 0) (0, 1)
    simpa using hs
  have hx' : DifferentiableAt ℝ (fun w => (1 / 2 : ℂ) * complexLift (px U) w) z :=
    (differentiableAt_const _).mul hxd
  have hy' : DifferentiableAt ℝ (fun w => (I / 2) * complexLift (py U) w) z :=
    (differentiableAt_const _).mul hyd
  rw [hfirst, dzbar_add hx' hy',
    dzbar_holomorphic_mul (differentiableAt_const _) hxd,
    dzbar_holomorphic_mul (differentiableAt_const _) hyd,
    dzbar_complexLift (contDiff_px hU), dzbar_complexLift (contDiff_py hU), hmix]
  push_cast
  linear_combination (py (py U) (z.re, z.im) : ℂ) * Complex.I_sq

#print axioms four_dzbar_twice_complexLift
#print axioms dzbar_comp_holomorphic
#print axioms dzbar_weightedKelvin
#print axioms dzbar_twice_weightedKelvin
end
end GaloisForLFunctions.HilbertMetric.Geometry.WeightedKelvinWirtinger
