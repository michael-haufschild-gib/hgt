import GaloisForLFunctions.RHTower.WeilWorkDeficitGlobalMellinAmplitude
import GaloisForLFunctions.HTGeometry.BesselArgumentDerivative
import Mathlib.Analysis.MellinInversion

/-!
# Inverse Mellin recovery of the actual derivative product kernel

The finite Bessel polynomial is continuous at every positive argument.
Its actual Mellin transform satisfies both inversion integrability gates,
so inverse Mellin integration recovers the kernel exactly on `Re(s)=4`.
The global vertical norm bound gives an explicit spatial bound, uniformly
in derivative order with the sigma-four saddle normalization.

Critical-line asymptotics and spectral-deficit production remain open.
-/

noncomputable section
open MeasureTheory Set Complex
open GaloisForLFunctions.HTGeometry
open RHTower.WeilWorkDeficitPrimeKernel RHTower.WeilWorkDeficitMellin
open RHTower.WeilWorkDeficitAmplitude RHTower.WeilWorkDeficitGlobalAmplitude
namespace RHTower.WeilWorkDeficitInversion

private theorem continuous_bessel {x : ℝ} (hx : 0 < x) (nu : ℝ) :
    ContinuousAt (fun y : ℝ => realModifiedBesselKOrder y nu) x := by
  have hc := (d4BM_hasDerivAt_modifiedBesselKOrder_argument hx (nu:ℂ)).continuousAt
  apply (Complex.continuous_re.continuousAt.comp hc).congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hx] with y hy
  dsimp only [Function.comp_apply]
  rw [modifiedBesselKOrder_ofReal hy]
  rfl

private theorem continuous_kernel (k : ℕ) {x : ℝ} (hx : 0 < x) :
    ContinuousAt (fun y : ℝ => (productKernel k y:ℂ)) x := by
  have hb (j l : ℕ) : ContinuousAt (fun y : ℝ =>
      realModifiedBesselKOrder (2*Real.pi*y) ((j:ℝ)-l)) x :=
    (continuous_bessel (by positivity) _).comp (by fun_prop)
  unfold productKernel
  fun_prop

private theorem mellin_convergent (k : ℕ) :
    MellinConvergent (fun x : ℝ => (productKernel k x:ℂ)) 4 := by
  simpa only [MellinConvergent, smul_eq_mul] using
    productKernel_mellin_integrable k (s := 4) (by norm_num)

private theorem vertical_integrable (k : ℕ) :
    VerticalIntegrable (mellin (fun x : ℝ => (productKernel k x:ℂ))) 4 := by
  convert! integrable_verticalMellin k using 1

private theorem norm_inverse_weight (x : Ioi (0:ℝ)) (t : ℝ) :
    ‖(x:ℂ)^(-(4+(t:ℂ)*I))‖ = ((x:ℝ)^4)⁻¹ := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos x.property]
  norm_num
  exact zpow_ofNat (x:ℝ) 4

/-- Absolute inverse Mellin integration of the actual product kernel. -/
theorem integrable_inverseMellin (k : ℕ) (x : Ioi (0:ℝ)) :
    Integrable (fun t : ℝ => (x:ℂ)^(-(4+(t:ℂ)*I))*verticalMellin k t) := by
  have hc : Continuous (fun t : ℝ => (x:ℂ)^(-(4+(t:ℂ)*I))) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (continuousAt_const_cpow (by exact_mod_cast x.property.ne')).comp (by fun_prop)
  apply ((integrable_verticalMellin k).norm.const_mul (((x:ℝ)^4)⁻¹)).mono'
  · exact hc.aestronglyMeasurable.mul (integrable_verticalMellin k).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun t => by rw [norm_mul, norm_inverse_weight])

/-- Literal inverse Mellin recovery at every positive argument. -/
theorem productKernel_mellin_inversion (k : ℕ) (x : Ioi (0:ℝ)) :
    (1/(2*Real.pi):ℝ) •
      (∫ t : ℝ, (x:ℂ)^(-(4+(t:ℂ)*I))*verticalMellin k t) =
      (productKernel k x:ℂ) := by
  simpa only [mellinInv, mellin, smul_eq_mul, verticalMellin, Complex.ofReal_ofNat] using
    mellinInv_mellin_eq 4 (fun y : ℝ => (productKernel k y:ℂ))
      x.property (by simpa using mellin_convergent k) (vertical_integrable k)
      (continuous_kernel k x.property)

/-- A uniform-in-order bound on the literal product kernel, with the sigma-four saddle. -/
theorem abs_productKernel_le (k : ℕ) (x : Ioi (0:ℝ)) :
    |productKernel k x| ≤ (10/Real.pi)*Real.exp (7*Real.pi/2)*saddleMass k*
      Real.sqrt (saddleHeight k)/(x:ℝ)^4 := by
  have hc : 0 ≤ (1/(2*Real.pi):ℝ) := by positivity
  calc |productKernel k x| = ‖(productKernel k x:ℂ)‖ := (Complex.norm_real _).symm
    _ = ‖(1/(2*Real.pi):ℝ) •
      (∫ t : ℝ, (x:ℂ)^(-(4+(t:ℂ)*I))*verticalMellin k t)‖ := by
        rw [productKernel_mellin_inversion]
    _ = (1/(2*Real.pi))*‖∫ t : ℝ, (x:ℂ)^(-(4+(t:ℂ)*I))*verticalMellin k t‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
    _ ≤ (1/(2*Real.pi))*(∫ t : ℝ, ‖(x:ℂ)^(-(4+(t:ℂ)*I))*verticalMellin k t‖) :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) hc
    _ = (1/(2*Real.pi))*(((x:ℝ)^4)⁻¹*(∫ t : ℝ, ‖verticalMellin k t‖)) := by
      simp_rw [norm_mul, norm_inverse_weight]
      rw [integral_const_mul]
    _ ≤ (1/(2*Real.pi))*(((x:ℝ)^4)⁻¹*
      (20*Real.exp (7*Real.pi/2)*saddleMass k*Real.sqrt (saddleHeight k))) := by
      gcongr
      exact integral_norm_verticalMellin_le k
    _ = _ := by ring

end RHTower.WeilWorkDeficitInversion
