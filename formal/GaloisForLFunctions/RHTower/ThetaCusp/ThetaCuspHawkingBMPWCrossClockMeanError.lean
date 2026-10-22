import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPWCrossClockActualError
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPWCrossClockMeanEquation
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCuspNativeMeanSquare

/-! Native modular integrability transferred to the literal full-width high-cusp mean. -/

open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open RHTower RHTower.D4BMModularCore RHTower.D4BMGlobalAngularResponse
open RHTower.D4BMPWCrossClockActualError RHTower.D4BMCuspProjection
open RHTower.D4BMCuspResponse
open RHTower.D4BMPWCrossClockMeanEquation RHTower.D4BMMixedParticularCuspFlux
open scoped ContDiff
noncomputable section
set_option autoImplicit false

namespace RHTower.D4BMPWCrossClockMeanError

private def highRectangle : Set ℂ :=
  {z | z.re ∈ Icc (-1/2) (1/2) ∧ 3 < z.im}

private theorem highRectangle_subset : highRectangle ⊆ cellChart := by
  intro z hz
  have hy : 0 < z.im := lt_trans (by norm_num) hz.2
  refine ⟨⟨z,hy⟩,?_,rfl⟩
  constructor
  · rw [Complex.normSq_apply]
    nlinarith [sq_nonneg z.re,hz.2]
  · change |z.re| ≤ 1/2
    exact abs_le.mpr (by simpa only [mem_Icc,neg_div] using hz.1)

/-- Full high-cusp horizontal mean of a native-integrable complex field is
integrable against its actual hyperbolic height density. -/
theorem native_integrable_cusp_mean_density (F : ℂ → ℂ)
    (hi : Integrable (fun z : UpperHalfPlane => F z) D4BMModularCore.measure) :
    IntegrableOn (fun y : ℝ =>
      mean (fun x => F (point x y))/(y:ℂ)^(2:ℕ)) (Ioi (3:ℝ)) := by
  have hmap : Integrable F (Measure.map UpperHalfPlane.coe D4BMModularCore.measure) :=
    UpperHalfPlane.measurableEmbedding_coe.integrable_map_iff.mpr hi
  rw [map_measure_eq] at hmap
  have hd : IntegrableOn (fun z => chartDensity z • F z) cellChart :=
    (integrable_withDensity_iff_integrable_smul (show Measurable chartDensity by
      unfold chartDensity; fun_prop)).mp hmap
  have hrect : IntegrableOn (fun z : ℂ => F z/(z.im:ℂ)^(2:ℕ)) highRectangle := by
    apply (hd.mono_set highRectangle_subset).congr_fun
    · intro z hz
      have hp : 0 < z.im := lt_trans (by norm_num) hz.2
      simp only [chartDensity,NNReal.smul_def,NNReal.coe_pow,NNReal.coe_div,
        NNReal.coe_one,coe_nnnorm,Real.norm_eq_abs,abs_of_pos hp,
        Complex.real_smul,Complex.ofReal_pow,Complex.ofReal_div,Complex.ofReal_one]
      ring
    · exact (isClosed_Icc.preimage Complex.continuous_re).measurableSet.inter
        (isOpen_lt continuous_const Complex.continuous_im).measurableSet
  let G : ℝ × ℝ → ℂ := fun xy =>
    F (Complex.measurableEquivRealProd.symm xy)/(xy.2:ℂ)^(2:ℕ)
  have hG : IntegrableOn G (Icc (-1/2:ℝ) (1/2) ×ˢ Ioi (3:ℝ))
      ((volume : Measure ℝ).prod volume) := by
    rw [← Measure.volume_eq_prod]
    apply (Complex.volume_preserving_equiv_real_prod.integrableOn_comp_preimage
      Complex.measurableEquivRealProd.measurableEmbedding).mp
    change IntegrableOn (fun z : ℂ => F z/(z.im:ℂ)^(2:ℕ)) highRectangle
    exact hrect
  have hp : Integrable G
      ((volume.restrict (Icc (-1/2:ℝ) (1/2))).prod (volume.restrict (Ioi (3:ℝ)))) := by
    simpa only [Measure.prod_restrict,IntegrableOn] using hG
  apply hp.integral_prod_right.congr
  filter_upwards with y
  dsimp [G]
  rw [integral_div,integral_Icc_eq_integral_Ioc]
  have he (x : ℝ) : (⟨x,y⟩:ℂ) = point x y := by
    apply Complex.ext <;> simp [point]
  simp only [mean,he]

/-- Actual weighted two-branch cross error in planar coordinates. -/
def crossErrorPlanar (q : XiZeroCopy) (z : ℂ) : ℂ :=
  weight q (angularCoordinates z) *
    ((cutoffResponse q true (angularCoordinates z) + responsePlanar q true z) *
        (cutoffResponse q false (angularCoordinates z) + responsePlanar q false z) -
      cutoffResponse q true (angularCoordinates z) *
        cutoffResponse q false (angularCoordinates z))

/-- The exact actual-error estimate survives horizontal averaging in the
high modular cusp; no pointwise bound on the L² correction is introduced. -/
theorem actual_cross_error_mean_density_integrable (q : XiZeroCopy)
    (hleft : (q.1 : ℂ).re < 1/2) :
    IntegrableOn (fun y : ℝ =>
      mean (fun x => crossErrorPlanar q (point x y))/(y:ℂ)^(2:ℕ))
      (Ioi (3:ℝ)) := by
  apply native_integrable_cusp_mean_density
  have hcoord (z : UpperHalfPlane) : angularCoordinates (z:ℂ) = coordinates z := rfl
  convert actual_cross_error_integrable q hleft using 1
  funext z
  simp only [crossErrorPlanar,responsePlanar,Function.comp_apply,hcoord,
    ofComplex_apply]

def principalCross (q : XiZeroCopy) (y : ℝ) : ℂ :=
  cuspResponse q true ![0,y] * cuspResponse q false ![0,y]

private theorem cusp_cutoff_eq (q : XiZeroCopy) (b : Bool)
    {x y : ℝ} (hy : 3 < y) :
    cutoffResponse q b ![x,y] = cuspResponse q b ![0,y] := by
  have hcut : cutoff ![x,y] = 1 := by
    simp only [cutoff,Matrix.cons_val_one,Matrix.cons_val_zero]
    exact_mod_cast Real.smoothTransition.one_of_one_le (show 1 ≤ y-2 by linarith)
  rw [cutoffResponse,hcut,one_mul]
  rfl

/-- On the actual high cusp, the native-integrable cross error is exactly the
weighted discrepancy between the full product and its noncancelling principal
two-branch product. -/
theorem crossErrorPlanar_high (q : XiZeroCopy) {x y : ℝ}
    (hx : x ∈ Ioc (-1/2:ℝ) (1/2)) (hy : 3 < y) :
    crossErrorPlanar q (point x y) =
      ((y ^ (-beta q) : ℝ) : ℂ) * (crossPlanar q (point x y) - principalCross q y) := by
  have hp : angularCoordinates (point x y) = ![x,y] := by
    ext i
    fin_cases i <;> simp [angularCoordinates,point]
  have hw : weight q ![x,y] = ((y ^ (-beta q) : ℝ) : ℂ) := by
    simp only [weight,Matrix.cons_val_one,Matrix.cons_val_zero,
      max_eq_right (by linarith : 1 ≤ y)]
  have hfield (b : Bool) :
      fullAngularField q b ![x,y] = fullAngular q b (ofComplex (point x y)) := by
    change fullAngular q b (ofComplex (angularCoordinates.symm ![x,y])) = _
    rw [← hp,angularCoordinates.symm_apply_apply]
  have hdtrue := fullAngularField_high_cusp_decomposition q true hx hy
  have hdfalse := fullAngularField_high_cusp_decomposition q false hx hy
  simp only [crossErrorPlanar,hp,hw]
  rw [← hdtrue,← hdfalse,cusp_cutoff_eq q true hy,cusp_cutoff_eq q false hy]
  rw [hfield true,hfield false]
  rfl

private theorem mean_const (c : ℂ) : mean (fun _x : ℝ => c) = c := by
  change (∫ _x in Ioc (-1/2:ℝ) (1/2), c) = c
  rw [← intervalIntegral.integral_of_le (by norm_num : (-1/2:ℝ) ≤ 1/2)]
  rw [intervalIntegral.integral_const]
  norm_num

/-- Full horizontal error is the exact mean of the planar native error,
with no pointwise bound on either response correction. -/
theorem crossErrorMean_high (q : XiZeroCopy) {y : ℝ} (hy : 3 < y) :
    mean (fun x => crossErrorPlanar q (point x y)) =
      ((y ^ (-beta q) : ℝ) : ℂ) * (crossMean q y - principalCross q y) := by
  have hF : IntegrableOn (fun x : ℝ => crossPlanar q (point x y))
      (Ioc (-1/2:ℝ) (1/2)) := by
    have hs : ContDiffOn ℝ ∞ (crossPlanar q) {z : ℂ | 0 < z.im} :=
      ((fullAngular_smooth q true).planar_contDiffOn).mul
        ((fullAngular_smooth q false).planar_contDiffOn)
    exact (slice_continuous (crossPlanar q) hs (by linarith)).integrableOn_Ioc
  calc
    _ = mean (fun x => ((y ^ (-beta q) : ℝ) : ℂ) *
        (crossPlanar q (point x y) - principalCross q y)) := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro x hx
      exact crossErrorPlanar_high q hx hy
    _ = _ := by
      have hc := mean_const (principalCross q y)
      change (∫ _x in Ioc (-1/2:ℝ) (1/2), principalCross q y) =
        principalCross q y at hc
      rw [mean,integral_const_mul,
        integral_sub hF (integrableOn_const (by simp [Real.volume_Ioc])),hc]
      rfl

/-- The actual full-product mean differs from its three-power principal
product by a genuinely integrable weighted high-cusp error. -/
theorem actual_cross_mean_error_density_integrable (q : XiZeroCopy)
    (hleft : (q.1 : ℂ).re < 1/2) :
    IntegrableOn (fun y : ℝ =>
      ((y ^ (-beta q) : ℝ) : ℂ) * (crossMean q y - principalCross q y) /
        (y:ℂ)^(2:ℕ)) (Ioi (3:ℝ)) := by
  apply (actual_cross_error_mean_density_integrable q hleft).congr_fun
  · intro y hy
    change mean (fun x => crossErrorPlanar q (point x y)) / (y:ℂ)^(2:ℕ) =
      ((y ^ (-beta q) : ℝ) : ℂ) * (crossMean q y - principalCross q y) /
        (y:ℂ)^(2:ℕ)
    rw [crossErrorMean_high q hy]
  · exact measurableSet_Ioi

end RHTower.D4BMPWCrossClockMeanError
