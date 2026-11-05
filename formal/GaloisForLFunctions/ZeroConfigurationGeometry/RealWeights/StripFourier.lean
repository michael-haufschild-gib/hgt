import GaloisForLFunctions.ZeroConfigurationGeometry.RealWeights.StripEnvelope
import GaloisForLFunctions.ZeroConfigurationGeometry.TheCameraAndTheTilt
import GaloisForLFunctions.ZeroConfigurationGeometry.FarZerosAreFaintInTheLocalCamera
import GaloisForLFunctions.RHTower.CosineProducerLocalPortObstruction
import GaloisForLFunctions.RHTower.ZetaSymbolArchimedeanHorizon


/-!
# A strip envelope with asymptotically unit mass

Compact Fourier transforms have vertical derivative given by multiplication
of their source by its coordinate. Plancherel bounds this derivative energy
by `ε²e^ε` times the central energy. The resulting common strip envelope
controls the full off-line point-image and has mass at most
`[1 + ε + (ε + ε²)e^ε]` times the central Fourier energy.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section
namespace GaloisForLFunctions.ZeroConfigurationGeometry
open Zeta23

/-- Differentiation of a compact Fourier transform multiplies its source by `iu`. -/
theorem hasDerivAt_cameraFT_compact {b : ℝ → ℂ} (hb : Continuous b)
    (hbc : HasCompactSupport b) (z : ℂ) :
    HasDerivAt (paperFT b) (paperFT (fun u => I * u * b u) z) z := by
  apply _root_.RHTower.LocalPort.hasDerivAt_paperFT_of_superExpDecay
  refine ⟨hb, fun c => ?_⟩
  exact (hb.norm.mul (by fun_prop)).integrable_of_hasCompactSupport hbc.norm.mul_right

/-- Vertical differentiation multiplies the source by its real coordinate. -/
theorem hasDerivAt_cameraFT_vertical {b : ℝ → ℂ} (hb : Continuous b)
    (hbc : HasCompactSupport b) (x y : ℝ) :
    HasDerivAt (fun v : ℝ => paperFT b ((x : ℂ) - I * v))
      (paperFT (fun u => (u : ℂ) * b u) ((x : ℂ) - I * y)) y := by
  have hq : HasDerivAt (fun z : ℂ => (x : ℂ) - I * z) (-I) (y : ℂ) := by
    simpa only [Pi.sub_apply, id_eq, zero_sub, mul_one] using!
      (hasDerivAt_const (y : ℂ) (x : ℂ)).sub ((hasDerivAt_id (y : ℂ)).const_mul I)
  have hh := ((hasDerivAt_cameraFT_compact hb hbc ((x : ℂ) - I * y)).comp (y : ℂ) hq).comp_ofReal
  have he : paperFT (fun u => I * u * b u) ((x : ℂ) - I * y) =
      I * paperFT (fun u => (u : ℂ) * b u) ((x : ℂ) - I * y) := by
    rw [paperFT_def, paperFT_def, ← integral_const_mul]
    congr 1
    funext u
    ring
  refine hh.congr_deriv ?_
  rw [he]
  have hI : I * I = -1 := Complex.I_mul_I
  calc I * paperFT (fun u => (u : ℂ) * b u) ((x : ℂ) - I * y) * -I =
      -(I * I) * paperFT (fun u => (u : ℂ) * b u) ((x : ℂ) - I * y) := by ring
    _ = _ := by rw [hI, neg_neg, one_mul]

/-- A common nonnegative envelope for all vertical displacements of size at most one half. -/
def cameraStripEnvelope (b : ℝ → ℂ) (ε x : ℝ) : ℝ :=
  (1 + ε) * ‖paperFT b x‖ ^ 2 + (1 + 1 / ε) *
    ∫ y in (-1 / 2 : ℝ)..(1 / 2),
      ‖paperFT (fun u => (u : ℂ) * b u) ((x : ℂ) - I * y)‖ ^ 2

theorem cameraStripEnvelope_nonneg {b : ℝ → ℂ} {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    0 ≤ cameraStripEnvelope b ε x := by
  have hi : 0 ≤ ∫ y in (-1 / 2 : ℝ)..(1 / 2),
      ‖paperFT (fun u => (u : ℂ) * b u) ((x : ℂ) - I * y)‖ ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) (fun _ _ => sq_nonneg _)
  unfold cameraStripEnvelope
  positivity

/-- The strip envelope bounds the squared transform pointwise, with variable depth. -/
theorem norm_cameraFT_vertical_sq_le_envelope {b : ℝ → ℂ} {ε v : ℝ}
    (hb : Continuous b) (hbc : HasCompactSupport b) (hε : 0 < ε)
    (hv : |v| ≤ 1 / 2) (x : ℝ) :
    ‖paperFT b ((x : ℂ) - I * v)‖ ^ 2 ≤ cameraStripEnvelope b ε x := by
  have hgc : Continuous fun u : ℝ => (u : ℂ) * b u := by fun_prop
  have hGc : Differentiable ℂ (paperFT (fun u => (u : ℂ) * b u)) :=
    fun z => (hasDerivAt_cameraFT_compact hgc hbc.mul_left z).differentiableAt
  have hG : Continuous fun y : ℝ =>
      paperFT (fun u => (u : ℂ) * b u) ((x : ℂ) - I * y) :=
    hGc.continuous.comp (by fun_prop)
  have hh := norm_sq_le_vertical_energy_envelope hε
    (hasDerivAt_cameraFT_vertical hb hbc x) hG hv
  simpa only [Complex.ofReal_zero, mul_zero, sub_zero, cameraStripEnvelope] using hh

/-- The same envelope controls an off-line zero's full bilinear point-image.
Both reflected transform values are bounded before taking their product. -/
theorem norm_local_pointImage_le_cameraStripEnvelope {b : ℝ → ℂ} {ε : ℝ}
    (hb : Continuous b) (hbc : HasCompactSupport b) (hε : 0 < ε)
    (z : ℂ) (hz : |depth z| ≤ 1 / 2) (X : ℝ) :
    ‖pointImage (localWindow X b) (localWindow X b) z‖ ≤
      cameraStripEnvelope b ε (z.im - X) := by
  have hp : gammaOf z - (X : ℂ) = ((z.im - X : ℝ) : ℂ) - I * depth z := by
    rw [gammaOf_eq]
    push_cast
    ring
  have hn : conj (gammaOf z) - (X : ℂ) =
      ((z.im - X : ℝ) : ℂ) - I * (-depth z) := by
    rw [gammaOf_eq, map_sub, map_mul, Complex.conj_ofReal,
      Complex.conj_I, Complex.conj_ofReal]
    push_cast
    ring
  have hu := norm_cameraFT_vertical_sq_le_envelope hb hbc hε hz (z.im - X)
  have hv := norm_cameraFT_vertical_sq_le_envelope hb hbc hε
    (show |-depth z| ≤ 1 / 2 by simpa only [abs_neg] using hz) (z.im - X)
  simp only [Complex.ofReal_neg] at hv
  rw [pointImage, paperFT_localWindow, paperFT_localWindow,
    norm_mul, Complex.norm_conj, hp, hn]
  nlinarith only [hu, hv, sq_nonneg
    (‖paperFT b (((z.im - X : ℝ) : ℂ) - I * depth z)‖ -
      ‖paperFT b (((z.im - X : ℝ) : ℂ) - I * (-(depth z : ℂ)))‖)]

/-- The energy of the vertical derivative is at most `ε²e^ε` times the central
Fourier energy when the source is supported in `[-ε,ε]`. -/
theorem integral_vertical_cameraFT_derivative_sq_le {b : ℝ → ℂ} {ε y : ℝ}
    (hb : ContDiff ℝ 2 b) (hbs : tsupport b ⊆ Icc (-ε) ε)
    (hy : |y| ≤ 1 / 2) :
    (∫ x : ℝ, ‖paperFT (fun u => (u : ℂ) * b u) ((x : ℂ) - I * y)‖ ^ 2) ≤
      (ε ^ 2 * Real.exp ε) * ∫ x : ℝ, ‖paperFT b x‖ ^ 2 := by
  let g : ℝ → ℂ := tilt y (fun u => (u : ℂ) * b u)
  have hbc : HasCompactSupport b := (show ApertureWindow ε b from ⟨hb, hbs⟩).hasCompactSupport
  have hg : ContDiff ℝ 2 g := by
    change ContDiff ℝ 2 (fun u : ℝ => ((u : ℂ) * b u) * (Real.exp (y * u) : ℂ))
    exact (Complex.ofRealCLM.contDiff.mul hb).mul
      (Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)))
  have hgc : HasCompactSupport g := hbc.mul_left.mul_right
  have hgs : tsupport g ⊆ Icc (-ε) ε := by
    dsimp only [g, tilt]
    exact tsupport_mul_subset_left.trans (tsupport_mul_subset_right.trans hbs)
  have hbi : Integrable fun u => ‖b u‖ ^ 2 := by
    simpa only [pow_two, Pi.mul_apply] using!
      (hb.continuous.norm.mul hb.continuous.norm).integrable_of_hasCompactSupport hbc.norm.mul_right
  have hgi : Integrable fun u => ‖g u‖ ^ 2 := by
    simpa only [pow_two, Pi.mul_apply] using!
      (hg.continuous.norm.mul hg.continuous.norm).integrable_of_hasCompactSupport hgc.norm.mul_right
  have hpoint (u : ℝ) : ‖g u‖ ^ 2 ≤ (ε ^ 2 * Real.exp ε) * ‖b u‖ ^ 2 := by
    by_cases hbu : b u = 0
    · simp only [g, tilt, hbu, mul_zero, zero_mul, norm_zero, zero_pow (by decide : 2 ≠ 0), le_refl]
    have hu : |u| ≤ ε := abs_le.mpr (hbs (subset_tsupport b (by exact hbu)))
    have hprod : y * u ≤ ε / 2 := by
      have hh := mul_le_mul hy hu (abs_nonneg u) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      have ha : y * u ≤ |y| * |u| := by rw [← abs_mul]; exact le_abs_self _
      linarith only [hh, ha]
    have hexp : Real.exp (y * u) ^ 2 ≤ Real.exp ε := by
      rw [sq, ← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith only [hprod])
    have hu2 := pow_le_pow_left₀ (abs_nonneg u) hu 2
    have he : ‖g u‖ ^ 2 = |u| ^ 2 * Real.exp (y * u) ^ 2 * ‖b u‖ ^ 2 := by
      simp only [g, tilt, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos (y * u)), mul_pow]
      ring
    rw [he]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul hu2 hexp (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)
  have hphysical := integral_mono hgi (hbi.const_mul (ε ^ 2 * Real.exp ε)) hpoint
  rw [integral_const_mul] at hphysical
  have hshift : (fun x : ℝ =>
      ‖paperFT (fun u => (u : ℂ) * b u) ((x : ℂ) - I * y)‖ ^ 2) =
      fun x : ℝ => ‖paperFT g x‖ ^ 2 := by
    funext x
    rw [paperFT_sub_I_mul_eq_tilt]
  rw [hshift, _root_.RHTower.integral_norm_sq_paperFT_eq hg hgs,
    _root_.RHTower.integral_norm_sq_paperFT_eq hb hbs]
  have hh := mul_le_mul_of_nonneg_left hphysical (by positivity : 0 ≤ 2 * π)
  linarith only [hh]

/-- The common strip envelope is integrable and loses only a factor tending to one
as the physical aperture tends to zero. -/
theorem cameraStripEnvelope_integrable_and_mass_le {b : ℝ → ℂ} {ε : ℝ}
    (hb : ContDiff ℝ 2 b) (hbs : tsupport b ⊆ Icc (-ε) ε) (hε : 0 < ε) :
    Integrable (cameraStripEnvelope b ε) ∧
      (∫ x, cameraStripEnvelope b ε x) ≤
        (1 + ε + (ε + ε ^ 2) * Real.exp ε) * ∫ x : ℝ, ‖paperFT b x‖ ^ 2 := by
  let Y : Set ℝ := Ioc (-1 / 2) (1 / 2)
  let μ : Measure ℝ := volume.restrict Y
  have hY : (-1 / 2 : ℝ) ≤ 1 / 2 := by norm_num
  haveI : IsFiniteMeasure μ := by
    refine ⟨?_⟩
    change volume.restrict (Ioc (-1 / 2 : ℝ) (1 / 2)) Set.univ < ⊤
    rw [Measure.restrict_apply_univ, Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  let g : ℝ → ℂ := fun u => (u : ℂ) * b u
  have hg : ContDiff ℝ 2 g := Complex.ofRealCLM.contDiff.mul hb
  have hbc : HasCompactSupport b := (show ApertureWindow ε b from ⟨hb, hbs⟩).hasCompactSupport
  have hgc : HasCompactSupport g := hbc.mul_left
  have hgd : Differentiable ℂ (paperFT g) :=
    fun z => (hasDerivAt_cameraFT_compact hg.continuous hgc z).differentiableAt
  let F : ℝ → ℝ → ℝ := fun y x => ‖paperFT g ((x : ℂ) - I * y)‖ ^ 2
  have hFc : Continuous (Function.uncurry F) := by
    exact (hgd.continuous.comp (by fun_prop)).norm.pow 2
  have hFn (y x : ℝ) : ‖F y x‖ = F y x := Real.norm_of_nonneg (sq_nonneg _)
  have hi (y : ℝ) : Integrable (F y) := by
    have htilt : ContDiff ℝ 2 (GaloisForLFunctions.ZeroConfigurationGeometry.tilt y g) := by
      change ContDiff ℝ 2 (fun u : ℝ => g u * (Real.exp (y * u) : ℂ))
      exact hg.mul (Complex.ofRealCLM.contDiff.comp
        (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)))
    have htilts : tsupport (tilt y g) ⊆ Icc (-ε) ε :=
      tsupport_mul_subset_left.trans (tsupport_mul_subset_right.trans hbs)
    have hh := _root_.RHTower.integrable_normSq_paperFT htilt htilts
    simpa only [F, paperFT_sub_I_mul_eq_tilt] using hh
  let B : ℝ := (ε ^ 2 * Real.exp ε) * ∫ x : ℝ, ‖paperFT b x‖ ^ 2
  have hbnd (y : ℝ) (hy : y ∈ Y) : (∫ x, F y x) ≤ B :=
    integral_vertical_cameraFT_derivative_sq_le hb hbs
      (abs_le.mpr ⟨by linarith only [hy.1], hy.2⟩)
  have hMean : Integrable (fun y => ∫ x, F y x) μ := by
    apply (integrable_const B).mono'
      hFc.stronglyMeasurable.integral_prod_right.aestronglyMeasurable
    filter_upwards [ae_restrict_mem (measurableSet_Ioc : MeasurableSet Y)] with y hy
    rw [Real.norm_of_nonneg (integral_nonneg fun x => sq_nonneg _)]
    exact hbnd y hy
  have hFi : Integrable (Function.uncurry F) (μ.prod volume) := by
    apply (integrable_prod_iff hFc.aestronglyMeasurable).mpr
    exact ⟨Eventually.of_forall hi, by simpa only [Function.uncurry_apply_pair, hFn] using hMean⟩
  have hvertical : Integrable fun x =>
      ∫ y in (-1 / 2 : ℝ)..(1 / 2), F y x := by
    simp only [intervalIntegral.integral_of_le hY]
    change Integrable (fun x => ∫ y, F y x ∂μ)
    exact hFi.integral_prod_right
  have hmass : (∫ x, ∫ y in (-1 / 2 : ℝ)..(1 / 2), F y x) ≤ B := by
    simp_rw [intervalIntegral.integral_of_le hY]
    change (∫ x, ∫ y, F y x ∂μ) ≤ B
    rw [← integral_integral_swap hFi]
    calc (∫ y, ∫ x, F y x ∂volume ∂μ) ≤ ∫ _y, B ∂μ := by
          apply integral_mono_ae hMean (integrable_const B)
          filter_upwards [ae_restrict_mem (measurableSet_Ioc : MeasurableSet Y)] with y hy
          exact hbnd y hy
      _ = B := by
          change (∫ _y in Ioc (-1 / 2 : ℝ) (1 / 2), B) = B
          rw [← intervalIntegral.integral_of_le hY, intervalIntegral.integral_const]
          norm_num
  have hbase := _root_.RHTower.integrable_normSq_paperFT hb hbs
  have he : cameraStripEnvelope b ε = fun x : ℝ =>
      (1 + ε) * ‖paperFT b x‖ ^ 2 + (1 + 1 / ε) *
        ∫ y in (-1 / 2 : ℝ)..(1 / 2), F y x := rfl
  rw [he]
  refine ⟨(hbase.const_mul _).add (hvertical.const_mul _), ?_⟩
  rw [integral_add (hbase.const_mul _) (hvertical.const_mul _),
    integral_const_mul, integral_const_mul]
  calc _ ≤ (1 + ε) * (∫ x : ℝ, ‖paperFT b x‖ ^ 2) + (1 + 1 / ε) * B :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left hmass
            (by positivity : 0 ≤ 1 + 1 / ε))
    _ = _ := by
          dsimp [B]
          field_simp [hε.ne']
          ring

end GaloisForLFunctions.ZeroConfigurationGeometry

#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.hasDerivAt_cameraFT_vertical
#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.norm_cameraFT_vertical_sq_le_envelope
#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.integral_vertical_cameraFT_derivative_sq_le

#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.cameraStripEnvelope_integrable_and_mass_le

#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.norm_local_pointImage_le_cameraStripEnvelope
