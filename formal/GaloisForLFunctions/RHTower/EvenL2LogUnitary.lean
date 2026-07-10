import GaloisForLFunctions.RHTower.SoninEvenCarrier
import GaloisForLFunctions.RHTower.L2MellinUnitary
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# The logarithmic unitary on the even real-line carrier

This file constructs the exact unitary

`L²(ℝ, dx)ᵉᵛ → L²(ℝ, dt),  f ↦ (t ↦ √2 e^(t/2) f(e^t))`,

including an explicit inverse and the unconditional intertwining of normalized physical dilation
with additive translation by `log p`. The Jacobian, null-set pullback, measurability, norm,
surjectivity, and operator identity are all proved in the `Lp` quotient.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace RHTower


theorem lintegral_Ioi_eq_lintegral_exp_mul (g : ℝ → ℝ≥0∞) :
    ∫⁻ x in Set.Ioi (0 : ℝ), g x =
      ∫⁻ t : ℝ, ENNReal.ofReal (Real.exp t) * g (Real.exp t) := by
  rw [← Real.range_exp, ← Set.image_univ]
  simpa only [Measure.restrict_univ, abs_of_pos (Real.exp_pos _)] using
    (MeasureTheory.lintegral_image_eq_lintegral_abs_deriv_mul
      (s := Set.univ) MeasurableSet.univ
      (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
      Real.exp_injective.injOn g)


theorem neg_image_Ioi : (fun x : ℝ => -x) '' Set.Ioi 0 = Set.Iio 0 := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa only [Set.mem_Ioi, Set.mem_Iio] using neg_lt_zero.mpr hy
  · intro hx
    refine ⟨-x, ?_, by simp⟩
    simpa only [Set.mem_Ioi] using neg_pos.mpr hx

theorem lintegral_Iio_eq_lintegral_Ioi_neg (g : ℝ → ℝ≥0∞) :
    ∫⁻ x in Set.Iio (0 : ℝ), g x = ∫⁻ x in Set.Ioi (0 : ℝ), g (-x) := by
  rw [← neg_image_Ioi]
  simpa only [abs_neg, abs_one, ENNReal.ofReal_one, one_mul] using
    (MeasureTheory.lintegral_image_eq_lintegral_abs_deriv_mul
      (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi
      (fun x _ => (hasDerivAt_neg x).hasDerivWithinAt)
      neg_injective.injOn g)

theorem lintegral_enorm_sq_even_eq_two_mul_Ioi
    (f : RHTower.evenSubspace) :
    (∫⁻ x : ℝ, ‖f.1 x‖ₑ ^ (2 : ℝ)) =
      2 * ∫⁻ x in Set.Ioi (0 : ℝ), ‖f.1 x‖ₑ ^ (2 : ℝ) := by
  have hfix : RHTower.l2Reflection f.1 = f.1 :=
    (RHTower.mem_evenSubspace_iff f.1).mp f.2
  have href := RHTower.l2Reflection_ae f.1
  rw [hfix] at href
  have heven : ∀ᵐ x : ℝ ∂volume,
      ‖f.1 (-x)‖ₑ ^ (2 : ℝ) = ‖f.1 x‖ₑ ^ (2 : ℝ) :=
    href.symm.mono fun x hx => by
      change f.1 (-x) = f.1 x at hx
      rw [hx]
  calc
    (∫⁻ x : ℝ, ‖f.1 x‖ₑ ^ (2 : ℝ)) =
        (∫⁻ x in Set.Ioi (0 : ℝ), ‖f.1 x‖ₑ ^ (2 : ℝ)) +
          ∫⁻ x in Set.Iic (0 : ℝ), ‖f.1 x‖ₑ ^ (2 : ℝ) := by
      simpa only [Set.compl_Ioi] using
        (MeasureTheory.lintegral_add_compl
          (μ := volume) (A := Set.Ioi (0 : ℝ))
          (fun x : ℝ => ‖f.1 x‖ₑ ^ (2 : ℝ)) measurableSet_Ioi).symm
    _ = (∫⁻ x in Set.Ioi (0 : ℝ), ‖f.1 x‖ₑ ^ (2 : ℝ)) +
          ∫⁻ x in Set.Iio (0 : ℝ), ‖f.1 x‖ₑ ^ (2 : ℝ) := by
      rw [MeasureTheory.restrict_Iio_eq_restrict_Iic (μ := volume)]
    _ = (∫⁻ x in Set.Ioi (0 : ℝ), ‖f.1 x‖ₑ ^ (2 : ℝ)) +
          ∫⁻ x in Set.Ioi (0 : ℝ), ‖f.1 (-x)‖ₑ ^ (2 : ℝ) := by
      rw [lintegral_Iio_eq_lintegral_Ioi_neg]
    _ = (∫⁻ x in Set.Ioi (0 : ℝ), ‖f.1 x‖ₑ ^ (2 : ℝ)) +
          ∫⁻ x in Set.Ioi (0 : ℝ), ‖f.1 x‖ₑ ^ (2 : ℝ) := by
      congr 1
      exact MeasureTheory.lintegral_congr_ae (MeasureTheory.ae_restrict_of_ae heven)
    _ = 2 * ∫⁻ x in Set.Ioi (0 : ℝ), ‖f.1 x‖ₑ ^ (2 : ℝ) := by ring

noncomputable def logEvenFun (f : RHTower.evenSubspace) (t : ℝ) : ℂ :=
  ((Real.sqrt 2 * Real.exp (t / 2) : ℝ) : ℂ) * f.1 (Real.exp t)

lemma enorm_logEvenFun_sq (f : RHTower.evenSubspace) (t : ℝ) :
    ‖logEvenFun f t‖ₑ ^ (2 : ℝ) =
      2 * ENNReal.ofReal (Real.exp t) * ‖f.1 (Real.exp t)‖ₑ ^ (2 : ℝ) := by
  simp only [ENNReal.rpow_two, enorm_eq_nnnorm]
  rw [ENNReal.ofReal_eq_coe_nnreal (Real.exp_pos _).le]
  norm_cast
  apply NNReal.eq
  simp only [NNReal.coe_pow, NNReal.coe_mul, coe_nnnorm,
    logEvenFun, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    NNReal.coe_mk]
  rw [abs_of_nonneg (Real.sqrt_nonneg _), abs_of_pos (Real.exp_pos _)]
  rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hexp : Real.exp (t / 2) ^ 2 = Real.exp t := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  norm_num

theorem lintegral_enorm_logEvenFun_sq (f : RHTower.evenSubspace) :
    (∫⁻ t : ℝ, ‖logEvenFun f t‖ₑ ^ (2 : ℝ)) =
      ∫⁻ x : ℝ, ‖f.1 x‖ₑ ^ (2 : ℝ) := by
  calc
    (∫⁻ t : ℝ, ‖logEvenFun f t‖ₑ ^ (2 : ℝ)) =
        ∫⁻ t : ℝ, 2 * (ENNReal.ofReal (Real.exp t) *
          ‖f.1 (Real.exp t)‖ₑ ^ (2 : ℝ)) := by
      apply MeasureTheory.lintegral_congr
      intro t
      rw [enorm_logEvenFun_sq]
      ring
    _ = 2 * ∫⁻ t : ℝ, ENNReal.ofReal (Real.exp t) *
          ‖f.1 (Real.exp t)‖ₑ ^ (2 : ℝ) := by
      exact MeasureTheory.lintegral_const_mul' 2 _ (by norm_num)
    _ = 2 * ∫⁻ x in Set.Ioi (0 : ℝ), ‖f.1 x‖ₑ ^ (2 : ℝ) := by
      rw [lintegral_Ioi_eq_lintegral_exp_mul]
    _ = ∫⁻ x : ℝ, ‖f.1 x‖ₑ ^ (2 : ℝ) :=
      (lintegral_enorm_sq_even_eq_two_mul_Ioi f).symm

theorem volume_preimage_exp_eq_zero_of_measurableSet
    {s : Set ℝ} (hsm : MeasurableSet s) (hs : volume s = 0) :
    volume (Real.exp ⁻¹' s) = 0 := by
  let g : ℝ → ℝ≥0∞ := s.indicator (fun _ => 1)
  have hs_ae : ∀ᵐ x : ℝ ∂volume, x ∉ s :=
    (MeasureTheory.measure_eq_zero_iff_ae_notMem).mp hs
  have hg_zero : g =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] 0 :=
    (MeasureTheory.ae_restrict_of_ae hs_ae).mono fun x hx => by
      exact Set.indicator_of_notMem hx _
  have hleft : (∫⁻ x in Set.Ioi (0 : ℝ), g x) = 0 :=
    MeasureTheory.lintegral_eq_zero_of_ae_eq_zero hg_zero
  have hweighted :
      (∫⁻ t : ℝ, ENNReal.ofReal (Real.exp t) * g (Real.exp t)) = 0 := by
    rw [← lintegral_Ioi_eq_lintegral_exp_mul]
    exact hleft
  have hmeas : Measurable (fun t : ℝ =>
      ENNReal.ofReal (Real.exp t) * g (Real.exp t)) := by
    dsimp only [g]
    fun_prop
  have hae := (MeasureTheory.lintegral_eq_zero_iff hmeas).mp hweighted
  have hnot : ∀ᵐ t : ℝ ∂volume, Real.exp t ∉ s := hae.mono fun t ht => by
    intro hmem
    simp only [g, Set.indicator_of_mem hmem, mul_one] at ht
    exact (ENNReal.ofReal_pos.mpr (Real.exp_pos t)).ne' ht
  rw [MeasureTheory.measure_eq_zero_iff_ae_notMem]
  simpa only [Set.mem_preimage] using hnot

theorem realExp_quasiMeasurePreserving :
    Measure.QuasiMeasurePreserving Real.exp volume volume := by
  refine ⟨Real.measurable_exp, ?_⟩
  intro s hs
  let t := MeasureTheory.toMeasurable volume s
  have htm : MeasurableSet t := MeasureTheory.measurableSet_toMeasurable _ _
  have ht0 : volume t = 0 := by
    simpa only [t, MeasureTheory.measure_toMeasurable] using hs
  have hpre : volume (Real.exp ⁻¹' t) = 0 :=
    volume_preimage_exp_eq_zero_of_measurableSet htm ht0
  apply le_antisymm ?_ bot_le
  calc
    volume.map Real.exp s ≤ volume.map Real.exp t :=
      measure_mono (MeasureTheory.subset_toMeasurable volume s)
    _ = volume (Real.exp ⁻¹' t) :=
      Measure.map_apply_of_aemeasurable Real.measurable_exp.aemeasurable htm
    _ = 0 := hpre

theorem eLpNorm_logEvenFun (f : RHTower.evenSubspace) :
    eLpNorm (logEvenFun f) 2 volume = eLpNorm (fun x : ℝ => f.1 x) 2 volume := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
  norm_num only [ENNReal.toReal_ofNat]
  rw [lintegral_enorm_logEvenFun_sq]

theorem memLp_logEvenFun (f : RHTower.evenSubspace) :
    MemLp (logEvenFun f) 2 volume := by
  refine ⟨?_, ?_⟩
  · have hfcomp := (Lp.aestronglyMeasurable f.1).comp_quasiMeasurePreserving
      realExp_quasiMeasurePreserving
    have hscalar : AEStronglyMeasurable
        (fun t : ℝ => (((Real.sqrt 2 * Real.exp (t / 2) : ℝ) : ℂ))) volume := by
      fun_prop
    exact hscalar.mul hfcomp
  · rw [eLpNorm_logEvenFun]
    exact (Lp.memLp f.1).2

noncomputable def logEvenAux (f : RHTower.evenSubspace) : RHTower.SoninL2 :=
  (memLp_logEvenFun f).toLp (logEvenFun f)

theorem logEvenAux_ae (f : RHTower.evenSubspace) :
    logEvenAux f =ᵐ[volume] logEvenFun f :=
  (memLp_logEvenFun f).coeFn_toLp

theorem logEvenFun_add_ae (f g : RHTower.evenSubspace) :
    logEvenFun (f + g) =ᵐ[volume] fun t => logEvenFun f t + logEvenFun g t := by
  have hadd := realExp_quasiMeasurePreserving.ae (Lp.coeFn_add f.1 g.1)
  filter_upwards [hadd] with t ht
  change (f + g : RHTower.evenSubspace).1 (Real.exp t) =
      f.1 (Real.exp t) + g.1 (Real.exp t) at ht
  simp only [logEvenFun, ht, mul_add]

theorem logEvenFun_smul_ae (c : ℂ) (f : RHTower.evenSubspace) :
    logEvenFun (c • f) =ᵐ[volume] fun t => c * logEvenFun f t := by
  have hsmul := realExp_quasiMeasurePreserving.ae (Lp.coeFn_smul c f.1)
  filter_upwards [hsmul] with t ht
  change (c • f : RHTower.evenSubspace).1 (Real.exp t) =
      c • f.1 (Real.exp t) at ht
  simp only [logEvenFun, ht, smul_eq_mul]
  ring

noncomputable def logEvenLinear : RHTower.evenSubspace →ₗ[ℂ] RHTower.SoninL2 where
  toFun := logEvenAux
  map_add' f g := by
    apply Lp.ext
    filter_upwards [logEvenAux_ae (f + g), logEvenAux_ae f, logEvenAux_ae g,
      logEvenFun_add_ae f g, Lp.coeFn_add (logEvenAux f) (logEvenAux g)] with
      t hfg hf hg hadd hsum
    rw [hfg, hadd, hsum]
    simp only [Pi.add_apply, hf, hg]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [logEvenAux_ae (c • f), logEvenAux_ae f,
      logEvenFun_smul_ae c f, Lp.coeFn_smul c (logEvenAux f)] with
      t hcf hf hsmul hcoesm
    rw [hcf, hsmul]
    simp only [RingHom.id_apply]
    rw [hcoesm]
    simp only [Pi.smul_apply, smul_eq_mul, hf]

theorem norm_logEvenAux (f : RHTower.evenSubspace) :
    ‖logEvenAux f‖ = ‖f‖ := by
  change ‖logEvenAux f‖ = ‖f.1‖
  rw [Lp.norm_def, Lp.norm_def,
    eLpNorm_congr_ae (logEvenAux_ae f), eLpNorm_logEvenFun]

noncomputable def logEvenIsometry :
    RHTower.evenSubspace →ₗᵢ[ℂ] RHTower.SoninL2 where
  toLinearMap := logEvenLinear
  norm_map' := norm_logEvenAux

@[simp] theorem logEvenIsometry_apply (f : RHTower.evenSubspace) :
    logEvenIsometry f = logEvenAux f := rfl

/-! ### Explicit inverse and surjectivity -/

noncomputable def l2MeasurableRep (g : RHTower.SoninL2) : ℝ → ℂ :=
  (Lp.aestronglyMeasurable g).mk (fun x : ℝ => g x)

theorem l2MeasurableRep_ae (g : RHTower.SoninL2) :
    l2MeasurableRep g =ᵐ[volume] fun x : ℝ => g x :=
  (Lp.aestronglyMeasurable g).ae_eq_mk.symm

noncomputable def invLogEvenWeight (x : ℝ) : ℝ :=
  if x = 0 then 0 else
    (Real.sqrt 2)⁻¹ * Real.exp (-(Real.log |x|) / 2)

noncomputable def invLogEvenFun (g : RHTower.SoninL2) (x : ℝ) : ℂ :=
  (invLogEvenWeight x : ℂ) * l2MeasurableRep g (Real.log |x|)

theorem invLogEvenFun_neg (g : RHTower.SoninL2) (x : ℝ) :
    invLogEvenFun g (-x) = invLogEvenFun g x := by
  simp only [invLogEvenFun, invLogEvenWeight, neg_eq_zero, abs_neg]

theorem invLogEvenFun_aestronglyMeasurable (g : RHTower.SoninL2) :
    AEStronglyMeasurable (invLogEvenFun g) volume := by
  have hw : StronglyMeasurable invLogEvenWeight := by
    apply Measurable.stronglyMeasurable
    unfold invLogEvenWeight
    exact Measurable.ite (measurableSet_singleton 0) measurable_const (by fun_prop)
  have hrep : StronglyMeasurable
      (fun x : ℝ => l2MeasurableRep g (Real.log |x|)) :=
    (Lp.aestronglyMeasurable g).stronglyMeasurable_mk.comp_measurable (by fun_prop)
  have hwC : AEStronglyMeasurable (fun x : ℝ => (invLogEvenWeight x : ℂ)) volume :=
    hw.measurable.complex_ofReal.aestronglyMeasurable
  exact hwC.mul hrep.aestronglyMeasurable

theorem logWeight_mul_invLogEvenFun_exp (g : RHTower.SoninL2) (t : ℝ) :
    (((Real.sqrt 2 * Real.exp (t / 2) : ℝ) : ℂ) *
      invLogEvenFun g (Real.exp t)) = l2MeasurableRep g t := by
  simp only [invLogEvenFun, invLogEvenWeight, Real.exp_ne_zero, if_false,
    abs_of_pos (Real.exp_pos _), Real.log_exp]
  have hcoef : (Real.sqrt 2 * Real.exp (t / 2)) *
      ((Real.sqrt 2)⁻¹ * Real.exp (-t / 2)) = 1 := by
    field_simp [Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2)]
    rw [← Real.exp_add]
    norm_num
  have hcoefC : (↑(Real.sqrt 2 * Real.exp (t / 2)) : ℂ) *
      (↑((Real.sqrt 2)⁻¹ * Real.exp (-t / 2)) : ℂ) = 1 := by
    exact_mod_cast hcoef
  rw [← mul_assoc, hcoefC, one_mul]

theorem enorm_logWeight_mul_sq (t : ℝ) (z : ℂ) :
    ‖(((Real.sqrt 2 * Real.exp (t / 2) : ℝ) : ℂ) * z)‖ₑ ^ (2 : ℝ) =
      2 * ENNReal.ofReal (Real.exp t) * ‖z‖ₑ ^ (2 : ℝ) := by
  simp only [ENNReal.rpow_two, enorm_eq_nnnorm]
  rw [ENNReal.ofReal_eq_coe_nnreal (Real.exp_pos _).le]
  norm_cast
  apply NNReal.eq
  simp only [NNReal.coe_pow, NNReal.coe_mul, coe_nnnorm, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, NNReal.coe_mk]
  rw [abs_of_nonneg (Real.sqrt_nonneg _), abs_of_pos (Real.exp_pos _)]
  rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hexp : Real.exp (t / 2) ^ 2 = Real.exp t := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  norm_num

theorem two_mul_exp_enorm_invLogEvenFun_sq (g : RHTower.SoninL2) (t : ℝ) :
    2 * (ENNReal.ofReal (Real.exp t) *
      ‖invLogEvenFun g (Real.exp t)‖ₑ ^ (2 : ℝ)) =
      ‖l2MeasurableRep g t‖ₑ ^ (2 : ℝ) := by
  rw [← mul_assoc, ← enorm_logWeight_mul_sq]
  rw [logWeight_mul_invLogEvenFun_exp]

theorem lintegral_enorm_invLogEvenFun_sq (g : RHTower.SoninL2) :
    (∫⁻ x : ℝ, ‖invLogEvenFun g x‖ₑ ^ (2 : ℝ)) =
      ∫⁻ t : ℝ, ‖g t‖ₑ ^ (2 : ℝ) := by
  have heven : ∀ x : ℝ,
      ‖invLogEvenFun g (-x)‖ₑ ^ (2 : ℝ) =
        ‖invLogEvenFun g x‖ₑ ^ (2 : ℝ) := fun x => by
    rw [invLogEvenFun_neg]
  have hwhole : (∫⁻ x : ℝ, ‖invLogEvenFun g x‖ₑ ^ (2 : ℝ)) =
      2 * ∫⁻ x in Set.Ioi (0 : ℝ), ‖invLogEvenFun g x‖ₑ ^ (2 : ℝ) := by
    calc
      (∫⁻ x : ℝ, ‖invLogEvenFun g x‖ₑ ^ (2 : ℝ)) =
          (∫⁻ x in Set.Ioi (0 : ℝ), ‖invLogEvenFun g x‖ₑ ^ (2 : ℝ)) +
            ∫⁻ x in Set.Iic (0 : ℝ), ‖invLogEvenFun g x‖ₑ ^ (2 : ℝ) := by
        simpa only [Set.compl_Ioi] using
          (MeasureTheory.lintegral_add_compl
            (μ := volume) (A := Set.Ioi (0 : ℝ))
            (fun x : ℝ => ‖invLogEvenFun g x‖ₑ ^ (2 : ℝ)) measurableSet_Ioi).symm
      _ = (∫⁻ x in Set.Ioi (0 : ℝ), ‖invLogEvenFun g x‖ₑ ^ (2 : ℝ)) +
            ∫⁻ x in Set.Iio (0 : ℝ), ‖invLogEvenFun g x‖ₑ ^ (2 : ℝ) := by
        rw [MeasureTheory.restrict_Iio_eq_restrict_Iic (μ := volume)]
      _ = (∫⁻ x in Set.Ioi (0 : ℝ), ‖invLogEvenFun g x‖ₑ ^ (2 : ℝ)) +
            ∫⁻ x in Set.Ioi (0 : ℝ), ‖invLogEvenFun g (-x)‖ₑ ^ (2 : ℝ) := by
        rw [lintegral_Iio_eq_lintegral_Ioi_neg]
      _ = (∫⁻ x in Set.Ioi (0 : ℝ), ‖invLogEvenFun g x‖ₑ ^ (2 : ℝ)) +
            ∫⁻ x in Set.Ioi (0 : ℝ), ‖invLogEvenFun g x‖ₑ ^ (2 : ℝ) := by
        congr 1
        apply MeasureTheory.lintegral_congr
        exact heven
      _ = 2 * ∫⁻ x in Set.Ioi (0 : ℝ), ‖invLogEvenFun g x‖ₑ ^ (2 : ℝ) := by ring
  rw [hwhole]
  calc
    2 * (∫⁻ x in Set.Ioi (0 : ℝ), ‖invLogEvenFun g x‖ₑ ^ (2 : ℝ)) =
        2 * ∫⁻ t : ℝ, ENNReal.ofReal (Real.exp t) *
          ‖invLogEvenFun g (Real.exp t)‖ₑ ^ (2 : ℝ) := by
      rw [lintegral_Ioi_eq_lintegral_exp_mul]
    _ = ∫⁻ t : ℝ, 2 * (ENNReal.ofReal (Real.exp t) *
          ‖invLogEvenFun g (Real.exp t)‖ₑ ^ (2 : ℝ)) := by
      rw [MeasureTheory.lintegral_const_mul' 2 _ (by norm_num)]
    _ = ∫⁻ t : ℝ, ‖l2MeasurableRep g t‖ₑ ^ (2 : ℝ) := by
      apply MeasureTheory.lintegral_congr
      exact two_mul_exp_enorm_invLogEvenFun_sq g
    _ = ∫⁻ t : ℝ, ‖g t‖ₑ ^ (2 : ℝ) := by
      apply MeasureTheory.lintegral_congr_ae
      exact (l2MeasurableRep_ae g).mono fun t ht => by
        change l2MeasurableRep g t = g t at ht
        simpa only using congrArg (fun z : ℂ => ‖z‖ₑ ^ (2 : ℝ)) ht

theorem memLp_invLogEvenFun (g : RHTower.SoninL2) :
    MemLp (invLogEvenFun g) 2 volume := by
  refine ⟨invLogEvenFun_aestronglyMeasurable g, ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
  norm_num only [ENNReal.toReal_ofNat]
  rw [lintegral_enorm_invLogEvenFun_sq]
  have hgfinite := (Lp.memLp g).2
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top] at hgfinite
  norm_num only [ENNReal.toReal_ofNat] at hgfinite
  exact hgfinite

noncomputable def invLogEvenAux (g : RHTower.SoninL2) : RHTower.SoninL2 :=
  (memLp_invLogEvenFun g).toLp (invLogEvenFun g)

theorem invLogEvenAux_ae (g : RHTower.SoninL2) :
    invLogEvenAux g =ᵐ[volume] invLogEvenFun g :=
  (memLp_invLogEvenFun g).coeFn_toLp

theorem invLogEvenAux_mem_evenSubspace (g : RHTower.SoninL2) :
    invLogEvenAux g ∈ RHTower.evenSubspace := by
  rw [RHTower.mem_evenSubspace_iff]
  apply Lp.ext
  have hneg := (invLogEvenAux_ae g).comp_tendsto
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae
  filter_upwards [RHTower.l2Reflection_ae (invLogEvenAux g), hneg,
    invLogEvenAux_ae g] with x href hnegx hpos
  rw [href]
  have hnegx' : invLogEvenAux g (-x) = invLogEvenFun g (-x) := by
    simpa only [Function.comp_apply] using hnegx
  rw [hnegx', hpos, invLogEvenFun_neg]

noncomputable def invLogEvenEven (g : RHTower.SoninL2) : RHTower.evenSubspace :=
  ⟨invLogEvenAux g, invLogEvenAux_mem_evenSubspace g⟩

@[simp] theorem invLogEvenEven_coe (g : RHTower.SoninL2) :
    (invLogEvenEven g : RHTower.SoninL2) = invLogEvenAux g := rfl

theorem logEvenIsometry_invLogEvenEven (g : RHTower.SoninL2) :
    logEvenIsometry (invLogEvenEven g) = g := by
  change logEvenAux (invLogEvenEven g) = g
  apply Lp.ext
  have hinvExp := (invLogEvenAux_ae g).comp_tendsto
    realExp_quasiMeasurePreserving.tendsto_ae
  filter_upwards [logEvenAux_ae (invLogEvenEven g), hinvExp,
    l2MeasurableRep_ae g] with t hout hinv hrep
  rw [hout]
  change (((Real.sqrt 2 * Real.exp (t / 2) : ℝ) : ℂ) *
      invLogEvenAux g (Real.exp t)) = g t
  have hinv' : invLogEvenAux g (Real.exp t) =
      invLogEvenFun g (Real.exp t) := by
    simpa only [Function.comp_apply] using hinv
  rw [hinv', logWeight_mul_invLogEvenFun_exp]
  change l2MeasurableRep g t = g t
  exact hrep

theorem logEvenIsometry_surjective : Function.Surjective logEvenIsometry := fun g =>
  ⟨invLogEvenEven g, logEvenIsometry_invLogEvenEven g⟩

/-- The exact unitary logarithmic-coordinate transform on even `L²(ℝ, dx)`. -/
noncomputable def logEvenUnitary :
    RHTower.evenSubspace ≃ₗᵢ[ℂ] RHTower.SoninL2 :=
  LinearIsometryEquiv.ofSurjective logEvenIsometry logEvenIsometry_surjective

@[simp] theorem logEvenUnitary_apply (f : RHTower.evenSubspace) :
    logEvenUnitary f = logEvenAux f := rfl

theorem logEvenUnitary_ae (f : RHTower.evenSubspace) :
    logEvenUnitary f =ᵐ[volume] fun t : ℝ =>
      (((Real.sqrt 2 * Real.exp (t / 2) : ℝ) : ℂ) * f.1 (Real.exp t)) :=
  logEvenAux_ae f

/-! ### Normalized dilations become additive translations -/

theorem logEvenUnitary_evenDilation (p : ℝ) (hp : 0 < p)
    (f : RHTower.evenSubspace) :
    logEvenUnitary (evenDilationUnitary p hp f) =
      RHTower.MellinL2.additiveTranslationUnitary (Real.log p) (logEvenUnitary f) := by
  apply Lp.ext
  have hdilExp := (RHTower.dilation_ae p hp f.1).comp_tendsto
    realExp_quasiMeasurePreserving.tendsto_ae
  have hlogShift := (logEvenUnitary_ae f).comp_tendsto
    (RHTower.MellinL2.realTranslation_measurePreserving (Real.log p)).quasiMeasurePreserving.tendsto_ae
  filter_upwards [logEvenUnitary_ae (evenDilationUnitary p hp f), hdilExp,
    Lp.coeFn_compMeasurePreserving (logEvenUnitary f)
      (RHTower.MellinL2.realTranslation_measurePreserving (Real.log p)),
    hlogShift] with t hleft hdil htrans hshift
  rw [hleft]
  change (((Real.sqrt 2 * Real.exp (t / 2) : ℝ) : ℂ) *
      (evenDilationUnitary p hp f : RHTower.SoninL2) (Real.exp t)) =
    Lp.compMeasurePreserving
      (RHTower.MellinL2.realTranslationEquiv (Real.log p))
      (RHTower.MellinL2.realTranslation_measurePreserving (Real.log p))
      (logEvenUnitary f) t
  rw [htrans]
  change (((Real.sqrt 2 * Real.exp (t / 2) : ℝ) : ℂ) *
      RHTower.dilation p hp f.1 (Real.exp t)) =
    logEvenUnitary f (t + Real.log p)
  have hdil' : RHTower.dilation p hp f.1 (Real.exp t) =
      (Real.sqrt p : ℂ) * f.1 (p * Real.exp t) := by
    simpa only [Function.comp_apply] using hdil
  have hshift' : logEvenUnitary f (t + Real.log p) =
      (((Real.sqrt 2 * Real.exp ((t + Real.log p) / 2) : ℝ) : ℂ) *
        f.1 (Real.exp (t + Real.log p))) := by
    simpa [Function.comp_apply, RHTower.MellinL2.realTranslationEquiv] using hshift
  rw [hdil', hshift']
  have harg : p * Real.exp t = Real.exp (t + Real.log p) := by
    rw [Real.exp_add, Real.exp_log hp]
    ring
  rw [harg]
  have hsqrt : Real.sqrt p = Real.exp (Real.log p / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hp]
    congr 1
    ring
  have hcoef : (Real.sqrt 2 * Real.exp (t / 2)) * Real.sqrt p =
      Real.sqrt 2 * Real.exp ((t + Real.log p) / 2) := by
    rw [hsqrt, mul_assoc, ← Real.exp_add]
    congr 1
    ring
  have hcoefC :
      (↑(Real.sqrt 2 * Real.exp (t / 2)) : ℂ) * (Real.sqrt p : ℂ) =
        (↑(Real.sqrt 2 * Real.exp ((t + Real.log p) / 2)) : ℂ) := by
    exact_mod_cast hcoef
  rw [← mul_assoc, hcoefC]

end RHTower
