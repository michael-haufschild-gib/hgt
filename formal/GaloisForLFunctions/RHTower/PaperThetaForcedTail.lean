import GaloisForLFunctions.HTGeometry.BoundedVariationKernelIntegral
import GaloisForLFunctions.RHTower.PaperThetaSourceRatio
import GaloisForLFunctions.RHTower.PaperThetaSpatialModule

/-! # Native theta tails with arbitrary continuous BV forcing

The source ratio pays the full variation of an inhomogeneous tail. No finite
spectral expansion or restriction on the forcing's support is imposed.
-/

noncomputable section
open MeasureTheory Set Filter Topology Complex

namespace RHTower.PaperThetaEndpoint
open HedenmalmThetaSource HedenmalmQuantile HedenmalmPrimeTranslation
  ThetaFiniteTransport

/-- Literal whole-line continuous profiles of finite total variation. -/
structure ThetaContinuousBV where
  toFun : ℝ → ℂ
  continuous : Continuous toFun
  bv : BoundedVariationOn toFun univ

instance : CoeFun ThetaContinuousBV (fun _ => ℝ → ℂ) := ⟨ThetaContinuousBV.toFun⟩

def ThetaContinuousBV.bound (g : ThetaContinuousBV) : ℝ :=
  ‖g 0‖+(eVariationOn g univ).toReal

theorem ThetaContinuousBV.bound_nonneg (g : ThetaContinuousBV) : 0 ≤ g.bound :=
  add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg

theorem ThetaContinuousBV.norm_le (g : ThetaContinuousBV) (x : ℝ) : ‖g x‖ ≤ g.bound := by
  have hd := g.bv.dist_le (mem_univ x) (mem_univ 0)
  have ht := norm_add_le (g x-g 0) (g 0)
  rw [sub_add_cancel] at ht
  rw [dist_eq_norm] at hd
  exact ht.trans (by dsimp [bound]; linarith)

theorem boundedVariation_affine {f : ℝ → ℂ} {s : Set ℝ}
    (hf : BoundedVariationOn f s) (a b : ℂ) :
    BoundedVariationOn (fun x => a+b*f x) s := by
  have hl : LipschitzWith ‖b‖₊ (fun z : ℂ => a+b*z) := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    simp only [dist_eq_norm, coe_nnnorm]
    rw [show a+b*x-(a+b*y) = b*(x-y) by ring, norm_mul]
  exact hl.comp_boundedVariationOn hf

def ThetaContinuousBV.affine (g : ThetaContinuousBV) (a b : ℂ) : ThetaContinuousBV where
  toFun x := a+b*g x
  continuous := continuous_const.add (continuous_const.mul g.continuous)
  bv := boundedVariation_affine g.bv a b

def ThetaContinuousBV.reflect (g : ThetaContinuousBV) : ThetaContinuousBV where
  toFun x := g (-x)
  continuous := g.continuous.comp continuous_neg
  bv := ne_top_of_le_ne_top g.bv (eVariationOn.comp_le_of_antitoneOn g
    (s := univ) (t := univ) (fun x : ℝ => -x)
    (fun _ _ _ _ h => neg_le_neg h) (fun _ _ => mem_univ _))

def forcedMoment (z : ℂ) (g : ThetaContinuousBV) : ℂ :=
  ∫ y, flatCharDensity z y*g y

theorem integrable_forcedDensity (z : ℂ) (g : ThetaContinuousBV) :
    Integrable (fun y => flatCharDensity z y*g y) :=
  (integrable_flatCharDensity_all z).mul_bdd g.continuous.aestronglyMeasurable
    (Eventually.of_forall g.norm_le)

def forcedRightTail (z : ℂ) (g : ThetaContinuousBV) (x : ℝ) : ℂ :=
  Complex.exp (-(I*z)*(x : ℂ)) /
    (thetaSource.normalized x : ℂ) * ∫ y in Ioi x, flatCharDensity z y*g y

theorem integrable_forcedRatio (z : ℂ) (g : ThetaContinuousBV) (x : ℝ) :
    Integrable (fun h => (sourceRatio h x : ℂ)*sourceChar z h*g (x+h)) :=
  (integrable_sourceRatio_character z x).mul_bdd
    (g.continuous.comp (continuous_const.add continuous_id)).aestronglyMeasurable
    (Eventually.of_forall fun _ => g.norm_le _)

theorem forcedRightTail_eq_ratio (z : ℂ) (g : ThetaContinuousBV) (x : ℝ) :
    forcedRightTail z g x =
      ∫ h in Ioi (0 : ℝ), (sourceRatio h x : ℂ)*sourceChar z h*g (x+h) := by
  have hρ : (thetaSource.normalized x : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (thetaSource.normalized_pos x).ne'
  rw [forcedRightTail, ← integral_Ioi_comp_add
    (fun y => flatCharDensity z y*g y) x, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with h
  rw [sourceRatio_normalized, flatCharDensity, sourceChar, sourceChar]
  push_cast
  have he : Complex.exp (-(I*z)*(x : ℂ))*Complex.exp (I*z*((x : ℂ)+(h : ℂ))) =
      Complex.exp (I*z*(h : ℂ)) := by rw [← Complex.exp_add]; congr 1; ring
  field_simp
  simp only [neg_mul] at he
  linear_combination (thetaSource.normalized (x+h) : ℂ)*g (x+h)*he

theorem eVariationOn_forcedRightTail_ray (z : ℂ) (g : ThetaContinuousBV) (a : ℝ) :
    eVariationOn (forcedRightTail z g) (Ici a) ≤
      ENNReal.ofReal ((g.bound+(eVariationOn g univ).toReal)*
        ∫ h in Ioi (0 : ℝ), sourceRatio h a*Real.exp (-z.im*h)) := by
  change eVariationOn (fun x => forcedRightTail z g x) (Ici a) ≤ _
  simp_rw [forcedRightTail_eq_ratio]
  have hB : IntegrableOn (fun h : ℝ => (g.bound+(eVariationOn g univ).toReal)*
      (sourceRatio h a*Real.exp (-z.im*h))) (Ioi (0 : ℝ)) :=
    (integrable_sourceRatio_tilt (-z.im) a).integrableOn.const_mul _
  rw [← integral_const_mul]
  apply GaloisForLFunctions.HTGeometry.eVariationOn_integral_le _ _ _ _
    (fun x _ => (integrable_forcedRatio z g x).integrableOn) hB
  intro n u hu ha
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
  have hp := GaloisForLFunctions.HTGeometry.antitone_kernel_partition_le (sourceRatio h) a
    (fun x => (sourceRatio_pos h x).le) (sourceRatio_antitone_all ⟨h, hh.le⟩)
    g.bv g.bound_nonneg g.norm_le h u hu ha n
  have he : ∀ i,
      ‖(sourceRatio h (u (i+1)) : ℂ)*sourceChar z h*g (u (i+1)+h)-
        (sourceRatio h (u i) : ℂ)*sourceChar z h*g (u i+h)‖ =
      Real.exp (-z.im*h)*
        ‖(sourceRatio h (u (i+1)) : ℂ)*g (u (i+1)+h)-
          (sourceRatio h (u i) : ℂ)*g (u i+h)‖ := by
    intro i
    rw [show (sourceRatio h (u (i+1)) : ℂ)*sourceChar z h*g (u (i+1)+h)-
        (sourceRatio h (u i) : ℂ)*sourceChar z h*g (u i+h) =
      sourceChar z h*((sourceRatio h (u (i+1)) : ℂ)*g (u (i+1)+h)-
        (sourceRatio h (u i) : ℂ)*g (u i+h)) by ring,
      norm_mul, norm_sourceChar]
  simp_rw [he]
  rw [← Finset.mul_sum]
  exact (mul_le_mul_of_nonneg_left hp (Real.exp_pos _).le).trans_eq (by ring)

/-- Both the forcing variation and the kernel variation are paid before integration. -/
theorem boundedVariationOn_forcedRightTail_ray (z : ℂ) (g : ThetaContinuousBV) (a : ℝ) :
    BoundedVariationOn (forcedRightTail z g) (Ici a) :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (eVariationOn_forcedRightTail_ray z g a)

def forcedTailMass (z : ℂ) (x : ℝ) : ℝ :=
  ∫ h in Ioi (0 : ℝ), sourceRatio h x*Real.exp (-z.im*h)

theorem forcedTailMass_nonneg (z : ℂ) (x : ℝ) : 0 ≤ forcedTailMass z x :=
  integral_nonneg fun h => mul_nonneg (sourceRatio_pos h x).le (Real.exp_pos _).le

theorem primitive_source_ratio (z : ℂ) (x : ℝ) :
    flatPrimitiveMode z x / (thetaSource.normalized x : ℂ) =
      ∫ h in Ioi (0 : ℝ), (sourceRatio h x : ℂ)*sourceChar z h := by
  have hρ : (thetaSource.normalized x : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (thetaSource.normalized_pos x).ne'
  rw [flatPrimitiveMode_shifted, ← integral_Ioi_comp_add
    (fun y => (thetaSource.normalized y : ℂ)*
      Complex.exp (I*z*((y-x : ℝ) : ℂ))) x, ← integral_div]
  apply integral_congr_ae
  filter_upwards [] with h
  rw [sourceRatio_normalized, sourceChar, show x+h-x = h by ring]
  push_cast
  field_simp

theorem sourceChar_imaginary (b h : ℝ) :
    sourceChar (I*(b : ℂ)) h = (Real.exp (-b*h) : ℂ) := by
  rw [sourceChar, Complex.ofReal_exp]
  congr 1
  push_cast
  ring_nf
  simp [Complex.I_sq]

theorem forcedTailMass_eq_primitive (z : ℂ) (x : ℝ) :
    forcedTailMass z x =
      ‖flatPrimitiveMode (I*(z.im : ℂ)) x‖ / thetaSource.normalized x := by
  have he : (∫ h in Ioi (0 : ℝ),
      (sourceRatio h x : ℂ)*sourceChar (I*(z.im : ℂ)) h) =
      (forcedTailMass z x : ℂ) := by
    simp_rw [sourceChar_imaginary, ← Complex.ofReal_mul]
    exact integral_ofReal
  have hn := congrArg norm (primitive_source_ratio (I*(z.im : ℂ)) x)
  rw [he, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (thetaSource.normalized_pos x), Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (forcedTailMass_nonneg z x)] at hn
  exact hn.symm

theorem tendsto_forcedTailMass (z : ℂ) : Tendsto (forcedTailMass z) atTop (𝓝 0) := by
  exact (tendsto_primitive_quotient_norm_atTop _).congr
    (fun x => (forcedTailMass_eq_primitive z x).symm)

theorem norm_forcedRightTail_le (z : ℂ) (g : ThetaContinuousBV) (x : ℝ) :
    ‖forcedRightTail z g x‖ ≤ g.bound*forcedTailMass z x := by
  rw [forcedRightTail_eq_ratio, forcedTailMass, ← integral_const_mul]
  apply (norm_integral_le_integral_norm _).trans
  apply setIntegral_mono_on (integrable_forcedRatio z g x).norm.integrableOn
    ((integrable_sourceRatio_tilt (-z.im) x).integrableOn.const_mul _)
    measurableSet_Ioi
  intro h _
  rw [norm_mul, norm_sourceRatio_character]
  exact (mul_le_mul_of_nonneg_left (g.norm_le _)
    (mul_nonneg (sourceRatio_pos h x).le (Real.exp_pos _).le)).trans_eq (by ring)

/-- The inhomogeneous right tail has zero trace for every whole-line BV forcing. -/
theorem tendsto_forcedRightTail_atTop (z : ℂ) (g : ThetaContinuousBV) :
    Tendsto (forcedRightTail z g) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) (norm_forcedRightTail_le z g)
  simpa using (tendsto_forcedTailMass z).const_mul g.bound

theorem forcedTail_integral_split (z : ℂ) (g : ThetaContinuousBV) (x : ℝ) :
    (∫ y in Ioi x, flatCharDensity z y*g y) =
      forcedMoment z g-∫ y in Iic x, flatCharDensity z y*g y := by
  have hs := intervalIntegral.integral_Iic_add_Ioi (μ := volume) (b := x)
    (integrable_forcedDensity z g).integrableOn (integrable_forcedDensity z g).integrableOn
  change _ = (∫ y, flatCharDensity z y*g y)-_
  rw [← hs]
  ring

theorem hasDerivAt_forcedRightTail (z : ℂ) (g : ThetaContinuousBV) (x : ℝ) :
    HasDerivAt (forcedRightTail z g)
      (-(sourceLogDerivative x+I*z)*forcedRightTail z g x-g x) x := by
  have hρ := ((differentiable_normalized_theta x).hasDerivAt.ofReal_comp).differentiableAt.hasDerivAt
  have hρ0 : (thetaSource.normalized x : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (thetaSource.normalized_pos x).ne'
  have hI := hasDerivAt_setIntegral_Iic ((continuous_flatCharDensity z).mul g.continuous)
    (integrable_forcedDensity z g) x
  have ht : HasDerivAt (fun x => ∫ y in Ioi x, flatCharDensity z y*g y)
      (-flatCharDensity z x*g x) x := by
    simp_rw [forcedTail_integral_split]
    convert hI.const_sub (forcedMoment z g) using 1 <;>
      first | rfl | simp only [Pi.mul_apply, neg_mul]
  have he : HasDerivAt (fun x : ℝ => Complex.exp (-(I*z)*(x : ℂ)))
      (-(I*z)*Complex.exp (-(I*z)*(x : ℂ))) x := by
    simpa [mul_comm] using
      (((hasDerivAt_id (x : ℂ)).const_mul (-(I*z))).cexp).comp_ofReal
  refine ((he.div hρ hρ0).mul ht).congr_deriv ?_
  dsimp [forcedRightTail, sourceLogDerivative, flatCharDensity]
  field_simp
  have hc := exp_mul_sourceChar z x
  simp only [neg_mul] at hc
  linear_combination -(thetaSource.normalized x : ℂ)^2*g x*hc

theorem continuous_forcedRightTail (z : ℂ) (g : ThetaContinuousBV) :
    Continuous (forcedRightTail z g) := by
  have hd : Differentiable ℝ (forcedRightTail z g) :=
    fun x => (hasDerivAt_forcedRightTail z g x).differentiableAt
  exact hd.continuous

end RHTower.PaperThetaEndpoint
