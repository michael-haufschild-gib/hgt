import GaloisForLFunctions.RHTower.XiCompactSpectralSampling
import GaloisForLFunctions.RHTower.CHMDCosineSourceFourier

/-! # Complex compact sources in the absolute Xi sampling space -/

open Complex MeasureTheory Filter Topology Set Zeta23
noncomputable section
namespace RHTower
open WeilSpectral

theorem WeilSpectral.ExpDecayTest.integrable_paperFT {f : ℝ → ℝ}
    (hf : ExpDecayTest f) {z : ℂ} (hz : |z.im| ≤ 1/2) :
    Integrable (fun x => (f x : ℂ)*exp (I*z*x)) := by
  have hc : Continuous (fun x : ℝ => (f x : ℂ)*exp (I*z*x)) := by
    have := hf.1.continuous
    fun_prop
  apply (integrable_tailMajorant hf (Λ := 0) le_rfl).mono' hc.aestronglyMeasurable
  filter_upwards [] with x
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc |f x| * ‖exp (I*z*x)‖ ≤ |f x| * Real.exp (1/2*|x|) :=
      mul_le_mul_of_nonneg_left (norm_cexp_I_mul_ofReal_le_of_strip hz x) (abs_nonneg _)
    _ ≤ tailMajorant f 0 x := by
      unfold tailMajorant
      nlinarith [abs_nonneg (deriv f x), Real.exp_pos (1/2*|x|)]

theorem paperFT_split_parts {f : ℝ → ℂ}
    (hr : ExpDecayTest (fun x => (f x).re)) (hi : ExpDecayTest (fun x => (f x).im))
    {z : ℂ} (hz : |z.im| ≤ 1/2) :
    paperFT f z = paperFT (fun x => ((f x).re : ℂ)) z +
      I*paperFT (fun x => ((f x).im : ℂ)) z := by
  have he : (fun x : ℝ => f x*exp (I*z*x)) =
      fun x => ((f x).re : ℂ)*exp (I*z*x) + I*(((f x).im : ℂ)*exp (I*z*x)) := by
    funext x
    nth_rw 1 [← Complex.re_add_im (f x)]
    ring
  rw [paperFT, he, integral_add (hr.integrable_paperFT hz)
    ((hi.integrable_paperFT hz).const_mul I), integral_const_mul]
  rfl

def complexXiEvaluation (f : ℝ → ℂ)
    (hr : ExpDecayTest (fun x => (f x).re)) (hi : ExpDecayTest (fun x => (f x).im)) :
    lp (fun _ : XiZeroCopy => ℂ) 2 :=
  realXiEvaluation (fun x => (f x).re) hr + I • realXiEvaluation (fun x => (f x).im) hi

theorem complexXiEvaluation_apply (f : ℝ → ℂ)
    (hr : ExpDecayTest (fun x => (f x).re)) (hi : ExpDecayTest (fun x => (f x).im))
    (q : XiZeroCopy) : complexXiEvaluation f hr hi q = paperFT f (xiSpectralPoint q) :=
  (paperFT_split_parts hr hi (abs_im_lt_half_of_XiC_eq_zero (XiC_xiSpectralPoint_eq_zero q)).le).symm

theorem complexXi_squareSummable (f : ℝ → ℂ)
    (hr : ExpDecayTest (fun x => (f x).re)) (hi : ExpDecayTest (fun x => (f x).im)) :
    XiWeilSquareSummable (paperFT f) := by
  exact (HilbertSchmidt.summable_coe_sq (complexXiEvaluation f hr hi)).congr
    (fun q => by rw [complexXiEvaluation_apply])

def compactXiTests : Submodule ℂ (ℝ → ℂ) where
  carrier := {f | ContDiff ℝ 2 f ∧ HasCompactSupport f}
  zero_mem' := ⟨contDiff_const, HasCompactSupport.intro isCompact_empty (fun _ _ => rfl)⟩
  add_mem' hf hg := ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  smul_mem' _c _f hf := ⟨contDiff_const.smul hf.1, hf.2.smul_left⟩

theorem compactXiTests.re_decay (f : compactXiTests) : ExpDecayTest (fun x => (f.1 x).re) :=
  CHMDDoobGraph.compact_expDecayTest (Complex.reCLM.contDiff.comp f.property.1)
    (f.property.2.comp_left Complex.zero_re)

theorem compactXiTests.im_decay (f : compactXiTests) : ExpDecayTest (fun x => (f.1 x).im) :=
  CHMDDoobGraph.compact_expDecayTest (Complex.imCLM.contDiff.comp f.property.1)
    (f.property.2.comp_left Complex.zero_im)

def compactXiFourier (z : ℂ) : compactXiTests →ₗ[ℂ] ℂ where
  toFun f := paperFT f z
  map_add' f g := paperFT_add_sources
    (CHMDDoobGraph.compact_expMomentSource f.property.1.continuous f.property.2)
    (CHMDDoobGraph.compact_expMomentSource g.property.1.continuous g.property.2) z
  map_smul' c f := paperFT_const_mul c f z

def compactXiEvaluation : compactXiTests →ₗ[ℂ] lp (fun _ : XiZeroCopy => ℂ) 2 where
  toFun f := complexXiEvaluation f (compactXiTests.re_decay f) (compactXiTests.im_decay f)
  map_add' f g := by
    apply Subtype.ext
    funext q
    change complexXiEvaluation (f+g) _ _ q =
      complexXiEvaluation f _ _ q + complexXiEvaluation g _ _ q
    simp only [complexXiEvaluation_apply]
    exact (compactXiFourier (xiSpectralPoint q)).map_add f g
  map_smul' c f := by
    apply Subtype.ext
    funext q
    change complexXiEvaluation (c • f) _ _ q = c * complexXiEvaluation f _ _ q
    simp only [complexXiEvaluation_apply]
    exact (compactXiFourier (xiSpectralPoint q)).map_smul c f

theorem compactXiEvaluation_apply (f : compactXiTests) (q : XiZeroCopy) :
    compactXiEvaluation f q = paperFT f (xiSpectralPoint q) := complexXiEvaluation_apply _ _ _ _

def compactXiAugment : compactXiTests →ₗ[ℂ]
    (lp (fun _ : XiZeroCopy => ℂ) 2 × (ℂ × ℂ)) :=
  compactXiEvaluation.prod ((compactXiFourier (I/2)).prod (compactXiFourier (-I/2)))

def complexXiTruncation (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f) (L : ℝ) : compactXiTests :=
  ⟨fun x => (truncTest (fun y => (f y).re) L x : ℂ) +
      I*(truncTest (fun y => (f y).im) L x : ℂ),
    (contDiff_ofReal_truncTest (Complex.reCLM.contDiff.comp hf) L).add
      (contDiff_const.mul (contDiff_ofReal_truncTest (Complex.imCLM.contDiff.comp hf) L)),
    ((hasCompactSupport_truncTest (fun y => (f y).re) L).comp_left Complex.ofReal_zero).add
      (((hasCompactSupport_truncTest (fun y => (f y).im) L).comp_left Complex.ofReal_zero).mul_left)⟩

theorem complexXiTruncation_evaluation (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f) (L : ℝ) :
    compactXiEvaluation (complexXiTruncation f hf L) =
      realXiEvaluation (truncTest (fun y => (f y).re) L)
        (CHMDDoobGraph.compact_expDecayTest
          (contDiff_truncTest (Complex.reCLM.contDiff.comp hf) L) (hasCompactSupport_truncTest _ L)) +
      I • realXiEvaluation (truncTest (fun y => (f y).im) L)
        (CHMDDoobGraph.compact_expDecayTest
          (contDiff_truncTest (Complex.imCLM.contDiff.comp hf) L) (hasCompactSupport_truncTest _ L)) := by
  apply Subtype.ext
  funext q
  change complexXiEvaluation _ _ _ q = _
  simp [complexXiEvaluation, realXiEvaluation, xiWeilEvaluationLp, complexXiTruncation]

theorem complexXiTruncation_augmented_tendsto {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hr : ExpDecayTest (fun x => (f x).re))
    (hi : ExpDecayTest (fun x => (f x).im)) :
    Tendsto (fun L : ℝ => compactXiAugment (complexXiTruncation f hf L)) atTop
      (𝓝 (complexXiEvaluation f hr hi, (paperFT f (I/2), paperFT f (-I/2)))) := by
  have he := (realXiEvaluation_trunc_tendsto hr).add
    ((realXiEvaluation_trunc_tendsto hi).const_smul I)
  have hp (z : ℂ) (hz : |z.im| ≤ 1/2) :
      Tendsto (fun L : ℝ => paperFT (complexXiTruncation f hf L) z) atTop (𝓝 (paperFT f z)) := by
    have h := (tendsto_paperFT_truncTest hr hz).add ((tendsto_paperFT_truncTest hi hz).const_mul I)
    rw [paperFT_split_parts hr hi hz]
    convert h using 1
    funext L
    rw [paperFT_split_parts (compactXiTests.re_decay (complexXiTruncation f hf L))
      (compactXiTests.im_decay (complexXiTruncation f hf L)) hz]
    simp [complexXiTruncation]
  have hprod := he.prodMk_nhds ((hp (I/2) (by norm_num)).prodMk_nhds (hp (-I/2) (by norm_num)))
  convert hprod using 1
  · funext L
    exact Prod.ext (complexXiTruncation_evaluation f hf L) rfl
  · rfl

end RHTower
