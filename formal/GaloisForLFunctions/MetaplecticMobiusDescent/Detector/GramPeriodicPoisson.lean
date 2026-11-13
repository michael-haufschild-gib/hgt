/-
Periodic Poisson for the Gram matrix adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.GramCommonLattices

/-!
# Periodic Poisson for the Gram matrix

Joint points and ideal quotient pairs of periodic Gram Poisson summation; mean-zero residue
weights gain arbitrary powers; joint amplitudes and profiles with uniform degree.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical Topology InnerProductSpace ComplexConjugate MatrixGroups ENNReal
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified
open scoped NNReal Pointwise
open RationalSource
open scoped Manifold ContDiff
open scoped Matrix
open UniqueFactorizationMonoid
open Asymptotics
open scoped ContDiff FourierTransform SchwartzMap
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical SchwartzMap
open scoped Classical SchwartzMap FourierTransform ContDiff
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical SchwartzMap
open MeasureTheory
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open MeasureTheory Filter
open scoped BigOperators Classical FourierTransform SchwartzMap RealInnerProductSpace

namespace ProbeGramPeriodicPoisson

abbrev Joint := WithLp 2 (ℂ × ℂ)

def point (x y : ℂ) : Joint := WithLp.toLp 2 (x, y)

def embeddingPair (m : Eisenstein.O × Eisenstein.O) : Joint :=
  point (ringComplex m.1) (ringComplex m.2)

@[simp] theorem norm_point_sq (x y : ℂ) :
    ‖point x y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 :=
  WithLp.prod_norm_sq_eq_of_L2 _

def leftInjection : ℂ →L[ℝ] Joint :=
  (((WithLp.linearEquiv 2 ℝ (ℂ × ℂ)).symm.toLinearMap).comp
    (LinearMap.inl ℝ ℂ ℂ)).toContinuousLinearMap

def rightInjection : ℂ →L[ℝ] Joint :=
  (((WithLp.linearEquiv 2 ℝ (ℂ × ℂ)).symm.toLinearMap).comp
    (LinearMap.inr ℝ ℂ ℂ)).toContinuousLinearMap

@[simp] theorem point_eq_add (x y : ℂ) :
    point x y = leftInjection x + rightInjection y := by
  change WithLp.toLp 2 (x,y) = WithLp.toLp 2 (x,0) + WithLp.toLp 2 (0,y)
  rw [← WithLp.toLp_add]
  simp

theorem slice_isometry (y : ℂ) : Isometry (fun x : ℂ => point x y) := by
  apply Isometry.of_dist_eq
  intro x z
  simp only [dist_eq_norm, point_eq_add, add_sub_add_right_eq_sub, ← map_sub]
  exact WithLp.norm_toLp_fst 2 ℂ ℂ (x-z)

theorem slice_temperate (y : ℂ) :
    (fun x : ℂ => point x y).HasTemperateGrowth := by
  simp only [point_eq_add]
  fun_prop

def leftSlice (W : 𝓢(Joint, ℂ)) (y : ℂ) : 𝓢(ℂ, ℂ) :=
  SchwartzMap.compCLMOfAntilipschitz ℂ (slice_temperate y)
    (slice_isometry y).antilipschitz W

@[simp] theorem leftSlice_apply (W : 𝓢(Joint, ℂ)) (y x : ℂ) :
    leftSlice W y x = W (point x y) := rfl

theorem fourier_joint_eq_iterated (f : Joint → ℂ) (hf : Integrable f) (ξ η : ℂ) :
    𝓕 f (point ξ η) =
      𝓕 (fun x : ℂ => 𝓕 (fun y : ℂ => f (point x y)) η) ξ := by
  let w : Joint := point ξ η
  let G : Joint → ℂ := fun z => Real.fourierChar (-inner ℝ z w) • f z
  have hG : Integrable G := (Real.fourierIntegral_convergent_iff w).mpr hf
  have hGp : Integrable (fun z : ℂ × ℂ => G (WithLp.toLp 2 z)) :=
    (WithLp.volume_preserving_toLp ℂ ℂ).integrable_comp_of_integrable hG
  calc
    𝓕 f (point ξ η) = ∫ z : Joint, G z := rfl
    _ = ∫ z : ℂ × ℂ, G (WithLp.toLp 2 z) :=
      ((WithLp.volume_preserving_toLp ℂ ℂ).integral_comp
        (MeasurableEquiv.toLp 2 (ℂ × ℂ)).measurableEmbedding G).symm
    _ = ∫ x : ℂ, ∫ y : ℂ, G (WithLp.toLp 2 (x, y)) := integral_prod _ hGp
    _ = _ := by
      simp only [Real.fourier_eq, Circle.smul_def, smul_eq_mul]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        dsimp only
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall fun y => by
          simp only [G, w, point, WithLp.prod_inner_apply,
            neg_add, Real.fourierChar.map_add_eq_mul, Circle.smul_def, smul_eq_mul,
            Circle.coe_mul, mul_assoc]

def partialFourier (W : 𝓢(Joint, ℂ)) (η x : ℂ) : ℂ :=
  𝓕 (fun y : ℂ => W (point x y)) η

def planeMajorant (y : ℂ) : ℝ := ((1 + ‖y‖ ^ 2) ^ 2)⁻¹

theorem planeMajorant_integrable : Integrable planeMajorant := by
  have h := integrable_rpow_neg_one_add_norm_sq (E := ℂ) (μ := volume)
    (r := 4) (by norm_num)
  change Integrable (fun y : ℂ => ((1 + ‖y‖ ^ 2) ^ 2)⁻¹)
  convert h using 1
  funext y
  rw [show -(4:ℝ)/2 = -(2:ℝ) by norm_num, Real.rpow_neg (by positivity), Real.rpow_two]

def majorantConstant (W : 𝓢(Joint, ℂ)) : ℝ :=
  SchwartzMap.seminorm ℝ 0 0 W + 2 * SchwartzMap.seminorm ℝ 2 0 W +
    SchwartzMap.seminorm ℝ 4 0 W

theorem norm_le_planeMajorant (W : 𝓢(Joint, ℂ)) (x y : ℂ) :
    ‖W (point x y)‖ ≤ majorantConstant W * planeMajorant y := by
  have h0 := SchwartzMap.norm_le_seminorm ℝ W (point x y)
  have h2 := SchwartzMap.norm_pow_mul_le_seminorm ℝ W 2 (point x y)
  have h4 := SchwartzMap.norm_pow_mul_le_seminorm ℝ W 4 (point x y)
  have hy : ‖y‖^2 ≤ ‖point x y‖^2 := by rw [norm_point_sq]; exact le_add_of_nonneg_left (sq_nonneg _)
  have hy4 : ‖y‖^4 ≤ ‖point x y‖^4 := by nlinarith [sq_nonneg (‖x‖^2)]
  have hm2 := mul_le_mul_of_nonneg_right hy (norm_nonneg (W (point x y)))
  have hm4 := mul_le_mul_of_nonneg_right hy4 (norm_nonneg (W (point x y)))
  rw [planeMajorant, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  dsimp [majorantConstant]
  nlinarith

theorem partialFourier_continuous (W : 𝓢(Joint, ℂ)) (η : ℂ) :
    Continuous (partialFourier W η) := by
  change Continuous (fun x : ℂ => ∫ y : ℂ,
    Real.fourierChar (-inner ℝ y η) • W (point x y))
  apply continuous_of_dominated (bound := fun y => majorantConstant W * planeMajorant y)
  · intro x
    exact ((by fun_prop : Continuous (fun y : ℂ => Real.fourierChar (-inner ℝ y η))).smul
      (W.continuous.comp (show Continuous (fun y : ℂ => point x y) from by
        simp only [point_eq_add]; fun_prop))).aestronglyMeasurable
  · intro x
    exact Eventually.of_forall fun y => by
      simpa only [Circle.smul_def, smul_eq_mul, norm_mul, Circle.norm_coe, one_mul] using
        norm_le_planeMajorant W x y
  · exact planeMajorant_integrable.const_mul _
  · exact Eventually.of_forall fun y =>
      continuous_const.smul (W.continuous.comp (slice_isometry y).continuous)

theorem partialFourier_integrable (W : 𝓢(Joint, ℂ)) (η : ℂ) :
    Integrable (partialFourier W η) := by
  let G : Joint → ℂ := fun z => Real.fourierChar (-inner ℝ z.snd η) • W z
  have hG : Integrable G := W.integrable.norm.mono'
    (by fun_prop : Continuous G).aestronglyMeasurable
    (Eventually.of_forall fun z => by
      simp only [G, Circle.smul_def, smul_eq_mul, norm_mul, Circle.norm_coe, one_mul]
      exact le_rfl)
  have hGp : Integrable (fun z : ℂ × ℂ => G (WithLp.toLp 2 z)) :=
    (WithLp.volume_preserving_toLp ℂ ℂ).integrable_comp_of_integrable hG
  change Integrable (fun x : ℂ => ∫ y : ℂ,
    Real.fourierChar (-inner ℝ y η) • W (point x y))
  exact hGp.integral_prod_left

def partialFourierSchwartz (W : 𝓢(Joint, ℂ)) (η : ℂ) : 𝓢(ℂ, ℂ) :=
  𝓕⁻ (leftSlice (𝓕 W) η)

theorem partialFourierSchwartz_apply (W : 𝓢(Joint, ℂ)) (η x : ℂ) :
    partialFourierSchwartz W η x = partialFourier W η x := by
  have heq : 𝓕 (partialFourier W η) = (leftSlice (𝓕 W) η : ℂ → ℂ) := by
    funext ξ
    change 𝓕 (fun x : ℂ => 𝓕 (fun y : ℂ => W (point x y)) η) ξ = _
    rw [← fourier_joint_eq_iterated W W.integrable ξ η]
    exact (congrFun (SchwartzMap.fourier_coe W) (point ξ η)).symm
  have hi : Integrable (𝓕 (partialFourier W η)) := by
    rw [heq]
    exact (leftSlice (𝓕 W) η).integrable
  change (𝓕⁻ (leftSlice (𝓕 W) η)) x = _
  rw [congrFun (SchwartzMap.fourierInv_coe (leftSlice (𝓕 W) η)) x, ← heq]
  exact (partialFourier_integrable W η).fourierInv_fourier_eq hi
    (partialFourier_continuous W η).continuousAt

theorem fourier_partialFourierSchwartz (W : 𝓢(Joint, ℂ)) (ξ η : ℂ) :
    𝓕 (partialFourierSchwartz W η) ξ = (𝓕 W) (point ξ η) := by
  simp [partialFourierSchwartz]

theorem jointCLM_finite_seminorm_control
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : 𝓢(Joint, ℂ) →L[ℝ] 𝓢(E, ℂ)) (S : Finset (ℕ × ℕ)) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧ ∀ W : 𝓢(Joint, ℂ),
      S.sup (schwartzSeminormFamily ℝ E ℂ) (T W) ≤
        C * s.sup (schwartzSeminormFamily ℝ Joint ℂ) W := by
  let q : Seminorm ℝ 𝓢(Joint, ℂ) :=
    (S.sup (schwartzSeminormFamily ℝ E ℂ)).comp T.toLinearMap
  have hq : Continuous q :=
    (((schwartz_withSeminorms ℝ E ℂ).finset_sups).continuous_seminorm S).comp T.continuous
  obtain ⟨s, C, hC, hbound⟩ :=
    Seminorm.bound_of_continuous (schwartz_withSeminorms ℝ Joint ℂ) q hq
  refine ⟨s, C, ?_, ?_⟩
  · exact_mod_cast (pos_iff_ne_zero.mpr hC : 0 < C)
  · intro W
    exact Seminorm.le_def.mp hbound W

def productDecayConstant (W : 𝓢(Joint, ℂ)) : ℝ :=
  2 ^ (8:ℕ) * (Finset.Iic (8,0)).sup (schwartzSeminormFamily ℝ Joint ℂ) W

theorem product_decay (W : 𝓢(Joint, ℂ)) (x y : ℂ) :
    ((1+‖x‖^2)^2 * (1+‖y‖^2)^2) * ‖W (point x y)‖ ≤ productDecayConstant W := by
  have hx := WithLp.norm_fst_le ℂ (point x y)
  have hy := WithLp.norm_snd_le ℂ (point x y)
  change ‖x‖ ≤ ‖point x y‖ at hx
  change ‖y‖ ≤ ‖point x y‖ at hy
  have hx2 : 1+‖x‖^2 ≤ (1+‖point x y‖)^2 := by nlinarith [norm_nonneg (point x y), norm_nonneg x, norm_nonneg y]
  have hy2 : 1+‖y‖^2 ≤ (1+‖point x y‖)^2 := by nlinarith [norm_nonneg (point x y), norm_nonneg x, norm_nonneg y]
  have hpow : (1+‖x‖^2)^2 * (1+‖y‖^2)^2 ≤ (1+‖point x y‖)^8 := by
    calc
      _ ≤ ((1+‖point x y‖)^2)^2 * ((1+‖point x y‖)^2)^2 := by gcongr
      _ = _ := by ring
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
    (m := (8,0)) (k := 8) (n := 0) le_rfl le_rfl W (point x y)
  simp only [norm_iteratedFDeriv_zero] at h
  exact (mul_le_mul_of_nonneg_right hpow (norm_nonneg _)).trans h

theorem norm_le_product_majorant (W : 𝓢(Joint, ℂ)) (x y : ℂ) :
    ‖W (point x y)‖ ≤ productDecayConstant W * (planeMajorant x * planeMajorant y) := by
  rw [planeMajorant, planeMajorant, ← mul_inv, ← div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity)).mpr
  simpa only [mul_comm] using product_decay W x y

theorem planeMajorant_eisenstein_summable :
    Summable (fun m : Eisenstein.O =>
      planeMajorant (ringComplex m)) := by
  have hs := CubicEisenstein.summable_embedding_rpow (-4) (by norm_num)
  rw [← Finset.summable_compl_iff (s := ({0} : Finset Eisenstein.O))]
  apply Summable.of_nonneg_of_le (fun _ => by unfold planeMajorant; positivity) _
    (hs.subtype (fun m : Eisenstein.O => m ∉ ({0} : Finset _)))
  intro m
  have hm : m.val ≠ 0 := by simpa using m.property
  have hn : 0 < ‖ringComplex m.val‖ := norm_pos_iff.mpr
    (ringComplex_ne_zero hm)
  change ((1+‖ringComplex m.val‖^2)^2)⁻¹ ≤
    ‖ringComplex m.val‖ ^ (-4:ℝ)
  rw [show (-4:ℝ) = -(4:ℝ) by rfl, Real.rpow_neg hn.le, Real.rpow_ofNat]
  apply inv_anti₀ (by positivity)
  nlinarith [sq_nonneg (‖ringComplex m.val‖^2)]

theorem joint_eisenstein_summable_norm (W : 𝓢(Joint, ℂ)) :
    Summable (fun m : Eisenstein.O × Eisenstein.O =>
      ‖W (embeddingPair m)‖) := by
  have hs := planeMajorant_eisenstein_summable.mul_of_nonneg
    planeMajorant_eisenstein_summable
    (fun _ => by unfold planeMajorant; positivity)
    (fun _ => by unfold planeMajorant; positivity)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    (hs.mul_left (productDecayConstant W))
  intro m
  exact norm_le_product_majorant W _ _

theorem joint_weighted_summable {R : Type*} (q : Eisenstein.O → R)
    (a : R × R → ℂ) (B : ℝ) (hB : ∀ r, ‖a r‖ ≤ B) (W : 𝓢(Joint, ℂ)) :
    Summable (fun m : Eisenstein.O × Eisenstein.O =>
      a (q m.1,q m.2) * W (embeddingPair m)) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    ((joint_eisenstein_summable_norm W).mul_left B)
  intro m
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _)

open scoped LineDeriv

theorem leftSlice_lineDeriv (F : 𝓢(Joint, ℂ)) (η v : ℂ) :
    ∂_{v} (leftSlice F η) = leftSlice (∂_{leftInjection v} F) η := by
  apply SchwartzMap.ext
  intro x
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, leftSlice_apply,
    SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have hd : HasFDerivAt (fun x : ℂ => point x η) leftInjection x := by
    simp only [point_eq_add]
    exact leftInjection.hasFDerivAt.add_const _
  have hc := (F.hasFDerivAt (point x η)).comp x hd
  change fderiv ℝ ((F : Joint → ℂ) ∘ (fun y => point y η)) x v = _
  rw [hc.fderiv]
  rfl

theorem norm_inverse_lineDeriv (g : 𝓢(ℂ, ℂ)) (v x : ℂ) :
    ‖(𝓕⁻ (∂_{v} g)) x‖ = (2 * Real.pi) * |inner ℝ x v| * ‖(𝓕⁻ g) x‖ := by
  have ht : (fun u : ℂ => inner ℝ u v).HasTemperateGrowth := by fun_prop
  have hc : ‖(-(2 * Real.pi * Complex.I) : ℂ)‖ = 2 * Real.pi := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [SchwartzMap.fourierInv_lineDerivOp_eq]
  simp only [smul_apply, SchwartzMap.smulLeftCLM_apply_apply ht,
    norm_smul]
  rw [hc]
  simp only [Real.norm_eq_abs, mul_assoc]

theorem inner_sq_mul_norm_inverse_le (g : 𝓢(ℂ, ℂ)) (v x : ℂ) :
    (inner ℝ x v)^2 * ‖(𝓕⁻ g) x‖ ≤ ‖(𝓕⁻ (∂_{v} (∂_{v} g))) x‖ := by
  rw [norm_inverse_lineDeriv, norm_inverse_lineDeriv]
  have hp : 1 ≤ (2 * Real.pi)^2 := by nlinarith [Real.pi_gt_three]
  calc
    _ ≤ ((2 * Real.pi)^2 * (inner ℝ x v)^2) * ‖(𝓕⁻ g) x‖ :=
      mul_le_mul_of_nonneg_right (le_mul_of_one_le_left (sq_nonneg _) hp) (norm_nonneg _)
    _ = _ := by rw [← sq_abs (inner ℝ x v)]; ring

theorem norm_sq_mul_norm_inverse_le (g : 𝓢(ℂ, ℂ)) (x : ℂ) :
    ‖x‖^2 * ‖(𝓕⁻ g) x‖ ≤
      ‖(𝓕⁻ (∂_{(1:ℂ)} (∂_{(1:ℂ)} g))) x‖ +
      ‖(𝓕⁻ (∂_{Complex.I} (∂_{Complex.I} g))) x‖ := by
  have h1 := inner_sq_mul_norm_inverse_le g 1 x
  have hi := inner_sq_mul_norm_inverse_le g Complex.I x
  have he : (inner ℝ x (1:ℂ))^2 + (inner ℝ x Complex.I)^2 = ‖x‖^2 := by
    rw [Complex.sq_norm]
    simp [Complex.inner, Complex.normSq_apply, sq]
  rw [← he, add_mul]
  exact add_le_add h1 hi

theorem norm_inverse_leftSlice_le (F : 𝓢(Joint, ℂ)) (η x : ℂ) :
    ‖(𝓕⁻ (leftSlice F η)) x‖ ≤
      productDecayConstant F * planeMajorant η * ∫ y : ℂ, planeMajorant y := by
  have hb : Integrable (fun y : ℂ =>
      productDecayConstant F * planeMajorant η * planeMajorant y) :=
    planeMajorant_integrable.const_mul _
  have h := norm_integral_le_of_norm_le
    (f := fun y : ℂ => Real.fourierChar (inner ℝ y x) • leftSlice F η y) hb
    (Eventually.of_forall fun y => by
      simpa only [Circle.smul_def, smul_eq_mul, norm_mul, Circle.norm_coe, one_mul,
        leftSlice_apply, mul_left_comm, mul_assoc, mul_comm] using norm_le_product_majorant F y η)
  rw [congrFun (SchwartzMap.fourierInv_coe (leftSlice F η)) x, Real.fourierInv_eq]
  simpa only [integral_const_mul] using h

def leftSecondReal (F : 𝓢(Joint, ℂ)) : 𝓢(Joint, ℂ) :=
  ∂_{leftInjection (1:ℂ)} (∂_{leftInjection (1:ℂ)} F)

def leftSecondImag (F : 𝓢(Joint, ℂ)) : 𝓢(Joint, ℂ) :=
  ∂_{leftInjection Complex.I} (∂_{leftInjection Complex.I} F)

def sliceIntegralBound (F : 𝓢(Joint, ℂ)) : ℝ :=
  productDecayConstant F * ∫ y : ℂ, planeMajorant y

def firstDecayBound (F : 𝓢(Joint, ℂ)) : ℝ :=
  sliceIntegralBound F + sliceIntegralBound (leftSecondReal F) +
    sliceIntegralBound (leftSecondImag F)

def secondDecayBound (F : 𝓢(Joint, ℂ)) : ℝ :=
  firstDecayBound F + firstDecayBound (leftSecondReal F) +
    firstDecayBound (leftSecondImag F)

theorem inverse_leftSlice_weight_le (F : 𝓢(Joint, ℂ)) (η x : ℂ) :
    (1+‖x‖^2) * ‖(𝓕⁻ (leftSlice F η)) x‖ ≤
      ‖(𝓕⁻ (leftSlice F η)) x‖ +
      ‖(𝓕⁻ (leftSlice (leftSecondReal F) η)) x‖ +
      ‖(𝓕⁻ (leftSlice (leftSecondImag F) η)) x‖ := by
  have h := norm_sq_mul_norm_inverse_le (leftSlice F η) x
  simp only [leftSlice_lineDeriv] at h
  change ‖x‖^2 * ‖(𝓕⁻ (leftSlice F η)) x‖ ≤
    ‖(𝓕⁻ (leftSlice (leftSecondReal F) η)) x‖ +
    ‖(𝓕⁻ (leftSlice (leftSecondImag F) η)) x‖ at h
  nlinarith

theorem inverse_leftSlice_first_decay (F : 𝓢(Joint, ℂ)) (η x : ℂ) :
    (1+‖x‖^2) * ‖(𝓕⁻ (leftSlice F η)) x‖ ≤ firstDecayBound F * planeMajorant η := by
  apply (inverse_leftSlice_weight_le F η x).trans
  have h0 := norm_inverse_leftSlice_le F η x
  have h1 := norm_inverse_leftSlice_le (leftSecondReal F) η x
  have h2 := norm_inverse_leftSlice_le (leftSecondImag F) η x
  dsimp [firstDecayBound, sliceIntegralBound]
  nlinarith

theorem inverse_leftSlice_second_decay (F : 𝓢(Joint, ℂ)) (η x : ℂ) :
    (1+‖x‖^2)^2 * ‖(𝓕⁻ (leftSlice F η)) x‖ ≤ secondDecayBound F * planeMajorant η := by
  have h := mul_le_mul_of_nonneg_left (inverse_leftSlice_weight_le F η x)
    (show 0 ≤ 1+‖x‖^2 by positivity)
  have h0 := inverse_leftSlice_first_decay F η x
  have h1 := inverse_leftSlice_first_decay (leftSecondReal F) η x
  have h2 := inverse_leftSlice_first_decay (leftSecondImag F) η x
  dsimp [secondDecayBound]
  nlinarith

theorem norm_partialFourier_le (W : 𝓢(Joint, ℂ)) (η x : ℂ) :
    ‖partialFourier W η x‖ ≤
      secondDecayBound (𝓕 W) * (planeMajorant x * planeMajorant η) := by
  rw [← partialFourierSchwartz_apply]
  change ‖(𝓕⁻ (leftSlice (𝓕 W) η)) x‖ ≤ _
  have h := inverse_leftSlice_second_decay (𝓕 W) η x
  have hd : ‖(𝓕⁻ (leftSlice (𝓕 W) η)) x‖ ≤
      secondDecayBound (𝓕 W) * planeMajorant η / (1+‖x‖^2)^2 :=
    (le_div_iff₀ (by positivity)).mpr (by nlinarith [h])
  convert hd using 1
  simp only [planeMajorant, div_eq_mul_inv]
  ring

open SchwartzPlanePoisson

theorem planeMajorant_cartesian_summable :
    Summable (fun p : ℤ × ℤ => planeMajorant (complexPoint (p.1:ℝ) (p.2:ℝ))) := by
  apply Summable.of_nonneg_of_le (fun _ => by unfold planeMajorant; positivity) _
    summable_int_cauchy_product
  intro p
  change ((1+‖complexPoint (p.1:ℝ) (p.2:ℝ)‖^2)^2)⁻¹ ≤ _
  rw [← mul_inv]
  apply inv_anti₀ (by positivity)
  rw [Complex.sq_norm]
  simp only [complexPoint, Complex.normSq_apply]
  nlinarith [sq_nonneg (p.1:ℝ), sq_nonneg (p.2:ℝ),
    mul_nonneg (sq_nonneg (p.1:ℝ)) (sq_nonneg (p.2:ℝ))]

def cartesianPoint (p : ℤ × ℤ) : ℂ := complexPoint (p.1:ℝ) (p.2:ℝ)

theorem joint_cartesian_summable_norm (W : 𝓢(Joint, ℂ)) :
    Summable (fun p : (ℤ × ℤ) × (ℤ × ℤ) =>
      ‖W (point (cartesianPoint p.1) (cartesianPoint p.2))‖) := by
  have hs := planeMajorant_cartesian_summable.mul_of_nonneg
    planeMajorant_cartesian_summable
    (fun _ => by unfold planeMajorant; positivity)
    (fun _ => by unfold planeMajorant; positivity)
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun _ => norm_le_product_majorant W _ _) (hs.mul_left (productDecayConstant W))

theorem partialFourier_cartesian_summable_norm (W : 𝓢(Joint, ℂ)) :
    Summable (fun p : (ℤ × ℤ) × (ℤ × ℤ) =>
      ‖partialFourier W (cartesianPoint p.2) (cartesianPoint p.1)‖) := by
  have hs := planeMajorant_cartesian_summable.mul_of_nonneg
    planeMajorant_cartesian_summable
    (fun _ => by unfold planeMajorant; positivity)
    (fun _ => by unfold planeMajorant; positivity)
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun _ => norm_partialFourier_le W _ _) (hs.mul_left (secondDecayBound (𝓕 W)))

theorem rightSlice_isometry (x : ℂ) : Isometry (fun y : ℂ => point x y) := by
  apply Isometry.of_dist_eq
  intro y z
  simp only [dist_eq_norm, point_eq_add, add_sub_add_left_eq_sub, ← map_sub]
  exact WithLp.norm_toLp_snd 2 ℂ ℂ (y-z)

def rightSlice (W : 𝓢(Joint, ℂ)) (x : ℂ) : 𝓢(ℂ, ℂ) :=
  SchwartzMap.compCLMOfAntilipschitz ℂ
    (by simp only [point_eq_add]; fun_prop : (fun y : ℂ => point x y).HasTemperateGrowth)
    (rightSlice_isometry x).antilipschitz W

@[simp] theorem rightSlice_apply (W : 𝓢(Joint, ℂ)) (x y : ℂ) :
    rightSlice W x y = W (point x y) := rfl

theorem rightSlice_poisson (W : 𝓢(Joint, ℂ)) (x : ℂ) :
    (∑' p : ℤ × ℤ, W (point x (cartesianPoint p))) =
      ∑' p : ℤ × ℤ, partialFourier W (cartesianPoint p) x := by
  have h := integer_pair_poisson (rightSlice W x)
  have hcoe : (rightSlice W x : ℂ → ℂ) = fun y => W (point x y) := rfl
  simpa only [rightSlice_apply, SchwartzMap.fourier_coe, hcoe, partialFourier, cartesianPoint] using h

private theorem joint_cartesian_eq_partial (W : 𝓢(Joint, ℂ)) :
    (∑' p : (ℤ × ℤ) × (ℤ × ℤ), W (point (cartesianPoint p.1) (cartesianPoint p.2))) =
      ∑' n : ℤ × ℤ, ∑' m : ℤ × ℤ,
        partialFourier W (cartesianPoint n) (cartesianPoint m) := by
  have hp := (joint_cartesian_summable_norm W).of_norm
  have hm := (partialFourier_cartesian_summable_norm W).of_norm
  calc
    _ = ∑' m : ℤ × ℤ, ∑' n : ℤ × ℤ,
        W (point (cartesianPoint m) (cartesianPoint n)) := hp.tsum_prod
    _ = ∑' m : ℤ × ℤ, ∑' n : ℤ × ℤ,
        partialFourier W (cartesianPoint n) (cartesianPoint m) := by
      apply tsum_congr
      intro m
      exact rightSlice_poisson W _
    _ = _ := hm.tsum_comm.symm

private theorem partial_cartesian_poisson (W : 𝓢(Joint, ℂ)) (n : ℤ × ℤ) :
    (∑' m : ℤ × ℤ, partialFourier W (cartesianPoint n) (cartesianPoint m)) =
      ∑' m : ℤ × ℤ, (𝓕 W) (point (cartesianPoint m) (cartesianPoint n)) := by
  calc
    _ = ∑' m : ℤ × ℤ, partialFourierSchwartz W (cartesianPoint n) (cartesianPoint m) :=
      tsum_congr fun m =>
        (partialFourierSchwartz_apply W (cartesianPoint n) (cartesianPoint m)).symm
    _ = ∑' m : ℤ × ℤ,
        (𝓕 (partialFourierSchwartz W (cartesianPoint n)) : 𝓢(ℂ, ℂ)) (cartesianPoint m) := by
      simpa only [cartesianPoint] using
        integer_pair_poisson (partialFourierSchwartz W (cartesianPoint n))
    _ = _ := tsum_congr fun m =>
      fourier_partialFourierSchwartz W (cartesianPoint m) (cartesianPoint n)

private theorem cartesian_swap_tsum (F : 𝓢(Joint, ℂ)) :
    (∑' n : ℤ × ℤ, ∑' m : ℤ × ℤ, F (point (cartesianPoint m) (cartesianPoint n))) =
      ∑' p : (ℤ × ℤ) × (ℤ × ℤ), F (point (cartesianPoint p.1) (cartesianPoint p.2)) := by
  have hF := (joint_cartesian_summable_norm F).of_norm
  exact hF.tsum_comm.trans hF.tsum_prod.symm

private theorem partial_cartesian_eq_fourier (W : 𝓢(Joint, ℂ)) :
    (∑' n : ℤ × ℤ, ∑' m : ℤ × ℤ,
      partialFourier W (cartesianPoint n) (cartesianPoint m)) =
      ∑' p : (ℤ × ℤ) × (ℤ × ℤ), (𝓕 W) (point (cartesianPoint p.1) (cartesianPoint p.2)) := by
  exact (tsum_congr (partial_cartesian_poisson W)).trans (cartesian_swap_tsum (𝓕 W))

theorem joint_cartesian_poisson (W : 𝓢(Joint, ℂ)) :
    (∑' p : (ℤ × ℤ) × (ℤ × ℤ), W (point (cartesianPoint p.1) (cartesianPoint p.2))) =
      ∑' p : (ℤ × ℤ) × (ℤ × ℤ), (𝓕 W) (point (cartesianPoint p.1) (cartesianPoint p.2)) := by
  exact (joint_cartesian_eq_partial W).trans (partial_cartesian_eq_fourier W)

def blockMap (A : ℂ ≃L[ℝ] ℂ) : Joint ≃L[ℝ] Joint :=
  ((A.toLinearEquiv.prodCongr A.toLinearEquiv).withLpCongr 2).toContinuousLinearEquiv

@[simp] theorem blockMap_apply (A : ℂ ≃L[ℝ] ℂ) (z : Joint) :
    blockMap A z = point (A z.fst) (A z.snd) := rfl

@[simp] theorem blockMap_symm_apply (A : ℂ ≃L[ℝ] ℂ) (z : Joint) :
    (blockMap A).symm z = point (A.symm z.fst) (A.symm z.snd) := rfl

theorem blockMap_det (A : ℂ ≃L[ℝ] ℂ) :
    LinearMap.det (blockMap A : Joint →ₗ[ℝ] Joint) =
      LinearMap.det (A : ℂ →ₗ[ℝ] ℂ) ^ 2 := by
  have h := LinearMap.det_conj
    ((A : ℂ →ₗ[ℝ] ℂ).prodMap (A : ℂ →ₗ[ℝ] ℂ))
    (WithLp.linearEquiv 2 ℝ (ℂ × ℂ)).symm
  rw [LinearMap.det_prodMap] at h
  convert h using 1 <;> first | rfl | ring

def jointInverseJacobian (A : Joint ≃L[ℝ] Joint) : ℝ :=
  |(LinearMap.det (A : Joint →ₗ[ℝ] Joint))⁻¹|

theorem jointInverseJacobian_blockMap (A : ℂ ≃L[ℝ] ℂ) :
    jointInverseJacobian (blockMap A) = inverseJacobian A ^ 2 := by
  rw [jointInverseJacobian, blockMap_det, ← inv_pow, abs_pow]
  rfl

def jointDual (A : Joint ≃L[ℝ] Joint) : Joint →L[ℝ] Joint :=
  A.symm.toContinuousLinearMap.adjoint

theorem joint_inner_linear_dual (A : Joint ≃L[ℝ] Joint) (x y : Joint) :
    inner ℝ (A x) (jointDual A y) = inner ℝ x y := by
  rw [jointDual, ContinuousLinearMap.adjoint_inner_right]
  simp

theorem jointDual_blockMap (A : ℂ ≃L[ℝ] ℂ) (ξ η : ℂ) :
    jointDual (blockMap A) (point ξ η) = point (dualMap A ξ) (dualMap A η) := by
  apply ext_inner_left ℝ
  intro z
  rw [jointDual, ContinuousLinearMap.adjoint_inner_right]
  change inner ℝ (point (A.symm z.fst) (A.symm z.snd)) (point ξ η) = _
  simp only [point, WithLp.prod_inner_apply, dualMap,
    ContinuousLinearMap.adjoint_inner_right]
  rfl

theorem joint_integral_comp_linearEquiv (A : Joint ≃L[ℝ] Joint) (f : Joint → ℂ) :
    (∫ x : Joint, f (A x)) = jointInverseJacobian A • ∫ x : Joint, f x := by
  have h := integral_map_equiv («μ» := (volume : Measure Joint))
    A.toHomeomorph.toMeasurableEquiv f
  have hm : Measure.map A (volume : Measure Joint) =
      ENNReal.ofReal (jointInverseJacobian A) • volume :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar volume A.toLinearEquiv.isUnit_det'.ne_zero
  change (∫ y : Joint, f y ∂Measure.map A volume) = (∫ x : Joint, f (A x)) at h
  rw [hm, integral_smul_measure, ENNReal.toReal_ofReal
    (show 0 ≤ jointInverseJacobian A from abs_nonneg _)] at h
  exact h.symm

theorem joint_fourier_comp_linearEquiv (A : Joint ≃L[ℝ] Joint)
    (f : Joint → ℂ) (w : Joint) :
    𝓕 (f ∘ A) w = jointInverseJacobian A • 𝓕 f (jointDual A w) := by
  let H : Joint → ℂ := fun z => Real.fourierChar (-inner ℝ z (jointDual A w)) • f z
  calc
    𝓕 (f ∘ A) w = ∫ x : Joint, H (A x) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        simp only [H, joint_inner_linear_dual, Function.comp_apply]
        rfl
    _ = jointInverseJacobian A • ∫ z : Joint, H z := joint_integral_comp_linearEquiv A H
    _ = _ := rfl

def jointTranslate (W : 𝓢(Joint, ℂ)) (b : Joint) : 𝓢(Joint, ℂ) :=
  SchwartzMap.compCLMOfAntilipschitz ℂ (g := fun z : Joint => z+b)
    (by fun_prop) (isometry_add_right b).antilipschitz W

def jointAffine (W : 𝓢(Joint, ℂ)) (A : Joint ≃L[ℝ] Joint) (b : Joint) : 𝓢(Joint, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A (jointTranslate W b)

@[simp] theorem jointAffine_apply (W : 𝓢(Joint, ℂ)) (A : Joint ≃L[ℝ] Joint) (b z : Joint) :
    jointAffine W A b z = W (A z+b) := rfl

theorem joint_fourier_affine (W : 𝓢(Joint, ℂ)) (A : Joint ≃L[ℝ] Joint) (b w : Joint) :
    (𝓕 (jointAffine W A b)) w =
      jointInverseJacobian A •
        (Real.fourierChar (inner ℝ b (jointDual A w)) • (𝓕 W) (jointDual A w)) := by
  rw [congrFun (SchwartzMap.fourier_coe _) w]
  change 𝓕 ((fun z => W (z+b)) ∘ A) w = _
  rw [joint_fourier_comp_linearEquiv]
  have ht : 𝓕 (fun z => W (z+b)) (jointDual A w) =
      Real.fourierChar (inner ℝ b (jointDual A w)) • 𝓕 (W : Joint → ℂ) (jointDual A w) :=
    congrFun (VectorFourier.fourierIntegral_comp_add_right Real.fourierChar
      (volume : Measure Joint) (innerₗ Joint) (W : Joint → ℂ) b) (jointDual A w)
  rw [ht]
  rw [congrFun (SchwartzMap.fourier_coe W) (jointDual A w)]

theorem joint_affine_poisson (W : 𝓢(Joint, ℂ)) (A : Joint ≃L[ℝ] Joint) (b : Joint) :
    (∑' p : (ℤ × ℤ) × (ℤ × ℤ),
      W (A (point (cartesianPoint p.1) (cartesianPoint p.2))+b)) =
      jointInverseJacobian A • ∑' p : (ℤ × ℤ) × (ℤ × ℤ),
        Real.fourierChar (inner ℝ b
          (jointDual A (point (cartesianPoint p.1) (cartesianPoint p.2)))) •
        (𝓕 W) (jointDual A (point (cartesianPoint p.1) (cartesianPoint p.2))) := by
  have h := joint_cartesian_poisson (jointAffine W A b)
  simp only [jointAffine_apply, joint_fourier_affine] at h
  rw [tsum_const_smul''] at h
  exact h

def jointFrequency (c : ℂ) (hc : c ≠ 0) (p : (ℤ × ℤ) × (ℤ × ℤ)) : Joint :=
  point (eisensteinDualFrequency c hc p.1) (eisensteinDualFrequency c hc p.2)

open Eisenstein 

theorem actual_joint_coset_poisson (W : 𝓢(Joint, ℂ)) (b : O × O) (c : O) (hc : c ≠ 0) :
    (∑' m : O × O, W (embeddingPair (b.1+c*m.1,b.2+c*m.2))) =
      (2 / (Real.sqrt 3 * ‖ringComplex c‖^2))^2 •
        ∑' p : (ℤ × ℤ) × (ℤ × ℤ),
          Real.fourierChar (inner ℝ (embeddingPair b)
            (jointFrequency (ringComplex c) (ringComplex_ne_zero hc) p)) •
            (𝓕 W) (jointFrequency (ringComplex c) (ringComplex_ne_zero hc) p) := by
  let A := eisensteinLatticeMap (ringComplex c) (ringComplex_ne_zero hc)
  have h := joint_affine_poisson W (blockMap A) (embeddingPair b)
  simp only [jointInverseJacobian_blockMap, jointDual_blockMap] at h
  rw [eisenstein_inverseJacobian] at h
  calc
    _ = ∑' p : (ℤ × ℤ) × (ℤ × ℤ), W (embeddingPair
        (b.1+c*Eisenstein.Coordinates.coordinateEquiv.symm p.1,b.2+c*Eisenstein.Coordinates.coordinateEquiv.symm p.2)) :=
      ((Eisenstein.Coordinates.coordinateEquiv.symm.prodCongr Eisenstein.Coordinates.coordinateEquiv.symm).tsum_eq _).symm
    _ = ∑' p : (ℤ × ℤ) × (ℤ × ℤ),
        W (blockMap A (point (cartesianPoint p.1) (cartesianPoint p.2))+embeddingPair b) := by
      apply tsum_congr
      intro p
      congr 1
      change point (ringComplex (b.1+c*Eisenstein.Coordinates.eval p.1.1 p.1.2))
        (ringComplex (b.2+c*Eisenstein.Coordinates.eval p.2.1 p.2.2)) = _
      simp only [map_add, map_mul, blockMap_apply, point]
      rw [← eisensteinLatticeMap_point (ringComplex c) (ringComplex_ne_zero hc) p.1,
        ← eisensteinLatticeMap_point (ringComplex c) (ringComplex_ne_zero hc) p.2]
      change point (ringComplex b.1 + A (cartesianPoint p.1))
        (ringComplex b.2 + A (cartesianPoint p.2)) =
          point (A (cartesianPoint p.1)+ringComplex b.1)
            (A (cartesianPoint p.2)+ringComplex b.2)
      simp only [add_comm]
    _ = _ := h

theorem joint_dual_summable_norm (W : 𝓢(Joint, ℂ)) (A : Joint ≃L[ℝ] Joint) :
    Summable (fun p : (ℤ × ℤ) × (ℤ × ℤ) =>
      ‖(𝓕 W) (jointDual A (point (cartesianPoint p.1) (cartesianPoint p.2)))‖) := by
  have hJ : 0 < jointInverseJacobian A :=
    abs_pos.mpr (inv_ne_zero A.toLinearEquiv.isUnit_det'.ne_zero)
  have hs := joint_cartesian_summable_norm (𝓕 (jointAffine W A 0))
  have hn (p : (ℤ × ℤ) × (ℤ × ℤ)) :
      ‖(𝓕 (jointAffine W A 0)) (point (cartesianPoint p.1) (cartesianPoint p.2))‖ =
      jointInverseJacobian A *
        ‖(𝓕 W) (jointDual A (point (cartesianPoint p.1) (cartesianPoint p.2)))‖ := by
    rw [joint_fourier_affine]
    simp [abs_of_pos hJ]
  simp_rw [hn] at hs
  have hi := hs.mul_left (jointInverseJacobian A)⁻¹
  simpa only [← mul_assoc, inv_mul_cancel₀ hJ.ne', one_mul] using hi

theorem jointFrequency_summable_norm (W : 𝓢(Joint, ℂ)) (c : ℂ) (hc : c ≠ 0) :
    Summable (fun p : (ℤ × ℤ) × (ℤ × ℤ) => ‖(𝓕 W) (jointFrequency c hc p)‖) := by
  have h := joint_dual_summable_norm W (blockMap (eisensteinLatticeMap c hc))
  simpa only [jointDual_blockMap, jointFrequency, eisensteinDualFrequency, cartesianPoint] using h

abbrev Residue (c : O) := O ⧸ Ideal.span {c}

def quotientPair (c : O) (m : O × O) : Residue c × Residue c :=
  (Ideal.Quotient.mk (Ideal.span {c}) m.1, Ideal.Quotient.mk (Ideal.span {c}) m.2)

def representativePair (c : O) (r : Residue c × Residue c) : O × O :=
  (GaussianShiftedPartition.representative c r.1, GaussianShiftedPartition.representative c r.2)

def jointFiberSplit (c : O) (r : Residue c × Residue c) :
    (quotientPair c ⁻¹' {r}) ≃
      ((Ideal.Quotient.mk (Ideal.span {c})) ⁻¹' {r.1}) ×
      ((Ideal.Quotient.mk (Ideal.span {c})) ⁻¹' {r.2}) where
  toFun z := (⟨z.1.1, congrArg Prod.fst z.2⟩, ⟨z.1.2, congrArg Prod.snd z.2⟩)
  invFun z := ⟨(z.1.1,z.2.1), Prod.ext z.1.2 z.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem joint_fiber_tsum (c : O) (hc : c ≠ 0) (r : Residue c × Residue c)
    (W : O × O → ℂ) :
    (∑' m : quotientPair c ⁻¹' {r}, W m.1) =
      ∑' m : O × O, W ((representativePair c r).1+c*m.1,
        (representativePair c r).2+c*m.2) := by
  let e1 := GaussianFiberEquiv.fiberEquiv c hc r.1
    (GaussianShiftedPartition.representative c r.1)
    (GaussianShiftedPartition.representative_spec c r.1)
  let e2 := GaussianFiberEquiv.fiberEquiv c hc r.2
    (GaussianShiftedPartition.representative c r.2)
    (GaussianShiftedPartition.representative_spec c r.2)
  let e := (e1.prodCongr e2).trans (jointFiberSplit c r).symm
  exact (e.tsum_eq (fun m => W m.1)).symm

def residueFourier (c : O) (hc : c ≠ 0) (a : Residue c × Residue c → ℂ)
    (p : (ℤ × ℤ) × (ℤ × ℤ)) : ℂ :=
  ∑' r : Residue c × Residue c, a r *
    (Real.fourierChar (inner ℝ (embeddingPair (representativePair c r))
      (jointFrequency (ringComplex c) (ringComplex_ne_zero hc) p)) : ℂ)

theorem actual_joint_periodic_poisson (W : 𝓢(Joint, ℂ)) (c : O) (hc : c ≠ 0)
    (a : Residue c × Residue c → ℂ) :
    letI : Finite (Residue c) := finiteEisensteinQuotientOfNonzero hc
    letI : Fintype (Residue c) := Fintype.ofFinite _
    (∑' m : O × O, a (quotientPair c m) * W (embeddingPair m)) =
      ∑ r : Residue c × Residue c, a r *
        ((2 / (Real.sqrt 3 * ‖ringComplex c‖^2))^2 •
          ∑' p : (ℤ × ℤ) × (ℤ × ℤ),
            Real.fourierChar (inner ℝ (embeddingPair (representativePair c r))
              (jointFrequency (ringComplex c) (ringComplex_ne_zero hc) p)) •
              (𝓕 W) (jointFrequency (ringComplex c) (ringComplex_ne_zero hc) p)) := by
  classical
  let : Finite (Residue c) := finiteEisensteinQuotientOfNonzero hc
  let : Fintype (Residue c) := Fintype.ofFinite _
  have ha (r : Residue c × Residue c) : ‖a r‖ ≤ ∑ t : Residue c × Residue c, ‖a t‖ :=
    Finset.single_le_sum (fun t _ => norm_nonneg (a t)) (Finset.mem_univ r)
  have hs := joint_weighted_summable (Ideal.Quotient.mk (Ideal.span {c})) a _ ha W
  rw [GaussianAbelPartition.tsum_periodic_weighted_partition (quotientPair c) a
    (fun m => W (embeddingPair m)) hs]
  apply Finset.sum_congr rfl
  intro r hr
  congr 1
  exact (joint_fiber_tsum c hc r (fun m => W (embeddingPair m))).trans
    (actual_joint_coset_poisson W (representativePair c r) c hc)

theorem actual_joint_periodic_fourier (W : 𝓢(Joint, ℂ)) (c : O) (hc : c ≠ 0)
    (a : Residue c × Residue c → ℂ) :
    (∑' m : O × O, a (quotientPair c m) * W (embeddingPair m)) =
      (2 / (Real.sqrt 3 * ‖ringComplex c‖^2))^2 •
        ∑' p : (ℤ × ℤ) × (ℤ × ℤ), residueFourier c hc a p *
          (𝓕 W) (jointFrequency (ringComplex c) (ringComplex_ne_zero hc) p) := by
  classical
  let : Finite (Residue c) := finiteEisensteinQuotientOfNonzero hc
  let : Fintype (Residue c) := Fintype.ofFinite _
  rw [actual_joint_periodic_poisson W c hc a]
  have hs (r : Residue c × Residue c) : Summable (fun p : (ℤ × ℤ) × (ℤ × ℤ) =>
      a r * (Real.fourierChar (inner ℝ (embeddingPair (representativePair c r))
        (jointFrequency (ringComplex c) (ringComplex_ne_zero hc) p)) •
        (𝓕 W) (jointFrequency (ringComplex c) (ringComplex_ne_zero hc) p))) := by
    apply Summable.mul_left
    apply Summable.of_norm
    simpa only [Circle.norm_smul] using
      jointFrequency_summable_norm W (ringComplex c) (ringComplex_ne_zero hc)
  simp_rw [mul_smul_comm, ← tsum_mul_left]
  rw [← Finset.smul_sum, ← Summable.tsum_finsetSum (fun r _ => hs r)]
  congr 1
  apply tsum_congr
  intro p
  simp only [residueFourier, tsum_fintype, Circle.smul_def, smul_eq_mul,
    Finset.sum_mul, mul_assoc]

@[simp] theorem jointFrequency_zero (c : ℂ) (hc : c ≠ 0) :
    jointFrequency c hc 0 = 0 := by
  have h : complexPoint (0:ℝ) 0 = 0 := by apply Complex.ext <;> rfl
  simp [jointFrequency, eisensteinDualFrequency, h, point]

@[simp] theorem residueFourier_zero (c : O) (hc : c ≠ 0)
    (a : Residue c × Residue c → ℂ) :
    residueFourier c hc a 0 = ∑' r, a r := by
  simp [residueFourier]

theorem residueFourier_norm_le (c : O) (hc : c ≠ 0)
    (a : Residue c × Residue c → ℂ) (B : ℝ) (hB : ∀ r, ‖a r‖ ≤ B)
    (p : (ℤ × ℤ) × (ℤ × ℤ)) :
    ‖residueFourier c hc a p‖ ≤ (Ideal.absNorm (Ideal.span {c}) : ℝ)^2 * B := by
  classical
  let : Finite (Residue c) := finiteEisensteinQuotientOfNonzero hc
  let : Fintype (Residue c) := Fintype.ofFinite _
  rw [residueFourier, tsum_fintype]
  calc
    _ ≤ ∑ r : Residue c × Residue c, ‖a r *
        (Real.fourierChar (inner ℝ (embeddingPair (representativePair c r))
          (jointFrequency (ringComplex c) (ringComplex_ne_zero hc) p)) : ℂ)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ r : Residue c × Residue c, B := by
      apply Finset.sum_le_sum
      intro r hr
      simpa only [norm_mul, Circle.norm_coe, mul_one] using hB r
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_prod,
        Nat.cast_mul, Ideal.absNorm_apply, Submodule.cardQuot_apply,
        Nat.card_eq_fintype_card, Residue, pow_two]

theorem principal_joint_inverse_covolume (c : O) (hc : c ≠ 0) :
    (2 / (Real.sqrt 3 * ‖ringComplex c‖^2))^2 *
      (Ideal.absNorm (Ideal.span {c}) : ℝ)^2 = 4/3 := by
  have hn : ‖ringComplex c‖ ≠ 0 := norm_ne_zero_iff.mpr (ringComplex_ne_zero hc)
  rw [← ringComplex_norm_sq_eq_absNorm_span]
  have hs : (Real.sqrt 3)^2 = (3:ℝ) := Real.sq_sqrt (by norm_num)
  have hs0 : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  field_simp
  nlinarith

theorem norm_periodic_zero_mean_le (W : 𝓢(Joint, ℂ)) (c : O) (hc : c ≠ 0)
    (a : Residue c × Residue c → ℂ) (B : ℝ) (hB : ∀ r, ‖a r‖ ≤ B)
    (hmean : (∑' r, a r) = 0) :
    ‖∑' m : O × O, a (quotientPair c m) * W (embeddingPair m)‖ ≤
      (4/3:ℝ) * B *
        ∑' p : {p : (ℤ × ℤ) × (ℤ × ℤ) // p ≠ 0},
          ‖(𝓕 W) (jointFrequency (ringComplex c) (ringComplex_ne_zero hc) p.val)‖ := by
  let F (p : (ℤ × ℤ) × (ℤ × ℤ)) := residueFourier c hc a p *
    (𝓕 W) (jointFrequency (ringComplex c) (ringComplex_ne_zero hc) p)
  let q : ℝ := Ideal.absNorm (Ideal.span {c})
  have hF0 : F 0 = 0 := by simp [F, hmean]
  have hnorm (p : (ℤ × ℤ) × (ℤ × ℤ)) : ‖F p‖ ≤ q^2 * B *
      ‖(𝓕 W) (jointFrequency (ringComplex c) (ringComplex_ne_zero hc) p)‖ := by
    dsimp only [F]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (residueFourier_norm_le c hc a B hB p) (norm_nonneg _)
  have hsF : Summable (fun p => ‖F p‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hnorm
      ((jointFrequency_summable_norm W (ringComplex c) (ringComplex_ne_zero hc)).mul_left _)
  have heq : (∑' p : {p : (ℤ × ℤ) × (ℤ × ℤ) // p ≠ 0}, F p.val) = ∑' p, F p := by
    apply tsum_subtype_eq_of_support_subset
    intro p hp
    change F p ≠ 0 at hp
    exact fun h => hp (h ▸ hF0)
  have hb : ‖∑' p, F p‖ ≤ q^2 * B *
      ∑' p : {p : (ℤ × ℤ) × (ℤ × ℤ) // p ≠ 0},
        ‖(𝓕 W) (jointFrequency (ringComplex c) (ringComplex_ne_zero hc) p.val)‖ := by
    rw [← heq]
    have hs1 : Summable (fun p : {p : (ℤ × ℤ) × (ℤ × ℤ) // p ≠ 0} => ‖F p.val‖) :=
      hsF.subtype (fun p => p ≠ 0)
    have hm : Summable (fun p : {p : (ℤ × ℤ) × (ℤ × ℤ) // p ≠ 0} =>
        ‖(𝓕 W) (jointFrequency (ringComplex c) (ringComplex_ne_zero hc) p.val)‖) :=
      (jointFrequency_summable_norm W (ringComplex c)
        (ringComplex_ne_zero hc)).subtype (fun p => p ≠ 0)
    have ht : (∑' p : {p : (ℤ × ℤ) × (ℤ × ℤ) // p ≠ 0}, ‖F p.val‖) ≤
        ∑' p : {p : (ℤ × ℤ) × (ℤ × ℤ) // p ≠ 0}, q^2 * B *
          ‖(𝓕 W) (jointFrequency (ringComplex c) (ringComplex_ne_zero hc) p.val)‖ :=
      Summable.tsum_le_tsum (fun p => hnorm p.val) hs1 (hm.mul_left (q^2*B))
    exact (norm_tsum_le_tsum_norm hs1).trans (by simpa only [tsum_mul_left] using ht)
  rw [actual_joint_periodic_fourier W c hc a, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg _)]
  calc
    _ ≤ (2/(Real.sqrt 3*‖ringComplex c‖^2))^2 * (q^2 * B *
      ∑' p : {p : (ℤ × ℤ) × (ℤ × ℤ) // p ≠ 0},
        ‖(𝓕 W) (jointFrequency (ringComplex c) (ringComplex_ne_zero hc) p.val)‖) :=
      mul_le_mul_of_nonneg_left hb (sq_nonneg _)
    _ = _ := by
      rw [← mul_assoc, ← mul_assoc, principal_joint_inverse_covolume c hc]

def scaleMap (t : ℝ) (ht : 0 < t) : Joint ≃L[ℝ] Joint :=
  blockMap (complexMulEquiv ((t⁻¹:ℝ):ℂ)
    (Complex.ofReal_ne_zero.mpr (inv_ne_zero ht.ne')))

@[simp] theorem scaleMap_apply (t : ℝ) (ht : 0 < t) (z : Joint) :
    scaleMap t ht z = t⁻¹ • z := by
  apply WithLp.ofLp_injective
  apply Prod.ext <;> simp [scaleMap, blockMap_apply, complexMulEquiv_apply, point, Algebra.smul_def]

theorem scaleMap_dual (t : ℝ) (ht : 0 < t) (z : Joint) :
    jointDual (scaleMap t ht) z = t • z := by
  have hz : z = point z.fst z.snd := rfl
  conv_lhs => rw [hz]
  rw [scaleMap, jointDual_blockMap, dual_mul_apply, dual_mul_apply]
  apply WithLp.ofLp_injective
  apply Prod.ext <;> simp [point, Algebra.smul_def]

theorem scaleMap_inverseJacobian (t : ℝ) (ht : 0 < t) :
    jointInverseJacobian (scaleMap t ht) = t^4 := by
  rw [scaleMap, jointInverseJacobian_blockMap, inverseJacobian, complexMulEquiv_det,
    abs_inv, abs_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos ht, ← inv_pow, inv_inv]
  ring

def scaledSource (W : 𝓢(Joint, ℂ)) (t : ℝ) (ht : 0 < t) : 𝓢(Joint, ℂ) :=
  jointAffine W (scaleMap t ht) 0

@[simp] theorem scaledSource_apply (W : 𝓢(Joint, ℂ)) (t : ℝ) (ht : 0 < t) (z : Joint) :
    scaledSource W t ht z = W (t⁻¹ • z) := by
  simp [scaledSource]

theorem fourier_scaledSource (W : 𝓢(Joint, ℂ)) (t : ℝ) (ht : 0 < t) (z : Joint) :
    (𝓕 (scaledSource W t ht)) z = t^4 • (𝓕 W) (t • z) := by
  rw [scaledSource, joint_fourier_affine, scaleMap_inverseJacobian, scaleMap_dual]
  simp

theorem scaledSource_physicalPoint (W : 𝓢(Joint, ℂ)) (N : ℝ) (hN : 0 < N) (m : O × O) :
    scaledSource W (Real.sqrt N) (Real.sqrt_pos.mpr hN) (embeddingPair m) =
      W (ProbeGramLatticeDecay.physicalPoint N m) := by
  rw [scaledSource_apply, ProbeGramLatticeDecay.physicalPoint_eq_smul]
  rfl

def generatorRotation (c : ℂ) : ℂ := (‖c‖:ℂ) / starRingEnd ℂ c

theorem norm_generatorRotation (c : ℂ) (hc : c ≠ 0) : ‖generatorRotation c‖ = 1 := by
  simp [generatorRotation, Complex.norm_real, norm_ne_zero_iff.mpr hc]

theorem scaled_jointFrequency_eq (c : ℂ) (hc : c ≠ 0) (N : ℝ) (hN : 0 < N)
    (p : (ℤ × ℤ) × (ℤ × ℤ)) :
    Real.sqrt N • jointFrequency c hc p =
      ProbeGramLatticeDecay.scaledDualPoint (Real.sqrt (N/‖c‖^2)) (generatorRotation c) p := by
  have hn : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
  have hs : Real.sqrt (N/‖c‖^2) = Real.sqrt N / ‖c‖ := by
    rw [Real.sqrt_div hN.le, Real.sqrt_sq (norm_nonneg c)]
  have hcoord (v : ℤ × ℤ) : (Real.sqrt N:ℂ) * eisensteinDualFrequency c hc v =
      generatorRotation c * (Real.sqrt (N/‖c‖^2):ℂ) * explicitDualFrequency 1 v := by
    rw [eisensteinDualFrequency_eq_paperFrequency, hs]
    simp only [generatorRotation, explicitDualFrequency, paperFrequency, map_div₀, div_one, Complex.ofReal_div]
    have hnC : (‖c‖:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn
    field_simp
  apply WithLp.ofLp_injective
  change (Real.sqrt N • eisensteinDualFrequency c hc p.1,
    Real.sqrt N • eisensteinDualFrequency c hc p.2) = _
  apply Prod.ext
  · simpa [Algebra.smul_def, ProbeGramLatticeDecay.scaledDualPoint, ProbeGramLatticeDecay.point] using hcoord p.1
  · simpa [Algebra.smul_def, ProbeGramLatticeDecay.scaledDualPoint, ProbeGramLatticeDecay.point] using hcoord p.2

theorem sqrt_ratio_decay (N q : ℝ) (hN : 0 < N) (hq : 0 < q) (A : ℕ) :
    (Real.sqrt (N/q))^(-((2*A:ℕ):ℝ)) = (q/N)^A := by
  rw [Real.rpow_neg (Real.sqrt_nonneg _), Real.rpow_natCast, pow_mul,
    Real.sq_sqrt (div_nonneg hN.le hq.le), ← inv_pow, inv_div]

theorem physical_weighted_summable (W : 𝓢(Joint, ℂ)) (N : ℝ) (hN : 0 < N)
    (d : O × O → ℂ) (B : ℝ) (hB : ∀ m, ‖d m‖ ≤ B) :
    Summable (fun m : O × O => d m * W (ProbeGramLatticeDecay.physicalPoint N m)) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    ((ProbeGramLatticeDecay.physical_summable W N hN).mul_left B)
  intro m
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hB m) (norm_nonneg _)

theorem principal_high_bound (A : ℕ) (hA : 2 < A) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(Joint, ℂ)) (c : O) (_hc : c ≠ 0)
        (a : Residue c × Residue c → ℂ) (B : ℝ), 0 ≤ B →
        (∀ r, ‖a r‖ ≤ B) → (∑' r, a r) = 0 →
        ∀ (N : ℝ), 0 < N → (Ideal.absNorm (Ideal.span {c}) : ℝ) ≤ N →
        ‖∑' m : O × O, a (quotientPair c m) * W (ProbeGramLatticeDecay.physicalPoint N m)‖ ≤
          C * ProbeGramLatticeDecay.sourceControl S W * B * N^2 *
            ((Ideal.absNorm (Ideal.span {c}) : ℝ)/N)^A := by
  obtain ⟨S,C,hC,hhigh⟩ := ProbeGramLatticeDecay.dual_fourier_lattice_bound A hA
  refine ⟨S,(4/3)*C,mul_pos (by norm_num) hC,?_⟩
  intro W c hc a B hB0 hB hmean N hN hscale
  let q : ℝ := Ideal.absNorm (Ideal.span {c})
  have hq : 0 < q := by
    dsimp only [q]
    rw [← ringComplex_norm_sq_eq_absNorm_span]
    exact sq_pos_of_pos (norm_pos_iff.mpr (ringComplex_ne_zero hc))
  have hL : 1 ≤ Real.sqrt (N/q) := by
    apply Real.le_sqrt_of_sq_le
    norm_num only [one_pow]
    exact (le_div_iff₀ hq).mpr (by simpa only [one_mul] using hscale)
  let u : ℂ := generatorRotation (ringComplex c)
  have hu : ‖u‖ = 1 := norm_generatorRotation _ (ringComplex_ne_zero hc)
  have ht4 : (Real.sqrt N)^4 = N^2 := by
    rw [show (4:ℕ) = 2*2 by norm_num, pow_mul, Real.sq_sqrt hN.le]
  have hf (p : (ℤ × ℤ) × (ℤ × ℤ)) :
      ‖(𝓕 (scaledSource W (Real.sqrt N) (Real.sqrt_pos.mpr hN)))
        (jointFrequency (ringComplex c) (ringComplex_ne_zero hc) p)‖ =
      N^2 * ‖(𝓕 W) (ProbeGramLatticeDecay.scaledDualPoint (Real.sqrt (N/q)) u p)‖ := by
    rw [fourier_scaledSource, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (Real.sqrt_nonneg _) _), ht4,
      scaled_jointFrequency_eq _ _ N hN]
    rw [ringComplex_norm_sq_eq_absNorm_span]
  have h := norm_periodic_zero_mean_le
    (scaledSource W (Real.sqrt N) (Real.sqrt_pos.mpr hN)) c hc a B hB hmean
  simp_rw [scaledSource_physicalPoint W N hN, hf, tsum_mul_left] at h
  have hD := hhigh W (Real.sqrt (N/q)) hL u hu
  rw [sqrt_ratio_decay N q hN hq A] at hD
  calc
    _ ≤ (4/3:ℝ)*B*(N^2 *
        ∑' p : {p : (ℤ × ℤ) × (ℤ × ℤ) // p ≠ 0},
          ‖(𝓕 W) (ProbeGramLatticeDecay.scaledDualPoint (Real.sqrt (N/q)) u p.val)‖) := h
    _ ≤ (4/3:ℝ)*B*(N^2 *
        (C * ProbeGramLatticeDecay.sourceControl S W * (q/N)^A)) := by
      gcongr
    _ = _ := by ring

theorem norm_physical_weighted_le (W : 𝓢(Joint, ℂ)) (N : ℝ) (hN : 0 < N)
    (d : O × O → ℂ) (B : ℝ) (hB : ∀ m, ‖d m‖ ≤ B) :
    ‖∑' m : O × O, d m * W (ProbeGramLatticeDecay.physicalPoint N m)‖ ≤
      B * ∑' m : O × O, ‖W (ProbeGramLatticeDecay.physicalPoint N m)‖ := by
  have hbound (m : O × O) : ‖d m * W (ProbeGramLatticeDecay.physicalPoint N m)‖ ≤
      B * ‖W (ProbeGramLatticeDecay.physicalPoint N m)‖ := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hB m) (norm_nonneg _)
  have hs := ProbeGramLatticeDecay.physical_summable W N hN
  have hsD := Summable.of_nonneg_of_le (fun m => norm_nonneg _) hbound (hs.mul_left B)
  apply (norm_tsum_le_tsum_norm hsD).trans
  have h := Summable.tsum_le_tsum hbound hsD (hs.mul_left B)
  simpa only [tsum_mul_left] using h

theorem principal_periodic_bound (A : ℕ) (hA : 2 < A) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(Joint, ℂ)) (c : O), c ≠ 0 →
        ∀ (a : Residue c × Residue c → ℂ) (B : ℝ), 0 ≤ B →
        (∀ r, ‖a r‖ ≤ B) → (∑' r, a r) = 0 → ∀ (N : ℝ), 1 ≤ N →
        Summable (fun m : O × O =>
          a (quotientPair c m) * W (ProbeGramLatticeDecay.physicalPoint N m)) ∧
        ‖∑' m : O × O, a (quotientPair c m) * W (ProbeGramLatticeDecay.physicalPoint N m)‖ ≤
          C * ProbeGramLatticeDecay.sourceControl S W * B * N^2 *
            min 1 (((Ideal.absNorm (Ideal.span {c}) : ℝ)/N)^A) := by
  obtain ⟨Sl,Cl,hCl,hl⟩ := ProbeGramLatticeDecay.physical_lattice_bound
  obtain ⟨Sh,Ch,hCh,hh⟩ := principal_high_bound A hA
  refine ⟨Sl∪Sh,Cl+Ch,add_pos hCl hCh,?_⟩
  intro W c hc a B hB0 hB hm N hN
  have hNp : 0 < N := lt_of_lt_of_le zero_lt_one hN
  refine ⟨physical_weighted_summable W N hNp _ B (fun m => hB _),?_⟩
  have hSl : Cl*ProbeGramLatticeDecay.sourceControl Sl W ≤
      (Cl+Ch)*ProbeGramLatticeDecay.sourceControl (Sl∪Sh) W :=
    mul_le_mul (le_add_of_nonneg_right hCh.le)
      (ProbeGramLatticeDecay.sourceControl_mono Finset.subset_union_left W)
      (ProbeGramLatticeDecay.sourceControl_nonneg _ _) (by positivity)
  have hSh : Ch*ProbeGramLatticeDecay.sourceControl Sh W ≤
      (Cl+Ch)*ProbeGramLatticeDecay.sourceControl (Sl∪Sh) W :=
    mul_le_mul (le_add_of_nonneg_left hCl.le)
      (ProbeGramLatticeDecay.sourceControl_mono Finset.subset_union_right W)
      (ProbeGramLatticeDecay.sourceControl_nonneg _ _) (by positivity)
  have hratio : 0 ≤ (Ideal.absNorm (Ideal.span {c}) : ℝ)/N := div_nonneg (by positivity) hNp.le
  by_cases hscale : (Ideal.absNorm (Ideal.span {c}) : ℝ) ≤ N
  · have hp : ((Ideal.absNorm (Ideal.span {c}) : ℝ)/N)^A ≤ 1 :=
      pow_le_one₀ hratio ((div_le_one hNp).mpr hscale)
    rw [min_eq_right hp]
    exact (hh W c hc a B hB0 hB hm N hNp hscale).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hSh hB0) (sq_nonneg _))
        (pow_nonneg hratio _))
  · have hp : 1 ≤ ((Ideal.absNorm (Ideal.span {c}) : ℝ)/N)^A :=
      one_le_pow₀ ((le_div_iff₀ hNp).mpr (by linarith))
    rw [min_eq_left hp, mul_one]
    calc
      _ ≤ B * ∑' m : O × O, ‖W (ProbeGramLatticeDecay.physicalPoint N m)‖ :=
        norm_physical_weighted_le W N hNp _ B (fun m => hB _)
      _ ≤ B * (Cl*ProbeGramLatticeDecay.sourceControl Sl W*N^2) :=
        mul_le_mul_of_nonneg_left (hl W N hN) hB0
      _ = Cl*ProbeGramLatticeDecay.sourceControl Sl W*B*N^2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hSl hB0) (sq_nonneg _)

def idealQuotientPair (r : Ideal O) (m : O × O) : (O ⧸ r) × (O ⧸ r) :=
  (Ideal.Quotient.mk r m.1, Ideal.Quotient.mk r m.2)

theorem ideal_periodic_bound (A : ℕ) (hA : 2 < A) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(Joint, ℂ)) (r : Ideal O), r ≠ 0 →
        ∀ (a : (O ⧸ r) × (O ⧸ r) → ℂ) (B : ℝ), 0 ≤ B →
        (∀ v, ‖a v‖ ≤ B) → (∑' v, a v) = 0 → ∀ (N : ℝ), 1 ≤ N →
        Summable (fun m : O × O =>
          a (idealQuotientPair r m) * W (ProbeGramLatticeDecay.physicalPoint N m)) ∧
        ‖∑' m : O × O, a (idealQuotientPair r m) * W (ProbeGramLatticeDecay.physicalPoint N m)‖ ≤
          C * ProbeGramLatticeDecay.sourceControl S W * B * N^2 *
            min 1 (((Ideal.absNorm r : ℝ)/N)^A) := by
  obtain ⟨S,C,hC,h⟩ := principal_periodic_bound A hA
  refine ⟨S,C,hC,?_⟩
  intro W r hr
  obtain ⟨c,hc,heq⟩ : ∃ c : O, c ≠ 0 ∧ Ideal.span {c} = r :=
    ⟨cubicIdealGenerator r,
      cubicIdealGenerator_ne_zero r hr,
      span_cubicIdealGenerator r⟩
  subst r
  exact h W c hc

theorem principal_annular_periodic_bound (A : ℕ) (hA : 2 < A)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(Joint, ℂ)), ProbeGramAnnularLattice.AnnularSupport a b W →
      ∀ (c : O), c ≠ 0 → ∀ (d : Residue c × Residue c → ℂ) (B : ℝ), 0 ≤ B →
        (∀ r, ‖d r‖ ≤ B) → (∑' r, d r) = 0 → ∀ (N : ℝ), 0 < N →
        Summable (fun m : O × O =>
          d (quotientPair c m) * W (ProbeGramLatticeDecay.physicalPoint N m)) ∧
        ‖∑' m : O × O, d (quotientPair c m) * W (ProbeGramLatticeDecay.physicalPoint N m)‖ ≤
          C * ProbeGramLatticeDecay.sourceControl S W * B * N^2 *
            min 1 (((Ideal.absNorm (Ideal.span {c}) : ℝ)/N)^A) := by
  obtain ⟨Sl,Cl,hCl,hl⟩ := ProbeGramAnnularLattice.annular_weighted_lattice_bound a b ha hab
  obtain ⟨Sh,Ch,hCh,hh⟩ := principal_high_bound A hA
  refine ⟨Sl∪Sh,Cl+Ch,add_pos hCl hCh,?_⟩
  intro W hW c hc d B hB0 hB hm N hN
  refine ⟨physical_weighted_summable W N hN _ B (fun m => hB _),?_⟩
  have hSl : Cl*ProbeGramLatticeDecay.sourceControl Sl W ≤
      (Cl+Ch)*ProbeGramLatticeDecay.sourceControl (Sl∪Sh) W :=
    mul_le_mul (le_add_of_nonneg_right hCh.le)
      (ProbeGramLatticeDecay.sourceControl_mono Finset.subset_union_left W)
      (ProbeGramLatticeDecay.sourceControl_nonneg _ _) (by positivity)
  have hSh : Ch*ProbeGramLatticeDecay.sourceControl Sh W ≤
      (Cl+Ch)*ProbeGramLatticeDecay.sourceControl (Sl∪Sh) W :=
    mul_le_mul (le_add_of_nonneg_left hCl.le)
      (ProbeGramLatticeDecay.sourceControl_mono Finset.subset_union_right W)
      (ProbeGramLatticeDecay.sourceControl_nonneg _ _) (by positivity)
  have hratio : 0 ≤ (Ideal.absNorm (Ideal.span {c}) : ℝ)/N := div_nonneg (by positivity) hN.le
  by_cases hscale : (Ideal.absNorm (Ideal.span {c}) : ℝ) ≤ N
  · have hp : ((Ideal.absNorm (Ideal.span {c}) : ℝ)/N)^A ≤ 1 :=
      pow_le_one₀ hratio ((div_le_one hN).mpr hscale)
    rw [min_eq_right hp]
    exact (hh W c hc d B hB0 hB hm N hN hscale).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hSh hB0) (sq_nonneg _))
        (pow_nonneg hratio _))
  · have hp : 1 ≤ ((Ideal.absNorm (Ideal.span {c}) : ℝ)/N)^A :=
      one_le_pow₀ ((le_div_iff₀ hN).mpr (by linarith))
    rw [min_eq_left hp, mul_one]
    exact (hl W hW (fun m => d (quotientPair c m)) B hB0
      (fun m => hB _) N hN).2.trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hSl hB0) (sq_nonneg _))

/-- Mean-zero residue weights gain arbitrary powers beyond the modulus scale. -/
theorem ideal_annular_periodic_bound (A : ℕ) (hA : 2 < A)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(Joint, ℂ)), ProbeGramAnnularLattice.AnnularSupport a b W →
      ∀ (r : Ideal O), r ≠ 0 → ∀ (d : (O ⧸ r) × (O ⧸ r) → ℂ) (B : ℝ), 0 ≤ B →
        (∀ v, ‖d v‖ ≤ B) → (∑' v, d v) = 0 → ∀ (N : ℝ), 0 < N →
        Summable (fun m : O × O =>
          d (idealQuotientPair r m) * W (ProbeGramLatticeDecay.physicalPoint N m)) ∧
        ‖∑' m : O × O, d (idealQuotientPair r m) * W (ProbeGramLatticeDecay.physicalPoint N m)‖ ≤
          C * ProbeGramLatticeDecay.sourceControl S W * B * N^2 *
            min 1 (((Ideal.absNorm r : ℝ)/N)^A) := by
  obtain ⟨S,C,hC,h⟩ := principal_annular_periodic_bound A hA a b ha hab
  refine ⟨S,C,hC,?_⟩
  intro W hW r hr
  obtain ⟨c,hc,heq⟩ : ∃ c : O, c ≠ 0 ∧ Ideal.span {c} = r :=
    ⟨cubicIdealGenerator r,
      cubicIdealGenerator_ne_zero r hr,
      span_cubicIdealGenerator r⟩
  subst r
  exact h W hW c hc

end ProbeGramPeriodicPoisson

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open Filter Set
open scoped Classical SchwartzMap ContDiff Topology

namespace ProbeGramJointConstruction
open ProbeGramLatticeDecay SchwartzPlanePoisson

def q1 (z : Joint) : ℝ := ‖z.fst‖^2
def q2 (z : Joint) : ℝ := ‖z.snd‖^2

lemma q1_smooth : ContDiff ℝ ∞ q1 :=
  (WithLp.fstL 2 ℝ ℂ ℂ).contDiff.norm_sq ℂ
lemma q2_smooth : ContDiff ℝ ∞ q2 :=
  (WithLp.sndL 2 ℝ ℂ ℂ).contDiff.norm_sq ℂ

lemma norm_sq_eq (z : Joint) : ‖z‖^2 = q1 z + q2 z :=
  WithLp.prod_norm_sq_eq_of_L2 z

def log1 (a b : ℝ) (ha : 0< a) (z : Joint) : ℝ :=
  CompletedHeight.patchedLog a b ha (q1 z)
def log2 (a b : ℝ) (ha : 0< a) (z : Joint) : ℝ :=
  CompletedHeight.patchedLog a b ha (q2 z)
def phase (a b : ℝ) (ha : 0< a) (z : Joint) : ℝ :=
  log1 a b ha z - log2 a b ha z
def rootScale (a b : ℝ) (ha : 0< a) (z : Joint) : ℝ :=
  Real.exp (-(log1 a b ha z + log2 a b ha z)/2)
def amplitude (W : ℝ→ℂ) (a b : ℝ) (ha : 0< a) (z : Joint) : ℂ :=
  W (q1 z)*star (W (q2 z))*Complex.exp (-((log1 a b ha z+log2 a b ha z):ℂ))

lemma patchedLog_smooth (a b : ℝ) (ha : 0< a) :
    ContDiff ℝ ∞ (CompletedHeight.patchedLog a b ha) :=
  contDiff_id.add (CompletedHeight.logCorrection_smooth a b ha)
lemma log1_smooth (a b : ℝ) (ha : 0< a) : ContDiff ℝ ∞ (log1 a b ha) :=
  (patchedLog_smooth a b ha).comp q1_smooth
lemma log2_smooth (a b : ℝ) (ha : 0< a) : ContDiff ℝ ∞ (log2 a b ha) :=
  (patchedLog_smooth a b ha).comp q2_smooth
lemma phase_smooth (a b : ℝ) (ha : 0< a) : ContDiff ℝ ∞ (phase a b ha) :=
  (log1_smooth a b ha).sub (log2_smooth a b ha)
lemma rootScale_smooth (a b : ℝ) (ha : 0< a) : ContDiff ℝ ∞ (rootScale a b ha) :=
  (((log1_smooth a b ha).add (log2_smooth a b ha)).neg.div_const 2).exp
lemma rootScale_pos (a b : ℝ) (ha : 0< a) (z : Joint) : 0< rootScale a b ha z :=
  Real.exp_pos _
lemma amplitude_smooth (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) (a b : ℝ) (ha : 0< a) :
    ContDiff ℝ ∞ (amplitude W a b ha) := by
  unfold amplitude
  have h1 := hW.comp q1_smooth
  have h2 := hW.comp q2_smooth
  have hl := (log1_smooth a b ha).add (log2_smooth a b ha)
  simpa only [Function.comp_apply, Complex.ofRealCLM_apply, Complex.ofReal_add, Complex.conjCLE_apply, Complex.star_def] using
    (h1.mul (Complex.conjCLE.contDiff.comp h2)).mul
      ((Complex.ofRealCLM.contDiff.comp hl).neg.cexp)

def rawProfile (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ)) (v T : ℝ) (z : Joint) : ℂ :=
  (W (q1 z)*(q1 z:ℂ)^(-1+(v:ℂ)*Complex.I))*
    star (W (q2 z)*(q2 z:ℂ)^(-1+(v:ℂ)*Complex.I))*
    paperRadialFourier U (T/(q1 z*q2 z))

def patchedProfile (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0< a)
    (v T : ℝ) (z : Joint) : ℂ :=
  amplitude W a b ha z * kernelLogPhase (v/(2*Real.pi)) (phase a b ha z) *
    paperFourierRayCLM U (Real.sqrt T*rootScale a b ha z)

lemma patchedProfile_smooth (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) (U : 𝓢(ℝ,ℂ))
    (a b : ℝ) (ha : 0< a) (v T : ℝ) :
    ContDiff ℝ ∞ (patchedProfile W U a b ha v T) := by
  have h1 := amplitude_smooth W hW a b ha
  have h2 := phase_smooth a b ha
  have h3 := rootScale_smooth a b ha
  have h4 := (paperFourierRayCLM U).smooth (⊤ : ℕ∞)
  have hp : ContDiff ℝ ∞ (fun z => kernelLogPhase (v/(2*Real.pi)) (phase a b ha z)) := by
    unfold kernelLogPhase
    exact ((Complex.ofRealCLM.contDiff.comp (contDiff_const.mul h2)).mul contDiff_const).cexp
  exact (h1.mul hp).mul (h4.comp (contDiff_const.mul h3))

lemma rawProfile_zero_left (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ)) (v T : ℝ) (z : Joint)
    (hz : W (q1 z)=0) : rawProfile W U v T z=0 := by simp [rawProfile,hz]
lemma rawProfile_zero_right (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ)) (v T : ℝ) (z : Joint)
    (hz : W (q2 z)=0) : rawProfile W U v T z=0 := by simp [rawProfile,hz]
lemma patchedProfile_zero_left (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0< a)
    (v T : ℝ) (z : Joint) (hz : W (q1 z)=0) : patchedProfile W U a b ha v T z=0 := by
  simp [patchedProfile,amplitude,hz]
lemma patchedProfile_zero_right (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0< a)
    (v T : ℝ) (z : Joint) (hz : W (q2 z)=0) : patchedProfile W U a b ha v T z=0 := by
  simp [patchedProfile,amplitude,hz]

def sourceCompact (b : ℝ) : Set Joint := Metric.closedBall 0 (1+2*b)
lemma sourceCompact_isCompact (b : ℝ) : IsCompact (sourceCompact b) :=
  isCompact_closedBall _ _

lemma support_amplitude (W : ℝ→ℂ) (a b : ℝ) (ha : 0< a)
    (hs : Function.support W⊆Icc a b) :
    Function.support (amplitude W a b ha)⊆{z | a≤ q1 z ∧ q1 z≤ b ∧ a≤ q2 z ∧ q2 z≤ b} := by
  intro z hz
  have h1 : W (q1 z)≠0 := fun h => hz (by simp [amplitude,h])
  have h2 : W (q2 z)≠0 := fun h => hz (by simp [amplitude,h])
  exact ⟨(hs h1).1,(hs h1).2,(hs h2).1,(hs h2).2⟩

lemma annulus_subset_sourceCompact (a b : ℝ) (ha : 0< a) (hab : a< b) :
    {z : Joint | a≤ q1 z ∧ q1 z≤ b ∧ a≤ q2 z ∧ q2 z≤ b}⊆sourceCompact b := by
  intro z hz
  change dist z 0≤1+2*b
  rw [dist_zero_right]
  have hn := norm_sq_eq z
  have hb : 0< b := ha.trans hab
  nlinarith [norm_nonneg z, sq_nonneg (‖z‖-1),hz.2.1,hz.2.2.2]

lemma tsupport_amplitude_subset (W : ℝ→ℂ) (a b : ℝ) (ha : 0< a) (hab : a< b)
    (hs : Function.support W⊆Icc a b) :
    tsupport (amplitude W a b ha)⊆sourceCompact b := by
  exact closure_minimal ((support_amplitude W a b ha hs).trans
    (annulus_subset_sourceCompact a b ha hab)) Metric.isClosed_closedBall

lemma amplitude_hasCompactSupport (W : ℝ→ℂ) (a b : ℝ) (ha : 0< a) (hab : a< b)
    (hs : Function.support W⊆Icc a b) : HasCompactSupport (amplitude W a b ha) :=
  HasCompactSupport.of_support_subset_isCompact (sourceCompact_isCompact b)
    ((support_amplitude W a b ha hs).trans (annulus_subset_sourceCompact a b ha hab))

lemma patchedProfile_hasCompactSupport (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ))
    (a b : ℝ) (ha : 0< a) (hab : a< b) (hs : Function.support W⊆Icc a b) (v T : ℝ) :
    HasCompactSupport (patchedProfile W U a b ha v T) :=
  ((amplitude_hasCompactSupport W a b ha hab hs).mul_right).mul_right

lemma norm_power_pair (v x y : ℝ) (hx : 0< x) (hy : 0< y) :
    (x:ℂ)^(-1+(v:ℂ)*Complex.I)*star ((y:ℂ)^(-1+(v:ℂ)*Complex.I)) =
      Complex.exp (-((Real.log x+Real.log y):ℂ))*
        kernelLogPhase (v/(2*Real.pi)) (Real.log x-Real.log y) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne')]
  rw [←Complex.ofReal_log hx.le,←Complex.ofReal_log hy.le]
  simp only [Complex.star_def,←Complex.exp_conj,map_mul,map_add,map_neg,map_one,
    Complex.conj_ofReal,Complex.conj_I]
  unfold kernelLogPhase
  rw [←Complex.exp_add,←Complex.exp_add]
  congr 1
  push_cast
  have hpi : (Real.pi:ℂ)≠0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  ring

lemma sqrt_reciprocal_product (T x y : ℝ) (hT : 0≤ T) (hx : 0< x) (hy : 0< y) :
    Real.sqrt (T/(x*y))=Real.sqrt T*Real.exp (-(Real.log x+Real.log y)/2) := by
  have he : Real.exp (-(Real.log x+Real.log y)/2)^2=(x*y)⁻¹ := by
    rw [←Real.exp_nat_mul]
    norm_num only [Nat.cast_ofNat]
    rw [show (2:ℝ)*(-(Real.log x+Real.log y)/2)=-(Real.log x+Real.log y) by ring,
      Real.exp_neg,Real.exp_add,Real.exp_log hx,Real.exp_log hy]
  have hl := Real.sq_sqrt (div_nonneg hT (mul_pos hx hy).le)
  have hr : (Real.sqrt T*Real.exp (-(Real.log x+Real.log y)/2))^2=T/(x*y) := by
    rw [mul_pow,Real.sq_sqrt hT,he,div_eq_mul_inv]
  nlinarith [Real.sqrt_nonneg (T/(x*y)),Real.sqrt_nonneg T,
    Real.exp_pos (-(Real.log x+Real.log y)/2),mul_nonneg (Real.sqrt_nonneg T)
      (Real.exp_pos (-(Real.log x+Real.log y)/2)).le]

theorem rawProfile_eq_patchedProfile (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ))
    (a b : ℝ) (ha : 0< a) (hs : Function.support W⊆Icc a b)
    (v T : ℝ) (hT : 0≤ T) (z : Joint) :
    rawProfile W U v T z=patchedProfile W U a b ha v T z := by
  by_cases h1 : W (q1 z)=0
  · rw [rawProfile_zero_left W U v T z h1,patchedProfile_zero_left W U a b ha v T z h1]
  by_cases h2 : W (q2 z)=0
  · rw [rawProfile_zero_right W U v T z h2,patchedProfile_zero_right W U a b ha v T z h2]
  have hx := ha.trans_le (hs h1).1
  have hy := ha.trans_le (hs h2).1
  have hl1 : log1 a b ha z=Real.log (q1 z) := CompletedHeight.patchedLog_eq_log a b ha _ (hs h1)
  have hl2 : log2 a b ha z=Real.log (q2 z) := CompletedHeight.patchedLog_eq_log a b ha _ (hs h2)
  have hker : paperRadialFourier U (T/(q1 z*q2 z)) =
      paperFourierRayCLM U (Real.sqrt T*rootScale a b ha z) := by
    rw [paperRadialFourier_eq_ray]
    change paperFourierRayCLM U (Real.sqrt (T/(q1 z*q2 z))) = _
    rw [sqrt_reciprocal_product T _ _ hT hx hy]
    simp only [rootScale,hl1,hl2]
  unfold rawProfile patchedProfile amplitude phase
  rw [hker,hl1,hl2]
  simp only [star_mul]
  calc
    _ = (W (q1 z)*star (W (q2 z)))*
        ((q1 z:ℂ)^(-1+(v:ℂ)*Complex.I)*star ((q2 z:ℂ)^(-1+(v:ℂ)*Complex.I)))*
        paperFourierRayCLM U (Real.sqrt T*rootScale a b ha z) := by ring
    _ = _ := by rw [norm_power_pair v _ _ hx hy];ring

def amplitudeSchwartz (W : ℝ→ℂ) (a b : ℝ) (ha : 0< a) (hab : a< b)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W) : 𝓢(Joint,ℂ) :=
  (amplitude_hasCompactSupport W a b ha hab hs).toSchwartzMap (amplitude_smooth W hW a b ha)

@[simp] lemma amplitudeSchwartz_apply (W : ℝ→ℂ) (a b : ℝ) (ha : 0< a) (hab : a< b)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W) (z : Joint) :
    amplitudeSchwartz W a b ha hab hs hW z=amplitude W a b ha z := rfl

lemma rawProfile_smooth (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ))
    (a b : ℝ) (ha : 0< a) (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (v T : ℝ) (hT : 0≤ T) : ContDiff ℝ ∞ (rawProfile W U v T) := by
  have he : rawProfile W U v T=patchedProfile W U a b ha v T :=
    funext (rawProfile_eq_patchedProfile W U a b ha hs v T hT)
  rw [he]
  exact patchedProfile_smooth W hW U a b ha v T

lemma support_rawProfile (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ))
    (a b : ℝ) (hs : Function.support W⊆Icc a b) (v T : ℝ) :
    Function.support (rawProfile W U v T)⊆{z | a≤ q1 z ∧ q1 z≤ b ∧ a≤ q2 z ∧ q2 z≤ b} := by
  intro z hz
  have h1 : W (q1 z)≠0 := fun h => hz (rawProfile_zero_left W U v T z h)
  have h2 : W (q2 z)≠0 := fun h => hz (rawProfile_zero_right W U v T z h)
  exact ⟨(hs h1).1,(hs h1).2,(hs h2).1,(hs h2).2⟩

lemma rawProfile_hasCompactSupport (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ))
    (a b : ℝ) (ha : 0< a) (hab : a< b) (hs : Function.support W⊆Icc a b) (v T : ℝ) :
    HasCompactSupport (rawProfile W U v T) :=
  HasCompactSupport.of_support_subset_isCompact (sourceCompact_isCompact b)
    ((support_rawProfile W U a b hs v T).trans (annulus_subset_sourceCompact a b ha hab))

/-- The annular two-variable profile combines Mellin weights with the radial Fourier kernel. -/
def jointProfile (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0< a) (hab : a< b)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (v T : ℝ) (hT : 0≤ T) : 𝓢(Joint,ℂ) :=
  (rawProfile_hasCompactSupport W U a b ha hab hs v T).toSchwartzMap
    (rawProfile_smooth W U a b ha hs hW v T hT)

@[simp] theorem jointProfile_apply (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0< a) (hab : a< b)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (v T : ℝ) (hT : 0≤ T) (z : Joint) :
    jointProfile W U a b ha hab hs hW v T hT z=rawProfile W U v T z := rfl

theorem jointProfile_factorization (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ))
    (a b : ℝ) (ha : 0< a) (hab : a< b)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (v T : ℝ) (hT : 0≤ T) (z : Joint) :
    jointProfile W U a b ha hab hs hW v T hT z=
      amplitude W a b ha z * kernelLogPhase (v/(2*Real.pi)) (phase a b ha z) *
        paperFourierRayCLM U (Real.sqrt T*rootScale a b ha z) :=
  rawProfile_eq_patchedProfile W U a b ha hs v T hT z

theorem jointProfile_annularSupport (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ))
    (a b : ℝ) (ha : 0< a) (hab : a< b)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (v T : ℝ) (hT : 0≤ T) :
    ProbeGramAnnularLattice.AnnularSupport a b (jointProfile W U a b ha hab hs hW v T hT) :=
  support_rawProfile W U a b hs v T

lemma jointProfile_zero_scale (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ))
    (a b : ℝ) (ha : 0< a) (hab : a< b)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W) (v : ℝ) (z : Joint) :
    jointProfile W U a b ha hab hs hW v 0 (by positivity) z=
      (W (q1 z)*(q1 z:ℂ)^(-1+(v:ℂ)*Complex.I))*
        star (W (q2 z)*(q2 z:ℂ)^(-1+(v:ℂ)*Complex.I))*paperRadialFourier U 0 := by
  simp only [jointProfile_apply,rawProfile,zero_div]

lemma jointProfile_zero_of_left_small (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ))
    (a b : ℝ) (ha : 0< a) (hab : a< b)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (v T : ℝ) (hT : 0≤ T) (z : Joint) (hz : q1 z< a) :
    jointProfile W U a b ha hab hs hW v T hT z=0 := by
  apply rawProfile_zero_left
  by_contra h
  exact (not_le.mpr hz) (hs h).1

lemma jointProfile_zero_of_right_small (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ))
    (a b : ℝ) (ha : 0< a) (hab : a< b)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (v T : ℝ) (hT : 0≤ T) (z : Joint) (hz : q2 z< a) :
    jointProfile W U a b ha hab hs hW v T hT z=0 := by
  apply rawProfile_zero_right
  by_contra h
  exact (not_le.mpr hz) (hs h).1

end ProbeGramJointConstruction

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set JointLogSeparation
namespace ProbeGramJointProfile
open ProbeGramLatticeDecay SchwartzPlanePoisson

def rayControl (B n : ℕ) (g : 𝓢(ℝ, ℂ)) : ℝ :=
  (Finset.Iic (2*B+n,n)).sup (schwartzSeminormFamily ℝ ℝ ℂ) g

lemma rayControl_nonneg (B n : ℕ) (g : 𝓢(ℝ, ℂ)) :
    0 ≤ rayControl B n g := apply_nonneg _ _

lemma mul_derivative_bound {f g : Joint → ℂ} (n : ℕ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : Joint)
    {C D : ℝ} (hC : 0 ≤ C) (_hD : 0 ≤ D)
    (hfb : ∀ i ≤ n, ‖iteratedFDeriv ℝ i f x‖ ≤ C)
    (hgb : ∀ i ≤ n, ‖iteratedFDeriv ℝ i g x‖ ≤ D) :
    ‖iteratedFDeriv ℝ n (fun y => f y * g y) x‖ ≤ 2^n*C*D := by
  calc
    _ ≤ ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (n-i) g x‖ :=
      norm_iteratedFDeriv_mul_le hf hg x (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
    _ ≤ ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) * C * D := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul (mul_le_mul_of_nonneg_left
        (hfb i (Finset.mem_range_succ_iff.mp hi)) (by positivity))
        (hgb (n-i) (Nat.sub_le _ _)) (norm_nonneg _) (by positivity)
    _ = _ := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
      norm_cast

lemma compact_derivatives {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Set Joint} (hK : IsCompact K) {f : Joint → F}
    (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ i ≤ n, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ i f x‖ ≤ D := by
  have hb (i : ℕ) : ∃ D : ℝ, ∀ x ∈ K, ‖iteratedFDeriv ℝ i f x‖ ≤ D := by
    have hc : Continuous (fun x => ‖iteratedFDeriv ℝ i f x‖) :=
      (hf.continuous_iteratedFDeriv (by exact_mod_cast (le_top : (i : ℕ∞) ≤ ⊤))).norm
    obtain ⟨D, hD⟩ := hK.bddAbove_image hc.continuousOn
    exact ⟨D, fun x hx => hD (Set.mem_image_of_mem _ hx)⟩
  choose D hD using hb
  refine ⟨1 + ∑ i ∈ Finset.range (n+1), |D i|, by
    have hn : 0 ≤ ∑ i ∈ Finset.range (n+1), |D i| := by positivity
    linarith, ?_⟩
  intro i hi x hx
  have hs : |D i| ≤ ∑ j ∈ Finset.range (n+1), |D j| :=
    Finset.single_le_sum (fun j _ => abs_nonneg (D j)) (Finset.mem_range.mpr (by omega))
  exact (hD i x hx).trans ((le_abs_self _).trans (by linarith))

lemma compact_positive_margin {K : Set Joint} (hK : IsCompact K)
    {h : Joint → ℝ} (hc : Continuous h) (hp : ∀ x ∈ K, 0 < h x) :
    ∃ m : ℝ, 0 < m ∧ m ≤ 1 ∧ ∀ x ∈ K, m ≤ h x := by
  by_cases hne : K.Nonempty
  · obtain ⟨x, hx, hm⟩ := hK.exists_isMinOn hne hc.continuousOn
    exact ⟨min 1 (h x), lt_min zero_lt_one (hp x hx), min_le_left _ _,
      fun y hy => (min_le_right _ _).trans (hm hy)⟩
  · exact ⟨1, zero_lt_one, le_rfl, fun x hx => False.elim (hne ⟨x,hx⟩)⟩

lemma scaled_argument_derivative {h : Joint → ℝ} (hh : ContDiff ℝ ∞ h)
    {D R : ℝ} (hD : 1 ≤ D) (hR : 0 ≤ R) (i : ℕ) (hi : 1 ≤ i)
    (x : Joint) (hb : ‖iteratedFDeriv ℝ i h x‖ ≤ D) :
    ‖iteratedFDeriv ℝ i (fun y => R*h y) x‖ ≤ (D^2*(1+R))^i := by
  have he : iteratedFDeriv ℝ i (fun y => R*h y) x = R • iteratedFDeriv ℝ i h x :=
    by simpa only [smul_eq_mul] using
      (iteratedFDeriv_const_smul_apply' (a := R) (i := i) (x := x)
        ((hh.of_le (by exact_mod_cast le_top)).contDiffAt))
  rw [he, norm_smul, Real.norm_of_nonneg hR]
  have hDi : D ≤ D^i := by
    calc D = D^1 := by simp
         _ ≤ D^i := pow_le_pow_right₀ hD hi
  have hRi : R ≤ (1+R)^i := by
    calc R ≤ 1+R := by linarith
         _ = (1+R)^1 := by simp
         _ ≤ (1+R)^i := pow_le_pow_right₀ (by linarith) hi
  calc
    R * ‖iteratedFDeriv ℝ i h x‖ ≤ R*D := mul_le_mul_of_nonneg_left hb hR
    _ ≤ (1+R)^i * D^i := mul_le_mul hRi hDi (by linarith) (by positivity)
    _ ≤ (D^2*(1+R))^i := by
      rw [mul_pow, pow_two, mul_pow]
      have hhD : 1 ≤ D^i := one_le_pow₀ hD
      nlinarith [mul_nonneg (show 0 ≤ (1+R)^i by positivity)
        (show 0 ≤ (D^i)^2-D^i by nlinarith)]

lemma normalized_phase_derivative (v x : ℝ) (i : ℕ) :
    ‖iteratedFDeriv ℝ i (kernelLogPhase (v/(2*Real.pi))) x‖ = |v|^i := by
  rw [JointLogSeparation.kernelLogPhase_iteratedFDeriv_norm, norm_div,
    Real.norm_of_nonneg (by positivity : 0 ≤ 2*Real.pi), Real.norm_eq_abs]
  congr 1
  field_simp

lemma phase_derivative_bound {φ : Joint → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {D : ℝ} (hD : 1 ≤ D) (n j : ℕ) (hj : j ≤ n)
    (x : Joint) (hb : ∀ i ≤ n, ‖iteratedFDeriv ℝ i φ x‖ ≤ D) (v : ℝ) :
    ‖iteratedFDeriv ℝ j (fun y => kernelLogPhase (v/(2*Real.pi)) (φ y)) x‖ ≤
      (n.factorial : ℝ)*D^n*(1+|v|)^n := by
  have hcomp := norm_iteratedFDeriv_comp_le (JointLogSeparation.kernelLogPhase_temperate (v/(2*Real.pi))).1
    hφ (n := j) (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤)) x (C := (1+|v|)^n) (D := D)
  have hc : ∀ i ≤ j, ‖iteratedFDeriv ℝ i (kernelLogPhase (v/(2*Real.pi))) (φ x)‖ ≤
      (1+|v|)^n := by
    intro i hi
    rw [normalized_phase_derivative]
    exact (pow_le_pow_left₀ (abs_nonneg _) (by linarith : |v| ≤ 1+|v|) i).trans
      (pow_le_pow_right₀ (by linarith [abs_nonneg v]) (hi.trans hj))
  have hd : ∀ i, 1 ≤ i → i ≤ j → ‖iteratedFDeriv ℝ i φ x‖ ≤ D^i := by
    intro i hi hij
    exact (hb i (hij.trans hj)).trans (by
      calc D = D^1 := by simp
           _ ≤ D^i := pow_le_pow_right₀ hD hi)
  calc
    _ ≤ (j.factorial : ℝ)*(1+|v|)^n*D^j := hcomp hc hd
    _ ≤ (n.factorial : ℝ)*(1+|v|)^n*D^n := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le hj) (by positivity))
        (pow_le_pow_right₀ hD hj) (by positivity) (by positivity)
    _ = _ := by ring

lemma kernel_derivative_bound {h : Joint → ℝ} (hh : ContDiff ℝ ∞ h)
    {D m R : ℝ} (hD : 1 ≤ D) (hm : 0 < m) (hm1 : m ≤ 1) (hR : 0 ≤ R)
    (B n j : ℕ) (hj : j ≤ n) (x : Joint)
    (hb : ∀ i ≤ n, ‖iteratedFDeriv ℝ i h x‖ ≤ D) (hl : m ≤ h x)
    (g : 𝓢(ℝ, ℂ)) :
    ‖iteratedFDeriv ℝ j (fun y => g (R*h y)) x‖ ≤
      (((n.factorial : ℝ)*2^(2*B+n)*(D^2)^n/m^(2*B+n))*rayControl B n g) /
        (1+R)^(2*B) := by
  have hu : 0 ≤ R*h x := mul_nonneg hR (hm.le.trans hl)
  have hden : 0 < (1+R*h x)^(2*B+n) := by positivity
  have harg : ContDiff ℝ ∞ (fun y => R*h y) := contDiff_const.mul hh
  have hcomp : ‖iteratedFDeriv ℝ j (fun y => g (R*h y)) x‖ ≤
      (j.factorial : ℝ)*(2^(2*B+n)*rayControl B n g/(1+R*h x)^(2*B+n))*
        (D^2*(1+R))^j := by
    apply norm_iteratedFDeriv_comp_le (g.smooth ⊤) harg
      (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤)) x
    · intro i hi
      apply (le_div_iff₀ hden).mpr
      have hd := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
        (m := (2*B+n,n)) (k := 2*B+n) (n := i) le_rfl (hi.trans hj) g (R*h x)
      change (1+‖R*h x‖)^(2*B+n) * ‖iteratedFDeriv ℝ i g (R*h x)‖ ≤
        2^(2*B+n)*rayControl B n g at hd
      rw [Real.norm_of_nonneg hu] at hd
      simpa only [mul_comm] using hd
    · intro i hi hij
      exact scaled_argument_derivative hh hD hR i hi x (hb i (hij.trans hj))
  have hscale : m*(1+R) ≤ 1+R*h x := by
    nlinarith [mul_nonneg hR (sub_nonneg.mpr hl)]
  have habs := JointLogSeparation.derivative_scale_absorption R (R*h x) m D
    (2^(2*B+n)*rayControl B n g) (2*B) n j hR hm (by linarith)
    (mul_nonneg (by positivity) (rayControl_nonneg _ _ _)) hu hscale hj
  have hbound : m^(2*B+n)*(1+R)^(2*B)*
      ‖iteratedFDeriv ℝ j (fun y => g (R*h y)) x‖ ≤
      (n.factorial : ℝ)*(2^(2*B+n)*rayControl B n g)*(D^2)^n := by
    calc
      _ ≤ m^(2*B+n)*(1+R)^(2*B)*
          ((j.factorial : ℝ)*(2^(2*B+n)*rayControl B n g/(1+R*h x)^(2*B+n))*
            (D^2*(1+R))^j) := mul_le_mul_of_nonneg_left hcomp (by positivity)
      _ ≤ (j.factorial : ℝ)*(2^(2*B+n)*rayControl B n g)*(D^2)^j := habs
      _ ≤ _ := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le hj)
            (mul_nonneg (by positivity) (rayControl_nonneg _ _ _)))
          (pow_le_pow_right₀ (one_le_pow₀ hD) hj) (by positivity)
          (mul_nonneg (by positivity) (mul_nonneg (by positivity) (rayControl_nonneg _ _ _)))
  apply (le_div_iff₀ (by positivity : 0 < (1+R)^(2*B))).mpr
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (by positivity : 0 < m^(2*B+n))).mpr
  convert hbound using 1 <;> first | rfl | ring

def amplitudeControl (n : ℕ) (A : 𝓢(Joint, ℂ)) : ℝ :=
  (Finset.Iic (0,n)).sup (schwartzSeminormFamily ℝ Joint ℂ) A

lemma amplitudeControl_nonneg (n : ℕ) (A : 𝓢(Joint, ℂ)) :
    0 ≤ amplitudeControl n A := apply_nonneg _ _

lemma amplitude_derivative_bound (n i : ℕ) (hi : i ≤ n)
    (A : 𝓢(Joint, ℂ)) (x : Joint) :
    ‖iteratedFDeriv ℝ i A x‖ ≤ amplitudeControl n A := by
  have hp : schwartzSeminormFamily ℝ Joint ℂ (0, i) ≤
      (Finset.Iic (0,n)).sup (schwartzSeminormFamily ℝ Joint ℂ) :=
    Finset.le_sup (Finset.mem_Iic.mpr ⟨le_rfl, hi⟩)
  have hz : ‖iteratedFDeriv ℝ i A x‖ ≤ SchwartzMap.seminorm ℝ 0 i A := by
    simpa using SchwartzMap.le_seminorm ℝ 0 i A x
  exact hz.trans (Seminorm.le_def.mp hp A)

theorem compact_profile_seminorm
    {K : Set Joint} (hK : IsCompact K) {φ h : Joint → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hh : ContDiff ℝ ∞ h)
    (hhpos : ∀ x ∈ K, 0 < h x) (B k n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : 𝓢(Joint, ℂ)), tsupport (A : Joint → ℂ) ⊆ K →
      ∀ (g : 𝓢(ℝ, ℂ)) (v R : ℝ), 0 ≤ R →
      ∀ (F : 𝓢(Joint, ℂ)),
      (∀ x, F x = A x * kernelLogPhase (v/(2*Real.pi)) (φ x) * g (R*h x)) →
      SchwartzMap.seminorm ℝ k n F ≤
        C*amplitudeControl n A*rayControl B n g*(1+|v|)^n/(1+R)^(2*B) := by
  obtain ⟨Dφ, hDφ, hbφ⟩ := compact_derivatives hK hφ n
  obtain ⟨Dh, hDh, hbh⟩ := compact_derivatives hK hh n
  obtain ⟨m, hm, hm1, hml⟩ := compact_positive_margin hK hh.continuous hhpos
  obtain ⟨L0, hL0⟩ := hK.bddAbove_image (continuous_norm.continuousOn : ContinuousOn (fun x : Joint => ‖x‖) K)
  let D := max Dφ Dh
  let L := max 1 L0
  have hD : 1 ≤ D := hDφ.trans (le_max_left _ _)
  have hL : 1 ≤ L := le_max_left _ _
  have hDp : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  let Cg : ℝ := (n.factorial : ℝ)*2^(2*B+n)*(D^2)^n/m^(2*B+n)
  have hCg : 0 < Cg := by dsimp [Cg]; positivity
  let Cp : ℝ := (n.factorial : ℝ)*D^n
  have hCp : 0 < Cp := by dsimp [Cp]; positivity
  refine ⟨L^k*2^n*2^n*Cp*Cg, by positivity, ?_⟩
  intro A hA g v R hR F hF
  have hp : ContDiff ℝ ∞ (fun y => kernelLogPhase (v/(2*Real.pi)) (φ y)) :=
    (JointLogSeparation.kernelLogPhase_temperate _).1.comp hφ
  have hg : ContDiff ℝ ∞ (fun y => g (R*h y)) :=
    (g.smooth ⊤).comp (contDiff_const.mul hh)
  have hFfun : (F : Joint → ℂ) =
      fun x => A x * kernelLogPhase (v/(2*Real.pi)) (φ x) * g (R*h x) := funext hF
  have hFs : tsupport (F : Joint → ℂ) ⊆ K := by
    rw [hFfun]
    exact (tsupport_mul_subset_left.trans tsupport_mul_subset_left).trans hA
  have hAn := amplitudeControl_nonneg n A
  have hgn := rayControl_nonneg B n g
  have hden : 0 < (1+R)^(2*B) := by positivity
  apply SchwartzMap.seminorm_le_bound ℝ k n F (by positivity)
  intro x
  by_cases hx : x ∈ K
  · have hxb : ‖x‖ ≤ L := (hL0 (mem_image_of_mem _ hx)).trans (le_max_right _ _)
    have hpbd (j : ℕ) (hj : j ≤ n) :
        ‖iteratedFDeriv ℝ j (fun y => kernelLogPhase (v/(2*Real.pi)) (φ y)) x‖ ≤
          Cp*(1+|v|)^n :=
      phase_derivative_bound hφ hD n j hj x
        (fun i hi => (hbφ i hi x hx).trans (le_max_left _ _)) v
    have hgbd (j : ℕ) (hj : j ≤ n) :
        ‖iteratedFDeriv ℝ j (fun y => g (R*h y)) x‖ ≤
          Cg*rayControl B n g/(1+R)^(2*B) :=
      kernel_derivative_bound hh hD hm hm1 hR B n j hj x
        (fun i hi => (hbh i hi x hx).trans (le_max_right _ _)) (hml x hx) g
    have hap (j : ℕ) (hj : j ≤ n) :
        ‖iteratedFDeriv ℝ j (fun y => A y * kernelLogPhase (v/(2*Real.pi)) (φ y)) x‖ ≤
          2^n*amplitudeControl n A*(Cp*(1+|v|)^n) := by
      calc
        _ ≤ 2^j*amplitudeControl n A*(Cp*(1+|v|)^n) :=
          mul_derivative_bound j (A.smooth ⊤) hp x hAn (by positivity)
            (fun i hi => amplitude_derivative_bound n i (hi.trans hj) A x)
            (fun i hi => hpbd i (hi.trans hj))
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) hAn) (by positivity)
    have hb := mul_derivative_bound n ((A.smooth ⊤).mul hp) hg x
      (C := 2^n*amplitudeControl n A*(Cp*(1+|v|)^n))
      (D := Cg*rayControl B n g/(1+R)^(2*B)) (by positivity) (by positivity) hap hgbd
    rw [hFfun]
    calc
      _ ≤ L^k * (2^n*(2^n*amplitudeControl n A*(Cp*(1+|v|)^n))*
          (Cg*rayControl B n g/(1+R)^(2*B))) :=
        mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hxb _) hb (norm_nonneg _) (by positivity)
      _ = _ := by ring
  · have hz : iteratedFDeriv ℝ n (F : Joint → ℂ) x = 0 := by
      apply Function.notMem_support.mp
      intro hx'
      exact hx (hFs ((support_iteratedFDeriv_subset n) hx'))
    rw [hz, norm_zero, mul_zero]
    positivity

lemma amplitudeControl_mono {n N : ℕ} (hn : n ≤ N) (A : 𝓢(Joint, ℂ)) :
    amplitudeControl n A ≤ amplitudeControl N A := by
  exact Seminorm.le_def.mp (Finset.sup_mono (by
    intro p hp
    exact Finset.mem_Iic.mpr (le_trans (Finset.mem_Iic.mp hp) ⟨le_rfl, hn⟩))) A

lemma rayControl_mono (B : ℕ) {n N : ℕ} (hn : n ≤ N) (g : 𝓢(ℝ, ℂ)) :
    rayControl B n g ≤ rayControl B N g := by
  exact Seminorm.le_def.mp (Finset.sup_mono (by
    intro p hp
    exact Finset.mem_Iic.mpr (le_trans (Finset.mem_Iic.mp hp) ⟨by omega, hn⟩))) g

def heightOrder (H : Finset (ℕ × ℕ)) : ℕ := H.sup Prod.snd

theorem compact_profile_finite
    {K : Set Joint} (hK : IsCompact K) {φ h : Joint → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hh : ContDiff ℝ ∞ h)
    (hhpos : ∀ x ∈ K, 0 < h x) (B : ℕ) (H : Finset (ℕ × ℕ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : 𝓢(Joint, ℂ)), tsupport (A : Joint → ℂ) ⊆ K →
      ∀ (g : 𝓢(ℝ, ℂ)) (v R : ℝ), 0 ≤ R →
      ∀ (F : 𝓢(Joint, ℂ)),
      (∀ x, F x = A x * kernelLogPhase (v/(2*Real.pi)) (φ x) * g (R*h x)) →
      sourceControl H F ≤
        C*amplitudeControl (heightOrder H) A*rayControl B (heightOrder H) g*
          (1+|v|)^(heightOrder H)/(1+R)^(2*B) := by
  have hc (p : ℕ × ℕ) := compact_profile_seminorm hK hφ hh hhpos B p.1 p.2
  choose C hC hbound using hc
  let D : ℝ := 1+∑ p ∈ H, C p
  have hD : 0 < D := by
    have hs : 0 ≤ ∑ p ∈ H, C p := Finset.sum_nonneg (fun p _ => (hC p).le)
    dsimp [D]
    linarith
  refine ⟨D, hD, ?_⟩
  intro A hA g v R hR F hF
  have hAn := amplitudeControl_nonneg (heightOrder H) A
  have hgn := rayControl_nonneg B (heightOrder H) g
  apply Seminorm.finset_sup_apply_le (by positivity)
  intro p hp
  have hn : p.2 ≤ heightOrder H := Finset.le_sup hp
  have hCD : C p ≤ D := by
    have hs := Finset.single_le_sum (fun p _ => (hC p).le) hp
    dsimp [D]
    linarith
  exact (hbound p A hA g v R hR F hF).trans (by
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul
    · exact mul_le_mul
        (mul_le_mul hCD (amplitudeControl_mono hn A)
          (amplitudeControl_nonneg _ _) hD.le)
        (rayControl_mono B hn g) (rayControl_nonneg _ _ _) (by positivity)
    · exact pow_le_pow_right₀ (by linarith [abs_nonneg v]) hn
    · positivity
    · positivity)

lemma sqrt_decay_absorption (T : ℝ) (hT : 0 ≤ T) (B : ℕ) :
    (1+T)^B ≤ (1+Real.sqrt T)^(2*B) := by
  have hbase : 1+T ≤ (1+Real.sqrt T)^2 := by
    nlinarith [Real.sq_sqrt hT, Real.sqrt_nonneg T]
  calc
    _ ≤ ((1+Real.sqrt T)^2)^B := pow_le_pow_left₀ (by positivity) hbase B
    _ = _ := by rw [pow_mul]

theorem compact_fourier_profile_finite
    {K : Set Joint} (hK : IsCompact K) {φ h : Joint → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hh : ContDiff ℝ ∞ h)
    (hhpos : ∀ x ∈ K, 0 < h x) (B : ℕ) (H : Finset (ℕ × ℕ)) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (A : 𝓢(Joint, ℂ)), tsupport (A : Joint → ℂ) ⊆ K →
      ∀ (U : 𝓢(ℝ, ℂ)) (v T : ℝ), 0 ≤ T →
      ∀ (F : 𝓢(Joint, ℂ)),
      (∀ x, F x = A x * kernelLogPhase (v/(2*Real.pi)) (φ x) *
        paperFourierRayCLM U (Real.sqrt T*h x)) →
      sourceControl H F ≤ C*amplitudeControl (heightOrder H) A*
        S.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^(heightOrder H)/(1+T)^B := by
  obtain ⟨D, hD, hbound⟩ := compact_profile_finite hK hφ hh hhpos B H
  obtain ⟨S, E, hE, hEbound⟩ := schwartzCLM_finite_seminorm_control
    paperFourierRayCLM (Finset.Iic (2*B+heightOrder H,heightOrder H))
  refine ⟨S, D*E, by positivity, ?_⟩
  intro A hA U v T hT F hF
  have hAn := amplitudeControl_nonneg (heightOrder H) A
  have hUn : 0 ≤ S.sup (schwartzSeminormFamily ℝ ℝ ℂ) U := apply_nonneg _ _
  have hg := hEbound U
  change rayControl B (heightOrder H) (paperFourierRayCLM U) ≤
    E*S.sup (schwartzSeminormFamily ℝ ℝ ℂ) U at hg
  calc
    _ ≤ D*amplitudeControl (heightOrder H) A*
        rayControl B (heightOrder H) (paperFourierRayCLM U)*
        (1+|v|)^(heightOrder H)/(1+Real.sqrt T)^(2*B) :=
      hbound A hA (paperFourierRayCLM U) v (Real.sqrt T) (Real.sqrt_nonneg _) F hF
    _ ≤ D*amplitudeControl (heightOrder H) A*
        (E*S.sup (schwartzSeminormFamily ℝ ℝ ℂ) U)*
        (1+|v|)^(heightOrder H)/(1+Real.sqrt T)^(2*B) := by
      gcongr
    _ ≤ D*amplitudeControl (heightOrder H) A*
        (E*S.sup (schwartzSeminormFamily ℝ ℝ ℂ) U)*
        (1+|v|)^(heightOrder H)/(1+T)^B :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (sqrt_decay_absorption T hT B)
    _ = _ := by ring

open ProbeGramJointConstruction

theorem jointProfile_homogeneous (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (B : ℕ) (H : Finset (ℕ × ℕ)) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : ℝ → ℂ) (hs : Function.support W ⊆ Icc a b) (hW : ContDiff ℝ ∞ W)
        (U : 𝓢(ℝ, ℂ)) (v T : ℝ) (hT : 0 ≤ T),
      sourceControl H (jointProfile W U a b ha hab hs hW v T hT) ≤
        C*amplitudeControl (heightOrder H) (amplitudeSchwartz W a b ha hab hs hW)*
          S.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*
          (1+|v|)^(heightOrder H)/(1+T)^B := by
  obtain ⟨S, C, hC, hb⟩ := compact_fourier_profile_finite
    (sourceCompact_isCompact b) (phase_smooth a b ha) (rootScale_smooth a b ha)
    (fun z _ => rootScale_pos a b ha z) B H
  refine ⟨S, C, hC, ?_⟩
  intro W hs hW U v T hT
  exact hb (amplitudeSchwartz W a b ha hab hs hW)
    (tsupport_amplitude_subset W a b ha hab hs) U v T hT
    (jointProfile W U a b ha hab hs hW v T hT)
    (jointProfile_factorization W U a b ha hab hs hW v T hT)

/-- Joint-profile seminorms have polynomial height growth and arbitrary radial decay. -/
theorem jointProfile_uniform_degree (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (B : ℕ) (H : Finset (ℕ × ℕ)) :
    ∃ (J : ℕ) (S : Finset (ℕ × ℕ)),
      ∀ (W : ℝ → ℂ) (hs : Function.support W ⊆ Icc a b) (hW : ContDiff ℝ ∞ W),
      ∃ C : ℝ, 0 < C ∧ ∀ (U : 𝓢(ℝ, ℂ)) (v T : ℝ) (hT : 0 ≤ T),
        sourceControl H (jointProfile W U a b ha hab hs hW v T hT) ≤
          C*S.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J/(1+T)^B := by
  obtain ⟨S, C, hC, hb⟩ := jointProfile_homogeneous a b ha hab B H
  refine ⟨heightOrder H, S, ?_⟩
  intro W hs hW
  let A := amplitudeControl (heightOrder H) (amplitudeSchwartz W a b ha hab hs hW)
  have hA : 0 ≤ A := amplitudeControl_nonneg _ _
  refine ⟨C*(1+A), by positivity, ?_⟩
  intro U v T hT
  have hU : 0 ≤ S.sup (schwartzSeminormFamily ℝ ℝ ℂ) U := apply_nonneg _ _
  exact (hb W hs hW U v T hT).trans (by
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by dsimp [A]; linarith :
        amplitudeControl (heightOrder H) (amplitudeSchwartz W a b ha hab hs hW) ≤ 1+A) hC.le) hU)

end ProbeGramJointProfile

end

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
