/-
Poisson summation on the Eisenstein lattice adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.FiniteReflectionBrackets

/-!
# Poisson summation on the Eisenstein lattice

Partial Fourier transforms of Schwartz functions, iterated one-dimensional Poisson summation
and Poisson summation for the Eisenstein embedding. Radial tests `scaledRadialTest`, lattice
summability of `paperRadialFourier`, and Pólya–Vinogradov for prime rows.
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

namespace SchwartzPlanePoisson

open MeasureTheory Filter LineDeriv
open scoped FourierTransform SchwartzMap Real RealInnerProductSpace
abbrev LogPlane := WithLp 2 (ℝ × ℝ)

/-- Fourier transformation in orthogonal coordinates is the iterated one-dimensional transform. -/
theorem fourier_prod_eq_iterated (f : LogPlane → ℂ) (hf : Integrable f) (ξ η : ℝ) :
    𝓕 f (WithLp.toLp 2 (ξ, η)) =
      𝓕 (fun x : ℝ => 𝓕 (fun y : ℝ => f (WithLp.toLp 2 (x, y))) η) ξ := by
  let w : LogPlane := WithLp.toLp 2 (ξ, η)
  let G : LogPlane → ℂ := fun z => Real.fourierChar (-⟪z, w⟫) • f z
  have hG : Integrable G := (Real.fourierIntegral_convergent_iff w).mpr hf
  have hGp : Integrable (fun z : ℝ × ℝ => G (WithLp.toLp 2 z)) :=
    (WithLp.volume_preserving_toLp ℝ ℝ).integrable_comp_of_integrable hG
  calc
    𝓕 f (WithLp.toLp 2 (ξ, η)) = ∫ z : LogPlane, G z := rfl
    _ = ∫ z : ℝ × ℝ, G (WithLp.toLp 2 z) :=
      ((WithLp.volume_preserving_toLp ℝ ℝ).integral_comp
        (MeasurableEquiv.toLp 2 (ℝ × ℝ)).measurableEmbedding G).symm
    _ = ∫ x : ℝ, ∫ y : ℝ, G (WithLp.toLp 2 (x, y)) := integral_prod _ hGp
    _ = 𝓕 (fun x : ℝ => 𝓕 (fun y : ℝ => f (WithLp.toLp 2 (x, y))) η) ξ := by
      simp only [Real.fourier_eq, Circle.smul_def, smul_eq_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        dsimp only
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun y => by
          simp only [G, w, WithLp.prod_inner_apply,
            neg_add, Real.fourierChar.map_add_eq_mul, Circle.smul_def, smul_eq_mul,
            Circle.coe_mul, mul_assoc]

def complexPoint (x y : ℝ) : ℂ := ⟨x, y⟩

theorem complexPoint_eq (x y : ℝ) : complexPoint x y = (x : ℂ) + Complex.I * (y : ℂ) := by
  apply Complex.ext <;> simp [complexPoint]

def planeComplexIso : LogPlane ≃ₗᵢ[ℝ] ℂ where
  toLinearEquiv := (WithLp.linearEquiv 2 ℝ (ℝ × ℝ)).trans
    Complex.equivRealProdCLM.toLinearEquiv.symm
  norm_map' z := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [WithLp.prod_norm_sq_eq_of_L2]
    change ‖complexPoint (WithLp.ofLp z).1 (WithLp.ofLp z).2‖ ^ 2 =
      ‖(WithLp.ofLp z).1‖ ^ 2 + ‖(WithLp.ofLp z).2‖ ^ 2
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply, complexPoint, Real.norm_eq_abs,  sq]

@[simp] theorem planeComplexIso_apply (x y : ℝ) :
    planeComplexIso (WithLp.toLp 2 (x, y)) = complexPoint x y := rfl

theorem horizontal_isometry (η : ℝ) : Isometry (fun x : ℝ => complexPoint x η) := by
  apply Isometry.of_dist_eq
  intro x y
  have h : complexPoint x η - complexPoint y η = ((x - y : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [complexPoint]
  simp only [dist_eq_norm, h, Complex.norm_real]

theorem horizontal_temperate (η : ℝ) :
    (fun x : ℝ => complexPoint x η).HasTemperateGrowth := by
  have heq : (fun x : ℝ => complexPoint x η) =
      (fun x : ℝ => Complex.ofRealCLM x + Complex.I * (η : ℂ)) := by
    funext x
    exact complexPoint_eq x η
  rw [heq]
  fun_prop

def horizontalSlice (f : SchwartzMap ℂ ℂ) (η : ℝ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.compCLMOfAntilipschitz ℂ (horizontal_temperate η)
    (horizontal_isometry η).antilipschitz f

@[simp] theorem horizontalSlice_apply (f : SchwartzMap ℂ ℂ) (η x : ℝ) :
    horizontalSlice f η x = f (complexPoint x η) := rfl

def partialFourier (f : SchwartzMap ℂ ℂ) (η x : ℝ) : ℂ :=
  𝓕 (fun y : ℝ => f (complexPoint x y)) η

theorem partialFourier_eq_integral (f : SchwartzMap ℂ ℂ) (η x : ℝ) :
    partialFourier f η x =
      ∫ y : ℝ, Real.fourierChar (-inner ℝ y η) • f (complexPoint x y) := rfl

theorem partialFourier_eq_exp_integral (f : SchwartzMap ℂ ℂ) (η x : ℝ) :
    partialFourier f η x = ∫ y : ℝ,
      Complex.exp (((-2 * Real.pi * (y * η) : ℝ) : ℂ) * Complex.I) *
        f ((x : ℂ) + Complex.I * (y : ℂ)) := by
  have hin (y : ℝ) : inner ℝ y η = y * η := by simp [RCLike.inner_apply, mul_comm]
  simp only [partialFourier, Real.fourier_eq', hin, complexPoint_eq, smul_eq_mul]

def verticalMajorant (f : SchwartzMap ℂ ℂ) (y : ℝ) : ℝ :=
  ((SchwartzMap.seminorm ℝ 0 0) f + (SchwartzMap.seminorm ℝ 2 0) f) * (1 + y ^ 2)⁻¹

theorem verticalMajorant_integrable (f : SchwartzMap ℂ ℂ) : Integrable (verticalMajorant f) :=
  integrable_inv_one_add_sq.const_mul _

theorem norm_le_verticalMajorant (f : SchwartzMap ℂ ℂ) (x y : ℝ) :
    ‖f (complexPoint x y)‖ ≤ verticalMajorant f y := by
  have h0 := SchwartzMap.norm_le_seminorm ℝ f (complexPoint x y)
  have h2 := SchwartzMap.norm_pow_mul_le_seminorm ℝ f 2 (complexPoint x y)
  have hy : y ^ 2 ≤ ‖complexPoint x y‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, complexPoint]
    nlinarith [sq_nonneg x]
  have hym := mul_le_mul_of_nonneg_right hy (norm_nonneg (f (complexPoint x y)))
  have hden : 0 < 1 + y ^ 2 := by positivity
  rw [verticalMajorant, ← div_eq_mul_inv]
  apply (le_div_iff₀ hden).mpr
  nlinarith only [h0, h2, hym]

theorem partialFourier_continuous (f : SchwartzMap ℂ ℂ) (η : ℝ) :
    Continuous (partialFourier f η) := by
  change Continuous (fun x : ℝ => ∫ y : ℝ,
    Real.fourierChar (-inner ℝ y η) • f (complexPoint x y))
  apply continuous_of_dominated
    (bound := verticalMajorant f)
  · intro x
    have hline : Continuous (fun y : ℝ => complexPoint x y) :=
      Complex.equivRealProdCLM.symm.continuous.comp (continuous_const.prodMk continuous_id)
    exact ((by fun_prop : Continuous (fun y : ℝ => Real.fourierChar (-inner ℝ y η))).smul
      (f.continuous.comp hline)).aestronglyMeasurable
  · intro x
    exact Eventually.of_forall fun y => by
      simpa only [Circle.smul_def, smul_eq_mul, norm_mul, Circle.norm_coe, one_mul] using
        norm_le_verticalMajorant f x y
  · exact verticalMajorant_integrable f
  · exact Eventually.of_forall fun y => by
      have hf : Continuous (fun x : ℝ => f (complexPoint x y)) :=
        f.continuous.comp (horizontal_isometry y).continuous
      exact continuous_const.smul hf

theorem partialFourier_integrable (f : SchwartzMap ℂ ℂ) (η : ℝ) :
    Integrable (partialFourier f η) := by
  let G : ℂ → ℂ := fun z => Real.fourierChar (-inner ℝ z.im η) • f z
  have hG : Integrable G := f.integrable.norm.mono'
    (by fun_prop : Continuous G).aestronglyMeasurable
    (Eventually.of_forall fun z => by
      simp only [G, Circle.smul_def, smul_eq_mul, norm_mul, Circle.norm_coe, one_mul]
      exact le_rfl)
  have hGp : Integrable (fun z : ℝ × ℝ => G (Complex.measurableEquivRealProd.symm z)) :=
    Complex.volume_preserving_equiv_real_prod.symm.integrable_comp_of_integrable hG
  change Integrable (fun x : ℝ => ∫ y : ℝ,
    Real.fourierChar (-inner ℝ y η) • f (complexPoint x y))
  simpa only [G, Complex.measurableEquivRealProd_symm_apply, complexPoint]
    using hGp.integral_prod_left

theorem fourier_partialFourier (f : SchwartzMap ℂ ℂ) (ξ η : ℝ) :
    𝓕 (partialFourier f η) ξ = 𝓕 (f : ℂ → ℂ) (complexPoint ξ η) := by
  let fp : SchwartzMap LogPlane ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ planeComplexIso.toContinuousLinearEquiv f
  have hprod := fourier_prod_eq_iterated (fp : LogPlane → ℂ) fp.integrable ξ η
  have hcoe : (fp : LogPlane → ℂ) = (f : ℂ → ℂ) ∘ planeComplexIso := rfl
  rw [hcoe, Real.fourier_comp_linearIsometry] at hprod
  change 𝓕 (fun x : ℝ => 𝓕 (fun y : ℝ => f (complexPoint x y)) η) ξ = _
  simpa only [Function.comp_apply, planeComplexIso_apply] using hprod.symm

/-- Partial Fourier transformation stays in the Schwartz class by Fourier inversion of a slice. -/
def partialFourierSchwartz (f : SchwartzMap ℂ ℂ) (η : ℝ) : SchwartzMap ℝ ℂ :=
  𝓕⁻ (horizontalSlice (𝓕 f) η)

theorem partialFourierSchwartz_apply (f : SchwartzMap ℂ ℂ) (η x : ℝ) :
    partialFourierSchwartz f η x = partialFourier f η x := by
  have heq : 𝓕 (partialFourier f η) =
      (horizontalSlice (𝓕 f) η : ℝ → ℂ) := by
    funext ξ
    rw [fourier_partialFourier, horizontalSlice_apply]
    exact (congrFun (SchwartzMap.fourier_coe f) (complexPoint ξ η)).symm
  have hi : Integrable (𝓕 (partialFourier f η)) := by
    rw [heq]
    exact (horizontalSlice (𝓕 f) η).integrable
  change (𝓕⁻ (horizontalSlice (𝓕 f) η)) x = _
  rw [congrFun (SchwartzMap.fourierInv_coe (horizontalSlice (𝓕 f) η)) x, ← heq]
  exact (partialFourier_integrable f η).fourierInv_fourier_eq hi
    (partialFourier_continuous f η).continuousAt

theorem partialFourierSchwartz_coe (f : SchwartzMap ℂ ℂ) (η : ℝ) :
    (partialFourierSchwartz f η : ℝ → ℂ) = partialFourier f η :=
  funext (partialFourierSchwartz_apply f η)

theorem fourier_partialFourierSchwartz (f : SchwartzMap ℂ ℂ) (ξ η : ℝ) :
    𝓕 (partialFourierSchwartz f η : ℝ → ℂ) ξ =
      𝓕 (f : ℂ → ℂ) ((ξ : ℂ) + Complex.I * (η : ℂ)) := by
  rw [partialFourierSchwartz_coe, fourier_partialFourier, complexPoint_eq]

theorem horizontal_hasFDerivAt (η x : ℝ) :
    HasFDerivAt (fun y : ℝ => complexPoint y η) Complex.ofRealCLM x := by
  have heq : (fun y : ℝ => complexPoint y η) =
      (fun y : ℝ => Complex.ofRealCLM y + Complex.I * (η : ℂ)) := by
    funext y
    exact complexPoint_eq y η
  rw [heq]
  exact Complex.ofRealCLM.hasFDerivAt.add_const _

theorem horizontalSlice_lineDerivOp (F : SchwartzMap ℂ ℂ) (η : ℝ) :
    ∂_{(1 : ℝ)} (horizontalSlice F η) = horizontalSlice (∂_{(1 : ℂ)} F) η := by
  apply SchwartzMap.ext
  intro x
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, horizontalSlice_apply,
    SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have hcomp := (F.hasFDerivAt (complexPoint x η)).comp x (horizontal_hasFDerivAt η x)
  change fderiv ℝ (fun y : ℝ => F (complexPoint y η)) x (1 : ℝ) = _
  change fderiv ℝ ((F : ℂ → ℂ) ∘ (fun y => complexPoint y η)) x (1 : ℝ) = _
  rw [hcomp.fderiv]
  simp only [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, Complex.ofReal_one]

theorem horizontalSlice_lineDerivOp_twice (F : SchwartzMap ℂ ℂ) (η : ℝ) :
    ∂_{(1 : ℝ)} (∂_{(1 : ℝ)} (horizontalSlice F η)) =
      horizontalSlice (∂_{(1 : ℂ)} (∂_{(1 : ℂ)} F)) η := by
  rw [horizontalSlice_lineDerivOp, horizontalSlice_lineDerivOp]

theorem summable_int_cauchy_weight :
    Summable (fun n : ℤ => (1 + (n : ℝ) ^ 2)⁻¹) := by
  classical
  have hp : Summable (fun n : ℤ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_int_pow.mpr (by norm_num)
  rw [← Finset.summable_compl_iff (s := ({0} : Finset ℤ))]
  apply Summable.of_nonneg_of_le (fun _ => by positivity) _
    (hp.subtype (fun n : ℤ => n ∉ ({0} : Finset ℤ)))
  intro n
  have hn : n.val ≠ 0 := by simpa only [Finset.mem_singleton] using n.property
  have hnr : (n.val : ℝ) ≠ 0 := by exact_mod_cast hn
  have hsq : 0 < (n.val : ℝ) ^ 2 := sq_pos_of_ne_zero hnr
  change (1 + (n.val : ℝ) ^ 2)⁻¹ ≤ 1 / (n.val : ℝ) ^ 2
  simpa only [one_div] using
    one_div_le_one_div_of_le hsq (show (n.val : ℝ) ^ 2 ≤ 1 + (n.val : ℝ) ^ 2 by linarith)

theorem summable_int_cauchy_product :
    Summable (fun p : ℤ × ℤ =>
      (1 + (p.1 : ℝ) ^ 2)⁻¹ * (1 + (p.2 : ℝ) ^ 2)⁻¹) :=
  summable_int_cauchy_weight.mul_of_nonneg summable_int_cauchy_weight
    (fun _ => by positivity) (fun _ => by positivity)

theorem summable_norm_of_cauchy_product (F : ℤ × ℤ → ℂ) (C : ℝ)
    (hF : ∀ p, ‖F p‖ ≤ C *
      ((1 + (p.1 : ℝ) ^ 2)⁻¹ * (1 + (p.2 : ℝ) ^ 2)⁻¹)) :
    Summable (fun p => ‖F p‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hF
    (summable_int_cauchy_product.mul_left C)

theorem summable_of_cauchy_product (F : ℤ × ℤ → ℂ) (C : ℝ)
    (hF : ∀ p, ‖F p‖ ≤ C *
      ((1 + (p.1 : ℝ) ^ 2)⁻¹ * (1 + (p.2 : ℝ) ^ 2)⁻¹)) : Summable F :=
  (summable_norm_of_cauchy_product F C hF).of_norm

def planeDecayConstant (F : SchwartzMap ℂ ℂ) : ℝ :=
  SchwartzMap.seminorm ℝ 0 0 F + SchwartzMap.seminorm ℝ 2 0 F +
    SchwartzMap.seminorm ℝ 4 0 F

theorem planeDecayConstant_nonneg (F : SchwartzMap ℂ ℂ) : 0 ≤ planeDecayConstant F := by
  unfold planeDecayConstant
  positivity

/-- Three seminorms give a summable product majorant on the integer lattice. -/
theorem plane_schwartz_product_decay (F : SchwartzMap ℂ ℂ) (ξ η : ℝ) :
    ((1 + ξ ^ 2) * (1 + η ^ 2)) * ‖F (complexPoint ξ η)‖ ≤
      planeDecayConstant F := by
  let z := complexPoint ξ η
  have hz : ‖z‖ ^ 2 = ξ ^ 2 + η ^ 2 := by
    rw [Complex.sq_norm]
    simp [z, Complex.normSq_apply, complexPoint, sq]
  have h0 := SchwartzMap.norm_le_seminorm ℝ F z
  have h2 := SchwartzMap.norm_pow_mul_le_seminorm ℝ F 2 z
  have h4 := SchwartzMap.norm_pow_mul_le_seminorm ℝ F 4 z
  have hz4 : ‖z‖ ^ 4 = (ξ ^ 2 + η ^ 2) ^ 2 := by
    calc
      ‖z‖ ^ 4 = (‖z‖ ^ 2) ^ 2 := by ring
      _ = (ξ ^ 2 + η ^ 2) ^ 2 := congrArg (fun t : ℝ => t ^ 2) hz
  have hxy : ξ ^ 2 * η ^ 2 ≤ ‖z‖ ^ 4 := by
    rw [hz4]
    nlinarith [sq_nonneg (ξ ^ 2), sq_nonneg (η ^ 2),
      mul_nonneg (sq_nonneg ξ) (sq_nonneg η)]
  have hm := mul_le_mul_of_nonneg_right hxy (norm_nonneg (F z))
  rw [hz] at h2
  change ((1 + ξ ^ 2) * (1 + η ^ 2)) * ‖F z‖ ≤ _
  unfold planeDecayConstant
  nlinarith only [h0, h2, h4, hm]

theorem norm_horizontalSlice_le (F : SchwartzMap ℂ ℂ) (η ξ : ℝ) :
    ‖horizontalSlice F η ξ‖ ≤
      (planeDecayConstant F / (1 + η ^ 2)) * (1 + ξ ^ 2)⁻¹ := by
  rw [horizontalSlice_apply, ← div_eq_mul_inv, div_div]
  apply (le_div_iff₀ (by positivity : 0 < (1 + η ^ 2) * (1 + ξ ^ 2))).mpr
  nlinarith [plane_schwartz_product_decay F ξ η]

theorem norm_inverse_horizontalSlice_le (F : SchwartzMap ℂ ℂ) (η x : ℝ) :
    ‖(𝓕⁻ (horizontalSlice F η)) x‖ ≤
      (planeDecayConstant F / (1 + η ^ 2)) * Real.pi := by
  rw [congrFun (SchwartzMap.fourierInv_coe (horizontalSlice F η)) x,
    Real.fourierInv_eq]
  have hb : Integrable (fun ξ : ℝ =>
      (planeDecayConstant F / (1 + η ^ 2)) * (1 + ξ ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul _
  have h := norm_integral_le_of_norm_le
    (f := fun ξ : ℝ => Real.fourierChar (inner ℝ ξ x) • horizontalSlice F η ξ) hb (Eventually.of_forall fun ξ => by
    simpa only [Circle.smul_def, smul_eq_mul, norm_mul, Circle.norm_coe, one_mul] using
      norm_horizontalSlice_le F η ξ)
  simpa only [integral_const_mul, integral_univ_inv_one_add_sq] using h

theorem norm_inverse_lineDeriv (g : SchwartzMap ℝ ℂ) (x : ℝ) :
    ‖(𝓕⁻ (∂_{(1 : ℝ)} g)) x‖ =
      (2 * Real.pi) * |x| * ‖(𝓕⁻ g) x‖ := by
  have ht : (fun u : ℝ => inner ℝ u (1 : ℝ)).HasTemperateGrowth := by fun_prop
  have hc : ‖(-(2 * Real.pi * Complex.I) : ℂ)‖ = 2 * Real.pi := by
    simp [ Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [SchwartzMap.fourierInv_lineDerivOp_eq]
  simp only [_root_.smul_apply, SchwartzMap.smulLeftCLM_apply_apply ht,
    norm_smul, hc]
  simp [RCLike.inner_apply, Real.norm_eq_abs, mul_assoc]

theorem sq_mul_norm_inverse_le_second (g : SchwartzMap ℝ ℂ) (x : ℝ) :
    x ^ 2 * ‖(𝓕⁻ g) x‖ ≤ ‖(𝓕⁻ (∂_{(1 : ℝ)} (∂_{(1 : ℝ)} g))) x‖ := by
  rw [norm_inverse_lineDeriv, norm_inverse_lineDeriv]
  have hp : 1 ≤ (2 * Real.pi) ^ 2 := by nlinarith [Real.pi_gt_three]
  calc
    x ^ 2 * ‖(𝓕⁻ g) x‖ ≤ ((2 * Real.pi) ^ 2 * x ^ 2) * ‖(𝓕⁻ g) x‖ :=
      mul_le_mul_of_nonneg_right (le_mul_of_one_le_left (sq_nonneg x) hp) (norm_nonneg _)
    _ = ((2 * Real.pi) ^ 2 * |x| ^ 2) * ‖(𝓕⁻ g) x‖ := by rw [sq_abs]
    _ = _ := by ring

theorem inverse_horizontalSlice_product_decay (F : SchwartzMap ℂ ℂ) (η x : ℝ) :
    ((1 + x ^ 2) * (1 + η ^ 2)) * ‖(𝓕⁻ (horizontalSlice F η)) x‖ ≤
      Real.pi * (planeDecayConstant F +
        planeDecayConstant (∂_{(1 : ℂ)} (∂_{(1 : ℂ)} F))) := by
  have h0 := norm_inverse_horizontalSlice_le F η x
  have h2a := sq_mul_norm_inverse_le_second (horizontalSlice F η) x
  rw [horizontalSlice_lineDerivOp_twice] at h2a
  have h2 := h2a.trans
    (norm_inverse_horizontalSlice_le (∂_{(1 : ℂ)} (∂_{(1 : ℂ)} F)) η x)
  have hden : 0 < 1 + η ^ 2 := by positivity
  have h0' : ‖(𝓕⁻ (horizontalSlice F η)) x‖ * (1 + η ^ 2) ≤
      planeDecayConstant F * Real.pi := by
    apply (le_div_iff₀ hden).mp
    simpa only [div_mul_eq_mul_div] using h0
  have h2' : (x ^ 2 * ‖(𝓕⁻ (horizontalSlice F η)) x‖) * (1 + η ^ 2) ≤
      planeDecayConstant (∂_{(1 : ℂ)} (∂_{(1 : ℂ)} F)) * Real.pi := by
    apply (le_div_iff₀ hden).mp
    simpa only [div_mul_eq_mul_div] using h2
  nlinarith only [h0', h2']

def partialFourierDecayConstant (f : SchwartzMap ℂ ℂ) : ℝ :=
  Real.pi * (planeDecayConstant (𝓕 f) +
    planeDecayConstant (∂_{(1 : ℂ)} (∂_{(1 : ℂ)} (𝓕 f))))

theorem partialFourierDecayConstant_nonneg (f : SchwartzMap ℂ ℂ) :
    0 ≤ partialFourierDecayConstant f :=
  mul_nonneg Real.pi_pos.le
    (add_nonneg (planeDecayConstant_nonneg _) (planeDecayConstant_nonneg _))

theorem partialFourier_product_decay (f : SchwartzMap ℂ ℂ) (η x : ℝ) :
    ((1 + x ^ 2) * (1 + η ^ 2)) * ‖partialFourier f η x‖ ≤
      partialFourierDecayConstant f := by
  rw [← partialFourierSchwartz_apply]
  exact inverse_horizontalSlice_product_decay (𝓕 f) η x

theorem norm_partialFourier_le (f : SchwartzMap ℂ ℂ) (η x : ℝ) :
    ‖partialFourier f η x‖ ≤
      partialFourierDecayConstant f * ((1 + x ^ 2)⁻¹ * (1 + η ^ 2)⁻¹) := by
  rw [← mul_inv, ← div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity : 0 < (1 + x ^ 2) * (1 + η ^ 2))).mpr
  nlinarith [partialFourier_product_decay f η x]

theorem partialFourier_lattice_summable_norm (f : SchwartzMap ℂ ℂ) :
    Summable (fun p : ℤ × ℤ =>
      ‖partialFourier f (p.2 : ℝ) (p.1 : ℝ)‖) := by
  apply summable_norm_of_cauchy_product
    (fun p : ℤ × ℤ => partialFourier f (p.2 : ℝ) (p.1 : ℝ))
    (partialFourierDecayConstant f)
  intro p
  exact norm_partialFourier_le f (p.2 : ℝ) (p.1 : ℝ)

theorem partialFourier_lattice_summable (f : SchwartzMap ℂ ℂ) :
    Summable (fun p : ℤ × ℤ => partialFourier f (p.2 : ℝ) (p.1 : ℝ)) :=
  (partialFourier_lattice_summable_norm f).of_norm

theorem plane_lattice_summable_norm (f : 𝓢(ℂ, ℂ)) :
    Summable (fun p : ℤ × ℤ => ‖f (complexPoint (p.1 : ℝ) (p.2 : ℝ))‖) := by
  apply summable_norm_of_cauchy_product _ (planeDecayConstant f)
  intro p
  rw [← mul_inv, ← div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity :
    0 < (1 + (p.1 : ℝ) ^ 2) * (1 + (p.2 : ℝ) ^ 2))).mpr
  nlinarith [plane_schwartz_product_decay f (p.1 : ℝ) (p.2 : ℝ)]

theorem plane_lattice_summable (f : 𝓢(ℂ, ℂ)) :
    Summable (fun p : ℤ × ℤ => f (complexPoint (p.1 : ℝ) (p.2 : ℝ))) :=
  (plane_lattice_summable_norm f).of_norm

theorem vertical_isometry (x : ℝ) : Isometry (fun y : ℝ => complexPoint x y) := by
  apply Isometry.of_dist_eq
  intro y z
  have h : complexPoint x y - complexPoint x z =
      Complex.I * ((y - z : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [complexPoint]
  simp only [dist_eq_norm, h, norm_mul, Complex.norm_I, one_mul, Complex.norm_real]

theorem vertical_temperate (x : ℝ) :
    (fun y : ℝ => complexPoint x y).HasTemperateGrowth := by
  have heq : (fun y : ℝ => complexPoint x y) =
      (fun y : ℝ => (x : ℂ) + Complex.I * Complex.ofRealCLM y) := by
    funext y
    exact complexPoint_eq x y
  rw [heq]
  fun_prop

def verticalSlice (f : 𝓢(ℂ, ℂ)) (x : ℝ) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLMOfAntilipschitz ℂ (vertical_temperate x)
    (vertical_isometry x).antilipschitz f

@[simp] theorem verticalSlice_apply (f : 𝓢(ℂ, ℂ)) (x y : ℝ) :
    verticalSlice f x y = f (complexPoint x y) := rfl

theorem schwartz_poisson_zero (g : 𝓢(ℝ, ℂ)) :
    (∑' n : ℤ, g (n : ℝ)) = ∑' n : ℤ, 𝓕 (g : ℝ → ℂ) (n : ℝ) := by
  simpa [fourier_eval_zero, SchwartzMap.fourier_coe] using g.tsum_eq_tsum_fourier 0

theorem vertical_poisson (f : 𝓢(ℂ, ℂ)) (x : ℝ) :
    (∑' n : ℤ, f (complexPoint x (n : ℝ))) =
      ∑' n : ℤ, partialFourier f (n : ℝ) x := by
  exact schwartz_poisson_zero (verticalSlice f x)

private theorem horizontal_poisson (f : 𝓢(ℂ, ℂ)) (n : ℤ) :
    (∑' m : ℤ, partialFourier f (n : ℝ) (m : ℝ)) =
      ∑' k : ℤ, (𝓕 f) (complexPoint (k : ℝ) (n : ℝ)) := by
  have h := schwartz_poisson_zero (partialFourierSchwartz f n)
  simpa only [partialFourierSchwartz_apply, partialFourierSchwartz_coe,
    fourier_partialFourier, SchwartzMap.fourier_coe] using h

private theorem iterated_poisson_pair_sum
    (f g h : ℤ → ℤ → ℂ)
    (hf : Summable (Function.uncurry f))
    (hg : Summable (Function.uncurry g))
    (hh : Summable (Function.uncurry h))
    (hvertical : ∀ m, (∑' n, f m n) = ∑' n, h m n)
    (hhorizontal : ∀ n, (∑' m, h m n) = ∑' m, g m n) :
    (∑' p : ℤ × ℤ, f p.1 p.2) = ∑' p : ℤ × ℤ, g p.1 p.2 := by
  calc
    (∑' p : ℤ × ℤ, f p.1 p.2) = ∑' m, ∑' n, f m n := hf.tsum_prod
    _ = ∑' m, ∑' n, h m n := tsum_congr hvertical
    _ = ∑' n, ∑' m, h m n := hh.tsum_comm.symm
    _ = ∑' n, ∑' m, g m n := tsum_congr hhorizontal
    _ = ∑' m, ∑' n, g m n := hg.tsum_comm
    _ = ∑' p : ℤ × ℤ, g p.1 p.2 := hg.tsum_prod.symm

/-- Absolute convergence permits two successive one-dimensional Poisson transformations. -/
theorem integer_pair_poisson (f : 𝓢(ℂ, ℂ)) :
    (∑' p : ℤ × ℤ, f (complexPoint (p.1 : ℝ) (p.2 : ℝ))) =
      ∑' p : ℤ × ℤ, (𝓕 f) (complexPoint (p.1 : ℝ) (p.2 : ℝ)) := by
  exact iterated_poisson_pair_sum
    (fun m n => f (complexPoint (m : ℝ) (n : ℝ)))
    (fun m n : ℤ => (𝓕 f : 𝓢(ℂ, ℂ)) (complexPoint (m : ℝ) (n : ℝ)))
    (fun m n => partialFourier f (n : ℝ) (m : ℝ))
    (plane_lattice_summable f) (plane_lattice_summable (𝓕 f))
    (partialFourier_lattice_summable f)
    (fun m => vertical_poisson f m) (horizontal_poisson f)



section
open MeasureTheory
open scoped FourierTransform SchwartzMap RealInnerProductSpace

def inverseJacobian (A : ℂ ≃L[ℝ] ℂ) : ℝ :=
  |(LinearMap.det (A : ℂ →ₗ[ℝ] ℂ))⁻¹|

theorem integral_comp_linearEquiv (A : ℂ ≃L[ℝ] ℂ) (f : ℂ → ℂ) :
    (∫ x : ℂ, f (A x)) = inverseJacobian A • ∫ x : ℂ, f x := by
  have h := integral_map_equiv («μ» := (volume : Measure ℂ))
    A.toHomeomorph.toMeasurableEquiv f
  have hm : Measure.map A (volume : Measure ℂ) =
      ENNReal.ofReal (inverseJacobian A) • volume := by
    exact Measure.map_linearMap_addHaar_eq_smul_addHaar volume
      A.toLinearEquiv.isUnit_det'.ne_zero
  change (∫ y : ℂ, f y ∂Measure.map A volume) = (∫ x : ℂ, f (A x)) at h
  rw [hm, integral_smul_measure, ENNReal.toReal_ofReal (show 0 ≤ inverseJacobian A from abs_nonneg _)] at h
  exact h.symm

def dualMap (A : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ :=
  A.symm.toContinuousLinearMap.adjoint

theorem inner_linear_dual (A : ℂ ≃L[ℝ] ℂ) (x y : ℂ) :
    inner ℝ (A x) (dualMap A y) = inner ℝ x y := by
  rw [dualMap, ContinuousLinearMap.adjoint_inner_right]
  simp

theorem fourier_comp_linearEquiv (A : ℂ ≃L[ℝ] ℂ) (f : ℂ → ℂ) (w : ℂ) :
    𝓕 (f ∘ A) w = inverseJacobian A • 𝓕 f (dualMap A w) := by
  let H : ℂ → ℂ := fun z => Real.fourierChar (-inner ℝ z (dualMap A w)) • f z
  calc
    𝓕 (f ∘ A) w = ∫ x : ℂ, H (A x) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        simp only [H, inner_linear_dual, Function.comp_apply]
        rfl
    _ = inverseJacobian A • ∫ z : ℂ, H z := integral_comp_linearEquiv A H
    _ = inverseJacobian A • 𝓕 f (dualMap A w) := rfl

def translateSchwartz (f : 𝓢(ℂ, ℂ)) (b : ℂ) : 𝓢(ℂ, ℂ) :=
  SchwartzMap.compCLMOfAntilipschitz ℂ (g := fun z : ℂ => z + b)
    (by fun_prop) (isometry_add_right b).antilipschitz f

@[simp] theorem translateSchwartz_apply (f : 𝓢(ℂ, ℂ)) (b z : ℂ) :
    translateSchwartz f b z = f (z + b) := rfl

theorem fourier_translate (f : ℂ → ℂ) (b w : ℂ) :
    𝓕 (fun z => f (z + b)) w =
      Real.fourierChar (inner ℝ b w) • 𝓕 f w := by
  exact congrFun
    (VectorFourier.fourierIntegral_comp_add_right Real.fourierChar
      (volume : Measure ℂ) (innerₗ ℂ) f b) w

def affinePullback (f : 𝓢(ℂ, ℂ)) (A : ℂ ≃L[ℝ] ℂ) (b : ℂ) : 𝓢(ℂ, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A (translateSchwartz f b)

@[simp] theorem affinePullback_apply (f : 𝓢(ℂ, ℂ)) (A : ℂ ≃L[ℝ] ℂ) (b z : ℂ) :
    affinePullback f A b z = f (A z + b) := rfl

theorem fourier_affinePullback (f : 𝓢(ℂ, ℂ)) (A : ℂ ≃L[ℝ] ℂ) (b w : ℂ) :
    (𝓕 (affinePullback f A b)) w =
      inverseJacobian A •
        (Real.fourierChar (inner ℝ b (dualMap A w)) • (𝓕 f) (dualMap A w)) := by
  rw [congrFun (SchwartzMap.fourier_coe _) w]
  change 𝓕 ((fun z => f (z + b)) ∘ A) w = _
  rw [fourier_comp_linearEquiv, fourier_translate]
  rw [congrFun (SchwartzMap.fourier_coe f) (dualMap A w)]

theorem affine_lattice_poisson (f : 𝓢(ℂ, ℂ)) (A : ℂ ≃L[ℝ] ℂ) (b : ℂ) :
    (∑' p : ℤ × ℤ, f (A (complexPoint (p.1 : ℝ) (p.2 : ℝ)) + b)) =
      inverseJacobian A • ∑' p : ℤ × ℤ,
        Real.fourierChar (inner ℝ b (dualMap A (complexPoint (p.1 : ℝ) (p.2 : ℝ)))) •
          (𝓕 f) (dualMap A (complexPoint (p.1 : ℝ) (p.2 : ℝ))) := by
  have h := integer_pair_poisson (affinePullback f A b)
  simp only [affinePullback_apply, fourier_affinePullback] at h
  rw [tsum_const_smul''] at h
  exact h

end

section
open scoped RealInnerProductSpace

def basisMap (w : ℂ) : ℂ →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp Complex.reCLM +
    w • (Complex.ofRealCLM.comp Complex.imCLM)

@[simp] theorem basisMap_apply (w z : ℂ) :
    basisMap w z = (z.re : ℂ) + w * (z.im : ℂ) := rfl

def basisEquiv (w : ℂ) (hw : w.im ≠ 0) : ℂ ≃L[ℝ] ℂ where
  toLinearEquiv :=
    { toLinearMap := (basisMap w).toLinearMap
      invFun z := complexPoint (z.re - z.im * w.re / w.im) (z.im / w.im)
      left_inv z := by
        change complexPoint ((basisMap w z).re - (basisMap w z).im * w.re / w.im)
          ((basisMap w z).im / w.im) = z
        apply Complex.ext
        · simp only [basisMap_apply, Complex.add_re, Complex.ofReal_re,
            Complex.mul_re, Complex.ofReal_im, mul_zero, sub_zero,
            Complex.add_im, Complex.mul_im,  zero_add, complexPoint]
          field_simp [hw]
          ring
        · simp [basisMap_apply, complexPoint, hw]
      right_inv z := by
        change basisMap w (complexPoint (z.re - z.im * w.re / w.im)
          (z.im / w.im)) = z
        apply Complex.ext
        · simp only [basisMap_apply, complexPoint, Complex.add_re, Complex.ofReal_re,
            Complex.mul_re, Complex.ofReal_im, mul_zero, sub_zero]
          field_simp [hw]
          ring
        · simp only [basisMap_apply, complexPoint, Complex.add_im,
            Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, mul_zero, zero_add]
          field_simp [hw] }
  continuous_toFun := (basisMap w).continuous
  continuous_invFun := by
    simp only [complexPoint_eq]
    fun_prop

@[simp] theorem basisEquiv_apply (w : ℂ) (hw : w.im ≠ 0) (z : ℂ) :
    basisEquiv w hw z = (z.re : ℂ) + w * (z.im : ℂ) := rfl

@[simp] theorem basisEquiv_symm_apply (w : ℂ) (hw : w.im ≠ 0) (z : ℂ) :
    (basisEquiv w hw).symm z =
      complexPoint (z.re - z.im * w.re / w.im) (z.im / w.im) := rfl

theorem basisEquiv_det (w : ℂ) (hw : w.im ≠ 0) :
    LinearMap.det ((basisEquiv w hw) : ℂ →ₗ[ℝ] ℂ) = w.im := by
  rw [← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, Complex.coe_basisOneI,
    Complex.coe_basisOneI_repr, basisEquiv_apply]

def complexMulEquiv (c : ℂ) (hc : c ≠ 0) : ℂ ≃L[ℝ] ℂ :=
  ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := ℂ) (Units.mk0 c hc)

@[simp] theorem complexMulEquiv_apply (c : ℂ) (hc : c ≠ 0) (z : ℂ) :
    complexMulEquiv c hc z = c * z := rfl

@[simp] theorem complexMulEquiv_symm_apply (c : ℂ) (hc : c ≠ 0) (z : ℂ) :
    (complexMulEquiv c hc).symm z = c⁻¹ * z := rfl

theorem complexMulEquiv_det (c : ℂ) (hc : c ≠ 0) :
    LinearMap.det ((complexMulEquiv c hc) : ℂ →ₗ[ℝ] ℂ) = Complex.normSq c := by
  rw [← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, Complex.coe_basisOneI,
    Complex.coe_basisOneI_repr, complexMulEquiv_apply, Complex.normSq_apply]

def scaledBasisEquiv (w : ℂ) (hw : w.im ≠ 0) (c : ℂ) (hc : c ≠ 0) : ℂ ≃L[ℝ] ℂ :=
  (basisEquiv w hw).trans (complexMulEquiv c hc)

@[simp] theorem scaledBasisEquiv_apply (w : ℂ) (hw : w.im ≠ 0)
    (c : ℂ) (hc : c ≠ 0) (z : ℂ) :
    scaledBasisEquiv w hw c hc z = c * ((z.re : ℂ) + w * (z.im : ℂ)) := rfl

theorem scaledBasisEquiv_det (w : ℂ) (hw : w.im ≠ 0) (c : ℂ) (hc : c ≠ 0) :
    LinearMap.det ((scaledBasisEquiv w hw c hc) : ℂ →ₗ[ℝ] ℂ) =
      Complex.normSq c * w.im := by
  change LinearMap.det
    (((complexMulEquiv c hc) : ℂ →ₗ[ℝ] ℂ).comp ((basisEquiv w hw) : ℂ →ₗ[ℝ] ℂ)) = _
  rw [LinearMap.det_comp, complexMulEquiv_det, basisEquiv_det]

end

end SchwartzPlanePoisson

namespace SchwartzPlanePoisson
open Eisenstein MeasureTheory
open scoped FourierTransform SchwartzMap RealInnerProductSpace

theorem finite_quotient_span {c : O} (hc : c ≠ 0) :
    Finite (O ⧸ Ideal.span {c}) :=
  (Ideal.span {c}).finiteQuotientOfFreeOfNeBot
    (fun h => hc (Ideal.span_singleton_eq_bot.mp h))

namespace GaussianAbelPartition

theorem tsum_by_finite_fibers {A B : Type*} [Fintype B]
    (q : A → B) (f : A → ℂ) (hf : Summable f) :
    (∑' a : A, f a) =
      ∑ b : B, ∑' a : (q ⁻¹' {b}), f a.1 := by
  have h := (hf.hasSum.tsum_fiberwise q).tsum_eq
  simpa only [tsum_fintype] using h.symm

theorem tsum_periodic_weighted_partition {A B : Type*} [Fintype B]
    (q : A → B) (P : B → ℂ) (W : A → ℂ)
    (hf : Summable (fun a => P (q a) * W a)) :
    (∑' a : A, P (q a) * W a) =
      ∑ b : B, P b * ∑' a : (q ⁻¹' {b}), W a.1 := by
  rw [tsum_by_finite_fibers q _ hf]
  apply Finset.sum_congr rfl
  intro b hb
  calc
    (∑' a : (q ⁻¹' {b}), P (q a.1) * W a.1) =
        ∑' a : (q ⁻¹' {b}), P b * W a.1 := by
      apply tsum_congr
      intro a
      have ha : q a.1 = b := by
        simpa only [Set.mem_preimage, Set.mem_singleton_iff] using a.property
      rw [ha]
    _ = P b * ∑' a : (q ⁻¹' {b}), W a.1 := tsum_mul_left

end GaussianAbelPartition
namespace GaussianFiberEquiv


def fiberMap (c : O) (r : O ⧸ Ideal.span {c})
    (r0 : O) (hr : Ideal.Quotient.mk (Ideal.span {c}) r0 = r)
    (w : O) : ((Ideal.Quotient.mk (Ideal.span {c})) ⁻¹' {r}) := by
  refine ⟨r0 + c*w, ?_⟩
  change Ideal.Quotient.mk (Ideal.span {c}) (r0 + c*w) = r
  rw [map_add, map_mul]
  have hc0 : Ideal.Quotient.mk (Ideal.span {c}) c = 0 :=
    (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.subset_span (Set.mem_singleton c))
  rw [hc0, zero_mul, add_zero, hr]

private theorem fiberMap_injective (c : O) (hc : c ≠ 0)
    (r : O ⧸ Ideal.span {c}) (r0 : O)
    (hr : Ideal.Quotient.mk (Ideal.span {c}) r0 = r) :
    Function.Injective (fiberMap c r r0 hr) := by
  intro u v h
  have hval := congrArg Subtype.val h
  change r0 + c*u = r0 + c*v at hval
  exact mul_left_cancel₀ hc (add_left_cancel hval)

private theorem fiberMap_surjective (c : O)
    (r : O ⧸ Ideal.span {c}) (r0 : O)
    (hr : Ideal.Quotient.mk (Ideal.span {c}) r0 = r) :
    Function.Surjective (fiberMap c r r0 hr) := by
  rintro ⟨z, hz⟩
  have hz' : Ideal.Quotient.mk (Ideal.span {c}) z = r := by
    simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hz
  have hdiff : z-r0 ∈ Ideal.span {c} :=
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem z r0).mp (hz'.trans hr.symm)
  obtain ⟨w, hw⟩ := (Ideal.mem_span_singleton).mp hdiff
  refine ⟨w, ?_⟩
  apply Subtype.ext
  change r0 + c*w = z
  rw [← hw]
  ring

noncomputable def fiberEquiv (c : O) (hc : c ≠ 0)
    (r : O ⧸ Ideal.span {c}) (r0 : O)
    (hr : Ideal.Quotient.mk (Ideal.span {c}) r0 = r) :
    O ≃ ((Ideal.Quotient.mk (Ideal.span {c})) ⁻¹' {r}) :=
  Equiv.ofBijective (fiberMap c r r0 hr)
    ⟨fiberMap_injective c hc r r0 hr, fiberMap_surjective c r r0 hr⟩

theorem fiber_tsum (c : O) (hc : c ≠ 0)
    (r : O ⧸ Ideal.span {c}) (r0 : O)
    (hr : Ideal.Quotient.mk (Ideal.span {c}) r0 = r)
    (W : O → ℂ) :
    (∑' z : ((Ideal.Quotient.mk (Ideal.span {c})) ⁻¹' {r}), W z.1) =
      ∑' w : O, W (r0 + c*w) := by
  have h := (fiberEquiv c hc r r0 hr).tsum_eq (fun z => W z.1)
  have happ (w : O) : ((fiberEquiv c hc r r0 hr) w).1 = r0 + c*w := rfl
  simpa only [happ] using h.symm

end GaussianFiberEquiv

namespace GaussianShiftedPartition


noncomputable def representative (c : O) (r : O ⧸ Ideal.span {c}) : O :=
  Classical.choose (Ideal.Quotient.mk_surjective r)

theorem representative_spec (c : O) (r : O ⧸ Ideal.span {c}) :
    Ideal.Quotient.mk (Ideal.span {c}) (representative c r) = r :=
  Classical.choose_spec (Ideal.Quotient.mk_surjective r)

end GaussianShiftedPartition

/-- Poisson summation for the actual Eisenstein embedding, in either orientation. -/
def eisensteinLatticeMap (c : ℂ) (hc : c ≠ 0) : ℂ ≃L[ℝ] ℂ :=
  scaledBasisEquiv (ringComplex omega) complex_omega_im_ne_zero c hc

theorem eisensteinLatticeMap_point (c : ℂ) (hc : c ≠ 0) (p : ℤ × ℤ) :
    eisensteinLatticeMap c hc (complexPoint (p.1 : ℝ) (p.2 : ℝ)) =
      c * ringComplex (Eisenstein.Coordinates.eval p.1 p.2) := by
  simp [eisensteinLatticeMap, complexPoint, ringComplex_eval, mul_comm]

theorem eisenstein_inverseJacobian (c : ℂ) (hc : c ≠ 0) :
    inverseJacobian (eisensteinLatticeMap c hc) = 2 / (Real.sqrt 3 * ‖c‖ ^ 2) := by
  unfold inverseJacobian eisensteinLatticeMap
  rw [scaledBasisEquiv_det, abs_inv, abs_mul,
    abs_of_nonneg (Complex.normSq_nonneg c), complex_omega_im_abs,
    Complex.normSq_eq_norm_sq]
  ring

def eisensteinDualFrequency (c : ℂ) (hc : c ≠ 0) (p : ℤ × ℤ) : ℂ :=
  dualMap (eisensteinLatticeMap c hc) (complexPoint (p.1 : ℝ) (p.2 : ℝ))

theorem actual_eisenstein_coset_poisson (f : 𝓢(ℂ, ℂ)) (b c : O) (hc : c ≠ 0) :
    (∑' z : O, f (ringComplex (b + c * z))) =
      (2 / (Real.sqrt 3 * ‖ringComplex c‖ ^ 2)) • ∑' p : ℤ × ℤ,
        Real.fourierChar (inner ℝ (ringComplex b)
          (eisensteinDualFrequency (ringComplex c) (ringComplex_ne_zero hc) p)) •
        (𝓕 f) (eisensteinDualFrequency (ringComplex c) (ringComplex_ne_zero hc) p) := by
  let A := eisensteinLatticeMap (ringComplex c) (ringComplex_ne_zero hc)
  have h := affine_lattice_poisson f A (ringComplex b)
  rw [eisenstein_inverseJacobian] at h
  calc
    (∑' z : O, f (ringComplex (b + c * z))) =
        ∑' p : ℤ × ℤ, f (ringComplex (b + c * Eisenstein.Coordinates.coordinateEquiv.symm p)) :=
      (Eisenstein.Coordinates.coordinateEquiv.symm.tsum_eq _).symm
    _ = ∑' p : ℤ × ℤ,
        f (A (complexPoint (p.1 : ℝ) (p.2 : ℝ)) + ringComplex b) := by
      apply tsum_congr
      intro p
      congr 1
      rw [map_add, map_mul]
      change ringComplex b + ringComplex c *
          ringComplex (Eisenstein.Coordinates.eval p.1 p.2) = _
      rw [← eisensteinLatticeMap_point]
      exact add_comm _ _
    _ = _ := h

theorem actual_eisenstein_coset_summable_norm (f : 𝓢(ℂ, ℂ)) (b c : O) (hc : c ≠ 0) :
    Summable (fun z : O => ‖f (ringComplex (b + c * z))‖) := by
  let A := eisensteinLatticeMap (ringComplex c) (ringComplex_ne_zero hc)
  have hp := plane_lattice_summable_norm (affinePullback f A (ringComplex b))
  have hpair : Summable (fun p : ℤ × ℤ =>
      ‖f (ringComplex (b + c * Eisenstein.Coordinates.coordinateEquiv.symm p))‖) := by
    convert hp using 1
    funext p
    rw [affinePullback_apply]
    apply congrArg norm
    apply congrArg f
    rw [map_add, map_mul]
    change ringComplex b + ringComplex c *
        ringComplex (Eisenstein.Coordinates.eval p.1 p.2) = _
    rw [← eisensteinLatticeMap_point]
    exact add_comm _ _
  exact (Eisenstein.Coordinates.coordinateEquiv.symm.summable_iff).mp hpair

theorem actual_eisenstein_summable_norm (f : 𝓢(ℂ, ℂ)) :
    Summable (fun z : O => ‖f (ringComplex z)‖) := by
  simpa using actual_eisenstein_coset_summable_norm f 0 1 one_ne_zero

theorem actual_eisenstein_periodic_summable (f : 𝓢(ℂ, ℂ))
    {R : Type*} [Fintype R] (q : O → R) (P : R → ℂ) :
    Summable (fun z : O => P (q z) * f (ringComplex z)) := by
  classical
  let C : ℝ := ∑ r : R, ‖P r‖
  have hP (r : R) : ‖P r‖ ≤ C :=
    Finset.single_le_sum (fun a _ => norm_nonneg (P a)) (Finset.mem_univ r)
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun z => norm_nonneg _) _
    ((actual_eisenstein_summable_norm f).mul_left C)
  intro z
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hP (q z)) (norm_nonneg _)

theorem actual_eisenstein_periodic_poisson (f : 𝓢(ℂ, ℂ)) (c : O) (hc : c ≠ 0)
    (P : O ⧸ Ideal.span {c} → ℂ) :
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    (∑' z : O, P (Ideal.Quotient.mk (Ideal.span {c}) z) * f (ringComplex z)) =
      ∑ r : O ⧸ Ideal.span {c}, P r *
        ((2 / (Real.sqrt 3 * ‖ringComplex c‖ ^ 2)) • ∑' p : ℤ × ℤ,
          Real.fourierChar (inner ℝ
            (ringComplex (GaussianShiftedPartition.representative c r))
            (eisensteinDualFrequency (ringComplex c) (ringComplex_ne_zero hc) p)) •
          (𝓕 f) (eisensteinDualFrequency (ringComplex c) (ringComplex_ne_zero hc) p)) := by
  classical
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  rw [GaussianAbelPartition.tsum_periodic_weighted_partition
    (Ideal.Quotient.mk (Ideal.span {c})) P (fun z => f (ringComplex z))
    (actual_eisenstein_periodic_summable f _ P)]
  apply Finset.sum_congr rfl
  intro r hr
  congr 1
  exact (GaussianFiberEquiv.fiber_tsum c hc r
    (GaussianShiftedPartition.representative c r)
    (GaussianShiftedPartition.representative_spec c r)
    (fun z => f (ringComplex z))).trans
      (actual_eisenstein_coset_poisson f _ c hc)

theorem inverseJacobian_pos (A : ℂ ≃L[ℝ] ℂ) : 0 < inverseJacobian A :=
  abs_pos.mpr (inv_ne_zero A.toLinearEquiv.isUnit_det'.ne_zero)

theorem dual_lattice_summable_norm (f : 𝓢(ℂ, ℂ)) (A : ℂ ≃L[ℝ] ℂ) :
    Summable (fun p : ℤ × ℤ =>
      ‖(𝓕 f) (dualMap A (complexPoint (p.1 : ℝ) (p.2 : ℝ)))‖) := by
  have hJ := inverseJacobian_pos A
  have hp := plane_lattice_summable_norm (𝓕 (affinePullback f A 0))
  have hn (p : ℤ × ℤ) :
      ‖(𝓕 (affinePullback f A 0)) (complexPoint (p.1 : ℝ) (p.2 : ℝ))‖ =
      inverseJacobian A * ‖(𝓕 f) (dualMap A (complexPoint (p.1 : ℝ) (p.2 : ℝ)))‖ := by
    rw [fourier_affinePullback]
    simp [ abs_of_pos hJ]
  simp_rw [hn] at hp
  have hi := hp.mul_left (inverseJacobian A)⁻¹
  simpa only [← mul_assoc, inv_mul_cancel₀ hJ.ne', one_mul] using hi

theorem finite_phase_sum {R : Type*} [Fintype R]
    (f : 𝓢(ℂ, ℂ)) (A : ℂ ≃L[ℝ] ℂ) (b : R → ℂ) (P : R → ℂ) :
    (∑ r : R, P r * (inverseJacobian A • ∑' p : ℤ × ℤ,
      Real.fourierChar (inner ℝ (b r) (dualMap A (complexPoint (p.1 : ℝ) (p.2 : ℝ)))) •
        (𝓕 f) (dualMap A (complexPoint (p.1 : ℝ) (p.2 : ℝ))))) =
    inverseJacobian A • ∑' p : ℤ × ℤ,
      (∑ r : R, P r * (Real.fourierChar (inner ℝ (b r)
        (dualMap A (complexPoint (p.1 : ℝ) (p.2 : ℝ)))) : ℂ)) *
        (𝓕 f) (dualMap A (complexPoint (p.1 : ℝ) (p.2 : ℝ))) := by
  classical
  have hs (r : R) : Summable (fun p : ℤ × ℤ =>
      P r * (Real.fourierChar (inner ℝ (b r)
        (dualMap A (complexPoint (p.1 : ℝ) (p.2 : ℝ)))) •
        (𝓕 f) (dualMap A (complexPoint (p.1 : ℝ) (p.2 : ℝ))))) := by
    apply Summable.mul_left
    apply Summable.of_norm
    simpa only [Circle.norm_smul] using dual_lattice_summable_norm f A
  simp_rw [mul_smul_comm, ← tsum_mul_left]
  rw [← Finset.smul_sum, ← Summable.tsum_finsetSum (fun r _ => hs r)]
  congr 1
  apply tsum_congr
  intro p
  simp only [Circle.smul_def, smul_eq_mul, Finset.sum_mul, mul_assoc]

theorem actual_eisenstein_periodic_fourier (f : 𝓢(ℂ, ℂ)) (c : O) (hc : c ≠ 0)
    (P : O ⧸ Ideal.span {c} → ℂ) :
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    (∑' z : O, P (Ideal.Quotient.mk (Ideal.span {c}) z) * f (ringComplex z)) =
      (2 / (Real.sqrt 3 * ‖ringComplex c‖ ^ 2)) • ∑' p : ℤ × ℤ,
        (∑ r : O ⧸ Ideal.span {c}, P r *
          (Real.fourierChar (inner ℝ
            (ringComplex (GaussianShiftedPartition.representative c r))
            (eisensteinDualFrequency (ringComplex c) (ringComplex_ne_zero hc) p)) : ℂ)) *
          (𝓕 f) (eisensteinDualFrequency (ringComplex c) (ringComplex_ne_zero hc) p) := by
  classical
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  rw [actual_eisenstein_periodic_poisson f c hc P]
  have h := finite_phase_sum f
    (eisensteinLatticeMap (ringComplex c) (ringComplex_ne_zero hc))
    (fun r => ringComplex (GaussianShiftedPartition.representative c r)) P
  rw [eisenstein_inverseJacobian] at h
  exact h

end SchwartzPlanePoisson

namespace SchwartzPlanePoisson
open Eisenstein MeasureTheory
open scoped FourierTransform SchwartzMap RealInnerProductSpace

/-- The trace-normalized dual frequency is independent of the embedding orientation. -/
def paperFrequency (u : ℂ) : ℂ := 2 * starRingEnd ℂ (u / ringComplex traceLambda)

def paperE (z : ℂ) : ℂ := tracePhase (z / ringComplex traceLambda)

theorem inner_paperFrequency (z u : ℂ) :
    inner ℝ z (paperFrequency u) = 2 * (z * (u / ringComplex traceLambda)).re := by
  simp only [paperFrequency, Complex.inner, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, Complex.re_ofNat, Complex.im_ofNat]
  ring

theorem fourierChar_paperFrequency (z u : ℂ) :
    (Real.fourierChar (inner ℝ z (paperFrequency u)) : ℂ) = paperE (z * u) := by
  rw [inner_paperFrequency, Real.fourierChar_apply]
  change Complex.exp _ = Complex.exp _
  congr 1
  have hdiv : z * u / ringComplex traceLambda = z * (u / ringComplex traceLambda) := by ring
  rw [hdiv]
  generalize z * (u / ringComplex traceLambda) = v
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

theorem paperFrequency_coordinates (u : ℂ) :
    paperFrequency u = complexPoint (u.im / (ringComplex omega).im)
      (u.re / (ringComplex omega).im) := by
  have hl : ringComplex traceLambda = complexPoint 0 (2 * (ringComplex omega).im) := by
    apply Complex.ext
    · simp only [traceLambda, map_add, map_mul, map_one, map_ofNat, Complex.add_re,
        Complex.mul_re, Complex.one_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul,
        sub_zero, complexPoint]
      linarith only [complex_omega_coordinates.1]
    · simp only [traceLambda, map_add, map_mul, map_one, map_ofNat, Complex.add_im,
        Complex.mul_im, Complex.one_im, Complex.re_ofNat, Complex.im_ofNat,
        zero_mul, zero_add, add_zero, complexPoint]
  rw [paperFrequency, hl]
  apply Complex.ext <;>
    simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Complex.div_re, Complex.div_im, Complex.normSq_apply, Complex.re_ofNat,
      Complex.im_ofNat, complexPoint] <;>
    field_simp [complex_omega_im_ne_zero] <;> ring

def dualFrequencyEquiv : ℤ × ℤ ≃ O :=
  ({ toFun := fun z => (z.1 + z.2, z.1)
     invFun := fun z => (z.2, z.1 - z.2)
     left_inv := by rintro ⟨k,l⟩; simp
     right_inv := by rintro ⟨k,l⟩; simp } : (ℤ × ℤ) ≃ (ℤ × ℤ)).trans
    Eisenstein.Coordinates.coordinateEquiv.symm

theorem dualFrequencyEquiv_coordinates (p : ℤ × ℤ) :
    ringComplex (dualFrequencyEquiv p) =
      complexPoint ((p.1 : ℝ) / 2 + (p.2 : ℝ))
        ((ringComplex omega).im * (p.1 : ℝ)) := by
  change ringComplex (Eisenstein.Coordinates.eval (p.1 + p.2) p.1) = _
  rw [ringComplex_eval]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.mul_re, Complex.intCast_re,
      Complex.intCast_im, zero_mul, sub_zero, complexPoint]
    push_cast
    rw [complex_omega_coordinates.1]
    ring
  · simp [complexPoint, mul_comm]

theorem dualMap_trans (A B : ℂ ≃L[ℝ] ℂ) (z : ℂ) :
    dualMap (A.trans B) z = dualMap B (dualMap A z) := by
  change (ContinuousLinearMap.adjoint
    (A.symm.toContinuousLinearMap.comp B.symm.toContinuousLinearMap)) z = _
  rw [ContinuousLinearMap.adjoint_comp]
  rfl

theorem dual_basis_apply (w : ℂ) (hw : w.im ≠ 0) (z : ℂ) :
    dualMap (basisEquiv w hw) z =
      complexPoint z.re ((z.im - w.re * z.re) / w.im) := by
  apply ext_inner_left ℝ
  intro v
  rw [dualMap, ContinuousLinearMap.adjoint_inner_right]
  change inner ℝ ((basisEquiv w hw).symm v) z = _
  simp only [basisEquiv_symm_apply, Complex.inner, complexPoint,
    Complex.mul_re, Complex.conj_re, Complex.conj_im]
  field_simp [hw]
  ring

theorem dual_mul_apply (c : ℂ) (hc : c ≠ 0) (z : ℂ) :
    dualMap (complexMulEquiv c hc) z = (starRingEnd ℂ c)⁻¹ * z := by
  apply ext_inner_left ℝ
  intro v
  rw [dualMap, ContinuousLinearMap.adjoint_inner_right]
  change inner ℝ (c⁻¹ * v) z = _
  simp only [Complex.inner, map_mul, map_inv₀]
  congr 1
  ring

theorem eisensteinDualFrequency_eq_paperFrequency (c : ℂ) (hc : c ≠ 0) (p : ℤ × ℤ) :
    eisensteinDualFrequency c hc p = paperFrequency (ringComplex (dualFrequencyEquiv p) / c) := by
  have hb : dualMap (basisEquiv (ringComplex omega) complex_omega_im_ne_zero)
      (complexPoint (p.1 : ℝ) (p.2 : ℝ)) =
      paperFrequency (ringComplex (dualFrequencyEquiv p)) := by
    rw [dual_basis_apply, paperFrequency_coordinates, dualFrequencyEquiv_coordinates]
    apply Complex.ext
    · simp [complexPoint, complex_omega_im_ne_zero]
    · simp only [complexPoint]
      congr 1
      rw [complex_omega_coordinates.1]
      ring
  unfold eisensteinDualFrequency eisensteinLatticeMap scaledBasisEquiv
  rw [dualMap_trans, hb, dual_mul_apply]
  simp only [paperFrequency, map_div₀]
  ring

theorem eisensteinDualFrequency_phase (r c : ℂ) (hc : c ≠ 0) (p : ℤ × ℤ) :
    (Real.fourierChar (inner ℝ r (eisensteinDualFrequency c hc p)) : ℂ) =
      paperE (r * ringComplex (dualFrequencyEquiv p) / c) := by
  rw [eisensteinDualFrequency_eq_paperFrequency, fourierChar_paperFrequency]
  congr 1
  ring

def paperFourier (f : ℂ → ℂ) (u : ℂ) : ℂ :=
  (2 / Real.sqrt 3 : ℝ) • ∫ z : ℂ, paperE (-(z * u)) * f z

theorem paperFourier_eq_standard (f : ℂ → ℂ) (u : ℂ) :
    paperFourier f u = (2 / Real.sqrt 3 : ℝ) • 𝓕 f (paperFrequency u) := by
  unfold paperFourier
  congr 1
  rw [Real.fourier_eq]
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [Circle.smul_def, smul_eq_mul]
  have hp : (Real.fourierChar (-inner ℝ z (paperFrequency u)) : ℂ) =
      paperE (-(z * u)) := by
    simpa only [inner_neg_left, neg_mul] using fourierChar_paperFrequency (-z) u
  rw [hp]

/-- Periodic Schwartz sums transform into the primitive trace-dual Eisenstein lattice. -/
theorem actual_eisenstein_paper_poisson (f : 𝓢(ℂ, ℂ)) (c : O) (hc : c ≠ 0)
    (P : O ⧸ Ideal.span {c} → ℂ) :
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    (∑' z : O, P (Ideal.Quotient.mk (Ideal.span {c}) z) * f (ringComplex z)) =
      (1 / ‖ringComplex c‖ ^ 2 : ℝ) • ∑' h : O,
        (∑ r : O ⧸ Ideal.span {c}, P r *
          paperE (ringComplex (GaussianShiftedPartition.representative c r) *
            ringComplex h / ringComplex c)) *
          paperFourier f (ringComplex h / ringComplex c) := by
  classical
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let A : O → ℂ := fun h => ∑ r : O ⧸ Ideal.span {c}, P r *
    paperE (ringComplex (GaussianShiftedPartition.representative c r) *
      ringComplex h / ringComplex c)
  have ht : (∑' h : O, A h * paperFourier f (ringComplex h / ringComplex c)) =
      (2 / Real.sqrt 3 : ℝ) • ∑' p : ℤ × ℤ,
        A (dualFrequencyEquiv p) *
          (𝓕 f) (eisensteinDualFrequency (ringComplex c) (ringComplex_ne_zero hc) p) := by
    calc
      _ = ∑' p : ℤ × ℤ, A (dualFrequencyEquiv p) *
          paperFourier f (ringComplex (dualFrequencyEquiv p) / ringComplex c) :=
        (dualFrequencyEquiv.tsum_eq _).symm
      _ = ∑' p : ℤ × ℤ, (2 / Real.sqrt 3 : ℝ) •
          (A (dualFrequencyEquiv p) *
            (𝓕 f) (eisensteinDualFrequency (ringComplex c) (ringComplex_ne_zero hc) p)) := by
        apply tsum_congr
        intro p
        rw [paperFourier_eq_standard, ← eisensteinDualFrequency_eq_paperFrequency _ (ringComplex_ne_zero hc)]
        change A (dualFrequencyEquiv p) *
          ((2 / Real.sqrt 3 : ℝ) • (𝓕 f) (eisensteinDualFrequency (ringComplex c) (ringComplex_ne_zero hc) p)) = _
        simp only [Algebra.smul_def]
        ring
      _ = _ := tsum_const_smul'' _
    rfl
  have hp := actual_eisenstein_periodic_fourier f c hc P
  simp_rw [eisensteinDualFrequency_phase] at hp
  change _ = (1 / ‖ringComplex c‖ ^ 2 : ℝ) •
    ∑' h : O, A h * paperFourier f (ringComplex h / ringComplex c)
  rw [ht, smul_smul]
  convert hp using 1
  congr 1
  ring

end SchwartzPlanePoisson

namespace SchwartzPlanePoisson
open Eisenstein MeasureTheory
open scoped FourierTransform SchwartzMap RealInnerProductSpace ContDiff

def radialTest (W : 𝓢(ℝ, ℂ)) : 𝓢(ℂ, ℂ) :=
  SchwartzMap.compCLM ℂ (Function.hasTemperateGrowth_norm_sq ℂ)
    ⟨1, 1, fun z => by
      simp only [pow_one, one_mul, norm_pow, Real.norm_of_nonneg (norm_nonneg z)]
      nlinarith [sq_nonneg (‖z‖ - 1)]⟩ W

@[simp] theorem radialTest_apply (W : 𝓢(ℝ, ℂ)) (z : ℂ) :
    radialTest W z = W (‖z‖ ^ 2) := rfl

theorem paperFourier_comp_mul (f : ℂ → ℂ) (a : ℂ) (ha : a ≠ 0) (u : ℂ) :
    paperFourier (fun z => f (a * z)) u =
      (1 / ‖a‖ ^ 2 : ℝ) • paperFourier f (u / a) := by
  have hd : dualMap (complexMulEquiv a ha) (paperFrequency u) =
      paperFrequency (u / a) := by
    rw [dual_mul_apply]
    unfold paperFrequency
    simp only [map_div₀]
    ring
  have hj : inverseJacobian (complexMulEquiv a ha) = 1 / ‖a‖ ^ 2 := by
    rw [inverseJacobian, complexMulEquiv_det, abs_inv,
      abs_of_nonneg (Complex.normSq_nonneg a), Complex.sq_norm]
    ring
  rw [paperFourier_eq_standard, paperFourier_eq_standard]
  have hF := fourier_comp_linearEquiv (complexMulEquiv a ha) f (paperFrequency u)
  simp only [Function.comp_def, complexMulEquiv_apply] at hF
  rw [hF, hd, hj, smul_smul, smul_smul]
  congr 1
  ring

def paperRadialFourier (W : ℝ → ℂ) (t : ℝ) : ℂ :=
  paperFourier (fun z => W (‖z‖ ^ 2)) (Real.sqrt t : ℂ)

theorem paperFourier_radial (W : ℝ → ℂ) (u : ℂ) :
    paperFourier (fun z => W (‖z‖ ^ 2)) u =
      paperRadialFourier W (‖u‖ ^ 2) := by
  unfold paperRadialFourier
  rw [Real.sqrt_sq (norm_nonneg u)]
  by_cases hu : u = 0
  · simp [hu]
  have hn : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  have hnC : (‖u‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn
  let a : ℂ := u / (‖u‖ : ℂ)
  have ha : a ≠ 0 := div_ne_zero hu hnC
  have hna : ‖a‖ = 1 := by
    simp [a, Complex.norm_real, hn]
  have hq : u / a = (‖u‖ : ℂ) := by
    dsimp [a]
    field_simp
  have hfun : (fun z : ℂ => W (‖a * z‖ ^ 2)) = fun z : ℂ => W (‖z‖ ^ 2) := by
    funext z
    rw [norm_mul, hna, one_mul]
  have hF := paperFourier_comp_mul (fun z => W (‖z‖ ^ 2)) a ha u
  rw [hfun, hna, hq] at hF
  simpa using hF

theorem inverseSqrt_ne_zero (K : ℝ) (hK : 0 < K) :
    (Real.sqrt K : ℂ)⁻¹ ≠ 0 :=
  inv_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr hK)))

theorem inverseSqrt_norm_sq (K : ℝ) (hK : 0 < K) :
    ‖(Real.sqrt K : ℂ)⁻¹‖ ^ 2 = 1 / K := by
  rw [norm_inv, inv_pow]
  simp only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg K), Real.sq_sqrt hK.le, one_div]

theorem paperFourier_radial_scaled (W : ℝ → ℂ) (K : ℝ) (hK : 0 < K) (u : ℂ) :
    paperFourier (fun z => W (‖z‖ ^ 2 / K)) u =
      K • paperRadialFourier W (K * ‖u‖ ^ 2) := by
  let a : ℂ := (Real.sqrt K : ℂ)⁻¹
  have ha : a ≠ 0 := inverseSqrt_ne_zero K hK
  have hna : ‖a‖ ^ 2 = 1 / K := inverseSqrt_norm_sq K hK
  have hfun : (fun z : ℂ => W (‖a * z‖ ^ 2)) =
      fun z : ℂ => W (‖z‖ ^ 2 / K) := by
    funext z
    rw [norm_mul, mul_pow, hna]
    congr 1
    ring
  have hnorm : ‖u / a‖ ^ 2 = K * ‖u‖ ^ 2 := by
    rw [norm_div, div_pow, hna]
    field_simp
  have hF := paperFourier_comp_mul (fun z => W (‖z‖ ^ 2)) a ha u
  rw [hfun, hna, one_div_one_div, paperFourier_radial, hnorm] at hF
  exact hF

def scaledRadialTest (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) : 𝓢(ℂ, ℂ) :=
  affinePullback (radialTest W)
    (complexMulEquiv ((Real.sqrt K : ℂ)⁻¹) (inverseSqrt_ne_zero K hK)) 0

@[simp] theorem scaledRadialTest_apply (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) (z : ℂ) :
    scaledRadialTest W K hK z = W (‖z‖ ^ 2 / K) := by
  simp only [scaledRadialTest, affinePullback_apply, complexMulEquiv_apply,
    add_zero, radialTest_apply, norm_mul, mul_pow, inverseSqrt_norm_sq K hK]
  congr 1
  ring

theorem paperFourier_scaledRadialTest (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) (u : ℂ) :
    paperFourier (scaledRadialTest W K hK) u =
      K • paperRadialFourier W (K * ‖u‖ ^ 2) := by
  change paperFourier (fun z => scaledRadialTest W K hK z) u = _
  simp only [scaledRadialTest_apply]
  exact paperFourier_radial_scaled W K hK u

theorem actual_radial_paper_poisson (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K)
    (c : O) (hc : c ≠ 0) (P : O ⧸ Ideal.span {c} → ℂ) :
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    (∑' z : O, P (Ideal.Quotient.mk (Ideal.span {c}) z) * W (‖ringComplex z‖ ^ 2 / K)) =
      (K / ‖ringComplex c‖ ^ 2 : ℝ) • ∑' h : O,
        (∑ r : O ⧸ Ideal.span {c}, P r *
          paperE (ringComplex (GaussianShiftedPartition.representative c r) * ringComplex h / ringComplex c)) *
          paperRadialFourier W (K * ‖ringComplex h‖ ^ 2 / ‖ringComplex c‖ ^ 2) := by
  classical
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let A : O → ℂ := fun h => ∑ r : O ⧸ Ideal.span {c}, P r *
    paperE (ringComplex (GaussianShiftedPartition.representative c r) * ringComplex h / ringComplex c)
  have ht : (∑' h : O, A h *
      paperFourier (scaledRadialTest W K hK) (ringComplex h / ringComplex c)) =
      K • ∑' h : O, A h *
        paperRadialFourier W (K * ‖ringComplex h‖ ^ 2 / ‖ringComplex c‖ ^ 2) := by
    calc
      _ = ∑' h : O, K • (A h *
          paperRadialFourier W (K * ‖ringComplex h‖ ^ 2 / ‖ringComplex c‖ ^ 2)) := by
        apply tsum_congr
        intro h
        rw [paperFourier_scaledRadialTest, norm_div, div_pow]
        have hr : K * (‖ringComplex h‖ ^ 2 / ‖ringComplex c‖ ^ 2) =
            K * ‖ringComplex h‖ ^ 2 / ‖ringComplex c‖ ^ 2 := by ring
        rw [hr]
        simp only [Algebra.smul_def]
        ring
      _ = _ := tsum_const_smul'' _
  have hp := actual_eisenstein_paper_poisson (scaledRadialTest W K hK) c hc P
  change (∑' z : O, P (Ideal.Quotient.mk (Ideal.span {c}) z) *
    scaledRadialTest W K hK (ringComplex z)) =
    (1 / ‖ringComplex c‖ ^ 2 : ℝ) • ∑' h : O, A h *
      paperFourier (scaledRadialTest W K hK) (ringComplex h / ringComplex c) at hp
  rw [ht, smul_smul] at hp
  simpa only [scaledRadialTest_apply, one_div_mul_eq_div] using hp

theorem actual_compact_radial_paper_poisson (W : ℝ → ℂ)
    (hWc : HasCompactSupport W) (hWs : ContDiff ℝ ∞ W) (K : ℝ) (hK : 0 < K)
    (c : O) (hc : c ≠ 0) (P : O ⧸ Ideal.span {c} → ℂ) :
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    (∑' z : O, P (Ideal.Quotient.mk (Ideal.span {c}) z) * W (‖ringComplex z‖ ^ 2 / K)) =
      (K / ‖ringComplex c‖ ^ 2 : ℝ) • ∑' h : O,
        (∑ r : O ⧸ Ideal.span {c}, P r *
          paperE (ringComplex (GaussianShiftedPartition.representative c r) * ringComplex h / ringComplex c)) *
          paperRadialFourier W (K * ‖ringComplex h‖ ^ 2 / ‖ringComplex c‖ ^ 2) := by
  exact actual_radial_paper_poisson (hWc.toSchwartzMap hWs) K hK c hc P

end SchwartzPlanePoisson

namespace SchwartzPlanePoisson
open Eisenstein MulChar AddChar

/-- The finite transform of a primitive multiplicative row is its inverse row times one Gauss factor. -/
theorem finite_crt_gauss_transform {ι R : Type*} [Fintype ι] [DecidableEq ι]
    (F : ι → Type*) [∀ i, Field (F i)] [∀ i, Fintype (F i)]
    [CommRing R] [Fintype R] (e : R ≃+* ∀ i, F i)
    (χ : ∀ i, MulChar (F i) ℂ) (hχ : ∀ i, χ i ≠ 1)
    (ψ : AddChar R ℂ) (h : R) :
    (∑ x : R, (∏ i, χ i (e x i)) * ψ (h * x)) =
      (∏ i, (χ i)⁻¹ (e h i)) * ∑ x : R, (∏ i, χ i (e x i)) * ψ x := by
  let ψ₀ := ψ.compAddMonoidHom e.symm.toAddMonoidHom
  have hl (i : ι) :
      ProductGauss.localChar F ((ψ.mulShift h).compAddMonoidHom e.symm.toAddMonoidHom) i =
        (ProductGauss.localChar F ψ₀ i).mulShift (e h i) := by
    ext x
    change ψ (h * e.symm (Pi.single i x)) = ψ (e.symm (Pi.single i (e h i * x)))
    congr 1
    apply e.injective
    simp only [map_mul, e.apply_symm_apply]
    ext k
    by_cases hik : i = k
    · subst k; simp
    · simp [Pi.single_eq_of_ne (Ne.symm hik)]
  change (∑ x : R, (∏ i, χ i (e x i)) * (ψ.mulShift h) x) = _
  rw [ProductGauss.factorization_equiv F e χ (ψ.mulShift h),
    ProductGauss.factorization_equiv F e χ ψ]
  simp_rw [hl, finiteGauss_mulShift_all _ _ (hχ _)]
  exact Finset.prod_mul_distrib

/-- Squared Gauss mass is exactly the residue-ring size. -/
theorem finite_crt_gauss_norm_sq {ι R : Type*} [Fintype ι] [DecidableEq ι]
    (F : ι → Type*) [∀ i, Field (F i)] [∀ i, Fintype (F i)]
    [CommRing R] [Fintype R] (e : R ≃+* ∀ i, F i)
    (χ : ∀ i, MulChar (F i) ℂ) (hχ : ∀ i, χ i ≠ 1)
    (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) :
    ‖∑ x : R, (∏ i, χ i (e x i)) * ψ x‖ ^ 2 = (Fintype.card R : ℝ) := by
  have hp := ProductGauss.primitive_comp_ringEquiv e.symm ψ hψ
  rw [ProductGauss.factorization_equiv F e χ ψ, norm_prod, ← Finset.prod_pow]
  have hn (i : ι) :
      ‖gaussSum (χ i) (ProductGauss.localChar F
        (ψ.compAddMonoidHom e.symm.toAddMonoidHom) i)‖ ^ 2 = (Fintype.card (F i) : ℝ) := by
    rw [← Complex.normSq_eq_norm_sq,
      ArithmeticEffectivityTheory.normSq_gaussSum_eq_card (hχ i)
        (ProductGauss.localChar_primitive F _ hp i)]
  simp_rw [hn]
  rw [Fintype.card_congr e.toEquiv, Fintype.card_pi, Nat.cast_prod]

end SchwartzPlanePoisson

namespace SchwartzPlanePoisson
open Eisenstein MulChar AddChar
open scoped SchwartzMap ContDiff

lemma residueTraceQuotientChar_frequency (c : O) (hc : c ≠ 0)
    (h : O) (r : O ⧸ Ideal.span {c}) :
    residueTraceQuotientChar 1 c hc (Ideal.Quotient.mk (Ideal.span {c}) h * r) =
      paperE (ringComplex (GaussianShiftedPartition.representative c r) * ringComplex h / ringComplex c) := by
  conv_lhs => rw [← GaussianShiftedPartition.representative_spec c r, ← map_mul]
  rw [residueTraceQuotientChar_phase, one_mul]
  simp only [paperE, map_mul]
  congr 1
  ring

/-- The radial second Poisson transformation uses the same primitive trace character as cubic reflection. -/
theorem actual_radial_poisson_trace (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y)
    (c : O) (hc : c ≠ 0) (P : O ⧸ Ideal.span {c} → ℂ) :
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    (∑' z : O, P (Ideal.Quotient.mk (Ideal.span {c}) z) * W (‖ringComplex z‖ ^ 2 / Y)) =
      (Y / ‖ringComplex c‖ ^ 2 : ℝ) • ∑' h : O,
        (∑ r : O ⧸ Ideal.span {c}, P r *
          residueTraceQuotientChar 1 c hc (Ideal.Quotient.mk (Ideal.span {c}) h * r)) *
          paperRadialFourier W (Y * ‖ringComplex h‖ ^ 2 / ‖ringComplex c‖ ^ 2) := by
  classical
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  simpa only [residueTraceQuotientChar_frequency] using actual_radial_paper_poisson W Y hY c hc P

/-- A nontrivial character in each prime coordinate transforms into its inverse row with exact Gauss mass. -/
theorem actual_radial_crt_character_poisson {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : ι → Type*) [∀ i, Field (F i)] [∀ i, Fintype (F i)]
    (c : O) (hc : c ≠ 0) (e : (O ⧸ Ideal.span {c}) ≃+* ∀ i, F i)
    (χ : ∀ i, MulChar (F i) ℂ) (hχ : ∀ i, χ i ≠ 1) :
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    ∃ G : ℂ, ‖G‖ ^ 2 = (Fintype.card (O ⧸ Ideal.span {c}) : ℝ) ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (Y : ℝ), 0 < Y →
        (∑' z : O, (∏ i, χ i (e (Ideal.Quotient.mk (Ideal.span {c}) z) i)) *
          W (‖ringComplex z‖ ^ 2 / Y)) =
        (Y / ‖ringComplex c‖ ^ 2 : ℝ) • (G * ∑' h : O,
          (∏ i, (χ i)⁻¹ (e (Ideal.Quotient.mk (Ideal.span {c}) h) i)) *
            paperRadialFourier W (Y * ‖ringComplex h‖ ^ 2 / ‖ringComplex c‖ ^ 2)) := by
  classical
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let ψ := residueTraceQuotientChar 1 c hc
  let P : O ⧸ Ideal.span {c} → ℂ := fun x => ∏ i, χ i (e x i)
  refine ⟨∑ x, P x * ψ x,
    finite_crt_gauss_norm_sq F e χ hχ ψ (residueTraceQuotientChar_primitive c hc), ?_⟩
  intro W Y hY
  rw [actual_radial_poisson_trace W Y hY c hc P]
  congr 1
  rw [← tsum_mul_left]
  apply tsum_congr
  intro h
  rw [finite_crt_gauss_transform F e χ hχ ψ]
  ring

end SchwartzPlanePoisson

namespace SchwartzPlanePoisson
open Eisenstein MulChar AddChar
open scoped SchwartzMap ContDiff

/-- The analytic normalization leaves a unit Gauss phase and the square-root conductor factor. -/
theorem actual_radial_crt_character_poisson_normalized {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : ι → Type*) [∀ i, Field (F i)] [∀ i, Fintype (F i)]
    (c : O) (hc : c ≠ 0) (e : (O ⧸ Ideal.span {c}) ≃+* ∀ i, F i)
    (χ : ∀ i, MulChar (F i) ℂ) (hχ : ∀ i, χ i ≠ 1) :
    ∃ β : ℂ, ‖β‖ = 1 ∧ ∀ (W : 𝓢(ℝ, ℂ)) (Y : ℝ), 0 < Y →
      (∑' z : O, (∏ i, χ i (e (Ideal.Quotient.mk (Ideal.span {c}) z) i)) *
        W (‖ringComplex z‖ ^ 2 / Y)) =
      ((Y : ℂ) * β / (‖ringComplex c‖ : ℂ)) * ∑' h : O,
        (∏ i, (χ i)⁻¹ (e (Ideal.Quotient.mk (Ideal.span {c}) h) i)) *
          paperRadialFourier W (Y * ‖ringComplex h‖ ^ 2 / ‖ringComplex c‖ ^ 2) := by
  classical
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  obtain ⟨G, hG, hP⟩ := actual_radial_crt_character_poisson F c hc e χ hχ
  have hcard : (Fintype.card (O ⧸ Ideal.span {c}) : ℝ) = ‖ringComplex c‖ ^ 2 := by
    simpa only [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
      using (ringComplex_norm_sq_eq_absNorm_span c).symm
  have hnorm : ‖G‖ = ‖ringComplex c‖ :=
    (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (hG.trans hcard)
  have hn : ‖ringComplex c‖ ≠ 0 := norm_ne_zero_iff.mpr (ringComplex_ne_zero hc)
  refine ⟨G / (‖ringComplex c‖ : ℂ), ?_, ?_⟩
  · rw [norm_div, hnorm, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _), div_self hn]
  · intro W Y hY
    rw [hP W Y hY]
    change ((Y / ‖ringComplex c‖ ^ 2 : ℝ) : ℂ) * _ = _
    push_cast
    ring

lemma span_finset_prime_product {ι : Type*} (p : ι → O) (s : Finset ι) :
    Ideal.span {∏ i ∈ s, p i} = ∏ i ∈ s, Ideal.span {p i} := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi, ← Ideal.span_singleton_mul_span_singleton, ih]

/-- Second Poisson reflection for a finite family of actual prime residue characters. -/
theorem prime_row_radial_poisson {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ) (hχ : ∀ i, χ i ≠ 1) :
    ∃ β : ℂ, ‖β‖ = 1 ∧ ∀ (W : 𝓢(ℝ, ℂ)) (Y : ℝ), 0 < Y →
      (∑' z : O, primeCuspRowCharacter p χ z * W (‖ringComplex z‖ ^ 2 / Y)) =
      ((Y : ℂ) * β / (‖ringComplex (∏ i, p i)‖ : ℂ)) * ∑' h : O,
        primeCuspRowCharacter p (fun i => (χ i)⁻¹) h *
          paperRadialFourier W (Y * ‖ringComplex h‖ ^ 2 / ‖ringComplex (∏ i, p i)‖ ^ 2) := by
  classical
  let P : ι → Ideal O := fun i => Ideal.span {p i}
  let c := ∏ i, p i
  have hc : c ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  have hspan : Ideal.span {c} = ∏ i, P i := span_finset_prime_product p Finset.univ
  let e : (O ⧸ Ideal.span {c}) ≃+* ∀ i, O ⧸ P i :=
    (Ideal.quotEquivOfEq hspan).trans (Eisenstein.primeCRT P hinj)
  have he (z : O) (i : ι) :
      e (Ideal.Quotient.mk (Ideal.span {c}) z) i = Ideal.Quotient.mk (P i) z := by
    simp only [e, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk, Eisenstein.primeCRT]
    rfl
  obtain ⟨β, hβ, h⟩ := actual_radial_crt_character_poisson_normalized
    (fun i => O ⧸ P i) c hc e χ hχ
  refine ⟨β, hβ, ?_⟩
  intro W Y hY
  change (∑' z : O, (∏ i, χ i (Ideal.Quotient.mk (P i) z)) * W (‖ringComplex z‖ ^ 2 / Y)) =
    ((Y : ℂ) * β / (‖ringComplex c‖ : ℂ)) * ∑' h : O,
      (∏ i, (χ i)⁻¹ (Ideal.Quotient.mk (P i) h)) *
        paperRadialFourier W (Y * ‖ringComplex h‖ ^ 2 / ‖ringComplex c‖ ^ 2)
  simpa only [he] using h W Y hY

end SchwartzPlanePoisson

namespace SchwartzPlanePoisson
open Eisenstein MeasureTheory Set
open scoped FourierTransform SchwartzMap RealInnerProductSpace ContDiff

lemma paperFrequency_norm_sq (u : ℂ) :
    ‖paperFrequency u‖ ^ 2 = (4 / 3 : ℝ) * ‖u‖ ^ 2 := by
  rw [paperFrequency_coordinates]
  simp only [Complex.sq_norm, Complex.normSq_apply, ← pow_two]
  change (u.im / (ringComplex omega).im) ^ 2 + (u.re / (ringComplex omega).im) ^ 2 =
    (4 / 3 : ℝ) * (u.re ^ 2 + u.im ^ 2)
  rw [div_pow, div_pow, complex_omega_coordinates.2]
  ring

def radialTestCLM : 𝓢(ℝ, ℂ) →L[ℝ] 𝓢(ℂ, ℂ) :=
  SchwartzMap.compCLM ℝ (Function.hasTemperateGrowth_norm_sq ℂ)
    ⟨1, 1, fun z => by
      simp only [pow_one, one_mul, norm_pow, Real.norm_of_nonneg (norm_nonneg z)]
      nlinarith [sq_nonneg (‖z‖ - 1)]⟩

@[simp] theorem radialTestCLM_apply (W : 𝓢(ℝ, ℂ)) : radialTestCLM W = radialTest W := by
  ext z
  rfl

def radialFourierCLM : 𝓢(ℝ, ℂ) →L[ℝ] 𝓢(ℂ, ℂ) :=
  (FourierTransform.fourierCLM ℝ 𝓢(ℂ, ℂ)).comp radialTestCLM

@[simp] theorem radialFourierCLM_apply (W : 𝓢(ℝ, ℂ)) :
    radialFourierCLM W = 𝓕 (radialTest W) := by
  simp [radialFourierCLM]

theorem paperRadialFourier_eq_plane (W : 𝓢(ℝ, ℂ)) (t : ℝ) :
    paperRadialFourier W t =
      (2 / Real.sqrt 3 : ℝ) • radialFourierCLM W (paperFrequency (Real.sqrt t : ℂ)) := by
  rw [paperRadialFourier, paperFourier_eq_standard, radialFourierCLM_apply]
  rfl

theorem paperFrequency_sqrt_norm_sq (t : ℝ) (ht : 0 ≤ t) :
    ‖paperFrequency (Real.sqrt t : ℂ)‖ ^ 2 = (4 / 3 : ℝ) * t := by
  rw [paperFrequency_norm_sq]
  simp only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg t), Real.sq_sqrt ht]

theorem paperRadialFourier_weighted_bound (W : 𝓢(ℝ, ℂ)) (A : ℕ)
    (t : ℝ) (ht : 0 ≤ t) :
    (1 + t) ^ A * ‖paperRadialFourier W t‖ ≤
      (2 / Real.sqrt 3 : ℝ) * 2 ^ (2 * A) *
        (Finset.Iic (2 * A, 0)).sup (schwartzSeminormFamily ℝ ℂ ℂ)
          (radialFourierCLM W) := by
  let ξ : ℂ := paperFrequency (Real.sqrt t : ℂ)
  have hn : ‖ξ‖ ^ 2 = (4 / 3 : ℝ) * t := paperFrequency_sqrt_norm_sq t ht
  have hscale : 0 ≤ (2 / Real.sqrt 3 : ℝ) := by positivity
  have hpow : (1 + t) ^ A ≤ (1 + ‖ξ‖) ^ (2 * A) := by
    have hbase : 1 + t ≤ (1 + ‖ξ‖) ^ 2 := by
      nlinarith [norm_nonneg ξ]
    calc
      (1 + t) ^ A ≤ ((1 + ‖ξ‖) ^ 2) ^ A := pow_le_pow_left₀ (by positivity) hbase A
      _ = _ := by rw [← pow_mul]
  have hb := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
    (m := (2 * A, 0)) (k := 2 * A) (n := 0) le_rfl le_rfl (radialFourierCLM W) ξ
  simp only [norm_iteratedFDeriv_zero] at hb
  have hsf : (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2) =
      schwartzSeminormFamily ℝ ℂ ℂ := by
    funext m
    rcases m with ⟨k, n⟩
    rfl
  rw [hsf] at hb
  rw [paperRadialFourier_eq_plane, norm_smul, Real.norm_eq_abs, abs_of_nonneg hscale]
  change (1 + t) ^ A * ((2 / Real.sqrt 3) * ‖radialFourierCLM W ξ‖) ≤ _
  calc
    _ = (2 / Real.sqrt 3) * ((1 + t) ^ A * ‖radialFourierCLM W ξ‖) := by ring
    _ ≤ (2 / Real.sqrt 3) * ((1 + ‖ξ‖) ^ (2 * A) * ‖radialFourierCLM W ξ‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hpow (norm_nonneg _)) hscale
    _ ≤ _ := by
      simpa only [mul_assoc, add_zero] using mul_le_mul_of_nonneg_left hb hscale

theorem schwartzCLM_finite_seminorm_control
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : 𝓢(ℝ, ℂ) →L[ℝ] 𝓢(E, ℂ)) (S : Finset (ℕ × ℕ)) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧ ∀ W : 𝓢(ℝ, ℂ),
      S.sup (schwartzSeminormFamily ℝ E ℂ) (T W) ≤
        C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  let q : Seminorm ℝ 𝓢(ℝ, ℂ) :=
    (S.sup (schwartzSeminormFamily ℝ E ℂ)).comp T.toLinearMap
  have hq : Continuous q :=
    (((schwartz_withSeminorms ℝ E ℂ).finset_sups).continuous_seminorm S).comp T.continuous
  obtain ⟨s, C, hC, hbound⟩ :=
    Seminorm.bound_of_continuous (schwartz_withSeminorms ℝ ℝ ℂ) q hq
  refine ⟨s, C, ?_, ?_⟩
  · exact_mod_cast (pos_iff_ne_zero.mpr hC : 0 < C)
  · intro W
    exact Seminorm.le_def.mp hbound W

theorem paperRadialFourier_source_weighted_bound (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (t : ℝ), 0 ≤ t →
        (1 + t) ^ A * ‖paperRadialFourier W t‖ ≤
          C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  obtain ⟨s, C, hC, hbound⟩ :=
    schwartzCLM_finite_seminorm_control radialFourierCLM (Finset.Iic (2 * A, 0))
  refine ⟨s, (2 / Real.sqrt 3) * 2 ^ (2 * A) * C, by positivity, ?_⟩
  intro W t ht
  apply (paperRadialFourier_weighted_bound W A t ht).trans
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left (hbound W)
      (show 0 ≤ (2 / Real.sqrt 3) * 2 ^ (2 * A) by positivity)

theorem paperRadialFourier_source_decay (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (t : ℝ), 0 ≤ t →
        ‖paperRadialFourier W t‖ ≤
          (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) / (1 + t) ^ A := by
  obtain ⟨s, C, hC, hbound⟩ := paperRadialFourier_source_weighted_bound A
  refine ⟨s, C, hC, ?_⟩
  intro W t ht
  apply (le_div_iff₀ (by positivity : 0 < (1 + t) ^ A)).mpr
  simpa only [mul_comm] using hbound W t ht

theorem inverse_square_le_cauchy_product (a b q : ℝ) (hq : 0 ≤ q)
    (hQ : (a ^ 2 + b ^ 2) / 2 ≤ q) :
    ((1 + q) ^ 2)⁻¹ ≤
      4 * ((1 + a ^ 2)⁻¹ * (1 + b ^ 2)⁻¹) := by
  have hsum : 1 + a ^ 2 + b ^ 2 ≤ 2 * (1 + q) := by linarith
  have hsquare : (1 + a ^ 2 + b ^ 2) ^ 2 ≤ (2 * (1 + q)) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity) hsum
  have hden : (1 + a ^ 2) * (1 + b ^ 2) ≤ 4 * (1 + q) ^ 2 := by
    nlinarith [sq_nonneg (a ^ 2), sq_nonneg (b ^ 2),
      mul_nonneg (sq_nonneg a) (sq_nonneg b)]
  calc
    _ = 1 / (1 + q) ^ 2 := by simp only [one_div]
    _ ≤ 4 / ((1 + a ^ 2) * (1 + b ^ 2)) :=
      (div_le_div_iff₀ (by positivity) (by positivity)).mpr (by simpa using hden)
    _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring

theorem eisenstein_cauchy_summable :
    Summable (fun h : O => ((1 + ‖ringComplex h‖ ^ 2) ^ 2)⁻¹) := by
  apply (Eisenstein.Coordinates.coordinateEquiv.symm.summable_iff).mp
  change Summable (fun p : ℤ × ℤ =>
    ((1 + ‖ringComplex (Eisenstein.Coordinates.coordinateEquiv.symm p)‖ ^ 2) ^ 2)⁻¹)
  apply Summable.of_nonneg_of_le (fun _ => inv_nonneg.mpr (sq_nonneg _)) _
    (summable_int_cauchy_product.mul_left 4)
  intro p
  apply inverse_square_le_cauchy_product (p.1 : ℝ) (p.2 : ℝ)
    (‖ringComplex (Eisenstein.Coordinates.coordinateEquiv.symm p)‖ ^ 2) (sq_nonneg _)
  change ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) / 2 ≤
    ‖ringComplex (Eisenstein.Coordinates.eval p.1 p.2)‖ ^ 2
  rw [Eisenstein.Coordinates.complex_norm_eval_sq]
  push_cast
  nlinarith [sq_nonneg ((p.1 : ℝ) - (p.2 : ℝ))]

def eisensteinCauchyMass : ℝ :=
  ∑' h : O, ((1 + ‖ringComplex h‖ ^ 2) ^ 2)⁻¹

theorem eisensteinCauchyMass_nonneg : 0 ≤ eisensteinCauchyMass :=
  tsum_nonneg (fun _ => by positivity)

theorem eisensteinCauchyMass_subtype (S : Set O) :
    (∑' h : S, ((1 + ‖ringComplex h.val‖ ^ 2) ^ 2)⁻¹) ≤ eisensteinCauchyMass := by
  exact (eisenstein_cauchy_summable.subtype S).tsum_le_tsum_of_inj
    Subtype.val Subtype.val_injective (fun _ _ => by positivity) (fun _ => le_rfl)
    eisenstein_cauchy_summable

theorem polynomial_tail_majorant (A : ℕ) (K T q B f : ℝ)
    (hK : 0 < K) (hT : 0 ≤ T) (hq : 0 ≤ q) (hf : 0 ≤ f)
    (htail : T ≤ K * q) (hbound : (1 + K * q) ^ (A + 2) * f ≤ B) :
    f ≤ (B / ((min 1 K) ^ 2 * (1 + T) ^ A)) * ((1 + q) ^ 2)⁻¹ := by
  have hm : 0 < min 1 K := lt_min (by norm_num) hK
  have hm1 : min 1 K ≤ 1 := min_le_left _ _
  have hmK : min 1 K ≤ K := min_le_right _ _
  have hbase : min 1 K * (1 + q) ≤ 1 + K * q := by
    nlinarith [mul_le_mul_of_nonneg_right hmK hq]
  have htwo : (min 1 K) ^ 2 * (1 + q) ^ 2 ≤ (1 + K * q) ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hbase _
  have hpow : (1 + T) ^ A ≤ (1 + K * q) ^ A :=
    pow_le_pow_left₀ (by positivity) (by linarith) _
  have hden : ((min 1 K) ^ 2 * (1 + T) ^ A) * (1 + q) ^ 2 ≤
      (1 + K * q) ^ (A + 2) := by
    have hh := mul_le_mul hpow htwo (by positivity) (by positivity)
    rw [pow_add]
    nlinarith
  have hprod : f * (((min 1 K) ^ 2 * (1 + T) ^ A) * (1 + q) ^ 2) ≤ B := by
    calc
      _ = (((min 1 K) ^ 2 * (1 + T) ^ A) * (1 + q) ^ 2) * f := mul_comm _ _
      _ ≤ (1 + K * q) ^ (A + 2) * f := mul_le_mul_of_nonneg_right hden hf
      _ ≤ B := hbound
  have hraw := (le_div_iff₀ (show 0 < ((min 1 K) ^ 2 * (1 + T) ^ A) * (1 + q) ^ 2
      by positivity)).mpr hprod
  simpa only [div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc] using hraw

theorem paperRadialFourier_lattice_summable_norm (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    Summable (fun h : O => ‖paperRadialFourier W (K * ‖ringComplex h‖ ^ 2)‖) := by
  obtain ⟨s, C, hC, hb⟩ := paperRadialFourier_source_weighted_bound 2
  let B := C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  let D := (min 1 K) ^ 2 * (1 + (0 : ℝ)) ^ (0 : ℕ)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    (eisenstein_cauchy_summable.mul_left (B / D))
  intro h
  exact polynomial_tail_majorant 0 K 0 _ B _ hK (by norm_num)
    (sq_nonneg _) (norm_nonneg _) (by positivity) (hb W _ (by positivity))


theorem scaled_cauchy_antitone (b : ℝ) :
    AntitoneOn (fun x : ℝ => (1 + (b * x) ^ 2)⁻¹) (Ici 0) := by
  intro x hx y hy hxy
  change 0 ≤ x at hx
  change 0 ≤ y at hy
  apply inv_anti₀ (by positivity)
  nlinarith [sq_nonneg b, sq_nonneg (y - x),
    mul_nonneg (sq_nonneg b) (show 0 ≤ y ^ 2 - x ^ 2 by nlinarith)]

theorem scaled_cauchy_nat_bound (b : ℝ) (hb : 0 < b) :
    (∑' n : ℕ, (1 + (b * (n : ℝ)) ^ 2)⁻¹) ≤ 1 + Real.pi / (2 * b) := by
  have hi := (integrable_inv_one_add_sq.comp_mul_left' hb.ne').integrableOn (s := Ioi 0)
  have ht := (scaled_cauchy_antitone b).tsum_le_integral hi
    (fun t ht => by positivity)
  have he : (∫ x : ℝ in Ioi 0, (1 + (b * x) ^ 2)⁻¹) = Real.pi / (2 * b) := by
    rw [integral_comp_mul_left_Ioi (fun x : ℝ => (1 + x ^ 2)⁻¹) 0 hb]
    simp only [mul_zero, integral_Ioi_inv_one_add_sq, Real.arctan_zero, sub_zero,
      smul_eq_mul]
    ring
  simpa [he] using ht

theorem summable_scaled_cauchy_nat (b : ℝ) (hb : 0 < b) :
    Summable (fun n : ℕ => (1 + (b * (n : ℝ)) ^ 2)⁻¹) := by
  exact (scaled_cauchy_antitone b).summable_of_integrableOn_Ioi_zero
    (integrable_inv_one_add_sq.comp_mul_left' hb.ne').integrableOn (fun _ _ => by positivity)

theorem summable_scaled_cauchy_int (b : ℝ) (hb : 0 < b) :
    Summable (fun n : ℤ => (1 + (b * (n : ℝ)) ^ 2)⁻¹) := by
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · simpa using summable_scaled_cauchy_nat b hb
  · simpa [mul_neg] using summable_scaled_cauchy_nat b hb

theorem scaled_cauchy_int_bound (b : ℝ) (hb : 0 < b) :
    (∑' n : ℤ, (1 + (b * (n : ℝ)) ^ 2)⁻¹) ≤ 1 + Real.pi / b := by
  have hs := summable_scaled_cauchy_nat b hb
  have hs1 := (summable_nat_add_iff 1).mpr hs
  have hneg : Summable (fun n : ℕ =>
      (1 + (b * ((-(n + 1) : ℤ) : ℝ)) ^ 2)⁻¹) := by
    simpa only [Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one,
      Nat.cast_add, Nat.cast_one, mul_neg, neg_sq] using hs1
  rw [tsum_of_nat_of_neg_add_one
    (f := fun n : ℤ => (1 + (b * (n : ℝ)) ^ 2)⁻¹)
    (by simpa only [Int.cast_natCast] using hs) hneg]
  simp only [Int.cast_natCast, Int.cast_neg, Int.cast_add, Int.cast_one, mul_neg,
    neg_sq]
  have hz := hs.tsum_eq_zero_add
  have he : (∑' n : ℕ, (1 + (b * (↑n + 1)) ^ 2)⁻¹) =
      (∑' n : ℕ, (1 + (b * (n : ℝ)) ^ 2)⁻¹) - 1 := by
    apply eq_sub_iff_add_eq.mpr
    simpa [add_comm] using hz.symm
  rw [he]
  have := scaled_cauchy_nat_bound b hb
  have hh : Real.pi / (2 * b) = (Real.pi / b) / 2 := by ring
  rw [hh] at this
  linarith

open Eisenstein

theorem scaled_eisenstein_cauchy_summable (K : ℝ) (hK : 0 < K) :
    Summable (fun h : O => ((1 + K * ‖ringComplex h‖ ^ 2) ^ 2)⁻¹) := by
  let b := Real.sqrt K
  have hb : 0 < b := Real.sqrt_pos.mpr hK
  have hbsq : b ^ 2 = K := Real.sq_sqrt hK.le
  have hs := summable_scaled_cauchy_int b hb
  have hp := hs.mul_of_nonneg hs (fun _ => by positivity) (fun _ => by positivity)
  apply (Eisenstein.Coordinates.coordinateEquiv.symm.summable_iff).mp
  change Summable (fun p : ℤ × ℤ =>
    ((1 + K * ‖ringComplex (Eisenstein.Coordinates.coordinateEquiv.symm p)‖ ^ 2) ^ 2)⁻¹)
  apply Summable.of_nonneg_of_le (fun _ => by positivity) _ (hp.mul_left 4)
  intro p
  apply inverse_square_le_cauchy_product (b * (p.1 : ℝ)) (b * (p.2 : ℝ))
    (K * ‖ringComplex (Eisenstein.Coordinates.coordinateEquiv.symm p)‖ ^ 2) (by positivity)
  change ((b * (p.1 : ℝ)) ^ 2 + (b * (p.2 : ℝ)) ^ 2) / 2 ≤
    K * ‖ringComplex (Eisenstein.Coordinates.eval p.1 p.2)‖ ^ 2
  rw [Eisenstein.Coordinates.complex_norm_eval_sq]
  push_cast
  nlinarith [mul_nonneg hK.le (sq_nonneg ((p.1 : ℝ) - (p.2 : ℝ)))]

theorem scaled_eisenstein_cauchy_bound (K : ℝ) (hK : 0 < K) :
    (∑' h : O, ((1 + K * ‖ringComplex h‖ ^ 2) ^ 2)⁻¹) ≤
      4 * (1 + Real.pi / Real.sqrt K) ^ 2 := by
  let b := Real.sqrt K
  have hb : 0 < b := Real.sqrt_pos.mpr hK
  have hbsq : b ^ 2 = K := Real.sq_sqrt hK.le
  have hs := summable_scaled_cauchy_int b hb
  have hp := hs.mul_of_nonneg hs (fun _ => by positivity) (fun _ => by positivity)
  have he : (∑' h : O, ((1 + K * ‖ringComplex h‖ ^ 2) ^ 2)⁻¹) =
      ∑' p : ℤ × ℤ, ((1 + K * ‖ringComplex (Eisenstein.Coordinates.coordinateEquiv.symm p)‖ ^ 2) ^ 2)⁻¹ :=
    (Eisenstein.Coordinates.coordinateEquiv.symm.tsum_eq _).symm
  rw [he]
  calc
    _ ≤ ∑' p : ℤ × ℤ, 4 * ((1 + (b * (p.1 : ℝ)) ^ 2)⁻¹ *
          (1 + (b * (p.2 : ℝ)) ^ 2)⁻¹) := by
      apply ((Eisenstein.Coordinates.coordinateEquiv.symm.summable_iff).mpr
        (scaled_eisenstein_cauchy_summable K hK)).tsum_le_tsum _ (hp.mul_left 4)
      intro p
      apply inverse_square_le_cauchy_product _ _ _ (by positivity)
      change ((b * (p.1 : ℝ)) ^ 2 + (b * (p.2 : ℝ)) ^ 2) / 2 ≤
        K * ‖ringComplex (Eisenstein.Coordinates.eval p.1 p.2)‖ ^ 2
      rw [Eisenstein.Coordinates.complex_norm_eval_sq]
      push_cast
      nlinarith [mul_nonneg hK.le (sq_nonneg ((p.1 : ℝ) - (p.2 : ℝ)))]
    _ = 4 * (∑' n : ℤ, (1 + (b * (n : ℝ)) ^ 2)⁻¹) ^ 2 := by
      rw [tsum_mul_left, ← hs.tsum_mul_tsum hs hp, pow_two]
    _ ≤ 4 * (1 + Real.pi / b) ^ 2 := by
      gcongr
      exact scaled_cauchy_int_bound b hb

theorem scaled_eisenstein_cauchy_small (K : ℝ) (hK : 0 < K) (hK1 : K ≤ 1) :
    K * (∑' h : O, ((1 + K * ‖ringComplex h‖ ^ 2) ^ 2)⁻¹) ≤
      4 * (1 + Real.pi) ^ 2 := by
  have hs := scaled_eisenstein_cauchy_bound K hK
  have hb : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK
  have hb1 : Real.sqrt K ≤ 1 := by simpa using Real.sqrt_le_sqrt hK1
  have hsq := Real.sq_sqrt hK.le
  calc
    _ ≤ K * (4 * (1 + Real.pi / Real.sqrt K) ^ 2) :=
      mul_le_mul_of_nonneg_left hs hK.le
    _ = 4 * (Real.sqrt K + Real.pi) ^ 2 := by
      nth_rw 1 [← hsq]
      field_simp
    _ ≤ _ := by gcongr

theorem one_le_eisenstein_norm_sq (h : O) (hh : h ≠ 0) :
    1 ≤ ‖ringComplex h‖ ^ 2 := by
  rw [ringComplex_norm_sq_eq_absNorm_span]
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (show Ideal.absNorm (Ideal.span {h}) ≠ 0 by
    rw [ne_eq, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hh)

theorem cauchy_large_scale_pointwise (K q : ℝ) (hK : 1 ≤ K) (hq : 1 ≤ q) :
    K * ((1 + K * q) ^ 2)⁻¹ ≤ 4 * ((1 + q) ^ 2)⁻¹ := by
  have hKp : 0 < K := by linarith
  have hqp : 0 < q := by linarith
  have h1 : K * (1 + q) ≤ 2 * (1 + K * q) := by nlinarith
  have h2 := pow_le_pow_left₀ (by positivity : 0 ≤ K * (1 + q)) h1 2
  have h3 : K * (1 + q) ^ 2 ≤ K ^ 2 * (1 + q) ^ 2 := by
    nlinarith [sq_nonneg (1 + q)]
  apply (div_le_div_iff₀ (by positivity : 0 < (1 + K * q) ^ 2)
    (by positivity : 0 < (1 + q) ^ 2)).mpr
  nlinarith

theorem lattice_profile_nonzero_scaled_bound
    (F : ℝ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hF : ∀ t : ℝ, 0 ≤ t → (1 + t) ^ 2 * ‖F t‖ ≤ B)
    (K : ℝ) (hK : 0 < K) :
    K * (∑' h : {h : O // h ≠ 0}, ‖F (K * ‖ringComplex h.val‖ ^ 2)‖) ≤
      (4 * (1 + Real.pi) ^ 2 + 4 * eisensteinCauchyMass) * B := by
  have hm (h : O) : ‖F (K * ‖ringComplex h‖ ^ 2)‖ ≤
      B * ((1 + K * ‖ringComplex h‖ ^ 2) ^ 2)⁻¹ := by
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ (by positivity)).mpr
    simpa only [mul_comm] using hF (K * ‖ringComplex h‖ ^ 2) (by positivity)
  have hs := scaled_eisenstein_cauchy_summable K hK
  have hf : Summable (fun h : O => ‖F (K * ‖ringComplex h‖ ^ 2)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hm (hs.mul_left B)
  have hsub := hf.subtype (fun h : O => h ≠ 0)
  have hc := eisenstein_cauchy_summable.subtype (fun h : O => h ≠ 0)
  by_cases hK1 : K ≤ 1
  · have htotal : (∑' h : {h : O // h ≠ 0}, ‖F (K * ‖ringComplex h.val‖ ^ 2)‖) ≤
        ∑' h : O, ‖F (K * ‖ringComplex h‖ ^ 2)‖ :=
      hsub.tsum_le_tsum_of_inj Subtype.val Subtype.val_injective
        (fun _ _ => norm_nonneg _) (fun _ => le_rfl) hf
    have hbound := hf.tsum_le_tsum hm (hs.mul_left B)
    rw [tsum_mul_left] at hbound
    calc
      _ ≤ K * (B * ∑' h : O, ((1 + K * ‖ringComplex h‖ ^ 2) ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left (htotal.trans hbound) hK.le
      _ = B * (K * ∑' h : O, ((1 + K * ‖ringComplex h‖ ^ 2) ^ 2)⁻¹) := by ring
      _ ≤ B * (4 * (1 + Real.pi) ^ 2) :=
        mul_le_mul_of_nonneg_left (scaled_eisenstein_cauchy_small K hK hK1) hB
      _ ≤ _ := by nlinarith [eisensteinCauchyMass_nonneg]
  · have hp (h : {h : O // h ≠ 0}) :
        K * ‖F (K * ‖ringComplex h.val‖ ^ 2)‖ ≤
          (4 * B) * ((1 + ‖ringComplex h.val‖ ^ 2) ^ 2)⁻¹ := by
      calc
        _ ≤ K * (B * ((1 + K * ‖ringComplex h.val‖ ^ 2) ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_left (hm h.val) hK.le
        _ = B * (K * ((1 + K * ‖ringComplex h.val‖ ^ 2) ^ 2)⁻¹) := by ring
        _ ≤ B * (4 * ((1 + ‖ringComplex h.val‖ ^ 2) ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_left (cauchy_large_scale_pointwise K _
            (le_of_not_ge hK1) (one_le_eisenstein_norm_sq h.val h.property)) hB
        _ = _ := by ring
    calc
      _ = ∑' h : {h : O // h ≠ 0}, K * ‖F (K * ‖ringComplex h.val‖ ^ 2)‖ := tsum_mul_left.symm
      _ ≤ ∑' h : {h : O // h ≠ 0}, (4 * B) * ((1 + ‖ringComplex h.val‖ ^ 2) ^ 2)⁻¹ :=
        (hsub.mul_left K).tsum_le_tsum hp (hc.mul_left (4 * B))
      _ = (4 * B) * ∑' h : {h : O // h ≠ 0}, ((1 + ‖ringComplex h.val‖ ^ 2) ^ 2)⁻¹ := tsum_mul_left
      _ ≤ (4 * B) * eisensteinCauchyMass := mul_le_mul_of_nonneg_left
        (eisensteinCauchyMass_subtype (fun h : O => h ≠ 0)) (by positivity)
      _ ≤ _ := by nlinarith [sq_nonneg (1 + Real.pi)]

theorem paperRadialFourier_nonzero_lattice_uniform :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : SchwartzMap ℝ ℂ) (K : ℝ), 0 < K →
        K * (∑' h : {h : O // h ≠ 0},
          ‖paperRadialFourier W (K * ‖ringComplex h.val‖ ^ 2)‖) ≤
            C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  obtain ⟨s, C, hC, hb⟩ := paperRadialFourier_source_weighted_bound 2
  refine ⟨s, (4 * (1 + Real.pi) ^ 2 + 4 * eisensteinCauchyMass) * C, ?_, ?_⟩
  · have := eisensteinCauchyMass_nonneg
    have := Real.pi_pos
    positivity
  · intro W K hK
    simpa only [mul_assoc] using lattice_profile_nonzero_scaled_bound
      (paperRadialFourier W) (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)
        (by positivity) (hb W) K hK

end SchwartzPlanePoisson

namespace SchwartzPlanePoisson
open Eisenstein MeasureTheory
open scoped SchwartzMap

lemma primeCuspRowCharacter_norm_le_one {ι : Type*} [Fintype ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ) (x : O) :
    ‖primeCuspRowCharacter p χ x‖ ≤ 1 := by
  change ‖∏ i, χ i (Ideal.Quotient.mk (Ideal.span {p i}) x)‖ ≤ 1
  rw [norm_prod]
  exact Finset.prod_le_one (fun _ _ => norm_nonneg _)
    (fun i _ => finiteMulChar_norm_le_one (χ i) _)

lemma primeCuspRowCharacter_zero {ι : Type*} [Fintype ι] [Nonempty ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ) :
    primeCuspRowCharacter p χ 0 = 0 := by
  classical
  obtain ⟨i⟩ := ‹Nonempty ι›
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [map_zero, MulChar.map_zero])

/-- The smoothed Pólya–Vinogradov bound is uniform in scale and in every nontrivial prime row. -/
theorem prime_row_polya_vinogradov :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
        (p : ι → O) (hp : ∀ i, p i ≠ 0)
        [∀ i, (Ideal.span {p i}).IsMaximal]
        (hinj : Function.Injective (fun i => Ideal.span {p i}))
        (χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ) (hχ : ∀ i, χ i ≠ 1)
        (W : 𝓢(ℝ, ℂ)) (Y : ℝ), 0 < Y →
        ‖∑' z : O, primeCuspRowCharacter p χ z * W (‖ringComplex z‖ ^ 2 / Y)‖ ≤
          (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) * ‖ringComplex (∏ i, p i)‖ := by
  obtain ⟨s, C, hC, hb⟩ := paperRadialFourier_nonzero_lattice_uniform
  refine ⟨s, C, hC, ?_⟩
  intro ι _ _ _ p hp _ hinj χ hχ W Y hY
  let c := ∏ i, p i
  let q := ‖ringComplex c‖
  have hc : c ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  have hq : 0 < q := norm_pos_iff.mpr (ringComplex_ne_zero hc)
  let t := Y / q ^ 2
  have ht : 0 < t := div_pos hY (sq_pos_of_pos hq)
  let F : O → ℂ := fun h => primeCuspRowCharacter p (fun i => (χ i)⁻¹) h *
    paperRadialFourier W (t * ‖ringComplex h‖ ^ 2)
  have hF (h : O) : ‖F h‖ ≤ ‖paperRadialFourier W (t * ‖ringComplex h‖ ^ 2)‖ := by
    dsimp only [F]
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (primeCuspRowCharacter_norm_le_one p _ h)
  have hs := paperRadialFourier_lattice_summable_norm W t ht
  have hFs : Summable (fun h : O => ‖F h‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hF hs
  have hzero : F 0 = 0 := by simp only [F, primeCuspRowCharacter_zero, zero_mul]
  have heq : (∑' h : O, F h) = ∑' h : {h : O // h ≠ 0}, F h := by
    symm
    apply tsum_subtype_eq_of_support_subset
    intro h hh hz
    subst h
    exact hh hzero
  have hn : ‖∑' h : O, F h‖ ≤
      ∑' h : {h : O // h ≠ 0}, ‖paperRadialFourier W (t * ‖ringComplex h.val‖ ^ 2)‖ := by
    rw [heq]
    exact (norm_tsum_le_tsum_norm (hFs.subtype _)).trans
      ((hFs.subtype _).tsum_le_tsum (fun h => hF h) (hs.subtype _))
  have hbound : t * ‖∑' h : O, F h‖ ≤ C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W :=
    (mul_le_mul_of_nonneg_left hn ht.le).trans (hb W t ht)
  obtain ⟨β, hβ, hpoisson⟩ := prime_row_radial_poisson p hp hinj χ hχ
  rw [hpoisson W Y hY]
  have hargs (h : O) : Y * ‖ringComplex h‖ ^ 2 / ‖ringComplex c‖ ^ 2 =
      t * ‖ringComplex h‖ ^ 2 := by dsimp [t, q]; ring
  change ‖((Y : ℂ) * β / (q : ℂ)) *
    ∑' h : O, primeCuspRowCharacter p (fun i => (χ i)⁻¹) h *
      paperRadialFourier W (Y * ‖ringComplex h‖ ^ 2 / ‖ringComplex c‖ ^ 2)‖ ≤ _
  simp_rw [hargs]
  change ‖((Y : ℂ) * β / (q : ℂ)) * ∑' h : O, F h‖ ≤ _
  rw [norm_mul, norm_div, norm_mul, hβ,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hY, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq]
  calc
    Y / q * ‖∑' h : O, F h‖ = q * (t * ‖∑' h : O, F h‖) := by dsimp [t]; field_simp
    _ ≤ q * (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) :=
      mul_le_mul_of_nonneg_left hbound hq.le
    _ = _ := mul_comm _ _

end SchwartzPlanePoisson

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
