import GaloisForLFunctions.RHTower.Suzuki.SuzukiTaCharacteristicRealization

/-!
# Complex spectral eigenspaces of Suzuki's minimal derivative

The deficiency-index computation at `±i` is not enough to justify the assertion in Suzuki v2
that every eigenvalue of every self-adjoint extension is detected by the displayed characteristic
function.  This file supplies the missing complex-parameter statement.  An explicit integrating
factor proves that the range of `i d/dx - star z` is dense in the kernel of the actual spectral
moment.  Taking orthogonal complements shows that every `z`-eigenvector of the adjoint is a scalar
multiple of the canonical Riesz vector.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct FourierTransform LinearPMap
open GaloisForLFunctions.HTGeometry

noncomputable section
namespace RHTower

/-- Complex spectral shift `i d/dx - star z` on the literal smooth core. -/
def suzukiTaSpectralCoreShift (a : SuzukiPositiveAperture) (z : ℂ) :
    SuzukiTaSmoothCore a →ₗ[ℂ] SuzukiTaSmoothCore a :=
  suzukiTaSmoothCoreIDeriv a - (star z) • LinearMap.id

@[simp] theorem suzukiTaSpectralCoreShift_apply
    (a : SuzukiPositiveAperture) (z : ℂ) (u : SuzukiTaSmoothCore a) (x : ℝ) :
    suzukiTaSpectralCoreShift a z u x = I * deriv u x - star z * u x := by
  simp [suzukiTaSpectralCoreShift, suzukiTaSmoothCoreIDeriv_apply]

def suzukiTaSpectralCoreShiftToHilbert
    (a : SuzukiPositiveAperture) (z : ℂ) :
    SuzukiTaSmoothCore a →ₗ[ℂ] SuzukiTaHilbert a :=
  (suzukiTaSmoothCoreToHilbert a).comp (suzukiTaSpectralCoreShift a z)

theorem suzukiTaSpectralMoment_shift_eq_zero
    (a : SuzukiPositiveAperture) (z : ℂ) (u : SuzukiTaSmoothCore a) :
    suzukiTaSpectralMoment a z (suzukiTaSpectralCoreShiftToHilbert a z u) = 0 := by
  rw [suzukiTaSpectralCoreShiftToHilbert, LinearMap.comp_apply,
    suzukiTaSpectralCoreShift, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, map_sub, map_smul]
  rw [map_sub, map_smul, suzukiTaSpectralMoment_IDeriv]
  ring

def suzukiTaSpectralWeightedCore (z : ℂ) (g : ℝ → ℂ) : ℝ → ℂ :=
  fun x => Complex.exp (I * star z * (x : ℂ)) * g x

theorem contDiff_suzukiTaSpectralWeightedCore
    (z : ℂ) {g : ℝ → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ContDiff ℝ (⊤ : ℕ∞) (suzukiTaSpectralWeightedCore z g) := by
  have harg : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : ℝ => I * star z * (x : ℂ)) :=
    contDiff_const.mul Complex.ofRealCLM.contDiff
  exact harg.cexp.mul hg

theorem suzukiTaSpectralWeightedCore_support_subset
    (a : SuzukiPositiveAperture) (z : ℂ) (g : SuzukiTaSmoothCore a) :
    Function.support (suzukiTaSpectralWeightedCore z g) ⊆
      Ioo (-suzukiTaSmoothCoreSupportRadius a g)
        (suzukiTaSmoothCoreSupportRadius a g) := by
  intro x hx
  apply suzukiTaSmoothCore_support_subset_radius a g
  intro hg
  exact hx (by simp [suzukiTaSpectralWeightedCore, hg])

def suzukiTaSpectralWeightedPrimitive
    (a : SuzukiPositiveAperture) (z : ℂ) (g : SuzukiTaSmoothCore a) : ℝ → ℂ :=
  suzukiSmoothIntegralPrimitive (suzukiTaSmoothCoreSupportRadius a g)
    (suzukiTaSpectralWeightedCore z g)

theorem contDiff_suzukiTaSpectralWeightedPrimitive
    (a : SuzukiPositiveAperture) (z : ℂ) (g : SuzukiTaSmoothCore a) :
    ContDiff ℝ (⊤ : ℕ∞) (suzukiTaSpectralWeightedPrimitive a z g) :=
  contDiff_suzukiSmoothIntegralPrimitive _ _
    (contDiff_suzukiTaSpectralWeightedCore z g.contDiff)

theorem deriv_suzukiTaSpectralWeightedPrimitive
    (a : SuzukiPositiveAperture) (z : ℂ) (g : SuzukiTaSmoothCore a) (x : ℝ) :
    deriv (suzukiTaSpectralWeightedPrimitive a z g) x =
      suzukiTaSpectralWeightedCore z g x :=
  deriv_suzukiSmoothIntegralPrimitive _ _
    (contDiff_suzukiTaSpectralWeightedCore z g.contDiff).continuous x

def suzukiTaSpectralShiftedPrimitiveSolution
    (a : SuzukiPositiveAperture) (z : ℂ) (g : SuzukiTaSmoothCore a)
    (hzero : (∫ x : ℝ, suzukiTaSpectralWeightedCore z g x) = 0) :
    SuzukiTaSmoothCore a where
  toFun x := -I * Complex.exp (-I * star z * (x : ℂ)) *
    suzukiTaSpectralWeightedPrimitive a z g x
  contDiff' := by
    have harg : ContDiff ℝ (⊤ : ℕ∞)
        (fun x : ℝ => -I * star z * (x : ℂ)) :=
      contDiff_const.mul Complex.ofRealCLM.contDiff
    exact (contDiff_const.mul harg.cexp).mul
      (contDiff_suzukiTaSpectralWeightedPrimitive a z g)
  hasCompactSupport' := by
    have hp := hasCompactSupport_suzukiSmoothIntegralPrimitive
      (suzukiTaSpectralWeightedCore_support_subset a z g) hzero
    refine HasCompactSupport.intro hp ?_
    intro x hx
    change -I * Complex.exp (-I * star z * (x : ℂ)) *
      suzukiSmoothIntegralPrimitive (suzukiTaSmoothCoreSupportRadius a g)
        (suzukiTaSpectralWeightedCore z g) x = 0
    rw [image_eq_zero_of_notMem_tsupport hx]
    ring
  tsupport_subset' := by
    let p : ℝ → ℂ := suzukiTaSpectralWeightedPrimitive a z g
    have hp : tsupport p ⊆
        Icc (-suzukiTaSmoothCoreSupportRadius a g)
          (suzukiTaSmoothCoreSupportRadius a g) :=
      tsupport_suzukiSmoothIntegralPrimitive_subset
        (suzukiTaSpectralWeightedCore_support_subset a z g) hzero
    have hsol : tsupport (fun x : ℝ =>
        -I * Complex.exp (-I * star z * (x : ℂ)) * p x) ⊆ tsupport p := by
      apply closure_minimal
      · intro x hx
        apply subset_closure
        intro hp0
        exact hx (by simp [hp0])
      · exact isClosed_tsupport p
    intro x hx
    have hi := hp (hsol hx)
    exact ⟨lt_of_lt_of_le (neg_lt_neg (suzukiTaSmoothCoreSupportRadius_lt a g)) hi.1,
      lt_of_le_of_lt hi.2 (suzukiTaSmoothCoreSupportRadius_lt a g)⟩

@[simp] theorem suzukiTaSpectralShiftedPrimitiveSolution_apply
    (a : SuzukiPositiveAperture) (z : ℂ) (g : SuzukiTaSmoothCore a)
    (hzero : (∫ x : ℝ, suzukiTaSpectralWeightedCore z g x) = 0) (x : ℝ) :
    suzukiTaSpectralShiftedPrimitiveSolution a z g hzero x =
      -I * Complex.exp (-I * star z * (x : ℂ)) *
        suzukiTaSpectralWeightedPrimitive a z g x := rfl

theorem suzukiTaSpectralCoreShift_solution
    (a : SuzukiPositiveAperture) (z : ℂ) (g : SuzukiTaSmoothCore a)
    (hzero : (∫ x : ℝ, suzukiTaSpectralWeightedCore z g x) = 0) :
    suzukiTaSpectralCoreShift a z
      (suzukiTaSpectralShiftedPrimitiveSolution a z g hzero) = g := by
  apply DFunLike.coe_injective
  funext x
  rw [suzukiTaSpectralCoreShift_apply]
  let p : ℝ → ℂ := suzukiTaSpectralWeightedPrimitive a z g
  have hpDiff : Differentiable ℝ p :=
    (contDiff_suzukiTaSpectralWeightedPrimitive a z g).differentiable (by simp)
  have hexp := hasDerivAt_cexp_const_mul (-I * star z) x
  have hp : HasDerivAt p (suzukiTaSpectralWeightedCore z g x) x := by
    exact (hpDiff x).hasDerivAt.congr_deriv
      (deriv_suzukiTaSpectralWeightedPrimitive a z g x)
  have hprod := (hexp.mul hp).const_mul (-I)
  have hderiv : deriv
      (suzukiTaSpectralShiftedPrimitiveSolution a z g hzero) x =
      -I * (Complex.exp (-I * star z * (x : ℂ)) * (-I * star z) * p x +
        Complex.exp (-I * star z * (x : ℂ)) *
          suzukiTaSpectralWeightedCore z g x) := by
    change deriv (fun y : ℝ =>
      -I * Complex.exp (-I * star z * (y : ℂ)) * p y) x = _
    have hfun : (fun y : ℝ =>
        -I * Complex.exp (-I * star z * (y : ℂ)) * p y) =
        fun y : ℝ => -I *
          ((fun t : ℝ => Complex.exp (-I * star z * (t : ℂ))) * p) y := by
      funext y
      change -I * Complex.exp (-I * star z * (y : ℂ)) * p y =
        -I * (Complex.exp (-I * star z * (y : ℂ)) * p y)
      ring
    rw [hfun]
    exact hprod.deriv
  rw [hderiv, suzukiTaSpectralShiftedPrimitiveSolution_apply]
  change I *
      (-I * (Complex.exp (-I * star z * (x : ℂ)) * (-I * star z) * p x +
        Complex.exp (-I * star z * (x : ℂ)) *
          (Complex.exp (I * star z * (x : ℂ)) * g x))) -
      star z * (-I * Complex.exp (-I * star z * (x : ℂ)) * p x) = g x
  have hexpInv : Complex.exp (-I * star z * (x : ℂ)) *
      Complex.exp (I * star z * (x : ℂ)) = 1 := by
    calc
      _ = Complex.exp 0 := by
        rw [← Complex.exp_add]
        congr 1
        ring
      _ = 1 := Complex.exp_zero
  rw [show Complex.exp (-I * star z * (x : ℂ)) *
      (Complex.exp (I * star z * (x : ℂ)) * g x) = g x by
        rw [← mul_assoc, hexpInv, one_mul]]
  have hI : I * (-I) = (1 : ℂ) := by
    rw [mul_neg, Complex.I_mul_I]
    simp
  rw [← mul_assoc, hI, one_mul]
  ring

theorem range_suzukiTaSpectralCoreShiftToHilbert_eq_correction
    (a : SuzukiPositiveAperture) (z : ℂ) :
    LinearMap.range (suzukiTaSpectralCoreShiftToHilbert a z) =
      LinearMap.range
        (DenseCoreHyperplane.correction
          (suzukiTaSmoothCoreToHilbert a) (suzukiTaSpectralMoment a z)
          (suzukiTaSpectralMomentNormalizer a z)) := by
  let J := suzukiTaSmoothCoreToHilbert a
  let L := suzukiTaSpectralMoment a z
  let q := suzukiTaSpectralMomentNormalizer a z
  have hq : L (J q) = 1 := suzukiTaSpectralMoment_normalizer a z
  rw [DenseCoreHyperplane.range_correction_eq J L q hq]
  apply le_antisymm
  · rintro y ⟨u, rfl⟩
    constructor
    · exact ⟨suzukiTaSpectralCoreShift a z u, rfl⟩
    · change L (suzukiTaSpectralCoreShiftToHilbert a z u) = 0
      exact suzukiTaSpectralMoment_shift_eq_zero a z u
  · rintro y ⟨⟨g, hg⟩, hLg⟩
    change L y = 0 at hLg
    have hLJg : L (J g) = 0 := by rw [hg]; exact hLg
    have hzero : (∫ x : ℝ, suzukiTaSpectralWeightedCore z g x) = 0 := by
      change (∫ x : ℝ, Complex.exp (I * star z * (x : ℂ)) * g x) = 0
      rw [← suzukiTaSpectralMoment_smoothCore_eq_integral a z g]
      exact hLJg
    refine ⟨suzukiTaSpectralShiftedPrimitiveSolution a z g hzero, ?_⟩
    change J (suzukiTaSpectralCoreShift a z
      (suzukiTaSpectralShiftedPrimitiveSolution a z g hzero)) = y
    rw [suzukiTaSpectralCoreShift_solution]
    exact hg

theorem topologicalClosure_range_suzukiTaSpectralCoreShiftToHilbert
    (a : SuzukiPositiveAperture) (z : ℂ) :
    (LinearMap.range (suzukiTaSpectralCoreShiftToHilbert a z)).topologicalClosure =
      LinearMap.ker (suzukiTaSpectralMoment a z).toLinearMap := by
  rw [range_suzukiTaSpectralCoreShiftToHilbert_eq_correction]
  exact DenseCoreHyperplane.topologicalClosure_range_correction_eq_ker
    (suzukiTaSmoothCoreToHilbert a) (suzukiTaSpectralMoment a z)
    (suzukiTaSpectralMomentNormalizer a z)
    (suzukiTaSpectralMoment_normalizer a z)
    (denseRange_suzukiTaSmoothCoreToHilbert a)

noncomputable def suzukiTaSpectralShiftPMap
    (a : SuzukiPositiveAperture) (z : ℂ) :
    SuzukiTaHilbert a →ₗ.[ℂ] SuzukiTaHilbert a where
  domain := LinearMap.range (suzukiTaSmoothCoreToHilbert a)
  toFun := (suzukiTaSpectralCoreShiftToHilbert a z).comp
    (suzukiTaSmoothCoreEquivRange a).symm.toLinearMap

theorem suzukiTaSpectralShiftPMap_apply
    (a : SuzukiPositiveAperture) (z : ℂ) (u : SuzukiTaSmoothCore a) :
    suzukiTaSpectralShiftPMap a z ((suzukiTaSmoothCoreEquivRange a) u) =
      suzukiTaSpectralCoreShiftToHilbert a z u := by
  change suzukiTaSpectralCoreShiftToHilbert a z
      ((suzukiTaSmoothCoreEquivRange a).symm
        ((suzukiTaSmoothCoreEquivRange a) u)) = _
  rw [LinearEquiv.symm_apply_apply]

theorem dense_suzukiTaSpectralShiftPMap_domain
    (a : SuzukiPositiveAperture) (z : ℂ) :
    Dense ((suzukiTaSpectralShiftPMap a z).domain : Set (SuzukiTaHilbert a)) := by
  change Dense (LinearMap.range (suzukiTaSmoothCoreToHilbert a) : Set (SuzukiTaHilbert a))
  exact denseRange_suzukiTaSmoothCoreToHilbert a

theorem suzukiTaSpectralShiftPMap_rangeSubmodule
    (a : SuzukiPositiveAperture) (z : ℂ) :
    (suzukiTaSpectralShiftPMap a z).rangeSubmodule =
      LinearMap.range (suzukiTaSpectralCoreShiftToHilbert a z) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨(suzukiTaSmoothCoreEquivRange a).symm x, rfl⟩
  · rintro ⟨u, rfl⟩
    exact ⟨(suzukiTaSmoothCoreEquivRange a) u,
      suzukiTaSpectralShiftPMap_apply a z u⟩

theorem suzukiTaSpectralMoment_adjoint_range_eq_span
    (a : SuzukiPositiveAperture) (z : ℂ) :
    LinearMap.range (suzukiTaSpectralMoment a z).adjoint.toLinearMap =
      ℂ ∙ suzukiTaSpectralVector a z := by
  ext y
  constructor
  · rintro ⟨c, rfl⟩
    rw [Submodule.mem_span_singleton]
    refine ⟨c, ?_⟩
    simpa [suzukiTaSpectralVector] using
      ((suzukiTaSpectralMoment a z).adjoint.map_smul c (1 : ℂ)).symm
  · rw [Submodule.mem_span_singleton]
    rintro ⟨c, rfl⟩
    refine ⟨c, ?_⟩
    simpa [suzukiTaSpectralVector] using
      ((suzukiTaSpectralMoment a z).adjoint.map_smul c (1 : ℂ))

theorem suzukiTaSpectralMoment_kernel_orthogonal_eq_span
    (a : SuzukiPositiveAperture) (z : ℂ) :
    (LinearMap.ker (suzukiTaSpectralMoment a z).toLinearMap)ᗮ =
      ℂ ∙ suzukiTaSpectralVector a z := by
  change (suzukiTaSpectralMoment a z).kerᗮ = _
  rw [(suzukiTaSpectralMoment a z).orthogonal_ker,
    suzukiTaSpectralMoment_adjoint_range_eq_span]
  exact Submodule.topologicalClosure_eq_self _

theorem suzukiTaSpectralShiftPMap_adjoint_kernel_eq_span
    (a : SuzukiPositiveAperture) (z : ℂ) :
    (suzukiTaSpectralShiftPMap a z).adjoint.kernel =
      ℂ ∙ suzukiTaSpectralVector a z := by
  rw [LinearPMap.adjoint_kernel_eq_orthogonal_range
    (suzukiTaSpectralShiftPMap a z)
      (dense_suzukiTaSpectralShiftPMap_domain a z)]
  rw [suzukiTaSpectralShiftPMap_rangeSubmodule,
    ← Submodule.orthogonal_closure,
    topologicalClosure_range_suzukiTaSpectralCoreShiftToHilbert,
    suzukiTaSpectralMoment_kernel_orthogonal_eq_span]

theorem suzukiTaSpectralShiftPMap_apply_eq_minimal_sub
    (a : SuzukiPositiveAperture) (z : ℂ)
    (x : (suzukiTaMinimalDerivative a).domain) :
    suzukiTaSpectralShiftPMap a z x =
      suzukiTaMinimalDerivative a x - star z • (x : SuzukiTaHilbert a) := by
  let u : SuzukiTaSmoothCore a := (suzukiTaSmoothCoreEquivRange a).symm x
  have hx : x = (suzukiTaSmoothCoreEquivRange a) u :=
    ((suzukiTaSmoothCoreEquivRange a).apply_symm_apply x).symm
  rw [hx, suzukiTaSpectralShiftPMap_apply, suzukiTaMinimalDerivative_apply]
  change suzukiTaSmoothCoreToHilbert a (suzukiTaSpectralCoreShift a z u) =
    suzukiTaSmoothCoreToHilbert a (suzukiTaSmoothCoreIDeriv a u) -
      star z • suzukiTaSmoothCoreToHilbert a u
  rw [suzukiTaSpectralCoreShift, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, map_sub, map_smul]

/-- Every adjoint `z`-eigenvector is a scalar multiple of the canonical Riesz vector. -/
theorem suzukiTa_adjoint_eigenspace_span
    (a : SuzukiPositiveAperture) (z : ℂ)
    (x : (suzukiTaMinimalDerivative a).adjoint.domain)
    (hx : (suzukiTaMinimalDerivative a).adjoint x =
      z • (x : SuzukiTaHilbert a)) :
    ∃ c : ℂ, (x : SuzukiTaHilbert a) = c • suzukiTaSpectralVector a z := by
  let T := suzukiTaSpectralShiftPMap a z
  have hxT : (x : SuzukiTaHilbert a) ∈ T.adjoint.domain := by
    apply LinearPMap.mem_adjoint_domain_of_exists
    refine ⟨0, ?_⟩
    intro y
    let yS : (suzukiTaMinimalDerivative a).domain :=
      ⟨(y : SuzukiTaHilbert a), y.property⟩
    have hformal := LinearPMap.adjoint_isFormalAdjoint
      (dense_suzukiTaShiftedDerivativePMap_domain a 0) x yS
    change inner ℂ 0 (yS : SuzukiTaHilbert a) =
      inner ℂ (x : SuzukiTaHilbert a) (T yS)
    rw [suzukiTaSpectralShiftPMap_apply_eq_minimal_sub,
      inner_sub_right, inner_smul_right, ← hformal, hx, inner_smul_left]
    rw [show (starRingEnd ℂ) z = star z from rfl]
    simp
  let xT : T.adjoint.domain := ⟨(x : SuzukiTaHilbert a), hxT⟩
  have hxTzero : T.adjoint xT = 0 := by
    apply LinearPMap.adjoint_apply_eq (dense_suzukiTaSpectralShiftPMap_domain a z)
    intro y
    let yS : (suzukiTaMinimalDerivative a).domain :=
      ⟨(y : SuzukiTaHilbert a), y.property⟩
    have hformal := LinearPMap.adjoint_isFormalAdjoint
      (dense_suzukiTaShiftedDerivativePMap_domain a 0) x yS
    change inner ℂ 0 (yS : SuzukiTaHilbert a) =
      inner ℂ (x : SuzukiTaHilbert a) (T yS)
    rw [suzukiTaSpectralShiftPMap_apply_eq_minimal_sub,
      inner_sub_right, inner_smul_right, ← hformal, hx, inner_smul_left]
    rw [show (starRingEnd ℂ) z = star z from rfl]
    simp
  have hxker : (x : SuzukiTaHilbert a) ∈ T.adjoint.kernel := ⟨xT, hxTzero, rfl⟩
  rw [show T.adjoint.kernel = ℂ ∙ suzukiTaSpectralVector a z from
    suzukiTaSpectralShiftPMap_adjoint_kernel_eq_span a z,
    Submodule.mem_span_singleton] at hxker
  obtain ⟨c, hc⟩ := hxker
  exact ⟨c, hc.symm⟩

end RHTower
