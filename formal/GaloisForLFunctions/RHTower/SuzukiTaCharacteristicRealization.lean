import GaloisForLFunctions.RHTower.SuzukiTaSymmetry
import GaloisForLFunctions.RHTower.SuzukiCompactL2Fourier
import GaloisForLFunctions.HTGeometry.VonNeumannDeficiency
import GaloisForLFunctions.HTGeometry.ExponentialCharacter

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct FourierTransform LinearPMap
open GaloisForLFunctions.HTGeometry

noncomputable section
namespace RHTower

attribute [local instance] Measure.Subtype.measureSpace

abbrev suzukiTaMinimalDerivative (a : SuzukiPositiveAperture) :
    SuzukiTaHilbert a →ₗ.[ℂ] SuzukiTaHilbert a :=
  suzukiTaShiftedDerivativePMap a 0

theorem suzukiTaSmoothCoreShift_zero (a : SuzukiPositiveAperture) (u : SuzukiTaSmoothCore a) :
    suzukiTaSmoothCoreShift a 0 u = suzukiTaSmoothCoreIDeriv a u := by
  apply DFunLike.coe_injective
  funext x
  simp [suzukiTaSmoothCoreShift_apply, suzukiTaSmoothCoreIDeriv_apply]

theorem suzukiTaMinimalDerivative_apply (a : SuzukiPositiveAperture) (u : SuzukiTaSmoothCore a) :
    suzukiTaMinimalDerivative a ((suzukiTaSmoothCoreEquivRange a) u) =
      suzukiTaSmoothCoreToHilbert a (suzukiTaSmoothCoreIDeriv a u) := by
  change suzukiTaShiftedDerivativePMap a 0
    ((suzukiTaSmoothCoreEquivRange a) u) = _
  rw [suzukiTaShiftedDerivativePMap_apply,
    suzukiTaSmoothCoreShiftToHilbert, LinearMap.comp_apply, suzukiTaSmoothCoreShift_zero]

theorem suzukiTaMinimalDerivative_symmetric (a : SuzukiPositiveAperture) :
    (suzukiTaMinimalDerivative a).IsFormalAdjoint (suzukiTaMinimalDerivative a) := by
  intro x y
  let u : SuzukiTaSmoothCore a := (suzukiTaSmoothCoreEquivRange a).symm x
  let v : SuzukiTaSmoothCore a := (suzukiTaSmoothCoreEquivRange a).symm y
  have hx : x = (suzukiTaSmoothCoreEquivRange a) u := by
    exact ((suzukiTaSmoothCoreEquivRange a).apply_symm_apply x).symm
  have hy : y = (suzukiTaSmoothCoreEquivRange a) v := by
    exact ((suzukiTaSmoothCoreEquivRange a).apply_symm_apply y).symm
  rw [hx, hy, suzukiTaMinimalDerivative_apply, suzukiTaMinimalDerivative_apply]
  exact suzukiTaSmoothCoreIDeriv_symmetric a u v

theorem suzukiTaMinimalDerivative_le_adjoint (a : SuzukiPositiveAperture) :
    suzukiTaMinimalDerivative a ≤ (suzukiTaMinimalDerivative a).adjoint :=
  (suzukiTaMinimalDerivative_symmetric a).le_adjoint (dense_suzukiTaShiftedDerivativePMap_domain a 0)

theorem suzukiTaMoment_IDeriv
    (a : SuzukiPositiveAperture) (eps : ℝ) (u : SuzukiTaSmoothCore a) :
    suzukiTaMoment a eps
        (suzukiTaSmoothCoreToHilbert a (suzukiTaSmoothCoreIDeriv a u)) =
      -((eps : ℂ) * I) *
        suzukiTaMoment a eps (suzukiTaSmoothCoreToHilbert a u) := by
  have h := suzukiTaMoment_shift_eq_zero a eps u
  rw [suzukiTaSmoothCoreShiftToHilbert, LinearMap.comp_apply,
    suzukiTaSmoothCoreShift, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.id_coe, id, map_add, map_smul] at h
  rw [map_add, map_smul] at h
  change _ + ((eps : ℂ) * I) * _ = 0 at h
  linear_combination h

def suzukiTaRawDeficiency (a : SuzukiPositiveAperture) (eps : ℝ) :
    SuzukiTaHilbert a :=
  (suzukiTaMoment a eps).adjoint (1 : ℂ)

theorem suzukiTaRawDeficiency_inner
    (a : SuzukiPositiveAperture) (eps : ℝ) (x : SuzukiTaHilbert a) :
    inner ℂ (suzukiTaRawDeficiency a eps) x = suzukiTaMoment a eps x := by
  rw [suzukiTaRawDeficiency, (suzukiTaMoment a eps).adjoint_inner_left]
  simp

theorem suzukiTaRawDeficiency_mem_adjoint
    (a : SuzukiPositiveAperture) (eps : ℝ) :
    suzukiTaRawDeficiency a eps ∈ (suzukiTaMinimalDerivative a).adjoint.domain := by
  apply LinearPMap.mem_adjoint_domain_of_exists
  refine ⟨((eps : ℂ) * I) • suzukiTaRawDeficiency a eps, ?_⟩
  intro x
  let u : SuzukiTaSmoothCore a := (suzukiTaSmoothCoreEquivRange a).symm x
  have hx : x = (suzukiTaSmoothCoreEquivRange a) u := by
    exact ((suzukiTaSmoothCoreEquivRange a).apply_symm_apply x).symm
  rw [hx]
  have hcoe : ((suzukiTaSmoothCoreEquivRange a u :
      LinearMap.range (suzukiTaSmoothCoreToHilbert a)) : SuzukiTaHilbert a) =
      suzukiTaSmoothCoreToHilbert a u := rfl
  rw [hcoe, suzukiTaMinimalDerivative_apply]
  change inner ℂ (((eps : ℂ) * I) • suzukiTaRawDeficiency a eps)
      (suzukiTaSmoothCoreToHilbert a u) =
    inner ℂ (suzukiTaRawDeficiency a eps)
      (suzukiTaSmoothCoreToHilbert a (suzukiTaSmoothCoreIDeriv a u))
  rw [inner_smul_left, suzukiTaRawDeficiency_inner,
    suzukiTaRawDeficiency_inner, suzukiTaMoment_IDeriv]
  simp only [map_mul, Complex.conj_ofReal, conj_I]
  ring

def suzukiTaRawDeficiencyDomain
    (a : SuzukiPositiveAperture) (eps : ℝ) : (suzukiTaMinimalDerivative a).adjoint.domain :=
  ⟨suzukiTaRawDeficiency a eps, suzukiTaRawDeficiency_mem_adjoint a eps⟩

theorem suzukiTa_adjoint_rawDeficiency
    (a : SuzukiPositiveAperture) (eps : ℝ) :
    (suzukiTaMinimalDerivative a).adjoint (suzukiTaRawDeficiencyDomain a eps) =
      ((eps : ℂ) * I) • suzukiTaRawDeficiency a eps := by
  apply LinearPMap.adjoint_apply_eq
    (dense_suzukiTaShiftedDerivativePMap_domain a 0)
  intro x
  let u : SuzukiTaSmoothCore a := (suzukiTaSmoothCoreEquivRange a).symm x
  have hx : x = (suzukiTaSmoothCoreEquivRange a) u := by
    exact ((suzukiTaSmoothCoreEquivRange a).apply_symm_apply x).symm
  rw [hx]
  have hcoe : ((suzukiTaSmoothCoreEquivRange a u :
      LinearMap.range (suzukiTaSmoothCoreToHilbert a)) : SuzukiTaHilbert a) =
      suzukiTaSmoothCoreToHilbert a u := rfl
  have hraw : ((suzukiTaRawDeficiencyDomain a eps :
      (suzukiTaMinimalDerivative a).adjoint.domain) : SuzukiTaHilbert a) =
      suzukiTaRawDeficiency a eps := rfl
  rw [hcoe, suzukiTaMinimalDerivative_apply, hraw]
  change inner ℂ (((eps : ℂ) * I) • suzukiTaRawDeficiency a eps)
      (suzukiTaSmoothCoreToHilbert a u) =
    inner ℂ (suzukiTaRawDeficiency a eps)
      (suzukiTaSmoothCoreToHilbert a (suzukiTaSmoothCoreIDeriv a u))
  rw [inner_smul_left, suzukiTaRawDeficiency_inner,
    suzukiTaRawDeficiency_inner, suzukiTaMoment_IDeriv]
  simp only [map_mul, Complex.conj_ofReal, conj_I]
  ring

theorem suzukiTaRawDeficiency_ne_zero
    (a : SuzukiPositiveAperture) (eps : ℝ) :
    suzukiTaRawDeficiency a eps ≠ 0 :=
  suzukiTaMoment_adjoint_one_ne_zero a eps

def suzukiTaPlusDeficiency (a : SuzukiPositiveAperture) : SuzukiTaHilbert a :=
  (‖suzukiTaRawDeficiency a (-1)‖ : ℂ) • suzukiTaRawDeficiency a 1

def suzukiTaMinusDeficiency (a : SuzukiPositiveAperture) : SuzukiTaHilbert a :=
  (‖suzukiTaRawDeficiency a 1‖ : ℂ) • suzukiTaRawDeficiency a (-1)

theorem suzukiTaPlusDeficiency_ne_zero (a : SuzukiPositiveAperture) : suzukiTaPlusDeficiency a ≠ 0 := by
  apply smul_ne_zero
  · exact_mod_cast norm_ne_zero_iff.mpr (suzukiTaRawDeficiency_ne_zero a (-1))
  · exact suzukiTaRawDeficiency_ne_zero a 1

theorem suzukiTaMinusDeficiency_ne_zero (a : SuzukiPositiveAperture) : suzukiTaMinusDeficiency a ≠ 0 := by
  apply smul_ne_zero
  · exact_mod_cast norm_ne_zero_iff.mpr (suzukiTaRawDeficiency_ne_zero a 1)
  · exact suzukiTaRawDeficiency_ne_zero a (-1)

theorem suzukiTaPlusDeficiency_norm_eq_suzukiTaMinusDeficiency (a : SuzukiPositiveAperture) :
    ‖suzukiTaPlusDeficiency a‖ = ‖suzukiTaMinusDeficiency a‖ := by
  rw [suzukiTaPlusDeficiency, suzukiTaMinusDeficiency, norm_smul, norm_smul]
  simp only [norm_real, Real.norm_eq_abs, abs_norm]
  ring

theorem suzukiTaPlusDeficiency_mem_adjoint (a : SuzukiPositiveAperture) :
    suzukiTaPlusDeficiency a ∈ (suzukiTaMinimalDerivative a).adjoint.domain := by
  exact (suzukiTaMinimalDerivative a).adjoint.domain.smul_mem _
    (suzukiTaRawDeficiency_mem_adjoint a 1)

theorem suzukiTaMinusDeficiency_mem_adjoint (a : SuzukiPositiveAperture) :
    suzukiTaMinusDeficiency a ∈ (suzukiTaMinimalDerivative a).adjoint.domain := by
  exact (suzukiTaMinimalDerivative a).adjoint.domain.smul_mem _
    (suzukiTaRawDeficiency_mem_adjoint a (-1))

def suzukiTaPlusDeficiencyDomain (a : SuzukiPositiveAperture) : (suzukiTaMinimalDerivative a).adjoint.domain :=
  ⟨suzukiTaPlusDeficiency a, suzukiTaPlusDeficiency_mem_adjoint a⟩

def suzukiTaMinusDeficiencyDomain (a : SuzukiPositiveAperture) : (suzukiTaMinimalDerivative a).adjoint.domain :=
  ⟨suzukiTaMinusDeficiency a, suzukiTaMinusDeficiency_mem_adjoint a⟩

theorem suzukiTa_adjoint_plusDeficiency (a : SuzukiPositiveAperture) :
    (suzukiTaMinimalDerivative a).adjoint (suzukiTaPlusDeficiencyDomain a) = I • suzukiTaPlusDeficiency a := by
  rw [suzukiTaPlusDeficiency, suzukiTaPlusDeficiencyDomain]
  change (suzukiTaMinimalDerivative a).adjoint
      ((‖suzukiTaRawDeficiency a (-1)‖ : ℂ) • suzukiTaRawDeficiencyDomain a 1) = _
  rw [LinearPMap.map_smul, suzukiTa_adjoint_rawDeficiency]
  simp
  module

theorem suzukiTa_adjoint_minusDeficiency (a : SuzukiPositiveAperture) :
    (suzukiTaMinimalDerivative a).adjoint (suzukiTaMinusDeficiencyDomain a) = (-I) • suzukiTaMinusDeficiency a := by
  rw [suzukiTaMinusDeficiency, suzukiTaMinusDeficiencyDomain]
  change (suzukiTaMinimalDerivative a).adjoint
      ((‖suzukiTaRawDeficiency a 1‖ : ℂ) • suzukiTaRawDeficiencyDomain a (-1)) = _
  rw [LinearPMap.map_smul, suzukiTa_adjoint_rawDeficiency]
  simp
  module

def suzukiTaBoundaryPhase (theta : ℝ) : ℂ := Complex.exp (I * (theta : ℂ))

@[simp] theorem norm_suzukiTaBoundaryPhase (theta : ℝ) : ‖suzukiTaBoundaryPhase theta‖ = 1 := by
  rw [suzukiTaBoundaryPhase, Complex.norm_exp]
  simp

theorem suzukiTaBoundaryPhase_ne_zero (theta : ℝ) : suzukiTaBoundaryPhase theta ≠ 0 :=
  Complex.exp_ne_zero _

def suzukiTaBoundaryVector (a : SuzukiPositiveAperture) (theta : ℝ) :
    SuzukiTaHilbert a :=
  suzukiTaPlusDeficiency a + suzukiTaBoundaryPhase theta • suzukiTaMinusDeficiency a

theorem suzukiTaBoundaryVector_mem_adjoint
    (a : SuzukiPositiveAperture) (theta : ℝ) :
    suzukiTaBoundaryVector a theta ∈ (suzukiTaMinimalDerivative a).adjoint.domain := by
  exact (suzukiTaMinimalDerivative a).adjoint.domain.add_mem
    (suzukiTaPlusDeficiency_mem_adjoint a)
    ((suzukiTaMinimalDerivative a).adjoint.domain.smul_mem _ (suzukiTaMinusDeficiency_mem_adjoint a))

def suzukiTaBoundaryVectorDomain
    (a : SuzukiPositiveAperture) (theta : ℝ) : (suzukiTaMinimalDerivative a).adjoint.domain :=
  ⟨suzukiTaBoundaryVector a theta, suzukiTaBoundaryVector_mem_adjoint a theta⟩

theorem suzukiTa_adjoint_boundaryVector
    (a : SuzukiPositiveAperture) (theta : ℝ) :
    (suzukiTaMinimalDerivative a).adjoint (suzukiTaBoundaryVectorDomain a theta) =
      I • suzukiTaPlusDeficiency a - I • (suzukiTaBoundaryPhase theta • suzukiTaMinusDeficiency a) := by
  change (suzukiTaMinimalDerivative a).adjoint
      (suzukiTaPlusDeficiencyDomain a + suzukiTaBoundaryPhase theta • suzukiTaMinusDeficiencyDomain a) = _
  rw [LinearPMap.map_add, LinearPMap.map_smul,
    suzukiTa_adjoint_plusDeficiency, suzukiTa_adjoint_minusDeficiency]
  module

theorem suzukiTa_boundaryVector_isotropic
    (a : SuzukiPositiveAperture) (theta : ℝ) :
    inner ℂ
        ((suzukiTaMinimalDerivative a).adjoint (suzukiTaBoundaryVectorDomain a theta))
        (suzukiTaBoundaryVector a theta) =
      inner ℂ (suzukiTaBoundaryVector a theta)
        ((suzukiTaMinimalDerivative a).adjoint (suzukiTaBoundaryVectorDomain a theta)) := by
  rw [suzukiTa_adjoint_boundaryVector, suzukiTaBoundaryVector]
  simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right]
  have hnorm := suzukiTaPlusDeficiency_norm_eq_suzukiTaMinusDeficiency a
  have hphase := norm_suzukiTaBoundaryPhase theta
  have hunit : star (suzukiTaBoundaryPhase theta) * suzukiTaBoundaryPhase theta = 1 := by
    change (starRingEnd ℂ) (suzukiTaBoundaryPhase theta) * suzukiTaBoundaryPhase theta = 1
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hphase]
    norm_num
  have hunit' : suzukiTaBoundaryPhase theta * star (suzukiTaBoundaryPhase theta) = 1 := by
    rw [mul_comm, hunit]
  simp only [map_mul, Complex.star_def, conj_I, map_neg]
  rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ), inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]
  push_cast
  rw [hnorm]
  have hdiag :
      suzukiTaBoundaryPhase theta * I * ((‖suzukiTaMinusDeficiency a‖ : ℝ) : ℂ) ^ 2 *
          star (suzukiTaBoundaryPhase theta) =
        I * ((‖suzukiTaMinusDeficiency a‖ : ℝ) : ℂ) ^ 2 := by
    calc
      _ = I * ((‖suzukiTaMinusDeficiency a‖ : ℝ) : ℂ) ^ 2 *
          (suzukiTaBoundaryPhase theta * star (suzukiTaBoundaryPhase theta)) := by ring
      _ = _ := by rw [hunit']; ring
  linear_combination 2 * hdiag

theorem suzukiTaShiftedDerivativePMap_apply_eq_minimal_add
    (a : SuzukiPositiveAperture) (eps : ℝ)
    (x : (suzukiTaMinimalDerivative a).domain) :
    suzukiTaShiftedDerivativePMap a eps x =
      suzukiTaMinimalDerivative a x + ((eps : ℂ) * I) • (x : SuzukiTaHilbert a) := by
  let v : SuzukiTaSmoothCore a := (suzukiTaSmoothCoreEquivRange a).symm x
  have hx : x = (suzukiTaSmoothCoreEquivRange a) v :=
    ((suzukiTaSmoothCoreEquivRange a).apply_symm_apply x).symm
  rw [hx, suzukiTaShiftedDerivativePMap_apply,
    suzukiTaMinimalDerivative_apply]
  change suzukiTaSmoothCoreToHilbert a (suzukiTaSmoothCoreShift a eps v) =
    suzukiTaSmoothCoreToHilbert a (suzukiTaSmoothCoreIDeriv a v) +
      ((eps : ℂ) * I) • suzukiTaSmoothCoreToHilbert a v
  rw [suzukiTaSmoothCoreShift, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.id_apply, map_add, map_smul]

theorem suzukiTa_plusEigenspace_span
    (a : SuzukiPositiveAperture)
    (x : (suzukiTaMinimalDerivative a).adjoint.domain)
    (hx : (suzukiTaMinimalDerivative a).adjoint x = I • (x : SuzukiTaHilbert a)) :
    ∃ alpha : ℂ, (x : SuzukiTaHilbert a) = alpha • suzukiTaPlusDeficiency a := by
  let T := suzukiTaShiftedDerivativePMap a 1
  have hxT : (x : SuzukiTaHilbert a) ∈ T.adjoint.domain := by
    apply LinearPMap.mem_adjoint_domain_of_exists
    refine ⟨0, ?_⟩
    intro y
    let yS : (suzukiTaMinimalDerivative a).domain := ⟨(y : SuzukiTaHilbert a), y.property⟩
    have hformal := LinearPMap.adjoint_isFormalAdjoint
      (dense_suzukiTaShiftedDerivativePMap_domain a 0) x yS
    change inner ℂ 0 (yS : SuzukiTaHilbert a) = inner ℂ (x : SuzukiTaHilbert a) (T yS)
    rw [suzukiTaShiftedDerivativePMap_apply_eq_minimal_add,
      inner_add_right, inner_smul_right, ← hformal, hx, inner_smul_left]
    simp
  let xT : T.adjoint.domain := ⟨(x : SuzukiTaHilbert a), hxT⟩
  have hxTzero : T.adjoint xT = 0 := by
    apply LinearPMap.adjoint_apply_eq
      (dense_suzukiTaShiftedDerivativePMap_domain a 1)
    intro y
    let yS : (suzukiTaMinimalDerivative a).domain := ⟨(y : SuzukiTaHilbert a), y.property⟩
    have hformal := LinearPMap.adjoint_isFormalAdjoint
      (dense_suzukiTaShiftedDerivativePMap_domain a 0) x yS
    change inner ℂ 0 (yS : SuzukiTaHilbert a) = inner ℂ (x : SuzukiTaHilbert a) (T yS)
    rw [suzukiTaShiftedDerivativePMap_apply_eq_minimal_add,
      inner_add_right, inner_smul_right, ← hformal, hx, inner_smul_left]
    simp
  have hxker : (x : SuzukiTaHilbert a) ∈ T.adjoint.kernel := by
    exact ⟨xT, hxTzero, rfl⟩
  have hspan : T.adjoint.kernel = ℂ ∙ suzukiTaRawDeficiency a 1 := by
    change (suzukiTaShiftedDerivativePMap a 1).adjoint.kernel = _
    rw [suzukiTaShiftedDerivativePMap_adjoint_kernel_eq_moment_orthogonal,
      suzukiTaMoment_kernel_orthogonal_eq_span]
    rfl
  rw [hspan, Submodule.mem_span_singleton] at hxker
  obtain ⟨c, hc⟩ := hxker
  have hk : (‖suzukiTaRawDeficiency a (-1)‖ : ℂ) ≠ 0 := by
    exact_mod_cast norm_ne_zero_iff.mpr (suzukiTaRawDeficiency_ne_zero a (-1))
  refine ⟨c / (‖suzukiTaRawDeficiency a (-1)‖ : ℂ), ?_⟩
  rw [← hc, suzukiTaPlusDeficiency]
  rw [smul_smul]
  congr 1
  field_simp

theorem suzukiTa_minusEigenspace_span
    (a : SuzukiPositiveAperture)
    (x : (suzukiTaMinimalDerivative a).adjoint.domain)
    (hx : (suzukiTaMinimalDerivative a).adjoint x = (-I) • (x : SuzukiTaHilbert a)) :
    ∃ beta : ℂ, (x : SuzukiTaHilbert a) = beta • suzukiTaMinusDeficiency a := by
  let T := suzukiTaShiftedDerivativePMap a (-1)
  have hxT : (x : SuzukiTaHilbert a) ∈ T.adjoint.domain := by
    apply LinearPMap.mem_adjoint_domain_of_exists
    refine ⟨0, ?_⟩
    intro y
    let yS : (suzukiTaMinimalDerivative a).domain := ⟨(y : SuzukiTaHilbert a), y.property⟩
    have hformal := LinearPMap.adjoint_isFormalAdjoint
      (dense_suzukiTaShiftedDerivativePMap_domain a 0) x yS
    change inner ℂ 0 (yS : SuzukiTaHilbert a) = inner ℂ (x : SuzukiTaHilbert a) (T yS)
    rw [suzukiTaShiftedDerivativePMap_apply_eq_minimal_add,
      inner_add_right, inner_smul_right, ← hformal, hx, inner_smul_left]
    simp
  let xT : T.adjoint.domain := ⟨(x : SuzukiTaHilbert a), hxT⟩
  have hxTzero : T.adjoint xT = 0 := by
    apply LinearPMap.adjoint_apply_eq
      (dense_suzukiTaShiftedDerivativePMap_domain a (-1))
    intro y
    let yS : (suzukiTaMinimalDerivative a).domain := ⟨(y : SuzukiTaHilbert a), y.property⟩
    have hformal := LinearPMap.adjoint_isFormalAdjoint
      (dense_suzukiTaShiftedDerivativePMap_domain a 0) x yS
    change inner ℂ 0 (yS : SuzukiTaHilbert a) = inner ℂ (x : SuzukiTaHilbert a) (T yS)
    rw [suzukiTaShiftedDerivativePMap_apply_eq_minimal_add,
      inner_add_right, inner_smul_right, ← hformal, hx, inner_smul_left]
    simp
  have hxker : (x : SuzukiTaHilbert a) ∈ T.adjoint.kernel := ⟨xT, hxTzero, rfl⟩
  have hspan : T.adjoint.kernel = ℂ ∙ suzukiTaRawDeficiency a (-1) := by
    change (suzukiTaShiftedDerivativePMap a (-1)).adjoint.kernel = _
    rw [suzukiTaShiftedDerivativePMap_adjoint_kernel_eq_moment_orthogonal,
      suzukiTaMoment_kernel_orthogonal_eq_span]
    rfl
  rw [hspan, Submodule.mem_span_singleton] at hxker
  obtain ⟨c, hc⟩ := hxker
  have hk : (‖suzukiTaRawDeficiency a 1‖ : ℂ) ≠ 0 := by
    exact_mod_cast norm_ne_zero_iff.mpr (suzukiTaRawDeficiency_ne_zero a 1)
  refine ⟨c / (‖suzukiTaRawDeficiency a 1‖ : ℂ), ?_⟩
  rw [← hc, suzukiTaMinusDeficiency]
  rw [smul_smul]
  congr 1
  field_simp

/-- Suzuki's concrete von Neumann extension on the actual energy space `H(T_a)`. -/
noncomputable def suzukiTaSelfAdjointExtension
    (a : SuzukiPositiveAperture) (theta : ℝ) :
    SuzukiTaHilbert a →ₗ.[ℂ] SuzukiTaHilbert a :=
  LinearPMap.deficiencyExtension
    (dense_suzukiTaShiftedDerivativePMap_domain a 0)
    (suzukiTaMinimalDerivative_symmetric a)
    (suzukiTaPlusDeficiencyDomain a) (suzukiTaMinusDeficiencyDomain a)
    (suzukiTaBoundaryPhase theta)

theorem suzukiTaSelfAdjointExtension_isSelfAdjoint
    (a : SuzukiPositiveAperture) (theta : ℝ) :
    IsSelfAdjoint (suzukiTaSelfAdjointExtension a theta) := by
  exact LinearPMap.deficiencyExtension_isSelfAdjoint
    (dense_suzukiTaShiftedDerivativePMap_domain a 0)
    (suzukiTaMinimalDerivative_symmetric a)
    (suzukiTa_adjoint_plusDeficiency a)
    (suzukiTa_adjoint_minusDeficiency a)
    (suzukiTaPlusDeficiency_ne_zero a)
    (suzukiTaPlusDeficiency_norm_eq_suzukiTaMinusDeficiency a)
    (norm_suzukiTaBoundaryPhase theta)
    (suzukiTa_plusEigenspace_span a)
    (suzukiTa_minusEigenspace_span a)

/-- Complex exponential representing evaluation at the conjugate spectral point. -/
def suzukiTaSpectralExponentialContinuous
    (a : SuzukiPositiveAperture) (z : ℂ) :
    C(SuzukiApertureInterval a.1, ℂ) where
  toFun x := Complex.exp (-I * z * ((x : ℝ) : ℂ))
  continuous_toFun := by fun_prop

def suzukiTaSpectralExponentialL2
    (a : SuzukiPositiveAperture) (z : ℂ) :
    SuzukiApertureIntervalL2 a.1 :=
  ContinuousMap.toLp 2 volume ℂ (suzukiTaSpectralExponentialContinuous a z)

/-- Riesz functional `u ↦ ∫ exp(i conj(z) x) u(x) dx` on the actual energy space. -/
def suzukiTaSpectralMoment (a : SuzukiPositiveAperture) (z : ℂ) :
    SuzukiTaHilbert a →L[ℂ] ℂ :=
  (innerSL ℂ (suzukiTaSpectralExponentialL2 a z)).comp
    (suzukiTaPhysicalEmbedding a)

theorem suzukiTaSpectralMoment_smoothCore_eq_integral
    (a : SuzukiPositiveAperture) (z : ℂ) (u : SuzukiTaSmoothCore a) :
    suzukiTaSpectralMoment a z (suzukiTaSmoothCoreToHilbert a u) =
      ∫ x : ℝ, Complex.exp (I * star z * (x : ℂ)) * u x := by
  rw [suzukiTaSpectralMoment, ContinuousLinearMap.comp_apply]
  change inner ℂ (suzukiTaSpectralExponentialL2 a z)
      (suzukiTaPhysicalEmbedding a (suzukiTaSmoothCoreToHilbert a u)) = _
  rw [MeasureTheory.L2.inner_def]
  calc
    (∫ x : SuzukiApertureInterval a.1,
        inner ℂ
          ((suzukiTaSpectralExponentialL2 a z :
            SuzukiApertureInterval a.1 → ℂ) x)
          ((suzukiTaPhysicalEmbedding a
            (suzukiTaSmoothCoreToHilbert a u) :
              SuzukiApertureInterval a.1 → ℂ) x)) =
        ∫ x : SuzukiApertureInterval a.1,
          Complex.exp (I * star z * ((x : ℝ) : ℂ)) * u (x : ℝ) := by
      apply integral_congr_ae
      filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume
          (suzukiTaSpectralExponentialContinuous a z),
        suzukiTaPhysicalEmbedding_smoothCore_ae a u] with x he hu
      change inner ℂ
        ((ContinuousMap.toLp 2 volume ℂ
          (suzukiTaSpectralExponentialContinuous a z) :
            SuzukiApertureInterval a.1 → ℂ) x)
        ((suzukiTaPhysicalEmbedding a
          (suzukiTaSmoothCoreToHilbert a u) :
            SuzukiApertureInterval a.1 → ℂ) x) = _
      rw [he, hu]
      simp only [suzukiTaSpectralExponentialContinuous, RCLike.inner_apply]
      change u (x : ℝ) *
        (starRingEnd ℂ) (Complex.exp (-I * z * ((x : ℝ) : ℂ))) = _
      rw [← Complex.exp_conj]
      simp only [map_mul, map_neg, conj_I, Complex.conj_ofReal]
      have hexp : Complex.exp
          (- -I * (starRingEnd ℂ) z * (((x : ℝ) : ℂ))) =
          Complex.exp (I * star z * (((x : ℝ) : ℂ))) := by
        congr 1
        ring
      rw [hexp, mul_comm]
    _ = ∫ x in Icc (-a.1) a.1,
        Complex.exp (I * star z * (x : ℂ)) * u x := by
      simpa only [SuzukiApertureInterval] using
        (MeasureTheory.integral_subtype measurableSet_Icc
          (fun x : ℝ => Complex.exp (I * star z * (x : ℂ)) * u x))
    _ = ∫ x : ℝ, Complex.exp (I * star z * (x : ℂ)) * u x := by
      apply MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hxt : x ∉ tsupport (u : ℝ → ℂ) := by
        intro hmem
        exact hx (Ioo_subset_Icc_self (u.tsupport_subset hmem))
      rw [image_eq_zero_of_notMem_tsupport hxt, mul_zero]

def suzukiTaSpectralMomentNormalizer
    (a : SuzukiPositiveAperture) (z : ℂ) : SuzukiTaSmoothCore a where
  toFun x := Complex.exp (-I * star z * (x : ℂ)) *
    (suzukiTaUnitIntegralBump a x : ℂ)
  contDiff' := by
    have harg : ContDiff ℝ (⊤ : ℕ∞)
        (fun x : ℝ => -I * star z * (x : ℂ)) := by
      exact contDiff_const.mul Complex.ofRealCLM.contDiff
    have hexp : ContDiff ℝ (⊤ : ℕ∞)
        (fun x : ℝ => Complex.exp (-I * star z * (x : ℂ))) := by
      exact harg.cexp
    exact hexp.mul
      (Complex.ofRealCLM.contDiff.comp (suzukiTaUnitIntegralBump_smooth a))
  hasCompactSupport' := by
    refine HasCompactSupport.intro (suzukiTaUnitIntegralBump_compact a) ?_
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport hx]
    simp
  tsupport_subset' := by
    refine (closure_minimal ?_ (isClosed_tsupport (suzukiTaUnitIntegralBump a))).trans
      (suzukiTaUnitIntegralBump_tsupport a)
    intro x hx
    apply subset_closure
    intro hb
    exact hx (by simp [hb])

theorem suzukiTaSpectralMoment_normalizer
    (a : SuzukiPositiveAperture) (z : ℂ) :
    suzukiTaSpectralMoment a z
      (suzukiTaSmoothCoreToHilbert a (suzukiTaSpectralMomentNormalizer a z)) = 1 := by
  rw [suzukiTaSpectralMoment_smoothCore_eq_integral]
  have hfun : (fun x : ℝ => Complex.exp (I * star z * (x : ℂ)) *
      suzukiTaSpectralMomentNormalizer a z x) =
      fun x => (suzukiTaUnitIntegralBump a x : ℂ) := by
    funext x
    change Complex.exp (I * star z * (x : ℂ)) *
        (Complex.exp (-I * star z * (x : ℂ)) *
          (suzukiTaUnitIntegralBump a x : ℂ)) = _
    rw [← mul_assoc, ← Complex.exp_add]
    have : I * star z * (x : ℂ) + -I * star z * (x : ℂ) = 0 := by ring
    rw [this, Complex.exp_zero, one_mul]
  have hi : (∫ x : ℝ, (suzukiTaUnitIntegralBump a x : ℂ)) =
      Complex.ofReal (∫ x : ℝ, suzukiTaUnitIntegralBump a x) := by
    exact integral_ofReal (𝕜 := ℂ)
  rw [hfun, hi, integral_suzukiTaUnitIntegralBump]
  norm_num

theorem suzukiTaSpectralMoment_IDeriv
    (a : SuzukiPositiveAperture) (z : ℂ) (u : SuzukiTaSmoothCore a) :
    suzukiTaSpectralMoment a z
        (suzukiTaSmoothCoreToHilbert a (suzukiTaSmoothCoreIDeriv a u)) =
      star z * suzukiTaSpectralMoment a z (suzukiTaSmoothCoreToHilbert a u) := by
  rw [suzukiTaSpectralMoment_smoothCore_eq_integral,
    suzukiTaSpectralMoment_smoothCore_eq_integral]
  let F : ℝ → ℂ := fun x => Complex.exp (I * star z * (x : ℂ)) * u x
  have hF : ContDiff ℝ 1 F := by
    have harg : ContDiff ℝ 1
        (fun x : ℝ => I * star z * (x : ℂ)) := by
      exact contDiff_const.mul Complex.ofRealCLM.contDiff
    have hexp : ContDiff ℝ 1
        (fun x : ℝ => Complex.exp (I * star z * (x : ℂ))) := by
      exact harg.cexp
    exact hexp.mul (u.contDiff.of_le (by simp))
  have hFc : HasCompactSupport F := u.hasCompactSupport.mul_left
  have hzero : (∫ x : ℝ, deriv F x) = 0 :=
    integral_complex_deriv_eq_zero_of_hasCompactSupport hF hFc
  have hFint : Integrable F := hF.continuous.integrable_of_hasCompactSupport hFc
  have hderivInt : Integrable (deriv F) :=
    (hF.continuous_deriv (by simp)).integrable_of_hasCompactSupport hFc.deriv
  have hderiv : ∀ x : ℝ, deriv F x =
      (I * star z) * Complex.exp (I * star z * (x : ℂ)) * u x +
        Complex.exp (I * star z * (x : ℂ)) * deriv u x := by
    intro x
    dsimp only [F]
    have hexp : HasDerivAt
        (fun y : ℝ => Complex.exp (I * star z * (y : ℂ)))
        ((I * star z) * Complex.exp (I * star z * (x : ℂ))) x := by
      convert hasDerivAt_cexp_const_mul (I * star z) x using 1 <;> ring
    exact (hexp.mul (u.contDiff.differentiable (by simp) x).hasDerivAt).deriv
  have hpoint : (fun x : ℝ =>
      Complex.exp (I * star z * (x : ℂ)) *
        suzukiTaSmoothCoreIDeriv a u x) =
      fun x => I * (deriv F x -
        (I * star z) * Complex.exp (I * star z * (x : ℂ)) * u x) := by
    funext x
    rw [suzukiTaSmoothCoreIDeriv_apply, hderiv]
    ring
  have hfactor : (fun x : ℝ =>
      I * star z * Complex.exp (I * star z * (x : ℂ)) * u x) =
      fun x : ℝ => (I * star z) *
        (Complex.exp (I * star z * (x : ℂ)) * u x) := by
    funext x
    ring
  have hfactorInt : Integrable (fun x : ℝ =>
      I * star z * Complex.exp (I * star z * (x : ℂ)) * u x) := by
    rw [hfactor]
    exact hFint.const_mul (I * star z)
  rw [hpoint, integral_const_mul, integral_sub hderivInt hfactorInt,
    hzero, zero_sub]
  rw [hfactor, integral_const_mul]
  rw [mul_neg]
  have hII : I * (I * star z) = -(star z) := by
    rw [← mul_assoc, Complex.I_mul_I]
    simp
  rw [hII]
  ring

end RHTower
