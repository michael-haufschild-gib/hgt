import GaloisForLFunctions.RHTower.OddSectorGroundDivisionOperator
import GaloisForLFunctions.RHTower.CCMRestrictedWeilGroundDerivativeCriterion

/-!
# Symmetric division and the exact odd ground radical

Imaginary-anchor squared-frequency division is symmetric for the full
arithmetic-corrected form, including its pole term. Smooth source density
shows that multiplication by squared frequency preserves the actual ground
space whenever the product belongs to the same complete form domain.
-/

open Complex MeasureTheory Set Filter Topology
open scoped InnerProduct ComplexConjugate
noncomputable section
namespace RHTower.OddSector
open GaloisForLFunctions.HTGeometry.FourierLaplaceDivision
open CCMRealRootedGround CCMGroundStructure CCMGroundQuadrature CCMGroundDerivative

theorem arithmeticShiftedForm_ground_left (a : SuzukiPositiveAperture)
    {G : CCMArchimedeanFormDomain a} (hG : G ∈ oddArithmeticGroundSpace a)
    (u : CCMArchimedeanFormDomain a) : arithmeticShiftedForm a G u = 0 := by
  rw [arithmeticShiftedForm,(mem_arithmeticGroundSpace_iff a G).mp hG.1 u,sub_self]

theorem arithmeticShiftedForm_ground_right (a : SuzukiPositiveAperture)
    {G : CCMArchimedeanFormDomain a} (hG : G ∈ oddArithmeticGroundSpace a)
    (u : CCMArchimedeanFormDomain a) : arithmeticShiftedForm a u G = 0 := by
  rw [arithmeticShiftedForm_conj,arithmeticShiftedForm_ground_left a hG,map_zero]

theorem arithmeticShiftedForm_continuous_right (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) : Continuous (arithmeticShiftedForm a u) := by
  unfold arithmeticShiftedForm arithmeticForm
  exact ((continuous_const.inner continuous_id).add
    (continuous_const.inner (ccmArchimedeanFormToAperture a).continuous)).sub
      (continuous_const.mul (continuous_const.inner
        (ccmArchimedeanFormToAperture a).continuous))

private theorem oddPart_eq_self (a : SuzukiPositiveAperture)
    {u : CCMArchimedeanFormDomain a} (hu : ccmArchimedeanFormReflection a u = -u) :
    ccmRestrictedWeilOddPart a u = u := by
  rw [ccmRestrictedWeilOddPart,hu,sub_neg_eq_add,← two_smul ℂ u,smul_smul,
    inv_mul_cancel₀ (two_ne_zero : (2 : ℂ) ≠ 0),one_smul]

private theorem input_pair_left (a : SuzukiPositiveAperture)
    {G : CCMArchimedeanFormDomain a} (hG : IsOddArithmeticGroundGenerator a G)
    (z : ℂ) {u : CCMArchimedeanFormDomain a}
    (hu : ccmArchimedeanFormReflection a u = -u) (v : CCMArchimedeanFormDomain a) :
    arithmeticShiftedForm a (groundDivisionInput a G z u) v = arithmeticShiftedForm a u v := by
  rw [groundDivisionInput,oddPart_eq_self a hu,arithmeticShiftedForm_sub_left,
    arithmeticShiftedForm_smul_left,arithmeticShiftedForm_ground_left a hG.1,mul_zero,sub_zero]

private theorem input_pair_right (a : SuzukiPositiveAperture)
    {G : CCMArchimedeanFormDomain a} (hG : IsOddArithmeticGroundGenerator a G)
    (z : ℂ) (u : CCMArchimedeanFormDomain a) {v : CCMArchimedeanFormDomain a}
    (hv : ccmArchimedeanFormReflection a v = -v) :
    arithmeticShiftedForm a u (groundDivisionInput a G z v) = arithmeticShiftedForm a u v := by
  rw [arithmeticShiftedForm_conj,input_pair_left a hG z hv,arithmeticShiftedForm_conj,
    Complex.conj_conj]

/-- Symmetry holds for the full signed arithmetic-corrected form. -/
theorem groundDivisionCLM_symmetric_form (a : SuzukiPositiveAperture)
    {G : CCMArchimedeanFormDomain a} (hG : IsOddArithmeticGroundGenerator a G)
    (b : ℝ) (hb : 0 < b)
    (hz : unitaryLaplace (timeRep a G) (I*(b : ℂ)) ≠ 0)
    {u v : CCMArchimedeanFormDomain a}
    (hu : ccmArchimedeanFormReflection a u = -u)
    (hv : ccmArchimedeanFormReflection a v = -v) :
    arithmeticShiftedForm a u (groundDivisionCLM a hG b hb hz v) =
      arithmeticShiftedForm a (groundDivisionCLM a hG b hb hz u) v := by
  have hc : conj ((I*(b : ℂ))^2) = (I*(b : ℂ))^2 := by
    simp only [map_pow,map_mul,Complex.conj_I,Complex.conj_ofReal,neg_mul,neg_sq]
  rw [groundDivisionCLM_apply,groundDivisionCLM_apply]
  have hz0 : I*(b : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr hb.ne')
  have h := arithmeticShiftedForm_quadratic_transfer a
    (groundDivisionInput a G (I*(b : ℂ)) u)
    (groundDivisionInput a G (I*(b : ℂ)) v) _ _ hc
    (groundDivision_factor a hG hz0 hz u) (groundDivision_factor a hG hz0 hz v)
  rwa [input_pair_left a hG _ hu,input_pair_right a hG _ _ hv] at h

theorem groundDivisionCLM_odd (a : SuzukiPositiveAperture)
    {G : CCMArchimedeanFormDomain a} (hG : IsOddArithmeticGroundGenerator a G)
    (b : ℝ) (hb : 0 < b)
    (hz : unitaryLaplace (timeRep a G) (I*(b : ℂ)) ≠ 0)
    (u : CCMArchimedeanFormDomain a) :
    ccmArchimedeanFormReflection a (groundDivisionCLM a hG b hb hz u) =
      -groundDivisionCLM a hG b hb hz u := by
  rw [groundDivisionCLM_apply]
  exact groundDivision_odd a hG _ hz u

/-- Normalized division descends to the quotient by the actual ground space. -/
theorem groundDivisionCLM_ground (a : SuzukiPositiveAperture)
    {G : CCMArchimedeanFormDomain a} (hG : IsOddArithmeticGroundGenerator a G)
    (b : ℝ) (hb : 0 < b)
    (hz : unitaryLaplace (timeRep a G) (I*(b : ℂ)) ≠ 0)
    {u : CCMArchimedeanFormDomain a} (hu : u ∈ oddArithmeticGroundSpace a) :
    groundDivisionCLM a hG b hb hz u ∈ oddArithmeticGroundSpace a := by
  apply (mem_oddArithmeticGroundSpace_iff a _).mpr
  refine ⟨groundDivisionCLM_odd a hG b hb hz u,?_⟩
  have he := groundDivisionCLM_symmetric_form a hG b hb hz hu.2
    (groundDivisionCLM_odd a hG b hb hz u)
  rw [arithmeticShiftedForm_ground_left a hu] at he
  rw [← he,Complex.zero_re]

/-- Squared-frequency multiplication preserves ground membership whenever
the product is an actual same-aperture odd form vector. -/
theorem oddArithmeticGround_mul_sq (a : SuzukiPositiveAperture)
    {G v : CCMArchimedeanFormDomain a} (hG : G ∈ oddArithmeticGroundSpace a)
    (hv : ccmArchimedeanFormReflection a v = -v)
    (hfac : ∀ w : ℂ, unitaryLaplace (timeRep a v) w =
      w^2*unitaryLaplace (timeRep a G) w) :
    v ∈ oddArithmeticGroundSpace a := by
  have hsmooth (u : CCMComplexSmoothInteriorSource a) :
      arithmeticShiftedForm a v u.toCCMFormVector = 0 := by
    let k : CCMArchimedeanFormDomain a :=
      ((2*Real.pi*I : ℂ)^2)⁻¹ •
        (derivSource a (derivSource a u)).toCCMFormVector
    have hk (w : ℂ) : unitaryLaplace (timeRep a k) w =
        w^2*unitaryLaplace (timeRep a u.toCCMFormVector) w := by
      dsimp only [k]
      rw [unitaryLaplace_timeRep_smul,unitaryLaplace_timeRep_source,
        unitaryLaplace_timeRep_source]
      change ((2*Real.pi*I : ℂ)^2)⁻¹ *
        unitaryLaplace (deriv (derivSource a u)) w = _
      rw [unitaryLaplace_deriv]
      change ((2*Real.pi*I : ℂ)^2)⁻¹ *
        (2*Real.pi*I*w*unitaryLaplace (deriv u) w) = _
      rw [unitaryLaplace_deriv]
      field_simp
    have he := arithmeticShiftedForm_quadratic_transfer a v k G u.toCCMFormVector
      (c := 0) (map_zero conj) (fun w => by simpa using hfac w)
      (fun w => by simpa using hk w)
    rw [he,arithmeticShiftedForm_ground_left a hG]
  have heq : arithmeticShiftedForm a v = fun _ => (0 : ℂ) := by
    apply Continuous.ext_on (denseRange_ccmComplexSmoothInteriorSource_toCCMFormVector a)
      (arithmeticShiftedForm_continuous_right a v) continuous_const
    rintro _ ⟨u,rfl⟩
    exact hsmooth u
  exact (mem_oddArithmeticGroundSpace_iff a v).mpr
    ⟨hv,congrArg Complex.re (congrFun heq v)⟩

end RHTower.OddSector
