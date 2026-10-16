import GaloisForLFunctions.RHTower.OddSectorExactDualAttainment
import GaloisForLFunctions.RHTower.CCMRestrictedWeilPolarGroundParityForcing
import GaloisForLFunctions.RHTower.ChronologicalLeastNormMomentRepair

/-!
# The blind odd minimum as an actual arithmetic-corrected eigenstate

The exact finite multipliers define a bounded self-adjoint arithmetic
correction. The shifted corrected form is nonnegative on the odd sector.
Every blind minimizer annihilates this form. Reflection extends the resulting
equation from odd variations to the entire form domain, so the physical source
belongs to the represented operator domain and is an actual eigenvector.
-/

open Complex MeasureTheory Set Filter Topology
open scoped InnerProduct
noncomputable section
namespace RHTower.OddSector
open EvenSector WeilOneSided GaloisForLFunctions.HTGeometry

/-- The finite correction uses precisely the strictly active integer lags. -/
def arithmeticCorrection (a : SuzukiPositiveAperture) :
    suzukiApertureHilbert a →L[ℂ] suzukiApertureHilbert a :=
  ∑ j : apertureNodes a,(blindMultiplier a j : ℂ) • ccmPrimeTransportOperator a j.1

theorem arithmeticCorrection_isSelfAdjoint (a : SuzukiPositiveAperture) :
    IsSelfAdjoint (arithmeticCorrection a) := by
  classical
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  unfold arithmeticCorrection
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  have h := ccmPrimeTransportOperator_isSelfAdjoint a j.1
  rw [ContinuousLinearMap.isSelfAdjoint_iff'] at h
  rw [ContinuousLinearMap.adjoint.map_smulₛₗ,Complex.conj_ofReal,h]

theorem inner_arithmeticCorrection (a : SuzukiPositiveAperture)
    (f g : suzukiApertureHilbert a) :
    inner ℂ (arithmeticCorrection a f) g =
      ∑ j : apertureNodes a,(blindMultiplier a j : ℂ) *
        inner ℂ (ccmPrimeTransportOperator a j.1 f) g := by
  simp [arithmeticCorrection]

theorem arithmeticCorrection_diagonal (a : SuzukiPositiveAperture) (u : OddFormSource a) :
    (inner ℂ (arithmeticCorrection a (ccmArchimedeanFormToAperture a u.1))
      (ccmArchimedeanFormToAperture a u.1)).re =
        ∑ j : apertureNodes a,blindMultiplier a j * formTrace u j.1 := by
  rw [inner_arithmeticCorrection,Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [inner_ccmPrimeTransportOperator,formTrace_apply]
  simp only [formLogValue,formProfile,energyProfile,ccmApertureCorrelation,neg_neg,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
    div_eq_mul_inv,one_mul,Complex.add_re]
  ring

def arithmeticRemainder (a : SuzukiPositiveAperture) :
    suzukiApertureHilbert a →L[ℂ] suzukiApertureHilbert a :=
  ccmRestrictedWeilBoundedRemainder a - arithmeticCorrection a

theorem arithmeticRemainder_isSelfAdjoint (a : SuzukiPositiveAperture) :
    IsSelfAdjoint (arithmeticRemainder a) :=
  (ccmRestrictedWeilBoundedRemainder_isSelfAdjoint a).sub
    (arithmeticCorrection_isSelfAdjoint a)

def arithmeticForm (a : SuzukiPositiveAperture)
    (u v : CCMArchimedeanFormDomain a) : ℂ :=
  inner ℂ u v + inner ℂ (arithmeticRemainder a (ccmArchimedeanFormToAperture a u))
    (ccmArchimedeanFormToAperture a v)

theorem arithmeticForm_eq (a : SuzukiPositiveAperture)
    (u v : CCMArchimedeanFormDomain a) :
    arithmeticForm a u v = ccmRestrictedWeilForm a u v -
      inner ℂ (arithmeticCorrection a (ccmArchimedeanFormToAperture a u))
        (ccmArchimedeanFormToAperture a v) := by
  simp only [arithmeticForm,arithmeticRemainder,ContinuousLinearMap.sub_apply,
    inner_sub_left,ccmRestrictedWeilForm]
  ring

theorem arithmeticForm_diagonal (a : SuzukiPositiveAperture) (u : OddFormSource a) :
    (arithmeticForm a u.1 u.1).re =
      formEnergy u - ∑ j : apertureNodes a,blindMultiplier a j * formTrace u j.1 := by
  rw [arithmeticForm_eq,Complex.sub_re,ccmRestrictedWeilForm_self_re_eq_source,
    arithmeticCorrection_diagonal]
  rfl

def arithmeticShiftedForm (a : SuzukiPositiveAperture)
    (u v : CCMArchimedeanFormDomain a) : ℂ :=
  arithmeticForm a u v - (blindMinimum a : ℂ) *
    inner ℂ (ccmArchimedeanFormToAperture a u) (ccmArchimedeanFormToAperture a v)

theorem arithmeticShiftedForm_add_left (a : SuzukiPositiveAperture)
    (u v w : CCMArchimedeanFormDomain a) :
    arithmeticShiftedForm a (u + v) w =
      arithmeticShiftedForm a u w + arithmeticShiftedForm a v w := by
  simp only [arithmeticShiftedForm,arithmeticForm,map_add,inner_add_left]
  ring

theorem arithmeticShiftedForm_add_right (a : SuzukiPositiveAperture)
    (u v w : CCMArchimedeanFormDomain a) :
    arithmeticShiftedForm a u (v + w) =
      arithmeticShiftedForm a u v + arithmeticShiftedForm a u w := by
  simp only [arithmeticShiftedForm,arithmeticForm,map_add,inner_add_right]
  ring

theorem arithmeticShiftedForm_sub_right (a : SuzukiPositiveAperture)
    (u v w : CCMArchimedeanFormDomain a) :
    arithmeticShiftedForm a u (v - w) =
      arithmeticShiftedForm a u v - arithmeticShiftedForm a u w := by
  simp only [arithmeticShiftedForm,arithmeticForm,map_sub,inner_sub_right]
  ring

theorem arithmeticShiftedForm_neg_left (a : SuzukiPositiveAperture)
    (u v : CCMArchimedeanFormDomain a) :
    arithmeticShiftedForm a (-u) v = -arithmeticShiftedForm a u v := by
  simp only [arithmeticShiftedForm,arithmeticForm,map_neg,inner_neg_left]
  ring

theorem arithmeticShiftedForm_smul_left (a : SuzukiPositiveAperture)
    (u v : CCMArchimedeanFormDomain a) (c : ℂ) :
    arithmeticShiftedForm a (c • u) v = conj c * arithmeticShiftedForm a u v := by
  simp only [arithmeticShiftedForm,arithmeticForm,map_smul,inner_smul_left]
  ring

theorem arithmeticShiftedForm_smul_right (a : SuzukiPositiveAperture)
    (u v : CCMArchimedeanFormDomain a) (c : ℂ) :
    arithmeticShiftedForm a u (c • v) = c * arithmeticShiftedForm a u v := by
  simp only [arithmeticShiftedForm,arithmeticForm,map_smul,inner_smul_right]
  ring

theorem arithmeticShiftedForm_conj (a : SuzukiPositiveAperture)
    (u v : CCMArchimedeanFormDomain a) :
    arithmeticShiftedForm a v u = conj (arithmeticShiftedForm a u v) := by
  simp only [arithmeticShiftedForm,arithmeticForm,map_sub,map_add,map_mul,Complex.conj_ofReal]
  rw [inner_conj_symm u v,inner_conj_symm (ccmArchimedeanFormToAperture a u)
    (ccmArchimedeanFormToAperture a v),inner_conj_symm]
  rw [(arithmeticRemainder_isSelfAdjoint a).isSymmetric]

theorem arithmeticShiftedForm_diagonal (a : SuzukiPositiveAperture) (u : OddFormSource a) :
    (arithmeticShiftedForm a u.1 u.1).re =
      formEnergy u - (∑ j : apertureNodes a,blindMultiplier a j * formTrace u j.1) -
        blindMinimum a * ‖ccmArchimedeanFormToAperture a u.1‖ ^ 2 := by
  rw [arithmeticShiftedForm,Complex.sub_re,arithmeticForm_diagonal,
    inner_self_eq_norm_sq_to_K]
  simp

theorem arithmeticShiftedForm_odd_nonneg (a : SuzukiPositiveAperture) (u : OddFormSource a) :
    0 ≤ (arithmeticShiftedForm a u.1 u.1).re := by
  rw [arithmeticShiftedForm_diagonal]
  linarith [blindMultiplier_spec a u]

theorem formTrace_blind (a : SuzukiPositiveAperture) (u : BlindUnitSource a) :
    formTrace (⟨u.1,u.2.1⟩ : OddFormSource a) = 0 := by
  ext j
  rw [formTrace_apply]
  change (energyProfile a (ccmArchimedeanFormToAperture a u.1) (Real.log j) +
    energyProfile a (ccmArchimedeanFormToAperture a u.1) (-Real.log j)).re / Real.sqrt j = 0
  rw [energyProfile_odd u.2.1,u.2.2.2 j]
  simp

private theorem arithmeticShiftedForm_ground_diagonal (a : SuzukiPositiveAperture)
    (u : BlindUnitSource a) (hu : ccmRestrictedWeilSourceQuadratic a u.1 = blindMinimum a) :
    (arithmeticShiftedForm a u.1 u.1).re = 0 := by
  rw [arithmeticShiftedForm_diagonal a ⟨u.1,u.2.1⟩,formTrace_blind]
  simp [formEnergy,hu,u.2.2.1]

private theorem arithmeticShiftedForm_ground_odd (a : SuzukiPositiveAperture)
    (u : BlindUnitSource a) (hu : ccmRestrictedWeilSourceQuadratic a u.1 = blindMinimum a)
    (v : CCMArchimedeanFormDomain a) (hv : ccmArchimedeanFormReflection a v = -v) :
    arithmeticShiftedForm a u.1 v = 0 := by
  have hu0 := arithmeticShiftedForm_ground_diagonal a u hu
  have hexp (w : CCMArchimedeanFormDomain a) (t : ℝ) :
      (arithmeticShiftedForm a (u.1 + (t : ℂ) • w) (u.1 + (t : ℂ) • w)).re =
        2 * t * (arithmeticShiftedForm a u.1 w).re +
          t ^ 2 * (arithmeticShiftedForm a w w).re := by
    rw [arithmeticShiftedForm_add_left,arithmeticShiftedForm_add_right,
      arithmeticShiftedForm_add_right,arithmeticShiftedForm_smul_left,
      arithmeticShiftedForm_smul_left,arithmeticShiftedForm_smul_right,
      arithmeticShiftedForm_smul_right,arithmeticShiftedForm_conj a u.1 w]
    simp only [Complex.add_re,Complex.mul_re,Complex.conj_ofReal,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,sub_zero,Complex.conj_re,Complex.conj_im,hu0]
    ring
  have hre (w : CCMArchimedeanFormDomain a) (hw : ccmArchimedeanFormReflection a w = -w) :
      (arithmeticShiftedForm a u.1 w).re = 0 := by
    apply eq_zero_of_forall_quadratic_nonneg (arithmeticShiftedForm_odd_nonneg a ⟨w,hw⟩)
    intro t
    rw [← hexp]
    apply arithmeticShiftedForm_odd_nonneg a ⟨u.1 + (t : ℂ) • w,?_⟩
    rw [map_add,map_smul,u.2.1,hw,smul_neg,neg_add]
  apply Complex.ext
  · exact hre v hv
  · have hi := hre (I • v) (by rw [map_smul,hv,smul_neg])
    rw [arithmeticShiftedForm_smul_right] at hi
    simpa only [Complex.mul_re,Complex.I_re,zero_mul,Complex.I_im,one_mul,
      zero_sub,neg_eq_zero,Complex.zero_im] using hi

private theorem prime_pair_reflection (a : SuzukiPositiveAperture) (n : ℕ)
    (u v : CCMArchimedeanFormDomain a) :
    inner ℂ (ccmPrimeTransportOperator a n
      (ccmArchimedeanFormToAperture a (ccmArchimedeanFormReflection a u)))
      (ccmArchimedeanFormToAperture a (ccmArchimedeanFormReflection a v)) =
    inner ℂ (ccmPrimeTransportOperator a n (ccmArchimedeanFormToAperture a u))
      (ccmArchimedeanFormToAperture a v) := by
  have h (s : ℝ) (f g : SoninL2) :
      inner ℂ (logTranslationCLM s (l2Reflection f)) (l2Reflection g) =
        inner ℂ (logTranslationCLM (-s) f) g := by
    have ht : logTranslationCLM s (l2Reflection f) =
        l2Reflection (logTranslationCLM (-s) f) := by
      simpa only [neg_neg] using (l2Reflection_logTranslationCLM (-s) f).symm
    rw [ht]
    exact l2ReflectionIsometry.inner_map_map _ _
  rw [inner_ccmPrimeTransportOperator,inner_ccmPrimeTransportOperator]
  simp only [ccmArchimedeanFormToAperture_reflection,h,neg_neg]
  ring

theorem arithmeticShiftedForm_reflection (a : SuzukiPositiveAperture)
    (u v : CCMArchimedeanFormDomain a) :
    arithmeticShiftedForm a (ccmArchimedeanFormReflection a u)
      (ccmArchimedeanFormReflection a v) = arithmeticShiftedForm a u v := by
  have hphysical : inner ℂ
      (ccmArchimedeanFormToAperture a (ccmArchimedeanFormReflection a u))
      (ccmArchimedeanFormToAperture a (ccmArchimedeanFormReflection a v)) =
      inner ℂ (ccmArchimedeanFormToAperture a u) (ccmArchimedeanFormToAperture a v) := by
    change inner ℂ
      (ccmArchimedeanFormToAperture a (ccmArchimedeanFormReflection a u) : SoninL2)
      (ccmArchimedeanFormToAperture a (ccmArchimedeanFormReflection a v) : SoninL2) = _
    rw [ccmArchimedeanFormToAperture_reflection,ccmArchimedeanFormToAperture_reflection]
    exact l2ReflectionIsometry.inner_map_map _ _
  simp only [arithmeticShiftedForm,arithmeticForm_eq,ccmRestrictedWeilForm_reflection,
    inner_arithmeticCorrection,prime_pair_reflection,hphysical]

/-- Every blind minimizer obeys the full complex equation, including even variations. -/
theorem arithmeticForm_ground_equation (a : SuzukiPositiveAperture)
    (u : BlindUnitSource a) (hu : ccmRestrictedWeilSourceQuadratic a u.1 = blindMinimum a)
    (v : CCMArchimedeanFormDomain a) :
    arithmeticForm a u.1 v = (blindMinimum a : ℂ) *
      inner ℂ (ccmArchimedeanFormToAperture a u.1) (ccmArchimedeanFormToAperture a v) := by
  have ho := arithmeticShiftedForm_ground_odd a u hu (ccmRestrictedWeilOddPart a v)
    (ccmArchimedeanFormReflection_oddPart a v)
  have hr := arithmeticShiftedForm_reflection a u.1 v
  rw [u.2.1,arithmeticShiftedForm_neg_left] at hr
  rw [ccmRestrictedWeilOddPart,arithmeticShiftedForm_smul_right,
    arithmeticShiftedForm_sub_right] at ho
  have hz : arithmeticShiftedForm a u.1 v = 0 := by
    linear_combination ho - (1/2 : ℂ) * hr
  exact sub_eq_zero.mp hz

/-- The represented operator retains the original gamma and pole terms. -/
def arithmeticGroundOperator (a : SuzukiPositiveAperture) :
    suzukiApertureHilbert a →ₗ.[ℂ] suzukiApertureHilbert a :=
  boundedPerturbedFriedrichsOperator (ccmArchimedeanFormToAperture a)
    (arithmeticRemainder a) (arithmeticRemainder_isSelfAdjoint a)

theorem arithmeticGroundOperator_isSelfAdjoint (a : SuzukiPositiveAperture) :
    IsSelfAdjoint (arithmeticGroundOperator a) :=
  boundedPerturbedFriedrichsOperator_isSelfAdjoint
    (ccmArchimedeanFormToAperture a) (arithmeticRemainder a)
    (arithmeticRemainder_isSelfAdjoint a) (ccmArchimedeanFormToAperture_injective a)
    (denseRange_ccmArchimedeanFormToAperture a)

/-- The same finite correction puts every blind minimizer in the actual operator domain. -/
theorem blind_minimizer_operator_eigenstate (a : SuzukiPositiveAperture)
    (u : BlindUnitSource a) (hu : ccmRestrictedWeilSourceQuadratic a u.1 = blindMinimum a) :
    ∃ hmem : ccmArchimedeanFormToAperture a u.1 ∈ (arithmeticGroundOperator a).domain,
      arithmeticGroundOperator a ⟨ccmArchimedeanFormToAperture a u.1,hmem⟩ =
        (blindMinimum a : ℂ) • ccmArchimedeanFormToAperture a u.1 := by
  apply boundedPerturbedFriedrichsOperator_mem_domain_of_represents
    (ccmArchimedeanFormToAperture a) (arithmeticRemainder a)
    (arithmeticRemainder_isSelfAdjoint a) (ccmArchimedeanFormToAperture_injective a)
    (denseRange_ccmArchimedeanFormToAperture a) u.1
  intro v
  change arithmeticForm a u.1 v = _
  rw [arithmeticForm_ground_equation a u hu v,inner_smul_left,Complex.conj_ofReal]

/-- At every positive aperture, an actual blind unit minimizer is an eigenstate of the
finite arithmetic-corrected operator at its exact odd-sector ground value. -/
theorem exists_exact_arithmetic_ground_state (a : SuzukiPositiveAperture) :
    ∃ u : BlindUnitSource a,
      ccmRestrictedWeilSourceQuadratic a u.1 = blindMinimum a ∧
      (∀ v : OddFormSource a,blindMinimum a * ‖ccmArchimedeanFormToAperture a v.1‖ ^ 2 ≤
        (arithmeticForm a v.1 v.1).re) ∧
      (∀ v : CCMArchimedeanFormDomain a,arithmeticForm a u.1 v = (blindMinimum a : ℂ) *
        inner ℂ (ccmArchimedeanFormToAperture a u.1) (ccmArchimedeanFormToAperture a v)) ∧
      ∃ hmem : ccmArchimedeanFormToAperture a u.1 ∈ (arithmeticGroundOperator a).domain,
        arithmeticGroundOperator a ⟨ccmArchimedeanFormToAperture a u.1,hmem⟩ =
          (blindMinimum a : ℂ) • ccmArchimedeanFormToAperture a u.1 := by
  refine ⟨blindMinimizer a,rfl,?_,arithmeticForm_ground_equation a (blindMinimizer a) rfl,
    blind_minimizer_operator_eigenstate a (blindMinimizer a) rfl⟩
  intro v
  rw [arithmeticForm_diagonal]
  linarith [blindMultiplier_spec a v]

end RHTower.OddSector
