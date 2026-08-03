import GaloisForLFunctions.RHTower.RealCoronaCompleteDivisorDetectability
import GaloisForLFunctions.RHTower.RealCoronaSpectralSmoothness

/-!
# Complete-divisor crossed-product smoothness fracture

Functional-equation reflection is smooth for the absolute divisor and genuinely non-Lipschitz for
the signed divisor.  The diagonal Real-corona orientation has the opposite defect: it is smooth
for the signed divisor but commutator-blind.  This is the exact smoothness--detectability tradeoff.
-/

noncomputable section

open Filter HilbertSchmidt
open GaloisForLFunctions.RHTower

namespace RHTower

/-- Linear functional-equation reflection on the complete Xi-divisor Hilbert space. -/
def xiCompleteDivisorReflection : Module.End ℂ XiDivisorL2 where
  toFun := fun a =>
    ⟨fun q => a (xiZeroCopyReflectEquiv q),
      HilbertSchmidt.memℓp_of_sq
        (xiZeroCopyReflectEquiv.summable_iff.mpr
          (HilbertSchmidt.summable_coe_sq a))⟩
  map_add' := by
    intro a b
    ext q
    rfl
  map_smul' := by
    intro c a
    ext q
    rfl

@[simp] theorem xiCompleteDivisorReflection_apply
    (a : XiDivisorL2) (q : XiZeroCopy) :
    xiCompleteDivisorReflection a q = a (xiZeroCopyReflectEquiv q) := rfl

theorem xiCompleteDivisorReflection_sq :
    xiCompleteDivisorReflection * xiCompleteDivisorReflection = 1 := by
  apply LinearMap.ext
  intro a
  ext q
  change a (xiZeroCopyReflectEquiv (xiZeroCopyReflectEquiv q)) = a q
  rw [xiZeroCopyReflectEquiv_apply_apply]

theorem norm_xiCompleteDivisorReflection (a : XiDivisorL2) :
    ‖xiCompleteDivisorReflection a‖ = ‖a‖ := by
  have hsq : ‖xiCompleteDivisorReflection a‖ ^ 2 = ‖a‖ ^ 2 := by
    rw [HilbertSchmidt.lp_norm_sq_eq, HilbertSchmidt.lp_norm_sq_eq]
    exact xiZeroCopyReflectEquiv.tsum_eq (fun q => ‖a q‖ ^ 2)
  nlinarith [norm_nonneg (xiCompleteDivisorReflection a), norm_nonneg a]

/-- Signed complete-divisor energy: canonical orbit orientation times absolute centered energy. -/
def xiCompleteDivisorSignedEnergy (q : XiZeroCopy) : ℝ :=
  (deningerArithmeticFEOrientation q).re * xiCompleteDivisorEnergy q

theorem abs_xiCompleteDivisorSignedEnergy (q : XiZeroCopy) :
    |xiCompleteDivisorSignedEnergy q| = xiCompleteDivisorEnergy q := by
  have heps : |(deningerArithmeticFEOrientation q).re| = 1 := by
    simp only [deningerArithmeticFEOrientation]
    split_ifs <;> norm_num
  rw [xiCompleteDivisorSignedEnergy, abs_mul, heps, one_mul]
  exact abs_of_nonneg (norm_nonneg _)

theorem xiCompleteDivisorSignedEnergy_reflect (q : XiZeroCopy) :
    xiCompleteDivisorSignedEnergy (xiZeroCopyReflectEquiv q) =
      -xiCompleteDivisorSignedEnergy q := by
  rw [xiCompleteDivisorSignedEnergy, xiCompleteDivisorSignedEnergy,
    deningerArithmeticFEOrientation_reflect, xiCompleteDivisorEnergy,
    xiCompleteDivisorEnergy, xiSpectralPoint_reflect, norm_neg]
  simp only [Complex.neg_re]
  ring

/-- Self-adjoint signed complete-divisor Dirac operator. -/
def xiCompleteDivisorSignedDirac : XiDivisorL2 →ₗ.[ℂ] XiDivisorL2 :=
  maximalRealDiagonal xiCompleteDivisorSignedEnergy

theorem xiCompleteDivisorSignedDirac_isSelfAdjoint :
    IsSelfAdjoint xiCompleteDivisorSignedDirac :=
  maximalRealDiagonal_isSelfAdjoint xiCompleteDivisorSignedEnergy

/-- Reflection preserves the signed maximal domain because it reverses energy but preserves its
absolute value. -/
theorem xiCompleteDivisorReflection_mem_signedDomain
    (x : xiCompleteDivisorSignedDirac.domain) :
    xiCompleteDivisorReflection (x : XiDivisorL2) ∈
      xiCompleteDivisorSignedDirac.domain := by
  change Memℓp
    (fun q : XiZeroCopy =>
      (xiCompleteDivisorSignedEnergy q : ℂ) *
        (x : XiDivisorL2) (xiZeroCopyReflectEquiv q)) 2
  apply HilbertSchmidt.memℓp_of_sq
  have hx : Summable (fun q : XiZeroCopy =>
      ‖(xiCompleteDivisorSignedEnergy q : ℂ) * (x : XiDivisorL2) q‖ ^ 2) := by
    simpa using x.property.summable (by norm_num)
  exact (xiZeroCopyReflectEquiv.summable_iff.mpr hx).congr fun q => by
    simp only [Function.comp_apply, xiCompleteDivisorSignedEnergy_reflect]
    rw [show ((-xiCompleteDivisorSignedEnergy q : ℝ) : ℂ) =
      -(xiCompleteDivisorSignedEnergy q : ℂ) by norm_num,
      neg_mul, norm_neg]

/-- Signed complete divisor is odd under functional-equation reflection. -/
theorem xiCompleteDivisorSignedDirac_reflection_odd
    (x : xiCompleteDivisorSignedDirac.domain) :
    xiCompleteDivisorSignedDirac
        ⟨xiCompleteDivisorReflection (x : XiDivisorL2),
          xiCompleteDivisorReflection_mem_signedDomain x⟩ =
      -xiCompleteDivisorReflection (xiCompleteDivisorSignedDirac x) := by
  ext q
  change (xiCompleteDivisorSignedEnergy q : ℂ) *
      (x : XiDivisorL2) (xiZeroCopyReflectEquiv q) =
    -((xiCompleteDivisorSignedEnergy (xiZeroCopyReflectEquiv q) : ℂ) *
      (x : XiDivisorL2) (xiZeroCopyReflectEquiv q))
  rw [xiCompleteDivisorSignedEnergy_reflect]
  push_cast
  ring

/-- Canonical basis vector in the signed complete-divisor maximal domain. -/
def xiCompleteDivisorSignedEigenvector (q : XiZeroCopy) :
    xiCompleteDivisorSignedDirac.domain :=
  ⟨lpBasis XiZeroCopy q,
    lpBasis_mem_maximalRealDiagonalDomain xiCompleteDivisorSignedEnergy q⟩

theorem xiCompleteDivisorSignedDirac_eigenvector (q : XiZeroCopy) :
    xiCompleteDivisorSignedDirac (xiCompleteDivisorSignedEigenvector q) =
      (xiCompleteDivisorSignedEnergy q : ℂ) •
        (xiCompleteDivisorSignedEigenvector q : XiDivisorL2) := by
  ext r
  classical
  change (xiCompleteDivisorSignedEnergy r : ℂ) * (lpBasis XiZeroCopy q) r =
    (xiCompleteDivisorSignedEnergy q : ℂ) * (lpBasis XiZeroCopy q) r
  by_cases hr : r = q
  · subst r
    rfl
  · rw [lpBasis_apply, lp.single_apply_ne _ _ _ hr]
    simp

theorem xiCompleteDivisorSignedDirac_genuinelyUnbounded :
    IsGenuinelyUnboundedLinearPMap xiCompleteDivisorSignedDirac := by
  rintro ⟨C, hC, hbound⟩
  have hev : ∀ᶠ q : XiZeroCopy in cofinite,
      C < xiCompleteDivisorEnergy q :=
    tendsto_norm_xiSpectralPoint_cofinite.eventually
      (eventually_gt_atTop C)
  rcases hev.exists with ⟨q, hq⟩
  have hb := hbound (xiCompleteDivisorSignedEigenvector q)
  have hnorm : ‖(xiCompleteDivisorSignedEigenvector q : XiDivisorL2)‖ = 1 := by
    simpa [xiCompleteDivisorSignedEigenvector] using
      (lpBasis XiZeroCopy).orthonormal.norm_eq_one q
  rw [xiCompleteDivisorSignedDirac_eigenvector, norm_smul, hnorm,
    mul_one] at hb
  simp only [Complex.norm_real, Real.norm_eq_abs,
    abs_xiCompleteDivisorSignedEnergy] at hb
  exact (not_lt_of_ge (by simpa using hb)) hq

/-- The crossed-product reflection generator is not Lipschitz for the signed complete divisor. -/
theorem xiCompleteDivisorSigned_reflectionCommutator_genuinelyUnbounded :
    IsGenuinelyUnboundedLinearPMap
      (linearPMapOrientationCommutator xiCompleteDivisorSignedDirac
        xiCompleteDivisorReflection
        xiCompleteDivisorReflection_mem_signedDomain) := by
  exact (genuinelyUnboundedLinearPMap_orientationCommutator_iff
    xiCompleteDivisorSignedDirac xiCompleteDivisorReflection
      xiCompleteDivisorReflection_mem_signedDomain
      xiCompleteDivisorSignedDirac_reflection_odd
      norm_xiCompleteDivisorReflection).mpr
    xiCompleteDivisorSignedDirac_genuinelyUnbounded

/-- No first-order smooth subalgebra containing functional-equation reflection can represent the
signed complete divisor. -/
theorem not_signedCompleteDivisorReflection_lipschitz :
    ¬HasLinearPMapBoundOnDomain
      (linearPMapOrientationCommutator xiCompleteDivisorSignedDirac
        xiCompleteDivisorReflection
        xiCompleteDivisorReflection_mem_signedDomain) :=
  xiCompleteDivisorSigned_reflectionCommutator_genuinelyUnbounded

/-- Reflection preserves the absolute complete-divisor maximal domain. -/
theorem xiCompleteDivisorReflection_mem_absoluteDomain
    (x : xiCompleteDivisorDirac.domain) :
    xiCompleteDivisorReflection (x : XiDivisorL2) ∈
      xiCompleteDivisorDirac.domain := by
  change Memℓp (fun q : XiZeroCopy =>
    (xiCompleteDivisorEnergy q : ℂ) *
      (x : XiDivisorL2) (xiZeroCopyReflectEquiv q)) 2
  apply HilbertSchmidt.memℓp_of_sq
  have hx : Summable (fun q : XiZeroCopy =>
      ‖(xiCompleteDivisorEnergy q : ℂ) * (x : XiDivisorL2) q‖ ^ 2) := by
    simpa using x.property.summable (by norm_num)
  exact (xiZeroCopyReflectEquiv.summable_iff.mpr hx).congr fun q => by
    simp only [Function.comp_apply, xiCompleteDivisorEnergy,
      xiSpectralPoint_reflect, norm_neg]

/-- By contrast, reflection commutes with the absolute complete divisor. -/
theorem xiCompleteDivisorDirac_reflection_commutes
    (x : xiCompleteDivisorDirac.domain) :
    xiCompleteDivisorDirac
        ⟨xiCompleteDivisorReflection (x : XiDivisorL2),
          xiCompleteDivisorReflection_mem_absoluteDomain x⟩ =
      xiCompleteDivisorReflection (xiCompleteDivisorDirac x) := by
  ext q
  change (xiCompleteDivisorEnergy q : ℂ) *
      (x : XiDivisorL2) (xiZeroCopyReflectEquiv q) =
    (xiCompleteDivisorEnergy (xiZeroCopyReflectEquiv q) : ℂ) *
      (x : XiDivisorL2) (xiZeroCopyReflectEquiv q)
  simp [xiCompleteDivisorEnergy, xiSpectralPoint_reflect]

theorem xiCompleteDivisorReflection_bounded :
    HasLinearOperatorBound xiCompleteDivisorReflection := by
  refine ⟨1, zero_le_one, fun x => ?_⟩
  rw [norm_xiCompleteDivisorReflection, one_mul]

/-- Absolute divisor makes functional-equation reflection smooth to every commutator order. -/
def xiCompleteDivisorAbsoluteReflectionSmooth :
    LinearPMapSmoothElement xiCompleteDivisorDirac :=
  linearPMapSmoothElementOfCommutes xiCompleteDivisorDirac
    xiCompleteDivisorReflection xiCompleteDivisorReflection_mem_absoluteDomain
    xiCompleteDivisorDirac_reflection_commutes
    xiCompleteDivisorReflection_bounded

/-- Signed divisor admits no all-orders smooth representative of the reflection generator. -/
theorem not_exists_signedCompleteDivisorSmoothReflection :
    ¬∃ S : LinearPMapSmoothElement xiCompleteDivisorSignedDirac,
      S.operator = xiCompleteDivisorReflection :=
  not_exists_smoothElement_of_genuinelyUnboundedCommutator
    xiCompleteDivisorSignedDirac xiCompleteDivisorReflection
    xiCompleteDivisorReflection_mem_signedDomain
    xiCompleteDivisorSigned_reflectionCommutator_genuinelyUnbounded

/-- Canonical diagonal orientation preserves the signed maximal domain. -/
theorem xiCompleteDivisorOrientation_mem_signedDomain
    (x : xiCompleteDivisorSignedDirac.domain) :
    xiCompleteDivisorOrientation (x : XiDivisorL2) ∈
      xiCompleteDivisorSignedDirac.domain := by
  change Memℓp (fun q : XiZeroCopy =>
    (xiCompleteDivisorSignedEnergy q : ℂ) *
      xiCompleteDivisorOrientation (x : XiDivisorL2) q) 2
  exact x.property.mono' fun q => by
    rw [xiCompleteDivisorOrientation_apply]
    simp only [norm_mul, norm_deningerArithmeticFEOrientation, one_mul]
    exact le_rfl

/-- Canonical diagonal orientation commutes with signed divisor and is therefore locally blind. -/
theorem xiCompleteDivisorSignedDirac_orientation_commutes
    (x : xiCompleteDivisorSignedDirac.domain) :
    xiCompleteDivisorSignedDirac
        ⟨xiCompleteDivisorOrientation (x : XiDivisorL2),
          xiCompleteDivisorOrientation_mem_signedDomain x⟩ =
      xiCompleteDivisorOrientation (xiCompleteDivisorSignedDirac x) := by
  ext q
  change (xiCompleteDivisorSignedEnergy q : ℂ) *
      (deningerArithmeticFEOrientation q * (x : XiDivisorL2) q) =
    deningerArithmeticFEOrientation q *
      ((xiCompleteDivisorSignedEnergy q : ℂ) * (x : XiDivisorL2) q)
  ring

theorem xiCompleteDivisorOrientation_bounded :
    HasLinearOperatorBound xiCompleteDivisorOrientation := by
  refine ⟨1, zero_le_one, fun x => ?_⟩
  rw [norm_xiCompleteDivisorOrientation, one_mul]

/-- Signed divisor makes the diagonal Real-corona orientation smooth to every order, but its first
and every higher commutator vanish. -/
def xiCompleteDivisorSignedOrientationSmooth :
    LinearPMapSmoothElement xiCompleteDivisorSignedDirac :=
  linearPMapSmoothElementOfCommutes xiCompleteDivisorSignedDirac
    xiCompleteDivisorOrientation xiCompleteDivisorOrientation_mem_signedDomain
    xiCompleteDivisorSignedDirac_orientation_commutes
    xiCompleteDivisorOrientation_bounded

/-- Functional-equation reflection conjugates diagonal Real-corona orientation to its negative. -/
theorem xiCompleteDivisorReflection_conjugates_orientation :
    xiCompleteDivisorReflection * xiCompleteDivisorOrientation *
        xiCompleteDivisorReflection =
      -xiCompleteDivisorOrientation := by
  apply LinearMap.ext
  intro a
  ext q
  change xiCompleteDivisorReflection
      (xiCompleteDivisorOrientation (xiCompleteDivisorReflection a)) q =
    -xiCompleteDivisorOrientation a q
  rw [xiCompleteDivisorReflection_apply,
    xiCompleteDivisorOrientation_apply,
    xiCompleteDivisorReflection_apply,
    xiZeroCopyReflectEquiv_apply_apply,
    xiCompleteDivisorOrientation_apply]
  rw [deningerArithmeticFEOrientation_reflect]
  ring

/-- Smoothness--detectability fracture on the actual complete divisor: absolute energy gives a
smooth crossed-product reflection, signed energy gives no smooth reflection, while diagonal
orientation remains smooth but commutator-blind. -/
theorem xiCompleteDivisor_smoothnessDetectabilityFracture :
    (∃ S : LinearPMapSmoothElement xiCompleteDivisorDirac,
        S.operator = xiCompleteDivisorReflection) ∧
      (¬∃ S : LinearPMapSmoothElement xiCompleteDivisorSignedDirac,
        S.operator = xiCompleteDivisorReflection) ∧
      (∃ S : LinearPMapSmoothElement xiCompleteDivisorSignedDirac,
        S.operator = xiCompleteDivisorOrientation) := by
  exact ⟨⟨xiCompleteDivisorAbsoluteReflectionSmooth, rfl⟩,
    not_exists_signedCompleteDivisorSmoothReflection,
    ⟨xiCompleteDivisorSignedOrientationSmooth, rfl⟩⟩

end RHTower

