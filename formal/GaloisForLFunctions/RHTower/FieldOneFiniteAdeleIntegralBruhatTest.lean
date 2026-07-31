import GaloisForLFunctions.RHTower.FieldOneSemilocalBruhatWeylTensor
import Mathlib.NumberTheory.Padics.ProperSpace

/-!
# Integral finite-adele Bruhat test

The product of the local integer rings is a compact open additive subgroup of
the rational finite adeles.  Its characteristic function is therefore a
canonical nonzero compactly supported locally constant test function.

This supplies a concrete finite-place test vector for contracting the
semilocal algebraic tensor back to its archimedean Schwartz factor.  The
construction is topological but uses no Haar measure, integration, LF
topology, completed tensor product, or analytic computation.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open Filter Function IsDedekindDomain Set
open scoped RestrictedProduct TensorProduct

/-- Integral finite adeles form a compact subset of the finite adele ring. -/
theorem fieldOneFiniteAdeleIntegralAddSubgroup_isCompact :
    IsCompact
      (fieldOneFiniteAdeleIntegralAddSubgroup :
        Set FieldOneFiniteAdele) := by
  letI (v : HeightOneSpectrum ℤ) :
      CompactSpace (v.adicCompletionIntegers ℚ) := by
    letI :
        Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v)) :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩
    letI : Algebra ℤ (v.adicCompletionIntegers ℚ) :=
      Ring.toIntAlgebra (v.adicCompletionIntegers ℚ)
    let eA :=
      (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v)
    let e :
        v.adicCompletionIntegers ℚ ≃ₜ
          ℤ_[Rat.HeightOneSpectrum.primesEquiv v] :=
      ContinuousAlgEquiv.toHomeomorph eA
    exact e.symm.compactSpace
  let ι := HeightOneSpectrum ℤ
  let R : ι → Type :=
    fun v => v.adicCompletion ℚ
  let A : (v : ι) → Set (R v) :=
    fun v => v.adicCompletionIntegers ℚ
  have hrange :
      Set.range
          (RestrictedProduct.structureMap R A cofinite) =
        (fieldOneFiniteAdeleIntegralAddSubgroup :
          Set FieldOneFiniteAdele) := by
    rw [RestrictedProduct.range_structureMap]
    rfl
  rw [← hrange]
  exact isCompact_range
    RestrictedProduct.isEmbedding_structureMap.continuous

theorem fieldOneFiniteAdeleIntegralAddSubgroup_isClosed :
    IsClosed
      (fieldOneFiniteAdeleIntegralAddSubgroup :
        Set FieldOneFiniteAdele) :=
  fieldOneFiniteAdeleIntegralAddSubgroup.isClosed_of_isOpen
    fieldOneFiniteAdeleIntegralAddSubgroup_isOpen

theorem fieldOneFiniteAdeleIntegralAddSubgroup_isClopen :
    IsClopen
      (fieldOneFiniteAdeleIntegralAddSubgroup :
        Set FieldOneFiniteAdele) :=
  ⟨fieldOneFiniteAdeleIntegralAddSubgroup_isClosed,
    fieldOneFiniteAdeleIntegralAddSubgroup_isOpen⟩

/-- Locally constant characteristic function of the compact open integral
finite adeles. -/
def fieldOneFiniteAdeleIntegralIndicatorLocallyConstant :
    LocallyConstant FieldOneFiniteAdele ℂ :=
  (LocallyConstant.const FieldOneFiniteAdele (1 : ℂ)).indicator
    fieldOneFiniteAdeleIntegralAddSubgroup_isClopen

open Classical in
@[simp]
theorem fieldOneFiniteAdeleIntegralIndicatorLocallyConstant_apply
    (x : FieldOneFiniteAdele) :
    fieldOneFiniteAdeleIntegralIndicatorLocallyConstant x =
      if x ∈ fieldOneFiniteAdeleIntegralAddSubgroup then 1 else 0 := by
  exact LocallyConstant.indicator_apply_eq_if _ _ _

theorem fieldOneFiniteAdeleIntegralIndicator_hasCompactSupport :
    HasCompactSupport
      (fieldOneFiniteAdeleIntegralIndicatorLocallyConstant :
        FieldOneFiniteAdele → ℂ) := by
  classical
  apply HasCompactSupport.of_support_subset_isCompact
    fieldOneFiniteAdeleIntegralAddSubgroup_isCompact
  intro x hx
  by_contra hnot
  apply hx
  rw [fieldOneFiniteAdeleIntegralIndicatorLocallyConstant_apply,
    if_neg]
  exact hnot

/-- Canonical finite Bruhat test: the characteristic function of integral
finite adeles. -/
def fieldOneFiniteAdeleIntegralBruhatTest :
    FieldOneFiniteBruhatSchwartz :=
  ⟨fieldOneFiniteAdeleIntegralIndicatorLocallyConstant,
    fieldOneFiniteAdeleIntegralIndicator_hasCompactSupport⟩

@[simp]
theorem fieldOneFiniteAdeleIntegralBruhatTest_zero :
    fieldOneFiniteAdeleIntegralBruhatTest.1 0 = 1 := by
  classical
  rw [fieldOneFiniteAdeleIntegralBruhatTest,
    fieldOneFiniteAdeleIntegralIndicatorLocallyConstant_apply,
    if_pos]
  exact zero_mem fieldOneFiniteAdeleIntegralAddSubgroup

theorem fieldOneFiniteAdeleIntegralBruhatTest_ne_zero :
    fieldOneFiniteAdeleIntegralBruhatTest ≠ 0 := by
  intro h
  have hz := congrArg (fun f : FieldOneFiniteBruhatSchwartz => f.1 0) h
  simp at hz

/-- Every finite Weyl multiplier fixes the value at zero of the canonical
integral test. -/
@[simp]
theorem fieldOneFiniteAdeleStandardWeylMultiplier_integralTest_zero
    (r : FieldOneFiniteAdele) :
    (fieldOneFiniteAdeleStandardWeylMultiplier r
      fieldOneFiniteAdeleIntegralBruhatTest).1 0 = 1 := by
  simp [fieldOneFiniteAdeleStandardWeylMultiplier,
    locallyConstantWeylMultiplier_apply]

/-- Evaluation at zero on the finite Bruhat factor. -/
def fieldOneFiniteBruhatEvalZero :
    FieldOneFiniteBruhatSchwartz →ₗ[ℂ] ℂ where
  toFun f := f.1 0
  map_add' f g := by simp
  map_smul' c f := by simp

/-- Contract the finite factor of a semilocal algebraic tensor by evaluation
at zero. -/
def fieldOneSemilocalContractFiniteZero :
    FieldOneSemilocalBruhatSchwartz →ₗ[ℂ]
      FieldOneArchimedeanSchwartz :=
  (TensorProduct.rid ℂ FieldOneArchimedeanSchwartz).toLinearMap.comp
    (TensorProduct.map LinearMap.id fieldOneFiniteBruhatEvalZero)

@[simp]
theorem fieldOneSemilocalContractFiniteZero_tmul
    (f : FieldOneArchimedeanSchwartz)
    (g : FieldOneFiniteBruhatSchwartz) :
    fieldOneSemilocalContractFiniteZero (f ⊗ₜ[ℂ] g) =
      g.1 0 • f := by
  simp [fieldOneSemilocalContractFiniteZero,
    fieldOneFiniteBruhatEvalZero]

@[simp]
theorem fieldOneSemilocalContractFiniteZero_integralTest
    (f : FieldOneArchimedeanSchwartz) :
    fieldOneSemilocalContractFiniteZero
        (f ⊗ₜ[ℂ] fieldOneFiniteAdeleIntegralBruhatTest) =
      f := by
  simp

end

end GaloisForLFunctions.RHTower
