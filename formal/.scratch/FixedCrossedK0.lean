import GaloisForLFunctions.RHTower.RealCoronaKZeroMultiplicityFracture
import GaloisForLFunctions.RHTower.RealCoronaHolomorphicReflectionCrossedProduct

noncomputable section

open Set

namespace GaloisForLFunctions.RHTower

@[simp] theorem reflectionParity_even_mul_even :
    ReflectionParity.even * ReflectionParity.even = ReflectionParity.even := rfl

@[simp] theorem reflectionParity_even_mul_odd :
    ReflectionParity.even * ReflectionParity.odd = ReflectionParity.odd := rfl

@[simp] theorem reflectionParity_odd_mul_even :
    ReflectionParity.odd * ReflectionParity.even = ReflectionParity.odd := rfl

@[simp] theorem reflectionParity_odd_mul_odd :
    ReflectionParity.odd * ReflectionParity.odd = ReflectionParity.even := rfl

@[reducible] def fixedCoordinateFunctionAction (ι : Type*) :
    MulSemiringAction ReflectionParity (ι → ℂ) where
  smul _ f := f
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl
  smul_one _ := rfl
  smul_mul _ _ _ := rfl

theorem fixedCoordinateFunction_smulCommClass (ι : Type*) :
    letI := fixedCoordinateFunctionAction ι
    SMulCommClass ReflectionParity ℂ (ι → ℂ) := by
  letI := fixedCoordinateFunctionAction ι
  constructor
  intro _ _ _
  rfl

@[simp] theorem fixedCoordinateFunction_smul (ι : Type*)
    (p : ReflectionParity) (f : ι → ℂ) :
    letI := fixedCoordinateFunctionAction ι
    p • f = f := by
  rfl

theorem reflectionParity_decompose {A : Type*} [Semiring A]
    [MulSemiringAction ReflectionParity A]
    (F : SkewMonoidAlgebra A ReflectionParity) :
    F = SkewMonoidAlgebra.single ReflectionParity.even (F.coeff ReflectionParity.even) +
      SkewMonoidAlgebra.single ReflectionParity.odd (F.coeff ReflectionParity.odd) := by
  ext p
  cases p <;> simp

def fixedReflectionFourierToFun (ι : Type*)
    (F : SkewMonoidAlgebra (ι → ℂ) ReflectionParity) : (ι → ℂ) × (ι → ℂ) :=
  (F.coeff ReflectionParity.even + F.coeff ReflectionParity.odd,
    F.coeff ReflectionParity.even - F.coeff ReflectionParity.odd)

def fixedReflectionFourierInvFun (ι : Type*)
    (p : (ι → ℂ) × (ι → ℂ)) : SkewMonoidAlgebra (ι → ℂ) ReflectionParity :=
  SkewMonoidAlgebra.single ReflectionParity.even ((p.1 + p.2) / 2) +
    SkewMonoidAlgebra.single ReflectionParity.odd ((p.1 - p.2) / 2)

theorem fixedReflectionFourierInvFun_leftInverse (ι : Type*) :
    letI := fixedCoordinateFunctionAction ι
    Function.LeftInverse (fixedReflectionFourierInvFun ι)
      (fixedReflectionFourierToFun ι) := by
  letI := fixedCoordinateFunctionAction ι
  intro F
  rw [reflectionParity_decompose F]
  ext p i
  cases p
  · simp [fixedReflectionFourierToFun, fixedReflectionFourierInvFun]
  · simp [fixedReflectionFourierToFun, fixedReflectionFourierInvFun]

theorem fixedReflectionFourierInvFun_rightInverse (ι : Type*) :
    letI := fixedCoordinateFunctionAction ι
    Function.RightInverse (fixedReflectionFourierInvFun ι)
      (fixedReflectionFourierToFun ι) := by
  letI := fixedCoordinateFunctionAction ι
  intro p
  apply Prod.ext <;> funext i
  <;> simp [fixedReflectionFourierToFun, fixedReflectionFourierInvFun]
  <;> ring

theorem fixedReflectionFourierToFun_mul (ι : Type*)
    (F H : SkewMonoidAlgebra (ι → ℂ) ReflectionParity) :
    letI := fixedCoordinateFunctionAction ι
    fixedReflectionFourierToFun ι (F * H) =
      fixedReflectionFourierToFun ι F * fixedReflectionFourierToFun ι H := by
  letI := fixedCoordinateFunctionAction ι
  rw [reflectionParity_decompose F, reflectionParity_decompose H]
  apply Prod.ext <;> funext i
  <;> simp only [mul_add, add_mul]
  <;> simp [fixedReflectionFourierToFun, SkewMonoidAlgebra.single_mul_single,
    fixedCoordinateFunction_smul]
  <;> ring

def fixedReflectionFourierRingEquiv (ι : Type*) :
    letI := fixedCoordinateFunctionAction ι
    SkewMonoidAlgebra (ι → ℂ) ReflectionParity ≃+* ((ι → ℂ) × (ι → ℂ)) := by
  letI := fixedCoordinateFunctionAction ι
  exact
    { toFun := fixedReflectionFourierToFun ι
      invFun := fixedReflectionFourierInvFun ι
      left_inv := fixedReflectionFourierInvFun_leftInverse ι
      right_inv := fixedReflectionFourierInvFun_rightInverse ι
      map_mul' := fixedReflectionFourierToFun_mul ι
      map_add' := by
        intro F H
        apply Prod.ext <;> funext i <;> simp [fixedReflectionFourierToFun] <;> ring }

theorem fixedReflectionFourierRingEquiv_coefficient (ι : Type*) (a : ι → ℂ) :
    letI := fixedCoordinateFunctionAction ι
    fixedReflectionFourierRingEquiv ι
        (SkewMonoidAlgebra.single (1 : ReflectionParity) a) = (a, a) := by
  letI := fixedCoordinateFunctionAction ι
  apply Prod.ext <;> funext i
  <;> simp [fixedReflectionFourierRingEquiv, fixedReflectionFourierToFun]

def realCoronaFixedCrossedProductIdempotent {ι : Type*} (q : ι →₀ ℕ) :
    letI := fixedCoordinateFunctionAction ι
    SkewMonoidAlgebra (ι → ℂ) ReflectionParity :=
  SkewMonoidAlgebra.single (1 : ReflectionParity)
    (realCoronaFixedCoordinateIdempotent q)

theorem realCoronaFixedCrossedProductIdempotent_isIdempotent
    {ι : Type*} (q : ι →₀ ℕ) :
    letI := fixedCoordinateFunctionAction ι
    IsIdempotentElem (realCoronaFixedCrossedProductIdempotent q) := by
  letI := fixedCoordinateFunctionAction ι
  rw [IsIdempotentElem]
  have he := realCoronaFixedCoordinateIdempotent_isIdempotent q
  rw [IsIdempotentElem] at he
  simp only [realCoronaFixedCrossedProductIdempotent,
    SkewMonoidAlgebra.single_mul_single, fixedCoordinateFunction_smul]
  rw [he, one_mul]

theorem fixedReflectionFourierRingEquiv_realCoronaIdempotent
    {ι : Type*} (q : ι →₀ ℕ) :
    letI := fixedCoordinateFunctionAction ι
    fixedReflectionFourierRingEquiv ι
        (realCoronaFixedCrossedProductIdempotent q) =
      (realCoronaFixedCoordinateIdempotent q,
        realCoronaFixedCoordinateIdempotent q) := by
  letI := fixedCoordinateFunctionAction ι
  exact fixedReflectionFourierRingEquiv_coefficient ι
    (realCoronaFixedCoordinateIdempotent q)

abbrev FixedReflectionCrossedProductKZero (ι : Type*) :=
  FiniteCoordinateKZero ι × FiniteCoordinateKZero ι

def fixedCoordinateToReflectionCrossedProductKZero {ι : Type*} :
    FiniteCoordinateKZero ι →+ FixedReflectionCrossedProductKZero ι where
  toFun x := (x, x)
  map_zero' := rfl
  map_add' _ _ := rfl

def realCoronaFixedCrossedProductKZeroClass {ι : Type*} (q : ι →₀ ℕ) :
    FixedReflectionCrossedProductKZero ι :=
  fixedCoordinateToReflectionCrossedProductKZero (realCoronaFixedKZeroClass q)

theorem realCoronaFixedCrossedProductKZeroClass_eq {ι : Type*} (q : ι →₀ ℕ) :
    realCoronaFixedCrossedProductKZeroClass q =
      (realCoronaFixedKZeroClass q, realCoronaFixedKZeroClass q) := rfl

def fixedReflectionCrossedProductKZeroPlusEvaluationRank
    {ι : Type*} (i : ι) : FixedReflectionCrossedProductKZero ι →+ ℤ where
  toFun x := finiteCoordinateKZeroEvaluationRank i x.1
  map_zero' := by simp
  map_add' _ _ := by simp

def fixedReflectionCrossedProductKZeroMinusEvaluationRank
    {ι : Type*} (i : ι) : FixedReflectionCrossedProductKZero ι →+ ℤ where
  toFun x := finiteCoordinateKZeroEvaluationRank i x.2
  map_zero' := by simp
  map_add' _ _ := by simp

theorem fixedReflectionCrossedProductKZeroPlusEvaluationRank_realCoronaClass
    {ι : Type*} (q : ι →₀ ℕ) (i : ι) :
    fixedReflectionCrossedProductKZeroPlusEvaluationRank i
        (realCoronaFixedCrossedProductKZeroClass q) =
      realCoronaKZeroSupportVector q i := by
  exact finiteCoordinateKZeroEvaluationRank_realCoronaFixedKZeroClass q i

theorem fixedReflectionCrossedProductKZeroMinusEvaluationRank_realCoronaClass
    {ι : Type*} (q : ι →₀ ℕ) (i : ι) :
    fixedReflectionCrossedProductKZeroMinusEvaluationRank i
        (realCoronaFixedCrossedProductKZeroClass q) =
      realCoronaKZeroSupportVector q i := by
  exact finiteCoordinateKZeroEvaluationRank_realCoronaFixedKZeroClass q i

def CompletedSelfDualAnalyticFamily.fixedCrossedProductKZeroClass
    {T : Type*} (F : CompletedSelfDualAnalyticFamily T) (t : T) :
    FixedReflectionCrossedProductKZero ℝ :=
  realCoronaFixedCrossedProductKZeroClass (F.realWindowMultiplicity t)

theorem CompletedSelfDualAnalyticFamily.centralFixedCrossedPlusKZero_eq_analyticRank_iff
    {T : Type*} (F : CompletedSelfDualAnalyticFamily T) (t : T) :
    fixedReflectionCrossedProductKZeroPlusEvaluationRank F.center
        (F.fixedCrossedProductKZeroClass t) =
        (F.toSelfDualRealZeroFamily.analyticRank t : ℤ) ↔
      F.toSelfDualRealZeroFamily.analyticRank t ≤ 1 := by
  rw [CompletedSelfDualAnalyticFamily.fixedCrossedProductKZeroClass,
    fixedReflectionCrossedProductKZeroPlusEvaluationRank_realCoronaClass]
  norm_cast
  exact realCoronaKZeroSupportVector_eq_analyticRankAt_iff
    F.center (F.realWindowMultiplicity t)

theorem CompletedSelfDualAnalyticFamily.centralFixedCrossedMinusKZero_eq_analyticRank_iff
    {T : Type*} (F : CompletedSelfDualAnalyticFamily T) (t : T) :
    fixedReflectionCrossedProductKZeroMinusEvaluationRank F.center
        (F.fixedCrossedProductKZeroClass t) =
        (F.toSelfDualRealZeroFamily.analyticRank t : ℤ) ↔
      F.toSelfDualRealZeroFamily.analyticRank t ≤ 1 := by
  rw [CompletedSelfDualAnalyticFamily.fixedCrossedProductKZeroClass,
    fixedReflectionCrossedProductKZeroMinusEvaluationRank_realCoronaClass]
  norm_cast
  exact realCoronaKZeroSupportVector_eq_analyticRankAt_iff
    F.center (F.realWindowMultiplicity t)

end GaloisForLFunctions.RHTower
