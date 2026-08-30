import GaloisForLFunctions.HTGeometry.MeroExponentialGauge
import GaloisForLFunctions.HTGeometry.MeroFieldConstants
import GaloisForLFunctions.HTGeometry.HyperexponentialPrimitive
import GaloisForLFunctions.HTGeometry.EllipticGammaRationalBaseMatroid
import GaloisForLFunctions.HTGeometry.RationalLinearCoefficientNoSolution
import GaloisForLFunctions.HTGeometry.PolynomialDriftRationalOuterFactorRigidity
import GaloisForLFunctions.HTGeometry.RelativeTwoShiftGaugeCharacterization
import GaloisForLFunctions.HTGeometry.MeromorphicRealizationDerivative
import GaloisForLFunctions.HTGeometry.FreeCoordinateExponentialObstruction
import GaloisForLFunctions.HTGeometry.DeSitterBoltzmann

/-!
# The Gaussian exponential inside the meromorphic field

The rational functions form an intermediate field of the meromorphic field of the plane, closed
under the derivation, and the Gaussian exponential `exp(-z²)` is a hyperexponential element over it
with logarithmic derivative `-2z`.  Because `w′ = -2k·z·w` has no nonzero rational solution for any
positive integer `k`, the Gaussian exponential is transcendental over the rational field.

The complex-linear form of the meromorphic derivation is built from three scalar identities.  The
algebra instance on analytic germs is deliberately kept out of scope: it produces a second
`Module ℂ` structure on the meromorphic field through the Ore localization, and the two are not
definitionally equal.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher
open scoped Differential

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra

/-! ### Bridges to the ambient instances -/

theorem deriv_analyticMeroElement' (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (Set.univ : Set ℂ)) :
    (analyticMeroElement f hf)′ = analyticMeroElement (deriv f) hf.deriv :=
  deriv_analyticMeroElement f hf

theorem deriv_complexConst (c : ℂ) : (algebraMap ℂ (meroField (Set.univ : Set ℂ)) c)′ = 0 :=
  meroField_deriv_algebraMap_complex_rationalBase c

theorem algebraMap_complex_eq_analyticMeroElement (c : ℂ) :
    algebraMap ℂ (meroField (Set.univ : Set ℂ)) c
      = analyticMeroElement (fun _ : ℂ => c) analyticOnNhd_const := by
  rw [analyticMeroElement_const]
  rfl

/-! ### The rational subfield -/

/-- The image of the rational function field inside the meromorphic field of the plane. -/
def ratField : IntermediateField ℂ (meroField (Set.univ : Set ℂ)) where
  carrier := Set.range (algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ)))
  mul_mem' := by rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a * b, map_mul _ _ _⟩
  add_mem' := by rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a + b, map_add _ _ _⟩
  zero_mem' := ⟨0, map_zero _⟩
  one_mem' := ⟨1, map_one _⟩
  inv_mem' := by rintro _ ⟨a, rfl⟩; exact ⟨a⁻¹, map_inv₀ _ _⟩
  algebraMap_mem' := fun c => by
    refine ⟨RatFunc.C c, ?_⟩
    rw [algebraMap_ratFunc_C_eq, algebraMap_complex_eq_analyticMeroElement]

theorem mem_ratField_iff (x : meroField (Set.univ : Set ℂ)) :
    x ∈ ratField ↔ ∃ r : RatFunc ℂ, algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) r = x :=
  Iff.rfl

theorem algebraMap_mem_ratField (r : RatFunc ℂ) :
    algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) r ∈ ratField := ⟨r, rfl⟩

/-- The rational subfield is closed under the derivation. -/
theorem derivationClosed_ratField : DerivationClosed ratField := by
  rintro x ⟨r, rfl⟩
  exact ⟨r′, (deriv_algebraMap r).symm⟩

/-! ### The ambient derivation as a complex derivation -/

set_option synthInstance.maxHeartbeats 1000000 in
theorem deriv_one_meroField : (1 : meroField (Set.univ : Set ℂ))′ = 0 := by
  have h := deriv_complexConst (1 : ℂ)
  rwa [map_one] at h

set_option synthInstance.maxHeartbeats 1000000 in
theorem deriv_complex_smul (c : ℂ) (x : meroField (Set.univ : Set ℂ)) :
    (c • x)′ = c • x′ := by
  rw [Algebra.smul_def c x, differential_deriv_mul, deriv_complexConst, zero_mul, zero_add,
    Algebra.smul_def]

set_option synthInstance.maxHeartbeats 1000000 in
theorem deriv_leibniz_smul (a b : meroField (Set.univ : Set ℂ)) :
    (a * b)′ = a • b′ + b • a′ := by
  rw [differential_deriv_mul]
  simp only [smul_eq_mul]
  ring

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- The meromorphic derivation, regarded as a complex-linear derivation. -/
def meroComplexDerivation :
    Derivation ℂ (meroField (Set.univ : Set ℂ)) (meroField (Set.univ : Set ℂ)) where
  toLinearMap :=
    { toAddHom := { toFun := fun x => x′, map_add' := fun x y => map_add _ x y }
      map_smul' := deriv_complex_smul }
  map_one_eq_zero' := deriv_one_meroField
  leibniz' := deriv_leibniz_smul

@[simp]
theorem meroComplexDerivation_apply (x : meroField (Set.univ : Set ℂ)) :
    meroComplexDerivation x = x′ := rfl

/-! ### The rational field as a differential base -/

instance ratFieldDifferential : Differential ↥ratField :=
  differentialOfDerivation (restrictDerivation meroComplexDerivation ratField
    (fun _v hv => derivationClosed_ratField hv))

@[simp]
theorem ratFieldDifferential_coe (v : ↥ratField) :
    ((v′ : ↥ratField) : meroField (Set.univ : Set ℂ))
      = ((v : meroField (Set.univ : Set ℂ)))′ := rfl

instance ratFieldDifferentialAlgebra :
    DifferentialAlgebra ↥ratField (meroField (Set.univ : Set ℂ)) where
  deriv_algebraMap _ := rfl

/-! ### The Gaussian exponential -/

theorem analyticOnNhd_gaussianExp :
    AnalyticOnNhd ℂ (fun z : ℂ => Complex.exp (-z ^ 2)) (Set.univ : Set ℂ) := by
  have hP : AnalyticOnNhd ℂ (fun z : ℂ => -z ^ 2) (Set.univ : Set ℂ) :=
    (analyticOnNhd_id.pow 2).neg
  exact hP.cexp

/-- The Gaussian exponential as an element of the meromorphic field. -/
def gaussElem : meroField (Set.univ : Set ℂ) :=
  analyticMeroElement (fun z : ℂ => Complex.exp (-z ^ 2)) analyticOnNhd_gaussianExp

/-- The rational function `-2X`, the logarithmic derivative of the Gaussian exponential. -/
def gaussLogDeriv : RatFunc ℂ :=
  algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C (-2 : ℂ) * Polynomial.X)

theorem gaussLogDeriv_mem : algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) gaussLogDeriv
    ∈ ratField := algebraMap_mem_ratField _

theorem algebraMap_gaussLogDeriv :
    algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) gaussLogDeriv
      = analyticMeroElement (fun z : ℂ => -2 * z)
        (by
          have h := analyticOnNhd_polyGerm (Polynomial.C (-2 : ℂ) * Polynomial.X)
          simpa using h) := by
  have h := analyticMeroElement_polyGerm (Polynomial.C (-2 : ℂ) * Polynomial.X)
  rw [gaussLogDeriv, ← h]
  exact analyticMeroElement_congr _ _ (by funext z; simp)

set_option synthInstance.maxHeartbeats 1000000 in
/-- The Gaussian exponential is hyperexponential with logarithmic derivative `-2z`. -/
theorem deriv_gaussElem :
    gaussElem′ = algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) gaussLogDeriv * gaussElem := by
  rw [gaussElem, deriv_analyticMeroElement', algebraMap_gaussLogDeriv,
    ← analyticMeroElement_mul _ analyticOnNhd_gaussianExp]
  refine analyticMeroElement_congr _ _ ?_
  funext z
  have hd : HasDerivAt (fun w : ℂ => Complex.exp (-w ^ 2)) (Complex.exp (-z ^ 2) * (-(2 * z))) z := by
    have h2 : HasDerivAt (fun w : ℂ => -(w ^ 2)) (-((2 : ℕ) * z ^ (2 - 1))) z :=
      (hasDerivAt_pow 2 z).neg
    have hcoef : (-((2 : ℕ) * z ^ (2 - 1)) : ℂ) = -(2 * z) := by norm_num
    rw [hcoef] at h2
    exact h2.cexp
  rw [hd.deriv]
  ring

theorem gaussElem_ne_zero : gaussElem ≠ 0 := by
  rw [gaussElem]
  intro h
  have := (analyticMeroElement_eq_zero_iff analyticOnNhd_gaussianExp).mp h 0 (Set.mem_univ 0)
  simp at this

end

end GaloisForLFunctions.HTGeometry
