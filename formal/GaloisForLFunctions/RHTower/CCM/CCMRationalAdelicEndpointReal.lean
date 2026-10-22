import GaloisForLFunctions.RHTower.CCM.CCMRationalAdelicRealStructure
import GaloisForLFunctions.RHTower.CCM.CCMRationalAdelicEpsilonOneCyclic
import GaloisForLFunctions.RHTower.KRealCyclicBarTrace
import GaloisForLFunctions.RHTower.KRealCyclicDoubleKernel

/-!
# Real compatibility of the rational CCM endpoints

Both exact endpoint traces of the actual rational adelic crossed product commute with the source
Real involution and complex conjugation.  Consequently their genuine all-degree cyclic morphisms
are Real-equivariant, and the literal reduced source
`ker ε₀^natural ∩ ker ε₁^natural` inherits an even Real cyclic-module structure.
-/

noncomputable section

open MeasureTheory
open scoped TensorProduct

namespace GaloisForLFunctions.RHTower

private abbrev Core := CCMRationalAdelicBruhatSimpleTensor
private abbrev Crossed := CCMRationalAdelicAlgebraicCrossedProduct
private abbrev Source := CCMRationalAdelicCyclicSourceAlgebra

/-! ## Reflection of the two Haar factors -/

theorem ccmRationalArchimedeanSchwartzIntegral_reflection
    (f : CCMRationalArchimedeanSchwartz) :
    ccmRationalArchimedeanSchwartzIntegral
        (ccmRationalArchimedeanSchwartzReflection f) =
      star (ccmRationalArchimedeanSchwartzIntegral f) := by
  rw [ccmRationalArchimedeanSchwartzIntegral_apply,
    ccmRationalArchimedeanSchwartzIntegral_apply]
  change (∫ x : ℝ, (starRingEnd ℂ) (f (-x))) =
    (starRingEnd ℂ) (∫ x : ℝ, f x)
  rw [integral_conj, MeasureTheory.integral_neg_eq_self]

theorem ccmRationalFiniteBruhatIntegral_reflection
    (f : CCMRationalFiniteBruhatSchwartz) :
    ccmRationalFiniteBruhatIntegral (ccmRationalFiniteBruhatReflection f) =
      star (ccmRationalFiniteBruhatIntegral f) := by
  rw [ccmRationalFiniteBruhatIntegral_apply,
    ccmRationalFiniteBruhatIntegral_apply]
  change (∫ x, (starRingEnd ℂ) (f.1 (-x))
      ∂ccmRationalFiniteAdeleHaar) =
    (starRingEnd ℂ) (∫ x, f.1 x ∂ccmRationalFiniteAdeleHaar)
  rw [integral_conj, MeasureTheory.integral_neg_eq_self]

/-! ## Real compatibility on the actual Bruhat tensor core -/

theorem ccmRationalAdelicBruhatZeroEval_real (x : Core) :
    ccmRationalAdelicBruhatZeroEval
        (ccmRationalAdelicBruhatSimpleTensorKRealEven.sigma x) =
      star (ccmRationalAdelicBruhatZeroEval x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul f φ =>
      simp only [ccmRationalAdelicBruhatSimpleTensor_sigma_tmul,
        ccmRationalAdelicBruhatZeroEval_tmul,
        ccmRationalArchimedeanSchwartzReflection_apply,
        ccmRationalFiniteBruhatReflection_apply, neg_zero]
      exact (map_mul (starRingEnd ℂ) (f 0) (φ.1 0)).symm
  | add x y hx hy =>
      rw [map_add, map_add, map_add, hx, hy, star_add]

theorem ccmRationalAdelicBruhatIntegral_real (x : Core) :
    ccmRationalAdelicBruhatIntegral
        (ccmRationalAdelicBruhatSimpleTensorKRealEven.sigma x) =
      star (ccmRationalAdelicBruhatIntegral x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul f φ =>
      simp only [ccmRationalAdelicBruhatSimpleTensor_sigma_tmul,
        ccmRationalAdelicBruhatIntegral_tmul,
        ccmRationalArchimedeanSchwartzIntegral_reflection,
        ccmRationalFiniteBruhatIntegral_reflection]
      exact (map_mul (starRingEnd ℂ)
        (ccmRationalArchimedeanSchwartzIntegral f)
        (ccmRationalFiniteBruhatIntegral φ)).symm
  | add x y hx hy =>
      rw [map_add, map_add, map_add, hx, hy, star_add]

/-! ## Endpoint traces on the crossed product and its minimal unitization -/

theorem ccmRationalAdelicEpsilonZeroNonunital_real (F : Crossed) :
    ccmRationalAdelicEpsilonZeroNonunital
        (ccmRationalAdelicCrossedProductRealStructure F) =
      star (ccmRationalAdelicEpsilonZeroNonunital F) := by
  change ccmRationalAdelicBruhatZeroEval
      (ccmRationalAdelicCrossedProductRealStructure F 1) =
    star (ccmRationalAdelicBruhatZeroEval (F 1))
  rw [ccmRationalAdelicCrossedProductRealStructure_apply]
  simp [ccmRationalAdelicMonomialRealTwist,
    ccmRationalAdelicBruhatZeroEval_real, ccmRationalUnitSign]

theorem ccmRationalAdelicEpsilonOneNonunital_real (F : Crossed) :
    ccmRationalAdelicEpsilonOneNonunital
        (ccmRationalAdelicCrossedProductRealStructure F) =
      star (ccmRationalAdelicEpsilonOneNonunital F) := by
  rw [ccmRationalAdelicEpsilonOneNonunital_apply,
    ccmRationalAdelicEpsilonOneNonunital_apply]
  rw [ccmRationalAdelicCrossedProductRealStructure_apply]
  simp [ccmRationalAdelicMonomialRealTwist,
    ccmRationalAdelicBruhatIntegral_real, ccmRationalUnitSign]

theorem ccmRationalAdelicEpsilonZero_real (x : Source) :
    ccmRationalAdelicEpsilonZero (ccmRationalAdelicSourceRealStructure x) =
      star (ccmRationalAdelicEpsilonZero x) := by
  change star x.fst + ccmRationalAdelicEpsilonZeroNonunital
      (ccmRationalAdelicCrossedProductRealStructure x.snd) =
    star (x.fst + ccmRationalAdelicEpsilonZeroNonunital x.snd)
  rw [ccmRationalAdelicEpsilonZeroNonunital_real, star_add]

theorem ccmRationalAdelicEpsilonOne_real (x : Source) :
    ccmRationalAdelicEpsilonOne (ccmRationalAdelicSourceRealStructure x) =
      star (ccmRationalAdelicEpsilonOne x) := by
  change star x.fst + ccmRationalAdelicEpsilonOneNonunital
      (ccmRationalAdelicCrossedProductRealStructure x.snd) =
    star (x.fst + ccmRationalAdelicEpsilonOneNonunital x.snd)
  rw [ccmRationalAdelicEpsilonOneNonunital_real, star_add]

theorem ccmRationalAdelicUnitizationAugmentation_real (x : Source) :
    ccmRationalAdelicUnitizationAugmentation
        (ccmRationalAdelicSourceRealStructure x) =
      star (ccmRationalAdelicUnitizationAugmentation x) :=
  rfl

/-! ## Genuine all-degree Real cyclic morphisms and reduced double kernel -/

/-- Even Real structure on the actual cyclic bar of the rational adelic source. -/
def ccmRationalAdelicSourceCyclicKReal :
    CyclicModule.KReal false CCMRationalAdelicSourceCyclicModule :=
  cyclicBarKReal ccmRationalAdelicSourceKRealAlgebra

/-- Unitization augmentation is Real-equivariant in every cyclic degree. -/
def ccmRationalAdelicUnitizationAugmentationCyclicKRealHom :
    CyclicModule.KRealHom ccmRationalAdelicSourceCyclicKReal
      scalarConstantCyclicKReal where
  toHom := ccmRationalAdelicUnitizationAugmentationCyclicHom
  real_naturality n x :=
    cyclicBarTraceAugmentation_kReal
      ccmRationalAdelicSourceKRealAlgebra
      ccmRationalAdelicUnitizationAugmentation
      ccmRationalAdelicUnitizationAugmentation_real n x

/-- Correct nonunital cyclic source inherits the ambient Real structure. -/
def ccmRationalAdelicNonunitalSourceCyclicKReal :
    CyclicModule.KReal false CCMRationalAdelicNonunitalSourceCyclicModule :=
  CyclicModule.doubleKernelKReal
    ccmRationalAdelicSourceCyclicKReal
    scalarConstantCyclicKReal scalarConstantCyclicKReal
    ccmRationalAdelicUnitizationAugmentationCyclicKRealHom
    ccmRationalAdelicUnitizationAugmentationCyclicKRealHom

/-- The genuine all-degree fixed-point endpoint is a Real cyclic morphism. -/
def ccmRationalAdelicEpsilonZeroCyclicKRealHom :
    CyclicModule.KRealHom ccmRationalAdelicSourceCyclicKReal
      scalarConstantCyclicKReal where
  toHom := ccmRationalAdelicEpsilonZeroCyclicHom
  real_naturality n x :=
    cyclicBarTraceAugmentation_kReal
      ccmRationalAdelicSourceKRealAlgebra
      ccmRationalAdelicEpsilonZero
      ccmRationalAdelicEpsilonZero_real n x

/-- The genuine all-degree Haar endpoint is a Real cyclic morphism. -/
def ccmRationalAdelicEpsilonOneCyclicKRealHom :
    CyclicModule.KRealHom ccmRationalAdelicSourceCyclicKReal
      scalarConstantCyclicKReal where
  toHom := ccmRationalAdelicEpsilonOneCyclicHom
  real_naturality n x :=
    cyclicBarTraceAugmentation_kReal
      ccmRationalAdelicSourceKRealAlgebra
      ccmRationalAdelicEpsilonOne
      ccmRationalAdelicEpsilonOne_real n x

/-- Fixed-point endpoint restricted to the nonunital Real cyclic source. -/
def ccmRationalAdelicNonunitalEpsilonZeroCyclicKRealHom :
    CyclicModule.KRealHom ccmRationalAdelicNonunitalSourceCyclicKReal
      scalarConstantCyclicKReal where
  toHom := ccmRationalAdelicNonunitalEpsilonZeroCyclicHom
  real_naturality n x := by
    change (scalarConstantCyclicKReal.real n).sigma
        (ccmRationalAdelicEpsilonZeroCyclicHom.simplicial.app
          (.op (.mk n)) x.1) =
      ccmRationalAdelicEpsilonZeroCyclicHom.simplicial.app
        (.op (.mk n))
        ((ccmRationalAdelicSourceCyclicKReal.real n).sigma x.1)
    exact ccmRationalAdelicEpsilonZeroCyclicKRealHom.real_naturality n x.1

/-- Haar endpoint restricted to the nonunital Real cyclic source. -/
def ccmRationalAdelicNonunitalEpsilonOneCyclicKRealHom :
    CyclicModule.KRealHom ccmRationalAdelicNonunitalSourceCyclicKReal
      scalarConstantCyclicKReal where
  toHom := ccmRationalAdelicNonunitalEpsilonOneCyclicHom
  real_naturality n x := by
    change (scalarConstantCyclicKReal.real n).sigma
        (ccmRationalAdelicEpsilonOneCyclicHom.simplicial.app
          (.op (.mk n)) x.1) =
      ccmRationalAdelicEpsilonOneCyclicHom.simplicial.app
        (.op (.mk n))
        ((ccmRationalAdelicSourceCyclicKReal.real n).sigma x.1)
    exact ccmRationalAdelicEpsilonOneCyclicKRealHom.real_naturality n x.1

/-- Exact simultaneous endpoint kernel is stable under the source Real involution in every
cyclic degree. -/
theorem ccmRationalAdelicReducedSourceCyclic_real_stable (n : ℕ) :
    (ccmRationalAdelicNonunitalSourceCyclicKReal.real n).StableSubmodule
      (ccmRationalAdelicNonunitalEpsilonZeroCyclicHom.doubleKernelSubmodule
        ccmRationalAdelicNonunitalEpsilonOneCyclicHom (.op (.mk n))) := by
  intro x hx
  rw [ccmRationalAdelicNonunitalEpsilonZeroCyclicHom.mem_doubleKernelSubmodule_iff] at hx ⊢
  constructor
  · calc
      ccmRationalAdelicNonunitalEpsilonZeroCyclicHom.simplicial.app
          (.op (.mk n))
          ((ccmRationalAdelicNonunitalSourceCyclicKReal.real n).sigma x) =
        (scalarConstantCyclicKReal.real n).sigma
          (ccmRationalAdelicNonunitalEpsilonZeroCyclicHom.simplicial.app
            (.op (.mk n)) x) := by
              simpa [ccmRationalAdelicNonunitalEpsilonZeroCyclicKRealHom] using
                (ccmRationalAdelicNonunitalEpsilonZeroCyclicKRealHom.real_naturality
                  n x).symm
      _ = 0 := by rw [hx.1, map_zero]
  · calc
      ccmRationalAdelicNonunitalEpsilonOneCyclicHom.simplicial.app
          (.op (.mk n))
          ((ccmRationalAdelicNonunitalSourceCyclicKReal.real n).sigma x) =
        (scalarConstantCyclicKReal.real n).sigma
          (ccmRationalAdelicNonunitalEpsilonOneCyclicHom.simplicial.app
            (.op (.mk n)) x) := by
              simpa [ccmRationalAdelicNonunitalEpsilonOneCyclicKRealHom] using
                (ccmRationalAdelicNonunitalEpsilonOneCyclicKRealHom.real_naturality
                  n x).symm
      _ = 0 := by rw [hx.2, map_zero]

/-- Exact even Real cyclic-module structure on
`ker ε₀^natural ∩ ker ε₁^natural`. -/
def ccmRationalAdelicReducedSourceCyclicKReal :
    CyclicModule.KReal false CCMRationalAdelicReducedSourceCyclicModule :=
  CyclicModule.doubleKernelKReal
    ccmRationalAdelicNonunitalSourceCyclicKReal
    scalarConstantCyclicKReal scalarConstantCyclicKReal
    ccmRationalAdelicNonunitalEpsilonZeroCyclicKRealHom
    ccmRationalAdelicNonunitalEpsilonOneCyclicKRealHom

@[simp]
theorem ccmRationalAdelicReducedSourceCyclicKReal_sigma_coe
    (n : ℕ) (x : CCMRationalAdelicReducedSourceCyclicModule.simplicial.degree n) :
    ((ccmRationalAdelicReducedSourceCyclicKReal.real n).sigma x).1 =
      (ccmRationalAdelicNonunitalSourceCyclicKReal.real n).sigma x.1 :=
  rfl

@[simp]
theorem ccmRationalAdelicReducedSourceCyclicKReal_sigma_ambient_coe
    (n : ℕ) (x : CCMRationalAdelicReducedSourceCyclicModule.simplicial.degree n) :
    ((ccmRationalAdelicReducedSourceCyclicKReal.real n).sigma x).1.1 =
      (ccmRationalAdelicSourceCyclicKReal.real n).sigma x.1.1 :=
  rfl

end GaloisForLFunctions.RHTower
