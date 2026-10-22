import GaloisForLFunctions.RHTower.CCM.CCMRationalNonunitalStrongCyclicReal
import GaloisForLFunctions.RHTower.CCM.CCMRationalAdelicRestrictionReal
import GaloisForLFunctions.RHTower.KRealCyclicDoubleKernel

/-!
# Real-equivariant literal nonunital adelic restriction

The sign-reflection involution is rebuilt on the instance-sealed twisted
crossed product and its global unitization.  Global augmentation and both
CCM endpoints are Real-equivariant, so the exact nested reduced source
inherits a Real cyclic structure.  Operator-level covariance proves that
restriction to the literal nonunital strong target is Real-equivariant.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

private abbrev Crossed :=
  CCMRationalAdelicTwistedCrossedProduct
private abbrev Source :=
  CCMRationalAdelicTwistedCyclicSourceAlgebra

/-- Sign-reflection involution on the instance-sealed twisted carrier. -/
def ccmRationalAdelicTwistedCrossedReal (F : Crossed) : Crossed :=
  ⟨ccmRationalAdelicCrossedProductRealStructure F.toFinsupp⟩

@[simp]
theorem ccmRationalAdelicTwistedCrossedReal_toFinsupp (F : Crossed) :
    (ccmRationalAdelicTwistedCrossedReal F).toFinsupp =
      ccmRationalAdelicCrossedProductRealStructure F.toFinsupp :=
  rfl

@[simp]
theorem ccmRationalAdelicTwistedCrossedReal_zero :
    ccmRationalAdelicTwistedCrossedReal (0 : Crossed) = 0 := by
  apply CCMRationalAdelicTwistedCrossedProduct.ext
  exact ccmRationalAdelicCrossedProductRealStructure_zero

theorem ccmRationalAdelicTwistedCrossedReal_add (F G : Crossed) :
    ccmRationalAdelicTwistedCrossedReal (F + G) =
      ccmRationalAdelicTwistedCrossedReal F +
        ccmRationalAdelicTwistedCrossedReal G := by
  apply CCMRationalAdelicTwistedCrossedProduct.ext
  exact ccmRationalAdelicCrossedProductRealStructure_add
    F.toFinsupp G.toFinsupp

theorem ccmRationalAdelicTwistedCrossedReal_smul
    (z : ℂ) (F : Crossed) :
    ccmRationalAdelicTwistedCrossedReal (z • F) =
      star z • ccmRationalAdelicTwistedCrossedReal F := by
  apply CCMRationalAdelicTwistedCrossedProduct.ext
  exact ccmRationalAdelicCrossedProductRealStructure_smul
    z F.toFinsupp

theorem ccmRationalAdelicTwistedCrossedReal_mul (F G : Crossed) :
    ccmRationalAdelicTwistedCrossedReal (F * G) =
      ccmRationalAdelicTwistedCrossedReal F *
        ccmRationalAdelicTwistedCrossedReal G := by
  apply CCMRationalAdelicTwistedCrossedProduct.ext
  exact ccmRationalAdelicCrossedProductRealStructure_mul
    F.toFinsupp G.toFinsupp

theorem ccmRationalAdelicTwistedCrossedReal_sq (F : Crossed) :
    ccmRationalAdelicTwistedCrossedReal
        (ccmRationalAdelicTwistedCrossedReal F) = F := by
  apply CCMRationalAdelicTwistedCrossedProduct.ext
  exact ccmRationalAdelicCrossedProductRealStructure_sq F.toFinsupp

def ccmRationalAdelicTwistedCrossedRealₛₗ : Crossed →ₗ⋆[ℂ] Crossed where
  toFun := ccmRationalAdelicTwistedCrossedReal
  map_add' := ccmRationalAdelicTwistedCrossedReal_add
  map_smul' := ccmRationalAdelicTwistedCrossedReal_smul

/-- Real involution on the sealed source's global unitization. -/
def ccmRationalAdelicTwistedSourceReal (x : Source) : Source :=
  Unitization.equiv.symm
    (star x.fst, ccmRationalAdelicTwistedCrossedReal x.snd)

@[simp]
theorem ccmRationalAdelicTwistedSourceReal_fst (x : Source) :
    (ccmRationalAdelicTwistedSourceReal x).fst = star x.fst :=
  rfl

@[simp]
theorem ccmRationalAdelicTwistedSourceReal_snd (x : Source) :
    (ccmRationalAdelicTwistedSourceReal x).snd =
      ccmRationalAdelicTwistedCrossedReal x.snd :=
  rfl

theorem ccmRationalAdelicTwistedSourceReal_add (x y : Source) :
    ccmRationalAdelicTwistedSourceReal (x + y) =
      ccmRationalAdelicTwistedSourceReal x +
        ccmRationalAdelicTwistedSourceReal y := by
  apply Unitization.ext <;>
    simp [ccmRationalAdelicTwistedCrossedReal_add]

theorem ccmRationalAdelicTwistedSourceReal_smul (z : ℂ) (x : Source) :
    ccmRationalAdelicTwistedSourceReal (z • x) =
      star z • ccmRationalAdelicTwistedSourceReal x := by
  apply Unitization.ext <;>
    simp [ccmRationalAdelicTwistedCrossedReal_smul]

theorem ccmRationalAdelicTwistedSourceReal_mul (x y : Source) :
    ccmRationalAdelicTwistedSourceReal (x * y) =
      ccmRationalAdelicTwistedSourceReal x *
        ccmRationalAdelicTwistedSourceReal y := by
  apply Unitization.ext
  · simp
  · simp only [Unitization.snd_mul,
      ccmRationalAdelicTwistedSourceReal_snd,
      ccmRationalAdelicTwistedSourceReal_fst,
      ccmRationalAdelicTwistedCrossedReal_add,
      ccmRationalAdelicTwistedCrossedReal_smul,
      ccmRationalAdelicTwistedCrossedReal_mul]

theorem ccmRationalAdelicTwistedSourceReal_one :
    ccmRationalAdelicTwistedSourceReal (1 : Source) = 1 := by
  apply Unitization.ext <;> simp

theorem ccmRationalAdelicTwistedSourceReal_sq (x : Source) :
    ccmRationalAdelicTwistedSourceReal
        (ccmRationalAdelicTwistedSourceReal x) = x := by
  apply Unitization.ext
  · simp
  · simp [ccmRationalAdelicTwistedCrossedReal_sq]

def ccmRationalAdelicTwistedSourceRealₛₗ : Source →ₗ⋆[ℂ] Source where
  toFun := ccmRationalAdelicTwistedSourceReal
  map_add' := ccmRationalAdelicTwistedSourceReal_add
  map_smul' := ccmRationalAdelicTwistedSourceReal_smul

def ccmRationalAdelicTwistedSourceKRealAlgebra :
    KRealAlgebraStructure Source where
  sigma := ccmRationalAdelicTwistedSourceRealₛₗ
  sq x := by
    change ccmRationalAdelicTwistedSourceReal
        (ccmRationalAdelicTwistedSourceReal x) = kRealParityAction false x
    rw [ccmRationalAdelicTwistedSourceReal_sq]
    rfl
  map_one := ccmRationalAdelicTwistedSourceReal_one
  map_mul := ccmRationalAdelicTwistedSourceReal_mul

/-! ## Endpoint Real covariance and reduced source -/

theorem ccmRationalAdelicTwistedUnitizationAugmentation_real (x : Source) :
    ccmRationalAdelicTwistedUnitizationAugmentation
        (ccmRationalAdelicTwistedSourceReal x) =
      star (ccmRationalAdelicTwistedUnitizationAugmentation x) :=
  rfl

theorem ccmRationalAdelicTwistedEpsilonZero_real (x : Source) :
    ccmRationalAdelicTwistedEpsilonZero
        (ccmRationalAdelicTwistedSourceReal x) =
      star (ccmRationalAdelicTwistedEpsilonZero x) := by
  change star x.fst + ccmRationalAdelicEpsilonZeroNonunital
      (ccmRationalAdelicCrossedProductRealStructure x.snd.toFinsupp) =
    star (x.fst +
      ccmRationalAdelicEpsilonZeroNonunital x.snd.toFinsupp)
  rw [ccmRationalAdelicEpsilonZeroNonunital_real, star_add]

theorem ccmRationalAdelicTwistedEpsilonOne_real (x : Source) :
    ccmRationalAdelicTwistedEpsilonOne
        (ccmRationalAdelicTwistedSourceReal x) =
      star (ccmRationalAdelicTwistedEpsilonOne x) := by
  change star x.fst + ccmRationalAdelicEpsilonOneNonunital
      (ccmRationalAdelicCrossedProductRealStructure x.snd.toFinsupp) =
    star (x.fst +
      ccmRationalAdelicEpsilonOneNonunital x.snd.toFinsupp)
  rw [ccmRationalAdelicEpsilonOneNonunital_real, star_add]

def ccmRationalAdelicTwistedSourceCyclicKReal :
    CyclicModule.KReal false CCMRationalAdelicTwistedSourceCyclicModule :=
  cyclicBarKReal ccmRationalAdelicTwistedSourceKRealAlgebra

def ccmRationalAdelicTwistedUnitizationAugmentationCyclicKRealHom :
    CyclicModule.KRealHom ccmRationalAdelicTwistedSourceCyclicKReal
      scalarConstantCyclicKReal where
  toHom := ccmRationalAdelicTwistedUnitizationAugmentationCyclicHom
  real_naturality n x :=
    cyclicBarTraceAugmentation_kReal
      ccmRationalAdelicTwistedSourceKRealAlgebra
      ccmRationalAdelicTwistedUnitizationAugmentation
      ccmRationalAdelicTwistedUnitizationAugmentation_real n x

def ccmRationalAdelicTwistedNonunitalSourceCyclicKReal :
    CyclicModule.KReal false
      CCMRationalAdelicTwistedNonunitalSourceCyclicModule :=
  CyclicModule.doubleKernelKReal
    ccmRationalAdelicTwistedSourceCyclicKReal
    scalarConstantCyclicKReal scalarConstantCyclicKReal
    ccmRationalAdelicTwistedUnitizationAugmentationCyclicKRealHom
    ccmRationalAdelicTwistedUnitizationAugmentationCyclicKRealHom

def ccmRationalAdelicTwistedEpsilonZeroCyclicKRealHom :
    CyclicModule.KRealHom ccmRationalAdelicTwistedSourceCyclicKReal
      scalarConstantCyclicKReal where
  toHom := ccmRationalAdelicTwistedEpsilonZeroCyclicHom
  real_naturality n x :=
    cyclicBarTraceAugmentation_kReal
      ccmRationalAdelicTwistedSourceKRealAlgebra
      ccmRationalAdelicTwistedEpsilonZero
      ccmRationalAdelicTwistedEpsilonZero_real n x

def ccmRationalAdelicTwistedEpsilonOneCyclicKRealHom :
    CyclicModule.KRealHom ccmRationalAdelicTwistedSourceCyclicKReal
      scalarConstantCyclicKReal where
  toHom := ccmRationalAdelicTwistedEpsilonOneCyclicHom
  real_naturality n x :=
    cyclicBarTraceAugmentation_kReal
      ccmRationalAdelicTwistedSourceKRealAlgebra
      ccmRationalAdelicTwistedEpsilonOne
      ccmRationalAdelicTwistedEpsilonOne_real n x

def ccmRationalAdelicTwistedNonunitalEpsilonZeroCyclicKRealHom :
    CyclicModule.KRealHom
      ccmRationalAdelicTwistedNonunitalSourceCyclicKReal
      scalarConstantCyclicKReal where
  toHom := ccmRationalAdelicTwistedNonunitalEpsilonZeroCyclicHom
  real_naturality n x := by
    change (scalarConstantCyclicKReal.real n).sigma
        (ccmRationalAdelicTwistedEpsilonZeroCyclicHom.simplicial.app
          (.op (.mk n)) x.1) =
      ccmRationalAdelicTwistedEpsilonZeroCyclicHom.simplicial.app
        (.op (.mk n))
        ((ccmRationalAdelicTwistedSourceCyclicKReal.real n).sigma x.1)
    exact
      ccmRationalAdelicTwistedEpsilonZeroCyclicKRealHom.real_naturality n x.1

def ccmRationalAdelicTwistedNonunitalEpsilonOneCyclicKRealHom :
    CyclicModule.KRealHom
      ccmRationalAdelicTwistedNonunitalSourceCyclicKReal
      scalarConstantCyclicKReal where
  toHom := ccmRationalAdelicTwistedNonunitalEpsilonOneCyclicHom
  real_naturality n x := by
    change (scalarConstantCyclicKReal.real n).sigma
        (ccmRationalAdelicTwistedEpsilonOneCyclicHom.simplicial.app
          (.op (.mk n)) x.1) =
      ccmRationalAdelicTwistedEpsilonOneCyclicHom.simplicial.app
        (.op (.mk n))
        ((ccmRationalAdelicTwistedSourceCyclicKReal.real n).sigma x.1)
    exact
      ccmRationalAdelicTwistedEpsilonOneCyclicKRealHom.real_naturality n x.1

/-- Even Real cyclic structure on the sealed reduced source. -/
def ccmRationalAdelicTwistedReducedSourceCyclicKReal :
    CyclicModule.KReal false
      CCMRationalAdelicTwistedReducedSourceCyclicModule :=
  CyclicModule.doubleKernelKReal
    ccmRationalAdelicTwistedNonunitalSourceCyclicKReal
    scalarConstantCyclicKReal scalarConstantCyclicKReal
    ccmRationalAdelicTwistedNonunitalEpsilonZeroCyclicKRealHom
    ccmRationalAdelicTwistedNonunitalEpsilonOneCyclicKRealHom

/-! ## Real covariance of literal restriction -/

theorem ccmRationalAdelicTwistedCrossedContinuousTraceNormHom_real
    (F : Crossed) :
    ccmRationalContinuousTraceNormIdealFieldReal
        (ccmRationalAdelicTwistedCrossedContinuousTraceNormHom F) =
      ccmRationalAdelicTwistedCrossedContinuousTraceNormHom
        (ccmRationalAdelicTwistedCrossedReal F) := by
  apply ContinuousMap.ext
  intro b
  change ccmRationalMoritaTraceNormRealStructure
      (ccmRationalAdelicMoritaTraceNormHom _ b.1.val F.toFinsupp) =
    ccmRationalAdelicMoritaTraceNormHom _ b.1.val
      (ccmRationalAdelicCrossedProductRealStructure F.toFinsupp)
  exact ccmRationalAdelicMoritaTraceNormHom_real _ b.1.val F.toFinsupp

theorem ccmRationalAdelicNonunitalIdealFieldUnitizationHom_real
    (x : Source) :
    ccmRationalNonunitalFieldReal
        (ccmRationalAdelicNonunitalIdealFieldUnitizationHom x) =
      ccmRationalAdelicNonunitalIdealFieldUnitizationHom
        (ccmRationalAdelicTwistedSourceReal x) := by
  apply Unitization.ext
  · simp
  · induction x using Unitization.ind with
    | inl_add_inr z F =>
        simp [ccmRationalAdelicNonunitalIdealFieldUnitizationHom,
          ccmRationalAdelicTwistedSourceReal,
          ccmRationalNonunitalFieldReal,
          Unitization.algebraMap_eq_inl,
          ccmRationalAdelicTwistedCrossedContinuousTraceNormHom_real]

def ccmRationalAdelicTwistedSourceNonunitalFieldCyclicKRealHom :
    CyclicModule.KRealHom ccmRationalAdelicTwistedSourceCyclicKReal
      (cyclicBarKReal ccmRationalNonunitalFieldKRealAlgebra) :=
  cyclicBarAlgHomKRealHom
    ccmRationalAdelicTwistedSourceKRealAlgebra
    ccmRationalNonunitalFieldKRealAlgebra
    ccmRationalAdelicNonunitalIdealFieldUnitizationHom
    ccmRationalAdelicNonunitalIdealFieldUnitizationHom_real

/-- **Real-equivariant exact restriction to literal Definition 4.9.** -/
def ccmRationalAdelicReducedNonunitalStrongCyclicKRealHom :
    CyclicModule.KRealHom
      ccmRationalAdelicTwistedReducedSourceCyclicKReal
      ccmRationalNonunitalStrongCyclicTargetKReal where
  toHom := ccmRationalAdelicReducedNonunitalStrongCyclicHom
  real_naturality n x := by
    apply Subtype.ext
    exact
      ccmRationalAdelicTwistedSourceNonunitalFieldCyclicKRealHom.real_naturality
        n x.1.1

end GaloisForLFunctions.RHTower
