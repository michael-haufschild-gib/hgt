import GaloisForLFunctions.RHTower.CCMRationalAdelicEpsilonOneCyclic

/-!
# Instance-sealed rational adelic crossed product and cyclic source

The algebraic crossed product was originally exposed as an abbreviation of a
Finsupp type.  Once the Bruhat core acquires its own semiring structure, Lean
can also synthesize the unrelated pointwise Finsupp multiplication.  That
instance overlap is unacceptable at the boundary of the literal CCM
nonunital cyclic module.

This file seals the carrier behind a structure and transports only its
additive and scalar structures.  Multiplication is explicitly the twisted
convolution already proved associative.  The unitization, augmentation, and
both CCM endpoint traces are then rebuilt on this instance-unambiguous
algebra.  No mathematical condition is changed.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

private abbrev LegacyCrossed :=
  CCMRationalAdelicAlgebraicCrossedProduct
private abbrev LegacySource :=
  CCMRationalAdelicCyclicSourceAlgebra

/-- Instance-sealed carrier of the rational adelic twisted crossed product. -/
structure CCMRationalAdelicTwistedCrossedProduct where
  /-- Underlying finite-support coefficient family. -/
  toFinsupp : LegacyCrossed

/-- Carrier equivalence used only to transport additive and scalar structure. -/
def ccmRationalAdelicTwistedCrossedProductEquiv :
    CCMRationalAdelicTwistedCrossedProduct ≃ LegacyCrossed where
  toFun := CCMRationalAdelicTwistedCrossedProduct.toFinsupp
  invFun := CCMRationalAdelicTwistedCrossedProduct.mk
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance : AddCommGroup
    CCMRationalAdelicTwistedCrossedProduct :=
  ccmRationalAdelicTwistedCrossedProductEquiv.addCommGroup

noncomputable instance : Module ℂ
    CCMRationalAdelicTwistedCrossedProduct :=
  ccmRationalAdelicTwistedCrossedProductEquiv.module ℂ

/-- Twisted convolution, explicitly sealed against pointwise Finsupp
multiplication. -/
noncomputable instance : Mul
    CCMRationalAdelicTwistedCrossedProduct :=
  ⟨fun F G =>
    ⟨ccmRationalAdelicCrossedProductMul F.toFinsupp G.toFinsupp⟩⟩

@[ext]
theorem CCMRationalAdelicTwistedCrossedProduct.ext
    {F G : CCMRationalAdelicTwistedCrossedProduct}
    (h : F.toFinsupp = G.toFinsupp) : F = G := by
  cases F
  cases G
  cases h
  rfl

@[simp]
theorem ccmRationalAdelicTwistedCrossedProduct_toFinsupp_zero :
    (0 : CCMRationalAdelicTwistedCrossedProduct).toFinsupp = 0 :=
  rfl

@[simp]
theorem ccmRationalAdelicTwistedCrossedProduct_toFinsupp_add
    (F G : CCMRationalAdelicTwistedCrossedProduct) :
    (F + G).toFinsupp = F.toFinsupp + G.toFinsupp :=
  rfl

@[simp]
theorem ccmRationalAdelicTwistedCrossedProduct_toFinsupp_smul
    (z : ℂ) (F : CCMRationalAdelicTwistedCrossedProduct) :
    (z • F).toFinsupp = z • F.toFinsupp :=
  rfl

@[simp]
theorem ccmRationalAdelicTwistedCrossedProduct_toFinsupp_mul
    (F G : CCMRationalAdelicTwistedCrossedProduct) :
    (F * G).toFinsupp =
      ccmRationalAdelicCrossedProductMul F.toFinsupp G.toFinsupp :=
  rfl

noncomputable instance : NonUnitalRing
    CCMRationalAdelicTwistedCrossedProduct where
  zero_mul F := by
    apply CCMRationalAdelicTwistedCrossedProduct.ext
    exact ccmRationalAdelicCrossedProduct_zero_mul F.toFinsupp
  mul_zero F := by
    apply CCMRationalAdelicTwistedCrossedProduct.ext
    exact ccmRationalAdelicCrossedProduct_mul_zero F.toFinsupp
  left_distrib F G H := by
    apply CCMRationalAdelicTwistedCrossedProduct.ext
    exact ccmRationalAdelicCrossedProduct_mul_add
      F.toFinsupp G.toFinsupp H.toFinsupp
  right_distrib F G H := by
    apply CCMRationalAdelicTwistedCrossedProduct.ext
    exact ccmRationalAdelicCrossedProduct_add_mul
      F.toFinsupp G.toFinsupp H.toFinsupp
  mul_assoc F G H := by
    apply CCMRationalAdelicTwistedCrossedProduct.ext
    exact ccmRationalAdelicCrossedProduct_mul_assoc
      F.toFinsupp G.toFinsupp H.toFinsupp

noncomputable instance : SMulCommClass ℂ
    CCMRationalAdelicTwistedCrossedProduct
    CCMRationalAdelicTwistedCrossedProduct where
  smul_comm z F G := by
    apply CCMRationalAdelicTwistedCrossedProduct.ext
    exact
      instSMulCommClassComplexCCMRationalAdelicAlgebraicCrossedProduct.smul_comm
        z F.toFinsupp G.toFinsupp

noncomputable instance : IsScalarTower ℂ
    CCMRationalAdelicTwistedCrossedProduct
    CCMRationalAdelicTwistedCrossedProduct where
  smul_assoc z F G := by
    apply CCMRationalAdelicTwistedCrossedProduct.ext
    exact
      instIsScalarTowerComplexCCMRationalAdelicAlgebraicCrossedProduct.smul_assoc
        z F.toFinsupp G.toFinsupp

/-- Underlying coefficient family as a complex-linear map. -/
def ccmRationalAdelicTwistedCrossedProductToFinsupp :
    CCMRationalAdelicTwistedCrossedProduct →ₗ[ℂ] LegacyCrossed where
  toFun := CCMRationalAdelicTwistedCrossedProduct.toFinsupp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Instance-unambiguous minimal unitization of the exact twisted algebra. -/
abbrev CCMRationalAdelicTwistedCyclicSourceAlgebra :=
  Unitization ℂ CCMRationalAdelicTwistedCrossedProduct

private abbrev TwistedCrossed :=
  CCMRationalAdelicTwistedCrossedProduct
private abbrev TwistedSource :=
  CCMRationalAdelicTwistedCyclicSourceAlgebra

/-- Additive/scalar identification with the legacy unitized carrier.  This is
not used to transport multiplication. -/
def ccmRationalAdelicTwistedSourceToLegacy :
    TwistedSource →ₗ[ℂ] LegacySource where
  toFun x := Unitization.inl x.fst + (x.snd.toFinsupp : LegacySource)
  map_add' x y := by
    ext <;> simp
  map_smul' z x := by
    ext <;> simp

@[simp]
theorem ccmRationalAdelicTwistedSourceToLegacy_fst
    (x : TwistedSource) :
    (ccmRationalAdelicTwistedSourceToLegacy x).fst = x.fst := by
  simp [ccmRationalAdelicTwistedSourceToLegacy]

@[simp]
theorem ccmRationalAdelicTwistedSourceToLegacy_snd
    (x : TwistedSource) :
    (ccmRationalAdelicTwistedSourceToLegacy x).snd = x.snd.toFinsupp := by
  simp [ccmRationalAdelicTwistedSourceToLegacy]

/-- First endpoint on the sealed nonunital crossed product. -/
def ccmRationalAdelicTwistedEpsilonZeroNonunital :
    TwistedCrossed →ₗ[ℂ] ℂ :=
  ccmRationalAdelicEpsilonZeroNonunital.comp
    ccmRationalAdelicTwistedCrossedProductToFinsupp

/-- Haar endpoint on the sealed nonunital crossed product. -/
def ccmRationalAdelicTwistedEpsilonOneNonunital :
    TwistedCrossed →ₗ[ℂ] ℂ :=
  ccmRationalAdelicEpsilonOneNonunital.comp
    ccmRationalAdelicTwistedCrossedProductToFinsupp

theorem ccmRationalAdelicTwistedEpsilonZeroNonunital_isTrace
    (F G : TwistedCrossed) :
    ccmRationalAdelicTwistedEpsilonZeroNonunital (F * G) =
      ccmRationalAdelicTwistedEpsilonZeroNonunital (G * F) := by
  exact ccmRationalAdelicEpsilonZeroNonunital_isTrace
    F.toFinsupp G.toFinsupp

theorem ccmRationalAdelicTwistedEpsilonOneNonunital_isTrace
    (F G : TwistedCrossed) :
    ccmRationalAdelicTwistedEpsilonOneNonunital (F * G) =
      ccmRationalAdelicTwistedEpsilonOneNonunital (G * F) := by
  exact ccmRationalAdelicEpsilonOneNonunital_isTrace
    F.toFinsupp G.toFinsupp

/-- Normalized first CCM endpoint on the sealed unitization. -/
def ccmRationalAdelicTwistedEpsilonZero : TwistedSource →ₗ[ℂ] ℂ where
  toFun x := x.fst + ccmRationalAdelicTwistedEpsilonZeroNonunital x.snd
  map_add' x y := by
    simp only [Unitization.fst_add, Unitization.snd_add, map_add]
    ring
  map_smul' z x := by
    simp only [Unitization.fst_smul, Unitization.snd_smul, map_smul,
      smul_eq_mul, RingHom.id_apply]
    ring

/-- Normalized Haar endpoint on the sealed unitization. -/
def ccmRationalAdelicTwistedEpsilonOne : TwistedSource →ₗ[ℂ] ℂ where
  toFun x := x.fst + ccmRationalAdelicTwistedEpsilonOneNonunital x.snd
  map_add' x y := by
    simp only [Unitization.fst_add, Unitization.snd_add, map_add]
    ring
  map_smul' z x := by
    simp only [Unitization.fst_smul, Unitization.snd_smul, map_smul,
      smul_eq_mul, RingHom.id_apply]
    ring

@[simp]
theorem ccmRationalAdelicTwistedEpsilonZero_toLegacy
    (x : TwistedSource) :
    ccmRationalAdelicEpsilonZero
        (ccmRationalAdelicTwistedSourceToLegacy x) =
      ccmRationalAdelicTwistedEpsilonZero x := by
  simp [ccmRationalAdelicEpsilonZero,
    ccmRationalAdelicTwistedEpsilonZero,
    ccmRationalAdelicTwistedEpsilonZeroNonunital,
    ccmRationalAdelicTwistedCrossedProductToFinsupp]

@[simp]
theorem ccmRationalAdelicTwistedEpsilonOne_toLegacy
    (x : TwistedSource) :
    ccmRationalAdelicEpsilonOne
        (ccmRationalAdelicTwistedSourceToLegacy x) =
      ccmRationalAdelicTwistedEpsilonOne x := by
  simp [ccmRationalAdelicEpsilonOne,
    ccmRationalAdelicTwistedEpsilonOne,
    ccmRationalAdelicTwistedEpsilonOneNonunital,
    ccmRationalAdelicTwistedCrossedProductToFinsupp]

theorem ccmRationalAdelicTwistedEpsilonZero_isTrace
    (x y : TwistedSource) :
    ccmRationalAdelicTwistedEpsilonZero (x * y) =
      ccmRationalAdelicTwistedEpsilonZero (y * x) := by
  change (x * y).fst +
      ccmRationalAdelicTwistedEpsilonZeroNonunital (x * y).snd =
    (y * x).fst +
      ccmRationalAdelicTwistedEpsilonZeroNonunital (y * x).snd
  rw [Unitization.fst_mul, Unitization.fst_mul,
    Unitization.snd_mul, Unitization.snd_mul]
  simp only [map_add, map_smul, smul_eq_mul]
  rw [ccmRationalAdelicTwistedEpsilonZeroNonunital_isTrace x.snd y.snd]
  ring

theorem ccmRationalAdelicTwistedEpsilonOne_isTrace
    (x y : TwistedSource) :
    ccmRationalAdelicTwistedEpsilonOne (x * y) =
      ccmRationalAdelicTwistedEpsilonOne (y * x) := by
  change (x * y).fst +
      ccmRationalAdelicTwistedEpsilonOneNonunital (x * y).snd =
    (y * x).fst +
      ccmRationalAdelicTwistedEpsilonOneNonunital (y * x).snd
  rw [Unitization.fst_mul, Unitization.fst_mul,
    Unitization.snd_mul, Unitization.snd_mul]
  simp only [map_add, map_smul, smul_eq_mul]
  rw [ccmRationalAdelicTwistedEpsilonOneNonunital_isTrace x.snd y.snd]
  ring

/-- Genuine cyclic bar of the sealed unitized twisted algebra. -/
abbrev CCMRationalAdelicTwistedSourceCyclicModule : CyclicModule ℂ :=
  cyclicBarCyclicModule (R := ℂ) (A := TwistedSource)

/-- Scalar-part augmentation of the sealed unitization. -/
def ccmRationalAdelicTwistedUnitizationAugmentation :
    TwistedSource →ₗ[ℂ] ℂ :=
  (Unitization.fstHom ℂ TwistedCrossed).toLinearMap

theorem ccmRationalAdelicTwistedUnitizationAugmentation_isTrace
    (x y : TwistedSource) :
    ccmRationalAdelicTwistedUnitizationAugmentation (x * y) =
      ccmRationalAdelicTwistedUnitizationAugmentation (y * x) := by
  change (x * y).fst = (y * x).fst
  rw [Unitization.fst_mul, Unitization.fst_mul, mul_comm]

def ccmRationalAdelicTwistedUnitizationAugmentationCyclicHom :
    CyclicModule.Hom CCMRationalAdelicTwistedSourceCyclicModule
      (scalarConstantCyclicModule (R := ℂ)) :=
  cyclicBarTraceCyclicHom
    ccmRationalAdelicTwistedUnitizationAugmentation
    ccmRationalAdelicTwistedUnitizationAugmentation_isTrace

def ccmRationalAdelicTwistedEpsilonZeroCyclicHom :
    CyclicModule.Hom CCMRationalAdelicTwistedSourceCyclicModule
      (scalarConstantCyclicModule (R := ℂ)) :=
  cyclicBarTraceCyclicHom ccmRationalAdelicTwistedEpsilonZero
    ccmRationalAdelicTwistedEpsilonZero_isTrace

def ccmRationalAdelicTwistedEpsilonOneCyclicHom :
    CyclicModule.Hom CCMRationalAdelicTwistedSourceCyclicModule
      (scalarConstantCyclicModule (R := ℂ)) :=
  cyclicBarTraceCyclicHom ccmRationalAdelicTwistedEpsilonOne
    ccmRationalAdelicTwistedEpsilonOne_isTrace

/-- Nonunital cyclic module: kernel of global unit augmentation. -/
abbrev CCMRationalAdelicTwistedNonunitalSourceCyclicModule :
    CyclicModule ℂ :=
  ccmRationalAdelicTwistedUnitizationAugmentationCyclicHom.doubleKernel
    ccmRationalAdelicTwistedUnitizationAugmentationCyclicHom

def ccmRationalAdelicTwistedNonunitalSourceCyclicInclusion :
    CyclicModule.Hom
      CCMRationalAdelicTwistedNonunitalSourceCyclicModule
      CCMRationalAdelicTwistedSourceCyclicModule :=
  ccmRationalAdelicTwistedUnitizationAugmentationCyclicHom.doubleKernelInclusion
    ccmRationalAdelicTwistedUnitizationAugmentationCyclicHom

def ccmRationalAdelicTwistedNonunitalEpsilonZeroCyclicHom :
    CyclicModule.Hom
      CCMRationalAdelicTwistedNonunitalSourceCyclicModule
      (scalarConstantCyclicModule (R := ℂ)) :=
  CyclicModule.Hom.comp
    ccmRationalAdelicTwistedNonunitalSourceCyclicInclusion
    ccmRationalAdelicTwistedEpsilonZeroCyclicHom

def ccmRationalAdelicTwistedNonunitalEpsilonOneCyclicHom :
    CyclicModule.Hom
      CCMRationalAdelicTwistedNonunitalSourceCyclicModule
      (scalarConstantCyclicModule (R := ℂ)) :=
  CyclicModule.Hom.comp
    ccmRationalAdelicTwistedNonunitalSourceCyclicInclusion
    ccmRationalAdelicTwistedEpsilonOneCyclicHom

/-- Exact reduced cyclic source on the instance-sealed twisted algebra. -/
abbrev CCMRationalAdelicTwistedReducedSourceCyclicModule : CyclicModule ℂ :=
  ccmRationalAdelicTwistedNonunitalEpsilonZeroCyclicHom.doubleKernel
    ccmRationalAdelicTwistedNonunitalEpsilonOneCyclicHom

/-- Canonical inclusion of the sealed reduced source into its full cyclic
bar. -/
def ccmRationalAdelicTwistedReducedSourceCyclicInclusion :
    CyclicModule.Hom CCMRationalAdelicTwistedReducedSourceCyclicModule
      CCMRationalAdelicTwistedSourceCyclicModule :=
  CyclicModule.Hom.comp
    (ccmRationalAdelicTwistedNonunitalEpsilonZeroCyclicHom.doubleKernelInclusion
      ccmRationalAdelicTwistedNonunitalEpsilonOneCyclicHom)
    ccmRationalAdelicTwistedNonunitalSourceCyclicInclusion

end GaloisForLFunctions.RHTower
