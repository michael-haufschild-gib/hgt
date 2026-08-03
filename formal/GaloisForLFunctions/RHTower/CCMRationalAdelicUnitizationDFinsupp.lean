import GaloisForLFunctions.RHTower.CCMRationalAdelicCyclicRestrictionLinear

/-!
# Minimal unitization as a dependent finitely supported coefficient family

The normalized higher CCM restriction must distinguish the scalar unit from trace-class crossed-
product sectors.  This file gives the exact linear decomposition of the minimal unitization as a
dependent finitely supported family with one scalar label and one Bruhat-core fiber for every
rational scaling label.  It is the input required by `PiTensorProduct.ofDFinsuppEquiv` for the
mixed scalar/nonunital cyclic sectors.
-/

noncomputable section

namespace GaloisForLFunctions
namespace RHTower

private abbrev Core := CCMRationalAdelicBruhatSimpleTensor
private abbrev Scale := CCMRationalAdelicScaling
private abbrev Crossed := CCMRationalAdelicAlgebraicCrossedProduct
private abbrev Source := CCMRationalAdelicCyclicSourceAlgebra

/-- Labels in the exact minimal unitization: scalar unit or a crossed-product scaling sector. -/
inductive CCMRationalAdelicUnitizedLabel
  | scalar
  | crossed (k : Scale)
deriving DecidableEq

/-- Dependent coefficient module of one unitized label. -/
def CCMRationalAdelicUnitizedFiber :
    CCMRationalAdelicUnitizedLabel → ModuleCat ℂ
  | .scalar => ModuleCat.of ℂ ℂ
  | .crossed _ => ModuleCat.of ℂ Core

abbrev CCMRationalAdelicUnitizedDFinsupp :=
  Π₀ label : CCMRationalAdelicUnitizedLabel,
    CCMRationalAdelicUnitizedFiber label

private def ccmRationalAdelicCrossedToUnitizedDFinsupp :
    Crossed →ₗ[ℂ] CCMRationalAdelicUnitizedDFinsupp :=
  (Finsupp.lsum ℂ) fun k =>
    DFinsupp.lsingle
      (M := fun label => (CCMRationalAdelicUnitizedFiber label : Type))
      (CCMRationalAdelicUnitizedLabel.crossed k)

private def ccmRationalAdelicScalarToSource : ℂ →ₗ[ℂ] Source where
  __ := Algebra.linearMap ℂ Source

private def ccmRationalAdelicUnitizedLabelToSource :
    (label : CCMRationalAdelicUnitizedLabel) →
      CCMRationalAdelicUnitizedFiber label →ₗ[ℂ] Source
  | .scalar => ccmRationalAdelicScalarToSource
  | .crossed k =>
      (Unitization.inrHom ℂ ℂ Crossed).comp
        (Finsupp.lsingle (R := ℂ) k)

/-- Linear expansion of the minimal unitization into its dependent coefficient family. -/
def ccmRationalAdelicSourceToUnitizedDFinsupp :
    Source →ₗ[ℂ] CCMRationalAdelicUnitizedDFinsupp where
  toFun x :=
    DFinsupp.single CCMRationalAdelicUnitizedLabel.scalar x.fst +
      ccmRationalAdelicCrossedToUnitizedDFinsupp x.snd
  map_add' x y := by
    simp only [Unitization.fst_add, Unitization.snd_add, map_add]
    rw [DFinsupp.single_add]
    abel
  map_smul' z x := by
    simp only [Unitization.fst_smul, Unitization.snd_smul, map_smul]
    rw [DFinsupp.single_smul]
    module

/-- Reassembly of the dependent coefficient family into the minimal unitization. -/
def ccmRationalAdelicUnitizedDFinsuppToSource :
    CCMRationalAdelicUnitizedDFinsupp →ₗ[ℂ] Source :=
  (DFinsupp.lsum ℂ) ccmRationalAdelicUnitizedLabelToSource

@[simp]
theorem ccmRationalAdelicCrossedToUnitizedDFinsupp_apply_crossed
    (F : Crossed) (k : Scale) :
    ccmRationalAdelicCrossedToUnitizedDFinsupp F
        (CCMRationalAdelicUnitizedLabel.crossed k) = F k := by
  classical
  induction F using Finsupp.induction with
  | zero => simp [ccmRationalAdelicCrossedToUnitizedDFinsupp]
  | @single_add l t F hlt ht hF =>
      by_cases hlk : l = k
      · subst l
        simp [ccmRationalAdelicCrossedToUnitizedDFinsupp, hF]
      · simp [ccmRationalAdelicCrossedToUnitizedDFinsupp, hF, hlk]

@[simp]
theorem ccmRationalAdelicCrossedToUnitizedDFinsupp_apply_scalar
    (F : Crossed) :
    ccmRationalAdelicCrossedToUnitizedDFinsupp F
        CCMRationalAdelicUnitizedLabel.scalar = 0 := by
  classical
  induction F using Finsupp.induction with
  | zero => simp [ccmRationalAdelicCrossedToUnitizedDFinsupp]
  | @single_add k t F hkt ht hF =>
      simp [ccmRationalAdelicCrossedToUnitizedDFinsupp, hF]

@[simp]
theorem ccmRationalAdelicSourceToUnitizedDFinsupp_apply_scalar (x : Source) :
    ccmRationalAdelicSourceToUnitizedDFinsupp x
        CCMRationalAdelicUnitizedLabel.scalar = x.fst := by
  classical
  simp [ccmRationalAdelicSourceToUnitizedDFinsupp]

@[simp]
theorem ccmRationalAdelicSourceToUnitizedDFinsupp_apply_crossed
    (x : Source) (k : Scale) :
    ccmRationalAdelicSourceToUnitizedDFinsupp x
        (CCMRationalAdelicUnitizedLabel.crossed k) = x.snd k := by
  classical
  simp [ccmRationalAdelicSourceToUnitizedDFinsupp]

@[simp]
theorem ccmRationalAdelicUnitizedDFinsuppToSource_single_scalar (z : ℂ) :
    ccmRationalAdelicUnitizedDFinsuppToSource
        (DFinsupp.single CCMRationalAdelicUnitizedLabel.scalar z) =
      algebraMap ℂ Source z := by
  classical
  simp [ccmRationalAdelicUnitizedDFinsuppToSource,
    ccmRationalAdelicUnitizedLabelToSource, ccmRationalAdelicScalarToSource]
  rfl

@[simp]
theorem ccmRationalAdelicUnitizedDFinsuppToSource_single_crossed
    (k : Scale) (t : Core) :
    ccmRationalAdelicUnitizedDFinsuppToSource
        (DFinsupp.single (CCMRationalAdelicUnitizedLabel.crossed k) t) =
      (Finsupp.single k t : Crossed) := by
  classical
  simp [ccmRationalAdelicUnitizedDFinsuppToSource,
    ccmRationalAdelicUnitizedLabelToSource]
  rfl

/-- Exact linear equivalence between the minimal unitization and scalar/crossed dependent
coefficients. -/
def ccmRationalAdelicSourceUnitizedDFinsuppEquiv :
    Source ≃ₗ[ℂ] CCMRationalAdelicUnitizedDFinsupp where
  toLinearMap := ccmRationalAdelicSourceToUnitizedDFinsupp
  invFun := ccmRationalAdelicUnitizedDFinsuppToSource
  left_inv x := by
    apply Unitization.ext
    · change (ccmRationalAdelicUnitizedDFinsuppToSource
          (ccmRationalAdelicSourceToUnitizedDFinsupp x)).fst = x.fst
      simp [ccmRationalAdelicUnitizedDFinsuppToSource,
        ccmRationalAdelicUnitizedLabelToSource]
    · change (ccmRationalAdelicUnitizedDFinsuppToSource
          (ccmRationalAdelicSourceToUnitizedDFinsupp x)).snd = x.snd
      ext k
      simp [ccmRationalAdelicUnitizedDFinsuppToSource,
        ccmRationalAdelicUnitizedLabelToSource]
  right_inv d := by
    apply DFinsupp.ext
    intro label
    cases label with
    | scalar =>
        simp
    | crossed k =>
        simp

end RHTower
end GaloisForLFunctions
