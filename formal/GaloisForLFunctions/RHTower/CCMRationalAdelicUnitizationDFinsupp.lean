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

/-- Dependent coefficient space of one unitized label. -/
abbrev CCMRationalAdelicUnitizedFiber : CCMRationalAdelicUnitizedLabel → Type
  | .scalar => ℂ
  | .crossed _ => Core

instance : (label : CCMRationalAdelicUnitizedLabel) →
    AddCommMonoid (CCMRationalAdelicUnitizedFiber label)
  | .scalar => inferInstanceAs (AddCommMonoid ℂ)
  | .crossed _ => inferInstanceAs (AddCommMonoid Core)

instance : (label : CCMRationalAdelicUnitizedLabel) →
    Module ℂ (CCMRationalAdelicUnitizedFiber label)
  | .scalar => inferInstanceAs (Module ℂ ℂ)
  | .crossed _ => inferInstanceAs (Module ℂ Core)

abbrev CCMRationalAdelicUnitizedDFinsupp :=
  Π₀ label : CCMRationalAdelicUnitizedLabel,
    CCMRationalAdelicUnitizedFiber label

private def ccmRationalAdelicCrossedToUnitizedDFinsupp :
    Crossed →ₗ[ℂ] CCMRationalAdelicUnitizedDFinsupp :=
  (Finsupp.lsum ℂ) fun k =>
    DFinsupp.lsingle
      (M := CCMRationalAdelicUnitizedFiber)
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
    simp only [RingHom.id_apply]
    module

/-- Reassembly of the dependent coefficient family into the minimal unitization. -/
def ccmRationalAdelicUnitizedDFinsuppToSource :
    CCMRationalAdelicUnitizedDFinsupp →ₗ[ℂ] Source :=
  (DFinsupp.lsum ℂ) ccmRationalAdelicUnitizedLabelToSource

@[simp]
theorem ccmRationalAdelicCrossedToUnitizedDFinsupp_single
    (k : Scale) (t : Core) :
    ccmRationalAdelicCrossedToUnitizedDFinsupp (Finsupp.single k t) =
      DFinsupp.single (CCMRationalAdelicUnitizedLabel.crossed k) t := by
  classical
  simp [ccmRationalAdelicCrossedToUnitizedDFinsupp]

@[simp]
theorem ccmRationalAdelicCrossedToUnitizedDFinsupp_apply_crossed
    (F : Crossed) (k : Scale) :
    ccmRationalAdelicCrossedToUnitizedDFinsupp F
        (CCMRationalAdelicUnitizedLabel.crossed k) = F k := by
  classical
  induction F using Finsupp.induction with
  | zero => simp
  | @single_add l t F hlt ht hF =>
      rw [map_add, ccmRationalAdelicCrossedToUnitizedDFinsupp_single]
      simp only [DFinsupp.add_apply, Finsupp.add_apply]
      rw [hF]
      by_cases hlk : l = k
      · subst l
        simp
      · simp [hlk]

@[simp]
theorem ccmRationalAdelicCrossedToUnitizedDFinsupp_apply_scalar
    (F : Crossed) :
    ccmRationalAdelicCrossedToUnitizedDFinsupp F
        CCMRationalAdelicUnitizedLabel.scalar = 0 := by
  classical
  induction F using Finsupp.induction with
  | zero => simp
  | @single_add k t F hkt ht hF =>
      rw [map_add, ccmRationalAdelicCrossedToUnitizedDFinsupp_single]
      simp only [DFinsupp.add_apply]
      rw [hF]
      simp

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

@[simp]
theorem ccmRationalAdelicUnitizedDFinsuppToSource_single_crossed
    (k : Scale) (t : Core) :
    ccmRationalAdelicUnitizedDFinsuppToSource
        (DFinsupp.single (CCMRationalAdelicUnitizedLabel.crossed k) t) =
      (Finsupp.single k t : Crossed) := by
  classical
  simp [ccmRationalAdelicUnitizedDFinsuppToSource,
    ccmRationalAdelicUnitizedLabelToSource]

theorem ccmRationalAdelicUnitizedDFinsuppToSource_fst
    (d : CCMRationalAdelicUnitizedDFinsupp) :
    (ccmRationalAdelicUnitizedDFinsuppToSource d).fst =
      d CCMRationalAdelicUnitizedLabel.scalar := by
  classical
  induction d using DFinsupp.induction with
  | h0 => simp
  | ha label value d hvalue hd hInd =>
      rw [map_add, Unitization.fst_add, hInd, DFinsupp.add_apply]
      cases label with
      | scalar =>
          rw [ccmRationalAdelicUnitizedDFinsuppToSource_single_scalar]
          rfl
      | crossed k =>
          rw [ccmRationalAdelicUnitizedDFinsuppToSource_single_crossed]
          simp

theorem ccmRationalAdelicUnitizedDFinsuppToSource_snd_apply
    (d : CCMRationalAdelicUnitizedDFinsupp) (k : Scale) :
    (ccmRationalAdelicUnitizedDFinsuppToSource d).snd k =
      d (CCMRationalAdelicUnitizedLabel.crossed k) := by
  classical
  induction d using DFinsupp.induction with
  | h0 => simp
  | ha label value d hvalue hd hInd =>
      rw [map_add, Unitization.snd_add, Finsupp.add_apply, hInd,
        DFinsupp.add_apply]
      cases label with
      | scalar =>
          rw [ccmRationalAdelicUnitizedDFinsuppToSource_single_scalar]
          rfl
      | crossed l =>
          rw [ccmRationalAdelicUnitizedDFinsuppToSource_single_crossed]
          by_cases hlk : l = k
          · subst l
            simp
          · simp [hlk]

/-- Exact linear equivalence between the minimal unitization and scalar/crossed dependent
coefficients. -/
def ccmRationalAdelicSourceUnitizedDFinsuppEquiv :
    Source ≃ₗ[ℂ] CCMRationalAdelicUnitizedDFinsupp where
  toLinearMap := ccmRationalAdelicSourceToUnitizedDFinsupp
  invFun := ccmRationalAdelicUnitizedDFinsuppToSource
  left_inv x := by
    apply Unitization.ext
    · rw [ccmRationalAdelicUnitizedDFinsuppToSource_fst]
      change ccmRationalAdelicSourceToUnitizedDFinsupp x
          CCMRationalAdelicUnitizedLabel.scalar = x.fst
      rw [ccmRationalAdelicSourceToUnitizedDFinsupp_apply_scalar]
    · apply Finsupp.ext
      intro k
      rw [ccmRationalAdelicUnitizedDFinsuppToSource_snd_apply]
      change ccmRationalAdelicSourceToUnitizedDFinsupp x
          (CCMRationalAdelicUnitizedLabel.crossed k) = x.snd k
      rw [ccmRationalAdelicSourceToUnitizedDFinsupp_apply_crossed]
  right_inv d := by
    apply DFinsupp.ext
    intro label
    cases label with
    | scalar =>
        change ccmRationalAdelicSourceToUnitizedDFinsupp
          (ccmRationalAdelicUnitizedDFinsuppToSource d)
            CCMRationalAdelicUnitizedLabel.scalar = _
        rw [ccmRationalAdelicSourceToUnitizedDFinsupp_apply_scalar,
          ccmRationalAdelicUnitizedDFinsuppToSource_fst]
    | crossed k =>
        change ccmRationalAdelicSourceToUnitizedDFinsupp
          (ccmRationalAdelicUnitizedDFinsuppToSource d)
            (CCMRationalAdelicUnitizedLabel.crossed k) = _
        rw [ccmRationalAdelicSourceToUnitizedDFinsupp_apply_crossed,
          ccmRationalAdelicUnitizedDFinsuppToSource_snd_apply]

@[simp]
theorem ccmRationalAdelicSourceToUnitizedDFinsupp_unitizedDFinsuppToSource
    (d : CCMRationalAdelicUnitizedDFinsupp) :
    ccmRationalAdelicSourceToUnitizedDFinsupp
        (ccmRationalAdelicUnitizedDFinsuppToSource d) = d :=
  ccmRationalAdelicSourceUnitizedDFinsuppEquiv.apply_symm_apply d

end RHTower
end GaloisForLFunctions
