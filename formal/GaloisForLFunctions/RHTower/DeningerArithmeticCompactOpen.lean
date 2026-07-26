import GaloisForLFunctions.RHTower.DeningerArithmeticCochainComplex
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Metrizable.ContinuousMap

/-!
# Compact-open source topology for Deninger arithmetic cohomology

Entire functions are realized as the closed complex subspace of `C(ℂ, ℂ)` consisting of
holomorphic maps.  The ambient continuous-map space carries the compact-open topology, so the
source is completely metrizable and Baire.  Evaluation is continuous, and multiplication by the
completed Xi source is a continuous linear differential.

This supplies quotient topological spaces for both the Xi range and its closure.  Their later
topological-vector-space structure is kept separate because the current mathlib quotient-module
instance is not definitionally compatible with this compact-open continuous-map module.  The
statement that reduced and unreduced coboundaries agree is isolated as
`DeningerArithmeticXiRangeClosed`; it is not assumed.
-/

open Complex Filter Set TopologicalSpace Topology

namespace RHTower

noncomputable section

/-- Entire functions as a complex submodule of the compact-open continuous-map space. -/
def deningerCompactOpenEntireSubmodule :
    Submodule ℂ C(ℂ, ℂ) where
  carrier := {F | Differentiable ℂ F}
  zero_mem' := by
    simp
  add_mem' := by
    intro F G hF hG
    simpa using hF.add hG
  smul_mem' := by
    intro c F hF
    simpa using hF.const_smul c

/-- Compact-open Fréchet model of the entire-function source. -/
abbrev DeningerCompactOpenEntire :=
  deningerCompactOpenEntireSubmodule

/-- Evaluate the compact-open entire subtype as an ordinary function. -/
instance deningerCompactOpenEntireCoeFun :
    CoeFun DeningerCompactOpenEntire (fun _ => ℂ → ℂ) :=
  ⟨fun F => F.1.1⟩

/-- Addition on the compact-open entire subtype is continuous. -/
instance deningerCompactOpenEntireContinuousAdd :
    ContinuousAdd DeningerCompactOpenEntire :=
  continuousAdd_induced deningerCompactOpenEntireSubmodule.subtype

/-- Scalar multiplication on the compact-open entire subtype is continuous. -/
instance deningerCompactOpenEntireContinuousSMul :
    ContinuousSMul ℂ DeningerCompactOpenEntire :=
  continuousSMul_induced deningerCompactOpenEntireSubmodule.subtype

/-- Entire functions are sequentially closed under compact-open convergence. -/
theorem isSeqClosed_deningerCompactOpenEntire :
    IsSeqClosed {F : C(ℂ, ℂ) | Differentiable ℂ F} := by
  intro u F hu huF
  have hloc :
      TendstoLocallyUniformly
        (fun n z => u n z) F atTop :=
    ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp huF
  have hdiff :
      ∀ᶠ n in atTop,
        DifferentiableOn ℂ (fun z => u n z) Set.univ := by
    filter_upwards [] with n
    exact (hu n).differentiableOn
  have hlimit :=
    hloc.tendstoLocallyUniformlyOn.differentiableOn
      hdiff isOpen_univ
  intro z
  simpa only [differentiableWithinAt_univ] using
    hlimit z (Set.mem_univ z)

/-- Entire functions form a closed compact-open subspace. -/
theorem isClosed_deningerCompactOpenEntire :
    IsClosed {F : C(ℂ, ℂ) | Differentiable ℂ F} :=
  isSeqClosed_deningerCompactOpenEntire.isClosed

noncomputable instance deningerCompactOpenEntire_complete :
    CompleteSpace DeningerCompactOpenEntire :=
  isClosed_deningerCompactOpenEntire.completeSpace_coe

noncomputable instance deningerCompactOpenEntire_completelyMetrizable :
    IsCompletelyMetrizableSpace DeningerCompactOpenEntire :=
  isClosed_deningerCompactOpenEntire.isCompletelyMetrizableSpace

noncomputable instance deningerCompactOpenEntire_baire :
    BaireSpace DeningerCompactOpenEntire := by
  infer_instance

/-- Forgetful linear equivalence from the compact-open model to the algebraic entire source. -/
def deningerCompactOpenEntireEquiv :
    DeningerCompactOpenEntire ≃ₗ[ℂ] DeningerEntire where
  toFun F := ⟨F.1, F.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun F := ⟨⟨F, F.2.continuous⟩, F.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Completed Xi as an element of the compact-open entire source. -/
def deningerCompactOpenEntireXi : DeningerCompactOpenEntire :=
  ⟨⟨XiC, XiC_differentiable.continuous⟩,
    XiC_differentiable⟩

@[simp]
theorem deningerCompactOpenEntireXi_apply (z : ℂ) :
    deningerCompactOpenEntireXi z = XiC z :=
  rfl

/-- Point evaluation is a continuous linear functional for the compact-open topology. -/
def deningerCompactOpenEvaluation (z : ℂ) :
    DeningerCompactOpenEntire →L[ℂ] ℂ :=
  (ContinuousMap.evalCLM ℂ z).comp
    (deningerCompactOpenEntireSubmodule.subtypeL)

@[simp]
theorem deningerCompactOpenEvaluation_apply
    (z : ℂ) (F : DeningerCompactOpenEntire) :
    deningerCompactOpenEvaluation z F = F z :=
  rfl

/-- Continuous degree-zero differential: multiplication by completed Xi. -/
def deningerCompactOpenXiMul :
    DeningerCompactOpenEntire →L[ℂ] DeningerCompactOpenEntire where
  toFun F :=
    ⟨deningerCompactOpenEntireXi.1 * F.1,
      deningerCompactOpenEntireXi.2.mul F.2⟩
  map_add' F G := by
    ext z
    simp
    ring
  map_smul' c F := by
    ext z
    simp
    ring
  cont := by
    apply Continuous.subtype_mk
    exact continuous_const.mul continuous_subtype_val

@[simp]
theorem deningerCompactOpenXiMul_apply
    (F : DeningerCompactOpenEntire) (z : ℂ) :
    deningerCompactOpenXiMul F z = XiC z * F z :=
  rfl

/-- Compact-open Xi multiplication agrees with the algebraic source differential. -/
theorem deningerCompactOpenEntireEquiv_XiMul
    (F : DeningerCompactOpenEntire) :
    deningerCompactOpenEntireEquiv (deningerCompactOpenXiMul F) =
      deningerEntireXi * deningerCompactOpenEntireEquiv F :=
  rfl

/-- The compact-open Xi differential remains injective. -/
theorem deningerCompactOpenXiMul_injective :
    Function.Injective deningerCompactOpenXiMul := by
  intro F G hFG
  apply deningerCompactOpenEntireEquiv.injective
  apply deningerEntireXi_mul_injective
  simpa only [deningerCompactOpenEntireEquiv_XiMul] using
    congrArg deningerCompactOpenEntireEquiv hFG

/-- Algebraic coboundary range in the compact-open entire source. -/
def deningerCompactOpenXiRange :
    Submodule ℂ DeningerCompactOpenEntire :=
  LinearMap.range deningerCompactOpenXiMul.toLinearMap

/-- Additive quotient relation attached to a compact-open coboundary submodule. -/
def deningerCompactOpenQuotientRel
    (S : Submodule ℂ DeningerCompactOpenEntire) :
    Setoid DeningerCompactOpenEntire :=
  QuotientAddGroup.leftRel S.toAddSubgroup

/-- Unreduced compact-open middle-cohomology quotient topology. -/
abbrev DeningerArithmeticCompactOpenH1 :=
  Quotient
    (deningerCompactOpenQuotientRel deningerCompactOpenXiRange)

/-- Canonical class in the unreduced compact-open quotient. -/
def deningerArithmeticCompactOpenH1Class
    (F : DeningerCompactOpenEntire) :
    DeningerArithmeticCompactOpenH1 :=
  Quotient.mk
    (deningerCompactOpenQuotientRel deningerCompactOpenXiRange) F

/-- Closed coboundary range used in reduced topological cohomology. -/
def deningerCompactOpenXiClosedRange :
    Submodule ℂ DeningerCompactOpenEntire :=
  deningerCompactOpenXiRange.topologicalClosure

/-- Reduced compact-open middle-cohomology quotient topology. -/
abbrev DeningerArithmeticReducedCompactOpenH1 :=
  Quotient
    (deningerCompactOpenQuotientRel
      deningerCompactOpenXiClosedRange)

/-- Canonical class in the reduced compact-open quotient. -/
def deningerArithmeticReducedCompactOpenH1Class
    (F : DeningerCompactOpenEntire) :
    DeningerArithmeticReducedCompactOpenH1 :=
  Quotient.mk
    (deningerCompactOpenQuotientRel
      deningerCompactOpenXiClosedRange) F

/-- Exact closed-range conjecture separating unreduced from reduced arithmetic cohomology. -/
def DeningerArithmeticXiRangeClosed : Prop :=
  IsClosed (deningerCompactOpenXiRange : Set DeningerCompactOpenEntire)

/-- Under the named closed-range conjecture, the reduced and unreduced coboundaries coincide. -/
theorem deningerCompactOpenXiClosedRange_eq
    (hclosed : DeningerArithmeticXiRangeClosed) :
    deningerCompactOpenXiClosedRange =
      deningerCompactOpenXiRange := by
  apply SetLike.ext'
  change
    closure
        (deningerCompactOpenXiRange :
          Set DeningerCompactOpenEntire) =
      deningerCompactOpenXiRange
  exact hclosed.closure_eq

/-- The reduced coboundary range is closed unconditionally. -/
theorem isClosed_deningerCompactOpenXiClosedRange :
    IsClosed
      (deningerCompactOpenXiClosedRange :
        Set DeningerCompactOpenEntire) :=
  Submodule.isClosed_topologicalClosure
    deningerCompactOpenXiRange

end

end RHTower
