/-
Relation--incidence horizon fusion and the strict-right integral nuclear defect.

Completion escape cannot be represented by a closed single-valued operator: its intrinsic
carrier is the multivalued horizon of a closed linear relation.  This module proves that imposing
an output incidence law commutes exactly with taking that horizon.  It then specializes the law
to the literal-source Meyer Xi relation and the all-cross-prime Calderon--Witt incidence complex.
One strict-right Xi copy becomes the unique full-support prime-mixed horizon, whose rank-one
projection is Schatten-1 and has trace one.
-/
import GaloisForLFunctions.RHTower.DeningerMeyerHalfDensityXiGraphClosure
import GaloisForLFunctions.RHTower.DeningerCalderonWittAllCrossPrimeIncidenceKoszul
import GaloisForLFunctions.RHTower.CCMShiftedXiCancellation
import GaloisForLFunctions.RHTower.NuclearRankOneSchatten
import GaloisForLFunctions.HTGeometry.PointedFisherCutoffWardTrace

open Complex Set Topology

namespace RHTower

noncomputable section

section RelationIncidence

variable {k X Y Z : Type*} [Field k]
  [AddCommGroup X] [Module k X]
  [AddCommGroup Y] [Module k Y]
  [AddCommGroup Z] [Module k Z]

/-- Inclusion of the output fibre as the vertical part of a linear relation. -/
def relationVerticalInclusion : Y →ₗ[k] X × Y where
  toFun y := (0, y)
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

/-- Output coordinate of a linear relation. -/
def relationOutput : X × Y →ₗ[k] Y where
  toFun xy := xy.2
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

/-- Multivalued horizon: outputs paired with zero source. -/
def linearRelationMultivaluedHorizon (R : Submodule k (X × Y)) : Submodule k Y :=
  R.comap relationVerticalInclusion

/-- Impose an output incidence law before reading a relation's vertical horizon. -/
def linearRelationIncidenceTotal
    (R : Submodule k (X × Y)) (δ : Y →ₗ[k] Z) : Submodule k (X × Y) :=
  R ⊓ LinearMap.ker (δ.comp relationOutput)

/-- Verticalization commutes exactly with incidence totalization. -/
theorem linearRelationMultivaluedHorizon_incidenceTotal
    (R : Submodule k (X × Y)) (δ : Y →ₗ[k] Z) :
    linearRelationMultivaluedHorizon (linearRelationIncidenceTotal R δ) =
      linearRelationMultivaluedHorizon R ⊓ LinearMap.ker δ := by
  ext y
  simp [linearRelationMultivaluedHorizon, linearRelationIncidenceTotal,
    relationVerticalInclusion, relationOutput]

end RelationIncidence

/-- Vertical horizon of the completed literal-source Xi relation at a strict-right copy. -/
def xiRightScalarVerticalHorizon (q : XiRightZeroCopy) : Submodule ℂ ℂ :=
  (deningerMeyerHalfDensityXiGraph q.1.1).topologicalClosure.comap
    (LinearMap.inr ℂ DeningerMeyerHalfDensityCompletion ℂ)

theorem xiRight_support_re_ne_half (q : XiRightZeroCopy) :
    (q.1.1 : ℂ).re ≠ 1 / 2 := by
  intro h
  have hcenter := congrArg Complex.re (xiRightCenteredZero_eq_support_sub_half q)
  simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re] at hcenter
  have hzero : (xiRightCenteredZero q).re = 0 := by linarith
  linarith [xiRightCenteredZero_re_pos q]

/-- Off-line closure makes the literal-source Xi relation maximally multivalued. -/
theorem xiRightScalarVerticalHorizon_eq_top (q : XiRightZeroCopy) :
    xiRightScalarVerticalHorizon q = ⊤ := by
  apply top_unique
  intro y hy
  exact deningerMeyerHalfDensityXiGraph_fullVertical_of_offline
    q.1.1 (xiRight_support_re_ne_half q) y

/-- Send the scalar vertical fibre into the full-support all-prime horizon. -/
def xiRightPrimeMixedVerticalHorizon (q : XiRightZeroCopy) :
    Submodule ℂ DeningerCalderonWittCrossPrimePacketHilbert :=
  (xiRightScalarVerticalHorizon q).map
    (LinearMap.toSpanSingleton ℂ
      DeningerCalderonWittCrossPrimePacketHilbert
      deningerCalderonWittCrossPrimePacketHorizon)

/-- All cross-prime incidences fuse the replicated off-line fibre into exactly one line. -/
theorem xiRightPrimeMixedVerticalHorizon_eq_incidenceKernel
    (q : XiRightZeroCopy) :
    xiRightPrimeMixedVerticalHorizon q =
      LinearMap.ker deningerCalderonWittPacketKoszulDifferential := by
  rw [xiRightPrimeMixedVerticalHorizon, xiRightScalarVerticalHorizon_eq_top,
    Submodule.map_top]
  exact ker_deningerCalderonWittPacketKoszulDifferential.symm

/-- Strict-right target fibre of the pre-divisor horizon defect. -/
def xiRightPrimeMixedHorizonDefect (_q : XiRightZeroCopy) :
    DeningerCalderonWittCrossPrimePacketHilbert →L[ℂ]
      DeningerCalderonWittCrossPrimePacketHilbert :=
  InnerProductSpace.rankOne ℂ
    deningerCalderonWittCrossPrimePacketHorizon
    deningerCalderonWittCrossPrimePacketHorizon

theorem xiRightPrimeMixedHorizonDefect_hasRankLE_one (q : XiRightZeroCopy) :
    HasRankLE (xiRightPrimeMixedHorizonDefect q) 1 := by
  have h := hasRankLE_sum_range_rankOne
    (fun _ : ℕ => deningerCalderonWittCrossPrimePacketHorizon)
    (fun _ : ℕ => deningerCalderonWittCrossPrimePacketHorizon) 1
  simpa [xiRightPrimeMixedHorizonDefect] using h

/-- The prime-mixed strict-right defect is nuclear in the project's Schatten-1 sense. -/
theorem xiRightPrimeMixedHorizonDefect_memSchattenClass_one
    (q : XiRightZeroCopy) :
    MemSchattenClass 1 (xiRightPrimeMixedHorizonDefect q) :=
  memSchattenClass_of_hasRankLE one_pos
    (xiRightPrimeMixedHorizonDefect_hasRankLE_one q)

/-- The integral target already costs exactly one full nuclear unit. -/
theorem traceNorm_xiRightPrimeMixedHorizonDefect (q : XiRightZeroCopy) :
    traceNorm DeningerCalderonWittCrossPrimePacketHilbert
      (xiRightPrimeMixedHorizonDefect q) = 1 := by
  rw [traceNorm_eq_norm_of_hasRankLE_one
      (xiRightPrimeMixedHorizonDefect_hasRankLE_one q),
    xiRightPrimeMixedHorizonDefect, InnerProductSpace.norm_rankOne,
    deningerCalderonWittCrossPrimePacketHorizon_norm]
  norm_num

@[simp] theorem xiRightPrimeMixedHorizonDefect_apply_horizon
    (q : XiRightZeroCopy) :
    xiRightPrimeMixedHorizonDefect q
      deningerCalderonWittCrossPrimePacketHorizon =
        deningerCalderonWittCrossPrimePacketHorizon := by
  rw [xiRightPrimeMixedHorizonDefect, InnerProductSpace.rankOne_apply]
  rw [inner_self_eq_norm_sq_to_K,
    deningerCalderonWittCrossPrimePacketHorizon_norm]
  simp

/-- The nuclear horizon defect carries the indivisible integer one. -/
theorem opTrace_xiRightPrimeMixedHorizonDefect (q : XiRightZeroCopy) :
    ContinuousLinearMap.opTrace (xiRightPrimeMixedHorizonDefect q) = 1 := by
  rw [xiRightPrimeMixedHorizonDefect,
    GaloisForLFunctions.HTGeometry.opTrace_rankOne]
  rw [inner_self_eq_norm_sq_to_K,
    deningerCalderonWittCrossPrimePacketHorizon_norm]
  norm_num

end
end RHTower
