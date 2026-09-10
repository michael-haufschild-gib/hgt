import GaloisForLFunctions.RHTower.FokasLenellsCausalBoundedPolynomialExponential

/-! Actual entire polynomial evolution on the genuine bounded Cauchy derivative space. -/
open Complex MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance causalPolynomialGroupLowerComplete : CompleteSpace (hardyL2ᗮ) := hardyL2.isClosed_orthogonal.completeSpace_coe
local instance causalPolynomialGroupChainComplete : CompleteSpace causalBoundedChain := causalBoundedChain_complete
local instance causalPolynomialGroupChainNormedGroup : NormedAddCommGroup causalBoundedChain := causalBoundedChain.normedAddCommGroup
local instance causalPolynomialGroupChainNormedSpace : NormedSpace ℂ causalBoundedChain := causalBoundedChain.normedSpace
local instance causalPolynomialGroupEndNormedRing : NormedRing (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  ContinuousLinearMap.toNormedRing
local instance causalPolynomialGroupEndTopology : TopologicalSpace (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  (inferInstance : NormedAddCommGroup
    (causalBoundedChain →L[ℂ] causalBoundedChain)).toUniformSpace.toTopologicalSpace
local instance causalPolynomialGroupEndTopologicalRing : IsTopologicalRing (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  NonUnitalSeminormedRing.toIsTopologicalRing

local instance causalPolynomialGroupEndNormedAlgebra : NormedAlgebra ℂ (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  ContinuousLinearMap.toNormedAlgebra
local instance causalPolynomialGroupEndNormOne : NormOneClass (causalBoundedChain →L[ℂ] causalBoundedChain) := ⟨by
  have he := congrArg (fun A : causalBoundedChain →L[ℂ] causalBoundedChain => ‖A‖)
    causalBoundedChainExponential_zero
  exact he.symm.trans (norm_causalBoundedChainExponential_real (0 : ℝ≥0))⟩


open Polynomial
local instance causalPolynomialGroupEndRationalAlgebra :
    NormedAlgebra ℚ (causalBoundedChain →L[ℂ] causalBoundedChain) := .restrictScalars ℚ ℂ _

/-- All polynomial differential operators commute on the actual bounded chain space. -/
theorem causalBoundedPolynomialOperator_commute (p q : ℂ[X]) :
    Commute (causalBoundedPolynomialOperator p) (causalBoundedPolynomialOperator q) := by
  have hm := congrArg (fun r : ℂ[X] => causalBoundedPolynomialOperator r) (mul_comm p q)
  have hp : causalBoundedPolynomialOperator (p*q) =
      causalBoundedPolynomialOperator p * causalBoundedPolynomialOperator q :=
    (Polynomial.aeval causalBoundedChainShift).map_mul p q
  have hq : causalBoundedPolynomialOperator (q*p) =
      causalBoundedPolynomialOperator q * causalBoundedPolynomialOperator p :=
    (Polynomial.aeval causalBoundedChainShift).map_mul q p
  exact hp.symm.trans (hm.trans hq)

/-- The actual polynomial flow obeys the complex additive group law. -/
theorem causalBoundedPolynomialExponential_add (p : ℂ[X]) (z w : ℂ) :
    causalBoundedPolynomialExponential p (z+w) =
      causalBoundedPolynomialExponential p z * causalBoundedPolynomialExponential p w := by
  have he : (z+w) • causalBoundedPolynomialOperator p =
      z • causalBoundedPolynomialOperator p + w • causalBoundedPolynomialOperator p := add_smul z w _
  exact (congrArg (fun A : causalBoundedChain →L[ℂ] causalBoundedChain => NormedSpace.exp A) he).trans
    (NormedSpace.exp_add_of_commute
      (((Commute.refl (causalBoundedPolynomialOperator p)).smul_left z).smul_right w))

/-- Negative complex time recovers every genuine chain. -/
theorem causalBoundedPolynomialExponential_neg_apply (p : ℂ[X]) (z : ℂ) (u : causalBoundedChain) :
    causalBoundedPolynomialExponential p (-z) (causalBoundedPolynomialExponential p z u) = u := by
  have h := congrArg (fun A : causalBoundedChain →L[ℂ] causalBoundedChain => A u)
    (causalBoundedPolynomialExponential_add p (-z) z)
  have hz : causalBoundedPolynomialExponential p 0 u = u :=
    congrArg (fun A : causalBoundedChain →L[ℂ] causalBoundedChain => A u) (causalBoundedPolynomialExponential_zero p)
  have hs : causalBoundedPolynomialExponential p (-z+z) u = u :=
    (congrArg (fun q : ℂ => causalBoundedPolynomialExponential p q u) (neg_add_cancel z)).trans hz
  exact h.symm.trans hs

/-- The opposite order of actual time reversal is also the identity. -/
theorem causalBoundedPolynomialExponential_apply_neg (p : ℂ[X]) (z : ℂ) (u : causalBoundedChain) :
    causalBoundedPolynomialExponential p z (causalBoundedPolynomialExponential p (-z) u) = u := by
  simpa only [neg_neg] using causalBoundedPolynomialExponential_neg_apply p (-z) u

/-- Every polynomial evolution is an actual continuous linear automorphism. -/
def causalBoundedPolynomialEntireGroup (p : ℂ[X]) (z : ℂ) : causalBoundedChain ≃L[ℂ] causalBoundedChain where
  toLinearMap := (causalBoundedPolynomialExponential p z).toLinearMap
  invFun := causalBoundedPolynomialExponential p (-z)
  left_inv := causalBoundedPolynomialExponential_neg_apply p z
  right_inv := causalBoundedPolynomialExponential_apply_neg p z
  continuous_toFun := (causalBoundedPolynomialExponential p z).continuous
  continuous_invFun := (causalBoundedPolynomialExponential p (-z)).continuous

/-- Combining arbitrary polynomial flows gives the flow of their scalar-weighted polynomial sum. -/
theorem causalBoundedPolynomialExponential_mix (p q : ℂ[X]) (z w : ℂ) :
    causalBoundedPolynomialExponential (z • p + w • q) 1 =
      causalBoundedPolynomialExponential p z * causalBoundedPolynomialExponential q w := by
  have hp : causalBoundedPolynomialOperator (z • p) = z • causalBoundedPolynomialOperator p :=
    (Polynomial.aeval causalBoundedChainShift).toLinearMap.map_smul z p
  have hq : causalBoundedPolynomialOperator (w • q) = w • causalBoundedPolynomialOperator q :=
    (Polynomial.aeval causalBoundedChainShift).toLinearMap.map_smul w q
  have ha : causalBoundedPolynomialOperator (z • p + w • q) =
      causalBoundedPolynomialOperator (z • p) + causalBoundedPolynomialOperator (w • q) :=
    (Polynomial.aeval causalBoundedChainShift).map_add (z • p) (w • q)
  have hs : (1 : ℂ) • causalBoundedPolynomialOperator (z • p + w • q) =
      z • causalBoundedPolynomialOperator p + w • causalBoundedPolynomialOperator q :=
    (one_smul ℂ _).trans (ha.trans (congrArg₂ (fun A B : causalBoundedChain →L[ℂ] causalBoundedChain => A+B) hp hq))
  exact (congrArg (fun A : causalBoundedChain →L[ℂ] causalBoundedChain => NormedSpace.exp A) hs).trans
    (NormedSpace.exp_add_of_commute (((causalBoundedPolynomialOperator_commute p q).smul_left z).smul_right w))

/-- Arbitrary polynomial differential flows commute without an added compatibility hypothesis. -/
theorem causalBoundedPolynomialExponential_commute (p q : ℂ[X]) (z w : ℂ) :
    Commute (causalBoundedPolynomialExponential p z) (causalBoundedPolynomialExponential q w) := by
  have h := congrArg (fun r : ℂ[X] => causalBoundedPolynomialExponential r 1) (add_comm (z • p) (w • q))
  exact (causalBoundedPolynomialExponential_mix p q z w).symm.trans
    (h.trans (causalBoundedPolynomialExponential_mix q p w z))

/-- Sequential evolution of every genuine datum is independent of the order of polynomial flows. -/
theorem causalBoundedPolynomialExponential_commute_apply (p q : ℂ[X]) (z w : ℂ)
    (u : causalBoundedChain) :
    causalBoundedPolynomialExponential p z (causalBoundedPolynomialExponential q w u) =
      causalBoundedPolynomialExponential q w (causalBoundedPolynomialExponential p z u) :=
  congrArg (fun A : causalBoundedChain →L[ℂ] causalBoundedChain => A u)
    (causalBoundedPolynomialExponential_commute p q z w)

end
end RHTower.FokasLenells
