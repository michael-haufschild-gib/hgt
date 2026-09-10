import GaloisForLFunctions.RHTower.FokasLenellsCausalBoundedPolynomialExponential

/-! Actual entire polynomial evolution on the genuine bounded Cauchy derivative space. -/
open Complex MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance causalPolynomialOrbitLowerComplete : CompleteSpace (hardyL2ᗮ) := hardyL2.isClosed_orthogonal.completeSpace_coe
local instance causalPolynomialOrbitChainComplete : CompleteSpace causalBoundedChain := causalBoundedChain_complete
local instance causalPolynomialOrbitChainNormedGroup : NormedAddCommGroup causalBoundedChain := causalBoundedChain.normedAddCommGroup
local instance causalPolynomialOrbitChainNormedSpace : NormedSpace ℂ causalBoundedChain := causalBoundedChain.normedSpace
local instance causalPolynomialOrbitEndNormedRing : NormedRing (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  ContinuousLinearMap.toNormedRing
local instance causalPolynomialOrbitEndTopology : TopologicalSpace (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  (inferInstance : NormedAddCommGroup
    (causalBoundedChain →L[ℂ] causalBoundedChain)).toUniformSpace.toTopologicalSpace
local instance causalPolynomialOrbitEndTopologicalRing : IsTopologicalRing (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  NonUnitalSeminormedRing.toIsTopologicalRing

local instance causalPolynomialOrbitEndNormedAlgebra : NormedAlgebra ℂ (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  ContinuousLinearMap.toNormedAlgebra
local instance causalPolynomialOrbitEndNormOne : NormOneClass (causalBoundedChain →L[ℂ] causalBoundedChain) := ⟨by
  have he := congrArg (fun A : causalBoundedChain →L[ℂ] causalBoundedChain => ‖A‖)
    causalBoundedChainExponential_zero
  exact he.symm.trans (norm_causalBoundedChainExponential_real (0 : ℝ≥0))⟩


open Polynomial

/-- Read each genuine spatial derivative in the original Hardy-complement Hilbert space. -/
def causalBoundedPolynomialEntireOrbit (p : ℂ[X]) (j : ℕ) (u : causalBoundedChain) (z : ℂ) : hardyL2ᗮ :=
  causalBoundedChainCoordinate j (causalBoundedPolynomialExponential p z u)

/-- The actual polynomial evolution solves the full spatial derivative hierarchy. -/
theorem causalBoundedPolynomialEntireOrbit_hasDerivAt (p : ℂ[X]) (j : ℕ)
    (u : causalBoundedChain) (z : ℂ) :
    HasDerivAt (causalBoundedPolynomialEntireOrbit p j u)
      (∑ k ∈ Finset.range (p.natDegree+1),
        p.coeff k • causalBoundedPolynomialEntireOrbit p (j+k) u z) z := by
  have h := (causalBoundedPolynomialExponential_hasDerivAt p z).clm_apply (hasDerivAt_const z u)
  have he : HasDerivAt (fun w : ℂ => causalBoundedPolynomialExponential p w u)
      (causalBoundedPolynomialOperator p (causalBoundedPolynomialExponential p z u)) z := by
    convert! h using 1
    simp only [map_zero, add_zero]
    rfl
  have hc := (causalBoundedChainCoordinate j).hasFDerivAt.comp_hasDerivAt z he
  have hd := causalBoundedPolynomialOperator_coordinate p j (causalBoundedPolynomialExponential p z u)
  have ht := congrArg (fun v : hardyL2ᗮ => HasDerivAt (causalBoundedPolynomialEntireOrbit p j u) v z) hd
  exact ht.mp hc

/-- Every genuine spatial derivative coordinate is entire in complex time. -/
theorem causalBoundedPolynomialEntireOrbit_analyticAt (p : ℂ[X]) (j : ℕ)
    (u : causalBoundedChain) (z : ℂ) : AnalyticAt ℂ (causalBoundedPolynomialEntireOrbit p j u) z :=
  (show Differentiable ℂ (causalBoundedPolynomialEntireOrbit p j u) from fun w =>
    (causalBoundedPolynomialEntireOrbit_hasDerivAt p j u w).differentiableAt).analyticAt z

/-- The polynomial flow starts at the actual derivative coordinates of its initial chain. -/
theorem causalBoundedPolynomialEntireOrbit_zero (p : ℂ[X]) (j : ℕ) (u : causalBoundedChain) :
    causalBoundedPolynomialEntireOrbit p j u 0 = causalBoundedChainCoordinate j u :=
  congrArg (fun A : causalBoundedChain →L[ℂ] causalBoundedChain => causalBoundedChainCoordinate j (A u))
    (causalBoundedPolynomialExponential_zero p)

/-- At every complex time, consecutive coordinates still form the actual causal derivative graph. -/
theorem causalBoundedPolynomialEntireOrbit_hasRightDeriv (p : ℂ[X]) (j : ℕ)
    (u : causalBoundedChain) (z : ℂ) :
    HasDerivWithinAt (causalForwardOrbit (causalBoundedPolynomialEntireOrbit p j u z))
      (causalBoundedPolynomialEntireOrbit p (j+1) u z) (Ioi 0) 0 :=
  causalBoundedChainCoordinate_hasRightDeriv j (causalBoundedPolynomialExponential p z u)

/-- Each original Hilbert coordinate inherits the genuine coefficient growth estimate. -/
theorem causalBoundedPolynomialEntireOrbit_norm_le (p : ℂ[X]) (j : ℕ)
    (u : causalBoundedChain) (z : ℂ) :
    ‖causalBoundedPolynomialEntireOrbit p j u z‖ ≤
      Real.exp (‖z‖*causalBoundedPolynomialSize p)*‖u‖ :=
  (causalBoundedChainCoordinate_norm_le j _).trans
    (((causalBoundedPolynomialExponential p z).le_opNorm u).trans
      (mul_le_mul_of_nonneg_right (norm_causalBoundedPolynomialExponential_le_coefficients p z) (norm_nonneg u)))

end
end RHTower.FokasLenells
