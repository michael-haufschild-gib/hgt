import GaloisForLFunctions.RHTower.FokasLenellsCausalBoundedHigherSpectrum
import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.Order.Interval.Set.Infinite

/-! Actual complex polynomial differential operators on genuine bounded Cauchy derivative chains. -/
open Complex MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance causalPolynomialLowerComplete : CompleteSpace (hardyL2ᗮ) := hardyL2.isClosed_orthogonal.completeSpace_coe
local instance causalPolynomialChainComplete : CompleteSpace causalBoundedChain := causalBoundedChain_complete
local instance causalPolynomialChainNormedGroup : NormedAddCommGroup causalBoundedChain := causalBoundedChain.normedAddCommGroup
local instance causalPolynomialChainNormedSpace : NormedSpace ℂ causalBoundedChain := causalBoundedChain.normedSpace
local instance causalPolynomialEndNormedRing : NormedRing (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  ContinuousLinearMap.toNormedRing
local instance causalPolynomialEndTopology : TopologicalSpace (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  (inferInstance : NormedAddCommGroup
    (causalBoundedChain →L[ℂ] causalBoundedChain)).toUniformSpace.toTopologicalSpace
local instance causalPolynomialEndTopologicalRing : IsTopologicalRing (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  NonUnitalSeminormedRing.toIsTopologicalRing

local instance causalPolynomialEndNormedAlgebra : NormedAlgebra ℂ (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  ContinuousLinearMap.toNormedAlgebra
local instance causalPolynomialEndNormOne : NormOneClass (causalBoundedChain →L[ℂ] causalBoundedChain) := ⟨by
  have he := congrArg (fun A : causalBoundedChain →L[ℂ] causalBoundedChain => ‖A‖)
    causalBoundedChainExponential_zero
  exact he.symm.trans (norm_causalBoundedChainExponential_real (0 : ℝ≥0))⟩


open Polynomial

/-- Evaluate a complex polynomial at the actual bounded derivative shift. -/
def causalBoundedPolynomialOperator (p : ℂ[X]) : causalBoundedChain →L[ℂ] causalBoundedChain :=
  Polynomial.aeval causalBoundedChainShift p

/-- Every polynomial operator is the literal finite combination of genuine derivative powers. -/
theorem causalBoundedPolynomialOperator_sum (p : ℂ[X]) :
    causalBoundedPolynomialOperator p =
      ∑ j ∈ Finset.range (p.natDegree+1), p.coeff j • causalBoundedChainShift^j :=
  Polynomial.aeval_eq_sum_range causalBoundedChainShift

private theorem actual_polynomial_apply_sum (p : ℂ[X]) (u : causalBoundedChain) :
    causalBoundedPolynomialOperator p u =
      ∑ k ∈ Finset.range (p.natDegree+1), p.coeff k • ((causalBoundedChainShift^k) u) := by
  have he := congrArg (fun A : causalBoundedChain →L[ℂ] causalBoundedChain => A u)
    (causalBoundedPolynomialOperator_sum p)
  have hs : ((∑ k ∈ Finset.range (p.natDegree+1), p.coeff k • causalBoundedChainShift^k) :
      causalBoundedChain →L[ℂ] causalBoundedChain) u =
      ∑ k ∈ Finset.range (p.natDegree+1), p.coeff k • ((causalBoundedChainShift^k) u) := by
    simp only [sum_apply, smul_apply]
  exact he.trans hs

/-- Polynomial evolution uses the actual higher derivative coordinates of the chain. -/
theorem causalBoundedPolynomialOperator_coordinate (p : ℂ[X]) (j : ℕ)
    (u : causalBoundedChain) :
    causalBoundedChainCoordinate j (causalBoundedPolynomialOperator p u) =
      ∑ k ∈ Finset.range (p.natDegree+1), p.coeff k • causalBoundedChainCoordinate (j+k) u := by
  have he := congrArg (fun v : causalBoundedChain => causalBoundedChainCoordinate j v)
    (actual_polynomial_apply_sum p u)
  have hs : causalBoundedChainCoordinate j
      (∑ k ∈ Finset.range (p.natDegree+1), p.coeff k • ((causalBoundedChainShift^k) u)) =
      ∑ k ∈ Finset.range (p.natDegree+1),
        p.coeff k • causalBoundedChainCoordinate j ((causalBoundedChainShift^k) u) := by
    simp only [map_sum, map_smul]
  have ht := Finset.sum_congr (s₁ := Finset.range (p.natDegree+1)) rfl (fun k _ =>
    congrArg (fun v : hardyL2ᗮ => p.coeff k • v)
      (causalBoundedChainShift_pow_coordinate k j u))
  exact he.trans (hs.trans ht)

/-- Every genuine disk chain remains a polynomial eigenchain with the evaluated symbol. -/
theorem causalBoundedPolynomialOperator_diskEigenchain (p : ℂ[X]) (q : causalBoundedDiskRate) :
    causalBoundedPolynomialOperator p (causalBoundedDiskEigenchain q) =
      p.eval (q : ℂ) • causalBoundedDiskEigenchain q := by
  have he := actual_polynomial_apply_sum p (causalBoundedDiskEigenchain q)
  have hs := Finset.sum_congr (s₁ := Finset.range (p.natDegree+1)) rfl (fun k _ =>
    (congrArg (fun v : causalBoundedChain => p.coeff k • v)
      (causalBoundedChainShift_pow_diskEigenchain k q)).trans
      (smul_smul (p.coeff k) ((q : ℂ)^k) (causalBoundedDiskEigenchain q)))
  have ht : (∑ k ∈ Finset.range (p.natDegree+1),
      (p.coeff k * (q : ℂ)^k) • causalBoundedDiskEigenchain q) =
      (∑ k ∈ Finset.range (p.natDegree+1), p.coeff k * (q : ℂ)^k) •
        causalBoundedDiskEigenchain q := Finset.sum_smul.symm
  have hp := congrArg (fun c : ℂ => c • causalBoundedDiskEigenchain q)
    (Polynomial.eval_eq_sum_range (p := p) (q : ℂ)).symm
  exact he.trans (hs.trans (ht.trans hp))

/-- The actual spectrum of any polynomial differential operator is the polynomial image of the left disk. -/
theorem causalBoundedPolynomialOperator_spectrum (p : ℂ[X]) :
    spectrum ℂ (causalBoundedPolynomialOperator p) =
      p.eval '' {z : ℂ | z.re ≤ 0 ∧ ‖z‖ ≤ 1} := by
  have hn : (spectrum ℂ causalBoundedChainShift).Nonempty :=
    ⟨-1, (causalBoundedChainShift_mem_spectrum_iff (-1)).mpr (by constructor <;> norm_num)⟩
  exact (spectrum.map_polynomial_aeval_of_nonempty causalBoundedChainShift p hn).trans
    (congrArg (fun s : Set ℂ => p.eval '' s) causalBoundedChainShift_spectrum)

/-- Distinct polynomial differential expressions give distinct actual operators on bounded chains. -/
theorem causalBoundedPolynomialOperator_injective : Function.Injective causalBoundedPolynomialOperator := by
  intro p q hpq
  apply Polynomial.eq_of_infinite_eval_eq
  have hI : (Complex.ofReal '' Set.Ioo (-1 : ℝ) 0).Infinite :=
    (Set.Ioo_infinite (show (-1 : ℝ) < 0 by norm_num)).image Complex.ofReal_injective.injOn
  apply hI.mono
  rintro z ⟨r, hr, rfl⟩
  let rate : causalBoundedDiskRate := ⟨(r : ℂ), by
    constructor
    · exact hr.2
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg hr.2]
      linarith [hr.1]⟩
  have he := congrArg (fun A : causalBoundedChain →L[ℂ] causalBoundedChain =>
    A (causalBoundedDiskEigenchain rate)) hpq
  have hm : p.eval (r : ℂ) • causalBoundedDiskEigenchain rate =
      q.eval (r : ℂ) • causalBoundedDiskEigenchain rate :=
    (causalBoundedPolynomialOperator_diskEigenchain p rate).symm.trans
      (he.trans (causalBoundedPolynomialOperator_diskEigenchain q rate))
  have hz : (p.eval (r : ℂ) - q.eval (r : ℂ)) • causalBoundedDiskEigenchain rate = 0 :=
    (sub_smul (p.eval (r : ℂ)) (q.eval (r : ℂ)) (causalBoundedDiskEigenchain rate)).trans
      ((congrArg (fun v : causalBoundedChain => v - q.eval (r : ℂ) •
        causalBoundedDiskEigenchain rate) hm).trans (sub_self _))
  exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right (causalBoundedDiskEigenchain_ne_zero rate))

/-- The actual bounded derivative shift satisfies no nonzero scalar polynomial identity. -/
theorem causalBoundedChainShift_transcendental : Transcendental ℂ causalBoundedChainShift :=
  transcendental_iff_injective.mpr causalBoundedPolynomialOperator_injective

end
end RHTower.FokasLenells
