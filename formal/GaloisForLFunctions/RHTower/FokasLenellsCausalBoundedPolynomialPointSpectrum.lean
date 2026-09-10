import GaloisForLFunctions.RHTower.FokasLenellsCausalBoundedPolynomialOperator

/-! Actual complex polynomial differential operators on genuine bounded Cauchy derivative chains. -/
open Complex MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance causalPolynomialPointLowerComplete : CompleteSpace (hardyL2ᗮ) := hardyL2.isClosed_orthogonal.completeSpace_coe
local instance causalPolynomialPointChainComplete : CompleteSpace causalBoundedChain := causalBoundedChain_complete
local instance causalPolynomialPointChainNormedGroup : NormedAddCommGroup causalBoundedChain := causalBoundedChain.normedAddCommGroup
local instance causalPolynomialPointChainNormedSpace : NormedSpace ℂ causalBoundedChain := causalBoundedChain.normedSpace
local instance causalPolynomialPointEndNormedRing : NormedRing (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  ContinuousLinearMap.toNormedRing
local instance causalPolynomialPointEndTopology : TopologicalSpace (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  (inferInstance : NormedAddCommGroup
    (causalBoundedChain →L[ℂ] causalBoundedChain)).toUniformSpace.toTopologicalSpace
local instance causalPolynomialPointEndTopologicalRing : IsTopologicalRing (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  NonUnitalSeminormedRing.toIsTopologicalRing

local instance causalPolynomialPointEndNormedAlgebra : NormedAlgebra ℂ (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  ContinuousLinearMap.toNormedAlgebra
local instance causalPolynomialPointEndNormOne : NormOneClass (causalBoundedChain →L[ℂ] causalBoundedChain) := ⟨by
  have he := congrArg (fun A : causalBoundedChain →L[ℂ] causalBoundedChain => ‖A‖)
    causalBoundedChainExponential_zero
  exact he.symm.trans (norm_causalBoundedChainExponential_real (0 : ℝ≥0))⟩


open Polynomial

/-- The eigenvalues of the actual polynomial derivative operator on genuine bounded chains. -/
def causalBoundedPolynomialPointSpectrum (p : ℂ[X]) : Set ℂ :=
  {z | ∃ u : causalBoundedChain, u ≠ 0 ∧ causalBoundedPolynomialOperator p u = z • u}

private theorem actual_root_factor (s : Multiset ℂ) (u : causalBoundedChain) (hu : u ≠ 0)
    (hz : causalBoundedPolynomialOperator ((s.map (fun r => X - C r)).prod) u = 0) :
    ∃ r : ℂ, r ∈ s ∧ r ∈ causalBoundedChainPointSpectrum := by
  classical
  induction s using Multiset.induction_on generalizing u with
  | empty =>
      have h : u = 0 := by simpa [causalBoundedPolynomialOperator] using hz
      exact (hu h).elim
  | cons r s ih =>
      let v := causalBoundedPolynomialOperator ((s.map (fun r => X - C r)).prod) u
      simp only [Multiset.map_cons, Multiset.prod_cons, causalBoundedPolynomialOperator,
        map_mul, map_sub, Polynomial.aeval_X, Polynomial.aeval_C] at hz
      change causalBoundedChainShift v - r • v = 0 at hz
      by_cases hv : v = 0
      · obtain ⟨a, ha, he⟩ := ih u hu hv
        exact ⟨a, by simp [ha], he⟩
      · exact ⟨r, by simp, v, hv, sub_eq_zero.mp hz⟩

/-- Polynomial combinations have exactly the polynomial images of the genuine derivative eigenvalues. -/
theorem causalBoundedPolynomialPointSpectrum_eq (p : ℂ[X]) :
    causalBoundedPolynomialPointSpectrum p = p.eval '' {z : ℂ | z.re < 0 ∧ ‖z‖ ≤ 1} := by
  classical
  ext z
  constructor
  · rintro ⟨u, hu, hzu⟩
    let q : ℂ[X] := p - C z
    by_cases hq : q = 0
    · have hp : p = C z := sub_eq_zero.mp hq
      refine ⟨-1, ?_, ?_⟩
      · constructor <;> norm_num
      · simp [hp]
    · have hqz : causalBoundedPolynomialOperator q u = 0 := by
        simp only [q, causalBoundedPolynomialOperator, map_sub, Polynomial.aeval_C]
        change causalBoundedPolynomialOperator p u - z • u = 0
        rw [hzu, sub_self]
      have hfac := congrArg (fun r : ℂ[X] => causalBoundedPolynomialOperator r u)
        (IsAlgClosed.splits q).eq_prod_roots
      have hscalar : q.leadingCoeff •
          causalBoundedPolynomialOperator ((q.roots.map (fun r => X - C r)).prod) u = 0 := by
        have h := hfac.symm.trans hqz
        simp only [causalBoundedPolynomialOperator, map_mul, Polynomial.aeval_C] at h
        exact h
      have hprod := (smul_eq_zero.mp hscalar).resolve_left
        (Polynomial.leadingCoeff_ne_zero.mpr hq)
      obtain ⟨r, hr, he⟩ := actual_root_factor q.roots u hu hprod
      have hroot := (Polynomial.mem_roots hq).mp hr
      change q.eval r = 0 at hroot
      change (p - C z).eval r = 0 at hroot
      rw [Polynomial.eval_sub, Polynomial.eval_C] at hroot
      exact ⟨r, (causalBoundedChainShift_mem_pointSpectrum_iff r).mp he, sub_eq_zero.mp hroot⟩
  · rintro ⟨r, hr, rfl⟩
    exact ⟨causalBoundedDiskEigenchain ⟨r, hr⟩, causalBoundedDiskEigenchain_ne_zero ⟨r, hr⟩,
      causalBoundedPolynomialOperator_diskEigenchain p ⟨r, hr⟩⟩

/-- Every actual polynomial eigenvalue is realized by one of the normalized rational disk chains. -/
theorem causalBoundedPolynomialPointSpectrum_has_unit_eigenchain (p : ℂ[X]) :
    causalBoundedPolynomialPointSpectrum p =
      {z | ∃ q : causalBoundedDiskRate,
        ‖causalBoundedDiskEigenchain q‖ = 1 ∧
        causalBoundedPolynomialOperator p (causalBoundedDiskEigenchain q) =
          z • causalBoundedDiskEigenchain q} := by
  ext z
  constructor
  · intro hz
    obtain ⟨r, hr, hpr⟩ := (Set.ext_iff.mp (causalBoundedPolynomialPointSpectrum_eq p) z).mp hz
    refine ⟨⟨r, hr⟩, norm_causalBoundedDiskEigenchain ⟨r, hr⟩, ?_⟩
    exact (causalBoundedPolynomialOperator_diskEigenchain p ⟨r, hr⟩).trans
      (congrArg (fun c : ℂ => c • causalBoundedDiskEigenchain ⟨r, hr⟩) hpr)
  · rintro ⟨q, _hnorm, he⟩
    exact ⟨causalBoundedDiskEigenchain q, causalBoundedDiskEigenchain_ne_zero q, he⟩

end
end RHTower.FokasLenells
