import GaloisForLFunctions.RHTower.FokasLenellsCausalUnitBoundaryRates
import GaloisForLFunctions.RHTower.FokasLenellsCausalBoundedExponentialEstimate

/-! Genuine rational eigenchains on the unit sphere of the actual derivative-chain Banach space.
Their exact complex exponential action supplies sharp growth lower bounds. -/
open Complex MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance : CompleteSpace (hardyL2ᗮ) := hardyL2.isClosed_orthogonal.completeSpace_coe
local instance : CompleteSpace causalBoundedChain := causalBoundedChain_complete
local instance : NormedAddCommGroup causalBoundedChain := causalBoundedChain.normedAddCommGroup
local instance : NormedSpace ℂ causalBoundedChain := causalBoundedChain.normedSpace
local instance : NormedRing (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  ContinuousLinearMap.toNormedRing
local instance : TopologicalSpace (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  (inferInstance : NormedAddCommGroup
    (causalBoundedChain →L[ℂ] causalBoundedChain)).toUniformSpace.toTopologicalSpace
local instance : IsTopologicalRing (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  NonUnitalSeminormedRing.toIsTopologicalRing

private theorem unit_power_norm (b ω : ℝ) (j : ℕ) :
    ‖(causalUnitBoundaryRate b ω).val^j • (causalUnitBoundaryEigenvector b ω).val‖ = 1 := by
  rw [norm_smul, norm_pow, norm_causalUnitBoundaryRate, one_pow]
  change 1 * ‖causalUnitBoundaryEigenvector b ω‖ = 1
  rw [norm_causalUnitBoundaryEigenvector, mul_one]

private theorem unit_graph_pair (b ω : ℝ) (j : ℕ) :
    ((causalUnitBoundaryRate b ω).val^j • (causalUnitBoundaryEigenvector b ω).val,
      (causalUnitBoundaryRate b ω).val^(j+1) • (causalUnitBoundaryEigenvector b ω).val) ∈
      causalGeneratorGraph := by
  apply (causalGeneratorGraph_mem_iff _ _).2
  have h := causalGenerator_hasRightDeriv
    ((causalUnitBoundaryRate b ω).val^j • causalUnitBoundaryEigenvector b ω)
  rw [map_smul, causalGenerator_unitBoundaryEigenvector] at h
  change HasDerivWithinAt
    (causalForwardOrbit ((causalUnitBoundaryRate b ω).val^j • (causalUnitBoundaryEigenvector b ω).val))
    ((causalUnitBoundaryRate b ω).val^j •
      ((causalUnitBoundaryRate b ω).val • (causalUnitBoundaryEigenvector b ω).val)) (Ioi 0) 0 at h
  rw [smul_smul, ← pow_succ] at h
  exact h

/-- The actual normalized rational eigenvector and all its genuine derivatives form a unit chain. -/
def causalBoundedUnitEigenchain (b ω : ℝ) : causalBoundedChain :=
  ⟨⟨fun j => (causalUnitBoundaryRate b ω).val^j • (causalUnitBoundaryEigenvector b ω).val,
    memℓp_infty ⟨1, by rintro y ⟨j, rfl⟩; exact (unit_power_norm b ω j).le⟩⟩,
    (causalBoundedChain_mem_iff _).2 (unit_graph_pair b ω)⟩

/-- Every genuine derivative coordinate of this rational chain has norm one. -/
theorem causalBoundedUnitEigenchain_coordinate_norm (b ω : ℝ) (j : ℕ) :
    ‖causalBoundedChainCoordinate j (causalBoundedUnitEigenchain b ω)‖ = 1 := unit_power_norm b ω j

/-- The initial coordinate is the original normalized genuine rational datum. -/
theorem causalBoundedUnitEigenchain_zero (b ω : ℝ) :
    causalBoundedChainCoordinate 0 (causalBoundedUnitEigenchain b ω) =
      (causalUnitBoundaryEigenvector b ω).val := by
  change (causalUnitBoundaryRate b ω).val^0 • (causalUnitBoundaryEigenvector b ω).val = _
  rw [pow_zero, one_smul]

/-- These concrete genuine eigenchains lie on the unit sphere in the actual supremum norm. -/
theorem norm_causalBoundedUnitEigenchain (b ω : ℝ) : ‖causalBoundedUnitEigenchain b ω‖ = 1 := by
  apply le_antisymm
  · exact lp.norm_le_of_forall_le zero_le_one (fun j => (unit_power_norm b ω j).le)
  · exact (causalBoundedUnitEigenchain_coordinate_norm b ω 0).symm.trans_le
      (causalBoundedChainCoordinate_norm_le 0 _)

/-- The literal bounded derivative shift has the genuine unit-circle eigenvalue. -/
theorem causalBoundedChainShift_unitEigenchain (b ω : ℝ) :
    causalBoundedChainShift (causalBoundedUnitEigenchain b ω) =
      (causalUnitBoundaryRate b ω).val • causalBoundedUnitEigenchain b ω := by
  apply Subtype.ext
  apply lp.ext
  funext j
  change (causalUnitBoundaryRate b ω).val^(j+1) • (causalUnitBoundaryEigenvector b ω).val =
    (causalUnitBoundaryRate b ω).val •
      ((causalUnitBoundaryRate b ω).val^j • (causalUnitBoundaryEigenvector b ω).val)
  rw [pow_succ', mul_smul]

/-- Every actual derivative-shift power retains the exact genuine rational eigencharacter. -/
theorem causalBoundedChainShift_pow_unitEigenchain (b ω : ℝ) (k : ℕ) :
    (causalBoundedChainShift^k) (causalBoundedUnitEigenchain b ω) =
      (causalUnitBoundaryRate b ω).val^k • causalBoundedUnitEigenchain b ω := by
  induction k with
  | zero => simp only [pow_zero, one_smul]; rfl
  | succ k ih =>
    have hp : causalBoundedChainShift^(k+1) =
        causalBoundedChainShift * causalBoundedChainShift^k := pow_succ' _ _
    have he := congrArg (fun A : causalBoundedChain →L[ℂ] causalBoundedChain =>
      A (causalBoundedUnitEigenchain b ω)) hp
    have hi := congrArg (fun v : causalBoundedChain => causalBoundedChainShift v) ih
    have hs := causalBoundedChainShift.map_smul
      ((causalUnitBoundaryRate b ω).val^k) (causalBoundedUnitEigenchain b ω)
    have hu := congrArg (fun v : causalBoundedChain => (causalUnitBoundaryRate b ω).val^k • v)
      (causalBoundedChainShift_unitEigenchain b ω)
    have hm := smul_smul ((causalUnitBoundaryRate b ω).val^k)
      (causalUnitBoundaryRate b ω).val (causalBoundedUnitEigenchain b ω)
    have hn := congrArg (fun c : ℂ => c • causalBoundedUnitEigenchain b ω)
      (pow_succ (causalUnitBoundaryRate b ω).val k).symm
    exact he.trans (hi.trans (hs.trans (hu.trans (hm.trans hn))))

/-- The actual complex-time evolution acts on a genuine unit eigenchain by its scalar exponential. -/
theorem causalBoundedChainExponential_unitEigenchain (b ω : ℝ) (z : ℂ) :
    causalBoundedChainExponential z (causalBoundedUnitEigenchain b ω) =
      Complex.exp (z*(causalUnitBoundaryRate b ω).val) • causalBoundedUnitEigenchain b ω := by
  have hc : HasSum (fun k : ℕ => ((k.factorial : ℂ))⁻¹ *
      (z*(causalUnitBoundaryRate b ω).val)^k) (Complex.exp (z*(causalUnitBoundaryRate b ω).val)) := by
    simpa only [smul_eq_mul, Complex.exp_eq_exp_ℂ] using
      NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (z*(causalUnitBoundaryRate b ω).val)
  calc
    _ = ∑' k : ℕ, (((k.factorial : ℂ))⁻¹*z^k) •
        ((causalBoundedChainShift^k) (causalBoundedUnitEigenchain b ω)) :=
      causalBoundedChainExponential_series z _
    _ = ∑' k : ℕ, (((k.factorial : ℂ))⁻¹*(z*(causalUnitBoundaryRate b ω).val)^k) •
        causalBoundedUnitEigenchain b ω := by
      apply tsum_congr
      intro k
      have hp := congrArg (fun v : causalBoundedChain => (((k.factorial : ℂ))⁻¹*z^k) • v)
        (causalBoundedChainShift_pow_unitEigenchain b ω k)
      have hs := smul_smul (((k.factorial : ℂ))⁻¹*z^k)
        ((causalUnitBoundaryRate b ω).val^k) (causalBoundedUnitEigenchain b ω)
      have hc' : (((k.factorial : ℂ))⁻¹*z^k) * (causalUnitBoundaryRate b ω).val^k =
          ((k.factorial : ℂ))⁻¹*(z*(causalUnitBoundaryRate b ω).val)^k := by
        rw [mul_pow, mul_assoc]
      exact hp.trans (hs.trans (congrArg (fun c : ℂ => c • causalBoundedUnitEigenchain b ω) hc'))
    _ = _ := (hc.smul_const (causalBoundedUnitEigenchain b ω)).tsum_eq

/-- Each genuine unit rational chain measures the exact exponential of the real eigencharacter. -/
theorem norm_causalBoundedChainExponential_unitEigenchain (b ω : ℝ) (z : ℂ) :
    ‖causalBoundedChainExponential z (causalBoundedUnitEigenchain b ω)‖ =
      Real.exp ((z*(causalUnitBoundaryRate b ω).val).re) := by
  have he := congrArg (fun v : causalBoundedChain => ‖v‖)
    (causalBoundedChainExponential_unitEigenchain b ω z)
  have hs := norm_smul (Complex.exp (z*(causalUnitBoundaryRate b ω).val)) (causalBoundedUnitEigenchain b ω)
  have hn := congrArg (fun r : ℝ => ‖Complex.exp (z*(causalUnitBoundaryRate b ω).val)‖*r)
    (norm_causalBoundedUnitEigenchain b ω)
  exact he.trans (hs.trans (hn.trans ((mul_one _).trans (Complex.norm_exp _))))

/-- The actual rational unit chains give unconditional lower bounds on every complex-time operator. -/
theorem causalBoundedChainExponential_unit_lower (b ω : ℝ) (z : ℂ) :
    Real.exp ((z*(causalUnitBoundaryRate b ω).val).re) ≤ ‖causalBoundedChainExponential z‖ := by
  have hn := congrArg (fun r : ℝ => ‖causalBoundedChainExponential z‖*r)
    (norm_causalBoundedUnitEigenchain b ω)
  exact (norm_causalBoundedChainExponential_unitEigenchain b ω z).symm.trans_le
    (((causalBoundedChainExponential z).le_opNorm _).trans_eq (hn.trans (mul_one _)))

end
end RHTower.FokasLenells
