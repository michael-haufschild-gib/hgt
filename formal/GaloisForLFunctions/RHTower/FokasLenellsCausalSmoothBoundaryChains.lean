import GaloisForLFunctions.RHTower.FokasLenellsCausalSmoothGraphTopology

/-! Actual rational boundary eigenvectors lift to genuine infinite derivative chains.
At small damping all finite collections of derivative seminorms remain bounded. -/
open Complex MeasureTheory Set Filter Topology
open scoped NNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

/-- The actual zero-frequency boundary eigenvector together with all of its genuine derivatives. -/
def causalSmoothBoundaryChain (b : ℝ) : causalSmoothGraph :=
  ⟨fun j : ℕ => ((causalBoundaryRate b 0).val)^j • (causalBoundaryEigenvector b 0).val, by
    apply (causalSmoothGraph_mem_iff _).2
    intro j
    apply (causalGeneratorGraph_mem_iff _ _).2
    have h := causalGenerator_hasRightDeriv
      (((causalBoundaryRate b 0).val)^j • causalBoundaryEigenvector b 0)
    rw [map_smul, causalGenerator_boundaryEigenvector] at h
    change HasDerivWithinAt
      (causalForwardOrbit (((causalBoundaryRate b 0).val)^j • (causalBoundaryEigenvector b 0).val))
      (((causalBoundaryRate b 0).val)^j •
        ((causalBoundaryRate b 0).val • (causalBoundaryEigenvector b 0).val)) (Ioi 0) 0 at h
    rw [smul_smul, ← pow_succ] at h
    exact h⟩

/-- Coordinate zero of the genuine boundary chain is the actual normalized rational datum. -/
theorem causalSmoothBoundaryChain_zero (b : ℝ) :
    causalSmoothGraphCoordinate 0 (causalSmoothBoundaryChain b) = (causalBoundaryEigenvector b 0).val := by
  change ((causalBoundaryRate b 0).val)^0 • (causalBoundaryEigenvector b 0).val =
    (causalBoundaryEigenvector b 0).val
  rw [pow_zero, one_smul]

/-- Every derivative coordinate of the actual rational chain has its exact damping power norm. -/
theorem norm_causalSmoothBoundaryChain_coordinate (b : ℝ) (j : ℕ) :
    ‖causalSmoothGraphCoordinate j (causalSmoothBoundaryChain b)‖ = (Real.exp b)^j := by
  change ‖((causalBoundaryRate b 0).val)^j • (causalBoundaryEigenvector b 0).val‖ = _
  rw [norm_smul, norm_pow]
  have hr : (causalBoundaryRate b 0).val = -(Real.exp b : ℂ) := by
    simp [causalBoundaryRate]
  rw [hr, norm_neg, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg b)]
  change _ * ‖causalBoundaryEigenvector b 0‖ = _
  rw [norm_causalBoundaryEigenvector, mul_one]

/-- The product seminorms evaluate to the exact actual derivative damping powers. -/
theorem causalSmoothGraphSeminorm_boundaryChain (b : ℝ) (i : Σ _j : ℕ, Fin 1) :
    causalSmoothGraphSeminorm i (causalSmoothBoundaryChain b) = (Real.exp b)^i.1 := by
  rw [causalSmoothGraphSeminorm_apply, norm_causalSmoothBoundaryChain_coordinate]

/-- A strictly negative damping parameter keeps every actual derivative seminorm bounded by one. -/
theorem causalSmoothGraphSeminorm_boundaryChain_negative (a : ℝ) (i : Σ _j : ℕ, Fin 1) :
    causalSmoothGraphSeminorm i (causalSmoothBoundaryChain (-Real.exp a)) ≤ 1 := by
  rw [causalSmoothGraphSeminorm_boundaryChain]
  exact pow_le_one₀ (Real.exp_nonneg _) (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.exp_nonneg _)))

/-- The literal initial coordinate has the exact scalar real decaying orbit. -/
theorem causalSmoothBoundaryChain_orbit (b : ℝ) (t : ℝ≥0) :
    causalLowerCauchyEvolution t (causalSmoothGraphCoordinate 0 (causalSmoothBoundaryChain b)) =
      Real.exp (-(t : ℝ)*Real.exp b) • (causalBoundaryEigenvector b 0).val := by
  rw [causalSmoothBoundaryChain_zero, causalLowerCauchyEvolution_boundaryEigenvector]
  have he : (((t : ℝ) : ℂ)*(causalBoundaryRate b 0).val) =
      ((-(t : ℝ)*Real.exp b : ℝ) : ℂ) := by
    simp [causalBoundaryRate]
  rw [he, ← Complex.ofReal_exp]
  exact (algebraMap_smul ℂ (Real.exp (-(t : ℝ)*Real.exp b))
    (causalBoundaryEigenvector b 0).val)

end
end RHTower.FokasLenells
