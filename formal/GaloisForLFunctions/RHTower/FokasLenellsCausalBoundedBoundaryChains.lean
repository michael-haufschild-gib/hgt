import GaloisForLFunctions.RHTower.FokasLenellsCausalBoundedChain

/-! Actual rational generator chains in the unit sphere of the bounded-chain Banach space. -/
open Complex MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

private theorem boundary_coordinate_le (b : {b : ℝ // b ≤ 0}) (j : ℕ) :
    ‖causalSmoothGraphCoordinate j (causalSmoothBoundaryChain b.val)‖ ≤ 1 := by
  rw [norm_causalSmoothBoundaryChain_coordinate]
  exact pow_le_one₀ (Real.exp_nonneg _) (Real.exp_le_one_iff.mpr b.property)

/-- The normalized rational boundary eigenvector and all its genuine derivatives form a bounded chain. -/
def causalBoundedBoundaryChain (b : {b : ℝ // b ≤ 0}) : causalBoundedChain :=
  ⟨⟨fun j => causalSmoothGraphCoordinate j (causalSmoothBoundaryChain b.val),
    memℓp_infty ⟨1, by rintro y ⟨j, rfl⟩; exact boundary_coordinate_le b j⟩⟩,
    (causalBoundedChain_mem_iff _).2
      ((causalSmoothGraph_mem_iff _).1 (causalSmoothBoundaryChain b.val).property)⟩

/-- The bounded rational chain has exactly the same genuine derivatives as its smooth-chain realization. -/
theorem causalBoundedBoundaryChain_coordinate (b : {b : ℝ // b ≤ 0}) (j : ℕ) :
    causalBoundedChainCoordinate j (causalBoundedBoundaryChain b) =
      causalSmoothGraphCoordinate j (causalSmoothBoundaryChain b.val) := rfl

/-- Its initial datum is the actual normalized rational Cauchy eigenvector. -/
theorem causalBoundedBoundaryChain_zero (b : {b : ℝ // b ≤ 0}) :
    causalBoundedChainCoordinate 0 (causalBoundedBoundaryChain b) =
      (causalBoundaryEigenvector b.val 0).val := causalSmoothBoundaryChain_zero b.val

/-- All of these genuine rational derivative chains lie on the unit sphere in the stronger norm. -/
theorem norm_causalBoundedBoundaryChain (b : {b : ℝ // b ≤ 0}) :
    ‖causalBoundedBoundaryChain b‖ = 1 := by
  apply le_antisymm
  · exact lp.norm_le_of_forall_le zero_le_one (boundary_coordinate_le b)
  · have h := causalBoundedChainCoordinate_norm_le 0 (causalBoundedBoundaryChain b)
    rw [causalBoundedBoundaryChain_zero] at h
    change ‖causalBoundaryEigenvector b.val 0‖ ≤ _ at h
    rwa [norm_causalBoundaryEigenvector] at h

/-- The actual rational initial orbit retains the exact slow exponential rate. -/
theorem causalBoundedBoundaryChain_orbit (b : {b : ℝ // b ≤ 0}) (t : ℝ≥0) :
    causalLowerCauchyEvolution t (causalBoundedChainCoordinate 0 (causalBoundedBoundaryChain b)) =
      Real.exp (-(t : ℝ)*Real.exp b.val) • (causalBoundaryEigenvector b.val 0).val :=
  causalSmoothBoundaryChain_orbit b.val t

/-- The actual forward orbit readout on the stronger bounded-chain space. -/
def causalBoundedChainOrbit (t : ℝ≥0) : causalBoundedChain →L[ℂ] hardyL2ᗮ :=
  (causalLowerCauchyEvolution t).comp (causalBoundedChainCoordinate 0)

/-- Actual evolution remains contractive from the bounded-chain norm to the original data norm. -/
theorem causalBoundedChainOrbit_norm_le (t : ℝ≥0) (u : causalBoundedChain) :
    ‖causalBoundedChainOrbit t u‖ ≤ ‖u‖ :=
  (causalLowerCauchyEvolution_norm_le t _).trans (causalBoundedChainCoordinate_norm_le 0 u)

/-- The stronger bounded-all-derivatives norm gives no uniform decay at any finite time. -/
theorem norm_causalBoundedChainOrbit (t : ℝ≥0) : ‖causalBoundedChainOrbit t‖ = 1 := by
  apply le_antisymm
  · exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      (fun u => by simpa only [one_mul] using causalBoundedChainOrbit_norm_le t u)
  · have hb : ∀ b : {b : ℝ // b ≤ 0}, Real.exp (-(t : ℝ)*Real.exp b.val) ≤
        ‖causalBoundedChainOrbit t‖ := by
      intro b
      have hn : ‖causalBoundedChainOrbit t‖ * ‖causalBoundedBoundaryChain b‖ =
          ‖causalBoundedChainOrbit t‖ :=
        (congrArg (fun r : ℝ => ‖causalBoundedChainOrbit t‖ * r)
          (norm_causalBoundedBoundaryChain b)).trans (mul_one _)
      have hv : ‖causalBoundedChainOrbit t (causalBoundedBoundaryChain b)‖ =
          Real.exp (-(t : ℝ)*Real.exp b.val) := by
        change ‖causalLowerCauchyEvolution t
          (causalBoundedChainCoordinate 0 (causalBoundedBoundaryChain b))‖ = _
        rw [causalBoundedBoundaryChain_zero]
        exact norm_causalLowerCauchyEvolution_boundaryEigenvector t b.val 0
      exact hv.symm.trans_le (((causalBoundedChainOrbit t).le_opNorm
        (causalBoundedBoundaryChain b)).trans_eq hn)
    have ht : Tendsto (fun b : ℝ => Real.exp (-(t : ℝ)*Real.exp b)) atBot (𝓝 1) := by
      have ha : Tendsto (fun b : ℝ => -(t : ℝ)*Real.exp b) atBot (𝓝 0) := by
        simpa only [mul_zero] using
          (tendsto_const_nhds (x := -(t : ℝ))).mul Real.tendsto_exp_atBot
      have he : Tendsto (fun b : ℝ => Real.exp (-(t : ℝ)*Real.exp b))
          atBot (𝓝 (Real.exp 0)) := (Real.continuous_exp.tendsto 0).comp ha
      simpa only [Real.exp_zero] using he
    exact le_of_tendsto ht ((eventually_le_atBot (0 : ℝ)).mono (fun b h => hb ⟨b, h⟩))

end
end RHTower.FokasLenells
