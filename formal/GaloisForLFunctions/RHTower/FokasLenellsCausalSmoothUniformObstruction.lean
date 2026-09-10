import GaloisForLFunctions.RHTower.FokasLenellsCausalSmoothBoundaryChains

/-! The corpus's finite-seminorm Banach--Steinhaus bound applied to genuine infinite
causal-generator chains. Uniformly bounded rational chains force a slow smooth input. -/
open Complex MeasureTheory Set Filter Topology
open scoped NNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section
local instance : InnerProductSpace ℝ (hardyL2ᗮ) := InnerProductSpace.rclikeToReal ℂ (hardyL2ᗮ)
local instance : IsUniformAddGroup causalSmoothGraph := causalSmoothGraph_uniformAddGroup
local instance : BarrelledSpace ℝ causalSmoothGraph := causalSmoothGraph_barrelled
local instance : ContinuousSMul ℝ causalSmoothGraph := withSeminorms_causalSmoothGraph.continuousSMul

/-- Real continuous orbit readouts indexed by integer time and an actual Hilbert unit vector. -/
def causalSmoothOrbitReadout (p : ℕ × {v : hardyL2ᗮ // ‖v‖ = 1}) : causalSmoothGraph →L[ℝ] ℝ :=
  ((p.1 : ℝ)+1) • ((innerSL ℝ p.2.val).comp
    (((causalLowerCauchyEvolution (p.1 : ℝ≥0)).restrictScalars ℝ).comp
      ((causalSmoothGraphCoordinate 0).restrictScalars ℝ)))

/-- Cauchy--Schwarz bounds every actual scalar readout by the corresponding weighted orbit norm. -/
theorem causalSmoothOrbitReadout_norm_le (p : ℕ × {v : hardyL2ᗮ // ‖v‖ = 1})
    (u : causalSmoothGraph) :
    ‖causalSmoothOrbitReadout p u‖ ≤ ((p.1 : ℝ)+1)*
      ‖causalLowerCauchyEvolution (p.1 : ℝ≥0) (causalSmoothGraphCoordinate 0 u)‖ := by
  change ‖((p.1 : ℝ)+1)*inner ℝ p.2.val
    (causalLowerCauchyEvolution (p.1 : ℝ≥0) (causalSmoothGraphCoordinate 0 u))‖ ≤ _
  rw [norm_mul, Real.norm_of_nonneg (by positivity)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (norm_inner_le_norm _ _).trans_eq (by rw [p.2.property, one_mul])

/-- Pairing a genuine zero-frequency boundary chain with its initial unit vector is exact. -/
theorem causalSmoothOrbitReadout_boundary (n : ℕ) (b : ℝ) :
    causalSmoothOrbitReadout
      (n, ⟨(causalBoundaryEigenvector b 0).val, norm_causalBoundaryEigenvector b 0⟩)
      (causalSmoothBoundaryChain b) = ((n : ℝ)+1)*Real.exp (-(n : ℝ)*Real.exp b) := by
  change ((n : ℝ)+1)*inner ℝ (causalBoundaryEigenvector b 0).val
    (causalLowerCauchyEvolution (n : ℝ≥0)
      (causalSmoothGraphCoordinate 0 (causalSmoothBoundaryChain b))) = _
  rw [causalSmoothBoundaryChain_orbit]
  change ((n : ℝ)+1)*inner ℝ (causalBoundaryEigenvector b 0).val
    (Real.exp (-(n : ℝ)*Real.exp b) • (causalBoundaryEigenvector b 0).val) = _
  have hi : inner ℝ (causalBoundaryEigenvector b 0).val
      (Real.exp (-(n : ℝ)*Real.exp b) • (causalBoundaryEigenvector b 0).val) =
      Real.exp (-(n : ℝ)*Real.exp b)*inner ℝ
        (causalBoundaryEigenvector b 0).val (causalBoundaryEigenvector b 0).val := by
    exact real_inner_smul_right _ _ _
  have hn : inner ℝ (causalBoundaryEigenvector b 0).val (causalBoundaryEigenvector b 0).val =
      ‖(causalBoundaryEigenvector b 0).val‖^2 := real_inner_self_eq_norm_sq _
  rw [hi, hn]
  change ((n : ℝ)+1)*(Real.exp (-(n : ℝ)*Real.exp b)*‖causalBoundaryEigenvector b 0‖^2) = _
  rw [norm_causalBoundaryEigenvector, one_pow, mul_one]

private theorem boundary_finite_seminorm_le (s : Finset (Σ _j : ℕ, Fin 1))
    (b : ℝ) (hb : b ≤ 0) : (s.sup causalSmoothGraphSeminorm) (causalSmoothBoundaryChain b) ≤ 1 := by
  apply Seminorm.finset_sup_apply_le zero_le_one
  intro i _
  rw [causalSmoothGraphSeminorm_boundaryChain]
  exact pow_le_one₀ (Real.exp_nonneg _) (Real.exp_le_one_iff.mpr hb)

/-- No finite collection of actual derivative seminorms bounds all weighted orbit readouts. -/
theorem causalSmoothOrbitReadout_no_finite_bound :
    ¬ ∃ (s : Finset (Σ _j : ℕ, Fin 1)) (C : ℝ≥0),
      ∀ (p : ℕ × {v : hardyL2ᗮ // ‖v‖ = 1}) (u : causalSmoothGraph),
        ‖causalSmoothOrbitReadout p u‖ ≤ C*(s.sup causalSmoothGraphSeminorm) u := by
  rintro ⟨s, C, hC⟩
  have hn (n : ℕ) : (n : ℝ)+1 ≤ (C : ℝ) := by
    have hb (b : ℝ) (hb : b ≤ 0) :
        ((n : ℝ)+1)*Real.exp (-(n : ℝ)*Real.exp b) ≤ (C : ℝ) := by
      have h := hC (n, ⟨(causalBoundaryEigenvector b 0).val,
        norm_causalBoundaryEigenvector b 0⟩) (causalSmoothBoundaryChain b)
      rw [causalSmoothOrbitReadout_boundary, Real.norm_of_nonneg (by positivity)] at h
      exact h.trans ((mul_le_mul_of_nonneg_left (boundary_finite_seminorm_le s b hb)
        C.property).trans_eq (mul_one _))
    have harg : Tendsto (fun b : ℝ => -(n : ℝ)*Real.exp b) atBot (𝓝 0) := by
      simpa only [mul_zero] using tendsto_const_nhds.mul Real.tendsto_exp_atBot
    have hc : Tendsto (fun _b : ℝ => (n : ℝ)+1) atBot (𝓝 ((n : ℝ)+1)) := tendsto_const_nhds
    have ht := hc.mul ((Real.continuous_exp.tendsto (0 : ℝ)).comp harg)
    have he : ∀ᶠ b : ℝ in atBot, ((n : ℝ)+1)*Real.exp (-(n : ℝ)*Real.exp b) ≤ (C : ℝ) :=
      (eventually_le_atBot (0 : ℝ)).mono (fun b hb0 => hb b hb0)
    simpa only [Real.exp_zero, mul_one] using le_of_tendsto ht he
  obtain ⟨n, h⟩ := exists_nat_gt (C : ℝ)
  have h' := hn n
  linarith only [h, h']

/-- One genuine infinite derivative chain has unbounded time-weighted initial orbit norms. -/
theorem causalSmoothGraph_exists_unbounded_orbit :
    ∃ u : causalSmoothGraph, ¬ BddAbove (Set.range (fun n : ℕ => ((n : ℝ)+1)*
      ‖causalLowerCauchyEvolution (n : ℝ≥0) (causalSmoothGraphCoordinate 0 u)‖)) := by
  by_contra h
  have hp : ∀ u : causalSmoothGraph, BddAbove (Set.range
      (fun p : ℕ × {v : hardyL2ᗮ // ‖v‖ = 1} => ‖causalSmoothOrbitReadout p u‖)) := by
    intro u
    have hu : BddAbove (Set.range (fun n : ℕ => ((n : ℝ)+1)*
        ‖causalLowerCauchyEvolution (n : ℝ≥0) (causalSmoothGraphCoordinate 0 u)‖)) := by
      by_contra hn
      exact h ⟨u, hn⟩
    obtain ⟨B, hB⟩ := hu
    refine ⟨B, ?_⟩
    rintro y ⟨p, rfl⟩
    exact (causalSmoothOrbitReadout_norm_le p u).trans (hB ⟨p.1, rfl⟩)
  exact causalSmoothOrbitReadout_no_finite_bound
    (exists_seminorm_bound_of_bddAbove withSeminorms_causalSmoothGraph causalSmoothOrbitReadout hp)

end
end RHTower.FokasLenells
