import GaloisForLFunctions.RHTower.FokasLenellsCausalStrongStability
import GaloisForLFunctions.RHTower.FokasLenellsCausalBoundaryEigenvectors
import GaloisForLFunctions.RHTower.SuzukiCausalDepthGammaWeakRobinTraceNoGo

/-! The actual causal evolution has one fixed input with no exponential decay rate.
Banach--Steinhaus is applied to the concrete, norm-unbounded family `(n+1) T_n`. -/
open Complex MeasureTheory Set Filter Topology
open scoped NNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

local instance : CompleteSpace (hardyL2ᗮ) := hardyL2.isClosed_orthogonal.completeSpace_coe

/-- Integer-time causal evolution weighted by the actual elapsed time plus one. -/
def causalWeightedEvolution (n : ℕ) : (hardyL2ᗮ) →L[ℂ] (hardyL2ᗮ) :=
  (((n : ℝ)+1 : ℝ) : ℂ) • causalLowerCauchyEvolution (n : ℝ≥0)

/-- The polynomially weighted actual evolution has an exactly growing operator norm. -/
theorem norm_causalWeightedEvolution (n : ℕ) :
    ‖causalWeightedEvolution n‖ = (n : ℝ)+1 := by
  have hf : ‖(((n : ℝ)+1 : ℝ) : ℂ)‖ = (n : ℝ)+1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  apply le_antisymm
  · exact (ContinuousLinearMap.opNorm_smul_le _ _).trans_eq
      (by rw [hf, norm_causalLowerCauchyEvolution, mul_one])
  · let v : hardyL2ᗮ := (causalBoundaryEigenvector 0 0).val
    have hv : ‖v‖ = 1 := norm_causalBoundaryEigenvector 0 0
    let w := causalLowerRecovery (n : ℝ≥0) v
    have hw : ‖w‖ = 1 := ((causalLowerRecovery (n : ℝ≥0)).norm_map v).trans hv
    have he : causalWeightedEvolution n w = (((n : ℝ)+1 : ℝ) : ℂ) • v := by
      change (((n : ℝ)+1 : ℝ) : ℂ) •
        causalLowerCauchyEvolution (n : ℝ≥0) (causalLowerRecovery (n : ℝ≥0) v) = _
      have h := congrArg (fun T : hardyL2ᗮ →L[ℂ] hardyL2ᗮ => T v)
        (causalLowerCauchyEvolution_comp_adjoint (n : ℝ≥0))
      rw [causalLowerCauchyEvolution_adjoint] at h
      change causalLowerCauchyEvolution (n : ℝ≥0) (causalLowerRecovery (n : ℝ≥0) v) = v at h
      rw [h]
    have h := (causalWeightedEvolution n).le_opNorm w
    rw [he, norm_smul, hf, hv, hw, mul_one, mul_one] at h
    exact h

/-- A single actual input has unbounded time-weighted orbit norms. -/
theorem causalWeightedEvolution_exists_unbounded_input :
    ∃ u : hardyL2ᗮ, ¬ BddAbove (Set.range
      (fun n : ℕ => ((n : ℝ)+1)*‖causalLowerCauchyEvolution (n : ℝ≥0) u‖)) := by
  by_contra h
  have hb : ∀ u : hardyL2ᗮ, BddAbove (Set.range (fun n : ℕ => ‖causalWeightedEvolution n u‖)) := by
    intro u
    have hu : BddAbove (Set.range
        (fun n : ℕ => ((n : ℝ)+1)*‖causalLowerCauchyEvolution (n : ℝ≥0) u‖)) := by
      by_contra hn
      exact h ⟨u, hn⟩
    have he : (fun n : ℕ => ‖causalWeightedEvolution n u‖) =
        (fun n : ℕ => ((n : ℝ)+1)*‖causalLowerCauchyEvolution (n : ℝ≥0) u‖) := by
      funext n
      change ‖(((n : ℝ)+1 : ℝ) : ℂ) • causalLowerCauchyEvolution (n : ℝ≥0) u‖ = _
      rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    rwa [he]
  obtain ⟨C, _, hC⟩ := RHTower.exists_uniform_opNorm_bound_of_pointwiseBounded
    causalWeightedEvolution hb
  obtain ⟨n, hn⟩ := exists_nat_gt C
  have hc := hC n
  rw [norm_causalWeightedEvolution] at hc
  linarith only [hn, hc]

/-- A fixed actual causal input chosen from the proved unbounded-orbit conclusion. -/
def causalSlowDecayVector : hardyL2ᗮ := Classical.choose causalWeightedEvolution_exists_unbounded_input

/-- This one fixed vector has unbounded polynomially weighted orbit norms. -/
theorem causalSlowDecayVector_unbounded :
    ¬ BddAbove (Set.range
      (fun n : ℕ => ((n : ℝ)+1)*‖causalLowerCauchyEvolution (n : ℝ≥0) causalSlowDecayVector‖)) :=
  Classical.choose_spec causalWeightedEvolution_exists_unbounded_input

/-- The fixed slow vector is nonzero. -/
theorem causalSlowDecayVector_ne_zero : causalSlowDecayVector ≠ 0 := by
  intro h
  apply causalSlowDecayVector_unbounded
  refine ⟨0, ?_⟩
  rintro y ⟨n, rfl⟩
  simp [h]

/-- The same fixed vector nevertheless decays strongly under the actual continuous-time evolution. -/
theorem causalSlowDecayVector_tendsto :
    Tendsto (fun t : ℝ≥0 => causalLowerCauchyEvolution t causalSlowDecayVector) atTop (𝓝 0) :=
  causalLowerCauchyEvolution_strong_tendsto causalSlowDecayVector

private theorem time_weight_exp_bound (a : ℝ) (n : ℕ) :
    ((n : ℝ)+1)*Real.exp (-(Real.exp a*(n : ℝ))) ≤ 1+(Real.exp a)⁻¹ := by
  have hn := Real.le_inv_mul_exp (n : ℝ) (Real.exp_pos a)
  have he : 1 ≤ Real.exp (Real.exp a*(n : ℝ)) := Real.one_le_exp (by positivity)
  have hb : (n : ℝ)+1 ≤ (1+(Real.exp a)⁻¹)*Real.exp (Real.exp a*(n : ℝ)) := by
    nlinarith only [hn, he]
  calc
    _ ≤ ((1+(Real.exp a)⁻¹)*Real.exp (Real.exp a*(n : ℝ)))*
        Real.exp (-(Real.exp a*(n : ℝ))) :=
      mul_le_mul_of_nonneg_right hb (Real.exp_nonneg _)
    _ = _ := by rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

/-- No positive exponential rate, with any real prefactor, bounds the orbit of this single vector. -/
theorem causalSlowDecayVector_no_exponential_bound (a B : ℝ) :
    ∃ n : ℕ, B*Real.exp (-(Real.exp a*(n : ℝ))) <
      ‖causalLowerCauchyEvolution (n : ℝ≥0) causalSlowDecayVector‖ := by
  by_contra h
  push Not at h
  apply causalSlowDecayVector_unbounded
  refine ⟨|B| *(1+(Real.exp a)⁻¹), ?_⟩
  rintro y ⟨n, rfl⟩
  have hn : ‖causalLowerCauchyEvolution (n : ℝ≥0) causalSlowDecayVector‖ ≤
      |B| *Real.exp (-(Real.exp a*(n : ℝ))) :=
    (h n).trans (mul_le_mul_of_nonneg_right (le_abs_self B) (Real.exp_nonneg _))
  calc
    _ ≤ ((n : ℝ)+1)*(|B| *Real.exp (-(Real.exp a*(n : ℝ)))) :=
      mul_le_mul_of_nonneg_left hn (by positivity)
    _ = |B| *(((n : ℝ)+1)*Real.exp (-(Real.exp a*(n : ℝ)))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (time_weight_exp_bound a n) (abs_nonneg B)

/-- The same fixed vector has arbitrarily large weighted orbit norms after every starting time. -/
theorem causalSlowDecayVector_weighted_late (B : ℝ) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ B < ((n : ℝ)+1)*
      ‖causalLowerCauchyEvolution (n : ℝ≥0) causalSlowDecayVector‖ := by
  by_contra h
  push Not at h
  apply causalSlowDecayVector_unbounded
  refine ⟨max B (((N : ℝ)+1)*‖causalSlowDecayVector‖), ?_⟩
  rintro y ⟨n, rfl⟩
  by_cases hn : N ≤ n
  · exact (h n hn).trans (le_max_left _ _)
  · have hnr : (n : ℝ)+1 ≤ (N : ℝ)+1 := by
      exact_mod_cast Nat.add_le_add_right (Nat.le_of_lt (lt_of_not_ge hn)) 1
    exact (mul_le_mul hnr (causalLowerCauchyEvolution_norm_le _ _)
      (norm_nonneg _) (by positivity)).trans (le_max_right _ _)

/-- Every positive exponential rate fails for this one fixed input at arbitrarily late times. -/
theorem causalSlowDecayVector_no_exponential_bound_late (a B : ℝ) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ B*Real.exp (-(Real.exp a*(n : ℝ))) <
      ‖causalLowerCauchyEvolution (n : ℝ≥0) causalSlowDecayVector‖ := by
  obtain ⟨n, hn, hu⟩ := causalSlowDecayVector_weighted_late
    (|B| * (1+(Real.exp a)⁻¹)) N
  refine ⟨n, hn, ?_⟩
  by_contra h
  have hb : ‖causalLowerCauchyEvolution (n : ℝ≥0) causalSlowDecayVector‖ ≤
      |B| * Real.exp (-(Real.exp a*(n : ℝ))) :=
    (le_of_not_gt h).trans (mul_le_mul_of_nonneg_right (le_abs_self B) (Real.exp_nonneg _))
  apply (not_le_of_gt hu)
  calc
    _ ≤ ((n : ℝ)+1)*(|B| * Real.exp (-(Real.exp a*(n : ℝ)))) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = |B| * (((n : ℝ)+1)*Real.exp (-(Real.exp a*(n : ℝ)))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (time_weight_exp_bound a n) (abs_nonneg B)

end
end RHTower.FokasLenells
