import GaloisForLFunctions.RHTower.FokasLenellsCausalGeneratorPowerDomains
import GaloisForLFunctions.RHTower.FokasLenellsCausalSlowDecay

/-! At every finite genuine generator order, one fixed actual datum decays strongly but
violates every exponential decay bound arbitrarily late. -/
open Complex MeasureTheory Set Filter Topology
open scoped NNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section
local instance fokasLenellsCausalSmoothSlowDecayInst1 : CompleteSpace (hardyL2ᗮ) := hardyL2.isClosed_orthogonal.completeSpace_coe

/-- The concrete time-weighted family after finite actual resolvent smoothing. -/
def causalWeightedSmoothedEvolution (z : {z : ℂ // 0 < z.re}) (k n : ℕ) :
    hardyL2ᗮ →L[ℂ] hardyL2ᗮ :=
  (((n : ℝ)+1 : ℝ) : ℂ) • causalSmoothedEvolution z k (n : ℝ≥0)

/-- Every smoothed time-weighted family has the exact unbounded linear growth in operator norm. -/
theorem norm_causalWeightedSmoothedEvolution (z : {z : ℂ // 0 < z.re}) (k n : ℕ) :
    ‖causalWeightedSmoothedEvolution z k n‖ = ((n : ℝ)+1)*(z.val.re⁻¹)^k := by
  have hc : 0 < (n : ℝ)+1 := by positivity
  have hf : ‖(((n : ℝ)+1 : ℝ) : ℂ)‖ = (n : ℝ)+1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg hc.le]
  apply le_antisymm
  · exact (ContinuousLinearMap.opNorm_smul_le _ _).trans_eq
      (by rw [hf, norm_causalSmoothedEvolution])
  · have hne : (((n : ℝ)+1 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
    have he : ((((n : ℝ)+1 : ℝ) : ℂ)⁻¹) • causalWeightedSmoothedEvolution z k n =
        causalSmoothedEvolution z k (n : ℝ≥0) := by
      change ((((n : ℝ)+1 : ℝ) : ℂ)⁻¹) •
        ((((n : ℝ)+1 : ℝ) : ℂ) • causalSmoothedEvolution z k (n : ℝ≥0)) = _
      exact inv_smul_smul₀ hne _
    have h := ContinuousLinearMap.opNorm_smul_le ((((n : ℝ)+1 : ℝ) : ℂ)⁻¹)
      (causalWeightedSmoothedEvolution z k n)
    rw [he, norm_causalSmoothedEvolution, norm_inv, hf] at h
    exact (le_inv_mul_iff₀ hc).mp h

/-- Banach--Steinhaus produces an input whose actual smoothed orbit has unbounded weighted norm. -/
theorem causalSmoothedEvolution_exists_unbounded_input (z : {z : ℂ // 0 < z.re}) (k : ℕ) :
    ∃ u : hardyL2ᗮ, ¬ BddAbove (Set.range (fun n : ℕ => ((n : ℝ)+1)*
      ‖causalLowerCauchyEvolution (n : ℝ≥0) (causalResolventPower z k u)‖)) := by
  by_contra h
  have hb : ∀ u : hardyL2ᗮ, BddAbove (Set.range
      (fun n : ℕ => ‖causalWeightedSmoothedEvolution z k n u‖)) := by
    intro u
    have hu : BddAbove (Set.range (fun n : ℕ => ((n : ℝ)+1)*
        ‖causalLowerCauchyEvolution (n : ℝ≥0) (causalResolventPower z k u)‖)) := by
      by_contra hn
      exact h ⟨u, hn⟩
    have he : (fun n : ℕ => ‖causalWeightedSmoothedEvolution z k n u‖) =
        (fun n : ℕ => ((n : ℝ)+1)*
          ‖causalLowerCauchyEvolution (n : ℝ≥0) (causalResolventPower z k u)‖) := by
      funext n
      change ‖(((n : ℝ)+1 : ℝ) : ℂ) • causalSmoothedEvolution z k (n : ℝ≥0) u‖ = _
      rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      rfl
    rwa [he]
  obtain ⟨C, _, hC⟩ := RHTower.exists_uniform_opNorm_bound_of_pointwiseBounded
    (causalWeightedSmoothedEvolution z k) hb
  have hd : 0 < (z.val.re⁻¹)^k := pow_pos (inv_pos.mpr z.property) k
  obtain ⟨n, hn⟩ := exists_nat_gt (C / (z.val.re⁻¹)^k)
  have hc := hC n
  rw [norm_causalWeightedSmoothedEvolution] at hc
  have hn' := (div_lt_iff₀ hd).mp hn
  nlinarith only [hn', hc, hd]

/-- One actual slow datum obtained by a k-th genuine resolvent power. -/
def causalSmoothSlowDecayVector (z : {z : ℂ // 0 < z.re}) (k : ℕ) : hardyL2ᗮ :=
  causalResolventPower z k (Classical.choose (causalSmoothedEvolution_exists_unbounded_input z k))

/-- The chosen actual datum has the asserted genuine generator regularity. -/
theorem causalSmoothSlowDecayVector_mem_powerDomain (z : {z : ℂ // 0 < z.re}) (k : ℕ) :
    causalSmoothSlowDecayVector z k ∈ causalGeneratorPowerDomain k :=
  causalResolventPower_mem_powerDomain z k _

/-- This one chosen regular vector has unbounded weighted orbit norms. -/
theorem causalSmoothSlowDecayVector_unbounded (z : {z : ℂ // 0 < z.re}) (k : ℕ) :
    ¬ BddAbove (Set.range (fun n : ℕ => ((n : ℝ)+1)*
      ‖causalLowerCauchyEvolution (n : ℝ≥0) (causalSmoothSlowDecayVector z k)‖)) :=
  Classical.choose_spec (causalSmoothedEvolution_exists_unbounded_input z k)

/-- The actual regular slow datum is nonzero at every finite order. -/
theorem causalSmoothSlowDecayVector_ne_zero (z : {z : ℂ // 0 < z.re}) (k : ℕ) :
    causalSmoothSlowDecayVector z k ≠ 0 := by
  intro h
  apply causalSmoothSlowDecayVector_unbounded z k
  refine ⟨0, ?_⟩
  rintro y ⟨n, rfl⟩
  simp [h]

/-- The same regular slow datum tends to zero under actual continuous-time causal evolution. -/
theorem causalSmoothSlowDecayVector_tendsto (z : {z : ℂ // 0 < z.re}) (k : ℕ) :
    Tendsto (fun t : ℝ≥0 => causalLowerCauchyEvolution t (causalSmoothSlowDecayVector z k))
      atTop (𝓝 0) := causalLowerCauchyEvolution_strong_tendsto _

/-- Weighted orbit norms of this one regular datum exceed every bound arbitrarily late. -/
theorem causalSmoothSlowDecayVector_weighted_late (z : {z : ℂ // 0 < z.re}) (k : ℕ)
    (B : ℝ) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ B < ((n : ℝ)+1)*
      ‖causalLowerCauchyEvolution (n : ℝ≥0) (causalSmoothSlowDecayVector z k)‖ := by
  by_contra h
  push Not at h
  apply causalSmoothSlowDecayVector_unbounded z k
  refine ⟨max B (((N : ℝ)+1)*‖causalSmoothSlowDecayVector z k‖), ?_⟩
  rintro y ⟨n, rfl⟩
  by_cases hn : N ≤ n
  · exact (h n hn).trans (le_max_left _ _)
  · have hnr : (n : ℝ)+1 ≤ (N : ℝ)+1 := by
      exact_mod_cast Nat.add_le_add_right (Nat.le_of_lt (lt_of_not_ge hn)) 1
    exact (mul_le_mul hnr (causalLowerCauchyEvolution_norm_le _ _)
      (norm_nonneg _) (by positivity)).trans (le_max_right _ _)

private theorem exponential_time_bound (a : ℝ) (n : ℕ) :
    ((n : ℝ)+1)*Real.exp (-(Real.exp a*(n : ℝ))) ≤ 1+(Real.exp a)⁻¹ := by
  have hn := Real.le_inv_mul_exp (n : ℝ) (Real.exp_pos a)
  have he : 1 ≤ Real.exp (Real.exp a*(n : ℝ)) := Real.one_le_exp (by positivity)
  have hb : (n : ℝ)+1 ≤ (1+(Real.exp a)⁻¹)*Real.exp (Real.exp a*(n : ℝ)) := by
    nlinarith only [hn, he]
  calc
    _ ≤ ((1+(Real.exp a)⁻¹)*Real.exp (Real.exp a*(n : ℝ)))*
        Real.exp (-(Real.exp a*(n : ℝ))) := mul_le_mul_of_nonneg_right hb (Real.exp_nonneg _)
    _ = _ := by rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

/-- At every finite generator order, one fixed regular input violates every positive exponential
rate and every real prefactor after every prescribed starting time. -/
theorem causalSmoothSlowDecayVector_no_exponential_bound_late
    (z : {z : ℂ // 0 < z.re}) (k : ℕ) (a B : ℝ) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ B*Real.exp (-(Real.exp a*(n : ℝ))) <
      ‖causalLowerCauchyEvolution (n : ℝ≥0) (causalSmoothSlowDecayVector z k)‖ := by
  obtain ⟨n, hn, hu⟩ := causalSmoothSlowDecayVector_weighted_late z k
    (|B| * (1+(Real.exp a)⁻¹)) N
  refine ⟨n, hn, ?_⟩
  by_contra h
  have hb : ‖causalLowerCauchyEvolution (n : ℝ≥0) (causalSmoothSlowDecayVector z k)‖ ≤
      |B| * Real.exp (-(Real.exp a*(n : ℝ))) :=
    (le_of_not_gt h).trans (mul_le_mul_of_nonneg_right (le_abs_self B) (Real.exp_nonneg _))
  apply not_le_of_gt hu
  calc
    _ ≤ ((n : ℝ)+1)*(|B| * Real.exp (-(Real.exp a*(n : ℝ)))) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = |B| * (((n : ℝ)+1)*Real.exp (-(Real.exp a*(n : ℝ)))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (exponential_time_bound a n) (abs_nonneg B)

end
end RHTower.FokasLenells
