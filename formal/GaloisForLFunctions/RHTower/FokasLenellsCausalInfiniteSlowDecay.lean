import GaloisForLFunctions.RHTower.FokasLenellsCausalSmoothUniformObstruction
import GaloisForLFunctions.RHTower.FokasLenellsCausalSlowOrbitAccumulation

/-! One fixed genuine all-orders input with strong decay and no exponential rate.
The same orbit is neither norm-summable at integer times nor Bochner integrable in continuous time. -/
open Complex MeasureTheory Set Filter Topology
open scoped NNReal BigOperators
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

/-- One actual infinite derivative chain obtained from the proved smooth uniform-boundedness obstruction. -/
def causalInfiniteSlowChain : causalSmoothGraph := Classical.choose causalSmoothGraph_exists_unbounded_orbit

/-- The initial datum of this one fixed genuine infinite derivative chain. -/
def causalInfiniteSlowVector : hardyL2ᗮ := causalSmoothGraphCoordinate 0 causalInfiniteSlowChain

/-- The one fixed datum permits every finite number of actual maximal-generator applications. -/
theorem causalInfiniteSlowVector_mem_powerDomain (k : ℕ) :
    causalInfiniteSlowVector ∈ causalGeneratorPowerDomain k :=
  causalSmoothGraphCoordinate_mem_powerDomain 0 k causalInfiniteSlowChain

/-- The same datum is in every finite resolvent-power range at every right-half-plane parameter. -/
theorem causalInfiniteSlowVector_resolvent_preimage (z : {z : ℂ // 0 < z.re}) (k : ℕ) :
    ∃ u : hardyL2ᗮ, causalResolventPower z k u = causalInfiniteSlowVector := by
  have h := causalInfiniteSlowVector_mem_powerDomain k
  rw [← causalResolventPower_range_eq_powerDomain z k] at h
  exact h

/-- Its time-weighted orbit norms are unbounded. -/
theorem causalInfiniteSlowVector_unbounded :
    ¬ BddAbove (Set.range (fun n : ℕ => ((n : ℝ)+1)*
      ‖causalLowerCauchyEvolution (n : ℝ≥0) causalInfiniteSlowVector‖)) :=
  Classical.choose_spec causalSmoothGraph_exists_unbounded_orbit

/-- This genuine all-orders slow datum is nonzero. -/
theorem causalInfiniteSlowVector_ne_zero : causalInfiniteSlowVector ≠ 0 := by
  intro h
  apply causalInfiniteSlowVector_unbounded
  refine ⟨0, ?_⟩
  rintro y ⟨n, rfl⟩
  simp [h]

/-- The one fixed all-orders datum still tends to zero under the actual causal evolution. -/
theorem causalInfiniteSlowVector_tendsto :
    Tendsto (fun t : ℝ≥0 => causalLowerCauchyEvolution t causalInfiniteSlowVector)
      atTop (𝓝 0) := causalLowerCauchyEvolution_strong_tendsto _

/-- Its weighted orbit exceeds every bound after every prescribed starting time. -/
theorem causalInfiniteSlowVector_weighted_late (B : ℝ) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ B < ((n : ℝ)+1)*
      ‖causalLowerCauchyEvolution (n : ℝ≥0) causalInfiniteSlowVector‖ := by
  by_contra h
  push Not at h
  apply causalInfiniteSlowVector_unbounded
  refine ⟨max B (((N : ℝ)+1)*‖causalInfiniteSlowVector‖), ?_⟩
  rintro y ⟨n, rfl⟩
  by_cases hn : N ≤ n
  · exact (h n hn).trans (le_max_left _ _)
  · have hnr : (n : ℝ)+1 ≤ (N : ℝ)+1 := by
      exact_mod_cast Nat.add_le_add_right (Nat.le_of_lt (lt_of_not_ge hn)) 1
    exact (mul_le_mul hnr (causalLowerCauchyEvolution_norm_le _ _)
      (norm_nonneg _) (by positivity)).trans (le_max_right _ _)

private theorem exponential_weight_bound (a : ℝ) (n : ℕ) :
    ((n : ℝ)+1)*Real.exp (-(Real.exp a*(n : ℝ))) ≤ 1+(Real.exp a)⁻¹ := by
  have hn := Real.le_inv_mul_exp (n : ℝ) (Real.exp_pos a)
  have he : 1 ≤ Real.exp (Real.exp a*(n : ℝ)) := Real.one_le_exp (by positivity)
  have hb : (n : ℝ)+1 ≤ (1+(Real.exp a)⁻¹)*Real.exp (Real.exp a*(n : ℝ)) := by
    nlinarith only [hn, he]
  calc
    _ ≤ ((1+(Real.exp a)⁻¹)*Real.exp (Real.exp a*(n : ℝ)))*
        Real.exp (-(Real.exp a*(n : ℝ))) := mul_le_mul_of_nonneg_right hb (Real.exp_nonneg _)
    _ = _ := by rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

/-- This same all-orders datum violates every positive exponential rate and every prefactor
arbitrarily late in its actual orbit. -/
theorem causalInfiniteSlowVector_no_exponential_bound_late (a B : ℝ) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ B*Real.exp (-(Real.exp a*(n : ℝ))) <
      ‖causalLowerCauchyEvolution (n : ℝ≥0) causalInfiniteSlowVector‖ := by
  obtain ⟨n, hn, hu⟩ := causalInfiniteSlowVector_weighted_late (|B| * (1+(Real.exp a)⁻¹)) N
  refine ⟨n, hn, ?_⟩
  by_contra h
  have hb : ‖causalLowerCauchyEvolution (n : ℝ≥0) causalInfiniteSlowVector‖ ≤
      |B| * Real.exp (-(Real.exp a*(n : ℝ))) :=
    (le_of_not_gt h).trans (mul_le_mul_of_nonneg_right (le_abs_self B) (Real.exp_nonneg _))
  apply not_le_of_gt hu
  calc
    _ ≤ ((n : ℝ)+1)*(|B| * Real.exp (-(Real.exp a*(n : ℝ)))) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = |B| * (((n : ℝ)+1)*Real.exp (-(Real.exp a*(n : ℝ)))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (exponential_weight_bound a n) (abs_nonneg B)

/-- All-orders generator regularity does not make this actual orbit norm summable. -/
theorem causalInfiniteSlowVector_norm_not_summable :
    ¬ Summable (fun n : ℕ => ‖causalLowerCauchyEvolution (n : ℝ≥0) causalInfiniteSlowVector‖) := by
  intro h
  apply causalInfiniteSlowVector_unbounded
  refine ⟨∑' n : ℕ, ‖causalLowerCauchyEvolution (n : ℝ≥0) causalInfiniteSlowVector‖, ?_⟩
  rintro y ⟨n, rfl⟩
  exact (causalOrbitNorm_partialSum_lower _ n).trans
    (h.sum_le_tsum (Finset.range (n+1)) (fun _ _ => norm_nonneg _))

/-- Its cumulative actual orbit norm exceeds every real bound. -/
theorem causalInfiniteSlowVector_integrals_unbounded (B : ℝ) :
    ∃ t : ℝ≥0, B < ∫ r in (0 : ℝ)..(t : ℝ), ‖causalForwardOrbit causalInfiniteSlowVector r‖ := by
  obtain ⟨n, _, hn⟩ := causalInfiniteSlowVector_weighted_late (B+‖causalInfiniteSlowVector‖) 0
  refine ⟨(n : ℝ≥0), ?_⟩
  have ht := causalOrbitNorm_integral_lower causalInfiniteSlowVector (n : ℝ≥0)
  have hu := causalLowerCauchyEvolution_norm_le (n : ℝ≥0) causalInfiniteSlowVector
  change (n : ℝ)*‖causalLowerCauchyEvolution (n : ℝ≥0) causalInfiniteSlowVector‖ ≤ _ at ht
  nlinarith only [hn, ht, hu]

/-- The actual scalar norm orbit of this one all-orders datum is not integrable. -/
theorem causalInfiniteSlowVector_normOrbit_not_integrable :
    ¬ IntegrableOn (fun r : ℝ => ‖causalForwardOrbit causalInfiniteSlowVector r‖) (Ioi 0) := by
  intro h
  obtain ⟨t, ht⟩ := causalInfiniteSlowVector_integrals_unbounded
    (∫ r in Ioi (0 : ℝ), ‖causalForwardOrbit causalInfiniteSlowVector r‖)
  have hb : (∫ r in Ioc (0 : ℝ) (t : ℝ), ‖causalForwardOrbit causalInfiniteSlowVector r‖) ≤
      ∫ r in Ioi (0 : ℝ), ‖causalForwardOrbit causalInfiniteSlowVector r‖ :=
    setIntegral_mono_set h (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
      (Filter.Eventually.of_forall (fun _ hx => hx.1))
  have he := intervalIntegral.integral_of_le (μ := volume)
    (f := fun r : ℝ => ‖causalForwardOrbit causalInfiniteSlowVector r‖) t.property
  exact (not_le_of_gt ht) (he.trans_le hb)

/-- The actual vector orbit remains non-Bochner-integrable despite genuine all-orders regularity. -/
theorem causalInfiniteSlowVector_forwardOrbit_not_integrable :
    ¬ IntegrableOn (causalForwardOrbit causalInfiniteSlowVector) (Ioi (0 : ℝ)) := by
  intro h
  exact causalInfiniteSlowVector_normOrbit_not_integrable h.norm

end
end RHTower.FokasLenells
