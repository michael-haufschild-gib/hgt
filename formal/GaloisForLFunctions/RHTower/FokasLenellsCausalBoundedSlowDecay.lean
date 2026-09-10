import GaloisForLFunctions.RHTower.FokasLenellsCausalBoundedBoundaryChains
import GaloisForLFunctions.RHTower.FokasLenellsCausalBoundedEntireIdentification
import GaloisForLFunctions.RHTower.FokasLenellsCausalSlowOrbitAccumulation

/-! One fixed genuine bounded derivative chain with strong decay and no exponential rate.
The same orbit is neither norm-summable at integer times nor Bochner integrable in continuous time. -/
open Complex MeasureTheory Set Filter Topology
open scoped NNReal BigOperators
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance : NormedAddCommGroup causalBoundedChain := causalBoundedChain.normedAddCommGroup
local instance : NormedSpace ℂ causalBoundedChain := causalBoundedChain.normedSpace
local instance : CompleteSpace causalBoundedChain := causalBoundedChain_complete
local instance : IsTopologicalAddGroup causalBoundedChain :=
  (norm_withSeminorms ℂ causalBoundedChain).topologicalAddGroup
local instance : ContinuousSMul ℂ causalBoundedChain :=
  (norm_withSeminorms ℂ causalBoundedChain).continuousSMul
local instance : TopologicalSpace.IsCompletelyPseudoMetrizableSpace causalBoundedChain :=
  ⟨⟨inferInstance, rfl, causalBoundedChain_complete⟩⟩
local instance : BaireSpace causalBoundedChain := BaireSpace.of_completelyPseudoMetrizable
local instance : BarrelledSpace ℂ causalBoundedChain := BaireSpace.instBarrelledSpace

/-- Time-weighted actual orbit readouts on the genuine bounded-chain Banach space. -/
def causalWeightedBoundedChainOrbit (n : ℕ) : causalBoundedChain →L[ℂ] hardyL2ᗮ :=
  (((n : ℝ)+1 : ℝ) : ℂ) • causalBoundedChainOrbit (n : ℝ≥0)

/-- The time-weighted orbit maps have exactly unbounded linear operator-norm growth. -/
theorem norm_causalWeightedBoundedChainOrbit (n : ℕ) :
    ‖causalWeightedBoundedChainOrbit n‖ = (n : ℝ)+1 := by
  have hc : 0 < (n : ℝ)+1 := by positivity
  have hf : ‖(((n : ℝ)+1 : ℝ) : ℂ)‖ = (n : ℝ)+1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg hc.le]
  apply le_antisymm
  · exact (ContinuousLinearMap.opNorm_smul_le _ _).trans_eq
      (by rw [hf, norm_causalBoundedChainOrbit, mul_one])
  · have hne : (((n : ℝ)+1 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
    have he : ((((n : ℝ)+1 : ℝ) : ℂ)⁻¹) • causalWeightedBoundedChainOrbit n =
        causalBoundedChainOrbit (n : ℝ≥0) := by
      change ((((n : ℝ)+1 : ℝ) : ℂ)⁻¹) •
        ((((n : ℝ)+1 : ℝ) : ℂ) • causalBoundedChainOrbit (n : ℝ≥0)) = _
      exact inv_smul_smul₀ hne _
    have h := ContinuousLinearMap.opNorm_smul_le ((((n : ℝ)+1 : ℝ) : ℂ)⁻¹)
      (causalWeightedBoundedChainOrbit n)
    have hl : ‖((((n : ℝ)+1 : ℝ) : ℂ)⁻¹) • causalWeightedBoundedChainOrbit n‖ = 1 :=
      (congrArg (fun A : causalBoundedChain →L[ℂ] hardyL2ᗮ => ‖A‖) he).trans
        (norm_causalBoundedChainOrbit (n : ℝ≥0))
    have hi : ‖((((n : ℝ)+1 : ℝ) : ℂ)⁻¹)‖ = ((n : ℝ)+1)⁻¹ :=
      (norm_inv _).trans (congrArg (fun r : ℝ => r⁻¹) hf)
    have hb : 1 ≤ ((n : ℝ)+1)⁻¹ * ‖causalWeightedBoundedChainOrbit n‖ :=
      hl.symm.trans_le (h.trans_eq (congrArg
        (fun r : ℝ => r * ‖causalWeightedBoundedChainOrbit n‖) hi))
    simpa only [mul_one] using (le_inv_mul_iff₀ hc).mp hb

/-- Banach--Steinhaus provides one actual bounded derivative chain with an unbounded weighted orbit. -/
theorem causalBoundedChain_exists_unbounded_orbit :
    ∃ u : causalBoundedChain, ¬ BddAbove (Set.range (fun n : ℕ => ((n : ℝ)+1)*
      ‖causalLowerCauchyEvolution (n : ℝ≥0) (causalBoundedChainCoordinate 0 u)‖)) := by
  by_contra h
  have hb : ∀ u : causalBoundedChain, BddAbove (Set.range
      (fun n : ℕ => ‖causalWeightedBoundedChainOrbit n u‖)) := by
    intro u
    have hu : BddAbove (Set.range (fun n : ℕ => ((n : ℝ)+1)*
        ‖causalLowerCauchyEvolution (n : ℝ≥0) (causalBoundedChainCoordinate 0 u)‖)) := by
      by_contra hn
      exact h ⟨u, hn⟩
    have he : (fun n : ℕ => ‖causalWeightedBoundedChainOrbit n u‖) =
        (fun n : ℕ => ((n : ℝ)+1)*
          ‖causalLowerCauchyEvolution (n : ℝ≥0) (causalBoundedChainCoordinate 0 u)‖) := by
      funext n
      change ‖(((n : ℝ)+1 : ℝ) : ℂ) • causalBoundedChainOrbit (n : ℝ≥0) u‖ = _
      have hs : ‖(((n : ℝ)+1 : ℝ) : ℂ)‖ = (n : ℝ)+1 := by
        rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      exact (norm_smul (((n : ℝ)+1 : ℝ) : ℂ) (causalBoundedChainOrbit (n : ℝ≥0) u)).trans
        (congrArg (fun r : ℝ => r * ‖causalBoundedChainOrbit (n : ℝ≥0) u‖) hs)
    rwa [he]
  obtain ⟨C, _, hC⟩ := RHTower.exists_uniform_opNorm_bound_of_pointwiseBounded
    causalWeightedBoundedChainOrbit hb
  obtain ⟨n, hn⟩ := exists_nat_gt C
  have hc := hC n
  rw [norm_causalWeightedBoundedChainOrbit] at hc
  linarith only [hn, hc]


/-- One actual infinite derivative chain obtained from the proved smooth uniform-boundedness obstruction. -/
def causalBoundedSlowChain : causalBoundedChain := Classical.choose causalBoundedChain_exists_unbounded_orbit

/-- The initial datum of this one fixed genuine infinite derivative chain. -/
def causalBoundedSlowVector : hardyL2ᗮ := causalBoundedChainCoordinate 0 causalBoundedSlowChain

/-- A single finite bound controls every genuine derivative of this fixed slow datum. -/
theorem causalBoundedSlowChain_all_derivatives_bounded (j : ℕ) :
    ‖causalBoundedChainCoordinate j causalBoundedSlowChain‖ ≤ ‖causalBoundedSlowChain‖ :=
  causalBoundedChainCoordinate_norm_le j causalBoundedSlowChain

/-- Every derivative in the bounded chain is the actual derivative of its predecessor's causal orbit. -/
theorem causalBoundedSlowChain_hasRightDeriv (j : ℕ) :
    HasDerivWithinAt (causalForwardOrbit (causalBoundedChainCoordinate j causalBoundedSlowChain))
      (causalBoundedChainCoordinate (j+1) causalBoundedSlowChain) (Ioi 0) 0 :=
  causalBoundedChainCoordinate_hasRightDeriv j causalBoundedSlowChain

/-- The one fixed datum permits every finite number of actual maximal-generator applications. -/
theorem causalBoundedSlowVector_mem_powerDomain (k : ℕ) :
    causalBoundedSlowVector ∈ causalGeneratorPowerDomain k :=
  causalBoundedChainCoordinate_mem_powerDomain 0 k causalBoundedSlowChain

/-- The same datum is in every finite resolvent-power range at every right-half-plane parameter. -/
theorem causalBoundedSlowVector_resolvent_preimage (z : {z : ℂ // 0 < z.re}) (k : ℕ) :
    ∃ u : hardyL2ᗮ, causalResolventPower z k u = causalBoundedSlowVector := by
  have h := causalBoundedSlowVector_mem_powerDomain k
  rw [← causalResolventPower_range_eq_powerDomain z k] at h
  exact h

/-- Its time-weighted orbit norms are unbounded. -/
theorem causalBoundedSlowVector_unbounded :
    ¬ BddAbove (Set.range (fun n : ℕ => ((n : ℝ)+1)*
      ‖causalLowerCauchyEvolution (n : ℝ≥0) causalBoundedSlowVector‖)) :=
  Classical.choose_spec causalBoundedChain_exists_unbounded_orbit

/-- This genuine all-orders slow datum is nonzero. -/
theorem causalBoundedSlowVector_ne_zero : causalBoundedSlowVector ≠ 0 := by
  intro h
  apply causalBoundedSlowVector_unbounded
  refine ⟨0, ?_⟩
  rintro y ⟨n, rfl⟩
  simp [h]

/-- The one fixed all-orders datum still tends to zero under the actual causal evolution. -/
theorem causalBoundedSlowVector_tendsto :
    Tendsto (fun t : ℝ≥0 => causalLowerCauchyEvolution t causalBoundedSlowVector)
      atTop (𝓝 0) := causalLowerCauchyEvolution_strong_tendsto _

/-- Its weighted orbit exceeds every bound after every prescribed starting time. -/
theorem causalBoundedSlowVector_weighted_late (B : ℝ) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ B < ((n : ℝ)+1)*
      ‖causalLowerCauchyEvolution (n : ℝ≥0) causalBoundedSlowVector‖ := by
  by_contra h
  push Not at h
  apply causalBoundedSlowVector_unbounded
  refine ⟨max B (((N : ℝ)+1)*‖causalBoundedSlowVector‖), ?_⟩
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
theorem causalBoundedSlowVector_no_exponential_bound_late (a B : ℝ) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ B*Real.exp (-(Real.exp a*(n : ℝ))) <
      ‖causalLowerCauchyEvolution (n : ℝ≥0) causalBoundedSlowVector‖ := by
  obtain ⟨n, hn, hu⟩ := causalBoundedSlowVector_weighted_late (|B| * (1+(Real.exp a)⁻¹)) N
  refine ⟨n, hn, ?_⟩
  by_contra h
  have hb : ‖causalLowerCauchyEvolution (n : ℝ≥0) causalBoundedSlowVector‖ ≤
      |B| * Real.exp (-(Real.exp a*(n : ℝ))) :=
    (le_of_not_gt h).trans (mul_le_mul_of_nonneg_right (le_abs_self B) (Real.exp_nonneg _))
  apply not_le_of_gt hu
  calc
    _ ≤ ((n : ℝ)+1)*(|B| * Real.exp (-(Real.exp a*(n : ℝ)))) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = |B| * (((n : ℝ)+1)*Real.exp (-(Real.exp a*(n : ℝ)))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (exponential_weight_bound a n) (abs_nonneg B)

/-- All-orders generator regularity does not make this actual orbit norm summable. -/
theorem causalBoundedSlowVector_norm_not_summable :
    ¬ Summable (fun n : ℕ => ‖causalLowerCauchyEvolution (n : ℝ≥0) causalBoundedSlowVector‖) := by
  intro h
  apply causalBoundedSlowVector_unbounded
  refine ⟨∑' n : ℕ, ‖causalLowerCauchyEvolution (n : ℝ≥0) causalBoundedSlowVector‖, ?_⟩
  rintro y ⟨n, rfl⟩
  exact (causalOrbitNorm_partialSum_lower _ n).trans
    (h.sum_le_tsum (Finset.range (n+1)) (fun _ _ => norm_nonneg _))

/-- Its cumulative actual orbit norm exceeds every real bound. -/
theorem causalBoundedSlowVector_integrals_unbounded (B : ℝ) :
    ∃ t : ℝ≥0, B < ∫ r in (0 : ℝ)..(t : ℝ), ‖causalForwardOrbit causalBoundedSlowVector r‖ := by
  obtain ⟨n, _, hn⟩ := causalBoundedSlowVector_weighted_late (B+‖causalBoundedSlowVector‖) 0
  refine ⟨(n : ℝ≥0), ?_⟩
  have ht := causalOrbitNorm_integral_lower causalBoundedSlowVector (n : ℝ≥0)
  have hu := causalLowerCauchyEvolution_norm_le (n : ℝ≥0) causalBoundedSlowVector
  change (n : ℝ)*‖causalLowerCauchyEvolution (n : ℝ≥0) causalBoundedSlowVector‖ ≤ _ at ht
  nlinarith only [hn, ht, hu]

/-- The actual scalar norm orbit of this one all-orders datum is not integrable. -/
theorem causalBoundedSlowVector_normOrbit_not_integrable :
    ¬ IntegrableOn (fun r : ℝ => ‖causalForwardOrbit causalBoundedSlowVector r‖) (Ioi 0) := by
  intro h
  obtain ⟨t, ht⟩ := causalBoundedSlowVector_integrals_unbounded
    (∫ r in Ioi (0 : ℝ), ‖causalForwardOrbit causalBoundedSlowVector r‖)
  have hb : (∫ r in Ioc (0 : ℝ) (t : ℝ), ‖causalForwardOrbit causalBoundedSlowVector r‖) ≤
      ∫ r in Ioi (0 : ℝ), ‖causalForwardOrbit causalBoundedSlowVector r‖ :=
    setIntegral_mono_set h (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
      (Filter.Eventually.of_forall (fun _ hx => hx.1))
  have he := intervalIntegral.integral_of_le (μ := volume)
    (f := fun r : ℝ => ‖causalForwardOrbit causalBoundedSlowVector r‖) t.property
  exact (not_le_of_gt ht) (he.trans_le hb)

/-- The actual vector orbit remains non-Bochner-integrable despite genuine all-orders regularity. -/
theorem causalBoundedSlowVector_forwardOrbit_not_integrable :
    ¬ IntegrableOn (causalForwardOrbit causalBoundedSlowVector) (Ioi (0 : ℝ)) := by
  intro h
  exact causalBoundedSlowVector_normOrbit_not_integrable h.norm

/-- This fixed slow causal orbit admits an actual entire extension, despite its nonintegrable norm. -/
theorem causalBoundedSlowVector_entire_extension :
    ∃ f : ℂ → hardyL2ᗮ, (∀ z : ℂ, AnalyticAt ℂ f z) ∧
      ∀ t : ℝ≥0, f ((t : ℝ) : ℂ) = causalLowerCauchyEvolution t causalBoundedSlowVector :=
  causalBoundedChainCoordinate_entire_extension 0 causalBoundedSlowChain

end
end RHTower.FokasLenells
