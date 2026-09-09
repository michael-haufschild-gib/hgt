import GaloisForLFunctions.RHTower.FokasLenellsCausalSlowDecay

/-! Strong decay need not give finite cumulative orbit size. The same actual slow datum has
nonsummable discrete orbit norms and a nonintegrable continuous-time orbit. -/
open Complex MeasureTheory Set Filter Topology
open scoped NNReal BigOperators
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

/-- Every actual causal orbit has a nonincreasing norm. -/
theorem causalOrbitNorm_antitone (u : hardyL2ᗮ) :
    Antitone (fun t : ℝ≥0 => ‖causalLowerCauchyEvolution t u‖) := by
  intro s t h
  change ‖causalLowerCauchyEvolution t u‖ ≤ ‖causalLowerCauchyEvolution s u‖
  have he : (t-s)+s = t := tsub_add_cancel_of_le h
  rw [← he, causalLowerCauchyEvolution_add]
  exact causalLowerCauchyEvolution_norm_le _ _

/-- Cumulative integer-time orbit norms dominate the elapsed-time weighted terminal norm. -/
theorem causalOrbitNorm_partialSum_lower (u : hardyL2ᗮ) (n : ℕ) :
    ((n : ℝ)+1)*‖causalLowerCauchyEvolution (n : ℝ≥0) u‖ ≤
      ∑ i ∈ Finset.range (n+1), ‖causalLowerCauchyEvolution (i : ℝ≥0) u‖ := by
  calc
    _ = ∑ _i ∈ Finset.range (n+1), ‖causalLowerCauchyEvolution (n : ℝ≥0) u‖ := by
      simp
    _ ≤ _ := Finset.sum_le_sum (fun i hi => causalOrbitNorm_antitone u
      (by exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hi)))

/-- The actual continuous cumulative norm dominates time times the terminal orbit norm. -/
theorem causalOrbitNorm_integral_lower (u : hardyL2ᗮ) (t : ℝ≥0) :
    (t : ℝ)*‖causalLowerCauchyEvolution t u‖ ≤
      ∫ r in (0 : ℝ)..(t : ℝ), ‖causalForwardOrbit u r‖ := by
  have h : (∫ r in (0 : ℝ)..(t : ℝ), ‖causalLowerCauchyEvolution t u‖) ≤
      ∫ r in (0 : ℝ)..(t : ℝ), ‖causalForwardOrbit u r‖ :=
    intervalIntegral.integral_mono_on t.property
    (intervalIntegrable_const : IntervalIntegrable
      (fun _ : ℝ => ‖causalLowerCauchyEvolution t u‖) volume 0 (t : ℝ))
    ((causalForwardOrbit_continuous u).norm.intervalIntegrable 0 (t : ℝ))
    (fun r hr => causalOrbitNorm_antitone u (Real.toNNReal_le_iff_le_coe.2 hr.2))
  simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] using h

/-- The fixed slow datum has divergent total discrete orbit norm. -/
theorem causalSlowDecayVector_norm_not_summable :
    ¬ Summable (fun n : ℕ => ‖causalLowerCauchyEvolution (n : ℝ≥0) causalSlowDecayVector‖) := by
  intro h
  apply causalSlowDecayVector_unbounded
  refine ⟨∑' n : ℕ, ‖causalLowerCauchyEvolution (n : ℝ≥0) causalSlowDecayVector‖, ?_⟩
  rintro y ⟨n, rfl⟩
  exact (causalOrbitNorm_partialSum_lower _ n).trans
    (h.sum_le_tsum (Finset.range (n+1)) (fun _ _ => norm_nonneg _))

/-- Finite cumulative continuous-time norms of the fixed slow datum exceed every real bound. -/
theorem causalSlowDecayVector_integrals_unbounded (B : ℝ) :
    ∃ t : ℝ≥0, B < ∫ r in (0 : ℝ)..(t : ℝ), ‖causalForwardOrbit causalSlowDecayVector r‖ := by
  obtain ⟨n, _, hn⟩ := causalSlowDecayVector_weighted_late (B+‖causalSlowDecayVector‖) 0
  refine ⟨(n : ℝ≥0), ?_⟩
  have ht := causalOrbitNorm_integral_lower causalSlowDecayVector (n : ℝ≥0)
  have hu := causalLowerCauchyEvolution_norm_le (n : ℝ≥0) causalSlowDecayVector
  change (n : ℝ)*‖causalLowerCauchyEvolution (n : ℝ≥0) causalSlowDecayVector‖ ≤ _ at ht
  nlinarith only [hn, ht, hu]

/-- Even its scalar norm orbit is not integrable on the positive time axis. -/
theorem causalSlowDecayVector_normOrbit_not_integrable :
    ¬ IntegrableOn (fun r : ℝ => ‖causalForwardOrbit causalSlowDecayVector r‖) (Ioi 0) := by
  intro h
  obtain ⟨t, ht⟩ := causalSlowDecayVector_integrals_unbounded
    (∫ r in Ioi (0 : ℝ), ‖causalForwardOrbit causalSlowDecayVector r‖)
  have hb : (∫ r in Ioc (0 : ℝ) (t : ℝ), ‖causalForwardOrbit causalSlowDecayVector r‖) ≤
      ∫ r in Ioi (0 : ℝ), ‖causalForwardOrbit causalSlowDecayVector r‖ :=
    setIntegral_mono_set h (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
      (Filter.Eventually.of_forall (fun _ hx => hx.1))
  have he := intervalIntegral.integral_of_le (μ := volume)
    (f := fun r : ℝ => ‖causalForwardOrbit causalSlowDecayVector r‖) t.property
  exact (not_le_of_gt ht) (he.trans_le hb)

/-- The actual vector orbit of the same strongly stable datum is not Bochner integrable. -/
theorem causalSlowDecayVector_forwardOrbit_not_integrable :
    ¬ IntegrableOn (causalForwardOrbit causalSlowDecayVector) (Ioi (0 : ℝ)) := by
  intro h
  exact causalSlowDecayVector_normOrbit_not_integrable h.norm

end
end RHTower.FokasLenells
