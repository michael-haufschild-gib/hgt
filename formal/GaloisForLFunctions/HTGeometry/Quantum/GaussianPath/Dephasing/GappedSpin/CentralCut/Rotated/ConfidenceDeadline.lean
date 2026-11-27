import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.Rotated.JointSurvival

/-! # High-confidence deadlines for the first robust crossing and subsequent first waits -/

open Set Filter MeasureTheory ProbabilityTheory Real
namespace GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut
open PrescribedTimes AccuracyScales.TenthPlateau
noncomputable section

/-- A deadline whose joint survival probability, even inside the
all-strong laboratory sector, is at most exp(−a·2ᴷ) has log deadline
at least (a·2ᴷ−CK²)/7. The failure probability is unconditional. -/
theorem all_strong_confidence_deadline :
    ∃ C > (0:ℝ), ∀ᶠ k : ℕ in atTop,
      let n := k+1
      let K := n+2
      let P := nearHilbertContinuousCircuitBudget K
      let μ := Measure.pi (fun _ : PrefixIndex n => gaussianReal 0 1)
      ∀ a : ℝ, ∀ T ≥ (1:ℝ),
        μ.real {x | x ∈ allCoordStrongEvent n (1/100) ∧ T < crossingOrigin n P (9/80) x ∧
          ∀ s ≤ P/2, T < crossingWait n P s x} ≤ exp (-a*2^K) →
        a*2^K-C*(K:ℝ)^2 ≤ 7*log T := by
  obtain ⟨C,hC,hfloor⟩ := all_strong_first_excursion
  refine ⟨C,hC,?_⟩
  filter_upwards [hfloor] with k hb
  intro n K P μ a T hT htail
  have hpos := zero_lt_one.trans_le hT
  have h := (hb T hT).trans (mul_le_mul_of_nonneg_left htail (pow_nonneg hpos.le _))
  have hlog := log_le_log (exp_pos _) h
  rw [log_exp,log_mul (pow_pos hpos 7).ne' (exp_pos _).ne',log_pow,log_exp] at hlog
  change -C*(K:ℝ)^2 ≤ (7:ℝ)*log T+ -a*2^K at hlog
  linarith only [hlog]

/-- The same deadline bound applies to the marginal first wait at
each individual budget, including the scalar return. -/
theorem first_wait_confidence_deadline :
    ∃ C > (0:ℝ), ∀ᶠ k : ℕ in atTop,
      let n := k+1
      let K := n+2
      let P := nearHilbertContinuousCircuitBudget K
      let μ := Measure.pi (fun _ : PrefixIndex n => gaussianReal 0 1)
      ∀ s ≤ P/2, ∀ a : ℝ, ∀ T ≥ (1:ℝ),
        μ.real {x | T < crossingWait n P s x} ≤ exp (-a*2^K) →
        a*2^K-C*(K:ℝ)^2 ≤ 7*log T := by
  obtain ⟨C,hC,hjoint⟩ := all_strong_confidence_deadline
  refine ⟨C,hC,?_⟩
  filter_upwards [hjoint] with k h
  intro n K P μ s hs a T hT htail
  apply h a T hT
  exact (measureReal_mono (fun x hx => hx.2.2 s hs) (measure_ne_top _ _)).trans htail

#print axioms all_strong_confidence_deadline
#print axioms first_wait_confidence_deadline
end
end GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut
