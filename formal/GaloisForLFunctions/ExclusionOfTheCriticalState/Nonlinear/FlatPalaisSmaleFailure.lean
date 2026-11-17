import GaloisForLFunctions.ExclusionOfTheCriticalState.Nonlinear.FlatEvenIntegralEnergy

/-!
# Flat energy has a noncompact critical sequence at its unique minimum

Lebesgue L² admits a sequence of unit profiles whose reflected flat
energy and genuine Fréchet gradient tend to zero. No subsequence
converges in norm: continuity would make its limit the unique zero
profile, contradicting the retained unit norm. Thus uniqueness of the
critical state does not provide Palais–Smale compactness, even at the
minimum energy level.
-/

open MeasureTheory Filter Topology
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.FlatConvex
noncomputable section

/-- A unit-norm critical sequence at energy zero has no norm-convergent subsequence. -/
theorem exists_noncompact_flat_critical_sequence :
    ∃ f : ℕ → Lp ℝ 2 (volume : Measure ℝ),
      (∀ n, ‖f n‖ = 1) ∧
      Tendsto (fun n => evenIntegralEnergy (f n)) atTop (𝓝 0) ∧
      Tendsto (fun n => ‖fderiv ℝ evenIntegralEnergy (f n)‖) atTop (𝓝 0) ∧
      ∀ (j : ℕ → ℕ), StrictMono j → ∀ g, ¬ Tendsto (fun n => f (j n)) atTop (𝓝 g) := by
  have hex (n : ℕ) := evenEnergy_unit_approximate_critical_profile
    (show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity)
  choose f hn he hg using hex
  have hE : Tendsto (fun n => evenIntegralEnergy (f n)) atTop (𝓝 0) :=
    squeeze_zero (fun n => (he n).1.le) (fun n => (he n).2.le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hG : Tendsto (fun n => ‖evenGradientLp (f n)‖) atTop (𝓝 0) :=
    squeeze_zero (fun n => norm_nonneg _) (fun n => (hg n).2.le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨f, hn, hE, ?_, ?_⟩
  · simpa only [(evenIntegralEnergy_hasFDerivAt _).fderiv, innerSL_apply_norm] using hG
  · intro j hj g hlim
    have heq : evenIntegralEnergy g = 0 := tendsto_nhds_unique
      (evenIntegralEnergy_contDiff_one.continuous.continuousAt.tendsto.comp hlim)
      (hE.comp hj.tendsto_atTop)
    have hg0 := (evenIntegralEnergy_zero_iff g).mp heq
    have hnorm : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 ‖g‖) := by
      simpa only [hn] using hlim.norm
    have heqnorm : (1 : ℝ) = ‖g‖ := tendsto_nhds_unique tendsto_const_nhds hnorm
    rw [hg0, norm_zero] at heqnorm
    exact one_ne_zero heqnorm

#print axioms exists_noncompact_flat_critical_sequence
end
end GaloisForLFunctions.ExclusionOfTheCriticalState.FlatConvex
