import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.ReturnIntensity.Gap
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.EmissionRate.Readout
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.UniversalResponse.ThermalCoherence

/-! # Phase-insensitive wave and thermal measurements of quantum composition -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.ReturnIntensity

open Filter Topology UniversalResponse ModeCapacities CoherentRay
open scoped NNReal

theorem wave_signal (A : Response) (f : Gas) (t : ℝ≥0) :
    inner ℂ f (evolution A t f) = signal A (fun n => ‖f n‖^2) t := by
  symm
  apply HasSum.tsum_eq
  apply (lp.hasSum_inner (𝕜 := ℂ) f (evolution A t f)).congr_fun
  intro n
  rw [RCLike.inner_apply, evolution_apply, mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]

private theorem singleton_return (A : Response) (f : Gas) {m : ℕ+} (only : ∀ n, n ≠ m → f n = 0) :
    ContinuousAt (fun t => ‖inner ℂ f (evolution A t f)‖) 0 := by
  have single (t : ℝ≥0) :
      ‖inner ℂ f (evolution A t f)‖ = Real.sqrt (Real.exp (-(t:ℝ)*energy m)) * ‖f m‖^2 := by
    rw [wave_signal, signal, tsum_eq_single m (fun n hn => by simp [only n hn]),
      norm_mul, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
    have mass : ‖survivalAmplitude A m t‖^2 = Real.exp (-(t:ℝ)*energy m) :=
      A.property.2 _ (survival_share t.property m)
    rw [← mass, Real.sqrt_sq (norm_nonneg _)]
  rw [show (fun t => ‖inner ℂ f (evolution A t f)‖) =
    (fun t : ℝ≥0 => Real.sqrt (Real.exp (-(t:ℝ)*energy m)) * ‖f m‖^2) from funext single]
  exact ((Real.continuous_sqrt.comp (Real.continuous_exp.comp
    (NNReal.continuous_coe.neg.mul continuous_const))).mul continuous_const).continuousAt

/-- A wave supported on one energy always returns continuously in magnitude.
Every other wave distinguishes exactly the continuous critical powers. -/
theorem wave_intensity_iff (A : Response) (f : Gas) :
    ContinuousAt (fun t => ‖inner ℂ f (evolution A t f)‖) 0 ↔
      (∃ m : ℕ+, ∀ n, n ≠ m → f n = 0) ∨
        ∃! s : Conserving, ∀ x ∈ Shares, A.val x = power s.val x := by
  by_cases single : ∃ m : ℕ+, ∀ n, n ≠ m → f n = 0
  · exact ⟨fun _ => Or.inl single,fun _ => single.elim (fun _ hm => singleton_return A f hm)⟩
  rw [or_iff_right single]
  have someMode : ∃ m : ℕ+, f m ≠ 0 := by
    by_contra! zero
    exact single ⟨1,fun n _ => zero n⟩
  obtain ⟨m,hm⟩ := someMode
  have other : ∃ n : ℕ+, n ≠ m ∧ f n ≠ 0 := by
    by_contra! atMost
    exact single ⟨m,atMost⟩
  obtain ⟨n,ne,hn⟩ := other
  have pos (k : ℕ+) (hk : f k ≠ 0) : 0 < ‖f k‖^2 := pow_pos (norm_pos_iff.mpr hk) 2
  simp only [wave_signal]
  rcases lt_or_gt_of_ne ne with h | h
  · exact two_levels_iff A (fun _ => sq_nonneg _) (EmissionRate.mass_sum f).summable h (pos n hn) (pos m hm)
  · exact two_levels_iff A (fun _ => sq_nonneg _) (EmissionRate.mass_sum f).summable h (pos m hm) (pos n hn)

/-- Measuring the magnitude of one unresolved Gibbs trace at the origin
detects the unique exponent governing all complex thermal traces. -/
theorem thermal_intensity_iff (A : Response) (β : TraceTemperature) :
    ContinuousAt (fun t => ‖ContinuousLinearMap.opTrace (prepared A β t)‖) 0 ↔
      ∃! s : Conserving, (∀ x ∈ Shares, A.val x = power s.val x) ∧
        ∀ (γ : TraceTemperature) (t : ℝ≥0),
          ContinuousLinearMap.opTrace (prepared A γ t) = riemannZeta ((γ.val:ℂ)+((t:ℝ):ℂ)*s.val) := by
  rw [← thermal_coherence_iff A β]
  simp only [prepared_real, prepared_trace]
  change ContinuousAt (fun t => ‖signal A (thermalWeight β) t‖) 0 ↔ _
  have pos := fun n => (thermalWeight_pos β n).le
  rw [two_levels_iff A pos (thermalWeight_summable β) (show (1:ℕ+)<2 from one_lt_two)
      (thermalWeight_pos β 1) (thermalWeight_pos β 2),
    weighted_iff A pos (thermalWeight_summable β) ⟨2,Real.log_pos (by norm_num),thermalWeight_pos β 2⟩]

#print axioms wave_signal
#print axioms wave_intensity_iff
#print axioms thermal_intensity_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.ReturnIntensity
