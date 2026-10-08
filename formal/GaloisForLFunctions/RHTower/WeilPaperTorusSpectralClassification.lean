import GaloisForLFunctions.RHTower.WeilPaperSpectralKernelClassification
import GaloisForLFunctions.RHTower.WeilLagFunctionDense

/-!
# The prime-torus law retains the entire spectral kernel and full energy

Rational character moments recover autocorrelation at logarithms of positive
rational numbers. These lags are dense, so continuity recovers the entire kernel.
The compact prime-torus pushforward therefore loses no spectral information on
the native normalized finite-mixture class.
-/

open Complex MeasureTheory Zeta23
noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided

/-- Logarithms of ratios of nonzero natural numbers are dense in the real line. -/
theorem dense_log_nat_ratios :
    Dense {y : ℝ | ∃ a b : ℕ, a ≠ 0 ∧ b ≠ 0 ∧ y = Real.log a - Real.log b} := by
  let S : AddSubgroup ℝ :=
    { carrier := {y | ∃ a b : ℕ, a ≠ 0 ∧ b ≠ 0 ∧ y = Real.log a - Real.log b}
      zero_mem' := ⟨1, 1, one_ne_zero, one_ne_zero, by simp⟩
      add_mem' := by
        rintro x y ⟨a, b, ha, hb, rfl⟩ ⟨c, d, hc, hd, rfl⟩
        refine ⟨a * c, b * d, mul_ne_zero ha hc, mul_ne_zero hb hd, ?_⟩
        rw [Nat.cast_mul, Nat.cast_mul,
          Real.log_mul (by exact_mod_cast ha) (by exact_mod_cast hc),
          Real.log_mul (by exact_mod_cast hb) (by exact_mod_cast hd)]
        ring
      neg_mem' := by
        rintro x ⟨a, b, ha, hb, rfl⟩
        exact ⟨b, a, hb, ha, by ring⟩ }
  have hlog (a : ℕ) (ha : a ≠ 0) : Real.log a ∈ S :=
    ⟨a, 1, ha, one_ne_zero, by simp⟩
  have hs : AddSubgroup.closure {Real.log (2 : ℕ), Real.log (3 : ℕ)} ≤ S := by
    apply (AddSubgroup.closure_le S).mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact hlog 2 (by omega)
    · have hx' := Set.mem_singleton_iff.mp hx
      rw [hx']
      exact hlog 3 (by omega)
  exact Dense.mono hs
    (dense_addSubgroup_log_primes Nat.prime_two Nat.prime_three (by omega))

/-- Rational-lag samples already determine the entire signed-mixture autocorrelation. -/
theorem mixtureSample_eq_of_log_nat_ratios (c d : WeilTestFn →₀ ℝ)
    (h : ∀ a b : ℕ, a ≠ 0 → b ≠ 0 →
      mixtureSample c (Real.log a - Real.log b) =
        mixtureSample d (Real.log a - Real.log b)) : mixtureSample c = mixtureSample d := by
  apply Continuous.ext_on dense_log_nat_ratios (admissible_mixtureSample c).cont
    (admissible_mixtureSample d).cont
  rintro y ⟨a, b, ha, hb, rfl⟩
  exact h a b ha hb

/-- The compact prime-torus pushforward is injective on actual native spectral laws. -/
theorem spectralTorusProbability_eq_iff_spectralProbability_eq (c d : NormalizedMixture) :
    spectralTorusProbability c = spectralTorusProbability d ↔
      spectralProbability c = spectralProbability d := by
  constructor
  · intro h
    apply (spectralProbability_eq_iff_mixtureSample_eq c d).mpr
    apply mixtureSample_eq_of_log_nat_ratios
    intro a b ha hb
    have hm := congrArg (fun μ : ProbabilityMeasure PrimePhaseSpace => phaseMoment μ a b) h
    rw [phaseMoment_spectralTorusProbability c ha hb,
      phaseMoment_spectralTorusProbability d ha hb] at hm
    exact hm
  · intro h
    exact congrArg (fun μ : ProbabilityMeasure ℝ =>
      μ.map continuous_primeSpectralPoint.measurable.aemeasurable) h

/-- The complete compact torus law determines full Weil energy. -/
theorem energy_eq_of_spectralTorusProbability_eq (c d : NormalizedMixture)
    (h : spectralTorusProbability c = spectralTorusProbability d) : energy c.1 = energy d.1 :=
  energy_eq_of_spectralProbability_eq c d
    ((spectralTorusProbability_eq_iff_spectralProbability_eq c d).mp h)

/-- Full energy is intrinsic to the origin-representing measure, independent of its mixture. -/
theorem energy_eq_of_spectralRepresentingMeasure_eq (c d : ComplexNullMixture)
    (h : spectralRepresentingMeasure c = spectralRepresentingMeasure d) :
    energy c.1.1 = energy d.1.1 :=
  energy_eq_of_spectralTorusProbability_eq c.1 d.1 (congrArg Subtype.val h)

end RHTower.WeilWorkPBAP
