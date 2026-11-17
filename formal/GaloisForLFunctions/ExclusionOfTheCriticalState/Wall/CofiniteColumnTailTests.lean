import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.PolynomialTailFilters
import GaloisForLFunctions.ArithmeticEffectivityTheory.Semigroups.ResidueColumns

/-!
# Cofinite exponent columns still detect both tail signs

The residue columns of the Kunz description omit finitely many monomials.
Multiplication by a sufficiently large power of `X` embeds every polynomial
test into the allowed columns. Its square is a strictly positive multiplier
on the exponential tail coordinate. Thus deleting these monomials loses no
density-sign information, even without additive closure of the columns.
-/

noncomputable section
open MeasureTheory Set
open _root_.Polynomial
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticEffectivityTheory.ResidueColumns
open ArithmeticHodgeTheoryOfDegenerations ArithmeticHarmonicAnalysis.Coleman
open BiScaleUncertainty.Observation

/-- A uniform monomial shift places every exponent above all column gaps. -/
theorem shiftedPolynomial_column_support (m : ℕ) (k : ℕ → ℕ) (P : ℝ[X]) :
    ∀ n ∈ (X ^ tailBound m k * P).support, n ∈ carrier m k := by
  intro n hn
  apply mem_of_tailBound_le
  by_contra h
  have hc := _root_.Polynomial.mem_support_iff.mp hn
  rw [coeff_X_pow_mul', if_neg h] at hc
  exact hc rfl

/-- Shifting the test is exactly the positive monomial filter of the tail density. -/
theorem tailProbeQuadratic_monomial_shift {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (T : ℝ) (C : ℕ) (P : ℝ[X]) :
    tailProbeQuadratic F T (X ^ C * P) =
      _root_.HTGeometry.momentFunctional (filteredTailMoment F T (X ^ (2 * C))) (P ^ 2) := by
  rw [tailProbeQuadratic_eq_integral hF, filteredTailMoment_square hF]
  apply integral_congr_ae
  filter_upwards [] with u
  simp only [eval_mul, eval_pow, eval_X]
  rw [Nat.mul_comm 2 C, pow_mul]
  ring

/-- Cofinite column tests characterize the full almost-everywhere density sign. -/
theorem column_tail_nonnegative_iff {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (T : ℝ) (m : ℕ) (k : ℕ → ℕ) :
    (∀ P : ℝ[X], (∀ n ∈ P.support, n ∈ carrier m k) → 0 ≤ tailProbeQuadratic F T P) ↔
      ∀ᵐ u ∂volume.restrict (Iio (-T)), 0 ≤ F u := by
  constructor
  · intro h
    have hs : ∀ P : ℝ[X], 0 ≤ _root_.HTGeometry.momentFunctional
        (filteredTailMoment F T (X ^ (2 * tailBound m k))) (P ^ 2) := by
      intro P
      rw [← tailProbeQuadratic_monomial_shift hF]
      exact h _ (shiftedPolynomial_column_support m k P)
    have hd := (filteredTailMoment_square_nonnegative_iff hF T _).mp hs
    filter_upwards [hd] with u hu
    simp only [eval_pow, eval_X] at hu
    exact (mul_nonneg_iff_of_pos_left (pow_pos (Real.exp_pos _) _)).mp hu
  · intro h P _
    rw [tailProbeQuadratic_eq_integral hF]
    apply integral_nonneg_of_ae
    filter_upwards [h] with u hu
    exact mul_nonneg (sq_nonneg _) (mul_nonneg hu (Real.exp_pos _).le)

/-- Every critical tail has square tests of both signs using only the allowed columns. -/
theorem criticalState_column_tail_both_signs {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F)
    (T : ℝ) (m : ℕ) (k : ℕ → ℕ) :
    (∃ P : ℝ[X], (∀ n ∈ P.support, n ∈ carrier m k) ∧ tailProbeQuadratic F T P < 0) ∧
      ∃ P : ℝ[X], (∀ n ∈ P.support, n ∈ carrier m k) ∧ 0 < tailProbeQuadratic F T P := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  obtain ⟨⟨P, hP⟩, ⟨Q, hQ⟩⟩ := criticalState_filteredTailMoment_both_signs hW ht hF T
    (q := X ^ (2 * tailBound m k)) (pow_ne_zero _ X_ne_zero)
  refine ⟨⟨X ^ tailBound m k * P, shiftedPolynomial_column_support m k P, ?_⟩,
    ⟨X ^ tailBound m k * Q, shiftedPolynomial_column_support m k Q, ?_⟩⟩
  · simpa only [tailProbeQuadratic_monomial_shift hd] using hP
  · simpa only [tailProbeQuadratic_monomial_shift hd] using hQ

/-- Unconditionally, RH holds or no cofinite residue-column restriction restores a tail sign. -/
theorem riemannHypothesis_or_indefinite_column_tail_tests :
    RiemannHypothesis ∨ ∃ (W₀ : ℝ) (F : ℝ → ℝ), 0 < W₀ ∧
      (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧ ∀ (T : ℝ) (m : ℕ) (k : ℕ → ℕ),
        (∃ P : ℝ[X], (∀ n ∈ P.support, n ∈ carrier m k) ∧ tailProbeQuadratic F T P < 0) ∧
          ∃ P : ℝ[X], (∀ n ∈ P.support, n ∈ carrier m k) ∧ 0 < tailProbeQuadratic F T P := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with hRH | ⟨W₀, F, hW, ht, hF⟩
  · exact Or.inl hRH
  · exact Or.inr ⟨W₀, F, hW, ht, hF, criticalState_column_tail_both_signs hW ht hF⟩

#print axioms column_tail_nonnegative_iff
#print axioms riemannHypothesis_or_indefinite_column_tail_tests

end GaloisForLFunctions.ExclusionOfTheCriticalState
