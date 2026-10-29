import GaloisForLFunctions.SignedArithmeticHodgeTheory.ActualGeneratorHeadsAndTailsHaveUniformGammaBounds
import GaloisForLFunctions.SignedArithmeticHodgeTheory.TheSquareSourceHeadErrorHasOnlyAGammaStabilityCost

/-!
# The complete even-power source has an original-Gamma approximation

Uniform Gamma stability of the actual stopping averages pays the projected
energies in the signed square-source estimate. One generator cutoff then
controls the entire even-prime-power error for every finite real cell source.
Every translation orbit of the retained generators remains present.
-/

noncomputable section
open MeasureTheory Set RHTower

namespace GaloisForLFunctions.SignedArithmeticHodgeTheory
open HTGeometry ArithmeticCastelnuovoSeveri.LogCells ArithmeticIndexDescent

/-- Signed compensation and uniform head stability pay every even prime power with original Gamma. -/
theorem exists_actualGenerator_even_originalGamma_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (A : ℕ+) (κ : Type) [Fintype κ] (n : κ → ℕ+) (c : κ → ℝ),
      |squarePrimeSource (finiteLogCellProfile n c) -
        squarePrimeSource (actualGeneratorHeadProfile A n c)| ≤
          (ε + C / (1 + Real.log (A : ℝ))) * levyEnergy (finiteLogCellProfile n c) := by
  obtain ⟨C, hC, hb⟩ := exists_actualGenerator_square_head_bound
    (div_pos hε generatorGammaStabilityConstant_pos)
  refine ⟨32 * C, mul_nonneg (by norm_num) hC, ?_⟩
  intro A κ _ n c
  have hh := mul_le_mul_of_nonneg_left (actualGeneratorHead_tail_gamma_le A n c)
    (div_pos hε generatorGammaStabilityConstant_pos).le
  calc
    _ ≤ (ε / generatorGammaStabilityConstant) *
        (levyEnergy (actualGeneratorHeadProfile A n c) + levyEnergy (actualGeneratorTailProfile A n c)) +
          C * (32 * levyEnergy (finiteLogCellProfile n c) / (1 + Real.log (A : ℝ))) := hb A κ n c
    _ ≤ (ε / generatorGammaStabilityConstant) *
        (generatorGammaStabilityConstant * levyEnergy (finiteLogCellProfile n c)) +
          C * (32 * levyEnergy (finiteLogCellProfile n c) / (1 + Real.log (A : ℝ))) :=
      add_le_add_right hh _
    _ = _ := by
      rw [← mul_assoc, div_mul_cancel₀ _ generatorGammaStabilityConstant_pos.ne']
      ring

/-- One cutoff, and every larger cutoff, makes the complete even-power error uniformly Gamma-small. -/
theorem exists_allEvenPrimePowers_generator_approximation {δ : ℝ} (hδ : 0 < δ) :
    ∃ A₀ : ℕ+, ∀ A : ℕ+, A₀ ≤ A →
      ∀ (κ : Type) [Fintype κ] (n : κ → ℕ+) (c : κ → ℝ),
        |squarePrimeSource (finiteLogCellProfile n c) -
          squarePrimeSource (actualGeneratorHeadProfile A n c)| ≤
            δ * levyEnergy (finiteLogCellProfile n c) := by
  obtain ⟨C, hC, hb⟩ := exists_actualGenerator_even_originalGamma_bound (half_pos hδ)
  obtain ⟨a, ha⟩ := exists_nat_gt (Real.exp (C / (δ / 2)))
  have ha0 : 0 < a := by
    exact_mod_cast (Real.exp_pos _).trans ha
  let A₀ : ℕ+ := ⟨a, ha0⟩
  refine ⟨A₀, ?_⟩
  intro A hA κ _ n c
  have haA : (a : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hlog : C / (δ / 2) < Real.log (A : ℝ) := by
    have h := Real.log_lt_log (Real.exp_pos _) (ha.trans_le haA)
    rwa [Real.log_exp] at h
  have hden : 0 < 1 + Real.log (A : ℝ) := by
    have h := Real.log_nonneg (by exact_mod_cast A.pos : (1 : ℝ) ≤ A)
    linarith only [h]
  have hcoef : C / (1 + Real.log (A : ℝ)) ≤ δ / 2 := by
    apply (div_le_iff₀ hden).mpr
    have h := (div_le_iff₀ (half_pos hδ)).mp hlog.le
    nlinarith only [h, hδ]
  have hΓ := levyEnergy_nonneg_bv (finiteLogCellProfile_bv n c) (finiteLogCellProfile_compact n c)
  exact (hb A κ n c).trans (mul_le_mul_of_nonneg_right (by linarith only [hcoef]) hΓ)

end GaloisForLFunctions.SignedArithmeticHodgeTheory

#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.exists_actualGenerator_even_originalGamma_bound
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.exists_allEvenPrimePowers_generator_approximation
