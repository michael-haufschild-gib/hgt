import GaloisForLFunctions.RHTower.PrimeGammaCofinalBocksteinCStarShilovBlindness
import GaloisForLFunctions.RHTower.DiagonalEllTwoOperator
import GaloisForLFunctions.RHTower.EulerActivationSquarefreeProbability
import GaloisForLFunctions.HTGeometry.DiagonalCompactOperator
import GaloisForLFunctions.HTGeometry.HilbertSchmidtMatrix

open Filter Topology

namespace RHTower

noncomputable section

/-- Prime-enumerated complex diagonal multiplier of the cofinal Gamma Bockstein. -/
def primeGammaCofinalBocksteinDiagonalMultiplier (t : ℝ) (n : ℕ) : ℂ :=
  primeGammaCofinalBocksteinCoefficient t (natEquivPrimes n)

theorem norm_primeGammaCofinalBocksteinDiagonalMultiplier_le_one
    {t : ℝ} (ht : |t| < 1) (n : ℕ) :
    ‖primeGammaCofinalBocksteinDiagonalMultiplier t n‖ ≤ 1 := by
  let p : Nat.Primes := natEquivPrimes n
  have hmag := (primeGammaCofinalBocksteinMagnitude_bounds t p).2
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.2.one_lt.le
  have hexp : |t| - 1 ≤ 0 := by linarith
  have hpow : (p : ℝ) ^ (|t| - 1) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hp1 hexp
  rw [primeGammaCofinalBocksteinDiagonalMultiplier,
    Complex.norm_real, Real.norm_eq_abs]
  exact hmag.trans hpow

/-- Bounded operator on the prime-enumerated `ℓ²` skeleton carrying the literal Gamma defect. -/
def primeGammaCofinalBocksteinDiagonalOperator
    (t : ℝ) (ht : |t| < 1) : EllTwo →L[ℂ] EllTwo :=
  diagonalOperator (primeGammaCofinalBocksteinDiagonalMultiplier t)
    (norm_primeGammaCofinalBocksteinDiagonalMultiplier_le_one ht)

theorem tendsto_norm_primeGammaCofinalBocksteinDiagonalMultiplier_zero
    {t : ℝ} (ht : |t| < 1) :
    Tendsto (fun n => ‖primeGammaCofinalBocksteinDiagonalMultiplier t n‖)
      atTop (𝓝 0) := by
  have hmag : Tendsto
      (fun n : ℕ => primeGammaCofinalBocksteinMagnitude t (natEquivPrimes n))
      atTop (𝓝 0) := by
    rw [← Nat.cofinite_eq_atTop]
    exact (primeGammaCofinalBocksteinMagnitude_tendsto_cofinite_zero ht).comp
      natEquivPrimes.injective.tendsto_cofinite
  exact hmag.congr' (Eventually.of_forall fun n => by
    simp only [primeGammaCofinalBocksteinDiagonalMultiplier,
      Complex.norm_real, Real.norm_eq_abs]
    rfl)

/-- Clause (1): the literal cofinal Gamma diagonal is compact throughout `|t| < 1`. -/
theorem isCompactOperator_primeGammaCofinalBocksteinDiagonalOperator
    {t : ℝ} (ht : |t| < 1) :
    IsCompactOperator (primeGammaCofinalBocksteinDiagonalOperator t ht) := by
  refine GaloisForLFunctions.HTGeometry.isCompactOperator_of_diag_tendsto_cofinite
    (c := primeGammaCofinalBocksteinDiagonalMultiplier t)
    (T := primeGammaCofinalBocksteinDiagonalOperator t ht)
    (HilbertSchmidt.lpBasis ℕ) ?_ ?_
  · intro i
    rw [HilbertSchmidt.lpBasis_apply]
    refine lp.ext (funext fun n => ?_)
    by_cases h : n = i
    · subst h
      simp [primeGammaCofinalBocksteinDiagonalOperator,
        lp.single_apply]
    · simp [primeGammaCofinalBocksteinDiagonalOperator,
        lp.single_apply, h]
  · rw [Nat.cofinite_eq_atTop]
    exact tendsto_norm_primeGammaCofinalBocksteinDiagonalMultiplier_zero ht

end
end RHTower
