import GaloisForLFunctions.ArithmeticCountingPositivity.PrimeParityPairing
import GaloisForLFunctions.RHTower.WeilConeUniquenessUnconditional

/-!
# Near-maximal prime gaps do not force complete Weil positivity

Single-prime parity twists have positive harmonic counts, completely
multiplicative signs, the untwisted polar matching coefficient, and prime
gaps arbitrarily close to `2 log 2`. Their actual weights differ from von
Mangoldt at the flipped prime, so full-cone uniqueness rules out complete
Weil positivity. The obstruction retains the positive parity count and its
quantitative gap payment.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.ArithmeticCountingPositivity

open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
  GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity

open _root_.RHTower _root_.RHTower.WeilSpectral _root_.Zeta23

/-- The literal arithmetic source obtained by flipping one prime. -/
def primeFlipWeight (p n : ℕ) : ℝ := finiteFlip {p} n * ArithmeticFunction.vonMangoldt n

theorem abs_primeFlipWeight (p n : ℕ) :
    |primeFlipWeight p n| = ArithmeticFunction.vonMangoldt n := by
  rw [primeFlipWeight, abs_mul,
    abs_eq_one_of_mul_self_eq_one (singleFlip_mul_self p n),
    abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, one_mul]

/-- Each prime flip fails full Weil positivity despite retaining its positive prime gap. -/
theorem primeFlip_not_weilPositiveFull {p : ℕ} (hp : p.Prime) :
    ¬ WeilPositiveFull (primeFlipWeight p) := by
  intro hW
  have h := eq_vonMangoldt_of_weilPositiveFull hW p hp.two_le
  have hflip : finiteFlip {p} p = -1 := by
    simp only [finiteFlip, prod_singleton, hp.factorization_self, pow_one]
  rw [primeFlipWeight, hflip, neg_one_mul, ArithmeticFunction.vonMangoldt_apply_prime hp] at h
  have hlog : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  linarith only [h, hlog]

/-- The failure has a compactly supported `C²` test in the literal complete
functional, retaining Gamma and both poles. -/
theorem primeFlip_exists_negative_complete_test {p : ℕ} (hp : p.Prime) :
    ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ HasCompactSupport f ∧
      (weilFullFunctional (primeFlipWeight p) (EF.weilTest f f)).re < 0 := by
  have h := primeFlip_not_weilPositiveFull hp
  unfold WeilPositiveFull at h
  push Not at h
  exact h

/-- Every prime supplies an explicit counting-paid gap and a complete-source failure. -/
theorem prime_parity_gap_and_complete_source_failure {p : ℕ} (hp : p.Prime) :
    HasHyperplaneGap (finiteFlip {p})
        (2 * Real.log 2 * (((p : ℝ) - 1) / ((p : ℝ) + 1)) ^ 2) ∧
      ¬ WeilPositiveFull (primeFlipWeight p) :=
  ⟨primeFlip_hasHyperplaneGap hp, primeFlip_not_weilPositiveFull hp⟩

/-- No submaximal gap threshold, even together with multiplicativity and matching,
forces the complete Weil sign. All source coefficients retain their exact majorant. -/
theorem near_maximal_gaps_do_not_force_weil_positivity {a : ℝ} (ha : a < 2 * Real.log 2) :
    ∃ p : ℕ, p.Prime ∧ IsSignGauge (finiteFlip {p}) ∧
      HasHyperplaneGap (finiteFlip {p}) a ∧
      (∀ n : ℕ, |primeFlipWeight p n| = ArithmeticFunction.vonMangoldt n) ∧
      (∀ y : ℕ, 1 ≤ y →
        |gaugeMertensSum (finiteFlip {p}) y - Real.log y| ≤
          Real.log 4 + 4 + 2 * Real.log p / ((p : ℝ) - 1)) ∧
      ¬ WeilPositiveFull (primeFlipWeight p) := by
  obtain ⟨p, hp, _, _, hsign, hgap, hmatching⟩ :=
    every_submaximal_gap_has_a_nontrivial_multiplicative_twin ha
  exact ⟨p, hp, hsign, hgap, abs_primeFlipWeight p, hmatching,
    primeFlip_not_weilPositiveFull hp⟩

end GaloisForLFunctions.ArithmeticCountingPositivity
