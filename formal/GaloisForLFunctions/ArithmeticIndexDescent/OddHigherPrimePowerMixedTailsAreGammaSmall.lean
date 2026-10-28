import GaloisForLFunctions.ArithmeticIndexDescent.AllHigherPrimePowerMixedTailsAreGammaSmall

/-!
# The disjoint odd higher-power mixed source

Only odd exponents at least three occur in this source. Its absolute Gamma
budget is bounded by the already summable budget for all higher powers.
Consequently the literal even-power source can be combined with these
mixed terms without counting any even exponent twice.
-/

noncomputable section
open MeasureTheory
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticIndexDescent
open ArithmeticCastelnuovoSeveri.LogCells BiarithmeticGaugeGeometry HTGeometry

/-- The original mixed prime-power term, retained precisely for odd exponents at least three. -/
def oddHigherPrimePowerMixedTerm (pk : Nat.Primes × ℕ) (d q : ℕ → ℝ) (X : ℕ) : ℝ :=
  if Odd (pk.2 + 3) then integerMixedSource (higherPrimePowerIndex pk) d q X X else 0

theorem oddHigherPrimePowerMixedTerm_even (pk : Nat.Primes × ℕ)
    (h : Even (pk.2 + 3)) (d q : ℕ → ℝ) (X : ℕ) :
    oddHigherPrimePowerMixedTerm pk d q X = 0 := by
  exact if_neg (Nat.not_odd_iff_even.mpr h)

/-- The full mixed source over odd exponents at least three and every prime. -/
def oddHigherPrimePowerMixedSource (d q : ℕ → ℝ) (X : ℕ) : ℝ :=
  ∑' pk : Nat.Primes × ℕ, oddHigherPrimePowerMixedTerm pk d q X

/-- The odd higher-power source is literally the sum of both original physical mixed correlations. -/
theorem oddHigherPrimePowerMixedSource_eq_integrals (d q : ℕ → ℝ) (X : ℕ) :
    oddHigherPrimePowerMixedSource d q X = ∑' pk : Nat.Primes × ℕ,
      if Odd (pk.2 + 3) then
        (2 * ArithmeticFunction.vonMangoldt (higherPrimePowerIndex pk) /
          Real.sqrt (higherPrimePowerIndex pk)) *
        ((∫ u, haarSectionProfile d X u *
          averageSectionProfile q X (u + Real.log (higherPrimePowerIndex pk))) +
          ∫ u, averageSectionProfile q X u *
            haarSectionProfile d X (u + Real.log (higherPrimePowerIndex pk))) else 0 := by
  unfold oddHigherPrimePowerMixedSource
  apply tsum_congr
  intro pk
  unfold oddHigherPrimePowerMixedTerm
  split_ifs
  · exact integerMixedSource_eq_integrals (higherPrimePowerIndex pk) d q X X
  · rfl

theorem summable_norm_oddHigherPrimePowerMixed (d q : ℕ → ℝ) (X : ℕ) :
    Summable (fun pk : Nat.Primes × ℕ => ‖oddHigherPrimePowerMixedTerm pk d q X‖) := by
  apply Summable.of_nonneg_of_le (fun pk => norm_nonneg _) (fun pk => ?_)
    (summable_norm_higherPrimePowerMixed d q X)
  unfold oddHigherPrimePowerMixedTerm
  split_ifs
  · exact le_rfl
  · simpa only [norm_zero] using norm_nonneg (integerMixedSource (higherPrimePowerIndex pk) d q X X)

theorem summable_oddHigherPrimePowerMixed (d q : ℕ → ℝ) (X : ℕ) :
    Summable (fun pk : Nat.Primes × ℕ => oddHigherPrimePowerMixedTerm pk d q X) :=
  (summable_norm_oddHigherPrimePowerMixed d q X).of_norm

/-- The odd source uses the original Gamma energy of the complete profile. -/
theorem abs_oddHigherPrimePowerMixed_tail_le_gamma (d q : ℕ → ℝ) {A : ℕ}
    (hA : 1 ≤ A) (X : ℕ) :
    |oddHigherPrimePowerMixedSource (fun a => if A ≤ a then d a else 0) q X| ≤
      higherPrimePowerGammaCost * (levyEnergy (completePairProfile q d X) / cellGammaWeight A) := by
  have hp (pk : Nat.Primes × ℕ) :
      |oddHigherPrimePowerMixedTerm pk (fun a => if A ≤ a then d a else 0) q X| ≤
        higherPrimePowerGammaWeight pk *
          (levyEnergy (completePairProfile q d X) / cellGammaWeight A) := by
    have h := abs_integerMixed_tail_le_gamma_div_weight d q hA (two_le_higherPrimePowerIndex pk) X
    rw [← higherPrimePowerGammaWeight_eq] at h
    unfold oddHigherPrimePowerMixedTerm
    split_ifs
    · exact h
    · rw [abs_zero]
      exact (abs_nonneg _).trans h
  have h := RHTower.abs_tsum_le_tsum_of_abs_le
    (summable_higherPrimePowerGammaWeight.mul_right
      (levyEnergy (completePairProfile q d X) / cellGammaWeight A)) hp
  rw [tsum_mul_right] at h
  exact h

/-- Finite-head subtraction is exactly the disjoint odd higher-power tail. -/
theorem oddHigherPrimePowerMixedSource_sub_head (d q : ℕ → ℝ) (A X : ℕ) :
    oddHigherPrimePowerMixedSource d q X -
      oddHigherPrimePowerMixedSource (fun a => if a < A then d a else 0) q X =
        oddHigherPrimePowerMixedSource (fun a => if A ≤ a then d a else 0) q X := by
  unfold oddHigherPrimePowerMixedSource
  rw [← (summable_oddHigherPrimePowerMixed d q X).tsum_sub
    (summable_oddHigherPrimePowerMixed (fun a => if a < A then d a else 0) q X)]
  apply tsum_congr
  intro pk
  unfold oddHigherPrimePowerMixedTerm
  split_ifs
  · exact integerMixedSource_sub_head (higherPrimePowerIndex pk) d q A X X
  · exact sub_self 0

/-- Any positive retained Gamma share pays the entire odd higher-power detail tail. -/
theorem exists_oddHigherPrimePower_gamma_small_tail {δ : ℝ} (hδ : 0 < δ) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ (d q : ℕ → ℝ) (X : ℕ),
      |oddHigherPrimePowerMixedSource (fun a => if A ≤ a then d a else 0) q X| ≤
        δ * levyEnergy (completePairProfile q d X) := by
  obtain ⟨A, hA⟩ := exists_nat_gt (Real.exp (higherPrimePowerGammaCost / δ))
  have hA1 : 1 ≤ A := by
    have hp : (0 : ℝ) < A := (Real.exp_pos _).trans hA
    exact Nat.one_le_iff_ne_zero.mpr (Nat.cast_ne_zero.mp hp.ne')
  have hlog : higherPrimePowerGammaCost / δ < Real.log (A : ℝ) := by
    have h := Real.log_lt_log (Real.exp_pos _) hA
    rwa [Real.log_exp] at h
  have hcoef : higherPrimePowerGammaCost / cellGammaWeight A ≤ δ := by
    apply (div_le_iff₀ (cellGammaWeight_pos hA1)).mpr
    calc
      _ ≤ δ * Real.log (A : ℝ) := by
        simpa only [mul_comm] using (div_le_iff₀ hδ).mp hlog.le
      _ ≤ _ := mul_le_mul_of_nonneg_left (log_le_cellGammaWeight hA1) hδ.le
  refine ⟨A, hA1, ?_⟩
  intro d q X
  have hE := levyEnergy_nonneg_bv (completePairProfile_bv q d X) (completePairProfile_compact q d X)
  calc
    _ ≤ _ := abs_oddHigherPrimePowerMixed_tail_le_gamma d q hA1 X
    _ = (higherPrimePowerGammaCost / cellGammaWeight A) * levyEnergy (completePairProfile q d X) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoef hE

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.oddHigherPrimePowerMixedTerm_even
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.oddHigherPrimePowerMixedSource_eq_integrals
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.summable_norm_oddHigherPrimePowerMixed
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.oddHigherPrimePowerMixedSource_sub_head
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.exists_oddHigherPrimePower_gamma_small_tail
