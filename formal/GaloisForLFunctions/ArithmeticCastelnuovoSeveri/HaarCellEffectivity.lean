import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.HaarCellGammaPayment
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.HaarCellPoleBound
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.HaarCellPrimeBound

/-!
# Positive original Weil energy on high-index balanced sections

The Gamma coefficient one exceeds the full-prime coefficient `1 / sqrt 2`.
The mass and pole terms have fixed costs. A single lower arithmetic index
therefore gives a positive floor for every finite signed balanced section,
independently of its upper support horizon.
-/

noncomputable section
open MeasureTheory Set
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells

private theorem log_odd_le_log_add_two {a : ℕ} (ha : 1 ≤ a) :
    Real.log ((2 * a + 1 : ℕ) : ℝ) ≤ Real.log (a : ℝ) + 2 := by
  have ha0 : (0 : ℝ) < a := Nat.cast_pos.mpr (by omega)
  have ho : (0 : ℝ) < ((2 * a + 1 : ℕ) : ℝ) := by positivity
  have h := Real.log_le_sub_one_of_pos (div_pos ho ha0)
  rw [Real.log_div ho.ne' ha0.ne'] at h
  have hd : ((2 * a + 1 : ℕ) : ℝ) / (a : ℝ) ≤ 3 := by
    rw [div_le_iff₀ ha0]
    exact_mod_cast (show 2 * a + 1 ≤ 3 * a by omega)
  linarith only [h, hd]

private theorem haarPrimeEnergy_le_log (c : ℕ → ℝ) (X : ℕ) :
    haarPrimeEnergy c X ≤ ∑ a ∈ Finset.Icc 1 X,
      (18 + Real.log (a : ℝ) / Real.sqrt 2) * haarMass a * c a ^ 2 := by
  apply (haarPrimeEnergy_le c X).trans
  apply Finset.sum_le_sum
  intro a ha
  have ha1 := (Finset.mem_Icc.mp ha).1
  have hd := div_le_div_of_nonneg_right (log_odd_le_log_add_two ha1) (Real.sqrt_nonneg 2)
  rw [add_div] at hd
  have hcoeff : 16 + Real.log ((2 * a + 1 : ℕ) : ℝ) / Real.sqrt 2 ≤
      18 + Real.log (a : ℝ) / Real.sqrt 2 := by
    have hsmall := haarPrime_log_coefficient_lt_one.le
    have htwo : (2 : ℝ) / Real.sqrt 2 ≤ 2 := by
      calc
        _ = 2 * (1 / Real.sqrt 2) := by ring
        _ ≤ 2 * 1 := mul_le_mul_of_nonneg_left hsmall (by norm_num)
        _ = 2 := by ring
    linarith only [hd, htwo]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcoeff (haarMass_pos ha1).le) (sq_nonneg _)

/-- The actual full Weil form has a growing arithmetic floor on balanced complete cells. -/
theorem haarSectionProfile_roughWeil_ge (c : ℕ → ℝ) (X : ℕ) :
    (∑ a ∈ Finset.Icc 1 X,
      ((1 - 1 / Real.sqrt 2) * Real.log (a : ℝ) + 2 * gammaHardyPhaseRate 0 - 20) *
        haarMass a * c a ^ 2) ≤ roughWeil (haarSectionProfile c X) := by
  have hgamma := haarSectionProfile_levyEnergy_ge c X
  have hprime := haarPrimeEnergy_le_log c X
  rw [haarPrimeEnergy_eq_primeSum] at hprime
  have hpole := haarSectionProfile_pole_ge c X
  have he (a : ℕ) :
      ((1 - 1 / Real.sqrt 2) * Real.log (a : ℝ) + 2 * gammaHardyPhaseRate 0 - 20) *
        haarMass a * c a ^ 2 =
      2 * gammaHardyPhaseRate 0 * (haarMass a * c a ^ 2) +
        Real.log (a : ℝ) * haarMass a * c a ^ 2 -
        (18 + Real.log (a : ℝ) / Real.sqrt 2) * haarMass a * c a ^ 2 -
        2 * (haarMass a * c a ^ 2) := by ring
  simp_rw [he, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  unfold roughWeil
  rw [integral_haarSectionProfile_sq]
  linarith only [hgamma, hprime, hpole]

/-- Coefficients of the complete pairs above a fixed arithmetic lower index. -/
def haarTailCoeffs (A : ℕ) (c : ℕ → ℝ) (a : ℕ) : ℝ := if A ≤ a then c a else 0

/-- One fixed lower index makes every finite signed balanced section uniformly positive. -/
theorem exists_haarTail_roughWeil_floor : ∃ A : ℕ, 1 ≤ A ∧ ∀ (c : ℕ → ℝ) (X : ℕ),
    (∑ a ∈ Finset.Icc 1 X, haarMass a * haarTailCoeffs A c a ^ 2) ≤
      roughWeil (haarSectionProfile (haarTailCoeffs A c) X) := by
  let κ : ℝ := 1 - 1 / Real.sqrt 2
  have hκ : 0 < κ := sub_pos.mpr haarPrime_log_coefficient_lt_one
  let T : ℝ := (21 - 2 * gammaHardyPhaseRate 0) / κ
  obtain ⟨A, hA⟩ := exists_nat_gt (Real.exp T)
  have hA1 : 1 ≤ A := by
    have hpos : (0 : ℝ) < A := (Real.exp_pos T).trans hA
    exact Nat.one_le_iff_ne_zero.mpr (Nat.cast_ne_zero.mp hpos.ne')
  have hcoeff (a : ℕ) (ha : A ≤ a) :
      1 ≤ κ * Real.log (a : ℝ) + 2 * gammaHardyPhaseRate 0 - 20 := by
    have haR : (A : ℝ) ≤ a := by exact_mod_cast ha
    have hlog : T < Real.log (a : ℝ) := by
      have := Real.log_lt_log (Real.exp_pos T) (hA.trans_le haR)
      simpa only [Real.log_exp] using this
    have hmul := mul_le_mul_of_nonneg_left hlog.le hκ.le
    have he : κ * T = 21 - 2 * gammaHardyPhaseRate 0 := by
      dsimp only [T]
      field_simp [hκ.ne']
    linarith only [hmul, he]
  refine ⟨A, hA1, fun c X => ?_⟩
  apply le_trans ?_ (haarSectionProfile_roughWeil_ge (haarTailCoeffs A c) X)
  apply Finset.sum_le_sum
  intro a ha
  by_cases hAa : A ≤ a
  · have hnonneg : 0 ≤ haarMass a * haarTailCoeffs A c a ^ 2 :=
      mul_nonneg (haarMass_pos (Finset.mem_Icc.mp ha).1).le (sq_nonneg _)
    simpa only [κ, one_mul, mul_assoc] using mul_le_mul_of_nonneg_right (hcoeff a hAa) hnonneg
  · simp only [haarTailCoeffs, if_neg hAa, zero_pow (by norm_num : 2 ≠ 0), mul_zero, le_refl]

#print axioms haarSectionProfile_roughWeil_ge
#print axioms exists_haarTail_roughWeil_floor

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
