import GaloisForLFunctions.SignedSuccessorArithmetic.SquareRootCancellationIsACount
import GaloisForLFunctions.RHTower.Deninger.DeningerQ8ActualGlobalArtinEpsilon

/-!
# Quartic Gauss phases from successor correlations

For the actual quartic residue characters at five and forty-one, the fourth
power of the Gauss sum is the field size times the square of the successor
correlation. The latter has squared norm equal to the field size. Thus these
finite successor statistics retain phase information lost by a norm estimate.
-/

noncomputable section

open RHTower

namespace GaloisForLFunctions.SignedSuccessorArithmetic

local instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
local instance : Fact (Nat.Prime 41) := ⟨by norm_num⟩

private theorem quartic_fourth_from_successor {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (h4 : χ ^ 4 = 1) (h2 : χ ^ 2 ≠ 1)
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) :
    gaussSum χ ψ ^ 4 = (Fintype.card F : ℂ) * charSuccCorr χ χ ^ 2 := by
  have hprod : χ * χ ≠ 1 := by rwa [← pow_two]
  have hJ : gaussSum (χ ^ 2) ψ * jacobiSum χ χ = gaussSum χ ψ ^ 2 := by
    simpa only [pow_two] using jacobiSum_mul_nontrivial hprod ψ
  have hquad : (χ ^ 2).IsQuadratic := MulChar.isQuadratic_iff_sq_eq_one.mpr (by
    rw [← pow_mul]
    exact h4)
  have hs := gaussSum_sq h2 hquad hψ
  rw [MulChar.pow_apply' _ (by norm_num), ← map_pow, neg_one_sq, map_one, one_mul] at hs
  rw [charSuccCorr_eq_jacobiSum, mul_pow, pow_two (χ (-1)), mulChar_neg_one_mul_self, one_mul]
  calc
    gaussSum χ ψ ^ 4 = (gaussSum χ ψ ^ 2) ^ 2 := by ring
    _ = (gaussSum (χ ^ 2) ψ * jacobiSum χ χ) ^ 2 := by rw [hJ]
    _ = _ := by rw [mul_pow, hs]

/-- At five, the quartic Gauss fourth power is determined by the successor correlation. -/
theorem five_quartic_gauss_fourth :
    gaussSum deningerQ8FiveResidueQuarticChar ZMod.stdAddChar ^ 4 =
      5 * charSuccCorr deningerQ8FiveResidueQuarticChar deningerQ8FiveResidueQuarticChar ^ 2 := by
  simpa only [ZMod.card, Nat.cast_ofNat] using quartic_fourth_from_successor deningerQ8FiveResidueQuarticChar
    deningerQ8FiveResidueQuarticChar_fourth_eq_one
    deningerQ8FiveResidueQuarticChar_sq_ne_one ZMod.stdAddChar (ZMod.isPrimitive_stdAddChar 5)

/-- Exact square-root cancellation of the quartic successor correlation at five. -/
theorem five_quartic_successor_norm_sq :
    ‖charSuccCorr deningerQ8FiveResidueQuarticChar deningerQ8FiveResidueQuarticChar‖ ^ 2 = 5 := by
  simpa only [ZMod.card, Nat.cast_ofNat] using norm_sq_charSuccCorr
    deningerQ8FiveResidueQuarticChar_ne_one deningerQ8FiveResidueQuarticChar_ne_one
    (show deningerQ8FiveResidueQuarticChar * deningerQ8FiveResidueQuarticChar ≠ 1 by
      rw [← pow_two]; exact deningerQ8FiveResidueQuarticChar_sq_ne_one)

private theorem fortyOne_fourth : deningerQ8FortyOneResidueQuarticChar ^ 4 = 1 := by
  rw [← deningerQ8FortyOneResidueQuarticChar_orderOf]
  exact pow_orderOf_eq_one _

private theorem fortyOne_square_ne_one : deningerQ8FortyOneResidueQuarticChar ^ 2 ≠ 1 := by
  intro h
  have hd := orderOf_dvd_of_pow_eq_one h
  rw [deningerQ8FortyOneResidueQuarticChar_orderOf] at hd
  norm_num at hd

private theorem fortyOne_ne_one : deningerQ8FortyOneResidueQuarticChar ≠ 1 := by
  intro h
  apply fortyOne_square_ne_one
  rw [h, one_pow]

/-- At forty-one, the same phase law uses the actual Q8 residue source. -/
theorem fortyOne_quartic_gauss_fourth :
    gaussSum deningerQ8FortyOneResidueQuarticChar ZMod.stdAddChar ^ 4 =
      41 * charSuccCorr deningerQ8FortyOneResidueQuarticChar deningerQ8FortyOneResidueQuarticChar ^ 2 := by
  simpa only [ZMod.card, Nat.cast_ofNat] using quartic_fourth_from_successor deningerQ8FortyOneResidueQuarticChar
    fortyOne_fourth fortyOne_square_ne_one ZMod.stdAddChar (ZMod.isPrimitive_stdAddChar 41)

/-- Exact square-root cancellation of the quartic successor correlation at forty-one. -/
theorem fortyOne_quartic_successor_norm_sq :
    ‖charSuccCorr deningerQ8FortyOneResidueQuarticChar deningerQ8FortyOneResidueQuarticChar‖ ^ 2 = 41 := by
  simpa only [ZMod.card, Nat.cast_ofNat] using norm_sq_charSuccCorr fortyOne_ne_one fortyOne_ne_one
    (show deningerQ8FortyOneResidueQuarticChar * deningerQ8FortyOneResidueQuarticChar ≠ 1 by
      rw [← pow_two]; exact fortyOne_square_ne_one)

end GaloisForLFunctions.SignedSuccessorArithmetic
