import GaloisForLFunctions.SignedArithmeticHodgeTheory.BalancedCellDetailsFormTheWanderingBasis
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.HaarCellPrimeCompression

/-!
# Literal physical normalization of arithmetic dyadic details

The unit coefficient-space detail embeds as the existing balanced Haar source
divided by its square-root mass. The exact equality survives every dyadic
level and every integer logarithmic translation. It permits source estimates
to use the same profiles and normalization on both sides.
-/

noncomputable section

open RHTower GaloisForLFunctions.BiarithmeticGaugeGeometry
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells

namespace GaloisForLFunctions.SignedArithmeticHodgeTheory

local notation "CellH" => lp (fun _ : ℕ+ => ℂ) 2

private theorem sqrt_pair_mass_mul_weight {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    Real.sqrt (u * v / (u + v)) * Real.sqrt (v / (u + v)) =
      (v / (u + v)) * Real.sqrt u := by
  have hsum := (add_pos hu hv).le
  have hm := div_nonneg (mul_nonneg hu.le hv.le) hsum
  have hr := div_nonneg hv.le hsum
  have he : (Real.sqrt (u * v / (u + v)) * Real.sqrt (v / (u + v))) ^ 2 =
      ((v / (u + v)) * Real.sqrt u) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hm, Real.sq_sqrt hr, mul_pow, Real.sq_sqrt hu.le]
    ring
  exact (sq_eq_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    (mul_nonneg hr (Real.sqrt_nonneg _))).mp he

private theorem parent_width (a : ℕ+) :
    logCellWidth (2 * (a : ℕ)) + logCellWidth (2 * (a : ℕ) + 1) = logCellWidth a := by
  change logCell (2 * (a : ℕ)) + logCell (2 * (a : ℕ) + 1) = logCell a
  simpa only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, Nat.add_zero, mul_comm] using
    sum_logCell_block (p := 2) (n := (a : ℕ)) (by norm_num) a.pos

/-- The coefficient basis embeds as the original complete physical cell. -/
theorem logCellEmbedding_weighted_single (a : ℕ+) :
    logCellEmbedding ((Real.sqrt (logCell a) : ℂ) •
      (lp.single 2 a (1 : ℂ) : CellH)) = cellAtom a := by
  rw [map_smul, logCellEmbedding_single, cellAtom, dif_pos a.pos]
  rfl

/-- Unit dyadic details are precisely the existing physical balanced Haar atoms
with their square-root mass normalization. -/
theorem sqrt_haarMass_smul_logCellEmbedding_detail (a : ℕ+) :
    (Real.sqrt (haarMass a) : ℂ) • logCellEmbedding (logCellDyadicDetail a) = haarAtom a := by
  have ha : 1 ≤ (a : ℕ) := a.pos
  have hl := logCellWidth_pos (show 1 ≤ 2 * (a : ℕ) by omega)
  have hr := logCellWidth_pos (show 1 ≤ 2 * (a : ℕ) + 1 by omega)
  have hleft : Real.sqrt (haarMass a) * dyadicRightWeight a =
      haarLeftCoeff a * Real.sqrt (logCellWidth (2 * (a : ℕ))) := by
    rw [haarMass, dyadicRightWeight, haarLeftCoeff]
    change Real.sqrt (logCellWidth (2 * (a : ℕ)) * logCellWidth (2 * (a : ℕ) + 1) /
        (logCellWidth (2 * (a : ℕ)) + logCellWidth (2 * (a : ℕ) + 1))) *
      Real.sqrt (logCellWidth (2 * (a : ℕ) + 1) / logCellWidth a) = _
    rw [← parent_width a]
    exact sqrt_pair_mass_mul_weight hl hr
  have hright : Real.sqrt (haarMass a) * dyadicLeftWeight a =
      haarRightCoeff a * Real.sqrt (logCellWidth (2 * (a : ℕ) + 1)) := by
    rw [haarMass, dyadicLeftWeight, haarRightCoeff]
    change Real.sqrt (logCellWidth (2 * (a : ℕ)) * logCellWidth (2 * (a : ℕ) + 1) /
        (logCellWidth (2 * (a : ℕ)) + logCellWidth (2 * (a : ℕ) + 1))) *
      Real.sqrt (logCellWidth (2 * (a : ℕ)) / logCellWidth a) = _
    rw [← parent_width a]
    simpa only [mul_comm (logCellWidth (2 * (a : ℕ) + 1)) (logCellWidth (2 * (a : ℕ))),
      add_comm (logCellWidth (2 * (a : ℕ) + 1)) (logCellWidth (2 * (a : ℕ)))] using
      sqrt_pair_mass_mul_weight hr hl
  simp only [logCellDyadicDetail, map_sub, map_smul, logCellEmbedding_single,
    smul_sub, smul_smul, ← Complex.ofReal_mul, hleft, hright, haarAtom, cellAtom,
    dif_pos (show 0 < 2 * (a : ℕ) by omega),
    dif_pos (show 0 < 2 * (a : ℕ) + 1 by omega),
    Nat.toPNat, dyadicLeftCell, dyadicRightCell]

/-- The physical normalization commutes with every dyadic level. -/
theorem sqrt_haarMass_smul_logCellEmbedding_detail_pow (a : ℕ+) (j : ℕ) :
    (Real.sqrt (haarMass a) : ℂ) •
        logCellEmbedding ((logCellShift 2 ^ j) (logCellDyadicDetail a)) =
      ((halfLineRightShift (Real.log 2)) ^ j) (haarAtom a) := by
  rw [logCellEmbedding_dyadic_pow, ← map_smul, sqrt_haarMass_smul_logCellEmbedding_detail]

/-- Every integer arithmetic translation uses the same physical Haar source. -/
theorem sqrt_haarMass_smul_logCellEmbedding_detail_shift (a : ℕ+) {p : ℕ} (hp : 2 ≤ p) :
    (Real.sqrt (haarMass a) : ℂ) •
        logCellEmbedding (logCellShift p (logCellDyadicDetail a)) =
      halfLineRightShift (Real.log p) (haarAtom a) := by
  have h := congrArg (fun T => T (logCellDyadicDetail a))
    (halfLineRightShift_comp_logCellEmbedding hp)
  change halfLineRightShift (Real.log p) (logCellEmbedding (logCellDyadicDetail a)) =
    logCellEmbedding (logCellShift p (logCellDyadicDetail a)) at h
  rw [← h, ← map_smul, sqrt_haarMass_smul_logCellEmbedding_detail]

end GaloisForLFunctions.SignedArithmeticHodgeTheory

#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.logCellEmbedding_weighted_single
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.sqrt_haarMass_smul_logCellEmbedding_detail
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.sqrt_haarMass_smul_logCellEmbedding_detail_pow
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.sqrt_haarMass_smul_logCellEmbedding_detail_shift
