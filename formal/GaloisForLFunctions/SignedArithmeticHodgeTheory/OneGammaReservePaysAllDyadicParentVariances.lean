import GaloisForLFunctions.SignedArithmeticHodgeTheory.TheSiblingGammaChargePaysItsParentVariance
import GaloisForLFunctions.HTGeometry.DyadicSiblingPartition
import GaloisForLFunctions.RHTower.LogFloorExpBridge

/-!
# One Gamma allocation for every dyadic parent

Nested logarithmic parent intervals have disjoint ordered sibling rectangles.
Their integer floor labels determine the unique binary split, so summing the
local parent-variance charges uses each source pair at most once. The resulting
finite-family bound retains arbitrary means and all dyadic levels.
-/

noncomputable section

open MeasureTheory Set Filter RHTower
open scoped ENNReal

namespace GaloisForLFunctions.SignedArithmeticHodgeTheory

open HTGeometry ArithmeticCastelnuovoSeveri.IntervalVariance
open ArithmeticCastelnuovoSeveri.MeanZeroIntervals ArithmeticCastelnuovoSeveri.LogCells

/-- The actual ordered sibling rectangle at a common translation and dyadic level. -/
def logCellSiblingRectangle (t : ℝ) (i : ℕ × ℕ+) : Set (ℝ × ℝ) :=
  Ioo (logCellSiblingLeft (t + i.1 * Real.log 2) i.2)
      (logCellSiblingMiddle (t + i.1 * Real.log 2) i.2) ×ˢ
    Ioo (logCellSiblingMiddle (t + i.1 * Real.log 2) i.2)
      (logCellSiblingRight (t + i.1 * Real.log 2) i.2)

private theorem log_dyadic_endpoint (t : ℝ) (j n : ℕ) (hn : 0 < n) :
    t + j * Real.log 2 + Real.log (n : ℝ) = t + Real.log ((n * 2 ^ j : ℕ) : ℝ) := by
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
    Real.log_mul (by exact_mod_cast (Nat.ne_of_gt hn) : (n : ℝ) ≠ 0) (by positivity),
    Real.log_pow]
  ring

private theorem floor_block {j q : ℕ} (hq : 0 < q) {z : ℝ}
    (hl : Real.log ((q * 2 ^ j : ℕ) : ℝ) < z)
    (hr : z < Real.log (((q + 1) * 2 ^ j : ℕ) : ℝ)) :
    ⌊Real.exp z⌋₊ / 2 ^ j = q := by
  have hpow : 0 < 2 ^ j := pow_pos (by norm_num) _
  have hlo : q * 2 ^ j ≤ ⌊Real.exp z⌋₊ :=
    (log_le_iff_le_floor (Nat.mul_pos hq hpow) z).mp hl.le
  have hhi : ⌊Real.exp z⌋₊ < (q + 1) * 2 ^ j := by
    by_contra h
    exact (not_le_of_gt hr)
      ((log_le_iff_le_floor (Nat.mul_pos (by omega) hpow) z).mpr (by omega))
  have hlq : q ≤ ⌊Real.exp z⌋₊ / 2 ^ j := (Nat.le_div_iff_mul_le hpow).mpr hlo
  have hrq : ⌊Real.exp z⌋₊ / 2 ^ j < q + 1 := (Nat.div_lt_iff_lt_mul hpow).mpr hhi
  omega

private theorem rectangle_floor_labels {t : ℝ} {i : ℕ × ℕ+} {p : ℝ × ℝ}
    (hp : p ∈ logCellSiblingRectangle t i) :
    ⌊Real.exp (p.1 - t)⌋₊ / 2 ^ i.1 = 2 * (i.2 : ℕ) ∧
      ⌊Real.exp (p.2 - t)⌋₊ / 2 ^ i.1 = 2 * (i.2 : ℕ) + 1 := by
  have ha := i.2.pos
  have hL := log_dyadic_endpoint t i.1 (2 * (i.2 : ℕ)) (by omega)
  have hM := log_dyadic_endpoint t i.1 (2 * (i.2 : ℕ) + 1) (by omega)
  have hR := log_dyadic_endpoint t i.1 (2 * (i.2 : ℕ) + 2) (by omega)
  change (logCellSiblingLeft _ _ < p.1 ∧ p.1 < logCellSiblingMiddle _ _) ∧
    (logCellSiblingMiddle _ _ < p.2 ∧ p.2 < logCellSiblingRight _ _) at hp
  dsimp only [logCellSiblingLeft, logCellSiblingMiddle, logCellSiblingRight] at hp
  rw [hL, hM, hR] at hp
  constructor
  · exact floor_block (by omega) (by linarith only [hp.1.1]) (by linarith only [hp.1.2])
  · apply floor_block (by omega)
    · linarith only [hp.2.1]
    · simpa only [Nat.add_assoc] using (show p.2 - t <
        Real.log (((2 * (i.2 : ℕ) + 2) * 2 ^ i.1 : ℕ) : ℝ) by linarith only [hp.2.2])

/-- Different levels spend disjoint source-pair regions, despite nested parents. -/
theorem logCellSiblingRectangle_pairwise_disjoint (t : ℝ) :
    Pairwise (Function.onFun Disjoint (logCellSiblingRectangle t)) := by
  intro i k hik
  apply disjoint_left.mpr
  intro p hi hk
  obtain ⟨hil, hir⟩ := rectangle_floor_labels hi
  obtain ⟨hkl, hkr⟩ := rectangle_floor_labels hk
  have hsi : DyadicSibling i.1 ⌊Real.exp (p.1 - t)⌋₊ ⌊Real.exp (p.2 - t)⌋₊ := by
    unfold DyadicSibling
    rw [hil, hir]
    omega
  have hsk : DyadicSibling k.1 ⌊Real.exp (p.1 - t)⌋₊ ⌊Real.exp (p.2 - t)⌋₊ := by
    unfold DyadicSibling
    rw [hkl, hkr]
    omega
  have hj : i.1 = k.1 := hsi.level_unique hsk
  have ha : i.2 = k.2 := by
    apply PNat.eq
    rw [hj, hkl] at hil
    omega
  exact hik (Prod.ext hj ha)

/-- The original source-pair charge restricted to one ordered sibling rectangle. -/
def logCellSiblingCharge (t : ℝ) (i : ℕ × ℕ+) (f : ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ p in logCellSiblingRectangle t i, gammaDifference f p.1 p.2 ∂(volume.prod volume)

/-- The parent variance on the literal translated dyadic interval. -/
def logCellDyadicParentVariance (t : ℝ) (i : ℕ × ℕ+) (f : ℝ → ℝ) : ℝ :=
  intervalVariance (logCellSiblingLeft (t + i.1 * Real.log 2) i.2)
    (logCellSiblingRight (t + i.1 * Real.log 2) i.2) f

theorem logCellSiblingCharge_eq (t : ℝ) (i : ℕ × ℕ+) {f : ℝ → ℝ} (hf : Measurable f) :
    logCellSiblingCharge t i f =
      ∫⁻ x in Ioo (logCellSiblingLeft (t + i.1 * Real.log 2) i.2)
          (logCellSiblingMiddle (t + i.1 * Real.log 2) i.2),
        ∫⁻ y in Ioo (logCellSiblingMiddle (t + i.1 * Real.log 2) i.2)
          (logCellSiblingRight (t + i.1 * Real.log 2) i.2), gammaDifference f x y := by
  rw [logCellSiblingCharge, logCellSiblingRectangle, ← Measure.prod_restrict]
  exact lintegral_prod _ (measurable_gammaDifference hf).aemeasurable

/-- Any finite collection of levels spends each source-pair charge at most once. -/
theorem sum_logCellSiblingCharge_le (t : ℝ) (S : Finset (ℕ × ℕ+))
    {f : ℝ → ℝ} (hf : Measurable f) :
    (∑ i ∈ S, logCellSiblingCharge t i f) ≤ ∫⁻ x, ∫⁻ y, gammaDifference f x y := by
  classical
  let R : S → Set (ℝ × ℝ) := fun i => logCellSiblingRectangle t i
  have hRm (i : S) : MeasurableSet (R i) := measurableSet_Ioo.prod measurableSet_Ioo
  have hpd : Pairwise (Function.onFun Disjoint R) := by
    intro i k hik
    exact logCellSiblingRectangle_pairwise_disjoint t
      (show (i : ℕ × ℕ+) ≠ k from fun h => hik (Subtype.ext h))
  rw [← Finset.sum_coe_sort]
  calc
    _ = ∫⁻ p in ⋃ i : S, R i, gammaDifference f p.1 p.2 ∂(volume.prod volume) := by
      rw [lintegral_iUnion hRm hpd, tsum_fintype]
      rfl
    _ ≤ ∫⁻ p, gammaDifference f p.1 p.2 ∂(volume.prod volume) :=
      lintegral_mono' Measure.restrict_le_self le_rfl
    _ = _ := lintegral_prod _ (measurable_gammaDifference hf).aemeasurable

/-- One original Gamma reserve pays the variances of all selected nested dyadic parents. -/
theorem sum_logCellDyadicParentVariance_le (t : ℝ) (S : Finset (ℕ × ℕ+))
    {f : ℝ → ℝ} (hv : BoundedVariationOn f univ) (hc : HasCompactSupport f) :
    (∑ i ∈ S, logCellDyadicParentVariance t i f) ≤ 16 * levyEnergy f := by
  have hfm := HTGeometry.measurable_of_boundedVariation_univ hv
  have hflp := memLp_compact_bv hv hc
  have hlocal (i : ℕ × ℕ+) : ENNReal.ofReal (logCellDyadicParentVariance t i f / 8) ≤
      logCellSiblingCharge t i f := by
    rw [logCellSiblingCharge_eq t i hfm]
    exact logCellSibling_gamma_ge_variance _ _ hflp
  have hsum := (Finset.sum_le_sum (s := S) (fun i _ => hlocal i)).trans
    (sum_logCellSiblingCharge_le t S hfm)
  rw [gammaDifference_eq_two_levyEnergy hv hc] at hsum
  have hnonneg (i : ℕ × ℕ+) : 0 ≤ logCellDyadicParentVariance t i f :=
    intervalVariance_nonneg _ _ _
  have hΓ := levyEnergy_nonneg_bv hv hc
  have heleft : (∑ i ∈ S, ENNReal.ofReal (logCellDyadicParentVariance t i f / 8)) =
      ENNReal.ofReal ((∑ i ∈ S, logCellDyadicParentVariance t i f) / 8) := by
    rw [Finset.sum_div, ENNReal.ofReal_sum_of_nonneg (fun i _ => div_nonneg (hnonneg i) (by norm_num))]
  have heright : (2 : ℝ≥0∞) * ENNReal.ofReal (levyEnergy f) =
      ENNReal.ofReal (2 * levyEnergy f) := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
  rw [heleft, heright] at hsum
  have hreal := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by norm_num) hΓ)).mp hsum
  linarith only [hreal]

/-- Complete arithmetic profiles satisfy the joint bound with every coarse mean free. -/
theorem completePair_sum_logCellDyadicParentVariance_le (q d : ℕ → ℝ) (X : ℕ)
    (t : ℝ) (S : Finset (ℕ × ℕ+)) :
    (∑ i ∈ S, logCellDyadicParentVariance t i (completePairProfile q d X)) ≤
      16 * levyEnergy (completePairProfile q d X) :=
  sum_logCellDyadicParentVariance_le t S
    (completePairProfile_bv q d X) (completePairProfile_compact q d X)

end GaloisForLFunctions.SignedArithmeticHodgeTheory

#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.logCellSiblingRectangle_pairwise_disjoint
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.sum_logCellDyadicParentVariance_le
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.completePair_sum_logCellDyadicParentVariance_le
