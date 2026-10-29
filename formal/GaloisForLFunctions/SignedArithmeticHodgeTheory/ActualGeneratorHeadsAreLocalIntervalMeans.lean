import GaloisForLFunctions.SignedArithmeticHodgeTheory.ActualGeneratorHeadsPreserveTheSourceMean
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.GammaMeanVarianceCapacity

/-!
# Physical generator heads are local interval means

A translated stopping cell is a finite union of original logarithmic cells.
Its indicator is fixed by the orthogonal generator projection. Self-adjointness
therefore preserves the integral over each stopping cell, while the explicit
coordinate formula makes the projected profile constant there.
-/

noncomputable section
open MeasureTheory Set Filter RHTower
open scoped InnerProductSpace

namespace GaloisForLFunctions.SignedArithmeticHodgeTheory
open HTGeometry ArithmeticCastelnuovoSeveri.LogCells BiarithmeticGaugeGeometry
open ArithmeticCastelnuovoSeveri.IntervalVariance

local notation "CellH" => lp (fun _ : ℕ+ => ℂ) 2
local notation "U" => wholeLineLogCellEmbedding
local notation "P" => logCellGeneratorHead
local notation "e" => fun n : ℕ+ => (lp.single 2 n (1 : ℂ) : CellH)

/-- Left endpoint of a literal dyadic block of original cells. -/
def dyadicBlockLeft (j : ℕ) (a : ℕ+) : ℝ := Real.log (((a : ℕ) * 2 ^ j : ℕ) : ℝ)

/-- Right endpoint of the same block. -/
def dyadicBlockRight (j : ℕ) (a : ℕ+) : ℝ := Real.log ((((a : ℕ) + 1) * 2 ^ j : ℕ) : ℝ)

theorem dyadicBlockLeft_eq (j : ℕ) (a : ℕ+) :
    dyadicBlockLeft j a = (j : ℝ) * Real.log 2 + Real.log (a : ℝ) := by
  rw [dyadicBlockLeft, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
    Real.log_mul (by exact_mod_cast a.pos.ne' : (a : ℝ) ≠ 0) (by positivity), Real.log_pow]
  ring

theorem dyadicBlockRight_eq (j : ℕ) (a : ℕ+) :
    dyadicBlockRight j a = (j : ℝ) * Real.log 2 + Real.log ((a : ℝ) + 1) := by
  rw [dyadicBlockRight, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_pow,
    Nat.cast_ofNat, Real.log_mul (by positivity) (by positivity), Real.log_pow]
  ring

theorem dyadicBlock_width (j : ℕ) (a : ℕ+) :
    dyadicBlockRight j a - dyadicBlockLeft j a = logCell a := by
  rw [dyadicBlockRight_eq, dyadicBlockLeft_eq, logCell]
  ring

theorem dyadicBlock_pos (j : ℕ) (a : ℕ+) : dyadicBlockLeft j a < dyadicBlockRight j a := by
  have h := logCell_pos a.pos
  rw [← dyadicBlock_width j a] at h
  exact sub_pos.mp h

private theorem logCellSet_disjoint {n m : ℕ+} (h : n ≠ m) :
    Disjoint (logCellSet n) (logCellSet m) := by
  apply disjoint_left.mpr
  intro x hn hm
  have hne : (n : ℕ) ≠ (m : ℕ) := fun he => h (PNat.eq he)
  rcases lt_or_gt_of_ne hne with hnm | hmn
  · have he : Real.log ((n : ℝ) + 1) ≤ Real.log (m : ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast hnm)
    exact (not_lt_of_ge (he.trans hm.1)) hn.2
  · have he : Real.log ((m : ℝ) + 1) ≤ Real.log (n : ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast hmn)
    exact (not_lt_of_ge (he.trans hn.1)) hm.2

private theorem rawCell_eq_logCellSet (n : ℕ+) :
    rawCell (n : ℕ) = (logCellSet n).indicator (fun _ => (1 : ℝ)) := by
  simp only [rawCell, logCellSet, Nat.cast_add, Nat.cast_one]

/-- The finite Hilbert coordinate divided by square-root width is the literal cell height. -/
theorem finiteLogCellProfile_eq_physicalHeight {ι : Type*} [Fintype ι]
    (n : ι → ℕ+) (c : ι → ℝ) (m : ℕ+) {x : ℝ} (hx : x ∈ logCellSet m) :
    (finiteLogCellProfile n c x : ℂ) = logCellPhysicalHeight (finiteLogCellVector n c) m := by
  classical
  have hcoord : (finiteLogCellVector n c) m =
      ∑ i, (c i : ℂ) * (Real.sqrt (logCell m) : ℂ) * (rawCell (n i) x : ℂ) := by
    calc
      _ = inner ℂ (e m) (finiteLogCellVector n c) := by
        simp only [lp.inner_single_left, RCLike.inner_apply, map_one, mul_one]
      _ = _ := by
        rw [finiteLogCellVector, inner_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [inner_smul_right, lp.inner_single_left, RCLike.inner_apply, map_one, mul_one]
        by_cases hi : n i = m
        · subst m
          simp only [lp.single_apply, Pi.single_apply, ite_true, rawCell_eq_logCellSet,
            indicator_of_mem hx, Complex.ofReal_one, mul_one, Complex.ofReal_mul]
        · have hix : x ∉ logCellSet (n i) := fun hix =>
            (disjoint_left.mp (logCellSet_disjoint hi)) hix hx
          have hmi : m ≠ n i := Ne.symm hi
          simp only [lp.single_apply, Pi.single_eq_of_ne hmi, rawCell_eq_logCellSet,
            indicator_of_notMem hix, Complex.ofReal_zero, mul_zero]
  rw [logCellPhysicalHeight, hcoord]
  have hs : (Real.sqrt (logCell m) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (logCell_pos m.pos)).ne'
  rw [Finset.sum_div]
  simp only [finiteLogCellProfile, Complex.ofReal_sum, Complex.ofReal_mul]
  apply Finset.sum_congr rfl
  intro i _
  field_simp

/-- The finite block source is exactly its interval indicator, including the left endpoint. -/
theorem finiteLogCellProfile_block (j : ℕ) (a : ℕ+) :
    finiteLogCellProfile (logCellDyadicBlockCell j a) (fun _ => 1) =
      (Ico (dyadicBlockLeft j a) (dyadicBlockRight j a)).indicator (fun _ => (1 : ℝ)) := by
  funext x
  apply Complex.ofReal_injective
  have h := indicator_Ico_log_eq_sum
    (show 0 < (a : ℕ) * 2 ^ j by positivity) (2 ^ j) (1 : ℂ) x
  have hend : (a : ℕ) * 2 ^ j + 2 ^ j = ((a : ℕ) + 1) * 2 ^ j := by ring
  rw [hend] at h
  rw [finiteLogCellProfile, Complex.ofReal_sum]
  simp only [one_mul]
  change (∑ r : Fin (2 ^ j), (rawCell ((a : ℕ) * 2 ^ j + (r : ℕ)) x : ℂ)) = _
  rw [Fin.sum_univ_eq_sum_range]
  convert h.symm using 1 <;>
    simp only [logCellDyadicBlockCell, dyadicBlockLeft, dyadicBlockRight, rawCell,
      logCellSet, RHTower.coe_toPNat, Nat.cast_add, Nat.cast_one,
      indicator_apply, apply_ite, Complex.ofReal_one, Complex.ofReal_zero]

/-- The indicator coordinates are the square-root length multiple of the normalized translated cell. -/
theorem finiteLogCellVector_block (j : ℕ) (a : ℕ+) :
    finiteLogCellVector (logCellDyadicBlockCell j a) (fun _ => 1) =
      (Real.sqrt (logCell a) : ℂ) • ((logCellShift 2 ^ j) (e a)) := by
  rw [finiteLogCellVector, logCellDyadic_pow_single_eq_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [one_mul, smul_smul]
  congr 1
  rw [← Complex.ofReal_mul, Real.sqrt_div (logCell_pos (logCellDyadicBlockCell j a r).pos).le]
  have ha := (Real.sqrt_pos.mpr (logCell_pos a.pos)).ne'
  congr 1
  field_simp

private theorem inner_real_profiles (f g : ℝ → ℝ)
    (hfv : BoundedVariationOn f univ) (hfc : HasCompactSupport f)
    (hgv : BoundedVariationOn g univ) (hgc : HasCompactSupport g) :
    inner ℂ (realSourceLp f hfv hfc) (realSourceLp g hgv hgc) =
      ((∫ x, f x * g x : ℝ) : ℂ) := by
  rw [L2.inner_def]
  calc
    _ = ∫ x, ((f x * g x : ℝ) : ℂ) := by
      apply integral_congr_ae
      filter_upwards [realSourceLp_coeFn f hfv hfc, realSourceLp_coeFn g hgv hgc] with x hf hg
      rw [hf, hg, RCLike.inner_apply, Complex.conj_ofReal, ← Complex.ofReal_mul, mul_comm]
    _ = _ := integral_complex_ofReal

/-- Projection preserves the original integral on every retained translated cell. -/
theorem integral_actualGeneratorHead_block {ι : Type*} [Fintype ι]
    (A : ℕ+) (n : ι → ℕ+) (c : ι → ℝ) (j : ℕ) (a : ℕ+)
    (ha : (a : ℕ) < 2 * (A : ℕ)) :
    (∫ x in Ioo (dyadicBlockLeft j a) (dyadicBlockRight j a), actualGeneratorHeadProfile A n c x) =
      ∫ x in Ioo (dyadicBlockLeft j a) (dyadicBlockRight j a), finiteLogCellProfile n c x := by
  let b := finiteLogCellProfile (logCellDyadicBlockCell j a) (fun _ => 1)
  let v := finiteLogCellVector (logCellDyadicBlockCell j a) (fun _ => 1)
  have hv : P A v = v := by
    dsimp only [v]
    rw [finiteLogCellVector_block, map_smul, logCellGeneratorHead_dyadic_pow,
      logCellGeneratorHead_single_of_lt A a ha]
  have he : (∫ x, b x * actualGeneratorHeadProfile A n c x) =
      ∫ x, b x * finiteLogCellProfile n c x := by
    apply Complex.ofReal_injective
    rw [← inner_real_profiles b (actualGeneratorHeadProfile A n c)
      (finiteLogCellProfile_bv _ _) (finiteLogCellProfile_compact _ _)
      (actualGeneratorHeadProfile_bv A n c) (actualGeneratorHeadProfile_compact A n c),
      ← inner_real_profiles b (finiteLogCellProfile n c)
      (finiteLogCellProfile_bv _ _) (finiteLogCellProfile_compact _ _)
      (finiteLogCellProfile_bv n c) (finiteLogCellProfile_compact n c)]
    simp only [realSourceLp_actualGeneratorHead, realSourceLp_finiteLogCellProfile]
    rw [← wholeLineLogCellEmbedding.adjoint_inner_right, ← wholeLineLogCellEmbedding.adjoint_inner_right,
      wholeLineLogCellEmbedding_adjoint_self, wholeLineLogCellEmbedding_adjoint_self,
      ← inner_logCellGeneratorHead, hv]
  have hmul (f : ℝ → ℝ) : (fun x => b x * f x) =
      (Ico (dyadicBlockLeft j a) (dyadicBlockRight j a)).indicator f := by
    funext x
    simp only [b, finiteLogCellProfile_block, indicator_apply]
    split_ifs <;> simp only [one_mul, zero_mul]
  rw [hmul, hmul, integral_indicator measurableSet_Ico,
    integral_indicator measurableSet_Ico] at he
  simpa only [Measure.restrict_congr_set Ioo_ae_eq_Ico] using he

private theorem exists_cell_in_dyadicBlock (j : ℕ) (a : ℕ+) {x : ℝ}
    (hx : x ∈ Ico (dyadicBlockLeft j a) (dyadicBlockRight j a)) :
    ∃ r : Fin (2 ^ j), x ∈ logCellSet (logCellDyadicBlockCell j a r) := by
  classical
  by_contra! hn
  have hz : finiteLogCellProfile (logCellDyadicBlockCell j a) (fun _ => 1) x = 0 := by
    apply Finset.sum_eq_zero
    intro r _
    rw [rawCell_eq_logCellSet, indicator_of_notMem (hn r), mul_zero]
  rw [finiteLogCellProfile_block, indicator_of_mem hx] at hz
  norm_num at hz

private theorem stoppingAncestor_block (A : ℕ+) (j : ℕ) (a : ℕ+)
    (ha : (a : ℕ) < 2 * (A : ℕ)) (hja : j = 0 ∨ (A : ℕ) ≤ (a : ℕ))
    (r : Fin (2 ^ j)) : logCellStoppingAncestor A (logCellDyadicBlockCell j a r) = (j, a) := by
  rcases hja with rfl | hAa
  · have he : logCellDyadicBlockCell 0 a r = a := PNat.eq (by
      simpa only [pow_zero, Nat.div_one] using logCellDyadicBlockCell_div 0 a r)
    rw [he, logCellStoppingAncestor_of_lt A a ha]
  · exact logCellStoppingAncestor_eq_of_div A a hAa ha j _ (logCellDyadicBlockCell_div j a r)

/-- The physical head is constant throughout each stopping interval. -/
theorem actualGeneratorHead_eq_on_block {ι : Type*} [Fintype ι]
    (A : ℕ+) (n : ι → ℕ+) (c : ι → ℝ) (j : ℕ) (a : ℕ+)
    (ha : (a : ℕ) < 2 * (A : ℕ)) (hja : j = 0 ∨ (A : ℕ) ≤ (a : ℕ))
    {x y : ℝ} (hx : x ∈ Ico (dyadicBlockLeft j a) (dyadicBlockRight j a))
    (hy : y ∈ Ico (dyadicBlockLeft j a) (dyadicBlockRight j a)) :
    actualGeneratorHeadProfile A n c x = actualGeneratorHeadProfile A n c y := by
  obtain ⟨r, hr⟩ := exists_cell_in_dyadicBlock j a hx
  obtain ⟨s, hs⟩ := exists_cell_in_dyadicBlock j a hy
  apply Complex.ofReal_injective
  have hx' := finiteLogCellProfile_eq_physicalHeight
    (stoppedLogCellLabel A n) (stoppedLogCellHeight A n c) _ hr
  have hy' := finiteLogCellProfile_eq_physicalHeight
    (stoppedLogCellLabel A n) (stoppedLogCellHeight A n c) _ hs
  rw [finiteLogCellVector_stopped] at hx' hy'
  change (finiteLogCellProfile _ _ x : ℂ) = (finiteLogCellProfile _ _ y : ℂ)
  rw [hx', hy']
  apply logCellGeneratorHead_height_eq_of_same_block A (logCellDyadicBlockCell j a s)
  rw [stoppingAncestor_block A j a ha hja s]
  exact logCellDyadicBlockCell_div j a r

/-- Every actual head value equals the original source mean on its stopping interval. -/
theorem actualGeneratorHead_eq_intervalMean {ι : Type*} [Fintype ι]
    (A : ℕ+) (n : ι → ℕ+) (c : ι → ℝ) (j : ℕ) (a : ℕ+)
    (ha : (a : ℕ) < 2 * (A : ℕ)) (hja : j = 0 ∨ (A : ℕ) ≤ (a : ℕ))
    {x : ℝ} (hx : x ∈ Ioo (dyadicBlockLeft j a) (dyadicBlockRight j a)) :
    actualGeneratorHeadProfile A n c x =
      intervalMean (dyadicBlockLeft j a) (dyadicBlockRight j a) (finiteLogCellProfile n c) := by
  have he := integral_actualGeneratorHead_block A n c j a ha
  have hc : (∫ y in Ioo (dyadicBlockLeft j a) (dyadicBlockRight j a),
      actualGeneratorHeadProfile A n c y) =
      (dyadicBlockRight j a - dyadicBlockLeft j a) * actualGeneratorHeadProfile A n c x := by
    calc
      _ = ∫ _y in Ioo (dyadicBlockLeft j a) (dyadicBlockRight j a),
          actualGeneratorHeadProfile A n c x := by
        apply setIntegral_congr_fun measurableSet_Ioo
        intro y hy
        exact actualGeneratorHead_eq_on_block A n c j a ha hja ⟨hy.1.le, hy.2⟩ ⟨hx.1.le, hx.2⟩
      _ = _ := by
        rw [setIntegral_const, Real.volume_real_Ioo_of_le (dyadicBlock_pos j a).le, smul_eq_mul]
  rw [intervalMean, ← he, hc]
  field_simp [(sub_pos.mpr (dyadicBlock_pos j a)).ne']

/-- Every finite positive-label source vanishes on the negative half-line. -/
theorem finiteLogCellProfile_zero_of_neg {ι : Type*} [Fintype ι]
    (n : ι → ℕ+) (c : ι → ℝ) {x : ℝ} (hx : x < 0) : finiteLogCellProfile n c x = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  have hi : x ∉ logCellSet (n i) := by
    intro h
    have hn := Real.log_nonneg (by exact_mod_cast (n i).pos : (1 : ℝ) ≤ (n i))
    exact (not_le_of_gt hx) (hn.trans h.1)
  rw [rawCell_eq_logCellSet, indicator_of_notMem hi, mul_zero]

/-- A finite source vanishes beyond an explicit finite sum of its right endpoints. -/
theorem exists_finiteLogCellProfile_zero_above {ι : Type*} [Fintype ι]
    (n : ι → ℕ+) (c : ι → ℝ) : ∃ R : ℝ, ∀ x, R ≤ x → finiteLogCellProfile n c x = 0 := by
  classical
  refine ⟨∑ i, Real.log (((n i : ℕ) + 1 : ℕ) : ℝ), ?_⟩
  intro x hx
  apply Finset.sum_eq_zero
  intro i hi
  have hnonneg (k : ι) : 0 ≤ Real.log (((n k : ℕ) + 1 : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ (n k : ℕ) + 1 by omega))
  have hle : Real.log (((n i : ℕ) + 1 : ℕ) : ℝ) ≤
      ∑ i, Real.log (((n i : ℕ) + 1 : ℕ) : ℝ) :=
    Finset.single_le_sum (fun k _ => hnonneg k) hi
  have hn : x ∉ logCellSet (n i) := by
    intro h
    apply (not_lt_of_ge (hle.trans hx))
    simpa only [Nat.cast_add, Nat.cast_one] using h.2
  rw [rawCell_eq_logCellSet, indicator_of_notMem hn, mul_zero]

end GaloisForLFunctions.SignedArithmeticHodgeTheory

#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.actualGeneratorHead_eq_intervalMean
