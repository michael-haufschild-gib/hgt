import GaloisForLFunctions.SignedArithmeticHodgeTheory.DyadicVarianceSplitsIntoTheLiteralHaarReadout
import Mathlib.Data.Nat.Log

/-!+# Counting ancestors without spending a variance twice

Summing exact variance conservation along a complete level orbit gives a binary
flow on generator labels. Its tail above twice a threshold, together with the
detail energy above that threshold, is bounded by the original variance tail.
Telescoping at powers of two counts each generator's ancestors. All sums are
justified by the single original Gamma bound.
-/

noncomputable section
open MeasureTheory Set RHTower
open scoped BigOperators

namespace GaloisForLFunctions.SignedArithmeticHodgeTheory

open HTGeometry ArithmeticCastelnuovoSeveri.IntervalVariance
open ArithmeticCastelnuovoSeveri.LogCells

private def positiveExtension (F : ℕ+ → ℝ) (a : ℕ) : ℝ :=
  if ha : 0 < a then F ⟨a, ha⟩ else 0

private theorem positiveExtension_coe (F : ℕ+ → ℝ) (a : ℕ+) :
    positiveExtension F a = F a := by simp only [positiveExtension, a.pos, dif_pos]

private theorem positiveExtension_summable {F : ℕ+ → ℝ} (hF : Summable F) :
    Summable (positiveExtension F) := by
  apply PNatBlock.summable_pnat_iff.mp
  simpa only [positiveExtension_coe] using hF

private def labelTail (F : ℕ → ℝ) (M : ℕ) : ℝ :=
  ∑' a, if M ≤ a then F a else 0

private theorem labelTail_summable {F : ℕ → ℝ} (hF : Summable F) (M : ℕ) :
    Summable (fun a => if M ≤ a then F a else 0) :=
  hF.indicator {a | M ≤ a}

private theorem labelTail_nonneg {F : ℕ → ℝ} (hF : ∀ a, 0 ≤ F a) (M : ℕ) :
    0 ≤ labelTail F M := by
  apply tsum_nonneg
  intro a
  split_ifs <;> positivity

private theorem labelTail_flow {F G : ℕ → ℝ}
    (hF : ∀ a, 0 ≤ F a) (hG : ∀ a, 0 ≤ G a)
    (hsF : Summable F) (hsG : Summable G)
    (hflow : ∀ a, 1 ≤ a → G a + F (2 * a) + F (2 * a + 1) ≤ F a)
    {M : ℕ} (hM : 1 ≤ M) :
    labelTail G M + labelTail F (2 * M) ≤ labelTail F M := by
  let C : ℕ → ℝ := fun a => if M ≤ a then F (2 * a) + F (2 * a + 1) else 0
  have hC0 (a : ℕ) : 0 ≤ C a := by dsimp [C]; split_ifs <;> positivity
  have hCle (a : ℕ) : C a ≤ if M ≤ a then F a else 0 := by
    dsimp only [C]
    split_ifs with ha
    · linarith only [hflow a (hM.trans ha), hG a]
    · rfl
  have hsC := Summable.of_nonneg_of_le hC0 hCle (labelTail_summable hsF M)
  have hchildren : labelTail F (2 * M) = ∑' a, C a := by
    rw [labelTail, PNatBlock.tsum_block (b := 2) (labelTail_summable hsF (2 * M))]
    apply tsum_congr
    intro a
    simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, Nat.add_zero]
    have he : 2 * M ≤ a * 2 ↔ M ≤ a := by omega
    have ho : 2 * M ≤ a * 2 + 1 ↔ M ≤ a := by omega
    simp only [he, ho, C, Nat.mul_comm a 2]
    split_ifs <;> simp
  rw [hchildren, labelTail, ← (labelTail_summable hsG M).tsum_add hsC]
  apply Summable.tsum_le_tsum _ ((labelTail_summable hsG M).add hsC)
    (labelTail_summable hsF M)
  intro a
  dsimp only [C]
  split_ifs with ha
  · simpa only [add_assoc] using hflow a (hM.trans ha)
  · simp

private theorem sum_labelTail_powers_le {F G : ℕ → ℝ}
    (hF : ∀ a, 0 ≤ F a) (hG : ∀ a, 0 ≤ G a)
    (hsF : Summable F) (hsG : Summable G)
    (hflow : ∀ a, 1 ≤ a → G a + F (2 * a) + F (2 * a + 1) ≤ F a)
    (L : ℕ) : (∑ r ∈ Finset.range L, labelTail G (2 ^ r)) ≤ labelTail F 1 := by
  have hstrong (L : ℕ) :
      (∑ r ∈ Finset.range L, labelTail G (2 ^ r)) + labelTail F (2 ^ L) ≤
        labelTail F 1 := by
    induction L with
    | zero => simp
    | succ L ih =>
      have h := labelTail_flow hF hG hsF hsG hflow (M := 2 ^ L)
        (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by decide)))
      rw [Finset.sum_range_succ, pow_succ]
      rw [Nat.mul_comm (2 ^ L) 2]
      linarith only [h, ih]
  linarith only [hstrong L, labelTail_nonneg hF (2 ^ L)]

private theorem count_binary_thresholds (a : ℕ+) {L : ℕ}
    (hL : Nat.log 2 (a : ℕ) + 1 ≤ L) (d : ℝ) :
    (∑ r ∈ Finset.range L, if 2 ^ r ≤ (a : ℕ) then d else 0) =
      ((Nat.log 2 (a : ℕ) + 1 : ℕ) : ℝ) * d := by
  classical
  have hfilter : (Finset.range L).filter (fun r => 2 ^ r ≤ (a : ℕ)) =
      Finset.range (Nat.log 2 (a : ℕ) + 1) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_range,
      ← Nat.le_log_iff_pow_le (by norm_num : 1 < 2) (Nat.ne_of_gt a.pos)]
    omega
  rw [← Finset.sum_filter, hfilter, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

private theorem sum_ancestor_weight_le {F G : ℕ → ℝ}
    (hF : ∀ a, 0 ≤ F a) (hG : ∀ a, 0 ≤ G a)
    (hsF : Summable F) (hsG : Summable G)
    (hflow : ∀ a, 1 ≤ a → G a + F (2 * a) + F (2 * a + 1) ≤ F a)
    (T : Finset ℕ+) :
    (∑ a ∈ T, ((Nat.log 2 (a : ℕ) + 1 : ℕ) : ℝ) * G a) ≤ labelTail F 1 := by
  classical
  let L := ∑ a ∈ T, (Nat.log 2 (a : ℕ) + 1)
  have hL (a : ℕ+) (ha : a ∈ T) : Nat.log 2 (a : ℕ) + 1 ≤ L :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) ha
  have hthreshold (r : ℕ) :
      (∑ a ∈ T, if 2 ^ r ≤ (a : ℕ) then G a else 0) ≤ labelTail G (2 ^ r) := by
    have hsum : Summable (fun a : ℕ+ => if 2 ^ r ≤ (a : ℕ) then G a else 0) :=
      PNatBlock.summable_pnat_iff.mpr (labelTail_summable hsG (2 ^ r))
    calc
      _ ≤ ∑' a : ℕ+, if 2 ^ r ≤ (a : ℕ) then G a else 0 :=
        hsum.sum_le_tsum T (fun a _ => by split_ifs <;> positivity)
      _ = labelTail G (2 ^ r) := PNatBlock.tsum_pnat _ (by
        rw [if_neg (by have := pow_pos (by norm_num : 0 < (2 : ℕ)) r; omega)])
  calc
    _ = ∑ a ∈ T, ∑ r ∈ Finset.range L, if 2 ^ r ≤ (a : ℕ) then G a else 0 :=
      Finset.sum_congr rfl (fun a ha => (count_binary_thresholds a (hL a ha) (G a)).symm)
    _ = ∑ r ∈ Finset.range L, ∑ a ∈ T, if 2 ^ r ≤ (a : ℕ) then G a else 0 :=
      Finset.sum_comm
    _ ≤ ∑ r ∈ Finset.range L, labelTail G (2 ^ r) :=
      Finset.sum_le_sum (fun r _ => hthreshold r)
    _ ≤ _ := sum_labelTail_powers_le hF hG hsF hsG hflow L

private theorem summable_parent_variances (t : ℝ) {f : ℝ → ℝ}
    (hv : BoundedVariationOn f univ) (hc : HasCompactSupport f) :
    Summable (fun i : ℕ × ℕ+ => logCellDyadicParentVariance t i f) :=
  summable_of_sum_le (fun _ => intervalVariance_nonneg _ _ _)
    (fun S => sum_logCellDyadicParentVariance_le t S hv hc)

private theorem summable_readout_squares (t : ℝ) {f : ℝ → ℝ}
    (hv : BoundedVariationOn f univ) (hc : HasCompactSupport f) :
    Summable (fun i : ℕ × ℕ+ => logCellHaarReadout t i f ^ 2) :=
  Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
    (fun i => logCellHaarReadout_sq_le_variance t i (memLp_compact_bv hv hc))
    (summable_parent_variances t hv hc)

/-- Variance spent by one generator label along its entire dyadic level orbit. -/
def logCellParentVarianceOrbit (t : ℝ) (a : ℕ+) (f : ℝ → ℝ) : ℝ :=
  ∑' j, logCellDyadicParentVariance t (j, a) f

/-- Actual Haar-coordinate square mass along an entire translation orbit. -/
def logCellHaarOrbitEnergy (t : ℝ) (a : ℕ+) (f : ℝ → ℝ) : ℝ :=
  ∑' j, logCellHaarReadout t (j, a) f ^ 2

private theorem parent_variance_rows (t : ℝ) {f : ℝ → ℝ}
    (hv : BoundedVariationOn f univ) (hc : HasCompactSupport f) :
    (∀ a : ℕ+, Summable (fun j => logCellDyadicParentVariance t (j, a) f)) ∧
      Summable (fun a => logCellParentVarianceOrbit t a f) := by
  have h := (summable_parent_variances t hv hc).comp_injective Prod.swap_injective
  exact (summable_prod_of_nonneg (fun i : ℕ+ × ℕ =>
    intervalVariance_nonneg _ _ _)).mp h

private theorem readout_rows (t : ℝ) {f : ℝ → ℝ}
    (hv : BoundedVariationOn f univ) (hc : HasCompactSupport f) :
    (∀ a : ℕ+, Summable (fun j => logCellHaarReadout t (j, a) f ^ 2)) ∧
      Summable (fun a => logCellHaarOrbitEnergy t a f) := by
  have h := (summable_readout_squares t hv hc).comp_injective Prod.swap_injective
  exact (summable_prod_of_nonneg (fun i : ℕ+ × ℕ => sq_nonneg _)).mp h

/-- Exact variance conservation produces a binary flow after retaining every level. -/
theorem logCellHaarOrbitEnergy_flow (t : ℝ) (a : ℕ+) {f : ℝ → ℝ}
    (hv : BoundedVariationOn f univ) (hc : HasCompactSupport f) :
    logCellHaarOrbitEnergy t a f +
        logCellParentVarianceOrbit t (dyadicLeftCell a) f +
        logCellParentVarianceOrbit t (dyadicRightCell a) f ≤
      logCellParentVarianceOrbit t a f := by
  have hV := (parent_variance_rows t hv hc).1
  have hD := (readout_rows t hv hc).1
  have hDs : Summable (fun j => logCellHaarReadout t (j + 1, a) f ^ 2) :=
    (summable_nat_add_iff 1).mpr (hD a)
  have hs := tsum_congr (fun j => logCellDyadicParentVariance_split t j a
    (memLp_compact_bv hv hc))
  rw [((hV (dyadicLeftCell a)).add (hV (dyadicRightCell a))).tsum_add hDs,
    (hV (dyadicLeftCell a)).tsum_add (hV (dyadicRightCell a))] at hs
  have hVa := (hV a).tsum_eq_zero_add
  have hDa := (hD a).tsum_eq_zero_add
  have hbase := logCellHaarReadout_sq_le_variance t (0, a) (memLp_compact_bv hv hc)
  unfold logCellHaarOrbitEnergy logCellParentVarianceOrbit
  linarith only [hs, hVa, hDa, hbase]

/-- The exact number of positive binary ancestors, including the generator itself. -/
def logCellAncestorWeight (a : ℕ+) : ℝ := ((Nat.log 2 (a : ℕ) + 1 : ℕ) : ℝ)

theorem logCellAncestorWeight_pos (a : ℕ+) : 0 < logCellAncestorWeight a := by
  unfold logCellAncestorWeight
  positivity

/-- Every ancestor is counted while the original Gamma reserve is spent only once. -/
theorem sum_logCellAncestorWeight_orbit_le (t : ℝ) (T : Finset ℕ+)
    {f : ℝ → ℝ} (hv : BoundedVariationOn f univ) (hc : HasCompactSupport f) :
    (∑ a ∈ T, logCellAncestorWeight a * logCellHaarOrbitEnergy t a f) ≤
      16 * levyEnergy f := by
  let F := positiveExtension (fun a => logCellParentVarianceOrbit t a f)
  let G := positiveExtension (fun a => logCellHaarOrbitEnergy t a f)
  have hF (a : ℕ) : 0 ≤ F a := by
    dsimp only [F, positiveExtension]
    split_ifs
    · exact tsum_nonneg (fun _ => intervalVariance_nonneg _ _ _)
    · rfl
  have hG (a : ℕ) : 0 ≤ G a := by
    dsimp only [G, positiveExtension]
    split_ifs
    · exact tsum_nonneg (fun _ => sq_nonneg _)
    · rfl
  have hsF := positiveExtension_summable (parent_variance_rows t hv hc).2
  have hsG := positiveExtension_summable (readout_rows t hv hc).2
  have hflow (a : ℕ) (ha : 1 ≤ a) : G a + F (2 * a) + F (2 * a + 1) ≤ F a := by
    simpa only [G, F, positiveExtension, dif_pos (show 0 < a by omega),
      dif_pos (show 0 < 2 * a by omega), dif_pos (show 0 < 2 * a + 1 by omega),
      dyadicLeftCell, dyadicRightCell] using
      logCellHaarOrbitEnergy_flow t ⟨a, ha⟩ hv hc
  have h := sum_ancestor_weight_le hF hG hsF hsG hflow T
  simp only [G, positiveExtension_coe, ← logCellAncestorWeight] at h
  apply h.trans
  have htail : labelTail F 1 = ∑' a : ℕ+, logCellParentVarianceOrbit t a f := by
    rw [labelTail, ← PNatBlock.tsum_pnat _ (by simp)]
    apply tsum_congr
    intro a
    rw [if_pos a.pos]
    exact positiveExtension_coe _ a
  rw [htail]
  have hs := (summable_parent_variances t hv hc).comp_injective Prod.swap_injective
  rw [show (∑' a : ℕ+, logCellParentVarianceOrbit t a f) =
      ∑' i : ℕ × ℕ+, logCellDyadicParentVariance t i f by
    rw [← hs.tsum_prod]
    exact (Equiv.prodComm ℕ+ ℕ).tsum_eq _]
  exact Real.tsum_le_of_sum_le (fun _ => intervalVariance_nonneg _ _ _)
    (fun S => sum_logCellDyadicParentVariance_le t S hv hc)

/-- The natural-logarithmic label cost is bounded by twice the exact ancestor count. -/
theorem one_add_log_le_two_ancestorWeight (a : ℕ+) :
    1 + Real.log (a : ℝ) ≤ 2 * logCellAncestorWeight a := by
  have hp := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (a : ℕ)
  have hl := Real.log_lt_log (by exact_mod_cast a.pos : (0 : ℝ) < a)
    (by exact_mod_cast hp : (a : ℝ) < ((2 ^ (Nat.log 2 (a : ℕ) + 1) : ℕ) : ℝ))
  rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] at hl
  have htwo : Real.log 2 ≤ 1 := by
    simpa using Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hw : 1 ≤ logCellAncestorWeight a := by unfold logCellAncestorWeight; norm_cast; omega
  have hmul := mul_le_mul_of_nonneg_left htwo (logCellAncestorWeight_pos a).le
  change Real.log (a : ℝ) < logCellAncestorWeight a * Real.log 2 at hl
  linarith only [hl, hw, hmul]

/-- Logarithmic control retains the entire orbit of every selected generator. -/
theorem sum_log_weight_haar_orbit_le (t : ℝ) (T : Finset ℕ+)
    {f : ℝ → ℝ} (hv : BoundedVariationOn f univ) (hc : HasCompactSupport f) :
    (∑ a ∈ T, (1 + Real.log (a : ℝ)) * logCellHaarOrbitEnergy t a f) ≤
      32 * levyEnergy f := by
  have h := sum_logCellAncestorWeight_orbit_le t T hv hc
  have hw : (∑ a ∈ T, (1 + Real.log (a : ℝ)) * logCellHaarOrbitEnergy t a f) ≤
      2 * ∑ a ∈ T, logCellAncestorWeight a * logCellHaarOrbitEnergy t a f := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a _
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (one_add_log_le_two_ancestorWeight a)
      (tsum_nonneg (fun _ => sq_nonneg _))
  linarith only [hw, h]

end GaloisForLFunctions.SignedArithmeticHodgeTheory

#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.logCellHaarOrbitEnergy_flow
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.sum_logCellAncestorWeight_orbit_le
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.sum_log_weight_haar_orbit_le
