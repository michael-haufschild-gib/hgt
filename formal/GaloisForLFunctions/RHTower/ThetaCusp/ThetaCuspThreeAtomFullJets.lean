import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspThreeAtomSourceHead

/-!
# Complete-source jets in the three-atom normalization

The full derivative series is exactly the sum of the three-atom head
and the retained infinite tail. After dividing the j-th normalized
jet by `q^(j+1)`, both head and full jets have the same constant
coefficient bounds. Their difference retains the factor `exp(-15q)`.
The zero-order head and full jets are at least `q` on `q ≥ π`.
-/

namespace RHTower.ThetaCuspThreeAtomFourth

noncomputable def headJet (j : ℕ) (q : ℝ) : ℝ :=
  rawHeadJet j q (Real.exp (-3*q)) (Real.exp (-8*q))

noncomputable def fullJet (j : ℕ) (q : ℝ) : ℝ := headJet j q + normalizedTailJet j q

noncomputable def scaledHeadJet (q : ℝ) (j : ℕ) : ℝ := headJet j q / q^(j+1)

noncomputable def scaledFullJet (q : ℝ) (j : ℕ) : ℝ := fullJet j q / q^(j+1)

theorem normalizedAtomJet_index_zero (j : ℕ) (q : ℝ) : normalizedAtomJet j q 0 = 0 := by
  simp [normalizedAtomJet]

/-- Exact decomposition of every literal full-source derivative. -/
theorem fullDerivative_eq_normalized (j : ℕ) (x : ℝ) :
    thetaCuspFullDerivative j x = sourcePrefactor x * fullJet j (sourceScale x) := by
  have hs := summable_iteratedDeriv_thetaCuspSourceTerm j x
  rw [thetaCuspFullDerivative, ← hs.sum_add_tsum_nat_add 4]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  simp_rw [iteratedDeriv_sourceTerm_eq_normalized]
  rw [tsum_mul_left]
  simp only [normalizedAtomJet_index_zero, mul_zero, zero_add]
  unfold fullJet headJet normalizedTailJet
  rw [rawHeadJet_eq_normalized]
  ring

theorem headJet_abs_le_weight {j : ℕ} (hj : j ≤ 4) {q : ℝ} (hq : Real.pi ≤ q) :
    |headJet j q| ≤ atomCoefficientBound j * q^(j+1) * headGaussianWeight (2*j+4) q := by
  have h1 := normalizedAtomJet_abs_le (n := 1) hj (by norm_num) hq
  have h2 := normalizedAtomJet_abs_le (n := 2) hj (by norm_num) hq
  have h3 := normalizedAtomJet_abs_le (n := 3) hj (by norm_num) hq
  norm_num at h1 h2 h3
  rw [headJet, rawHeadJet_eq_normalized]
  calc
    _ ≤ |normalizedAtomJet j q 1| + |normalizedAtomJet j q 2| + |normalizedAtomJet j q 3| :=
      (abs_add_le _ _).trans (_root_.add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ _ := by
      simp only [headGaussianWeight, neg_mul]
      linear_combination h1+h2+h3

theorem normalizedTailJet_abs_le_weight {j : ℕ} (hj : j ≤ 4)
    {q : ℝ} (hq : Real.pi ≤ q) :
    |normalizedTailJet j q| ≤ atomCoefficientBound j * q^(j+1) *
      ∑' k : ℕ, gaussianTailWeight (2*j+4) q k := by
  have hm : 2*j+4 ≤ 12 := by omega
  have hs := (summable_gaussianTailWeight hm hq).mul_left (atomCoefficientBound j*q^(j+1))
  have ha : Summable (fun k : ℕ => |normalizedAtomJet j q (k+4)|) :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (normalizedAtomJet_tail_abs_le hj hq) hs
  unfold normalizedTailJet
  calc
    _ ≤ ∑' k : ℕ, |normalizedAtomJet j q (k+4)| := by
      simpa only [Real.norm_eq_abs] using
        norm_tsum_le_tsum_norm (f := fun k : ℕ => normalizedAtomJet j q (k+4))
          (by simpa only [Real.norm_eq_abs] using ha)
    _ ≤ ∑' k : ℕ, atomCoefficientBound j*q^(j+1)*gaussianTailWeight (2*j+4) q k :=
      ha.tsum_le_tsum (normalizedAtomJet_tail_abs_le hj hq) hs
    _ = _ := tsum_mul_left

theorem headJet_abs_le {j : ℕ} (hj : j ≤ 4) {q : ℝ} (hq : Real.pi ≤ q) :
    |headJet j q| ≤ (2*atomCoefficientBound j)*q^(j+1) := by
  have hcoef : 0 < atomCoefficientBound j*q^(j+1) :=
    mul_pos (atomCoefficientBound_pos hj) (pow_pos (Real.pi_pos.trans_le hq) _)
  have hweight := headGaussianWeight_lt_two (show 2*j+4 ≤ 12 by omega) hq
  have h := (headJet_abs_le_weight hj hq).trans
    (mul_le_mul_of_nonneg_left hweight.le hcoef.le)
  nlinarith only [h]

theorem fullJet_abs_le {j : ℕ} (hj : j ≤ 4) {q : ℝ} (hq : Real.pi ≤ q) :
    |fullJet j q| ≤ (2*atomCoefficientBound j)*q^(j+1) := by
  have hcoef : 0 < atomCoefficientBound j*q^(j+1) :=
    mul_pos (atomCoefficientBound_pos hj) (pow_pos (Real.pi_pos.trans_le hq) _)
  have hweight := headGaussianWeight_add_tail_lt_two (show 2*j+4 ≤ 12 by omega) hq
  have hs := mul_le_mul_of_nonneg_left hweight.le hcoef.le
  have hh := headJet_abs_le_weight hj hq
  have ht := normalizedTailJet_abs_le_weight hj hq
  unfold fullJet
  have habs := abs_add_le (headJet j q) (normalizedTailJet j q)
  nlinarith only [hs, hh, ht, habs]

theorem scaledHeadJet_abs_le {q : ℝ} (hq : Real.pi ≤ q) {j : ℕ} (hj : j ≤ 4) :
    |scaledHeadJet q j| ≤ 2*atomCoefficientBound j := by
  have hp := pow_pos (Real.pi_pos.trans_le hq) (j+1)
  rw [scaledHeadJet, abs_div, abs_of_pos hp]
  exact (div_le_iff₀ hp).mpr (headJet_abs_le hj hq)

theorem scaledFullJet_abs_le {q : ℝ} (hq : Real.pi ≤ q) {j : ℕ} (hj : j ≤ 4) :
    |scaledFullJet q j| ≤ 2*atomCoefficientBound j := by
  have hp := pow_pos (Real.pi_pos.trans_le hq) (j+1)
  rw [scaledFullJet, abs_div, abs_of_pos hp]
  exact (div_le_iff₀ hp).mpr (fullJet_abs_le hj hq)

/-- The full normalized jet differs from the head by an exponentially small tail. -/
theorem scaledFullJet_sub_head_abs_le {q : ℝ} (hq : Real.pi ≤ q) {j : ℕ} (hj : j ≤ 4) :
    |scaledFullJet q j-scaledHeadJet q j| ≤
      (2*atomCoefficientBound j*4^(2*j+4))*Real.exp (-15*q) := by
  have hp := pow_pos (Real.pi_pos.trans_le hq) (j+1)
  have heq : scaledFullJet q j-scaledHeadJet q j = normalizedTailJet j q / q^(j+1) := by
    unfold scaledFullJet scaledHeadJet fullJet
    ring
  rw [heq, abs_div, abs_of_pos hp]
  apply (div_le_iff₀ hp).mpr
  calc
    _ ≤ 2*atomCoefficientBound j*4^(2*j+4)*q^(j+1)*Real.exp (-15*q) :=
      normalizedTailJet_abs_le hj hq
    _ = _ := by ring

theorem normalizedAtomJet_zero_nonneg {n : ℕ} (hn : 1 ≤ n)
    {q : ℝ} (hq : Real.pi ≤ q) : 0 ≤ normalizedAtomJet 0 q n := by
  have hq3 : 3 ≤ q := by linarith [Real.pi_gt_d2]
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hn2 : (1:ℝ) ≤ (n:ℝ)^2 := by nlinarith
  have hp := mul_le_mul_of_nonneg_left hn2 (show 0 ≤ q by linarith)
  simp only [mul_one] at hp
  have hpoly : 0 ≤ 2*(q*(n:ℝ)^2)-3 := by linarith
  simp only [normalizedAtomJet, atomJetPolynomial, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]
  exact mul_nonneg (mul_nonneg (sq_nonneg _) hpoly) (Real.exp_pos _).le

theorem normalizedTailJet_zero_nonneg {q : ℝ} (hq : Real.pi ≤ q) :
    0 ≤ normalizedTailJet 0 q := by
  exact tsum_nonneg (fun k => normalizedAtomJet_zero_nonneg (show 1 ≤ k+4 by omega) hq)

theorem headJet_zero_ge {q : ℝ} (hq : Real.pi ≤ q) : q ≤ headJet 0 q := by
  have hq3 : 3 ≤ q := by linarith [Real.pi_gt_d2]
  have h2 := mul_nonneg (show 0 ≤ 32*q-12 by linarith) (Real.exp_pos (-3*q)).le
  have h3 := mul_nonneg (show 0 ≤ 162*q-27 by linarith) (Real.exp_pos (-8*q)).le
  rw [headJet, rawHeadJet_zero]
  simp only [eulerJet]
  linarith

theorem fullJet_zero_ge {q : ℝ} (hq : Real.pi ≤ q) : q ≤ fullJet 0 q := by
  have hh := headJet_zero_ge hq
  have ht := normalizedTailJet_zero_nonneg hq
  unfold fullJet
  linarith

end RHTower.ThetaCuspThreeAtomFourth
