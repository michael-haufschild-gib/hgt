import GaloisForLFunctions.ExceptionalLayerTheory.GaussianCofactorCorrelationBounds
import GaloisForLFunctions.TransThresholdPairCorrelation.CosineTransformLogarithmicTransport

/-!
# The width of a near-diagonal cofactor row

Rotation and moment order confine normalized Gaussian correlations to width
`W/(t sqrt(r))` among integer cofactors at most `W`. Bernoulli's inequality
reduces the overlap to a Lorentzian; its lattice sum is bounded by a telescoping
affine-square majorant.
-/

open Complex Finset

noncomputable section

namespace GaloisForLFunctions.ExceptionalLayerTheory

private theorem cofactor_relative_gap {m k W : ℝ} (hm : 0 < m) (hk : 0 < k)
    (hmW : m ≤ W) (hkW : k ≤ W) :
    |m - k| / W ≤ |(m ^ 2 - k ^ 2) / (2 * m * k)| := by
  have hW : 0 < W := hm.trans_le hmW
  have hden : 0 < 2 * m * k := by positivity
  have hc : 1 / W ≤ (m + k) / (2 * m * k) := by
    rw [div_le_div_iff₀ hW hden]
    have h1 := mul_le_mul_of_nonneg_left hmW hk.le
    have h2 := mul_le_mul_of_nonneg_left hkW hm.le
    nlinarith only [h1, h2]
  have he : (m ^ 2 - k ^ 2) / (2 * m * k) =
      (m - k) * ((m + k) / (2 * m * k)) := by ring
  rw [he, abs_mul, abs_of_pos (div_pos (add_pos hm hk) hden)]
  simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hc (abs_nonneg (m - k))

/-- Moment order sharpens the near-diagonal quadratic denominator by a factor `r`. -/
theorem gaussianCofactorOverlap_le_lorentzian (r : ℕ) {ε : ℂ} {t m k W : ℝ}
    (hε : 0 < ε.re) (ht : 0 ≤ t) (hm : 0 < m) (hk : 0 < k)
    (hmW : m ≤ W) (hkW : k ≤ W) (hrot : ε.re * t ≤ |ε.im|) :
    gaussianCofactorOverlap r ε m k ≤
      1 / (1 + (r : ℝ) * t ^ 2 * ((m - k) / W) ^ 2) := by
  have hW : 0 < W := hm.trans_le hmW
  have hrot' : t ≤ |ε.im / ε.re| := by
    rw [abs_div, abs_of_pos hε, le_div_iff₀ hε]
    simpa only [mul_comm] using hrot
  have hr2 := pow_le_pow_left₀ ht hrot' 2
  rw [sq_abs] at hr2
  have hgap := pow_le_pow_left₀ (div_nonneg (abs_nonneg _) hW.le)
    (cofactor_relative_gap hm hk hmW hkW) 2
  rw [div_pow, sq_abs, sq_abs] at hgap
  have hgap' : ((m - k) / W) ^ 2 ≤ ((m ^ 2 - k ^ 2) / (2 * m * k)) ^ 2 := by
    simpa only [div_pow] using hgap
  have hbase : t ^ 2 * ((m - k) / W) ^ 2 ≤
      (1 + (ε.im / ε.re) ^ 2) * ((m ^ 2 - k ^ 2) / (2 * m * k)) ^ 2 := by
    have hh := mul_le_mul hr2 hgap' (by positivity) (sq_nonneg (ε.im / ε.re))
    nlinarith only [hh, sq_nonneg ((m ^ 2 - k ^ 2) / (2 * m * k))]
  have hB := one_add_mul_le_pow
    (a := (1 + (ε.im / ε.re) ^ 2) * ((m ^ 2 - k ^ 2) / (2 * m * k)) ^ 2)
    (by
      have hp : 0 ≤ (1 + (ε.im / ε.re) ^ 2) *
        ((m ^ 2 - k ^ 2) / (2 * m * k)) ^ 2 := by positivity
      linarith only [hp]) r
  have hden : 1 + (r : ℝ) * t ^ 2 * ((m - k) / W) ^ 2 ≤
      (1 + (1 + (ε.im / ε.re) ^ 2) * ((m ^ 2 - k ^ 2) / (2 * m * k)) ^ 2) ^ r := by
    have hh := mul_le_mul_of_nonneg_left hbase (Nat.cast_nonneg r : (0 : ℝ) ≤ r)
    nlinarith only [hB, hh]
  rw [gaussianCofactorOverlap_eq r hε hm hk, inv_pow, one_div]
  exact inv_anti₀ (by positivity) hden

private theorem lorentzian_le_affine_square (y : ℝ) :
    1 / (1 + y ^ 2) ≤ 2 / (1 + |y|) ^ 2 := by
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith only [sq_nonneg (|y| - 1), sq_abs y]

private theorem sum_positive_lorentzian_le {α : ℝ} (hα : 0 < α) (L : ℕ) :
    (∑ j ∈ range L, 1 / (1 + (α * ((j : ℝ) + 1)) ^ 2)) ≤ 2 / α := by
  calc
    _ ≤ ∑ j ∈ range L, 2 / (1 + α * ((j : ℝ) + 1)) ^ 2 := by
      apply sum_le_sum
      intro j _
      have hp : 0 < α * ((j : ℝ) + 1) := by positivity
      simpa only [abs_of_pos hp] using
        lorentzian_le_affine_square (α * ((j : ℝ) + 1))
    _ = 2 * ∑ j ∈ range L, 1 / (1 + α * ((j : ℝ) + 1)) ^ 2 := by
      rw [mul_sum]
      apply sum_congr rfl
      intro j _
      ring
    _ ≤ 2 * (1 / α) := mul_le_mul_of_nonneg_left
      (TransThresholdPairCorrelation.sum_inverse_square_affine_le hα L) (by norm_num)
    _ = _ := by ring

private theorem sum_lorentzian_natDist_le {α : ℝ} (hα : 0 < α) (M i : ℕ) :
    (∑ j ∈ range M, 1 / (1 + (α * (Nat.dist i j : ℝ)) ^ 2)) ≤ 1 + 4 / α := by
  let f : ℕ → ℝ := fun d => 1 / (1 + (α * (d : ℝ)) ^ 2)
  have hf (d : ℕ) : 0 ≤ f d := by dsimp [f]; positivity
  have hsplit (j : ℕ) : f (Nat.dist i j) =
      (if j = i then 1 else 0) + (if j < i then f (i - j) else 0) +
        (if i < j then f (j - i) else 0) := by
    rcases lt_trichotomy j i with h | rfl | h
    · rw [if_neg h.ne, if_pos h, if_neg (by omega), Nat.dist_comm i j,
        Nat.dist_eq_sub_of_le h.le]
      ring
    · simp [f]
    · rw [if_neg h.ne', if_neg (by omega), if_pos h, Nat.dist_eq_sub_of_le h.le]
      ring
  have hleft : (∑ j ∈ range M, if j < i then f (i - j) else 0) ≤
      ∑ d ∈ range (M + i), f (d + 1) := by
    rw [← sum_filter]
    calc
      _ = ∑ d ∈ ((range M).filter (· < i)).image (fun j => i - j - 1), f (d + 1) := by
        rw [sum_image]
        · apply sum_congr rfl
          intro j hj
          have := (mem_filter.mp hj).2
          congr 1
          omega
        · intro a ha b hb hab
          have := (mem_filter.mp ha).2
          have := (mem_filter.mp hb).2
          dsimp only at hab
          omega
      _ ≤ _ := by
        apply sum_le_sum_of_subset_of_nonneg _ (fun d _ _ => hf _)
        intro d hd
        obtain ⟨j, hj, rfl⟩ := mem_image.mp hd
        have := (mem_filter.mp hj).2
        exact mem_range.mpr (by omega)
  have hright : (∑ j ∈ range M, if i < j then f (j - i) else 0) ≤
      ∑ d ∈ range (M + i), f (d + 1) := by
    rw [← sum_filter]
    calc
      _ = ∑ d ∈ ((range M).filter (i < ·)).image (fun j => j - i - 1), f (d + 1) := by
        rw [sum_image]
        · apply sum_congr rfl
          intro j hj
          have := (mem_filter.mp hj).2
          congr 1
          omega
        · intro a ha b hb hab
          have := (mem_filter.mp ha).2
          have := (mem_filter.mp hb).2
          dsimp only at hab
          omega
      _ ≤ _ := by
        apply sum_le_sum_of_subset_of_nonneg _ (fun d _ _ => hf _)
        intro d hd
        obtain ⟨j, hj, rfl⟩ := mem_image.mp hd
        have := mem_range.mp (mem_filter.mp hj).1
        exact mem_range.mpr (by omega)
  have hdiag : (∑ j ∈ range M, if j = i then (1 : ℝ) else 0) ≤ 1 := by
    simp only [sum_ite_eq']
    split_ifs <;> norm_num
  have hs : (∑ d ∈ range (M + i), f (d + 1)) ≤ 2 / α := by
    simpa only [f, Nat.cast_add, Nat.cast_one] using sum_positive_lorentzian_le hα (M + i)
  change (∑ j ∈ range M, f (Nat.dist i j)) ≤ _
  simp_rw [hsplit, sum_add_distrib]
  calc
    _ ≤ (1 + 2 / α) + 2 / α :=
      add_le_add (add_le_add hdiag (hleft.trans hs)) (hright.trans hs)
    _ = _ := by ring

/-- Every normalized cofactor row has width `W/(t sqrt(r))`, including its diagonal. -/
theorem sum_gaussianCofactorOverlap_le {r W m : ℕ} (hr : 1 ≤ r) (hm : 1 ≤ m) (hmW : m ≤ W)
    {ε : ℂ} {t : ℝ} (hε : 0 < ε.re) (ht : 0 < t) (hrot : ε.re * t ≤ |ε.im|) :
    (∑ j ∈ range W, gaussianCofactorOverlap r ε (m : ℝ) ((j + 1 : ℕ) : ℝ)) ≤
      1 + 4 * (W : ℝ) / (t * Real.sqrt r) := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hr
  have hm0 : (0 : ℝ) < m := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hm
  have hW0 : (0 : ℝ) < W := hm0.trans_le (by exact_mod_cast hmW)
  let α : ℝ := t * Real.sqrt r / W
  have hα : 0 < α := div_pos (mul_pos ht (Real.sqrt_pos.mpr hr0)) hW0
  have hd (j : ℕ) : ((Nat.dist (m - 1) j : ℕ) : ℝ) ^ 2 =
      ((m : ℝ) - ((j + 1 : ℕ) : ℝ)) ^ 2 := by
    have hmcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by rw [Nat.cast_sub hm, Nat.cast_one]
    rcases le_total (m - 1) j with hj | hj
    · rw [Nat.dist_eq_sub_of_le hj, Nat.cast_sub hj, hmcast]
      push_cast
      ring
    · rw [Nat.dist_comm (m - 1) j, Nat.dist_eq_sub_of_le hj, Nat.cast_sub hj, hmcast]
      push_cast
      ring
  calc
    _ ≤ ∑ j ∈ range W, 1 / (1 + (α * (Nat.dist (m - 1) j : ℝ)) ^ 2) := by
      apply sum_le_sum
      intro j hj
      have hjW : j + 1 ≤ W := by have := mem_range.mp hj; omega
      have hh := gaussianCofactorOverlap_le_lorentzian r (W := (W : ℝ)) hε ht.le hm0
        (by positivity : (0 : ℝ) < ((j + 1 : ℕ) : ℝ))
        (by exact_mod_cast hmW) (by exact_mod_cast hjW) hrot
      refine hh.trans_eq ?_
      congr 2
      rw [mul_pow, hd]
      dsimp only [α]
      simp only [div_pow, mul_pow, Real.sq_sqrt hr0.le]
      ring
    _ ≤ 1 + 4 / α := sum_lorentzian_natDist_le hα W (m - 1)
    _ = _ := by dsimp only [α]; field_simp

/-- The same row bound holds for the complete lattice correlations, with the
Bernoulli discretization error paid once per cofactor. -/
theorem sum_normalized_gaussian_pair_le {r W m : ℕ} (hr : 1 ≤ r) (hm : 1 ≤ m) (hmW : m ≤ W)
    {ε : ℂ} {t : ℝ} (hε : 0 < ε.re) (ht : 1 ≤ t)
    (hsector : ‖ε‖ ≤ 4 * ε.re * t) (hrot : ε.re * t ≤ |ε.im|) :
    (∑ j ∈ range W,
      ‖∑' d : ℕ, gaussianHigherPrimeMomentWeight r (1 / 2) t ε (m * (d + 1)) *
        (starRingEnd ℂ) (gaussianHigherPrimeMomentWeight r (1 / 2) t ε ((j + 1) * (d + 1)))‖ /
          gaussianCofactorCorrelationScale r t ε m (j + 1)) ≤
      1 + 4 * (W : ℝ) / (t * Real.sqrt r) +
        (W : ℝ) * (2048 * (r : ℝ) ^ 3 * ε.re * t ^ 2 * (W : ℝ) ^ 2) ^ r := by
  have hrow := sum_gaussianCofactorOverlap_le hr hm hmW hε (zero_lt_one.trans_le ht) hrot
  have hpoint (j : ℕ) (hj : j ∈ range W) :
      ‖∑' d : ℕ, gaussianHigherPrimeMomentWeight r (1 / 2) t ε (m * (d + 1)) *
        (starRingEnd ℂ) (gaussianHigherPrimeMomentWeight r (1 / 2) t ε ((j + 1) * (d + 1)))‖ /
          gaussianCofactorCorrelationScale r t ε m (j + 1) ≤
      gaussianCofactorOverlap r ε m (j + 1) +
        (2048 * (r : ℝ) ^ 3 * ε.re * t ^ 2 * (W : ℝ) ^ 2) ^ r := by
    have hm0 : 0 < m := lt_of_lt_of_le Nat.zero_lt_one hm
    have hjW : j + 1 ≤ W := by have := mem_range.mp hj; omega
    have hS := gaussianCofactorCorrelationScale_nonneg r t hε
      (show (0 : ℝ) < m by exact_mod_cast hm0) (by positivity : (0 : ℝ) < j + 1)
    rcases eq_or_lt_of_le hS with hS | hS
    · rw [← hS, div_zero]
      exact add_nonneg (gaussianCofactorOverlap_nonneg _ _ _ _) (by positivity)
    · rw [div_le_iff₀ hS, mul_comm]
      simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_succ] using
        norm_tsum_gaussianHigherPrimeMoment_pair_le (r := r) (W := (W : ℝ))
        (by omega) ht hε hsector hm0
        (Nat.succ_pos j) (by exact_mod_cast hmW) (by exact_mod_cast hjW)
  calc
    _ ≤ ∑ j ∈ range W, (gaussianCofactorOverlap r ε m (j + 1) +
        (2048 * (r : ℝ) ^ 3 * ε.re * t ^ 2 * (W : ℝ) ^ 2) ^ r) := sum_le_sum hpoint
    _ = (∑ j ∈ range W, gaussianCofactorOverlap r ε m (j + 1)) +
        (W : ℝ) * (2048 * (r : ℝ) ^ 3 * ε.re * t ^ 2 * (W : ℝ) ^ 2) ^ r := by
      rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul]
    _ ≤ _ := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        add_le_add hrow (le_refl ((W : ℝ) *
          (2048 * (r : ℝ) ^ 3 * ε.re * t ^ 2 * (W : ℝ) ^ 2) ^ r))

end GaloisForLFunctions.ExceptionalLayerTheory
