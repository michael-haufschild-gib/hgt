import GaloisForLFunctions.ZeroConfigurationGeometry.RightSubstripCutoffsHavePowerTails

/-!
# A power-saving remainder after retaining a right-substrip trace

Truncate the right zeros and smooth the prime count at the same small
power of the argument. The subunit moment controls both the retained
cardinality and the omitted reciprocal mass. The lower strip is paid by
the existing interpolated window estimate.
-/

noncomputable section

open Complex Set
open _root_.RHTower

namespace GaloisForLFunctions.ZeroConfigurationGeometry

private theorem rightNormalizedZeroTerm_eq_div_power {σ β x : ℝ} (hx : 0 < x)
    (q : XiZeroCopy) (hq : σ ≤ (q.1 : ℂ).re) :
    rightNormalizedZeroTerm σ β x q =
      ((x : ℂ) ^ (q.1 : ℂ) / (q.1 : ℂ)) / ((x ^ β : ℝ) : ℂ) := by
  rw [rightNormalizedZeroTerm, if_pos hq,
    Complex.cpow_sub _ _ (by exact_mod_cast hx.ne'), Complex.ofReal_cpow hx.le β]
  ring

/-- Above the critical line, retaining the full right-substrip trace
leaves an actual power saving, even with no gap below the bounding line. -/
theorem exists_power_bound_primeError_add_rightTrace {σ β : ℝ}
    (hσ : 1 / 2 < σ) (hσβ : σ < β) (hβ1 : β ≤ 1)
    (hβ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ β) :
    ∃ κ C x₀ : ℝ, σ < κ ∧ κ < β ∧ 0 ≤ C ∧ ∀ x : ℝ, x₀ ≤ x →
      |Chebyshev.psi x - x + x ^ β * (rightNormalizedZeroTrace σ β x).re| ≤
        C * x ^ κ := by
  classical
  obtain ⟨p, S, hp, hp1, hS, hcut⟩ := exists_rightSubstrip_cutoff_bounds hσ
  let κ := max ((p + 1) / 8) (max (β + (p - 1) / 8) ((β + σ) / 2))
  have hk1 : (p + 1) / 8 ≤ κ := le_max_left _ _
  have hk2 : β + (p - 1) / 8 ≤ κ := (le_max_left _ _).trans (le_max_right _ _)
  have hk3 : (β + σ) / 2 ≤ κ := (le_max_right _ _).trans (le_max_right _ _)
  have hkβ : κ < β := max_lt
    (by linarith only [hp1, hσ, hσβ])
    (max_lt (by linarith only [hp1]) (by linarith only [hσβ]))
  let θ := (β - σ) / 2
  have hθ : 0 < θ := by dsimp only [θ]; linarith only [hσβ]
  have hθ1 : θ ≤ 1 := by dsimp only [θ]; linarith only [hσ, hβ1]
  let W := ∑' q, zeroWeight θ q
  have hW : 0 ≤ W := tsum_nonneg (zeroWeight_nonneg θ)
  have hlog : 0 ≤ Real.log (2 * Real.pi) :=
    Real.log_nonneg (by nlinarith only [Real.pi_gt_three])
  refine ⟨κ, 2 + Real.log (2 * Real.pi) + 5 * S + 16 * W,
    max 4 ((2 : ℝ) ^ (1 / (7 / 8 : ℝ))),
    by linarith only [hk3, hσβ], hkβ, by positivity, ?_⟩
  intro x hx
  have hx4 : 4 ≤ x := (le_max_left _ _).trans hx
  have hx2 : (2 : ℝ) ^ (1 / (7 / 8 : ℝ)) ≤ x := (le_max_right _ _).trans hx
  have hx0 : 0 < x := by linarith only [hx4]
  have hx1 : 1 ≤ x := by linarith only [hx4]
  let H := x ^ (1 / 8 : ℝ)
  have hH : 0 < H := Real.rpow_pos_of_pos hx0 _
  have hH1 : 1 ≤ H := Real.one_le_rpow hx1 (by norm_num)
  have h2 : 2 ≤ x ^ (7 / 8 : ℝ) := by
    have hh := Real.rpow_le_rpow (by positivity) hx2 (by norm_num : (0 : ℝ) ≤ 7 / 8)
    rw [← Real.rpow_mul (by norm_num)] at hh
    norm_num at hh
    exact hh
  have hsplit : H * x ^ (7 / 8 : ℝ) = x := by
    dsimp only [H]
    rw [← Real.rpow_add hx0]
    norm_num
  have hHx : H ≤ x / 2 := by
    rw [le_div_iff₀ (by norm_num)]
    nlinarith only [mul_le_mul_of_nonneg_left h2 hH.le, hsplit]
  obtain ⟨F, hF, hcard, htail⟩ := hcut H hH
  have hxκ : 1 ≤ x ^ κ := Real.one_le_rpow hx1 (by linarith only [hk1, hp])
  have hHκ : H ≤ x ^ κ := Real.rpow_le_rpow_of_exponent_le hx1
    (by linarith only [hk1, hp])
  have hcardH : (F.card : ℝ) * H ≤ S * x ^ κ := by
    calc
      _ ≤ (S * H ^ p) * H := mul_le_mul_of_nonneg_right hcard hH.le
      _ = S * (x ^ ((1 / 8 : ℝ) * p) * x ^ (1 / 8 : ℝ)) := by
        dsimp only [H]
        rw [← Real.rpow_mul hx0.le]
        ring
      _ = S * x ^ ((p + 1) / 8) := by
        rw [← Real.rpow_add hx0]
        congr 2
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hx1 hk1) hS
  have htailβ : x ^ β * (∑' q, rightSubstripTailWeight σ F q) ≤ S * x ^ κ := by
    calc
      _ ≤ x ^ β * (S * H ^ (p - 1)) :=
        mul_le_mul_of_nonneg_left htail (Real.rpow_nonneg hx0.le _)
      _ = S * (x ^ β * x ^ ((1 / 8 : ℝ) * (p - 1))) := by
        dsimp only [H]
        rw [← Real.rpow_mul hx0.le]
        ring
      _ = S * x ^ (β + (p - 1) / 8) := by
        rw [← Real.rpow_add hx0]
        congr 2
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hx1 hk2) hS
  have hratio : (x / H) ^ θ ≤ x ^ θ :=
    Real.rpow_le_rpow (by positivity) (div_le_self hx0.le hH1) hθ.le
  have hlow : 16 * x ^ σ * (x / H) ^ θ * W ≤ 16 * W * x ^ κ := by
    have hpow : x ^ σ * x ^ θ ≤ x ^ κ := by
      rw [← Real.rpow_add hx0]
      apply Real.rpow_le_rpow_of_exponent_le hx1
      have he : σ + θ = (β + σ) / 2 := by dsimp only [θ]; ring
      rw [he]
      exact hk3
    calc
      _ ≤ 16 * x ^ σ * x ^ θ * W :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hratio (by positivity)) hW
      _ = (16 * W) * (x ^ σ * x ^ θ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)
  have hfinite := abs_psi_sub_add_re_finiteSum_le (F := F) hσ hβ hθ hθ1 hx4 hH1 hHx
  have hxβ : 0 < x ^ β := Real.rpow_pos_of_pos hx0 _
  have hR : (∑ q ∈ F, rightNormalizedZeroTerm σ β x q).re =
      (∑ q ∈ F, (x : ℂ) ^ (q.1 : ℂ) / (q.1 : ℂ)).re / x ^ β := by
    rw [Finset.sum_congr rfl fun q hq =>
      rightNormalizedZeroTerm_eq_div_power hx0 q ((hF q).mp hq).1, ← Finset.sum_div]
    simp only [div_eq_mul_inv, ← Complex.ofReal_inv, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
  have htrace : |x ^ β * (rightNormalizedZeroTrace σ β x).re -
      (∑ q ∈ F, (x : ℂ) ^ (q.1 : ℂ) / (q.1 : ℂ)).re| ≤ S * x ^ κ := by
    have hr : |(rightNormalizedZeroTrace σ β x).re -
        (∑ q ∈ F, rightNormalizedZeroTerm σ β x q).re| ≤
          ∑' q, rightSubstripTailWeight σ F q := by
      rw [← Complex.sub_re]
      exact (Complex.abs_re_le_norm _).trans
        (norm_rightNormalizedZeroTrace_sub_sum_le hσ hx1 hβ F)
    have he : x ^ β * (rightNormalizedZeroTrace σ β x).re -
        (∑ q ∈ F, (x : ℂ) ^ (q.1 : ℂ) / (q.1 : ℂ)).re =
        x ^ β * ((rightNormalizedZeroTrace σ β x).re -
          (∑ q ∈ F, rightNormalizedZeroTerm σ β x q).re) := by
      rw [hR]
      field_simp
    rw [he, abs_mul, abs_of_pos hxβ]
    exact (mul_le_mul_of_nonneg_left hr hxβ.le).trans htailβ
  have hlogκ : Real.log (2 * Real.pi) ≤ Real.log (2 * Real.pi) * x ^ κ :=
    le_mul_of_one_le_right hlog hxκ
  have he : Chebyshev.psi x - x + x ^ β * (rightNormalizedZeroTrace σ β x).re =
      (Chebyshev.psi x - x + (∑ q ∈ F, (x : ℂ) ^ (q.1 : ℂ) / (q.1 : ℂ)).re) +
      (x ^ β * (rightNormalizedZeroTrace σ β x).re -
        (∑ q ∈ F, (x : ℂ) ^ (q.1 : ℂ) / (q.1 : ℂ)).re) := by ring
  rw [he]
  apply (abs_add_le _ _).trans
  nlinarith only [hfinite, htrace, hHκ, hxκ, hlogκ, hcardH, htailβ, hlow]

/-- At the actual zero abscissa the full retained substrip has a
power-saving remainder; the upper bound on every zero is supplied. -/
theorem exists_power_bound_primeError_add_actualRightTrace {σ : ℝ}
    (hσ : 1 / 2 < σ) (hσΘ : σ < zetaZeroAbscissa) :
    ∃ κ C x₀ : ℝ, σ < κ ∧ κ < zetaZeroAbscissa ∧ 0 ≤ C ∧ ∀ x : ℝ, x₀ ≤ x →
      |Chebyshev.psi x - x + x ^ zetaZeroAbscissa *
        (rightNormalizedZeroTrace σ zetaZeroAbscissa x).re| ≤ C * x ^ κ :=
  exists_power_bound_primeError_add_rightTrace hσ hσΘ zetaZeroAbscissa_le_one
    (fun q => re_le_zetaZeroAbscissa (riemannZeta_eq_zero_of_xiZeroCopy q))

end GaloisForLFunctions.ZeroConfigurationGeometry
