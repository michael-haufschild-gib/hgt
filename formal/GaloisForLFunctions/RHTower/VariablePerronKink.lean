import GaloisForLFunctions.RHTower.QuietCrossingRigidity
import GaloisForLFunctions.RHTower.QuietFlankGrowth

/-!
# Variable-width Perron kinks

The fixed quiet-crossing kernel uses the three knots `n+1/2,n,n-1/2` and isolates `a n / 2`.
There is no reason to freeze the width.  For every `0 < δ < 1`, the knots
`n+δ,n,n-δ` isolate exactly `δ * a n`, while the left-edge frequency scale improves from
`n-1/2` to `n-δ`.

This module constructs that variable kernel and proves the finite identity consumed by
`HasVariableQuietFlankCoefficientBound` in `QuietFlankGrowth.lean`.
-/

noncomputable section

namespace RHTower

open Complex MeasureTheory Filter Topology Asymptotics intervalIntegral Set

/-- The variable-width Perron numerator at the three knots `n+δ,n,n-δ`. -/
def perronKinkAt (n : ℕ) (δ : ℝ) (s : ℂ) : ℂ :=
    (((n : ℝ) + δ : ℝ) : ℂ) ^ (s + 1) + (((n : ℝ) - δ : ℝ) : ℂ) ^ (s + 1)
      - 2 * (((n : ℝ) : ℝ) : ℂ) ^ (s + 1)

/-- The fixed half-width numerator is the specialization `δ=1/2`. -/
theorem perronKinkAt_oneHalf_eq (n : ℕ) : perronKinkAt n (1 / 2) = perronKink n := rfl

/-- The variable numerator vanishes at the first removable pole `s=0`. -/
theorem perronKinkAt_zero (n : ℕ) (δ : ℝ) : perronKinkAt n δ 0 = 0 := by
  unfold perronKinkAt
  rw [show (0 : ℂ) + 1 = 1 by ring, Complex.cpow_one, Complex.cpow_one, Complex.cpow_one]
  push_cast
  ring

/-- The variable numerator vanishes at the second removable pole `s=-1`. -/
theorem perronKinkAt_negOne (n : ℕ) (δ : ℝ) : perronKinkAt n δ (-1) = 0 := by
  unfold perronKinkAt
  rw [show (-1 : ℂ) + 1 = 0 by ring, Complex.cpow_zero, Complex.cpow_zero,
    Complex.cpow_zero]
  ring

/-- The variable numerator is entire when all three real bases are positive. -/
theorem perronKinkAt_differentiable {n : ℕ} {δ : ℝ}
    (hn : 1 ≤ n) (hδ0 : 0 < δ) (hδn : δ < (n : ℝ)) :
    Differentiable ℂ (perronKinkAt n δ) := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hb1 : ((((n : ℝ) + δ : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast ne_of_gt (show (0 : ℝ) < (n : ℝ) + δ by linarith)
  have hb2 : ((((n : ℝ) - δ : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast ne_of_gt (sub_pos.mpr hδn)
  have hb3 : ((((n : ℝ) : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast ne_of_gt (show (0 : ℝ) < (n : ℝ) by linarith)
  have d1 : Differentiable ℂ (fun s : ℂ => (((n : ℝ) + δ : ℝ) : ℂ) ^ (s + 1)) :=
    fun s => (differentiableAt_id.add_const 1).const_cpow (Or.inl hb1)
  have d2 : Differentiable ℂ (fun s : ℂ => (((n : ℝ) - δ : ℝ) : ℂ) ^ (s + 1)) :=
    fun s => (differentiableAt_id.add_const 1).const_cpow (Or.inl hb2)
  have d3 : Differentiable ℂ (fun s : ℂ => (((n : ℝ) : ℝ) : ℂ) ^ (s + 1)) :=
    fun s => (differentiableAt_id.add_const 1).const_cpow (Or.inl hb3)
  exact (d1.add d2).sub (d3.const_mul 2)

/-- The variable entire regularization, obtained by removing the zeros at `0` and `-1`. -/
def perronEAt (n : ℕ) (δ : ℝ) : ℂ → ℂ :=
  dslope (dslope (perronKinkAt n δ) 0) (-1)

/-- The fixed half-width regularization is the specialization `δ=1/2`. -/
theorem perronEAt_oneHalf_eq (n : ℕ) : perronEAt n (1 / 2) = perronE n := rfl

/-- The variable regularized kernel is entire. -/
theorem perronEAt_differentiable {n : ℕ} {δ : ℝ}
    (hn : 1 ≤ n) (hδ0 : 0 < δ) (hδn : δ < (n : ℝ)) :
    Differentiable ℂ (perronEAt n δ) := by
  have g1 : Differentiable ℂ (dslope (perronKinkAt n δ) 0) := by
    rw [← differentiableOn_univ, differentiableOn_dslope Filter.univ_mem]
    exact (perronKinkAt_differentiable hn hδ0 hδn).differentiableOn
  unfold perronEAt
  rw [← differentiableOn_univ, differentiableOn_dslope Filter.univ_mem]
  exact g1.differentiableOn

/-- Away from the removable poles, the variable kernel is its numerator divided by `s(s+1)`. -/
theorem perronEAt_eq (n : ℕ) (δ : ℝ) {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ -1) :
    perronEAt n δ s = perronKinkAt n δ s / (s * (s + 1)) := by
  have e0 : dslope (perronKinkAt n δ) 0 s = perronKinkAt n δ s / s := by
    rw [dslope_of_ne _ h0, slope_def_field, perronKinkAt_zero, sub_zero, sub_zero]
  have em1 : dslope (perronKinkAt n δ) 0 (-1) = 0 := by
    rw [dslope_of_ne _ (by norm_num : (-1 : ℂ) ≠ 0), slope_def_field,
      perronKinkAt_zero, perronKinkAt_negOne, sub_zero, zero_div]
  unfold perronEAt
  rw [dslope_of_ne _ h1, slope_def_field, e0, em1, sub_zero, sub_neg_eq_add, div_div]

/-- Uniform triangle bound for the variable numerator. -/
theorem perronKinkAt_norm_le {n : ℕ} {δ : ℝ}
    (hn : 1 ≤ n) (hδ0 : 0 < δ) (hδn : δ < (n : ℝ)) (s : ℂ) :
    ‖perronKinkAt n δ s‖ ≤ ((n : ℝ) + δ) ^ (s.re + 1) + ((n : ℝ) - δ) ^ (s.re + 1)
      + 2 * ((n : ℝ)) ^ (s.re + 1) := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hb1 : (0 : ℝ) < (n : ℝ) + δ := by linarith
  have hb2 : (0 : ℝ) < (n : ℝ) - δ := sub_pos.mpr hδn
  have hb3 : (0 : ℝ) < (n : ℝ) := by linarith
  have hre : (s + 1).re = s.re + 1 := by rw [Complex.add_re, Complex.one_re]
  have n1 : ‖(((n : ℝ) + δ : ℝ) : ℂ) ^ (s + 1)‖ = ((n : ℝ) + δ) ^ (s.re + 1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hb1, hre]
  have n2 : ‖(((n : ℝ) - δ : ℝ) : ℂ) ^ (s + 1)‖ = ((n : ℝ) - δ) ^ (s.re + 1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hb2, hre]
  have n3 : ‖(((n : ℝ) : ℝ) : ℂ) ^ (s + 1)‖ = ((n : ℝ)) ^ (s.re + 1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hb3, hre]
  unfold perronKinkAt
  calc
    ‖(((n : ℝ) + δ : ℝ) : ℂ) ^ (s + 1) + (((n : ℝ) - δ : ℝ) : ℂ) ^ (s + 1)
        - 2 * (((n : ℝ) : ℝ) : ℂ) ^ (s + 1)‖
        ≤ ‖(((n : ℝ) + δ : ℝ) : ℂ) ^ (s + 1) + (((n : ℝ) - δ : ℝ) : ℂ) ^ (s + 1)‖
          + ‖2 * (((n : ℝ) : ℝ) : ℂ) ^ (s + 1)‖ := norm_sub_le _ _
    _ ≤ (‖(((n : ℝ) + δ : ℝ) : ℂ) ^ (s + 1)‖ +
          ‖(((n : ℝ) - δ : ℝ) : ℂ) ^ (s + 1)‖)
          + ‖2 * (((n : ℝ) : ℝ) : ℂ) ^ (s + 1)‖ := by
            gcongr
            exact norm_add_le _ _
    _ = ((n : ℝ) + δ) ^ (s.re + 1) + ((n : ℝ) - δ) ^ (s.re + 1)
          + 2 * ((n : ℝ)) ^ (s.re + 1) := by
      rw [norm_mul, n1, n2, n3]
      simp only [Complex.norm_ofNat]

/-- **Variable Perron kink identity.**  For `0 < δ < 1`, the second difference of the smoothed
Perron sums at `n+δ,n,n-δ` is exactly `δ * a n`.  Earlier integer indices lie in the affine region
of all three weights; later integer indices lie beyond `n+δ`; only `m=n` survives. -/
theorem perronKinkAt_second_difference (a : ℕ → ℂ) {n : ℕ} {δ : ℝ}
    (hn : 1 ≤ n) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (∑' m : ℕ, (if m = 0 then (0 : ℂ) else
        a m * ((max (((n : ℝ) + δ) - m) 0 : ℝ) : ℂ)))
      + (∑' m : ℕ, (if m = 0 then (0 : ℂ) else
        a m * ((max (((n : ℝ) - δ) - m) 0 : ℝ) : ℂ)))
      - 2 * (∑' m : ℕ, (if m = 0 then (0 : ℂ) else
        a m * ((max ((n : ℝ) - m) 0 : ℝ) : ℂ)))
      = a n * (δ : ℂ) := by
  have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn
  have hvanish : ∀ (x : ℝ), x ≤ (n : ℝ) + δ →
      ∀ m ∉ Finset.range (n + 1),
        (if m = 0 then (0 : ℂ) else a m * ((max (x - m) 0 : ℝ) : ℂ)) = 0 := by
    intro x hx m hm
    rw [Finset.mem_range, not_lt] at hm
    have hmn : (n : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hm
    have hle : x - (m : ℝ) ≤ 0 := by linarith
    rw [max_eq_right hle]
    simp
  rw [tsum_eq_sum (hvanish _ (le_refl _)),
      tsum_eq_sum (hvanish _ (by linarith)),
      tsum_eq_sum (hvanish _ (by linarith))]
  rw [show (∑ m ∈ Finset.range (n + 1),
            (if m = 0 then (0 : ℂ) else a m * ((max (((n : ℝ) + δ) - m) 0 : ℝ) : ℂ)))
          + (∑ m ∈ Finset.range (n + 1),
            (if m = 0 then (0 : ℂ) else a m * ((max (((n : ℝ) - δ) - m) 0 : ℝ) : ℂ)))
          - 2 * (∑ m ∈ Finset.range (n + 1),
            (if m = 0 then (0 : ℂ) else a m * ((max ((n : ℝ) - m) 0 : ℝ) : ℂ)))
        = ∑ m ∈ Finset.range (n + 1),
            ((if m = 0 then (0 : ℂ) else a m * ((max (((n : ℝ) + δ) - m) 0 : ℝ) : ℂ))
              + (if m = 0 then (0 : ℂ) else a m * ((max (((n : ℝ) - δ) - m) 0 : ℝ) : ℂ))
              - 2 * (if m = 0 then (0 : ℂ) else a m * ((max ((n : ℝ) - m) 0 : ℝ) : ℂ)))
        from by rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]]
  rw [Finset.sum_eq_single n]
  · rw [if_neg hn0, if_neg hn0, if_neg hn0]
    have e1 : ((n : ℝ) + δ) - n = δ := by ring
    have e2 : ((n : ℝ) - δ) - n = -δ := by ring
    have e3 : (n : ℝ) - n = 0 := by ring
    rw [e1, e2, e3, max_eq_left hδ0.le, max_eq_right (neg_nonpos.mpr hδ0.le), max_self]
    push_cast
    ring
  · intro m hmem hmn
    rcases Nat.eq_zero_or_pos m with hm0 | hm0
    · subst hm0
      simp
    · have hmlt : m < n := lt_of_le_of_ne
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hmem)) hmn
      have hmr : (m : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hmlt
      rw [if_neg hm0.ne', if_neg hm0.ne', if_neg hm0.ne',
          max_eq_left (by linarith : (0 : ℝ) ≤ ((n : ℝ) + δ) - m),
          max_eq_left (by linarith : (0 : ℝ) ≤ ((n : ℝ) - δ) - m),
          max_eq_left (by linarith : (0 : ℝ) ≤ (n : ℝ) - m)]
      push_cast
      ring
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self n)) h

/-- **Variable-width Perron integral representation.**  For `0 < δ < 1`, the exact
coefficient extraction `δ * a n` equals the vertical integral of the entire variable regularization
`perronEAt n δ`.  The proof combines the three smoothed Perron identities and uses the already
formalized Mellin integrability of `1/(s(s+1))` to justify the integral algebra. -/
theorem perronSecondDiffAt_integral {F : ℂ → ℂ} {a : ℕ → ℂ} {c : ℝ}
    (hc0 : 0 < c) (hsum : LSeriesSummable a c) (hF : Differentiable ℂ F)
    (hFeq : ∀ s : ℂ, c ≤ s.re → F s = LSeries a s)
    {n : ℕ} {δ : ℝ} (hn : 1 ≤ n) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    a n * (δ : ℂ)
      = (1 / (2 * Real.pi) : ℝ) •
          ∫ t : ℝ, F ((c : ℂ) + ↑t * I) * perronEAt n δ ((c : ℂ) + ↑t * I) := by
  obtain ⟨B, hB⟩ := lseries_bounded_on_halfplane hsum
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hxp : (0 : ℝ) < (n : ℝ) + δ := by linarith
  have hx0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hxm : (0 : ℝ) < (n : ℝ) - δ := by linarith
  have hrec : ∀ t : ℝ, ((c : ℂ) + ↑t * I).re = c := fun t => by simp
  have hle : ∀ t : ℝ, c ≤ ((c : ℂ) + ↑t * I).re := fun t => le_of_eq (hrec t).symm
  have hLF : ∀ t : ℝ, LSeries a ((c : ℂ) + ↑t * I) = F ((c : ℂ) + ↑t * I) := fun t =>
    (hFeq _ (hle t)).symm
  have hB0 : (0 : ℝ) ≤ B := le_trans (norm_nonneg _) (hB ↑c (by rw [Complex.ofReal_re]))
  have hKernelInt : Integrable (fun t : ℝ => mellin perronKernelG (↑c + ↑t * I)) := by
    exact perronKernel_verticalIntegrable hc0
  have hIntKnot : ∀ x : ℝ, 0 < x → Integrable (fun t : ℝ =>
      LSeries a ((c : ℂ) + ↑t * I) *
        ((↑x : ℂ) ^ (((c : ℂ) + ↑t * I) + 1) /
          (((c : ℂ) + ↑t * I) * (((c : ℂ) + ↑t * I) + 1)))) := by
    intro x hx
    have hxc : (↑x : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hx
    have heqint : (fun t : ℝ =>
        LSeries a ((c : ℂ) + ↑t * I) *
          ((↑x : ℂ) ^ (((c : ℂ) + ↑t * I) + 1) /
            (((c : ℂ) + ↑t * I) * (((c : ℂ) + ↑t * I) + 1)))) =
        fun t : ℝ => F ((c : ℂ) + ↑t * I) *
          (↑x : ℂ) ^ (((c : ℂ) + ↑t * I) + 1) *
            mellin perronKernelG ((c : ℂ) + ↑t * I) := by
      funext t
      rw [hLF t, perronKernel_mellin (by simpa [hrec t] using hc0)]
      ring
    have hmeas : AEStronglyMeasurable (fun t : ℝ =>
        LSeries a ((c : ℂ) + ↑t * I) *
          ((↑x : ℂ) ^ (((c : ℂ) + ↑t * I) + 1) /
            (((c : ℂ) + ↑t * I) * (((c : ℂ) + ↑t * I) + 1)))) := by
      rw [heqint]
      exact ((hF.continuous.comp (by fun_prop)).mul
        (Continuous.const_cpow (by fun_prop) (Or.inl hxc))).aestronglyMeasurable.mul
          hKernelInt.aestronglyMeasurable
    have hbound : ∀ t : ℝ,
        ‖LSeries a ((c : ℂ) + ↑t * I) *
          ((↑x : ℂ) ^ (((c : ℂ) + ↑t * I) + 1) /
            (((c : ℂ) + ↑t * I) * (((c : ℂ) + ↑t * I) + 1)))‖
          ≤ (B * x ^ (c + 1)) * ‖mellin perronKernelG ((c : ℂ) + ↑t * I)‖ := by
      intro t
      have h1 : ‖LSeries a ((c : ℂ) + ↑t * I)‖ ≤ B := hB _ (hle t)
      have h2 : ‖(↑x : ℂ) ^ (((c : ℂ) + ↑t * I) + 1)‖ = x ^ (c + 1) := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.add_re, Complex.one_re, hrec]
      have hinv0 : 0 ≤ ‖((c : ℂ) + ↑t * I) * (((c : ℂ) + ↑t * I) + 1)‖⁻¹ :=
        inv_nonneg.mpr (norm_nonneg _)
      rw [norm_mul, norm_div, h2, div_eq_mul_inv,
        perronKernel_mellin (by simpa [hrec t] using hc0), one_div, norm_inv]
      simpa [mul_assoc] using mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hx.le (c + 1))) hinv0
    exact (hKernelInt.norm.const_mul (B * x ^ (c + 1))).mono'
      hmeas (Eventually.of_forall hbound)
  have hpt : ∀ t : ℝ, F ((c : ℂ) + ↑t * I) * perronEAt n δ ((c : ℂ) + ↑t * I)
      = LSeries a ((c : ℂ) + ↑t * I) *
          ((↑((n : ℝ) + δ) : ℂ) ^ (((c : ℂ) + ↑t * I) + 1) /
            (((c : ℂ) + ↑t * I) * (((c : ℂ) + ↑t * I) + 1)))
        + LSeries a ((c : ℂ) + ↑t * I) *
          ((↑((n : ℝ) - δ) : ℂ) ^ (((c : ℂ) + ↑t * I) + 1) /
            (((c : ℂ) + ↑t * I) * (((c : ℂ) + ↑t * I) + 1)))
        - 2 * (LSeries a ((c : ℂ) + ↑t * I) *
          ((↑((n : ℝ)) : ℂ) ^ (((c : ℂ) + ↑t * I) + 1) /
            (((c : ℂ) + ↑t * I) * (((c : ℂ) + ↑t * I) + 1)))) := by
    intro t
    have hs0 : ((c : ℂ) + ↑t * I) ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      rw [hrec] at this
      simp at this
      linarith
    have hs1 : ((c : ℂ) + ↑t * I) ≠ -1 := by
      intro h
      have := congrArg Complex.re h
      rw [hrec] at this
      simp at this
      linarith
    rw [← hLF t, perronEAt_eq n δ hs0 hs1]
    unfold perronKinkAt
    ring
  rw [← perronKinkAt_second_difference a hn hδ0 hδ1]
  rw [smoothed_perron_sum hc0 hsum hxp, smoothed_perron_sum hc0 hsum hxm,
      smoothed_perron_sum hc0 hsum hx0]
  have hcomb : (∫ t : ℝ, F ((c : ℂ) + ↑t * I) * perronEAt n δ ((c : ℂ) + ↑t * I))
      = (∫ t : ℝ, LSeries a ((c : ℂ) + ↑t * I) *
            ((↑((n : ℝ) + δ) : ℂ) ^ (((c : ℂ) + ↑t * I) + 1) /
              (((c : ℂ) + ↑t * I) * (((c : ℂ) + ↑t * I) + 1))))
        + (∫ t : ℝ, LSeries a ((c : ℂ) + ↑t * I) *
            ((↑((n : ℝ) - δ) : ℂ) ^ (((c : ℂ) + ↑t * I) + 1) /
              (((c : ℂ) + ↑t * I) * (((c : ℂ) + ↑t * I) + 1))))
        - 2 * (∫ t : ℝ, LSeries a ((c : ℂ) + ↑t * I) *
            ((↑((n : ℝ)) : ℂ) ^ (((c : ℂ) + ↑t * I) + 1) /
              (((c : ℂ) + ↑t * I) * (((c : ℂ) + ↑t * I) + 1)))) := by
    calc
      (∫ t : ℝ, F ((c : ℂ) + ↑t * I) * perronEAt n δ ((c : ℂ) + ↑t * I))
          = ∫ t : ℝ, (LSeries a ((c : ℂ) + ↑t * I) *
                ((↑((n : ℝ) + δ) : ℂ) ^ (((c : ℂ) + ↑t * I) + 1) /
                  (((c : ℂ) + ↑t * I) * (((c : ℂ) + ↑t * I) + 1)))
              + LSeries a ((c : ℂ) + ↑t * I) *
                ((↑((n : ℝ) - δ) : ℂ) ^ (((c : ℂ) + ↑t * I) + 1) /
                  (((c : ℂ) + ↑t * I) * (((c : ℂ) + ↑t * I) + 1)))
              - 2 * (LSeries a ((c : ℂ) + ↑t * I) *
                ((↑((n : ℝ)) : ℂ) ^ (((c : ℂ) + ↑t * I) + 1) /
                  (((c : ℂ) + ↑t * I) * (((c : ℂ) + ↑t * I) + 1))))) :=
            MeasureTheory.integral_congr_ae (Eventually.of_forall hpt)
      _ = (∫ t : ℝ, (LSeries a ((c : ℂ) + ↑t * I) *
                ((↑((n : ℝ) + δ) : ℂ) ^ (((c : ℂ) + ↑t * I) + 1) /
                  (((c : ℂ) + ↑t * I) * (((c : ℂ) + ↑t * I) + 1)))
              + LSeries a ((c : ℂ) + ↑t * I) *
                ((↑((n : ℝ) - δ) : ℂ) ^ (((c : ℂ) + ↑t * I) + 1) /
                  (((c : ℂ) + ↑t * I) * (((c : ℂ) + ↑t * I) + 1)))))
            - ∫ t : ℝ, 2 * (LSeries a ((c : ℂ) + ↑t * I) *
                ((↑((n : ℝ)) : ℂ) ^ (((c : ℂ) + ↑t * I) + 1) /
                  (((c : ℂ) + ↑t * I) * (((c : ℂ) + ↑t * I) + 1)))) :=
            MeasureTheory.integral_sub ((hIntKnot _ hxp).add (hIntKnot _ hxm))
              ((hIntKnot _ hx0).const_mul 2)
      _ = _ := by
        rw [MeasureTheory.integral_add (hIntKnot _ hxp) (hIntKnot _ hxm),
          MeasureTheory.integral_const_mul]
  rw [hcomb]
  simp only [Complex.real_smul]
  ring


end RHTower
