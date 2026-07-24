import GaloisForLFunctions.RHTower.ZetaTruncatedExtension
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Low-height zero-freeness of ζ near `Re s = 1`

Two facts closing the `|t| ≤ 9` gap of the logarithmic zero-free
region.  Near the pole, `ζ(s) = 1 + 1/(s-1) - s·tail(s)` forces
`‖ζ(s)‖ ≥ 8 - 16/7 > 0` on `0 < ‖s-1‖ ≤ 1/8`.  Off the pole, the
zeros of `ζ` in the compact box `[7/8,1]×[-9,9] ∖ B(1,1/8)` cannot
accumulate on the line `Re s = 1` (where `ζ ≠ 0`), so some margin
`δ > 0` is zero-free — by sequential compactness.
-/

noncomputable section

namespace RHTower

open MeasureTheory Set Filter

/-- **ζ does not vanish near its pole**: `ζ(s) ≠ 0` for
`0 < ‖s-1‖ ≤ 1/8`. -/
theorem riemannZeta_ne_zero_of_near_one {s : ℂ} (hs : s ≠ 1)
    (hd : ‖s - 1‖ ≤ 1 / 8) : riemannZeta s ≠ 0 := by
  intro h0
  have hd0 : 0 < ‖s - 1‖ := by
    rw [norm_pos_iff]
    exact sub_ne_zero.2 hs
  have hre : 7 / 8 ≤ s.re := by
    have h1 : |s.re - 1| ≤ ‖s - 1‖ := by
      have h2 := Complex.abs_re_le_norm (s - 1)
      rwa [Complex.sub_re, Complex.one_re] at h2
    have h3 := (abs_le.1 (le_trans h1 hd)).1
    linarith
  have hre0 : (0 : ℝ) < s.re := by linarith
  have htr := zeta_eq_truncated_of_re_pos (N := 1) (le_refl 1) hre0 hs
  rw [h0, zetaTruncated, Finset.Icc_self, Finset.sum_singleton,
    Nat.cast_one, Complex.one_cpow, Complex.one_cpow] at htr
  have hkey : (1 : ℂ) / (s - 1) = s * zetaSawtoothTail 1 s - 1 := by
    linear_combination -htr
  -- norms
  have htail : ‖zetaSawtoothTail 1 s‖ ≤ 8 / 7 := by
    have h1 := norm_zetaSawtoothTail_le hre0 (le_refl 1)
    rw [Nat.cast_one, Real.one_rpow] at h1
    calc ‖zetaSawtoothTail 1 s‖ ≤ 1 / s.re := h1
      _ ≤ 8 / 7 := by
        rw [div_le_div_iff₀ hre0 (by norm_num)]
        linarith
  have hsnorm : ‖s‖ ≤ 9 / 8 := by
    calc ‖s‖ = ‖(s - 1) + 1‖ := by ring_nf
      _ ≤ ‖s - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ 1 / 8 + 1 := by
        rw [norm_one]
        linarith
      _ = 9 / 8 := by norm_num
  have hlow : (8 : ℝ) ≤ ‖(1 : ℂ) / (s - 1)‖ := by
    rw [norm_div, norm_one]
    calc (8 : ℝ) = 1 / (1 / 8) := by norm_num
      _ ≤ 1 / ‖s - 1‖ := one_div_le_one_div_of_le hd0 hd
  have hhigh : ‖s * zetaSawtoothTail 1 s - 1‖ ≤ 16 / 7 := by
    calc ‖s * zetaSawtoothTail 1 s - 1‖
        ≤ ‖s * zetaSawtoothTail 1 s‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = ‖s‖ * ‖zetaSawtoothTail 1 s‖ + 1 := by rw [norm_mul, norm_one]
      _ ≤ (9 / 8) * (8 / 7) + 1 := by
        have h2 : ‖s‖ * ‖zetaSawtoothTail 1 s‖ ≤ (9 / 8) * (8 / 7) :=
          mul_le_mul hsnorm htail (norm_nonneg _) (by norm_num)
        linarith
      _ = 16 / 7 := by norm_num
  rw [hkey] at hlow
  linarith

/-- **The low-height zero-free margin**: some `δ ∈ (0, 1/8]` has no
zeta zeros in `{1 - δ ≤ Re s, |Im s| ≤ 9} ∖ {1}`. -/
theorem exists_low_height_zeta_zero_free :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 8 ∧
      ∀ s : ℂ, 1 - δ ≤ s.re → |s.im| ≤ 9 → s ≠ 1 → riemannZeta s ≠ 0 := by
  by_contra hcon
  push Not at hcon
  -- a sequence of zeros approaching the line `Re s = 1`
  have hseq : ∀ n : ℕ, ∃ s : ℂ,
      1 - min (1 / 8 : ℝ) (1 / (n + 1)) ≤ s.re ∧ |s.im| ≤ 9 ∧ s ≠ 1 ∧
        riemannZeta s = 0 := by
    intro n
    exact hcon _ (lt_min (by norm_num) (by positivity)) (min_le_left _ _)
  choose g hg1 hg2 hg3 hg4 using hseq
  -- the compact box away from the pole
  have hCcomp : IsCompact {z : ℂ | 7 / 8 ≤ z.re ∧ z.re ≤ 1
      ∧ |z.im| ≤ 9 ∧ 1 / 8 ≤ ‖z - 1‖} := by
    apply Metric.isCompact_of_isClosed_isBounded
    · have h1 : IsClosed {z : ℂ | 7 / 8 ≤ z.re} :=
        isClosed_le continuous_const Complex.continuous_re
      have h2 : IsClosed {z : ℂ | z.re ≤ 1} :=
        isClosed_le Complex.continuous_re continuous_const
      have h3 : IsClosed {z : ℂ | |z.im| ≤ 9} :=
        isClosed_le (continuous_abs.comp Complex.continuous_im)
          continuous_const
      have h4 : IsClosed {z : ℂ | 1 / 8 ≤ ‖z - 1‖} :=
        isClosed_le continuous_const
          ((continuous_id.sub continuous_const).norm)
      have hset : {z : ℂ | 7 / 8 ≤ z.re ∧ z.re ≤ 1
            ∧ |z.im| ≤ 9 ∧ 1 / 8 ≤ ‖z - 1‖}
          = {z : ℂ | 7 / 8 ≤ z.re} ∩ ({z : ℂ | z.re ≤ 1}
            ∩ ({z : ℂ | |z.im| ≤ 9} ∩ {z : ℂ | 1 / 8 ≤ ‖z - 1‖})) := by
        ext z
        simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
      rw [hset]
      exact h1.inter (h2.inter (h3.inter h4))
    · apply Bornology.IsBounded.subset
        (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 10))
      rintro z ⟨ha, hb, hc, -⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      rw [show z = (z.re : ℂ) + (z.im : ℂ) * Complex.I from
        (Complex.re_add_im z).symm]
      rw [Complex.norm_add_mul_I]
      have hre2 : z.re ^ 2 ≤ 1 := by nlinarith
      have him2 : z.im ^ 2 ≤ 81 := by
        have h5 := abs_le.1 hc
        nlinarith [h5.1, h5.2]
      calc Real.sqrt (z.re ^ 2 + z.im ^ 2)
          ≤ Real.sqrt 100 := Real.sqrt_le_sqrt (by linarith)
        _ = 10 := by
          rw [show (100 : ℝ) = 10 ^ 2 by norm_num, Real.sqrt_sq
            (by norm_num)]
  -- the zeros live in the box
  have hgC : ∀ n : ℕ, g n ∈ {z : ℂ | 7 / 8 ≤ z.re ∧ z.re ≤ 1
      ∧ |z.im| ≤ 9 ∧ 1 / 8 ≤ ‖z - 1‖} := by
    intro n
    have hdist : 1 / 8 ≤ ‖g n - 1‖ := by
      by_contra hlt
      push Not at hlt
      exact riemannZeta_ne_zero_of_near_one (hg3 n) hlt.le (hg4 n)
    have hle1 : (g n).re ≤ 1 := by
      by_contra hgt
      push Not at hgt
      exact riemannZeta_ne_zero_of_one_le_re hgt.le (hg4 n)
    refine ⟨?_, hle1, hg2 n, hdist⟩
    have h6 := hg1 n
    have h7 : min (1 / 8 : ℝ) (1 / (n + 1)) ≤ 1 / 8 := min_le_left _ _
    linarith
  -- extract a convergent subsequence of zeros
  obtain ⟨sl, hslC, φ, hφ, hlim⟩ := hCcomp.tendsto_subseq hgC
  have hsl1 : sl ≠ 1 := by
    intro h1
    have hd := hslC.2.2.2
    rw [h1, sub_self, norm_zero] at hd
    linarith
  -- the limit is a zero of ζ
  have hz : riemannZeta sl = 0 := by
    have h1 : Tendsto (fun n : ℕ => riemannZeta (g (φ n))) atTop
        (nhds (riemannZeta sl)) :=
      ((differentiableAt_riemannZeta hsl1).continuousAt.tendsto).comp hlim
    have h2 : (fun n : ℕ => riemannZeta (g (φ n))) = fun _ : ℕ => 0 :=
      funext fun n => hg4 (φ n)
    rw [h2] at h1
    exact tendsto_nhds_unique h1 tendsto_const_nhds
  -- the limit sits on the line `Re s = 1`
  have hre1 : sl.re = 1 := by
    have hle : sl.re ≤ 1 := hslC.2.1
    have hrelim : Tendsto (fun n : ℕ => (g (φ n)).re) atTop
        (nhds sl.re) :=
      (Complex.continuous_re.continuousAt.tendsto).comp hlim
    have h0 : Tendsto (fun n : ℕ => (1 : ℝ) / (φ n + 1)) atTop
        (nhds 0) := by
      apply squeeze_zero (fun n => by positivity) (fun n => ?_)
        tendsto_one_div_add_atTop_nhds_zero_nat
      apply one_div_le_one_div_of_le (by positivity)
      have h8 : (n : ℝ) ≤ (φ n : ℝ) := by
        exact_mod_cast hφ.le_apply
      linarith
    have hminlim : Tendsto
        (fun n : ℕ => 1 - min (1 / 8 : ℝ) (1 / (φ n + 1))) atTop
        (nhds 1) := by
      have h9 : Tendsto (fun n : ℕ => min (1 / 8 : ℝ) (1 / (φ n + 1)))
          atTop (nhds (min (1 / 8 : ℝ) 0)) :=
        ((continuous_const.min continuous_id).continuousAt.tendsto).comp h0
      rw [min_eq_right (by norm_num)] at h9
      have h10 := tendsto_const_nhds (x := (1 : ℝ))
        (f := atTop (α := ℕ)) |>.sub h9
      simpa using h10
    have hge : ∀ n : ℕ, 1 - min (1 / 8 : ℝ) (1 / (φ n + 1))
        ≤ (g (φ n)).re := fun n => hg1 (φ n)
    have h11 := le_of_tendsto_of_tendsto' hminlim hrelim hge
    linarith
  exact riemannZeta_ne_zero_of_one_le_re (le_of_eq hre1.symm) hz

end RHTower
