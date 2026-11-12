import GaloisForLFunctions.WorldsOfTheZeroConfiguration.TheEditSeriesHasAPrescribedZeroPair
import GaloisForLFunctions.RHTower.Sieve.ZetaTruncated

/-!
# The tail of `ζ` beyond a cutoff

A pair `ρ, ρ̄` can enter a target late: `cutTarget ρ N k` is the target `−2 Re k^{ρ−1}` for
`k > N` and `0` for `k ≤ N`.  Its Dirichlet series is

`−Σ_{k > N} (k^{−w} + k^{−w̄'})`, `w = s + 1 − ρ`, `w̄' = s + 1 − ρ̄`,

and `Σ_{k > N} k^{−w} = 1/(w − 1) + Z_N(w)` with the entire function

`Z_N(w) = ζ(w) − 1/(w − 1) − Σ_{k ≤ N} k^{−w}` (`zetaCut`).

So the series of the late target has the same two poles as the series of the full target, and
the regular part `Z_N` in place of `ζ(w) − 1/(w − 1)` (`lseriesHasSum_cutTarget`).

**Size of the regular part** (`norm_zetaCut_le`).  For `Re w > 0`, `w ≠ 1`:

`|Z_N(w)| ≤ (N^{1 − Re w} + 1)/|w − 1| + |w| N^{−Re w}/Re w`,

from `Σ_{k ≤ N} k^{−w} = ζ(w) − N^{1−w}/(w − 1) + w ∫_N^∞ {t} t^{−w−1} dt`.  The first term wants
a small cutoff, the second a large one; they balance at `N = |Im ρ|²`.

**The balanced cutoff** (`norm_zetaCut_sq_le`).  For `0 ≤ Re ρ ≤ b`, `1/2 ≤ b ≤ 1`, `Re s > 1/2`,
`|s| ≤ T` and `|Im ρ| ≥ 2T + 3`:

`|Z_N(s + 1 − ρ)| ≤ 10 |Im ρ|^{2b − 2}`, `N = ⌈|Im ρ|⌉²`.
-/

open Complex Filter Topology Finset MeasureTheory

noncomputable section

namespace GaloisForLFunctions.WorldsOfTheZeroConfiguration.PrimeEdits

/-! ## The cut regular part -/

/-- `ζ(w) − 1/(w − 1) − Σ_{k ≤ N} k^{−w}`, as an entire function of `w`. -/
def zetaCut (N : ℕ) (w : ℂ) : ℂ := zetaRegular w - ∑ k ∈ Icc 1 N, (k : ℂ) ^ (-w)

theorem differentiable_zetaCut (N : ℕ) : Differentiable ℂ (zetaCut N) := by
  show Differentiable ℂ (fun w : ℂ => zetaRegular w - ∑ k ∈ Icc 1 N, (k : ℂ) ^ (-w))
  refine differentiable_zetaRegular.sub (Differentiable.fun_sum fun k hk => ?_)
  have hk0 : (k : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by have := (Finset.mem_Icc.mp hk).1; omega)
  exact differentiable_id.neg.const_cpow (Or.inl hk0)

/-- **The size of the cut regular part.** -/
theorem norm_zetaCut_le {N : ℕ} (hN : 1 ≤ N) {w : ℂ} (hw0 : 0 < w.re) (hw1 : w ≠ 1) :
    ‖zetaCut N w‖ ≤
      ((N : ℝ) ^ (1 - w.re) + 1) / ‖w - 1‖ + ‖w‖ * ((N : ℝ) ^ (-w.re) / w.re) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 := _root_.RHTower.Sieve.riemannZeta_eq_sum_add_tail hw0 hw1 hN
  have h2 := riemannZeta_eq_zetaRegular hw1
  have hI := _root_.RHTower.Sieve.norm_integral_Ioi_fract_cpow_le hw0 hN
  have hcast : ∑ k ∈ Icc 1 N, ((k : ℝ) : ℂ) ^ (-w) = ∑ k ∈ Icc 1 N, (k : ℂ) ^ (-w) :=
    Finset.sum_congr rfl fun k _ => by rw [Complex.ofReal_natCast]
  rw [hcast] at h1
  have heq : zetaCut N w = ((N : ℝ) : ℂ) ^ (1 - w) / (w - 1) - (w - 1)⁻¹ -
      w * ∫ t in Set.Ioi (N : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(w + 1)) := by
    rw [zetaCut]
    linear_combination h1 - h2
  have hre : ((1 : ℂ) - w).re = 1 - w.re := by simp
  have hP : ‖((N : ℝ) : ℂ) ^ (1 - w) / (w - 1)‖ = (N : ℝ) ^ (1 - w.re) / ‖w - 1‖ := by
    rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hN0, hre]
  rw [heq]
  calc ‖((N : ℝ) : ℂ) ^ (1 - w) / (w - 1) - (w - 1)⁻¹ -
        w * ∫ t in Set.Ioi (N : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(w + 1))‖
      ≤ ‖((N : ℝ) : ℂ) ^ (1 - w) / (w - 1)‖ + ‖(w - 1)⁻¹‖ +
          ‖w * ∫ t in Set.Ioi (N : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(w + 1))‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ (N : ℝ) ^ (1 - w.re) / ‖w - 1‖ + ‖w - 1‖⁻¹ + ‖w‖ * ((N : ℝ) ^ (-w.re) / w.re) := by
        rw [hP, norm_inv, norm_mul]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hI (norm_nonneg w))
    _ = ((N : ℝ) ^ (1 - w.re) + 1) / ‖w - 1‖ + ‖w‖ * ((N : ℝ) ^ (-w.re) / w.re) := by ring

/-! ## A pair that enters late -/

/-- The target of the pair `ρ` switched on beyond `N`. -/
def cutTarget (ρ : ℂ) (N k : ℕ) : ℝ := if N < k then target ρ k else 0

theorem abs_cutTarget_le (ρ : ℂ) (N : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    |cutTarget ρ N k| ≤ 2 * (k : ℝ) ^ (ρ.re - 1) := by
  unfold cutTarget
  split_ifs
  · exact abs_target_le ρ hk
  · rw [abs_zero]
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg k) _)

/-- The head of the target has a finite Dirichlet series. -/
theorem lseriesHasSum_head (ρ s : ℂ) (N : ℕ) :
    LSeriesHasSum (fun k : ℕ => ((if N < k then 0 else target ρ k : ℝ) : ℂ)) s
      (∑ k ∈ Icc 1 N, (target ρ k : ℂ) / (k : ℂ) ^ s) := by
  have hval : ∑ k ∈ Icc 1 N,
      LSeries.term (fun k : ℕ => ((if N < k then 0 else target ρ k : ℝ) : ℂ)) s k =
      ∑ k ∈ Icc 1 N, (target ρ k : ℂ) / (k : ℂ) ^ s := by
    refine Finset.sum_congr rfl fun k hk => ?_
    obtain ⟨hk1, hkN⟩ := Finset.mem_Icc.mp hk
    have hk0 : k ≠ 0 := by omega
    have hNk : ¬ N < k := by omega
    simp only [LSeries.term_of_ne_zero hk0, if_neg hNk]
  rw [LSeriesHasSum, ← hval]
  refine hasSum_sum_of_ne_finset_zero fun k hk => ?_
  rcases eq_or_ne k 0 with rfl | hk0
  · exact LSeries.term_zero _ _
  · have hNk : N < k := by
      by_contra hcon
      exact hk (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    simp only [LSeries.term_of_ne_zero hk0, if_pos hNk, Complex.ofReal_zero, zero_div]

/-- **The Dirichlet series of a pair that enters late**: the two poles of the pair and the cut
regular parts. -/
theorem lseriesHasSum_cutTarget {ρ s : ℂ} (hs : ρ.re < s.re) (N : ℕ) :
    LSeriesHasSum (fun k : ℕ => (cutTarget ρ N k : ℂ)) s
      (-(((s - ρ)⁻¹ + zetaCut N (s - (ρ - 1))) +
        ((s - (starRingEnd ℂ) ρ)⁻¹ + zetaCut N (s - ((starRingEnd ℂ) ρ - 1))))) := by
  have hfun : (fun k : ℕ => (cutTarget ρ N k : ℂ)) =
      (fun k : ℕ => (target ρ k : ℂ)) -
        fun k : ℕ => ((if N < k then 0 else target ρ k : ℝ) : ℂ) := by
    funext k
    simp only [Pi.sub_apply, cutTarget]
    split_ifs <;> simp
  have hsub := (lseriesHasSum_target (ρ := ρ) (s := s) hs).sub (lseriesHasSum_head ρ s N)
  -- the two arguments are not `1`
  have hw1 : s - (ρ - 1) ≠ 1 := by
    intro h
    have h' := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re] at h'
    linarith
  have hw1' : s - ((starRingEnd ℂ) ρ - 1) ≠ 1 := by
    intro h
    have h' := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re] at h'
    linarith
  -- the head as a sum of powers
  have hterm : ∀ k ∈ Icc 1 N, (target ρ k : ℂ) / (k : ℂ) ^ s =
      -((k : ℂ) ^ (-(s - (ρ - 1))) + (k : ℂ) ^ (-(s - ((starRingEnd ℂ) ρ - 1)))) := by
    intro k hk
    have hk0 : (k : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (by have := (Finset.mem_Icc.mp hk).1; omega)
    rw [target_eq, show -(s - (ρ - 1)) = (ρ - 1) - s by ring,
      show -(s - ((starRingEnd ℂ) ρ - 1)) = ((starRingEnd ℂ) ρ - 1) - s by ring,
      Complex.cpow_sub (ρ - 1) s hk0, Complex.cpow_sub ((starRingEnd ℂ) ρ - 1) s hk0]
    ring
  have hsumeq : ∑ k ∈ Icc 1 N, (target ρ k : ℂ) / (k : ℂ) ^ s =
      -(∑ k ∈ Icc 1 N, (k : ℂ) ^ (-(s - (ρ - 1))) +
        ∑ k ∈ Icc 1 N, (k : ℂ) ^ (-(s - ((starRingEnd ℂ) ρ - 1)))) := by
    rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib, Finset.sum_add_distrib]
  have hval : -(riemannZeta (s - (ρ - 1)) + riemannZeta (s - ((starRingEnd ℂ) ρ - 1))) -
      ∑ k ∈ Icc 1 N, (target ρ k : ℂ) / (k : ℂ) ^ s =
      -(((s - ρ)⁻¹ + zetaCut N (s - (ρ - 1))) +
        ((s - (starRingEnd ℂ) ρ)⁻¹ + zetaCut N (s - ((starRingEnd ℂ) ρ - 1)))) := by
    rw [hsumeq, riemannZeta_eq_zetaRegular hw1, riemannZeta_eq_zetaRegular hw1', zetaCut,
      zetaCut, show s - (ρ - 1) - 1 = s - ρ by ring,
      show s - ((starRingEnd ℂ) ρ - 1) - 1 = s - (starRingEnd ℂ) ρ by ring]
    ring
  rw [hfun, ← hval]
  exact hsub

/-! ## The balanced cutoff -/

/-- **The regular part at the balanced cutoff.**  Far above the point `s`, the regular part of a
pair cut at `⌈|Im ρ|⌉²` is `O(|Im ρ|^{2b−2})`. -/
theorem norm_zetaCut_sq_le {ρ s : ℂ} {b T : ℝ} (hρ0 : 0 ≤ ρ.re) (hρb : ρ.re ≤ b)
    (hb : 1 / 2 ≤ b) (hb1 : b ≤ 1) (hT0 : 0 ≤ T) (hT : 2 * T + 3 ≤ |ρ.im|)
    (hs : 1 / 2 < s.re) (hsT : ‖s‖ ≤ T) :
    ‖zetaCut (⌈|ρ.im|⌉₊ ^ 2) (s - (ρ - 1))‖ ≤ 10 * |ρ.im| ^ (2 * b - 2) := by
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = |ρ.im| := ⟨_, rfl⟩
  rw [← ht] at hT ⊢
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = ⌈t⌉₊ := ⟨_, rfl⟩
  rw [← hn]
  have ht3 : 3 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  have hnt : t ≤ n := by rw [hn]; exact Nat.le_ceil t
  have hnt1 : (n : ℝ) < t + 1 := by rw [hn]; exact Nat.ceil_lt_add_one ht0.le
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le ht0 hnt
  have hn1r : (1 : ℝ) ≤ n := by linarith
  have hn1 : 1 ≤ n := by exact_mod_cast hn1r
  have hN1 : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hNcast : ((n ^ 2 : ℕ) : ℝ) = (n : ℝ) ^ 2 := by push_cast; ring
  have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  obtain ⟨w, hw⟩ : ∃ w : ℂ, w = s - (ρ - 1) := ⟨_, rfl⟩
  rw [← hw]
  have hwre : w.re = s.re + 1 - ρ.re := by
    rw [hw]
    simp only [Complex.sub_re, Complex.one_re]
    ring
  have hwre1 : 3 / 2 - b < w.re := by rw [hwre]; linarith
  have hw0 : 0 < w.re := by linarith
  have hwhalf : 1 / 2 ≤ w.re := by linarith
  -- the distance to the pole
  have hw1sub : w - 1 = s - ρ := by rw [hw]; ring
  have hdist : t / 2 ≤ ‖w - 1‖ := by
    rw [hw1sub]
    have h1 : |(s - ρ).im| ≤ ‖s - ρ‖ := Complex.abs_im_le_norm _
    have h2 : |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm _
    have h3 : |ρ.im| - |s.im| ≤ |(s - ρ).im| := by
      rw [Complex.sub_im]
      have h4 := abs_sub_abs_le_abs_sub ρ.im s.im
      rwa [abs_sub_comm] at h4
    rw [← ht] at h3
    linarith
  have hd0 : 0 < ‖w - 1‖ := lt_of_lt_of_le (by linarith) hdist
  have hw1 : w ≠ 1 := fun h => by
    rw [h, sub_self, norm_zero] at hd0
    exact lt_irrefl 0 hd0
  have hwnorm : ‖w‖ ≤ 2 * t := by
    have h1 : ‖w‖ ≤ ‖s‖ + ‖ρ - 1‖ := by rw [hw]; exact norm_sub_le _ _
    have h2 : ‖ρ - 1‖ ≤ ‖ρ‖ + 1 := by
      have h5 := norm_sub_le ρ 1
      rwa [norm_one] at h5
    have h3 : ‖ρ‖ ≤ |ρ.re| + |ρ.im| := Complex.norm_le_abs_re_add_abs_im ρ
    have h4 : |ρ.re| ≤ 1 := by rw [abs_of_nonneg hρ0]; linarith
    rw [← ht] at h3
    linarith
  have hmain := norm_zetaCut_le hN1 hw0 hw1
  rw [hNcast] at hmain
  -- powers of `t`
  have hpow1 : t ^ (2 * b - 1) = t * t ^ (2 * b - 2) := by
    rw [show 2 * b - 1 = 1 + (2 * b - 2) by ring, Real.rpow_add ht0, Real.rpow_one]
  have hpow3 : t ^ (2 * b - 3) * t = t ^ (2 * b - 2) := by
    rw [show 2 * b - 2 = (2 * b - 3) + 1 by ring, Real.rpow_add ht0, Real.rpow_one]
  have hone : 1 ≤ t ^ (2 * b - 1) := Real.one_le_rpow (by linarith) (by linarith)
  have hX : 0 ≤ t ^ (2 * b - 2) := Real.rpow_nonneg ht0.le _
  have hY : 0 ≤ t ^ (2 * b - 3) := Real.rpow_nonneg ht0.le _
  -- the main term: `(n²)^{1 − Re w} ≤ 2 t^{2b−1}`
  have hA : ((n : ℝ) ^ 2) ^ (1 - w.re) ≤ 2 * t ^ (2 * b - 1) := by
    have h1 : ((n : ℝ) ^ 2) ^ (1 - w.re) ≤ ((n : ℝ) ^ 2) ^ (b - 1 / 2) :=
      Real.rpow_le_rpow_of_exponent_le hn2 (by linarith)
    have h2 : ((n : ℝ) ^ 2) ^ (b - 1 / 2) = (n : ℝ) ^ (2 * b - 1) := by
      rw [← Real.rpow_two, ← Real.rpow_mul hn0.le]
      congr 1
      ring
    have h3 : (n : ℝ) ^ (2 * b - 1) ≤ (2 * t) ^ (2 * b - 1) :=
      Real.rpow_le_rpow hn0.le (by linarith) (by linarith)
    have h4 : (2 * t) ^ (2 * b - 1) = 2 ^ (2 * b - 1) * t ^ (2 * b - 1) :=
      Real.mul_rpow (by norm_num) ht0.le
    have h5 : (2 : ℝ) ^ (2 * b - 1) ≤ 2 := by
      have h6 := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
        (by linarith : 2 * b - 1 ≤ 1)
      rwa [Real.rpow_one] at h6
    have h7 : 0 ≤ t ^ (2 * b - 1) := Real.rpow_nonneg ht0.le _
    rw [h2] at h1
    rw [h4] at h3
    exact h1.trans (h3.trans (mul_le_mul_of_nonneg_right h5 h7))
  -- the remainder: `(n²)^{−Re w} ≤ t^{2b−3}`
  have hB : ((n : ℝ) ^ 2) ^ (-w.re) ≤ t ^ (2 * b - 3) := by
    have h1 : ((n : ℝ) ^ 2) ^ (-w.re) ≤ ((n : ℝ) ^ 2) ^ (-(3 / 2 - b)) :=
      Real.rpow_le_rpow_of_exponent_le hn2 (by linarith)
    have h2 : ((n : ℝ) ^ 2) ^ (-(3 / 2 - b)) = (n : ℝ) ^ (2 * b - 3) := by
      rw [← Real.rpow_two, ← Real.rpow_mul hn0.le]
      congr 1
      ring
    have h3 : (n : ℝ) ^ (2 * b - 3) ≤ t ^ (2 * b - 3) :=
      Real.rpow_le_rpow_of_nonpos ht0 hnt (by linarith)
    rw [h2] at h1
    exact h1.trans h3
  have hfirst : (((n : ℝ) ^ 2) ^ (1 - w.re) + 1) / ‖w - 1‖ ≤ 6 * t ^ (2 * b - 2) := by
    rw [div_le_iff₀ hd0]
    have h1 : 6 * t ^ (2 * b - 2) * (t / 2) ≤ 6 * t ^ (2 * b - 2) * ‖w - 1‖ :=
      mul_le_mul_of_nonneg_left hdist (by linarith)
    have h2 : 6 * t ^ (2 * b - 2) * (t / 2) = 3 * t ^ (2 * b - 1) := by rw [hpow1]; ring
    linarith
  have hsecond : ‖w‖ * (((n : ℝ) ^ 2) ^ (-w.re) / w.re) ≤ 4 * t ^ (2 * b - 2) := by
    have h1 : ((n : ℝ) ^ 2) ^ (-w.re) / w.re ≤ 2 * t ^ (2 * b - 3) := by
      rw [div_le_iff₀ hw0]
      have h2 := mul_le_mul_of_nonneg_left hwhalf hY
      linarith
    have h3 : 0 ≤ ((n : ℝ) ^ 2) ^ (-w.re) / w.re :=
      div_nonneg (Real.rpow_nonneg (by linarith) _) hw0.le
    calc ‖w‖ * (((n : ℝ) ^ 2) ^ (-w.re) / w.re) ≤ (2 * t) * (2 * t ^ (2 * b - 3)) :=
          mul_le_mul hwnorm h1 h3 (by linarith)
      _ = 4 * t ^ (2 * b - 2) := by rw [← hpow3]; ring
  calc ‖zetaCut (n ^ 2) w‖
      ≤ (((n : ℝ) ^ 2) ^ (1 - w.re) + 1) / ‖w - 1‖ +
          ‖w‖ * (((n : ℝ) ^ 2) ^ (-w.re) / w.re) := hmain
    _ ≤ 6 * t ^ (2 * b - 2) + 4 * t ^ (2 * b - 2) := add_le_add hfirst hsecond
    _ = 10 * t ^ (2 * b - 2) := by ring

end GaloisForLFunctions.WorldsOfTheZeroConfiguration.PrimeEdits
