import GaloisForLFunctions.RHTower.Sieve.ChordalSeparation
import Mathlib.Algebra.Order.Chebyshev

/-!
# The windowed Weyl–van der Corput inequality

Averaging a sum over `H` shifts and applying Cauchy–Schwarz bounds the square of an
exponential sum by its shifted autocorrelations:

    H·‖∑_{n<N} a n‖² ≤ 4N·( N + Σ_{h=1}^{H−1} ‖∑_{n<N−h} a(n+h)·conj(a n)‖ ),

for any window `1 ≤ H ≤ N` and any coefficients bounded by one.  The correlation sums run
over full truncated ranges, which is the shape the iterated derivative tests consume: the
`h`-differenced phase of a smooth phase is again a smooth phase on an interval.
-/

namespace RHTower.Sieve

open Finset

/-- The `h`-shifted autocorrelation of a coefficient sequence on `range N`. -/
noncomputable def weylCorr (a : ℕ → ℂ) (N h : ℕ) : ℂ :=
  ∑ n ∈ Finset.range (N - h), a (n + h) * (starRingEnd ℂ) (a n)

/-- The zero-shift correlation is the coefficient energy, at most `N` for bounded
coefficients. -/
theorem norm_weylCorr_zero_le (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) (N : ℕ) :
    ‖weylCorr a N 0‖ ≤ (N : ℝ) := by
  rw [weylCorr]
  refine le_trans (norm_sum_le _ _) ?_
  have hpt : ∀ n ∈ Finset.range (N - 0), ‖a (n + 0) * (starRingEnd ℂ) (a n)‖ ≤ 1 := by
    intro n _
    rw [norm_mul, RCLike.norm_conj]
    have := ha (n + 0)
    have h2 := ha n
    simp only [Nat.add_zero] at this ⊢
    nlinarith [norm_nonneg (a n)]
  refine le_trans (Finset.sum_le_sum hpt) ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  simp

/-- The shifted window indicator sequence. -/
noncomputable def weylShift (a : ℕ → ℂ) (N r m : ℕ) : ℂ :=
  if r ≤ m ∧ m < N + r then a (m - r) else 0

/-- Each shifted window sums to the full sum. -/
theorem sum_weylShift (a : ℕ → ℂ) (N H r : ℕ) (hr : r < H) :
    ∑ m ∈ Finset.range (N + H), weylShift a N r m = ∑ n ∈ Finset.range N, a n := by
  have hfil : (Finset.range (N + H)).filter (fun m => r ≤ m ∧ m < N + r)
      = Finset.Ico r (N + r) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  calc ∑ m ∈ Finset.range (N + H), weylShift a N r m
      = ∑ m ∈ (Finset.range (N + H)).filter (fun m => r ≤ m ∧ m < N + r),
          a (m - r) := by
        rw [Finset.sum_filter]
        exact Finset.sum_congr rfl fun m _ => rfl
    _ = ∑ m ∈ Finset.Ico r (N + r), a (m - r) := by rw [hfil]
    _ = ∑ i ∈ Finset.range (N + r - r), a (r + i - r) := Finset.sum_Ico_eq_sum_range _ _ _
    _ = ∑ n ∈ Finset.range N, a n := by
        refine Finset.sum_congr (by congr 1; omega) fun n _ => ?_
        congr 1
        omega

/-- The correlation of two shifted windows is a shifted autocorrelation. -/
theorem sum_weylShift_mul_conj (a : ℕ → ℂ) (N H r r' : ℕ)
    (hr : r < H) (hr' : r' ≤ r) :
    ∑ m ∈ Finset.range (N + H), weylShift a N r m * (starRingEnd ℂ) (weylShift a N r' m)
      = (starRingEnd ℂ) (weylCorr a N (r - r')) := by
  have hfil : (Finset.range (N + H)).filter
      (fun m => (r ≤ m ∧ m < N + r) ∧ (r' ≤ m ∧ m < N + r'))
      = Finset.Ico r (N + r') := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  have hterm : ∀ m : ℕ,
      weylShift a N r m * (starRingEnd ℂ) (weylShift a N r' m)
        = if (r ≤ m ∧ m < N + r) ∧ (r' ≤ m ∧ m < N + r')
            then a (m - r) * (starRingEnd ℂ) (a (m - r')) else 0 := by
    intro m
    rw [weylShift, weylShift, apply_ite (starRingEnd ℂ), map_zero]
    by_cases h1 : r ≤ m ∧ m < N + r <;> by_cases h2 : r' ≤ m ∧ m < N + r' <;>
      simp [h1, h2]
  calc ∑ m ∈ Finset.range (N + H),
        weylShift a N r m * (starRingEnd ℂ) (weylShift a N r' m)
      = ∑ m ∈ (Finset.range (N + H)).filter
          (fun m => (r ≤ m ∧ m < N + r) ∧ (r' ≤ m ∧ m < N + r')),
          a (m - r) * (starRingEnd ℂ) (a (m - r')) := by
        rw [Finset.sum_filter]
        exact Finset.sum_congr rfl fun m _ => hterm m
    _ = ∑ m ∈ Finset.Ico r (N + r'), a (m - r) * (starRingEnd ℂ) (a (m - r')) := by
        rw [hfil]
    _ = ∑ i ∈ Finset.range (N + r' - r), a (r + i - r)
          * (starRingEnd ℂ) (a (r + i - r')) := Finset.sum_Ico_eq_sum_range _ _ _
    _ = ∑ n ∈ Finset.range (N - (r - r')), a n
          * (starRingEnd ℂ) (a (n + (r - r'))) := by
        refine Finset.sum_congr (by congr 1; omega) fun n _ => ?_
        have h1 : r + n - r = n := by omega
        have h2 : r + n - r' = n + (r - r') := by omega
        rw [h1, h2]
    _ = (starRingEnd ℂ) (weylCorr a N (r - r')) := by
        rw [weylCorr, map_sum]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [map_mul, RingHomInvPair.comp_apply_eq₂]
        ring

/-- Windows correlate symmetrically. -/
theorem norm_sum_weylShift_mul_conj (a : ℕ → ℂ) (N H r r' : ℕ)
    (hr : r < H) (hr' : r' < H) :
    ‖∑ m ∈ Finset.range (N + H),
        weylShift a N r m * (starRingEnd ℂ) (weylShift a N r' m)‖
      = ‖weylCorr a N (max r r' - min r r')‖ := by
  rcases le_total r' r with hle | hle
  · rw [sum_weylShift_mul_conj a N H r r' hr hle, RCLike.norm_conj,
      max_eq_left hle, min_eq_right hle]
  · have hswap : ∑ m ∈ Finset.range (N + H),
        weylShift a N r m * (starRingEnd ℂ) (weylShift a N r' m)
        = (starRingEnd ℂ) (∑ m ∈ Finset.range (N + H),
            weylShift a N r' m * (starRingEnd ℂ) (weylShift a N r m)) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [map_mul, RingHomInvPair.comp_apply_eq₂]
      ring
    rw [hswap, RCLike.norm_conj,
      sum_weylShift_mul_conj a N H r' r hr' hle, RCLike.norm_conj,
      max_eq_right hle, min_eq_left hle]

/-- The distance-indexed correlation sums over one row of shifts. -/
theorem sum_norm_weylCorr_row_le (g : ℕ → ℝ) (hg : ∀ d, 0 ≤ g d) (H r : ℕ) (hr : r < H) :
    ∑ r' ∈ Finset.range H, g (max r r' - min r r')
      ≤ 2 * ∑ d ∈ Finset.range H, g d := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.range H)
    (fun r' => r' ≤ r) (fun r' => g (max r r' - min r r'))
  have h1 : ∑ r' ∈ (Finset.range H).filter (fun r' => r' ≤ r),
      g (max r r' - min r r') ≤ ∑ d ∈ Finset.range H, g d := by
    have hbij : ∑ r' ∈ (Finset.range H).filter (fun r' => r' ≤ r),
        g (max r r' - min r r') = ∑ d ∈ Finset.range (r + 1), g d := by
      refine Finset.sum_bij' (fun r' _ => r - r') (fun d _ => r - d) ?_ ?_ ?_ ?_ ?_
      · intro r' hr'
        simp only [Finset.mem_filter, Finset.mem_range] at hr'
        simp only [Finset.mem_range]
        omega
      · intro d hd
        simp only [Finset.mem_range] at hd
        simp only [Finset.mem_filter, Finset.mem_range]
        omega
      · intro r' hr'
        simp only [Finset.mem_filter, Finset.mem_range] at hr'
        omega
      · intro d hd
        simp only [Finset.mem_range] at hd
        omega
      · intro r' hr'
        simp only [Finset.mem_filter, Finset.mem_range] at hr'
        congr 1
        omega
    rw [hbij]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun d _ _ => hg d)
    intro d hd
    simp only [Finset.mem_range] at hd ⊢
    omega
  have h2 : ∑ r' ∈ (Finset.range H).filter (fun r' => ¬ r' ≤ r),
      g (max r r' - min r r') ≤ ∑ d ∈ Finset.range H, g d := by
    have hbij : ∑ r' ∈ (Finset.range H).filter (fun r' => ¬ r' ≤ r),
        g (max r r' - min r r') = ∑ d ∈ Finset.Icc 1 (H - 1 - r), g d := by
      refine Finset.sum_bij' (fun r' _ => r' - r) (fun d _ => d + r) ?_ ?_ ?_ ?_ ?_
      · intro r' hr'
        simp only [Finset.mem_filter, Finset.mem_range, not_le] at hr'
        simp only [Finset.mem_Icc]
        omega
      · intro d hd
        simp only [Finset.mem_Icc] at hd
        simp only [Finset.mem_filter, Finset.mem_range, not_le]
        omega
      · intro r' hr'
        simp only [Finset.mem_filter, Finset.mem_range, not_le] at hr'
        omega
      · intro d hd
        simp only [Finset.mem_Icc] at hd
        omega
      · intro r' hr'
        simp only [Finset.mem_filter, Finset.mem_range, not_le] at hr'
        have hle : r ≤ r' := hr'.2.le
        rw [max_eq_right hle, min_eq_left hle]
    rw [hbij]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun d _ _ => hg d)
    intro d hd
    simp only [Finset.mem_Icc] at hd
    simp only [Finset.mem_range]
    omega
  linarith

/-- **The windowed Weyl–van der Corput inequality.** -/
theorem weyl_vdc (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) (N H : ℕ)
    (hH : 1 ≤ H) (hHN : H ≤ N) :
    (H : ℝ) * ‖∑ n ∈ Finset.range N, a n‖ ^ 2
      ≤ 4 * (N : ℝ)
        * ((N : ℝ) + ∑ h ∈ Finset.Icc 1 (H - 1), ‖weylCorr a N h‖) := by
  classical
  set T : ℕ → ℂ := fun m => ∑ r ∈ Finset.range H, weylShift a N r m with hT
  -- the averaged representation
  have hHS : ∑ m ∈ Finset.range (N + H), T m
      = (H : ℂ) * ∑ n ∈ Finset.range N, a n := by
    simp only [hT]
    rw [Finset.sum_comm]
    have : ∀ r ∈ Finset.range H,
        ∑ m ∈ Finset.range (N + H), weylShift a N r m
          = ∑ n ∈ Finset.range N, a n := fun r hr =>
      sum_weylShift a N H r (Finset.mem_range.mp hr)
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- Cauchy–Schwarz over the enlarged window
  have hCS : ((H : ℝ) * ‖∑ n ∈ Finset.range N, a n‖) ^ 2
      ≤ ((N : ℝ) + H) * ∑ m ∈ Finset.range (N + H), ‖T m‖ ^ 2 := by
    have h1 : (H : ℝ) * ‖∑ n ∈ Finset.range N, a n‖
        = ‖∑ m ∈ Finset.range (N + H), T m‖ := by
      rw [hHS, norm_mul, Complex.norm_natCast]
    rw [h1]
    have h2 : ‖∑ m ∈ Finset.range (N + H), T m‖
        ≤ ∑ m ∈ Finset.range (N + H), ‖T m‖ := norm_sum_le _ _
    have h3 : (∑ m ∈ Finset.range (N + H), ‖T m‖) ^ 2
        ≤ ((Finset.range (N + H)).card : ℝ)
          * ∑ m ∈ Finset.range (N + H), ‖T m‖ ^ 2 := sq_sum_le_card_mul_sum_sq
    rw [Finset.card_range] at h3
    have h4 : ‖∑ m ∈ Finset.range (N + H), T m‖ ^ 2
        ≤ (∑ m ∈ Finset.range (N + H), ‖T m‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h2 2
    push_cast at h3 ⊢
    nlinarith [h3, h4]
  -- expansion of the energy into shifted correlations
  have henergy : ∑ m ∈ Finset.range (N + H), ‖T m‖ ^ 2
      ≤ ∑ r ∈ Finset.range H, ∑ r' ∈ Finset.range H,
          ‖weylCorr a N (max r r' - min r r')‖ := by
    have hexp : ∑ m ∈ Finset.range (N + H), T m * (starRingEnd ℂ) (T m)
        = ∑ r ∈ Finset.range H, ∑ r' ∈ Finset.range H,
            ∑ m ∈ Finset.range (N + H),
              weylShift a N r m * (starRingEnd ℂ) (weylShift a N r' m) := by
      have hpt : ∀ m : ℕ, T m * (starRingEnd ℂ) (T m)
          = ∑ r ∈ Finset.range H, ∑ r' ∈ Finset.range H,
              weylShift a N r m * (starRingEnd ℂ) (weylShift a N r' m) := by
        intro m
        simp only [hT]
        rw [map_sum, Finset.sum_mul_sum]
      rw [Finset.sum_congr rfl fun m _ => hpt m]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun r _ => Finset.sum_comm
    have hre : ∑ m ∈ Finset.range (N + H), ‖T m‖ ^ 2
        = (∑ m ∈ Finset.range (N + H), T m * (starRingEnd ℂ) (T m)).re := by
      rw [Complex.re_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    rw [hre, hexp]
    refine le_trans (Complex.re_le_norm _) ?_
    refine le_trans (norm_sum_le _ _) ?_
    refine Finset.sum_le_sum fun r hr => ?_
    refine le_trans (norm_sum_le _ _) ?_
    refine Finset.sum_le_sum fun r' hr' => ?_
    rw [norm_sum_weylShift_mul_conj a N H r r'
      (Finset.mem_range.mp hr) (Finset.mem_range.mp hr')]
  -- the distance-indexed bound
  have hrows : ∑ r ∈ Finset.range H, ∑ r' ∈ Finset.range H,
      ‖weylCorr a N (max r r' - min r r')‖
      ≤ (H : ℝ) * (2 * ∑ d ∈ Finset.range H, ‖weylCorr a N d‖) := by
    have hrow : ∀ r ∈ Finset.range H,
        ∑ r' ∈ Finset.range H, ‖weylCorr a N (max r r' - min r r')‖
          ≤ 2 * ∑ d ∈ Finset.range H, ‖weylCorr a N d‖ := fun r hr =>
      sum_norm_weylCorr_row_le (fun d => ‖weylCorr a N d‖)
        (fun d => norm_nonneg _) H r (Finset.mem_range.mp hr)
    refine le_trans (Finset.sum_le_sum hrow) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- split off the zero shift
  have hzero : ∑ d ∈ Finset.range H, ‖weylCorr a N d‖
      ≤ (N : ℝ) + ∑ h ∈ Finset.Icc 1 (H - 1), ‖weylCorr a N h‖ := by
    obtain ⟨H', rfl⟩ : ∃ H', H = H' + 1 := ⟨H - 1, by omega⟩
    rw [Finset.sum_range_succ']
    have hIcc : ∑ i ∈ Finset.range H', ‖weylCorr a N (i + 1)‖
        = ∑ h ∈ Finset.Icc 1 (H' + 1 - 1), ‖weylCorr a N h‖ := by
      refine Finset.sum_bij' (fun i _ => i + 1) (fun h _ => h - 1) ?_ ?_ ?_ ?_ ?_
      · intro i hi
        simp only [Finset.mem_range] at hi
        simp only [Finset.mem_Icc]
        omega
      · intro h hh
        simp only [Finset.mem_Icc] at hh
        simp only [Finset.mem_range]
        omega
      · intro i hi
        omega
      · intro h hh
        simp only [Finset.mem_Icc] at hh
        omega
      · intro i _
        rfl
    rw [hIcc]
    have := norm_weylCorr_zero_le a ha N
    linarith
  -- assemble
  have hNH : ((N : ℝ) + H) ≤ 2 * N := by
    have : (H : ℝ) ≤ N := by exact_mod_cast hHN
    linarith
  have hHpos : (0 : ℝ) < H := by exact_mod_cast hH
  have hsum0 : (0 : ℝ) ≤ ∑ m ∈ Finset.range (N + H), ‖T m‖ ^ 2 :=
    Finset.sum_nonneg fun m _ => sq_nonneg _
  have hchain : ((H : ℝ) * ‖∑ n ∈ Finset.range N, a n‖) ^ 2
      ≤ 2 * (N : ℝ) * ((H : ℝ) * (2 * ((N : ℝ)
          + ∑ h ∈ Finset.Icc 1 (H - 1), ‖weylCorr a N h‖))) := by
    have hstep2 : ∑ m ∈ Finset.range (N + H), ‖T m‖ ^ 2
        ≤ (H : ℝ) * (2 * ((N : ℝ)
            + ∑ h ∈ Finset.Icc 1 (H - 1), ‖weylCorr a N h‖)) := by
      refine le_trans henergy (le_trans hrows ?_)
      have hH0 : (0 : ℝ) ≤ H := by positivity
      nlinarith [hzero]
    calc ((H : ℝ) * ‖∑ n ∈ Finset.range N, a n‖) ^ 2
        ≤ ((N : ℝ) + H) * ∑ m ∈ Finset.range (N + H), ‖T m‖ ^ 2 := hCS
      _ ≤ 2 * (N : ℝ) * ∑ m ∈ Finset.range (N + H), ‖T m‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hNH hsum0
      _ ≤ 2 * (N : ℝ) * ((H : ℝ) * (2 * ((N : ℝ)
            + ∑ h ∈ Finset.Icc 1 (H - 1), ‖weylCorr a N h‖))) := by
          refine mul_le_mul_of_nonneg_left hstep2 (by positivity)
  have hexpand : ((H : ℝ) * ‖∑ n ∈ Finset.range N, a n‖) ^ 2
      = (H : ℝ) * ((H : ℝ) * ‖∑ n ∈ Finset.range N, a n‖ ^ 2) := by ring
  have hrhs : 2 * (N : ℝ) * ((H : ℝ) * (2 * ((N : ℝ)
      + ∑ h ∈ Finset.Icc 1 (H - 1), ‖weylCorr a N h‖)))
      = (H : ℝ) * (4 * (N : ℝ) * ((N : ℝ)
          + ∑ h ∈ Finset.Icc 1 (H - 1), ‖weylCorr a N h‖)) := by ring
  rw [hexpand, hrhs] at hchain
  exact le_of_mul_le_mul_left hchain hHpos

end RHTower.Sieve
