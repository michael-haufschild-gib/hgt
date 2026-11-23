import GaloisForLFunctions.RHTower.DQPTTailNormal
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.SignedPartialSumClassificationAndReflectedSieve

/-!
# Exponentially Accelerated Euler–Knopp Signed Partial Sums of Dirichlet Eta

Untruncated or paired Dirichlet eta partial sums `∑_{n ≤ N} (-1)^{n-1} n^{-s}` have first-difference
Abel remainder `O((‖s‖ / Re s) · (N + 1)^{-Re s})`, requiring polynomially astronomical prefix
lengths `N ≳ |Im s|^{1 / Re s}` (`≈ |Im s|^8` near the left zero-free boundary
`Re s = 3001 / 24000`) and suffering an additional `|η(s)|^{-1 / Re s}` blow-up on Speiser-shadowed
ordinates where `|ζ(s)|` is small.

This module constructs the arbitrary-order Euler–Knopp binomial-averaged signed Dirichlet partial
sums `eulerEtaPartialSum N M s = ∑_{n=1}^{N+M} eulerEtaSign N M n · n^{-s}` with explicit dyadic
signs `eulerEtaSign N M n ∈ [-1, 1]` (`(-1)^{n-1}` on `1 ≤ n ≤ N` and tapered binomial tails on
`N < n ≤ N + M`) and proves unconditionally:

1. **Iterated falling-difference calculus (`iterate_unitFallDiff_eq_sum_choose`,
   `norm_iterate_unitFallDiff_dqptRp_le`):** The `k`-th unit falling difference of `x ↦ x^{-s}` on
   `(0, ∞)` expands as `∑_{r=0}^k (-1)^r C(k, r) (x + r)^{-s}` and satisfies the exact Pochhammer
   mean-value bound `‖(unitFallDiff^[k] (dqptRp s)) a‖ ≤ (∏_{m < k} ‖s + m‖) · a^{-Re s - k}`.
2. **Exact arbitrary-order decomposition and `ζ`-free remainder (`eta_eq_eulerEtaPartialSum_add_diffTail`,
   `norm_eta_sub_eulerEtaPartialSum_le`):** For all `N : ℕ`, `M ≥ 1`, and `Re s > 0` (`s ≠ 1`),
   `(1 - 2^{1-s}) ζ(s) - eulerEtaPartialSum N M s` equals `(-1)^N 2^{-M} ∑_{j ≥ 0} Δ^{M+1}((N+1+2j)^{-s})`
   and is bounded in norm by
   `eulerEtaTailBound N M s = (3 / 2^{M+1}) (∏_{m=0}^M ‖s + m‖) (N + 1)^{-Re s - M}`
   (recovering `dqptAltTail_sub_half_norm_le` identically at `M = 1`).
3. **Uniform `O(|Im s|)` prefix collapse and exponential `2^{-M/2}` tail
   (`eulerEtaTailBound_two_mul_le`, `eulerEtaTailBound_two_mul_le_three_div_two_pow_half`,
   `eulerEtaTailBound_above_oneHundredEightyFour_lt`):** At linear cutoff `N = 2 M` (`3 M` total
   terms) with `|Im s| ≤ M` and `0 < Re s ≤ 1`, every Pochhammer factor `‖s + m‖ ≤ 2 M + 1` cancels
   against `(2 M + 1)^{-M}`, collapsing the `ζ`-free tail uniformly in `Re s` to
   `≤ 3 (2 M + 1) / 2^{M + 1} ≤ 3 / 2^{M / 2}` (`M ≥ 10`), and `< 10^{-52}` across the entire
   remaining frontier `|Im s| > 184` at `M = ⌈|Im s|⌉₊` (`555` terms near height `185`).
4. **Logarithmic sensitivity on Speiser-shadowed ordinates, zero-exception certification through
   height `184`, and `RiemannHypothesis` equivalence (`eulerEtaPartialSum_beats_tail_of_eta_lower_bound`,
   `zero_exception_euler_linear_through_oneHundredEightyFour`,
   `rh_iff_linear_euler_signedPartialSum_above_oneHundredEightyFour`):** Whenever
   `‖(1 - 2^{1-s}) ζ(s)‖ > 6 / 2^K`, the single explicit `3 M`-term signed partial sum at
   `M = max 10 (max ⌈|Im s|⌉₊ (2 K))` strictly beats its `ζ`-free tail (`O(|Im s| + log(1/|η(s)|))`
   terms, with zero search over rank-one omissions or divisor packets). Every off-line strip point
   with `|Im s| ≤ 184` passes this test unconditionally, and `RiemannHypothesis` is equivalent to
   passing this single `O(|Im s|)`-scale dyadic-signed partial-sum test on
   `{3001/24000 ≤ Re s < 1/2 ∧ |Im s| > 184}`.
-/

noncomputable section

open Complex Filter Topology Set
open scoped BigOperators ComplexConjugate

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas

open _root_.RHTower.DQPT
open InverseSpectrum.ShellMixing

/-! ### 1. Iterated Unit Falling Differences of `x ↦ x^{-s}` -/

/-- Unit falling difference operator `(D g)(x) = g(x) - g(x + 1)`. -/
def unitFallDiff (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  g x - g (x + 1)

@[simp]
lemma unitFallDiff_apply (g : ℝ → ℂ) (x : ℝ) :
    unitFallDiff g x = g x - g (x + 1) := rfl

/-- Binomial expansion of the `k`-th iterated unit falling difference. -/
theorem iterate_unitFallDiff_eq_sum_choose (k : ℕ) (g : ℝ → ℂ) (x : ℝ) :
    (unitFallDiff^[k] g) x =
      ∑ r ∈ Finset.range (k + 1), (-1 : ℂ) ^ r * (k.choose r : ℂ) * g (x + (r : ℝ)) := by
  induction k generalizing x with
  | zero =>
    rw [Function.iterate_zero_apply, Finset.range_one, Finset.sum_singleton]
    simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', unitFallDiff_apply, ih x, ih (x + 1)]
    rw [Finset.sum_range_succ' (fun r => (-1 : ℂ) ^ r * (k.choose r : ℂ) * g (x + (r : ℝ))) k,
      Finset.sum_range_succ (fun r => (-1 : ℂ) ^ r * (k.choose r : ℂ) * g (x + 1 + (r : ℝ))) k,
      Finset.sum_range_succ (fun r => (-1 : ℂ) ^ r * ((k + 1).choose r : ℂ) * g (x + (r : ℝ))) (k + 1),
      Finset.sum_range_succ' (fun r => (-1 : ℂ) ^ r * ((k + 1).choose r : ℂ) * g (x + (r : ℝ))) k]
    have h0_l : (-1 : ℂ) ^ 0 * (k.choose 0 : ℂ) * g (x + ((0 : ℕ) : ℝ)) = g x := by simp
    have h0_r : (-1 : ℂ) ^ 0 * ((k + 1).choose 0 : ℂ) * g (x + ((0 : ℕ) : ℝ)) = g x := by simp
    have hlast : -((-1 : ℂ) ^ k * (k.choose k : ℂ) * g (x + 1 + (k : ℝ))) =
        (-1 : ℂ) ^ (k + 1) * ((k + 1).choose (k + 1) : ℂ) * g (x + ((k + 1 : ℕ) : ℝ)) := by
      rw [Nat.choose_self, Nat.choose_self, Nat.cast_one, mul_one, mul_one, pow_succ]
      have harg : x + 1 + (k : ℝ) = x + ((k + 1 : ℕ) : ℝ) := by push_cast; ring
      rw [harg]
      ring
    have hmid : (∑ r ∈ Finset.range k,
          ((-1 : ℂ) ^ (r + 1) * (k.choose (r + 1) : ℂ) * g (x + ((r + 1 : ℕ) : ℝ)) -
            (-1 : ℂ) ^ r * (k.choose r : ℂ) * g (x + 1 + (r : ℝ)))) =
        ∑ r ∈ Finset.range k,
          (-1 : ℂ) ^ (r + 1) * ((k + 1).choose (r + 1) : ℂ) * g (x + ((r + 1 : ℕ) : ℝ)) := by
      refine Finset.sum_congr rfl fun r _ => ?_
      have harg : x + 1 + (r : ℝ) = x + ((r + 1 : ℕ) : ℝ) := by push_cast; ring
      have hch : (((k + 1).choose (r + 1) : ℕ) : ℂ) =
          (k.choose r : ℂ) + (k.choose (r + 1) : ℂ) := by
        exact_mod_cast Nat.choose_succ_succ k r
      rw [harg, hch, pow_succ]
      ring
    rw [h0_l, h0_r, ← hmid, Finset.sum_sub_distrib, ← hlast]
    ring

/-- Differentiability of the `k`-th unit falling difference of `dqptRp s` on `(0, ∞)`. -/
theorem hasDerivAt_iterate_unitFallDiff_dqptRp (k : ℕ) {s : ℂ} (hs : 0 < s.re)
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt (unitFallDiff^[k] (dqptRp s))
      ((-s) * (unitFallDiff^[k] (dqptRp (s + 1))) x) x := by
  induction k generalizing x with
  | zero =>
    simpa only [Function.iterate_zero_apply] using hasDerivAt_dqptRp hs hx
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    have h1 := ih hx
    have h2 : HasDerivAt (fun y : ℝ => (unitFallDiff^[k] (dqptRp s)) (y + 1))
        ((-s) * (unitFallDiff^[k] (dqptRp (s + 1))) (x + 1)) x :=
      HasDerivAt.comp_add_const x 1 (ih (by linarith : 0 < x + 1))
    exact (h1.sub h2).congr_deriv (by simp only [unitFallDiff_apply]; ring)

/-- Pochhammer mean-value bound for the `k`-th unit falling difference of `x ↦ x^{-s}`:
`‖(D^k (x^{-s}))(a)‖ ≤ (∏_{m < k} ‖s + m‖) · a^{-Re s - k}` for all `Re s > 0` and `a > 0`. -/
theorem norm_iterate_unitFallDiff_dqptRp_le (k : ℕ) {s : ℂ} (hs : 0 < s.re)
    {a : ℝ} (ha : 0 < a) :
    ‖(unitFallDiff^[k] (dqptRp s)) a‖ ≤
      (∏ m ∈ Finset.range k, ‖s + (m : ℂ)‖) * a ^ (-s.re - (k : ℝ)) := by
  induction k generalizing s a with
  | zero =>
    rw [Function.iterate_zero_apply, Finset.range_zero, Finset.prod_empty,
      Nat.cast_zero, sub_zero, one_mul, dqptRp_norm ha]
  | succ k ih =>
    rw [Function.iterate_succ_apply', unitFallDiff_apply]
    set ψ : ℝ → ℂ := unitFallDiff^[k] (dqptRp s)
    set C : ℝ := (∏ m ∈ Finset.range (k + 1), ‖s + (m : ℂ)‖) * a ^ (-s.re - ((k + 1 : ℕ) : ℝ))
    have hs1 : 0 < (s + 1).re := by rw [Complex.add_re, Complex.one_re]; linarith
    have hderiv : ∀ x ∈ Icc a (a + 1),
        HasDerivWithinAt ψ ((-s) * (unitFallDiff^[k] (dqptRp (s + 1))) x) (Icc a (a + 1)) x := by
      intro x hx
      exact (hasDerivAt_iterate_unitFallDiff_dqptRp k hs (lt_of_lt_of_le ha hx.1)).hasDerivWithinAt
    have hprod_eq : ‖s‖ * (∏ m ∈ Finset.range k, ‖s + 1 + (m : ℂ)‖) =
        ∏ m ∈ Finset.range (k + 1), ‖s + (m : ℂ)‖ := by
      rw [Finset.prod_range_succ' (fun m => ‖s + (m : ℂ)‖) k, Nat.cast_zero, add_zero, mul_comm]
      congr 1
      refine Finset.prod_congr rfl fun m _ => ?_
      congr 1
      push_cast
      ring
    have hbound : ∀ x ∈ Ico a (a + 1),
        ‖(-s) * (unitFallDiff^[k] (dqptRp (s + 1))) x‖ ≤ C := by
      intro x hx
      have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
      have hstep := ih hs1 hx0
      have hexp : -(s + 1).re - (k : ℝ) = -s.re - ((k + 1 : ℕ) : ℝ) := by
        rw [Complex.add_re, Complex.one_re]; push_cast; ring
      rw [hexp] at hstep
      have hmono : x ^ (-s.re - ((k + 1 : ℕ) : ℝ)) ≤ a ^ (-s.re - ((k + 1 : ℕ) : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos ha hx.1 (by linarith)
      rw [norm_mul, norm_neg]
      calc ‖s‖ * ‖(unitFallDiff^[k] (dqptRp (s + 1))) x‖
          ≤ ‖s‖ * ((∏ m ∈ Finset.range k, ‖s + 1 + (m : ℂ)‖) *
              x ^ (-s.re - ((k + 1 : ℕ) : ℝ))) :=
            mul_le_mul_of_nonneg_left hstep (norm_nonneg s)
        _ ≤ ‖s‖ * ((∏ m ∈ Finset.range k, ‖s + 1 + (m : ℂ)‖) *
              a ^ (-s.re - ((k + 1 : ℕ) : ℝ))) := by
            refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg s)
            exact mul_le_mul_of_nonneg_left hmono
              (Finset.prod_nonneg fun _ _ => norm_nonneg _)
        _ = (‖s‖ * ∏ m ∈ Finset.range k, ‖s + 1 + (m : ℂ)‖) *
              a ^ (-s.re - ((k + 1 : ℕ) : ℝ)) := by ring
        _ = C := by rw [hprod_eq]
    have key := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound (a + 1)
      (right_mem_Icc.2 (by linarith))
    rw [show a + 1 - a = 1 by ring, mul_one, norm_sub_rev] at key
    exact key

/-! ### 2. Explicit Euler–Knopp Dyadic-Signed Partial Sums of `(1 - 2^{1-s}) ζ(s)` -/

/-- Dyadic-rational sign coefficients of the `(N, M)` Euler–Knopp accelerated Dirichlet eta partial
sum: pure alternating signs `(-1)^{n-1}` on `1 ≤ n ≤ N` followed by `M` binomial-tail-tapered
alternating weights on `N < n ≤ N + M`. -/
def eulerEtaSign (N M n : ℕ) : ℝ :=
  if n = 0 then 0
  else if n ≤ N then (-1 : ℝ) ^ (n - 1)
  else if n ≤ N + M then
    (-1 : ℝ) ^ (n - 1) * ((∑ r ∈ Finset.Icc (n - N) M, (M.choose r : ℝ)) / (2 : ℝ) ^ M)
  else 0

/-- Finite `(N + M)`-term signed Dirichlet partial sum with weights `eulerEtaSign N M`. -/
def eulerEtaPartialSum (N M : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 (N + M), (eulerEtaSign N M n : ℂ) * (n : ℂ) ^ (-s)

/-- Structural properties of `eulerEtaSign`: exact `±1` signs on `[1, N]`, vanishing above `N + M`,
and uniform bound `|eulerEtaSign N M n| ≤ 1`. -/
theorem eulerEtaSign_properties (N M : ℕ) :
    (∀ n : ℕ, 1 ≤ n → n ≤ N → eulerEtaSign N M n = (-1 : ℝ) ^ (n - 1)) ∧
    (∀ n : ℕ, N + M < n → eulerEtaSign N M n = 0) ∧
    (∀ n : ℕ, |eulerEtaSign N M n| ≤ 1) := by
  refine ⟨fun n hn1 hnN => ?_, fun n hgt => ?_, fun n => ?_⟩
  · unfold eulerEtaSign
    rw [if_neg (by omega : n ≠ 0), if_pos hnN]
  · unfold eulerEtaSign
    rw [if_neg (by omega : n ≠ 0), if_neg (by omega : ¬ n ≤ N), if_neg (by omega : ¬ n ≤ N + M)]
  · unfold eulerEtaSign
    split_ifs with h0 hN hNM
    · norm_num
    · rw [abs_pow, abs_neg, abs_one, one_pow]
    · have hsub : Finset.Icc (n - N) M ⊆ Finset.range (M + 1) := by
        intro r hr
        exact Finset.mem_range.mpr (by have := (Finset.mem_Icc.mp hr).2; omega)
      have hsum_nn : 0 ≤ ∑ r ∈ Finset.Icc (n - N) M, (M.choose r : ℝ) :=
        Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
      have hsum_le : (∑ r ∈ Finset.Icc (n - N) M, (M.choose r : ℝ)) ≤ (2 : ℝ) ^ M := by
        calc (∑ r ∈ Finset.Icc (n - N) M, (M.choose r : ℝ))
            ≤ ∑ r ∈ Finset.range (M + 1), (M.choose r : ℝ) :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => Nat.cast_nonneg _
          _ = (2 : ℝ) ^ M := by exact_mod_cast Nat.sum_range_choose M
      rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
        abs_of_nonneg (div_nonneg hsum_nn (by positivity))]
      exact (div_le_one (by positivity)).mpr hsum_le
    · norm_num

private lemma dqptAltPartialSum_eq_sum_Icc_ite {L K : ℕ} (hLK : L ≤ K) (s : ℂ) :
    dqptAltPartialSum s L =
      ∑ n ∈ Finset.Icc 1 K, if n ≤ L then (-1 : ℂ) ^ (n - 1) * (n : ℂ) ^ (-s) else 0 := by
  rw [← Finset.sum_filter]
  have hfilt : (Finset.Icc 1 K).filter (· ≤ L) = Finset.Icc 1 L := by
    ext n; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
  rw [hfilt]
  unfold dqptAltPartialSum dqptRp
  refine Finset.sum_bij (fun k _ => k + 1) ?_ ?_ ?_ ?_
  · intro k hk
    have := Finset.mem_range.mp hk
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro k₁ _ k₂ _ heq; omega
  · intro n hn
    obtain ⟨hn1, hnL⟩ := Finset.mem_Icc.mp hn
    exact ⟨n - 1, Finset.mem_range.mpr (by omega), by omega⟩
  · intro k _
    simp only [Nat.add_sub_cancel]
    congr 2
    push_cast
    ring

/-- **Binomial-average representation:** `eulerEtaPartialSum N M s` is the exact `2^{-M} C(M, r)`
binomial average of the raw alternating partial sums `dqptAltPartialSum s (N + r)` (`0 ≤ r ≤ M`). -/
theorem eulerEtaPartialSum_eq_avg_dqptAltPartialSum (N M : ℕ) (s : ℂ) :
    eulerEtaPartialSum N M s =
      ((2 : ℂ) ^ M)⁻¹ *
        ∑ r ∈ Finset.range (M + 1), (M.choose r : ℂ) * dqptAltPartialSum s (N + r) := by
  have hrw : (∑ r ∈ Finset.range (M + 1), (M.choose r : ℂ) * dqptAltPartialSum s (N + r)) =
      ∑ n ∈ Finset.Icc 1 (N + M),
        ∑ r ∈ Finset.range (M + 1),
          (M.choose r : ℂ) *
            (if n ≤ N + r then (-1 : ℂ) ^ (n - 1) * (n : ℂ) ^ (-s) else 0) := by
    trans (∑ r ∈ Finset.range (M + 1),
        ∑ n ∈ Finset.Icc 1 (N + M),
          (M.choose r : ℂ) *
            (if n ≤ N + r then (-1 : ℂ) ^ (n - 1) * (n : ℂ) ^ (-s) else 0))
    · refine Finset.sum_congr rfl fun r hr => ?_
      have hrM : r ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
      rw [dqptAltPartialSum_eq_sum_Icc_ite (by omega : N + r ≤ N + M) s, Finset.mul_sum]
    · exact Finset.sum_comm
  rw [hrw, Finset.mul_sum]
  unfold eulerEtaPartialSum
  refine Finset.sum_congr rfl fun n hn => ?_
  obtain ⟨hn1, hnNM⟩ := Finset.mem_Icc.mp hn
  have h2_ne : (2 : ℂ) ^ M ≠ 0 := pow_ne_zero M two_ne_zero
  unfold eulerEtaSign
  rw [if_neg (by omega : n ≠ 0)]
  by_cases hnN : n ≤ N
  · rw [if_pos hnN]
    have hall : (∑ r ∈ Finset.range (M + 1),
          (M.choose r : ℂ) * (if n ≤ N + r then (-1 : ℂ) ^ (n - 1) * (n : ℂ) ^ (-s) else 0)) =
        (∑ r ∈ Finset.range (M + 1), (M.choose r : ℂ)) *
          ((-1 : ℂ) ^ (n - 1) * (n : ℂ) ^ (-s)) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [if_pos (by omega : n ≤ N + r)]
    have hchoose : (∑ r ∈ Finset.range (M + 1), (M.choose r : ℂ)) = (2 : ℂ) ^ M := by
      exact_mod_cast Nat.sum_range_choose M
    rw [hall, hchoose, inv_mul_cancel_left₀ h2_ne]
    push_cast
    rfl
  · rw [if_neg hnN, if_pos hnNM]
    have hfilt_eq : (Finset.range (M + 1)).filter (fun r => n ≤ N + r) = Finset.Icc (n - N) M := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
      omega
    have hpart : (∑ r ∈ Finset.range (M + 1),
          (M.choose r : ℂ) * (if n ≤ N + r then (-1 : ℂ) ^ (n - 1) * (n : ℂ) ^ (-s) else 0)) =
        (∑ r ∈ Finset.Icc (n - N) M, (M.choose r : ℂ)) *
          ((-1 : ℂ) ^ (n - 1) * (n : ℂ) ^ (-s)) := by
      rw [← hfilt_eq, Finset.sum_filter, Finset.sum_mul]
      refine Finset.sum_congr rfl fun r _ => ?_
      split_ifs <;> ring
    rw [hpart]
    push_cast
    ring

/-! ### 3. Exact `(M + 1)`-th Difference Tail Identity and Arbitrary-Order Bound -/

/-- **Exact arbitrary-order decomposition of `(1 - 2^{1-s}) ζ(s)`:** for every `N, M : ℕ` and
`Re s > 0`, `s ≠ 1`, the remainder after `eulerEtaPartialSum N M s` is `(-1)^N 2^{-M}` times the
`(M + 1)`-th unit falling-difference series at odd shifts `N + 1 + 2 j`. -/
theorem eta_eq_eulerEtaPartialSum_add_diffTail {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) (N M : ℕ) :
    (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s =
      eulerEtaPartialSum N M s +
        (-1 : ℂ) ^ N * ((2 : ℂ) ^ M)⁻¹ *
          ∑' j : ℕ, (unitFallDiff^[M + 1] (dqptRp s)) ((N : ℝ) + 1 + 2 * (j : ℝ)) := by
  set η : ℂ := (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s
  have h2_ne : (2 : ℂ) ^ M ≠ 0 := pow_ne_zero M two_ne_zero
  have hchoose : (∑ r ∈ Finset.range (M + 1), (M.choose r : ℂ)) = (2 : ℂ) ^ M := by
    exact_mod_cast Nat.sum_range_choose M
  have hη_avg : η = ((2 : ℂ) ^ M)⁻¹ * ∑ r ∈ Finset.range (M + 1), (M.choose r : ℂ) * η := by
    rw [← Finset.sum_mul, hchoose, inv_mul_cancel_left₀ h2_ne]
  have hsub : η - eulerEtaPartialSum N M s =
      (-1 : ℂ) ^ N * ((2 : ℂ) ^ M)⁻¹ *
        ∑ r ∈ Finset.range (M + 1), (-1 : ℂ) ^ r * (M.choose r : ℂ) * dqptAltTail s (N + r) := by
    conv_lhs => rw [hη_avg]
    rw [eulerEtaPartialSum_eq_avg_dqptAltPartialSum, ← mul_sub, ← Finset.sum_sub_distrib]
    have hinner : (∑ r ∈ Finset.range (M + 1),
          ((M.choose r : ℂ) * η - (M.choose r : ℂ) * dqptAltPartialSum s (N + r))) =
        (-1 : ℂ) ^ N * ∑ r ∈ Finset.range (M + 1),
          (-1 : ℂ) ^ r * (M.choose r : ℂ) * dqptAltTail s (N + r) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      have hdecomp := dqptEta_eq_altPartialSum_add_tail hs hs1 (N + r)
      have hdiff : η - dqptAltPartialSum s (N + r) =
          (-1 : ℂ) ^ N * (-1 : ℂ) ^ r * dqptAltTail s (N + r) := by
        rw [← pow_add]
        linear_combination hdecomp
      linear_combination (M.choose r : ℂ) * hdiff
    rw [hinner]
    ring
  have htsum : (∑ r ∈ Finset.range (M + 1),
        (-1 : ℂ) ^ r * (M.choose r : ℂ) * dqptAltTail s (N + r)) =
      ∑' j : ℕ, (unitFallDiff^[M + 1] (dqptRp s)) ((N : ℝ) + 1 + 2 * (j : ℝ)) := by
    have hmul : ∀ r ∈ Finset.range (M + 1),
        (-1 : ℂ) ^ r * (M.choose r : ℂ) * dqptAltTail s (N + r) =
          ∑' j : ℕ, (-1 : ℂ) ^ r * (M.choose r : ℂ) * dqptAltTailTerm s (N + r) j := by
      intro r _
      unfold dqptAltTail
      exact tsum_mul_left.symm
    rw [Finset.sum_congr rfl hmul,
      ← Summable.tsum_finsetSum (fun r _ => (summable_dqptAltTailTerm hs (N + r)).mul_left _)]
    refine tsum_congr fun j => ?_
    have hterm : ∀ r : ℕ, dqptAltTailTerm s (N + r) j =
        unitFallDiff (dqptRp s) (((N : ℝ) + 1 + 2 * (j : ℝ)) + (r : ℝ)) := by
      intro r
      unfold dqptAltTailTerm unitFallDiff
      congr 2 <;> (push_cast; ring)
    simp_rw [hterm]
    rw [← iterate_unitFallDiff_eq_sum_choose M (unitFallDiff (dqptRp s))
      ((N : ℝ) + 1 + 2 * (j : ℝ)), ← Function.iterate_succ_apply unitFallDiff M (dqptRp s)]
  rw [htsum] at hsub
  linear_combination hsub

/-- Explicit `ζ`-free arbitrary-order tail majorant at cutoff `N` and Euler order `M`. -/
def eulerEtaTailBound (N M : ℕ) (s : ℂ) : ℝ :=
  (3 / (2 : ℝ) ^ (M + 1)) *
    (∏ m ∈ Finset.range (M + 1), ‖s + (m : ℂ)‖) *
      ((N : ℝ) + 1) ^ (-s.re - (M : ℝ))

/-- At `M = 1`, `eulerEtaTailBound N 1 s` recovers `DQPTTailNormal`'s `3/4 · ‖s‖ ‖s+1‖ (N+1)^{-Re s - 1}`. -/
theorem eulerEtaTailBound_one (N : ℕ) (s : ℂ) :
    eulerEtaTailBound N 1 s =
      (3 / 4) * (‖s‖ * ‖s + 1‖) * ((N : ℝ) + 1) ^ (-s.re - 1) := by
  unfold eulerEtaTailBound
  rw [Finset.prod_range_succ, Finset.prod_range_one]
  norm_num

/-- **Unconditional `ζ`-free remainder bound for all `M ≥ 1`:**
`‖(1 - 2^{1-s}) ζ(s) - eulerEtaPartialSum N M s‖ ≤ eulerEtaTailBound N M s`. -/
theorem norm_eta_sub_eulerEtaPartialSum_le {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1)
    (N M : ℕ) (hM : 1 ≤ M) :
    ‖(1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s - eulerEtaPartialSum N M s‖ ≤
      eulerEtaTailBound N M s := by
  have hN0 : 0 < (N : ℝ) + 1 := by positivity
  have hN1 : 1 ≤ (N : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) N]
  set P : ℝ := ∏ m ∈ Finset.range (M + 1), ‖s + (m : ℂ)‖
  have hP_nn : 0 ≤ P := Finset.prod_nonneg fun _ _ => norm_nonneg _
  set K : ℝ := P * ((N : ℝ) + 1) ^ (-s.re - ((M - 1 : ℕ) : ℝ))
  have hK_nn : 0 ≤ K := mul_nonneg hP_nn (Real.rpow_nonneg hN0.le _)
  have hM_sub : ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1 := by rw [Nat.cast_sub hM, Nat.cast_one]
  have hpt : ∀ j : ℕ,
      ‖(unitFallDiff^[M + 1] (dqptRp s)) ((N : ℝ) + 1 + 2 * (j : ℝ))‖ ≤
        K * ((1 : ℝ) / ((N : ℝ) + 1 + 2 * (j : ℝ)) ^ 2) := by
    intro j
    set x : ℝ := (N : ℝ) + 1 + 2 * (j : ℝ)
    have hx0 : 0 < x := by positivity
    have hx_ge : (N : ℝ) + 1 ≤ x := by dsimp [x]; linarith [Nat.cast_nonneg (α := ℝ) j]
    have hdiff := norm_iterate_unitFallDiff_dqptRp_le (M + 1) hs hx0
    have hexp : -s.re - ((M + 1 : ℕ) : ℝ) = (-s.re - ((M - 1 : ℕ) : ℝ)) + (-2 : ℝ) := by
      rw [hM_sub]; push_cast; ring
    have hrpow_split : x ^ (-s.re - ((M + 1 : ℕ) : ℝ)) =
        x ^ (-s.re - ((M - 1 : ℕ) : ℝ)) * ((1 : ℝ) / x ^ 2) := by
      rw [hexp, Real.rpow_add hx0]
      congr 1
      rw [Real.rpow_neg hx0.le]
      norm_num
    have hmono : x ^ (-s.re - ((M - 1 : ℕ) : ℝ)) ≤ ((N : ℝ) + 1) ^ (-s.re - ((M - 1 : ℕ) : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hN0 hx_ge (by linarith [Nat.cast_nonneg (α := ℝ) (M - 1)])
    refine hdiff.trans ?_
    rw [hrpow_split]
    calc P * (x ^ (-s.re - ((M - 1 : ℕ) : ℝ)) * (1 / x ^ 2))
        ≤ P * (((N : ℝ) + 1) ^ (-s.re - ((M - 1 : ℕ) : ℝ)) * (1 / x ^ 2)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hmono (by positivity)) hP_nn
      _ = K * (1 / x ^ 2) := by dsimp [K]; ring
  have hmaj : Summable (fun j : ℕ => K * ((1 : ℝ) / ((N : ℝ) + 1 + 2 * (j : ℝ)) ^ 2)) :=
    (dqpt_summable_inv_sq_shift hN1).mul_left K
  have htsum_le : ‖∑' j : ℕ, (unitFallDiff^[M + 1] (dqptRp s)) ((N : ℝ) + 1 + 2 * (j : ℝ))‖ ≤
      K * (3 / (2 * ((N : ℝ) + 1))) := by
    calc ‖∑' j : ℕ, (unitFallDiff^[M + 1] (dqptRp s)) ((N : ℝ) + 1 + 2 * (j : ℝ))‖
        ≤ ∑' j : ℕ, K * ((1 : ℝ) / ((N : ℝ) + 1 + 2 * (j : ℝ)) ^ 2) :=
          tsum_of_norm_bounded hmaj.hasSum hpt
      _ = K * ∑' j : ℕ, (1 : ℝ) / ((N : ℝ) + 1 + 2 * (j : ℝ)) ^ 2 :=
          Summable.tsum_mul_left K (dqpt_summable_inv_sq_shift hN1)
      _ ≤ K * (3 / (2 * ((N : ℝ) + 1))) :=
          mul_le_mul_of_nonneg_left (dqpt_tsum_inv_sq_shift_le hN1) hK_nn
  have hdecomp := eta_eq_eulerEtaPartialSum_add_diffTail hs hs1 N M
  have hsub_eq : (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s - eulerEtaPartialSum N M s =
      (-1 : ℂ) ^ N * ((2 : ℂ) ^ M)⁻¹ *
        ∑' j : ℕ, (unitFallDiff^[M + 1] (dqptRp s)) ((N : ℝ) + 1 + 2 * (j : ℝ)) := by
    linear_combination hdecomp
  have hcoef_norm : ‖(-1 : ℂ) ^ N * ((2 : ℂ) ^ M)⁻¹‖ = ((2 : ℝ) ^ M)⁻¹ := by
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_inv, norm_pow]
    norm_num
  have hrpow_join : ((N : ℝ) + 1) ^ (-s.re - ((M - 1 : ℕ) : ℝ)) * ((N : ℝ) + 1)⁻¹ =
      ((N : ℝ) + 1) ^ (-s.re - (M : ℝ)) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hN0, hM_sub]
    congr 1
    ring
  rw [hsub_eq, norm_mul, hcoef_norm]
  calc ((2 : ℝ) ^ M)⁻¹ *
        ‖∑' j : ℕ, (unitFallDiff^[M + 1] (dqptRp s)) ((N : ℝ) + 1 + 2 * (j : ℝ))‖
      ≤ ((2 : ℝ) ^ M)⁻¹ * (K * (3 / (2 * ((N : ℝ) + 1)))) :=
        mul_le_mul_of_nonneg_left htsum_le (by positivity)
    _ = (3 / (2 : ℝ) ^ (M + 1)) * P *
          (((N : ℝ) + 1) ^ (-s.re - ((M - 1 : ℕ) : ℝ)) * ((N : ℝ) + 1)⁻¹) := by
        dsimp [K]
        rw [pow_succ]
        field_simp [hN0.ne']
    _ = eulerEtaTailBound N M s := by
        rw [hrpow_join]
        rfl

/-! ### 4. Exponential Collapse at Linear Prefix Length `N = 2 M` (`O(|Im s|)` Terms) -/

private lemma norm_add_nat_le_two_mul_add_one {s : ℂ} (hs0 : 0 ≤ s.re) (hs1 : s.re ≤ 1)
    {M m : ℕ} (him : |s.im| ≤ (M : ℝ)) (hm : m ≤ M) :
    ‖s + (m : ℂ)‖ ≤ ((2 * M : ℕ) : ℝ) + 1 := by
  have hdecomp : s + (m : ℂ) = ((s.re + (m : ℝ) : ℝ) : ℂ) + (s.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  rw [hdecomp]
  refine (norm_add_le _ _).trans ?_
  rw [Complex.norm_real, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hmR : (m : ℝ) ≤ (M : ℝ) := by exact_mod_cast hm
  push_cast
  linarith

/-- **Uniform exponential collapse at linear prefix `N = 2 M` (`3 M` total terms):** for every
`0 < Re s ≤ 1` and `|Im s| ≤ M` (`M ≥ 1`), every Pochhammer factor `1 ≤ m ≤ M` satisfies
`‖s + m‖ ≤ 2 M + 1`, cancelling `(2 M + 1)^{-M}` completely and bounding `eulerEtaTailBound (2 M) M s`
uniformly across all `0 < Re s ≤ 1` by `3 (2 M + 1) / 2^{M + 1}`. -/
theorem eulerEtaTailBound_two_mul_le {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re ≤ 1)
    {M : ℕ} (_hM : 1 ≤ M) (him : |s.im| ≤ (M : ℝ)) :
    eulerEtaTailBound (2 * M) M s ≤
      (3 / (2 : ℝ) ^ (M + 1)) * ‖s‖ * (((2 * M : ℕ) : ℝ) + 1) ^ (-s.re) ∧
    eulerEtaTailBound (2 * M) M s ≤
      3 * (((2 * M : ℕ) : ℝ) + 1) / (2 : ℝ) ^ (M + 1) := by
  set B : ℝ := ((2 * M : ℕ) : ℝ) + 1
  have hB_pos : 0 < B := by positivity
  have hB_ge1 : 1 ≤ B := by dsimp [B]; linarith [Nat.cast_nonneg (α := ℝ) (2 * M)]
  have hprod_le : (∏ m ∈ Finset.range (M + 1), ‖s + (m : ℂ)‖) ≤ ‖s‖ * B ^ M := by
    rw [Finset.prod_range_succ' (fun m => ‖s + (m : ℂ)‖) M, Nat.cast_zero, add_zero, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg s)
    calc (∏ m ∈ Finset.range M, ‖s + ((m + 1 : ℕ) : ℂ)‖)
        ≤ ∏ _m ∈ Finset.range M, B := by
          refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun m hm => ?_
          exact norm_add_nat_le_two_mul_add_one hs0.le hs1 him
            (by have := Finset.mem_range.mp hm; omega)
      _ = B ^ M := by rw [Finset.prod_const, Finset.card_range]
  have hrpow_cancel : B ^ M * B ^ (-s.re - (M : ℝ)) = B ^ (-s.re) := by
    rw [← Real.rpow_natCast B M, ← Real.rpow_add hB_pos]
    congr 1
    ring
  have h1 : eulerEtaTailBound (2 * M) M s ≤ (3 / (2 : ℝ) ^ (M + 1)) * ‖s‖ * B ^ (-s.re) := by
    unfold eulerEtaTailBound
    calc (3 / (2 : ℝ) ^ (M + 1)) * (∏ m ∈ Finset.range (M + 1), ‖s + (m : ℂ)‖) *
            B ^ (-s.re - (M : ℝ))
        ≤ (3 / (2 : ℝ) ^ (M + 1)) * (‖s‖ * B ^ M) * B ^ (-s.re - (M : ℝ)) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hB_pos.le _)
          exact mul_le_mul_of_nonneg_left hprod_le (by positivity)
      _ = (3 / (2 : ℝ) ^ (M + 1)) * ‖s‖ * (B ^ M * B ^ (-s.re - (M : ℝ))) := by ring
      _ = (3 / (2 : ℝ) ^ (M + 1)) * ‖s‖ * B ^ (-s.re) := by rw [hrpow_cancel]
  have hs_le_B : ‖s‖ ≤ B := by
    simpa only [Nat.cast_zero, add_zero] using
      norm_add_nat_le_two_mul_add_one hs0.le hs1 him (Nat.zero_le M)
  have hrpow_le1 : B ^ (-s.re) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hB_ge1 (by linarith)
  refine ⟨h1, h1.trans ?_⟩
  calc (3 / (2 : ℝ) ^ (M + 1)) * ‖s‖ * B ^ (-s.re)
      ≤ (3 / (2 : ℝ) ^ (M + 1)) * B * 1 := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hs_le_B (by positivity))
          hrpow_le1 (Real.rpow_nonneg hB_pos.le _) (by positivity)
    _ = 3 * B / (2 : ℝ) ^ (M + 1) := by ring

private lemma two_mul_add_one_le_two_pow_div_two {M : ℕ} (hM : 10 ≤ M) :
    2 * M + 1 ≤ 2 ^ (M / 2) := by
  have h5 : 5 ≤ M / 2 := by omega
  have hbase : ∀ k : ℕ, 5 ≤ k → 4 * k + 3 ≤ 2 ^ k := by
    refine Nat.le_induction (by decide) fun k hk ih => ?_
    rw [pow_succ]
    omega
  have hk := hbase (M / 2) h5
  omega

/-- For all `M ≥ 10` with `|Im s| ≤ M` and `0 < Re s ≤ 1`, the `3 M`-term Euler–Knopp tail is at
most `3 / 2^{M / 2}`, purely exponential in `M` and independent of `Re s`. -/
theorem eulerEtaTailBound_two_mul_le_three_div_two_pow_half {s : ℂ} (hs0 : 0 < s.re)
    (hs1 : s.re ≤ 1) {M : ℕ} (hM : 10 ≤ M) (him : |s.im| ≤ (M : ℝ)) :
    eulerEtaTailBound (2 * M) M s ≤ 3 / (2 : ℝ) ^ (M / 2) := by
  refine (eulerEtaTailBound_two_mul_le hs0 hs1 (by omega) him).2.trans ?_
  have hnat : 2 * M + 1 ≤ 2 ^ (M / 2) := two_mul_add_one_le_two_pow_div_two hM
  have hpow : 2 ^ (M / 2) * 2 ^ (M / 2) ≤ 2 ^ (M + 1) := by
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by omega : M / 2 + M / 2 ≤ M + 1)
  have hR1 : (((2 * M : ℕ) : ℝ) + 1) ≤ (2 : ℝ) ^ (M / 2) := by exact_mod_cast hnat
  have hR2 : (2 : ℝ) ^ (M / 2) * (2 : ℝ) ^ (M / 2) ≤ (2 : ℝ) ^ (M + 1) := by exact_mod_cast hpow
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [show (0 : ℝ) < (2 : ℝ) ^ (M / 2) by positivity]

private lemma three_mul_two_mul_add_one_div_two_pow_antitone {k m : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m) :
    3 * (((2 * m : ℕ) : ℝ) + 1) / (2 : ℝ) ^ (m + 1) ≤
      3 * (((2 * k : ℕ) : ℝ) + 1) / (2 : ℝ) ^ (k + 1) := by
  refine Nat.le_induction le_rfl (fun n hkn ih => ?_) m hkm
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_trans hk hkn
  have hstep : 3 * (((2 * (n + 1) : ℕ) : ℝ) + 1) / (2 : ℝ) ^ (n + 2) ≤
      3 * (((2 * n : ℕ) : ℝ) + 1) / (2 : ℝ) ^ (n + 1) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hpow : (2 : ℝ) ^ (n + 2) = 2 * (2 : ℝ) ^ (n + 1) := by ring
    rw [hpow]
    have hlin : 3 * (((2 * (n + 1) : ℕ) : ℝ) + 1) ≤ 6 * (((2 * n : ℕ) : ℝ) + 1) := by
      push_cast; linarith
    have hp : 0 < (2 : ℝ) ^ (n + 1) := by positivity
    nlinarith
  exact hstep.trans ih

/-- Across the entire unverified strip frontier `|Im s| > 184` (`0 < Re s ≤ 1`), choosing linear
order `M = ⌈|Im s|⌉₊` (`≥ 185`, using `3 ⌈|Im s|⌉₊` Dirichlet terms — `555` terms near height `185`
instead of `185^8 > 10^{18}` for raw `η`) forces the unconditional `ζ`-free remainder strictly
below `10^{-52}`. -/
theorem eulerEtaTailBound_above_oneHundredEightyFour_lt {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re ≤ 1)
    (him : 184 < |s.im|) :
    let M := Nat.ceil |s.im|
    ‖(1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s - eulerEtaPartialSum (2 * M) M s‖ ≤
      eulerEtaTailBound (2 * M) M s ∧
    eulerEtaTailBound (2 * M) M s < (1 : ℝ) / 10 ^ 52 := by
  dsimp only
  set M := Nat.ceil |s.im|
  have hM185 : 185 ≤ M := by
    have : 184 < M := (Nat.lt_ceil).mpr (by exact_mod_cast him)
    omega
  have hs_ne1 : s ≠ 1 := fun h => by rw [h, Complex.one_im, abs_zero] at him; linarith
  have him_le : |s.im| ≤ (M : ℝ) := Nat.le_ceil |s.im|
  refine ⟨norm_eta_sub_eulerEtaPartialSum_le hs0 hs_ne1 (2 * M) M (by omega), ?_⟩
  have h2 := (eulerEtaTailBound_two_mul_le hs0 hs1 (by omega) him_le).2
  have hanti := three_mul_two_mul_add_one_div_two_pow_antitone (by norm_num : 1 ≤ 185) hM185
  have hnum : 3 * (((2 * 185 : ℕ) : ℝ) + 1) / (2 : ℝ) ^ (185 + 1) < (1 : ℝ) / 10 ^ 52 := by
    norm_num
  linarith

/-! ### 5. Zero-Locking, Logarithmic Sensitivity on Shadowed Ordinates, and `RiemannHypothesis` Equivalence -/

/-- **Zero-exclusion criterion:** if any `(N, M)` Euler–Knopp signed partial sum (`M ≥ 1`) beats its
explicit `ζ`-free tail `eulerEtaTailBound N M s`, then `(1 - 2^{1-s}) ζ(s) ≠ 0` and `ζ(s) ≠ 0`. -/
theorem zeta_ne_zero_of_eulerEtaPartialSum_beats_tail {s : ℂ} (hs0 : 0 < s.re) (hs1 : s ≠ 1)
    {N M : ℕ} (hM : 1 ≤ M)
    (hbeat : eulerEtaTailBound N M s < ‖eulerEtaPartialSum N M s‖) :
    (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s ≠ 0 ∧ riemannZeta s ≠ 0 := by
  have htb := norm_eta_sub_eulerEtaPartialSum_le hs0 hs1 N M hM
  have hη : (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s ≠ 0 := by
    intro h0
    rw [h0, zero_sub, norm_neg] at htb
    linarith
  exact ⟨hη, right_ne_zero_of_mul hη⟩

/-- **Exponential zero-locking law:** at any hypothetical `ζ`-zero (`0 < Re s`, `s ≠ 1`), every
Euler–Knopp signed partial sum (`M ≥ 1`) is locked below `eulerEtaTailBound N M s`; in particular,
above height `184` in the strip, `‖eulerEtaPartialSum (2 ⌈|Im s|⌉₊) ⌈|Im s|⌉₊ s‖ < 10^{-52}`. -/
theorem norm_eulerEtaPartialSum_le_tail_of_zeta_eq_zero {s : ℂ} (hs0 : 0 < s.re) (hs1 : s ≠ 1)
    (hz : riemannZeta s = 0) :
    (∀ (N M : ℕ), 1 ≤ M → ‖eulerEtaPartialSum N M s‖ ≤ eulerEtaTailBound N M s) ∧
    (s.re ≤ 1 → 184 < |s.im| →
      ‖eulerEtaPartialSum (2 * Nat.ceil |s.im|) (Nat.ceil |s.im|) s‖ < (1 : ℝ) / 10 ^ 52) := by
  have hall : ∀ (N M : ℕ), 1 ≤ M → ‖eulerEtaPartialSum N M s‖ ≤ eulerEtaTailBound N M s := by
    intro N M hM
    have htb := norm_eta_sub_eulerEtaPartialSum_le hs0 hs1 N M hM
    rwa [hz, mul_zero, zero_sub, norm_neg] at htb
  refine ⟨hall, fun hre1 him => ?_⟩
  have hlt := (eulerEtaTailBound_above_oneHundredEightyFour_lt hs0 hre1 him).2
  have hM1 : 1 ≤ Nat.ceil |s.im| := by
    have : 184 < Nat.ceil |s.im| := (Nat.lt_ceil).mpr (by exact_mod_cast him)
    omega
  exact (hall (2 * Nat.ceil |s.im|) (Nat.ceil |s.im|) hM1).trans_lt hlt

/-- **Logarithmic sensitivity on Speiser-shadowed ordinates:** whenever
`‖(1 - 2^{1-s}) ζ(s)‖ > 6 / 2^K` (`0 < Re s < 1`), the single explicit `3 M`-term dyadic-signed
partial sum at `M = max 10 (max ⌈|Im s|⌉₊ (2 K))` (`O(|Im s| + K)` terms, independent of `1 / Re s`)
strictly beats both `eulerEtaTailBound (2 M) M s` and `3 / 2^{M / 2}`. -/
theorem eulerEtaPartialSum_beats_tail_of_eta_lower_bound {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1)
    {K : ℕ} (hη : (6 : ℝ) / (2 : ℝ) ^ K < ‖(1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s‖) :
    let M := max 10 (max (Nat.ceil |s.im|) (2 * K))
    eulerEtaTailBound (2 * M) M s ≤ 3 / (2 : ℝ) ^ (M / 2) ∧
    3 / (2 : ℝ) ^ (M / 2) < ‖eulerEtaPartialSum (2 * M) M s‖ := by
  dsimp only
  set M := max 10 (max (Nat.ceil |s.im|) (2 * K))
  have hM10 : 10 ≤ M := le_max_left _ _
  have him_le : |s.im| ≤ (M : ℝ) :=
    (Nat.le_ceil |s.im|).trans (by exact_mod_cast (le_max_left _ _).trans (le_max_right 10 _))
  have h2K : 2 * K ≤ M := (le_max_right _ _).trans (le_max_right 10 _)
  have hKM : K ≤ M / 2 := by omega
  have hs_ne1 : s ≠ 1 := fun h => hs1.ne (by rw [h, Complex.one_re])
  have hM1 : 1 ≤ M := le_trans (by norm_num : 1 ≤ 10) hM10
  have htb := norm_eta_sub_eulerEtaPartialSum_le hs0 hs_ne1 (2 * M) M hM1
  have hexp := eulerEtaTailBound_two_mul_le_three_div_two_pow_half hs0 hs1.le hM10 him_le
  have hpow : (2 : ℝ) ^ K ≤ (2 : ℝ) ^ (M / 2) := by
    exact_mod_cast Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hKM
  have hK_le : (3 : ℝ) / (2 : ℝ) ^ (M / 2) ≤ (3 : ℝ) / (2 : ℝ) ^ K :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) hpow
  have htri : ‖(1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s‖ ≤
      ‖eulerEtaPartialSum (2 * M) M s‖ +
        ‖(1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s - eulerEtaPartialSum (2 * M) M s‖ := by
    simpa only [add_sub_cancel] using norm_add_le (eulerEtaPartialSum (2 * M) M s)
      ((1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s - eulerEtaPartialSum (2 * M) M s)
  have hhalf : (6 : ℝ) / (2 : ℝ) ^ K = 2 * ((3 : ℝ) / (2 : ℝ) ^ K) := by ring
  exact ⟨hexp, by linarith⟩

/-- **Pointwise strip characterization:** at every `0 < Re s < 1`, `riemannZeta s ≠ 0` if and only
if some linear-scale `3 M`-term Euler–Knopp signed partial sum (`M ≥ max 10 ⌈|Im s|⌉₊`) beats the
`Re s`-independent exponential bound `3 / 2^{M / 2}` (and equivalently beats `eulerEtaTailBound (2 M) M s`). -/
theorem exists_linear_eulerEtaPartialSum_beats_tail_iff_zeta_ne_zero
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    ((∃ M : ℕ, max 10 (Nat.ceil |s.im|) ≤ M ∧
        3 / (2 : ℝ) ^ (M / 2) < ‖eulerEtaPartialSum (2 * M) M s‖) ↔ riemannZeta s ≠ 0) ∧
    ((∃ M : ℕ, max 1 (Nat.ceil |s.im|) ≤ M ∧
        eulerEtaTailBound (2 * M) M s < ‖eulerEtaPartialSum (2 * M) M s‖) ↔ riemannZeta s ≠ 0) := by
  have hs_ne1 : s ≠ 1 := fun h => hs1.ne (by rw [h, Complex.one_re])
  have h1m2_ne : 1 - (2 : ℂ) ^ (1 - s) ≠ 0 := by
    intro h0
    have h2_gt1 : (1 : ℝ) < (2 : ℝ) ^ (1 - s.re) := Real.one_lt_rpow one_lt_two (sub_pos.mpr hs1)
    have hn : ‖(2 : ℂ) ^ (1 - s)‖ = (2 : ℝ) ^ (1 - s.re) := by
      rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.norm_cpow_eq_rpow_re_of_pos two_pos,
        Complex.sub_re, Complex.one_re]
    have h := norm_sub_norm_le ((2 : ℂ) ^ (1 - s)) 1
    rw [norm_sub_rev, h0, norm_zero, hn, norm_one] at h
    linarith
  have hconstruct : riemannZeta s ≠ 0 →
      ∃ M : ℕ, max 10 (Nat.ceil |s.im|) ≤ M ∧
        eulerEtaTailBound (2 * M) M s ≤ 3 / (2 : ℝ) ^ (M / 2) ∧
        3 / (2 : ℝ) ^ (M / 2) < ‖eulerEtaPartialSum (2 * M) M s‖ := by
    intro hζ
    set δ : ℝ := ‖(1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s‖
    have hδ_pos : 0 < δ := norm_pos_iff.mpr (mul_ne_zero h1m2_ne hζ)
    set K : ℕ := Nat.ceil (6 / δ) + 1
    have h6_div_lt_K : 6 / δ < (K : ℝ) := by
      have hle : 6 / δ ≤ (Nat.ceil (6 / δ) : ℝ) := Nat.le_ceil (6 / δ)
      dsimp [K]; push_cast; linarith
    have hK_le_pow : (K : ℝ) ≤ (2 : ℝ) ^ K := by
      exact_mod_cast (Nat.lt_two_pow_self (n := K)).le
    have h6_lt : (6 : ℝ) / (2 : ℝ) ^ K < δ := by
      rw [div_lt_iff₀ (by positivity)]
      have h1 : 6 < (K : ℝ) * δ := (div_lt_iff₀ hδ_pos).mp h6_div_lt_K
      nlinarith
    have hres := eulerEtaPartialSum_beats_tail_of_eta_lower_bound hs0 hs1 h6_lt
    dsimp only at hres
    refine ⟨max 10 (max (Nat.ceil |s.im|) (2 * K)), ?_, hres.1, hres.2⟩
    exact max_le (le_max_left _ _) ((le_max_left _ _).trans (le_max_right 10 _))
  refine ⟨⟨?_, fun hζ => ?_⟩, ⟨?_, fun hζ => ?_⟩⟩
  · rintro ⟨M, hM, hbeat⟩
    have hM10 : 10 ≤ M := (le_max_left _ _).trans hM
    have him_le : |s.im| ≤ (M : ℝ) :=
      (Nat.le_ceil |s.im|).trans (by exact_mod_cast (le_max_right 10 _).trans hM)
    have hexp := eulerEtaTailBound_two_mul_le_three_div_two_pow_half hs0 hs1.le hM10 him_le
    exact (zeta_ne_zero_of_eulerEtaPartialSum_beats_tail hs0 hs_ne1 (N := 2 * M) (M := M)
      (le_trans (by norm_num : 1 ≤ 10) hM10) (hexp.trans_lt hbeat)).2
  · obtain ⟨M, hM, _, hbeat⟩ := hconstruct hζ
    exact ⟨M, hM, hbeat⟩
  · rintro ⟨M, hM, hbeat⟩
    exact (zeta_ne_zero_of_eulerEtaPartialSum_beats_tail hs0 hs_ne1
      ((le_max_left _ _).trans hM) hbeat).2
  · obtain ⟨M, hM, hexp, hbeat⟩ := hconstruct hζ
    exact ⟨M, max_le (by omega) ((le_max_right 10 _).trans hM), hexp.trans_lt hbeat⟩

/-- **Zero-exception linear-scale Euler–Knopp certification through height `184`:** every off-line
point `0 < Re s < 1`, `Re s ≠ 1 / 2`, `|Im s| ≤ 184` is certified directly by a `3 M`-term
dyadic-signed Dirichlet partial sum (`M ≥ max 10 ⌈|Im s|⌉₊`, zero search over omissions or divisor
packets) beating its `Re s`-uniform exponential tail `3 / 2^{M / 2}` both at `s` and at `1 - conj s`. -/
theorem zero_exception_euler_linear_through_oneHundredEightyFour
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) (hne_half : s.re ≠ 1 / 2) (him : |s.im| ≤ 184) :
    (∃ M : ℕ, max 10 (Nat.ceil |s.im|) ≤ M ∧
      eulerEtaTailBound (2 * M) M s ≤ 3 / (2 : ℝ) ^ (M / 2) ∧
      3 / (2 : ℝ) ^ (M / 2) < ‖eulerEtaPartialSum (2 * M) M s‖) ∧
    (∃ M : ℕ, max 10 (Nat.ceil |s.im|) ≤ M ∧
      eulerEtaTailBound (2 * M) M (1 - conj s) ≤ 3 / (2 : ℝ) ^ (M / 2) ∧
      3 / (2 : ℝ) ^ (M / 2) < ‖eulerEtaPartialSum (2 * M) M (1 - conj s)‖) := by
  have hζ_s := (riemannZeta_ne_zero_of_strip_abs_im_le_oneHundredEightyFour
    hs0 hs1 hne_half him).1
  obtain ⟨M₁, hM₁, hbeat₁⟩ :=
    (exists_linear_eulerEtaPartialSum_beats_tail_iff_zeta_ne_zero hs0 hs1).1.mpr hζ_s
  have him₁ : |s.im| ≤ (M₁ : ℝ) :=
    (Nat.le_ceil |s.im|).trans (by exact_mod_cast (le_max_right 10 _).trans hM₁)
  have hexp₁ := eulerEtaTailBound_two_mul_le_three_div_two_pow_half hs0 hs1.le
    ((le_max_left _ _).trans hM₁) him₁
  set w : ℂ := 1 - conj s
  have hw_re : w.re = 1 - s.re := by simp [w]
  have hw_im : |w.im| = |s.im| := by
    have : w.im = s.im := by simp [w]
    rw [this]
  have hw0 : 0 < w.re := by linarith
  have hw1 : w.re < 1 := by linarith
  have hw_ne_half : w.re ≠ 1 / 2 := fun h => hne_half (by linarith)
  have hζ_w := (riemannZeta_ne_zero_of_strip_abs_im_le_oneHundredEightyFour
    hw0 hw1 hw_ne_half (by rwa [hw_im])).1
  obtain ⟨M₂, hM₂, hbeat₂⟩ :=
    (exists_linear_eulerEtaPartialSum_beats_tail_iff_zeta_ne_zero hw0 hw1).1.mpr hζ_w
  rw [hw_im] at hM₂
  have him₂ : |w.im| ≤ (M₂ : ℝ) := by
    rw [hw_im]
    exact (Nat.le_ceil |s.im|).trans (by exact_mod_cast (le_max_right 10 _).trans hM₂)
  have hexp₂ := eulerEtaTailBound_two_mul_le_three_div_two_pow_half hw0 hw1.le
    ((le_max_left _ _).trans hM₂) him₂
  exact ⟨⟨M₁, hM₁, hexp₁, hbeat₁⟩, ⟨M₂, hM₂, hexp₂, hbeat₂⟩⟩

/-- **Unconditional `RiemannHypothesis` equivalence with `O(|Im s|)`-length Euler–Knopp signed
partial sums above height `184`:** `RiemannHypothesis` holds if and only if at every remaining point
`3001 / 24000 ≤ Re s < 1 / 2`, `184 < |Im s|`, some `3 M`-term dyadic-signed partial sum
`eulerEtaPartialSum (2 M) M s` (`M ≥ ⌈|Im s|⌉₊`, zero search over omissions or divisor packets,
uniform in `Re s`) beats the exponential bound `3 / 2^{M / 2}` (and equivalently beats
`eulerEtaTailBound (2 M) M s`). -/
theorem rh_iff_linear_euler_signedPartialSum_above_oneHundredEightyFour :
    (RiemannHypothesis ↔
      ∀ s : ℂ, 3001 / 24000 ≤ s.re → s.re < 1 / 2 → 184 < |s.im| →
        ∃ M : ℕ, Nat.ceil |s.im| ≤ M ∧
          3 / (2 : ℝ) ^ (M / 2) < ‖eulerEtaPartialSum (2 * M) M s‖) ∧
    (RiemannHypothesis ↔
      ∀ s : ℂ, 3001 / 24000 ≤ s.re → s.re < 1 / 2 → 184 < |s.im| →
        ∃ M : ℕ, Nat.ceil |s.im| ≤ M ∧
          eulerEtaTailBound (2 * M) M s < ‖eulerEtaPartialSum (2 * M) M s‖) := by
  have hdiv_rh := (rh_iff_exists_divisorSigned_partialSum_above_oneHundredEightyFour
    (Λ := 1) one_pos).2.1
  have hiff1 : (∀ s : ℂ, 3001 / 24000 ≤ s.re → s.re < 1 / 2 → 184 < |s.im| →
        ∃ (M : ℕ) (b : ℕ → ℝ) (N : ℕ),
          (∑ m ∈ Finset.Icc 1 M, b m / (m : ℝ)) = 0 ∧
          divisorPacketL1 M b * (‖s‖ / s.re) * occupationWeight N ^ s.re <
            ‖divisorSignedPartialSum M b N s‖) ↔
      ∀ s : ℂ, 3001 / 24000 ≤ s.re → s.re < 1 / 2 → 184 < |s.im| →
        ∃ M : ℕ, Nat.ceil |s.im| ≤ M ∧
          3 / (2 : ℝ) ^ (M / 2) < ‖eulerEtaPartialSum (2 * M) M s‖ := by
    refine forall₄_congr fun s hlo hhi him => ?_
    have hs0 : 0 < s.re := by linarith
    have hs1 : s.re < 1 := by linarith
    have hceil185 : 185 ≤ Nat.ceil |s.im| := by
      have : 184 < Nat.ceil |s.im| := (Nat.lt_ceil).mpr (by exact_mod_cast him)
      omega
    have hmax10 : max 10 (Nat.ceil |s.im|) = Nat.ceil |s.im| :=
      max_eq_right (by omega)
    rw [exists_divisorSignedPartialSum_beats_tail_iff_zeta_ne_zero hs0 hs1,
      ← (exists_linear_eulerEtaPartialSum_beats_tail_iff_zeta_ne_zero hs0 hs1).1, hmax10]
  have hiff2 : (∀ s : ℂ, 3001 / 24000 ≤ s.re → s.re < 1 / 2 → 184 < |s.im| →
        ∃ (M : ℕ) (b : ℕ → ℝ) (N : ℕ),
          (∑ m ∈ Finset.Icc 1 M, b m / (m : ℝ)) = 0 ∧
          divisorPacketL1 M b * (‖s‖ / s.re) * occupationWeight N ^ s.re <
            ‖divisorSignedPartialSum M b N s‖) ↔
      ∀ s : ℂ, 3001 / 24000 ≤ s.re → s.re < 1 / 2 → 184 < |s.im| →
        ∃ M : ℕ, Nat.ceil |s.im| ≤ M ∧
          eulerEtaTailBound (2 * M) M s < ‖eulerEtaPartialSum (2 * M) M s‖ := by
    refine forall₄_congr fun s hlo hhi him => ?_
    have hs0 : 0 < s.re := by linarith
    have hs1 : s.re < 1 := by linarith
    have hceil185 : 185 ≤ Nat.ceil |s.im| := by
      have : 184 < Nat.ceil |s.im| := (Nat.lt_ceil).mpr (by exact_mod_cast him)
      omega
    have hmax1 : max 1 (Nat.ceil |s.im|) = Nat.ceil |s.im| :=
      max_eq_right (by omega)
    rw [exists_divisorSignedPartialSum_beats_tail_iff_zeta_ne_zero hs0 hs1,
      ← (exists_linear_eulerEtaPartialSum_beats_tail_iff_zeta_ne_zero hs0 hs1).2, hmax1]
  exact ⟨hdiv_rh.trans hiff1, hdiv_rh.trans hiff2⟩

#print axioms iterate_unitFallDiff_eq_sum_choose
#print axioms norm_iterate_unitFallDiff_dqptRp_le
#print axioms eulerEtaSign_properties
#print axioms eulerEtaPartialSum_eq_avg_dqptAltPartialSum
#print axioms eta_eq_eulerEtaPartialSum_add_diffTail
#print axioms norm_eta_sub_eulerEtaPartialSum_le
#print axioms eulerEtaTailBound_two_mul_le
#print axioms eulerEtaTailBound_two_mul_le_three_div_two_pow_half
#print axioms eulerEtaTailBound_above_oneHundredEightyFour_lt
#print axioms zeta_ne_zero_of_eulerEtaPartialSum_beats_tail
#print axioms norm_eulerEtaPartialSum_le_tail_of_zeta_eq_zero
#print axioms eulerEtaPartialSum_beats_tail_of_eta_lower_bound
#print axioms exists_linear_eulerEtaPartialSum_beats_tail_iff_zeta_ne_zero
#print axioms zero_exception_euler_linear_through_oneHundredEightyFour
#print axioms rh_iff_linear_euler_signedPartialSum_above_oneHundredEightyFour

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas

end
