import GaloisForLFunctions.BiScaleUncertainty.CliqueSphereDualityAndExtremalTheory
import GaloisForLFunctions.BiScaleUncertainty.FoldedCollarIntegralAndObstructionResolution

/-!
# Pillar X: Periodic-Collar Clique Tiling, Square-Root Cancellation, and the Beurling–Turán Window Problem

This module establishes standalone harmonic-analysis and bi-scale window theorems in
`GaloisForLFunctions.BiScaleUncertainty` by combining Pillar V's **Multi-Node Clique Sphere
Duality** (`CliqueSphereDualityAndExtremalTheory.lean`) with exact periodic collar tiling.

## Main Results

1. **Exact Periodic-Collar Tiling Identity (`intervalIntegral_periodic_collar_sum_eq`):**
   For any continuous function `F : ℝ → ℝ`, base point `t₀ ∈ ℝ`, step `δ ∈ ℝ`, and `K : ℕ`,
   the integral over `[t₀, t₀ + K * δ]` decomposes into `K` shifted collars of width `δ`:
   `∫ x in t₀..(t₀ + K * δ), F x = ∫ y in 0..δ, ∑ k ∈ range K, F (t₀ + k * δ + y)`.
2. **Weighted Periodic-Clique Window Lower Bound (`integral_periodic_clique_weighted_sub_ge`):**
   If `h = autocorr f` vanishes at the `M` arithmetic multiples `m * δ` (`1 ≤ m ≤ M`, `δ ≥ 0`),
   then the `M + 1` nodes `t_k = k * δ` (`0 ≤ k ≤ M`) form a difference-orthogonal clique whose
   right collars `[k * δ, (k + 1) * δ]` tile `[0, (M + 1) * δ]`. For any continuous weight `w`,
   `(∫ y in 0..δ, cliqueSphereDualityFactor (range (M + 1)) (fun k => w (k * δ + y))) * h(0) ≤ ∫ x in 0..((M + 1) * δ), w x * (h(0) - h(x))`.
3. **The Beurling–Turán Window Divergence Theorem (`integral_autocorr_sub_ge_of_arithmetic_zeros`):**
   Setting `w ≡ 1` proves that if `h(m * δ) = 0` for `1 ≤ m ≤ M` (`δ ≥ 0`), then
   `δ * ((M + 1 : ℝ) - √(M + 1 : ℝ)) * h(0) ≤ ∫ x in 0..((M + 1) * δ), (h(0) - h(x))`.
4. **Square-Root Cancellation of the Autocorrelation Integral
   (`integral_autocorr_le_sqrt_of_arithmetic_zeros`):**
   Subtracting `(M + 1) * δ * h(0)` from both sides yields the sharp square-root cancellation law:
   `∫ x in 0..((M + 1) * δ), h(x) ≤ δ * √(M + 1 : ℝ) * h(0)`
   (improving the trivial Cauchy–Schwarz bound `(M + 1) * δ * h(0)` by a factor of `√(M + 1)`).
5. **Bi-Scale Lévy Energy Lower Bound Across Dyadic Logarithmic Chains
   (`biScaleLevyEnergy_ge_dyadic_clique_integral`):**
   Specializing to `t₀ = log 2`, `δ = log 2`, and `w = archLevySinhWeight` across the dyadic
   logarithmic progression `{log 2, 2 log 2, ..., M log 2}` bounds `biScaleLevyEnergy f` from below
   by the `M`-node clique sphere integral on `[log 2, (M + 1) log 2]`.
-/

open MeasureTheory Set Filter Topology Finset intervalIntegral
open scoped BigOperators
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section

/-! ## §1. Exact Periodic-Collar Tiling Identity -/

/-- Single-collar shift identity:
`∫ y in 0..δ, F (c + y) = ∫ x in c..(c + δ), F x`. -/
theorem intervalIntegral_collar_shift (F : ℝ → ℝ) (c δ : ℝ) :
    (∫ y in (0 : ℝ)..δ, F (c + y)) = ∫ x in c..(c + δ), F x := by
  have h := intervalIntegral.integral_comp_add_left F c (a := (0 : ℝ)) (b := δ)
  simpa only [add_zero] using h

/-- **Exact Periodic-Collar Tiling Identity:**
For any continuous function `F : ℝ → ℝ`, base point `t₀ ∈ ℝ`, step `δ ∈ ℝ`, and `K : ℕ`,
`∫ x in t₀..(t₀ + K * δ), F x = ∫ y in 0..δ, ∑ k ∈ range K, F (t₀ + k * δ + y)`. -/
theorem intervalIntegral_periodic_collar_sum_eq {F : ℝ → ℝ} (hF : Continuous F)
    (t₀ δ : ℝ) (K : ℕ) :
    (∫ x in t₀..(t₀ + (K : ℝ) * δ), F x) =
      ∫ y in (0 : ℝ)..δ, ∑ k ∈ Finset.range K, F (t₀ + (k : ℝ) * δ + y) := by
  have hsum_adj :
      (∫ x in t₀..(t₀ + (K : ℝ) * δ), F x) =
        ∑ k ∈ Finset.range K, ∫ y in (0 : ℝ)..δ, F (t₀ + (k : ℝ) * δ + y) := by
    induction K with
    | zero =>
      simp
    | succ K ih =>
      have split_pt :
          t₀ + ((K + 1 : ℕ) : ℝ) * δ = (t₀ + (K : ℝ) * δ) + δ := by
        push_cast; ring
      rw [Finset.sum_range_succ, ← ih, split_pt]
      have h1 : IntervalIntegrable F volume t₀ (t₀ + (K : ℝ) * δ) :=
        hF.intervalIntegrable _ _
      have h2 : IntervalIntegrable F volume (t₀ + (K : ℝ) * δ) ((t₀ + (K : ℝ) * δ) + δ) :=
        hF.intervalIntegrable _ _
      rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2,
        intervalIntegral_collar_shift F (t₀ + (K : ℝ) * δ) δ]
  rw [hsum_adj]
  refine (intervalIntegral.integral_finsetSum fun k _ => ?_).symm
  exact (hF.comp ((continuous_const.add continuous_id))).intervalIntegrable _ _

/-- **Periodic-Collar Tiling Identity on a Closed Interval:**
For any function `F : ℝ → ℝ`, base point `t₀ ∈ ℝ`, nonnegative step `0 ≤ δ`, and `K : ℕ`,
if `F` is continuous on `Icc t₀ (t₀ + K * δ)`, then
`∫ x in t₀..(t₀ + K * δ), F x = ∫ y in 0..δ, ∑ k ∈ range K, F (t₀ + k * δ + y)`. -/
theorem intervalIntegral_periodic_collar_sum_eq_of_continuousOn {F : ℝ → ℝ}
    {t₀ δ : ℝ} (hδ : 0 ≤ δ) (K : ℕ)
    (hF : ContinuousOn F (Icc t₀ (t₀ + (K : ℝ) * δ))) :
    (∫ x in t₀..(t₀ + (K : ℝ) * δ), F x) =
      ∫ y in (0 : ℝ)..δ, ∑ k ∈ Finset.range K, F (t₀ + (k : ℝ) * δ + y) := by
  have hsum_adj :
      (∫ x in t₀..(t₀ + (K : ℝ) * δ), F x) =
        ∑ k ∈ Finset.range K, ∫ y in (0 : ℝ)..δ, F (t₀ + (k : ℝ) * δ + y) := by
    induction K with
    | zero =>
      simp
    | succ K ih =>
      have split_pt :
          t₀ + ((K + 1 : ℕ) : ℝ) * δ = (t₀ + (K : ℝ) * δ) + δ := by
        push_cast; ring
      have hK_nonneg : 0 ≤ (K : ℝ) * δ := mul_nonneg (Nat.cast_nonneg K) hδ
      have hsub1 : Icc t₀ (t₀ + (K : ℝ) * δ) ⊆ Icc t₀ (t₀ + ((K + 1 : ℕ) : ℝ) * δ) := by
        intro x hx
        rw [Set.mem_Icc] at hx ⊢
        refine ⟨hx.1, ?_⟩
        rw [split_pt]
        linarith [hx.2]
      have hsub2 :
          Icc (t₀ + (K : ℝ) * δ) ((t₀ + (K : ℝ) * δ) + δ) ⊆
            Icc t₀ (t₀ + ((K + 1 : ℕ) : ℝ) * δ) := by
        intro x hx
        rw [Set.mem_Icc] at hx ⊢
        rw [split_pt]
        exact ⟨by linarith [hx.1], hx.2⟩
      have h1 : IntervalIntegrable F volume t₀ (t₀ + (K : ℝ) * δ) := by
        refine ContinuousOn.intervalIntegrable ?_
        rw [Set.uIcc_of_le (by linarith)]
        exact hF.mono hsub1
      have h2 : IntervalIntegrable F volume (t₀ + (K : ℝ) * δ) ((t₀ + (K : ℝ) * δ) + δ) := by
        refine ContinuousOn.intervalIntegrable ?_
        rw [Set.uIcc_of_le (by linarith)]
        exact hF.mono hsub2
      rw [Finset.sum_range_succ, ← ih (hF.mono hsub1), split_pt,
        ← intervalIntegral.integral_add_adjacent_intervals h1 h2,
        intervalIntegral_collar_shift F (t₀ + (K : ℝ) * δ) δ]
  rw [hsum_adj]
  refine (intervalIntegral.integral_finsetSum fun k hk => ?_).symm
  refine ContinuousOn.intervalIntegrable ?_
  rw [Set.uIcc_of_le hδ]
  refine hF.comp (continuous_const.add continuous_id).continuousOn ?_
  intro y hy
  rw [Set.mem_Icc] at hy ⊢
  have hk_lt : k < K := Finset.mem_range.mp hk
  have hk_le : (k : ℝ) + 1 ≤ (K : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hk_lt
  have hk_nonneg : 0 ≤ (k : ℝ) * δ := mul_nonneg (Nat.cast_nonneg k) hδ
  have hk_ub : (k : ℝ) * δ + δ ≤ (K : ℝ) * δ := by
    calc
      (k : ℝ) * δ + δ = ((k : ℝ) + 1) * δ := by ring
      _ ≤ (K : ℝ) * δ := mul_le_mul_of_nonneg_right hk_le hδ
  exact ⟨by linarith [hy.1], by linarith [hy.2]⟩

/-! ## §2. Difference-Orthogonality of Arithmetic & Dyadic Progressions -/

/-- If `autocorr f ((m : ℝ) * δ) = 0` for all `1 ≤ m ≤ M`, then the arithmetic progression
`t k = t₀ + (k : ℝ) * δ` is pairwise difference-orthogonal on `Finset.range (M + 1)`. -/
theorem arithmetic_progression_pairwise_orth {f : ℝ → ℝ} (t₀ δ : ℝ) (M : ℕ)
    (hzeros : ∀ m : ℕ, 1 ≤ m → m ≤ M → autocorr f ((m : ℝ) * δ) = 0) :
    ∀ i ∈ Finset.range (M + 1), ∀ j ∈ Finset.range (M + 1), i ≠ j →
      autocorr f ((t₀ + (i : ℝ) * δ) - (t₀ + (j : ℝ) * δ)) = 0 := by
  intro i hi j hj hij
  rw [Finset.mem_range] at hi hj
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have hm1 : 1 ≤ j - i := by omega
    have hm2 : j - i ≤ M := by omega
    have hdiff :
        (t₀ + (i : ℝ) * δ) - (t₀ + (j : ℝ) * δ) = -(((j - i : ℕ) : ℝ) * δ) := by
      rw [Nat.cast_sub hlt.le]
      ring
    rw [hdiff, autocorr_neg f (((j - i : ℕ) : ℝ) * δ)]
    exact hzeros (j - i) hm1 hm2
  · have hm1 : 1 ≤ i - j := by omega
    have hm2 : i - j ≤ M := by omega
    have hdiff :
        (t₀ + (i : ℝ) * δ) - (t₀ + (j : ℝ) * δ) = ((i - j : ℕ) : ℝ) * δ := by
      rw [Nat.cast_sub hgt.le]
      ring
    rw [hdiff]
    exact hzeros (i - j) hm1 hm2

/-! ## §3. Weighted Periodic-Clique Window Lower Bound & Square-Root Cancellation -/

/-- **Weighted Periodic-Clique Window Lower Bound:**
Let `f ∈ C²_c(ℝ)` satisfy `autocorr f ((m : ℝ) * δ) = 0` for `1 ≤ m ≤ K - 1` (`δ ≥ 0`).
Then for any base point `t₀ ∈ ℝ` and any continuous weight `w : ℝ → ℝ`,
`(∫ y in 0..δ, cliqueSphereDualityFactor (range K) (fun k => w (t₀ + k * δ + y))) * h(0) ≤ ∫ x in t₀..(t₀ + K * δ), w x * (h(0) - h(x))`. -/
theorem integral_periodic_clique_weighted_sub_ge {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (t₀ : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) (K : ℕ)
    (horth : ∀ i ∈ Finset.range K, ∀ j ∈ Finset.range K, i ≠ j →
      autocorr f ((t₀ + (i : ℝ) * δ) - (t₀ + (j : ℝ) * δ)) = 0)
    {w : ℝ → ℝ} (hw : Continuous w) :
    (∫ y in (0 : ℝ)..δ,
        cliqueSphereDualityFactor (Finset.range K) (fun k => w (t₀ + (k : ℝ) * δ + y))) *
      autocorr f 0 ≤
      ∫ x in t₀..(t₀ + (K : ℝ) * δ), w x * (autocorr f 0 - autocorr f x) := by
  have hc : Continuous (autocorr f) := continuous_autocorr hf hfc
  have hF : Continuous (fun x => w x * (autocorr f 0 - autocorr f x)) :=
    hw.mul (continuous_const.sub hc)
  rw [intervalIntegral_periodic_collar_sum_eq hF t₀ δ K]
  have hint_lhs :
      IntervalIntegrable
        (fun y =>
          cliqueSphereDualityFactor (Finset.range K) (fun k => w (t₀ + (k : ℝ) * δ + y)) *
            autocorr f 0)
        volume 0 δ := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hδ]
    refine (continuousOn_cliqueSphereDualityFactor (Finset.range K)
      (fun k y => w (t₀ + (k : ℝ) * δ + y)) ?_).mul continuousOn_const
    intro k _
    exact (hw.comp (continuous_const.add continuous_id)).continuousOn
  have hint_rhs :
      IntervalIntegrable
        (fun y =>
          ∑ k ∈ Finset.range K,
            w (t₀ + (k : ℝ) * δ + y) *
              (autocorr f 0 - autocorr f (t₀ + (k : ℝ) * δ + y)))
        volume 0 δ := by
    refine Continuous.intervalIntegrable ?_ _ _
    exact continuous_finsetSum (Finset.range K) fun k _ =>
      hF.comp (continuous_const.add continuous_id)
  have hmono :
      (∫ y in (0 : ℝ)..δ,
          cliqueSphereDualityFactor (Finset.range K) (fun k => w (t₀ + (k : ℝ) * δ + y)) *
            autocorr f 0) ≤
        ∫ y in (0 : ℝ)..δ,
          ∑ k ∈ Finset.range K,
            w (t₀ + (k : ℝ) * δ + y) *
              (autocorr f 0 - autocorr f (t₀ + (k : ℝ) * δ + y)) :=
    intervalIntegral.integral_mono_on hδ hint_lhs hint_rhs fun y _ =>
      autocorr_weighted_clique_right_collar_ge hfc hf.continuous (Finset.range K)
        (fun k => t₀ + (k : ℝ) * δ) horth (fun k => w (t₀ + (k : ℝ) * δ + y)) y
  rwa [intervalIntegral.integral_mul_const] at hmono

/-- **The Beurling–Turán Window Divergence Theorem:**
If `f ∈ C²_c(ℝ)` satisfies `autocorr f ((m : ℝ) * δ) = 0` for `1 ≤ m ≤ M` (`δ ≥ 0`), then
`δ * ((M + 1 : ℝ) - √(M + 1 : ℝ)) * autocorr f 0 ≤ ∫ x in 0..((M + 1) * δ), (autocorr f 0 - autocorr f x)`. -/
theorem integral_autocorr_sub_ge_of_arithmetic_zeros {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    {δ : ℝ} (hδ : 0 ≤ δ) (M : ℕ)
    (hzeros : ∀ m : ℕ, 1 ≤ m → m ≤ M → autocorr f ((m : ℝ) * δ) = 0) :
    δ * (((M + 1 : ℕ) : ℝ) - Real.sqrt ((M + 1 : ℕ) : ℝ)) * autocorr f 0 ≤
      ∫ x in (0 : ℝ)..(((M + 1 : ℕ) : ℝ) * δ), (autocorr f 0 - autocorr f x) := by
  have horth := arithmetic_progression_pairwise_orth 0 δ M hzeros
  have hbound := integral_periodic_clique_weighted_sub_ge hf hfc 0 hδ (M + 1) horth
    (w := fun _ => (1 : ℝ)) continuous_const
  have hfac :
      cliqueSphereDualityFactor (Finset.range (M + 1)) (fun _ => (1 : ℝ)) =
        ((M + 1 : ℕ) : ℝ) - Real.sqrt ((M + 1 : ℕ) : ℝ) := by
    have h := cliqueSphereDualityFactor_const (Finset.range (M + 1)) 1 zero_le_one
    simpa only [Finset.card_range, one_mul] using h
  simp only [hfac, intervalIntegral.integral_const, sub_zero, smul_eq_mul,
    zero_add, one_mul] at hbound
  exact hbound

/-- **Square-Root Cancellation of the Autocorrelation Integral:**
If `f ∈ C²_c(ℝ)` satisfies `autocorr f ((m : ℝ) * δ) = 0` for `1 ≤ m ≤ M` (`δ ≥ 0`), then
`∫ x in 0..((M + 1) * δ), autocorr f x ≤ δ * √(M + 1 : ℝ) * autocorr f 0`. -/
theorem integral_autocorr_le_sqrt_of_arithmetic_zeros {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    {δ : ℝ} (hδ : 0 ≤ δ) (M : ℕ)
    (hzeros : ∀ m : ℕ, 1 ≤ m → m ≤ M → autocorr f ((m : ℝ) * δ) = 0) :
    (∫ x in (0 : ℝ)..(((M + 1 : ℕ) : ℝ) * δ), autocorr f x) ≤
      δ * Real.sqrt ((M + 1 : ℕ) : ℝ) * autocorr f 0 := by
  have hsub := integral_autocorr_sub_ge_of_arithmetic_zeros hf hfc hδ M hzeros
  have hc : Continuous (autocorr f) := continuous_autocorr hf hfc
  have hsplit :
      (∫ x in (0 : ℝ)..(((M + 1 : ℕ) : ℝ) * δ), (autocorr f 0 - autocorr f x)) =
        (((M + 1 : ℕ) : ℝ) * δ) * autocorr f 0 -
          ∫ x in (0 : ℝ)..(((M + 1 : ℕ) : ℝ) * δ), autocorr f x := by
    rw [intervalIntegral.integral_sub (intervalIntegrable_const) (hc.intervalIntegrable _ _),
      intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  rw [hsplit] at hsub
  linarith

/-! ## §4. Bi-Scale Lévy Energy Lower Bound Across Dyadic Logarithmic Chains -/

/-- The `M`-node dyadic clique collar constant on `[log 2, (M + 1) log 2]`:
`∫ y in 0..(log 2), cliqueSphereDualityFactor (range M) (fun k => archLevySinhWeight ((k + 1) * log 2 + y))`. -/
def dyadicCliqueLevyConstant (M : ℕ) : ℝ :=
  ∫ y in (0 : ℝ)..Real.log 2,
    cliqueSphereDualityFactor (Finset.range M)
      (fun k => archLevySinhWeight (Real.log 2 + (k : ℝ) * Real.log 2 + y))

/-- **Bi-Scale Lévy Energy Lower Bound Across a Dyadic Logarithmic Progression:**
If `f ∈ C²_c(ℝ)` vanishes at the dyadic nodes `m * log 2` for `1 ≤ m ≤ M`, then
`dyadicCliqueLevyConstant M * autocorr f 0 ≤ biScaleLevyEnergy f`. -/
theorem biScaleLevyEnergy_ge_dyadic_clique_integral {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (M : ℕ)
    (hzeros : ∀ m : ℕ, 1 ≤ m → m ≤ M → autocorr f ((m : ℝ) * Real.log 2) = 0) :
    dyadicCliqueLevyConstant M * autocorr f 0 ≤ biScaleLevyEnergy f := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have horth_full := arithmetic_progression_pairwise_orth (Real.log 2) (Real.log 2) M hzeros
  have horth :
      ∀ i ∈ Finset.range M, ∀ j ∈ Finset.range M, i ≠ j →
        autocorr f ((Real.log 2 + (i : ℝ) * Real.log 2) -
          (Real.log 2 + (j : ℝ) * Real.log 2)) = 0 := by
    intro i hi j hj hij
    refine horth_full i ?_ j ?_ hij
    · rw [Finset.mem_range] at hi ⊢; omega
    · rw [Finset.mem_range] at hj ⊢; omega
  have hc : Continuous (autocorr f) := continuous_autocorr hf hfc
  set B := Real.log 2 + (M : ℝ) * Real.log 2
  have hB_ge : Real.log 2 ≤ B := by
    dsimp [B]
    have : 0 ≤ (M : ℝ) * Real.log 2 := mul_nonneg (Nat.cast_nonneg M) hlog2_pos.le
    linarith
  have hw_cont : ContinuousOn archLevySinhWeight (Icc (Real.log 2) B) :=
    continuousOn_archLevySinhWeight fun x hx => lt_of_lt_of_le hlog2_pos hx.1
  have hF_cont :
      ContinuousOn (fun x => archLevySinhWeight x * (autocorr f 0 - autocorr f x))
        (Icc (Real.log 2) B) :=
    hw_cont.mul (continuousOn_const.sub hc.continuousOn)
  have hshift_eq :
      (∫ x in Real.log 2..B, archLevySinhWeight x * (autocorr f 0 - autocorr f x)) =
        ∫ y in (0 : ℝ)..Real.log 2,
          ∑ k ∈ Finset.range M,
            archLevySinhWeight (Real.log 2 + (k : ℝ) * Real.log 2 + y) *
              (autocorr f 0 - autocorr f (Real.log 2 + (k : ℝ) * Real.log 2 + y)) :=
    intervalIntegral_periodic_collar_sum_eq_of_continuousOn hlog2_pos.le M hF_cont
  have hmaps : ∀ k ∈ Finset.range M,
      Set.MapsTo (fun y : ℝ => Real.log 2 + (k : ℝ) * Real.log 2 + y)
        (Icc 0 (Real.log 2)) (Icc (Real.log 2) B) := by
    intro k hk y hy
    rw [Set.mem_Icc] at hy ⊢
    have hk_lt : k < M := Finset.mem_range.mp hk
    have hk_le : (k : ℝ) + 1 ≤ (M : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hk_lt
    have hk_nonneg : 0 ≤ (k : ℝ) * Real.log 2 :=
      mul_nonneg (Nat.cast_nonneg k) hlog2_pos.le
    have hk_ub : (k : ℝ) * Real.log 2 + Real.log 2 ≤ (M : ℝ) * Real.log 2 := by
      calc
        (k : ℝ) * Real.log 2 + Real.log 2 = ((k : ℝ) + 1) * Real.log 2 := by ring
        _ ≤ (M : ℝ) * Real.log 2 := mul_le_mul_of_nonneg_right hk_le hlog2_pos.le
    dsimp [B]
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hint_lhs :
      IntervalIntegrable
        (fun y =>
          cliqueSphereDualityFactor (Finset.range M)
            (fun k => archLevySinhWeight (Real.log 2 + (k : ℝ) * Real.log 2 + y)) *
            autocorr f 0)
        volume 0 (Real.log 2) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hlog2_pos.le]
    refine (continuousOn_cliqueSphereDualityFactor (Finset.range M)
      (fun k y => archLevySinhWeight (Real.log 2 + (k : ℝ) * Real.log 2 + y)) ?_).mul
      continuousOn_const
    intro k hk
    exact hw_cont.comp (continuous_const.add continuous_id).continuousOn (hmaps k hk)
  have hint_rhs :
      IntervalIntegrable
        (fun y =>
          ∑ k ∈ Finset.range M,
            archLevySinhWeight (Real.log 2 + (k : ℝ) * Real.log 2 + y) *
              (autocorr f 0 - autocorr f (Real.log 2 + (k : ℝ) * Real.log 2 + y)))
        volume 0 (Real.log 2) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hlog2_pos.le]
    refine continuousOn_finsetSum (Finset.range M) fun k hk => ?_
    exact hF_cont.comp (continuous_const.add continuous_id).continuousOn (hmaps k hk)
  have hmono :
      dyadicCliqueLevyConstant M * autocorr f 0 ≤
        ∫ x in Real.log 2..B, archLevySinhWeight x * (autocorr f 0 - autocorr f x) := by
    unfold dyadicCliqueLevyConstant
    rw [← intervalIntegral.integral_mul_const, hshift_eq]
    exact intervalIntegral.integral_mono_on hlog2_pos.le hint_lhs hint_rhs fun y _ =>
      autocorr_weighted_clique_right_collar_ge hfc hf.continuous (Finset.range M)
        (fun k => Real.log 2 + (k : ℝ) * Real.log 2) horth
        (fun k => archLevySinhWeight (Real.log 2 + (k : ℝ) * Real.log 2 + y)) y
  have hcomm :
      (∫ x in Real.log 2..B, archLevySinhWeight x * (autocorr f 0 - autocorr f x)) =
        ∫ x in Ioc (Real.log 2) B, (autocorr f 0 - autocorr f x) * archLevySinhWeight x := by
    rw [intervalIntegral.integral_of_le hB_ge]
    refine setIntegral_congr_fun measurableSet_Ioc fun x _ => mul_comm _ _
  have hdom :
      (∫ x in Ioc (Real.log 2) B, (autocorr f 0 - autocorr f x) * archLevySinhWeight x) ≤
        biScaleLevyEnergy f := by
    unfold biScaleLevyEnergy
    refine setIntegral_mono_set (integrableOn_biScaleLevyIntegrand hf hfc) ?_ ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact mul_nonneg (autocorr_sub_nonneg hfc hf.continuous x) (archLevySinhWeight_pos hx).le
    · refine Eventually.of_forall fun x hx => ?_
      exact lt_trans hlog2_pos hx.1
  linarith

end

end GaloisForLFunctions.BiScaleUncertainty
