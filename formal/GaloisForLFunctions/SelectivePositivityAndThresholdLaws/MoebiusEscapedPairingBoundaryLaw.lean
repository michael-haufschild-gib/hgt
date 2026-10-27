import GaloisForLFunctions.ArithmeticCorrelationGeometry.TheMoebiusBoundarySeparatesGaugeTwins
import GaloisForLFunctions.BezoutValuationIncidence.TheVaughanEmptyLegReadsTheZeroAbscissa
import GaloisForLFunctions.RHTower.MobiusMertensEvenConvolutionExactOrder

/-!
# The Square-Root Boundary Law for Escaped Möbius Pairings

On the horizon space `HorizonSpace N`, the escaped pairing of the critical Möbius source
`μ(j) j^{-1/2}` against the flat critical source `j^{-1/2}` under the affine map `j ↦ a j + b` is
`escapedPairing N a b (moebiusSource N) (flatSource N) = ∑_{(N - b)/a < j ≤ N} μ(j) / j`.

This module establishes the complete three-regime classification of power-saving laws for this
escaped boundary pairing:

1. **Unconditional failure of unrestricted multiplier uniformity:** Across arbitrary multipliers
   `a : ℕ+`, adjacent multipliers `a = N` and `a = N + 1` at `b = 0` differ by the single atom
   `μ(1) / 1 = 1`, forcing `max(|escapedPairing N N 0|, |escapedPairing N (N + 1) 0|) ≥ 1 / 2` for
   every `N ≥ 1`. Consequently, no uniform `O(N^{-θ})` bound (`θ > 0`) can hold without controlling
   the escaped start `M = (N - b) / a`.
2. **Exact Quasi-Riemann and Riemann Hypothesis equivalence on the growing-endpoint regime:**
   For every `θ ∈ (0, 1/2]`, uniform power saving `O_ε(((N - b)/a)^{-θ + ε})` across all `N, a, b`
   with `1 ≤ (N - b)/a` is equivalent to the single dyadic-multiplier saving `O_ε(N^{-θ + ε})` at
   `a = 2, b = 0`, and both are unconditionally equivalent to the zero-free strip
   `zetaZeroAbscissa ≤ 1 - θ`. Holding across every `θ ∈ (0, 1/2)` is unconditionally equivalent
   to `RiemannHypothesis`.
3. **Unconditional refutation beyond the square-root exponent (`θ > 1/2`):** Even at the single
   fixed multiplier `a = 2, b = 0`, no bound `O(N^{-θ})` with `θ > 1/2` can hold, as dyadic
   telescoping and Abel summation would force `zetaZeroAbscissa < 1 / 2`, contradicting the
   critical-line lower bound `1 / 2 ≤ zetaZeroAbscissa`.
-/

open Finset Filter Topology RHTower
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open GaloisForLFunctions.ArithmeticCorrelationGeometry
open GaloisForLFunctions.BezoutValuationIncidence
open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace GaloisForLFunctions.SelectivePositivityAndThresholdLaws

set_option autoImplicit false

/-! ### 1. Unrestricted Multiplier Obstruction at the Escape Origin -/

/-- Adjacent multipliers `a = N` and `a = N + 1` at `b = 0` isolate the unit cell `j = 1`, so
their escaped Möbius pairings differ by `μ(1) / 1 = 1` for every `N ≥ 1`. -/
theorem escapedPairing_moebius_succ_sub_self {N : ℕ} (hN : 1 ≤ N) :
    escapedPairing N ⟨N + 1, by omega⟩ 0 (moebiusSource N) (flatSource N) -
      escapedPairing N ⟨N, by omega⟩ 0 (moebiusSource N) (flatSource N) = 1 := by
  rw [escapedPairing_moebiusSource, escapedPairing_moebiusSource]
  have hdiv1 : (N - 0) / (N + 1) = 0 := Nat.div_eq_of_lt (by omega)
  have hdiv2 : (N - 0) / N = 1 := by
    rw [Nat.sub_zero, Nat.div_self (by omega)]
  change (∑ j ∈ Ioc ((N - 0) / (N + 1)) N, (μ j : ℝ) / j) -
      (∑ j ∈ Ioc ((N - 0) / N) N, (μ j : ℝ) / j) = 1
  rw [hdiv1, hdiv2]
  have hsplit : Ioc 0 N = insert 1 (Ioc 1 N) := by
    ext j
    simp only [mem_Ioc, mem_insert]
    omega
  rw [hsplit, sum_insert (by simp), add_sub_cancel_right]
  simp

/-- For every `N ≥ 1`, at least one of the two multipliers `a = N` or `a = N + 1` produces escaped
Möbius pairing of magnitude at least `1 / 2`. -/
theorem half_le_max_abs_escapedPairing_moebius {N : ℕ} (hN : 1 ≤ N) :
    (1 / 2 : ℝ) ≤
      max |escapedPairing N ⟨N, by omega⟩ 0 (moebiusSource N) (flatSource N)|
        |escapedPairing N ⟨N + 1, by omega⟩ 0 (moebiusSource N) (flatSource N)| := by
  have hdiff := escapedPairing_moebius_succ_sub_self hN
  set x := escapedPairing N ⟨N, by omega⟩ 0 (moebiusSource N) (flatSource N)
  set y := escapedPairing N ⟨N + 1, by omega⟩ 0 (moebiusSource N) (flatSource N)
  have h1 : (1 : ℝ) ≤ |y| + |x| := by
    calc (1 : ℝ) = |y - x| := by rw [hdiff, abs_one]
      _ ≤ |y| + |x| := abs_sub y x
  have hxm : |x| ≤ max |x| |y| := le_max_left _ _
  have hym : |y| ≤ max |x| |y| := le_max_right _ _
  linarith

/-- **No-Go for Unrestricted Multiplier Uniformity:**
For every `θ > 0` and `C : ℝ`, there is no horizon-uniform bound
`|escapedPairing N a b (moebiusSource N) (flatSource N)| ≤ C * N^{-θ}` valid across all
`a : ℕ+` and `N ≥ 1` (already failing at `b = 0`). -/
theorem not_uniform_all_multipliers_escapedPairing_rpow {θ : ℝ} (hθ : 0 < θ) :
    ¬ ∃ C : ℝ, ∀ (N : ℕ) (a : ℕ+), 1 ≤ N →
      |escapedPairing N a 0 (moebiusSource N) (flatSource N)| ≤ C * (N : ℝ) ^ (-θ) := by
  rintro ⟨C, hC⟩
  have hlim : Tendsto (fun N : ℕ => C * (N : ℝ) ^ (-θ)) atTop (𝓝 0) := by
    simpa [mul_zero] using
      ((tendsto_rpow_neg_atTop hθ).comp tendsto_natCast_atTop_atTop).const_mul C
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.mp hlim (1 / 4) (by norm_num)
  let N := max N₀ 1
  have hN1 : 1 ≤ N := le_max_right _ _
  have hsmall : C * (N : ℝ) ^ (-θ) < 1 / 4 := by
    have hd := hN₀ N (le_max_left _ _)
    rw [Real.dist_eq, sub_zero] at hd
    exact (le_abs_self _).trans_lt hd
  have ha1 := hC N ⟨N, by omega⟩ hN1
  have ha2 := hC N ⟨N + 1, by omega⟩ hN1
  have hmax : max |escapedPairing N ⟨N, by omega⟩ 0 (moebiusSource N) (flatSource N)|
      |escapedPairing N ⟨N + 1, by omega⟩ 0 (moebiusSource N) (flatSource N)| ≤
        C * (N : ℝ) ^ (-θ) := max_le ha1 ha2
  have hhalf := half_le_max_abs_escapedPairing_moebius hN1
  linarith

/-! ### 2. Exact Abel Duality Between Reciprocal Möbius Tails and Mertens Sums -/

/-- The negated partial harmonic Möbius sum `R(N) = - ∑_{n ≤ N} μ(n) / n`, which converges to `0` by
the Prime Number Theorem (`tendsto_sum_range_succ_moebius_div`) and satisfies `R(0) = 0`. -/
def moebiusHarmonicTail (N : ℕ) : ℝ :=
  - ∑ n ∈ range (N + 1), (μ n : ℝ) / n

theorem moebiusHarmonicTail_zero : moebiusHarmonicTail 0 = 0 := by
  simp [moebiusHarmonicTail]

theorem moebiusHarmonicTail_step (N : ℕ) :
    ((N : ℝ) + 1) * (moebiusHarmonicTail N - moebiusHarmonicTail (N + 1)) =
      moebiusReal (N + 1) := by
  have hpos : ((N : ℝ) + 1) ≠ 0 := by positivity
  have hdiff : moebiusHarmonicTail N - moebiusHarmonicTail (N + 1) =
      (μ (N + 1) : ℝ) / ((N : ℝ) + 1) := by
    unfold moebiusHarmonicTail
    rw [Finset.sum_range_succ _ (N + 1), Nat.cast_add, Nat.cast_one]
    ring
  rw [hdiff, mul_div_cancel₀ _ hpos]
  rfl

/-- Exact zero-damping Abel identity reconstructing Mertens partial sums from
`moebiusHarmonicTail` with unit weight increments and zero origin constant. -/
theorem sum_moebiusReal_eq_moebiusHarmonicTail_abel (N : ℕ) :
    (∑ n ∈ Icc 1 N, moebiusReal n) =
      -((N : ℝ) + 1) * moebiusHarmonicTail N +
        ∑ n ∈ Icc 1 N, moebiusHarmonicTail n := by
  induction N with
  | zero => simp [moebiusHarmonicTail_zero]
  | succ N ih =>
    rw [sum_Icc_succ_top (by omega : 1 ≤ N + 1), ih,
      sum_Icc_succ_top (by omega : 1 ≤ N + 1)]
    have h := moebiusHarmonicTail_step N
    push_cast
    linear_combination -h

/-- Any power bound `|moebiusHarmonicTail n| ≤ K n^{-η}` with `η ∈ (0, 1)` transfers directly to
`|∑_{1 ≤ n ≤ N} μ(n)| ≤ K' N^{1 - η}`, including the supercritical regime `η ∈ (1/2, 1)`. -/
theorem abs_sum_moebiusReal_le_of_moebiusHarmonicTail {η K : ℝ}
    (hη0 : 0 < η) (hη1 : η < 1) (hK : 0 ≤ K)
    (hR : ∀ n : ℕ, 1 ≤ n → |moebiusHarmonicTail n| ≤ K * (n : ℝ) ^ (-η))
    {N : ℕ} (hN : 1 ≤ N) :
    |∑ n ∈ Icc 1 N, moebiusReal n| ≤
      (2 * K + K * (1 / (1 - η) + 1)) * (N : ℝ) ^ (1 - η) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hpow1 : 1 ≤ (N : ℝ) ^ (1 - η) := Real.one_le_rpow hN1 (by linarith)
  have hbdry : |-((N : ℝ) + 1) * moebiusHarmonicTail N| ≤ 2 * K * (N : ℝ) ^ (1 - η) := by
    rw [neg_mul, abs_neg, abs_mul, abs_of_pos (by positivity)]
    calc ((N : ℝ) + 1) * |moebiusHarmonicTail N|
        ≤ (2 * (N : ℝ)) * (K * (N : ℝ) ^ (-η)) :=
          mul_le_mul (by linarith) (hR N hN) (abs_nonneg _) (by positivity)
      _ = 2 * K * ((N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (-η)) := by rw [Real.rpow_one]; ring
      _ = 2 * K * (N : ℝ) ^ (1 - η) := by
          rw [← Real.rpow_add hN0, show (1 : ℝ) + -η = 1 - η by ring]
  have hsum : |∑ n ∈ Icc 1 N, moebiusHarmonicTail n| ≤
      K * (1 / (1 - η) + 1) * (N : ℝ) ^ (1 - η) := by
    calc |∑ n ∈ Icc 1 N, moebiusHarmonicTail n|
        ≤ ∑ n ∈ Icc 1 N, |moebiusHarmonicTail n| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Icc 1 N, K * (n : ℝ) ^ (-η) :=
          sum_le_sum fun n hn => hR n (mem_Icc.mp hn).1
      _ = K * ∑ n ∈ Icc 1 N, (n : ℝ) ^ (-η) := by rw [mul_sum]
      _ ≤ K * ((N : ℝ) ^ (1 - η) / (1 - η) + 1) :=
          mul_le_mul_of_nonneg_left (RHTower.Sieve.sum_rpow_neg_subcritical_le hη0 hη1 N) hK
      _ ≤ K * ((N : ℝ) ^ (1 - η) / (1 - η) + (N : ℝ) ^ (1 - η)) :=
          mul_le_mul_of_nonneg_left (add_le_add le_rfl hpow1) hK
      _ = K * (1 / (1 - η) + 1) * (N : ℝ) ^ (1 - η) := by ring
  rw [sum_moebiusReal_eq_moebiusHarmonicTail_abel]
  calc |-((N : ℝ) + 1) * moebiusHarmonicTail N + ∑ n ∈ Icc 1 N, moebiusHarmonicTail n|
      ≤ |-((N : ℝ) + 1) * moebiusHarmonicTail N| + |∑ n ∈ Icc 1 N, moebiusHarmonicTail n| :=
        abs_add_le _ _
    _ ≤ 2 * K * (N : ℝ) ^ (1 - η) + K * (1 / (1 - η) + 1) * (N : ℝ) ^ (1 - η) :=
        add_le_add hbdry hsum
    _ = (2 * K + K * (1 / (1 - η) + 1)) * (N : ℝ) ^ (1 - η) := by ring

/-- Dyadic telescoping from the single multiplier `a = 2, b = 0`: any bound
`|escapedPairing N 2 0| ≤ C N^{-η}` (`η > 0`) implies `|moebiusHarmonicTail n| ≤ (C/(2^η - 1)) n^{-η}`
for every `n ≥ 1`. -/
theorem abs_moebiusHarmonicTail_le_of_dyadic_escapedPairing {η C : ℝ}
    (hη : 0 < η) (hC : 0 ≤ C)
    (hdyad : ∀ N : ℕ, 1 ≤ N →
      |escapedPairing N 2 0 (moebiusSource N) (flatSource N)| ≤
        C * (N : ℝ) ^ (-η))
    {n : ℕ} (hn : 1 ≤ n) :
    |moebiusHarmonicTail n| ≤ (C / ((2 : ℝ) ^ η - 1)) * (n : ℝ) ^ (-η) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h2pow_gt : (1 : ℝ) < (2 : ℝ) ^ η := Real.one_lt_rpow (by norm_num) hη
  have hden_pos : 0 < (2 : ℝ) ^ η - 1 := sub_pos.mpr h2pow_gt
  set q : ℝ := (2 : ℝ) ^ (-η)
  have hq0 : 0 ≤ q := Real.rpow_nonneg (by norm_num) _
  have hq1 : q < 1 := by
    have hq_eq : q = ((2 : ℝ) ^ η)⁻¹ := Real.rpow_neg (by norm_num) η
    rw [hq_eq]
    exact inv_lt_one_of_one_lt₀ h2pow_gt
  have hstep : ∀ m : ℕ, 1 ≤ m →
      |moebiusHarmonicTail m - moebiusHarmonicTail (2 * m)| ≤
        C * (2 : ℝ) ^ (-η) * (m : ℝ) ^ (-η) := by
    intro m hm
    have hesc := hdyad (2 * m) (by omega)
    rw [escapedPairing_moebiusSource] at hesc
    simp only [Nat.sub_zero, PNat.val_ofNat] at hesc
    have hdiv : 2 * m / 2 = m := Nat.mul_div_right m (by norm_num)
    rw [hdiv, sum_Ioc_moebius_div m (2 * m) (by omega)] at hesc
    have htail : moebiusHarmonicTail m - moebiusHarmonicTail (2 * m) =
        ∑ k ∈ range (2 * m + 1), (μ k : ℝ) / k - ∑ k ∈ range (m + 1), (μ k : ℝ) / k := by
      simp [moebiusHarmonicTail]
      ring
    rw [htail]
    refine hesc.trans ?_
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    rw [Nat.cast_mul, Nat.cast_ofNat, Real.mul_rpow (by norm_num) hm0]
    exact le_of_eq (by ring)
  have htele : ∀ K : ℕ,
      |moebiusHarmonicTail n - moebiusHarmonicTail (2 ^ K * n)| ≤
        (C / ((2 : ℝ) ^ η - 1)) * (n : ℝ) ^ (-η) := by
    intro K
    have htel_eq : moebiusHarmonicTail n - moebiusHarmonicTail (2 ^ K * n) =
        ∑ k ∈ range K, (moebiusHarmonicTail (2 ^ k * n) -
          moebiusHarmonicTail (2 ^ (k + 1) * n)) := by
      induction K with
      | zero => simp
      | succ K ih =>
        rw [Finset.sum_range_succ, ← ih]
        ring
    rw [htel_eq]
    calc |∑ k ∈ range K, (moebiusHarmonicTail (2 ^ k * n) -
            moebiusHarmonicTail (2 ^ (k + 1) * n))|
        ≤ ∑ k ∈ range K, |moebiusHarmonicTail (2 ^ k * n) -
            moebiusHarmonicTail (2 ^ (k + 1) * n)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ range K, C * q * (n : ℝ) ^ (-η) * q ^ k := by
          refine sum_le_sum fun k _ => ?_
          have hmk : 1 ≤ 2 ^ k * n := Nat.mul_pos (pow_pos (by norm_num) k) hn
          have h2k : 2 ^ (k + 1) * n = 2 * (2 ^ k * n) := by ring
          rw [h2k]
          refine (hstep (2 ^ k * n) hmk).trans ?_
          have hpow_cast : ((2 ^ k * n : ℕ) : ℝ) ^ (-η) = q ^ k * (n : ℝ) ^ (-η) := by
            rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
              Real.mul_rpow (by positivity) hn0.le,
              ← Real.rpow_natCast 2 k, ← Real.rpow_mul (by norm_num),
              mul_comm (k : ℝ) (-η), Real.rpow_mul (by norm_num), Real.rpow_natCast]
          rw [hpow_cast]
          exact le_of_eq (by ring)
      _ = C * q * (n : ℝ) ^ (-η) * ∑ k ∈ range K, q ^ k := by rw [← mul_sum]
      _ ≤ C * q * (n : ℝ) ^ (-η) * ((1 - q)⁻¹) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have hgeom : ∑ k ∈ range K, q ^ k = (1 - q ^ K) * (1 - q)⁻¹ := by
            rw [geom_sum_eq hq1.ne]
            have hne1 : q - 1 ≠ 0 := sub_ne_zero.mpr hq1.ne
            have hne2 : 1 - q ≠ 0 := sub_ne_zero.mpr hq1.ne'
            field_simp
            ring
          rw [hgeom]
          have hsub_le : 1 - q ^ K ≤ 1 := sub_le_self 1 (pow_nonneg hq0 K)
          have hinv_pos : 0 ≤ (1 - q)⁻¹ := inv_nonneg.mpr (sub_nonneg.mpr hq1.le)
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hsub_le hinv_pos
      _ = (C / ((2 : ℝ) ^ η - 1)) * (n : ℝ) ^ (-η) := by
          have hq_id : q * (1 - q)⁻¹ = 1 / ((2 : ℝ) ^ η - 1) := by
            have h2pos : 0 < (2 : ℝ) ^ η := Real.rpow_pos_of_pos (by norm_num) η
            have hq_inv : q = ((2 : ℝ) ^ η)⁻¹ := Real.rpow_neg (by norm_num) η
            rw [hq_inv]
            field_simp [h2pos.ne', hden_pos.ne']
          calc C * q * (n : ℝ) ^ (-η) * (1 - q)⁻¹
              = C * (q * (1 - q)⁻¹) * (n : ℝ) ^ (-η) := by ring
            _ = C * (1 / ((2 : ℝ) ^ η - 1)) * (n : ℝ) ^ (-η) := by rw [hq_id]
            _ = (C / ((2 : ℝ) ^ η - 1)) * (n : ℝ) ^ (-η) := by ring
  have hmono : StrictMono (fun K : ℕ => 2 ^ K * n) := by
    intro a b hab
    exact Nat.mul_lt_mul_of_pos_right (Nat.pow_lt_pow_right (by norm_num) hab) hn
  have htend_tail : Tendsto (fun K : ℕ => moebiusHarmonicTail (2 ^ K * n)) atTop (𝓝 0) := by
    have h0 : Tendsto moebiusHarmonicTail atTop (𝓝 0) := by
      unfold moebiusHarmonicTail
      simpa using RHTower.tendsto_sum_range_succ_moebius_div.neg
    exact h0.comp hmono.tendsto_atTop
  have htend_abs : Tendsto
      (fun K : ℕ => |moebiusHarmonicTail n - moebiusHarmonicTail (2 ^ K * n)|)
      atTop (𝓝 |moebiusHarmonicTail n|) := by
    simpa [sub_zero] using ((tendsto_const_nhds.sub htend_tail).abs)
  exact le_of_tendsto htend_abs (Eventually.of_forall htele)

/-! ### 3. Reverse Transfer: Mertens Power Bounds Control All Growing-Endpoint Escaped Pairings -/

/-- Concavity telescoping step: for `δ ∈ (0, 1)` and `j ≥ 1`,
`j^{-δ} / (j + 1) ≤ (1 / δ) * (j^{-δ} - (j + 1)^{-δ})`. -/
theorem rpow_neg_div_succ_le_telescope {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {j : ℕ} (hj : 1 ≤ j) :
    (j : ℝ) ^ (-δ) / ((j : ℝ) + 1) ≤
      (1 / δ) * ((j : ℝ) ^ (-δ) - ((j : ℝ) + 1) ^ (-δ)) := by
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hjp : 0 < (j : ℝ) + 1 := by positivity
  have hx : -(1 : ℝ) ≤ -1 / ((j : ℝ) + 1) := by
    rw [neg_div, neg_le_neg_iff]
    exact div_le_one_of_le₀ (by linarith) hjp.le
  have hconc := rpow_one_add_le_one_add_mul_self hx hδ0.le hδ1
  have hbase : 1 + (-1 / ((j : ℝ) + 1)) = (j : ℝ) / ((j : ℝ) + 1) := by
    field_simp
    ring
  rw [hbase] at hconc
  have hprod : ((j : ℝ) + 1) ^ (-δ) =
      (j : ℝ) ^ (-δ) * ((j : ℝ) / ((j : ℝ) + 1)) ^ δ := by
    rw [div_eq_mul_inv, Real.mul_rpow hj0.le (inv_nonneg.mpr hjp.le), ← mul_assoc,
      ← Real.rpow_add hj0, neg_add_cancel, Real.rpow_zero, one_mul,
      Real.inv_rpow hjp.le, ← Real.rpow_neg hjp.le]
  have hstep : ((j : ℝ) + 1) ^ (-δ) ≤
      (j : ℝ) ^ (-δ) * (1 + δ * (-1 / ((j : ℝ) + 1))) := by
    rw [hprod]
    exact mul_le_mul_of_nonneg_left hconc (Real.rpow_nonneg hj0.le _)
  have hsub : δ * ((j : ℝ) ^ (-δ) / ((j : ℝ) + 1)) ≤
      (j : ℝ) ^ (-δ) - ((j : ℝ) + 1) ^ (-δ) := by
    have hrew : (j : ℝ) ^ (-δ) * (1 + δ * (-1 / ((j : ℝ) + 1))) =
        (j : ℝ) ^ (-δ) - δ * ((j : ℝ) ^ (-δ) / ((j : ℝ) + 1)) := by ring
    linarith
  calc (j : ℝ) ^ (-δ) / ((j : ℝ) + 1)
      = (1 / δ) * (δ * ((j : ℝ) ^ (-δ) / ((j : ℝ) + 1))) := by
        field_simp [hδ0.ne']
    _ ≤ (1 / δ) * ((j : ℝ) ^ (-δ) - ((j : ℝ) + 1) ^ (-δ)) :=
        mul_le_mul_of_nonneg_left hsub (by positivity)

/-- Finite summation by parts on `(M, N]` expressing `∑_{M < j ≤ N} μ(j) / j` in terms of the
Mertens partial sums `M_sum(n) = ∑_{1 ≤ k ≤ n} μ(k)`. -/
theorem sum_Ioc_moebius_div_eq_mertens_abel {M N : ℕ} (hMN : M ≤ N) :
    ∑ j ∈ Ioc M N, (μ j : ℝ) / j =
      (if M = N then 0 else
        (∑ k ∈ Icc 1 N, moebiusReal k) / (N : ℝ) -
          (∑ k ∈ Icc 1 M, moebiusReal k) / ((M : ℝ) + 1) +
          ∑ j ∈ Ico (M + 1) N,
            (∑ k ∈ Icc 1 j, moebiusReal k) * (1 / (j : ℝ) - 1 / ((j : ℝ) + 1))) := by
  induction N, hMN using Nat.le_induction with
  | base => simp
  | succ n hMn ih =>
    have hne : M ≠ n + 1 := by omega
    rw [if_neg hne, sum_Ioc_succ_top hMn, ih]
    have hmu : (μ (n + 1) : ℝ) =
        (∑ k ∈ Icc 1 (n + 1), moebiusReal k) - ∑ k ∈ Icc 1 n, moebiusReal k := by
      rw [sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
      unfold moebiusReal
      ring
    rcases eq_or_lt_of_le hMn with rfl | hlt
    · simp only [ ↓reduceIte, zero_add, Ico_self, sum_empty, add_zero]
      rw [hmu]
      push_cast
      ring
    · rw [if_neg (by omega : M ≠ n), sum_Ico_succ_top (by omega : M + 1 ≤ n)]
      rw [hmu]
      push_cast
      ring

/-- Any Mertens power bound `|M(n)| ≤ C n^{1 - δ}` (`δ ∈ (0, 1)`) controls `∑_{M < j ≤ N} μ(j)/j`
uniformly across all `1 ≤ M ≤ N` by `(2 + 1/δ) C M^{-δ}`. -/
theorem abs_sum_Ioc_moebius_div_le_of_mertens_bound {δ C : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hC : 0 ≤ C)
    (hM : ∀ n : ℕ, 1 ≤ n → |∑ k ∈ Icc 1 n, moebiusReal k| ≤ C * (n : ℝ) ^ (1 - δ))
    {M N : ℕ} (hM1 : 1 ≤ M) (hMN : M ≤ N) :
    |∑ j ∈ Ioc M N, (μ j : ℝ) / j| ≤ (2 + 1 / δ) * C * (M : ℝ) ^ (-δ) := by
  rw [sum_Ioc_moebius_div_eq_mertens_abel hMN]
  split_ifs with heq
  · rw [abs_zero]
    positivity
  · have hlt : M < N := lt_of_le_of_ne hMN heq
    have hN1 : 1 ≤ N := by omega
    have hM0 : (0 : ℝ) < M := by exact_mod_cast hM1
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
    have hbN : |(∑ k ∈ Icc 1 N, moebiusReal k) / (N : ℝ)| ≤ C * (M : ℝ) ^ (-δ) := by
      rw [abs_div, abs_of_pos hN0]
      calc |∑ k ∈ Icc 1 N, moebiusReal k| / (N : ℝ)
          ≤ (C * (N : ℝ) ^ (1 - δ)) / (N : ℝ) :=
            div_le_div_of_nonneg_right (hM N hN1) hN0.le
        _ = C * (N : ℝ) ^ (-δ) := by
            rw [mul_div_assoc, ← Real.rpow_sub_one hN0.ne', show 1 - δ - 1 = -δ by ring]
        _ ≤ C * (M : ℝ) ^ (-δ) :=
            mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_nonpos hM0 (by exact_mod_cast hMN) (by linarith)) hC
    have hbM : |(∑ k ∈ Icc 1 M, moebiusReal k) / ((M : ℝ) + 1)| ≤ C * (M : ℝ) ^ (-δ) := by
      have hMp : 0 < (M : ℝ) + 1 := by positivity
      rw [abs_div, abs_of_pos hMp]
      calc |∑ k ∈ Icc 1 M, moebiusReal k| / ((M : ℝ) + 1)
          ≤ |∑ k ∈ Icc 1 M, moebiusReal k| / (M : ℝ) :=
            div_le_div_of_nonneg_left (abs_nonneg _) hM0 (by linarith)
        _ ≤ (C * (M : ℝ) ^ (1 - δ)) / (M : ℝ) :=
            div_le_div_of_nonneg_right (hM M hM1) hM0.le
        _ = C * (M : ℝ) ^ (-δ) := by
            rw [mul_div_assoc, ← Real.rpow_sub_one hM0.ne', show 1 - δ - 1 = -δ by ring]
    have hsum : |∑ j ∈ Ico (M + 1) N,
        (∑ k ∈ Icc 1 j, moebiusReal k) * (1 / (j : ℝ) - 1 / ((j : ℝ) + 1))| ≤
          (1 / δ) * C * (M : ℝ) ^ (-δ) := by
      have htele_sum : ∑ j ∈ Ico (M + 1) N, ((j : ℝ) ^ (-δ) - ((j : ℝ) + 1) ^ (-δ)) =
          ((M + 1 : ℕ) : ℝ) ^ (-δ) - (N : ℝ) ^ (-δ) := by
        have h := sum_Ico_sub (fun j : ℕ => (j : ℝ) ^ (-δ)) (by omega : M + 1 ≤ N)
        have hneg : -(∑ j ∈ Ico (M + 1) N, (((j + 1 : ℕ) : ℝ) ^ (-δ) - (j : ℝ) ^ (-δ))) =
            ∑ j ∈ Ico (M + 1) N, ((j : ℝ) ^ (-δ) - ((j : ℝ) + 1) ^ (-δ)) := by
          rw [← sum_neg_distrib]
          refine sum_congr rfl fun j _ => ?_
          push_cast
          ring
        linarith
      calc |∑ j ∈ Ico (M + 1) N,
            (∑ k ∈ Icc 1 j, moebiusReal k) * (1 / (j : ℝ) - 1 / ((j : ℝ) + 1))|
          ≤ ∑ j ∈ Ico (M + 1) N,
              |(∑ k ∈ Icc 1 j, moebiusReal k) * (1 / (j : ℝ) - 1 / ((j : ℝ) + 1))| :=
            abs_sum_le_sum_abs _ _
        _ ≤ ∑ j ∈ Ico (M + 1) N,
              C * ((1 / δ) * ((j : ℝ) ^ (-δ) - ((j : ℝ) + 1) ^ (-δ))) := by
            refine sum_le_sum fun j hj => ?_
            have hj1 : 1 ≤ j := by have := (mem_Ico.mp hj).1; omega
            have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
            have hjp : 0 < (j : ℝ) + 1 := by positivity
            have hdiff_pos : 0 ≤ 1 / (j : ℝ) - 1 / ((j : ℝ) + 1) :=
              sub_nonneg.mpr (one_div_le_one_div_of_le hj0 (by linarith))
            rw [abs_mul, abs_of_nonneg hdiff_pos]
            have hfrac : 1 / (j : ℝ) - 1 / ((j : ℝ) + 1) = 1 / ((j : ℝ) * ((j : ℝ) + 1)) := by
              field_simp
              ring
            have h1 : |∑ k ∈ Icc 1 j, moebiusReal k| * (1 / (j : ℝ) - 1 / ((j : ℝ) + 1)) ≤
                C * ((j : ℝ) ^ (-δ) / ((j : ℝ) + 1)) := by
              calc |∑ k ∈ Icc 1 j, moebiusReal k| * (1 / (j : ℝ) - 1 / ((j : ℝ) + 1))
                  ≤ (C * (j : ℝ) ^ (1 - δ)) * (1 / ((j : ℝ) * ((j : ℝ) + 1))) := by
                    rw [← hfrac]
                    exact mul_le_mul_of_nonneg_right (hM j hj1) hdiff_pos
                _ = C * (((j : ℝ) ^ (1 - δ) / (j : ℝ)) / ((j : ℝ) + 1)) := by
                    field_simp [hj0.ne', hjp.ne']
                _ = C * ((j : ℝ) ^ (-δ) / ((j : ℝ) + 1)) := by
                    rw [← Real.rpow_sub_one hj0.ne', show 1 - δ - 1 = -δ by ring]
            exact h1.trans (mul_le_mul_of_nonneg_left
              (rpow_neg_div_succ_le_telescope hδ0 hδ1.le hj1) hC)
        _ = C * (1 / δ) * ∑ j ∈ Ico (M + 1) N, ((j : ℝ) ^ (-δ) - ((j : ℝ) + 1) ^ (-δ)) := by
            rw [← mul_sum, ← mul_sum, mul_assoc]
        _ = C * (1 / δ) * (((M + 1 : ℕ) : ℝ) ^ (-δ) - (N : ℝ) ^ (-δ)) := by rw [htele_sum]
        _ ≤ C * (1 / δ) * (M : ℝ) ^ (-δ) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            have hNnonneg : 0 ≤ (N : ℝ) ^ (-δ) := Real.rpow_nonneg hN0.le _
            have hMstep : ((M + 1 : ℕ) : ℝ) ^ (-δ) ≤ (M : ℝ) ^ (-δ) :=
              Real.rpow_le_rpow_of_nonpos hM0 (by exact_mod_cast Nat.le_succ M) (by linarith)
            linarith
        _ = (1 / δ) * C * (M : ℝ) ^ (-δ) := by ring
    calc |(∑ k ∈ Icc 1 N, moebiusReal k) / (N : ℝ) -
            (∑ k ∈ Icc 1 M, moebiusReal k) / ((M : ℝ) + 1) +
            ∑ j ∈ Ico (M + 1) N,
              (∑ k ∈ Icc 1 j, moebiusReal k) * (1 / (j : ℝ) - 1 / ((j : ℝ) + 1))|
        ≤ |(∑ k ∈ Icc 1 N, moebiusReal k) / (N : ℝ)| +
            |(∑ k ∈ Icc 1 M, moebiusReal k) / ((M : ℝ) + 1)| +
            |∑ j ∈ Ico (M + 1) N,
              (∑ k ∈ Icc 1 j, moebiusReal k) * (1 / (j : ℝ) - 1 / ((j : ℝ) + 1))| :=
          (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
      _ ≤ C * (M : ℝ) ^ (-δ) + C * (M : ℝ) ^ (-δ) + (1 / δ) * C * (M : ℝ) ^ (-δ) :=
          add_le_add (add_le_add hbN hbM) hsum
      _ = (2 + 1 / δ) * C * (M : ℝ) ^ (-δ) := by ring

/-! ### 4. Complete Classification of the Square-Root Boundary Law -/

/-- Uniform growing-endpoint power saving at exponent `θ` for the escaped Möbius pairing:
for every `ε > 0`, `|escapedPairing N a b (moebiusSource N) (flatSource N)| = O_ε(((N - b)/a)^{-θ+ε})`
uniformly over all `N : ℕ`, `a : ℕ+`, `b : ℕ` with `1 ≤ (N - b) / a` and `b ≤ N`. -/
def GrowingEndpointEscapedMoebiusLaw (θ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (a : ℕ+) (b : ℕ),
    b ≤ N → 1 ≤ (N - b) / a →
      |escapedPairing N a b (moebiusSource N) (flatSource N)| ≤
        C * (((N - b) / a : ℕ) : ℝ) ^ (-θ + ε)

/-- Single-multiplier dyadic escaped Möbius power saving at `a = 2, b = 0`:
for every `ε > 0`, `|escapedPairing N 2 0 (moebiusSource N) (flatSource N)| = O_ε(N^{-θ+ε})`. -/
def DyadicEscapedMoebiusLaw (θ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
    |escapedPairing N 2 0 (moebiusSource N) (flatSource N)| ≤
      C * (N : ℝ) ^ (-θ + ε)

/-- **Exact Quasi-Riemann Equivalence for the Escaped Möbius Boundary (`0 < θ ≤ 1 / 2`):**
For every `θ ∈ (0, 1 / 2]`, the following are unconditionally equivalent:
1. `GrowingEndpointEscapedMoebiusLaw θ` (uniform `O_ε(((N - b)/a)^{-θ+ε})` across all `a, b` with
   `1 ≤ (N - b)/a`);
2. `DyadicEscapedMoebiusLaw θ` (the single multiplier `a = 2, b = 0`);
3. `zetaZeroAbscissa ≤ 1 - θ`. -/
theorem growingEndpointEscapedMoebiusLaw_tfae {θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ ≤ 1 / 2) :
    List.TFAE [GrowingEndpointEscapedMoebiusLaw θ,
      DyadicEscapedMoebiusLaw θ,
      zetaZeroAbscissa ≤ 1 - θ] := by
  tfae_have 1 → 2 := by
    intro hgrow ε hε
    by_cases hεθ : θ ≤ ε
    · refine ⟨2, by norm_num, fun N hN => ?_⟩
      rw [escapedPairing_moebiusSource]
      simp only [Nat.sub_zero, PNat.val_ofNat]
      have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
      have hpow : 1 ≤ (N : ℝ) ^ (-θ + ε) := Real.one_le_rpow hN1 (by linarith)
      have htriv : |∑ j ∈ Ioc (N / 2) N, (μ j : ℝ) / j| ≤ 2 := by
        calc |∑ j ∈ Ioc (N / 2) N, (μ j : ℝ) / j|
            ≤ ∑ j ∈ Ioc (N / 2) N, |(μ j : ℝ) / j| := abs_sum_le_sum_abs _ _
          _ ≤ ∑ _j ∈ Ioc (N / 2) N, (1 / ((N / 2 + 1 : ℕ) : ℝ)) := by
              refine sum_le_sum fun j hj => ?_
              have hj_lo : N / 2 + 1 ≤ j := (mem_Ioc.mp hj).1
              have hj_pos : (0 : ℝ) < j := by exact_mod_cast (by omega : 0 < j)
              rw [abs_div, abs_of_pos hj_pos]
              have hmu : |(μ j : ℝ)| ≤ 1 := by
                exact_mod_cast ArithmeticFunction.abs_moebius_le_one
              calc |(μ j : ℝ)| / (j : ℝ) ≤ 1 / (j : ℝ) :=
                    div_le_div_of_nonneg_right hmu hj_pos.le
                _ ≤ 1 / ((N / 2 + 1 : ℕ) : ℝ) :=
                    one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hj_lo)
          _ = ((N - N / 2 : ℕ) : ℝ) / ((N / 2 + 1 : ℕ) : ℝ) := by
              rw [sum_const, Nat.card_Ioc, nsmul_eq_mul, mul_one_div]
          _ ≤ 2 := by
              rw [div_le_iff₀ (by positivity)]
              have hle : N - N / 2 ≤ 2 * (N / 2 + 1) := by omega
              exact_mod_cast hle
      nlinarith
    · push Not at hεθ
      obtain ⟨C, hC, hbd⟩ := hgrow ε hε
      refine ⟨max 1 (C * (3 : ℝ) ^ (θ - ε)), by positivity, fun N hN => ?_⟩
      rcases eq_or_lt_of_le hN with rfl | hN2
      · rw [escapedPairing_moebiusSource]
        simp only [Nat.sub_zero, PNat.val_ofNat]
        have hIoc : Ioc (1 / 2) 1 = {1} := by
          ext j; simp only [mem_Ioc, mem_singleton]; omega
        rw [hIoc, sum_singleton, Nat.cast_one, Real.one_rpow, mul_one]
        simp only [ArithmeticFunction.moebius_apply_one, Int.cast_one, div_one, abs_one]
        exact le_max_left _ _
      · have hdiv1 : 1 ≤ (N - 0) / (2 : ℕ+) := by
          simp only [Nat.sub_zero, PNat.val_ofNat]
          omega
        have h := hbd N 2 0 (Nat.zero_le N) hdiv1
        have hN3 : (N : ℝ) ≤ 3 * (((N - 0) / (2 : ℕ+) : ℕ) : ℝ) := by
          simp only [Nat.sub_zero, PNat.val_ofNat]
          exact_mod_cast (show N ≤ 3 * (N / 2) by omega)
        have hm0 : 0 < (((N - 0) / (2 : ℕ+) : ℕ) : ℝ) := by exact_mod_cast hdiv1
        have hrpow : (((N - 0) / (2 : ℕ+) : ℕ) : ℝ) ^ (-θ + ε) ≤
            (3 : ℝ) ^ (θ - ε) * (N : ℝ) ^ (-θ + ε) := by
          have hdiv_ge : (N : ℝ) / 3 ≤ (((N - 0) / (2 : ℕ+) : ℕ) : ℝ) := by linarith
          calc (((N - 0) / (2 : ℕ+) : ℕ) : ℝ) ^ (-θ + ε)
              ≤ ((N : ℝ) / 3) ^ (-θ + ε) :=
                Real.rpow_le_rpow_of_nonpos (by positivity) hdiv_ge (by linarith)
            _ = (N : ℝ) ^ (-θ + ε) * ((3 : ℝ)⁻¹) ^ (-θ + ε) := by
                rw [div_eq_mul_inv, Real.mul_rpow (by positivity) (by positivity)]
            _ = (3 : ℝ) ^ (θ - ε) * (N : ℝ) ^ (-θ + ε) := by
                rw [Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num),
                  show -(-θ + ε) = θ - ε by ring, mul_comm]
        calc |escapedPairing N 2 0 (moebiusSource N) (flatSource N)|
            ≤ C * (((N - 0) / (2 : ℕ+) : ℕ) : ℝ) ^ (-θ + ε) := h
          _ ≤ C * ((3 : ℝ) ^ (θ - ε) * (N : ℝ) ^ (-θ + ε)) :=
              mul_le_mul_of_nonneg_left hrpow hC
          _ = (C * (3 : ℝ) ^ (θ - ε)) * (N : ℝ) ^ (-θ + ε) := by ring
          _ ≤ max 1 (C * (3 : ℝ) ^ (θ - ε)) * (N : ℝ) ^ (-θ + ε) :=
              mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (by positivity) _)
  tfae_have 2 → 3 := by
    intro hdyad
    by_contra hnot
    push Not at hnot
    set ε : ℝ := min (θ / 2) ((zetaZeroAbscissa - (1 - θ)) / 2)
    have hε0 : 0 < ε := lt_min (half_pos hθ0) (by linarith)
    set η : ℝ := θ - ε
    have hη0 : 0 < η := by
      have : ε ≤ θ / 2 := min_le_left _ _
      linarith
    have hη1 : η < 1 := by linarith
    obtain ⟨C, hC, hbd⟩ := hdyad ε hε0
    have htail : ∀ n : ℕ, 1 ≤ n →
        |moebiusHarmonicTail n| ≤ (C / ((2 : ℝ) ^ η - 1)) * (n : ℝ) ^ (-η) := by
      intro n hn
      refine abs_moebiusHarmonicTail_le_of_dyadic_escapedPairing hη0 hC (fun N hN => ?_) hn
      simpa [η, sub_eq_add_neg, add_comm] using hbd N hN
    have h2gt : (1 : ℝ) < (2 : ℝ) ^ η := Real.one_lt_rpow (by norm_num) hη0
    have hK0 : 0 ≤ C / ((2 : ℝ) ^ η - 1) := div_nonneg hC (sub_nonneg.mpr h2gt.le)
    have hM := fun N (hN : 1 ≤ N) =>
      abs_sum_moebiusReal_le_of_moebiusHarmonicTail hη0 hη1 hK0 htail hN
    have h1η : 0 < 1 - η := by linarith
    have hC_mert : 0 ≤ 2 * (C / ((2 : ℝ) ^ η - 1)) +
        C / ((2 : ℝ) ^ η - 1) * (1 / (1 - η) + 1) := by positivity
    have habs := zetaZeroAbscissa_le_of_moebius_power_bound hC_mert h1η.le hM
    have hε2 : ε ≤ (zetaZeroAbscissa - (1 - θ)) / 2 := min_le_right _ _
    linarith
  tfae_have 3 → 1 := by
    intro habs ε hε
    set δ : ℝ := θ - min (ε / 2) (θ / 2)
    have hδ0 : 0 < δ := by
      have : min (ε / 2) (θ / 2) ≤ θ / 2 := min_le_right _ _
      linarith
    have hδ1 : δ < 1 := by
      have : 0 < min (ε / 2) (θ / 2) := lt_min (half_pos hε) (half_pos hθ0)
      linarith
    have hlt_abs : zetaZeroAbscissa < 1 - δ := by
      have : 0 < min (ε / 2) (θ / 2) := lt_min (half_pos hε) (half_pos hθ0)
      linarith
    obtain ⟨C, hC, hM⟩ := exists_moebius_power_bound_of_abscissa_lt hlt_abs
    refine ⟨(2 + 1 / δ) * C, by positivity, fun N a b hbN hM1 => ?_⟩
    rw [escapedPairing_moebiusSource]
    have hMN : (N - b) / a ≤ N := (Nat.div_le_self _ _).trans (Nat.sub_le N b)
    have hbound := abs_sum_Ioc_moebius_div_le_of_mertens_bound hδ0 hδ1 hC hM hM1 hMN
    refine hbound.trans ?_
    have hexp : -δ ≤ -θ + ε := by
      have : min (ε / 2) (θ / 2) ≤ ε / 2 := min_le_left _ _
      linarith
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hM1) hexp) (by positivity)
  tfae_finish

/-- **Corollary (Riemann Hypothesis Equivalence Across the Square-Root Threshold):**
The growing-endpoint escaped Möbius boundary law holds across all `θ ∈ (0, 1 / 2)` (equivalently,
at `θ = 1 / 2`) if and only if `RiemannHypothesis` holds. -/
theorem riemannHypothesis_iff_growingEndpointEscapedMoebiusLaw_half :
    RiemannHypothesis ↔ GrowingEndpointEscapedMoebiusLaw (1 / 2) := by
  have htfae := growingEndpointEscapedMoebiusLaw_tfae (θ := 1 / 2) (by norm_num) le_rfl
  have heq : GrowingEndpointEscapedMoebiusLaw (1 / 2) ↔ zetaZeroAbscissa ≤ 1 - 1 / 2 :=
    htfae.out 0 2
  rw [heq, show (1 : ℝ) - 1 / 2 = 1 / 2 by ring,
    ← zetaZeroAbscissa_eq_half_iff_riemannHypothesis]
  constructor
  · intro h; exact h.le
  · intro h; exact le_antisymm h half_le_zetaZeroAbscissa

/-- **Corollary (All Sub-Half Exponents Equivalence):**
`RiemannHypothesis` holds if and only if `GrowingEndpointEscapedMoebiusLaw θ` holds for every
`θ ∈ (0, 1 / 2)`. -/
theorem riemannHypothesis_iff_forall_lt_half_growingEndpointEscapedMoebiusLaw :
    RiemannHypothesis ↔ ∀ θ : ℝ, 0 < θ → θ < 1 / 2 → GrowingEndpointEscapedMoebiusLaw θ := by
  constructor
  · intro hRH θ hθ0 hθ2
    have habs : zetaZeroAbscissa ≤ 1 - θ := by
      rw [zetaZeroAbscissa_eq_half_iff_riemannHypothesis.mpr hRH]
      linarith
    exact ((growingEndpointEscapedMoebiusLaw_tfae hθ0 hθ2.le).out 2 0).mp habs
  · intro hall
    apply zetaZeroAbscissa_eq_half_iff_riemannHypothesis.mp
    apply le_antisymm _ half_le_zetaZeroAbscissa
    by_contra hgt
    push Not at hgt
    let σ : ℝ := (1 / 2 + min zetaZeroAbscissa (3 / 4)) / 2
    have hσ_gt : 1 / 2 < σ := by
      have : 1 / 2 < min zetaZeroAbscissa (3 / 4) := lt_min hgt (by norm_num)
      dsimp [σ]; linarith
    have hσ_lt_abs : σ < zetaZeroAbscissa := by
      have : min zetaZeroAbscissa (3 / 4) ≤ zetaZeroAbscissa := min_le_left _ _
      dsimp [σ]; linarith
    have hσ_le : σ ≤ 5 / 8 := by
      have : min zetaZeroAbscissa (3 / 4) ≤ 3 / 4 := min_le_right _ _
      dsimp [σ]; linarith
    have hθ_pos : 0 < 1 - σ := by linarith
    have hθ_lt : 1 - σ < 1 / 2 := by linarith
    have hlaw := hall (1 - σ) hθ_pos hθ_lt
    have habs : zetaZeroAbscissa ≤ 1 - (1 - σ) :=
      ((growingEndpointEscapedMoebiusLaw_tfae hθ_pos hθ_lt.le).out 0 2).mp hlaw
    linarith

/-- **Unconditional No-Go Beyond the Square-Root Exponent (`θ > 1 / 2`):**
Even at the single fixed multiplier `a = 2, b = 0`, there is no constant `C` and exponent
`θ > 1 / 2` such that `|escapedPairing N 2 0 (moebiusSource N) (flatSource N)| ≤ C N^{-θ}` for all
`N ≥ 1`. -/
theorem not_dyadic_escapedPairing_rpow_of_half_lt {θ : ℝ} (hθ : 1 / 2 < θ) :
    ¬ ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
      |escapedPairing N 2 0 (moebiusSource N) (flatSource N)| ≤
        C * (N : ℝ) ^ (-θ) := by
  rintro ⟨C, hC, hbd⟩
  set η : ℝ := min θ (3 / 4)
  have hη_half : 1 / 2 < η := lt_min hθ (by norm_num)
  have hη0 : 0 < η := by linarith
  have hη1 : η < 1 := by
    have : η ≤ 3 / 4 := min_le_right _ _
    linarith
  have hbd_η : ∀ N : ℕ, 1 ≤ N →
      |escapedPairing N 2 0 (moebiusSource N) (flatSource N)| ≤
        C * (N : ℝ) ^ (-η) := by
    intro N hN
    refine (hbd N hN).trans (mul_le_mul_of_nonneg_left ?_ hC)
    have hle : η ≤ θ := min_le_left _ _
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by linarith)
  have htail := fun n (hn : 1 ≤ n) =>
    abs_moebiusHarmonicTail_le_of_dyadic_escapedPairing hη0 hC hbd_η hn
  have h2gt : (1 : ℝ) < (2 : ℝ) ^ η := Real.one_lt_rpow (by norm_num) hη0
  have hK0 : 0 ≤ C / ((2 : ℝ) ^ η - 1) := div_nonneg hC (sub_nonneg.mpr h2gt.le)
  have hM := fun N (hN : 1 ≤ N) =>
    abs_sum_moebiusReal_le_of_moebiusHarmonicTail hη0 hη1 hK0 htail hN
  have h1η : 0 < 1 - η := by linarith
  have hC_mert : 0 ≤ 2 * (C / ((2 : ℝ) ^ η - 1)) +
      C / ((2 : ℝ) ^ η - 1) * (1 / (1 - η) + 1) := by positivity
  have habs := zetaZeroAbscissa_le_of_moebius_power_bound hC_mert h1η.le hM
  have hhalf := half_le_zetaZeroAbscissa
  linarith

end GaloisForLFunctions.SelectivePositivityAndThresholdLaws
