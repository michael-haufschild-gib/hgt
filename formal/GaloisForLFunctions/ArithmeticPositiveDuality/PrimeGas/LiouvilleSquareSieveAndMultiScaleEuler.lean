import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.EulerAcceleratedSignedPartialSums
import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.SubSevenEighthsZeroFreeHalfPlane
import GaloisForLFunctions.RHTower.ZetaEulerRegionDiscSeamMargin
import GaloisForLFunctions.RHTower.LiouvilleSummatoryRH
import GaloisForLFunctions.RHTower.MobiusMertensAbscissaLittlewood
import GaloisForLFunctions.RHTower.AbelTailLSeries
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Prime-Gas Liouville Square Sieve, Multi-Scale Stride-Euler Operators, and All-Height Defect Laws

Additive Euler–Knopp acceleration (`eulerEtaPartialSum N M s`) collapses the archimedean remainder
of `(1 - 2^{1-s}) ζ(s)` from polynomial prefix scale `O(|Im s|^{1/Re s})` to linear prefix scale
`3 M` (`M = ⌈|Im s|⌉₊`) with `ζ`-free error `< 10^{-52}` above height `184`, yet by itself sees only
the additive sequence `n^{-s}` and cannot distinguish `ζ` from real quartet-symmetric Euler
deformations or non-multiplicative functional-equation countermodels.

Reflecting `s` (`0 < Re s < 1/2`) to `w = 1 - conj s` (`1/2 < Re w < 1`) places the doubled
parameter `2 w` (`Re(2 w) = 2 - 2 Re s > 1`) strictly inside the absolute-convergence Euler-product
half-plane of `ζ(2 w)`, coupling `eulerEtaPartialSum` to the completely multiplicative Prime-Gas
occupation parity `λ(n) = (-1)^{Ω(n)}` across **all** ordinates `Im s ∈ ℝ`:

1. **Pascal recurrence, cutoff antitonicity, all-order zero normal, and sub-Nyquist order-optimality
   (`eulerEtaPartialSum_succ_order`, `eulerEtaPartialSum_add_one_sub`,
   `eulerEtaPartialSum_succ_order_sub`, `norm_eulerEtaPartialSum_add_leading_le_of_zeta_eq_zero`,
   `eulerEtaTailBound_antitone_cutoff`, `norm_eulerEtaPartialSum_lt_tail_of_sub_nyquist`):**
   `eulerEtaPartialSum N (M + 1) s = (eulerEtaPartialSum N M s + eulerEtaPartialSum (N + 1) M s) / 2`,
   `eulerEtaPartialSum N (M + 1) s - eulerEtaPartialSum N M s = (-1)^N 2^{-(M+1)} (D^M(x^{-s}))(N+1)`,
   at any `ζ(s) = 0`, `(-1)^{N+1} 2^{-(M+1)} (D^M(x^{-s}))(N+1)` is the exact leading normal of
   `eulerEtaPartialSum N M s`, and on `0 ≤ Re s ≤ 1/2` with `4 (N + 1) ≤ |Im s|` **no** order `M ≥ 1`
   can ever beat `eulerEtaTailBound N M s` (proving `N ≳ |Im s|` is order-optimal across all heights).
2. **Exact 2-adic floor-parity rigidity and commuting multi-scale stride-Euler operators
   (`odd_div_sub_div_forall_iff`, `no_single_stride_flips_one_and_two`, `strideAvg_comm`,
   `iterate_strideAvg_altPartialSum_div_eq_eulerEtaPartialSum`,
   `norm_multiStrideEuler_lowDivisors_le_of_zeta_eq_zero`):**
   A single stride `k ≥ 1` flips `(-1)^{⌊X / d⌋}` uniformly in `X` iff `d ∣ k` and `Odd (k / d)`,
   so no single stride can simultaneously cancel `d = 1` and `d = 2`. Factoring instead into the
   commuting product `multiStrideEuler (List.range' 1 D) M` drives all first `D` Liouville divisor
   channels `1 ≤ d ≤ D` simultaneously below `3 / 2^{M / 2}` at any `ζ(w) = 0` (`X₀ ≥ 2 D M`,
   `M ≥ max 10 ⌈|Im w|⌉₊`), while stretching the cutoff horizon only quadratically by `M D(D+1)/2`.
3. **All-height Liouville–eta square sieve and height-independent double-energy floor
   (`sum_liouville_mul_dqptAltPartialSum_eq_squareEtaHead`, `norm_eta_two_mul_refl_ge`,
   `norm_squareEtaHead_refl_sub_le`, `norm_multiStrideEuler_squareEtaHead_refl_ge`):**
   For every `X : ℕ` and `w : ℂ`, `∑_{d=1}^X λ(d) d^{-w} S_{⌊X/d⌋}(w)` collapses identically to
   `squareEtaHead X w = ∑_{k² ≤ X} k^{-2w} - 2^{1-w} ∑_{2k² ≤ X} k^{-2w}`. For every `0 < Re s < 1/2`
   and **every** `Im s ∈ ℝ` (uniformly as `|Im s| → ∞`), `‖(1 - 2^{conj s}) ζ(2 - 2 conj s)‖` is
   bounded below by `(2^{Re s} - 1) (1 - 2 Re s) / (2 - 2 Re s) > 0`, with an explicit `Im s`-free
   tail bound `squareEtaTailBound X s.re`.
4. **Forced high-divisor concentration, 0–1 phase transition of `liouvilleEulerDefect`, and
   all-height `RiemannHypothesis` equivalence
   (`exists_euler_beats_tail_of_multiStride_highDivisors_lt`,
   `tendsto_liouvilleEulerDefect_zero_of_zeroFree`,
   `tendsto_liouvilleEulerDefect_of_zeta_eq_zero`,
   `eulerEtaPartialSum_beats_tail_of_liouvilleEulerDefect_lt`,
   `rh_iff_liouvilleEulerDefect_above_oneHundredEightyFour`):**
   Right of any zero-free abscissa `Θ ∈ [1/2, 1]` (unconditionally on `0 < Re s < 3001/24000`, and
   on all `0 < Re s < 1/2` under `RiemannHypothesis`), `liouvilleEulerDefect (2 M) M (1 - conj s) → 0`
   at every height, whereas at any `ζ(s) = 0` it converges to `-(1 - 2^{conj s}) ζ(2 - 2 conj s) ≠ 0`.
   Beating the height-uniform square-sieve floor at a single `M ≥ ⌈|Im s|⌉₊` forces
   `eulerEtaPartialSum (2 M) M (1 - conj s)` to strictly exceed `eulerEtaTailBound (2 M) M (1 - conj s)`.
5. **Planted quartet Euler-3 obstruction (`plantedQuartetEuler3_obstruction`):**
   Multiplying `(1 - 2^{1-s}) ζ(s)` by the real quartet-symmetric Euler-3 polynomial
   `(1 - 3^{s₀ - s})(1 - 3^{conj s₀ - s})(1 - 3^{1 - s₀ - s})(1 - 3^{1 - conj s₀ - s})` preserves
   real conjugate symmetry and `O_{s₀}(2^{-M/2})` Euler–Knopp tail decay, yet at all four quartet
   points `{s₀, conj s₀, 1 - s₀, 1 - conj s₀}` no order `(N, M)` (`M ≥ 1`) ever beats its error
   bound — while Liouville square-sieving immediately detects the planted prime-3 zero via vanishing
   of `Q_{s₀}(1 - conj s₀) (1 - 2^{conj s₀}) ζ(2 - 2 conj s₀)`.
-/

noncomputable section

open Complex Filter Topology Set
open scoped BigOperators ComplexConjugate

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas

open _root_.RHTower.DQPT

/-! ### 1. Pascal Recurrence, Cutoff Antitonicity, and All-Order Zero Normal -/

/-- Order `0` of `eulerEtaPartialSum` is the raw alternating Dirichlet partial sum. -/
theorem eulerEtaPartialSum_zero_order (N : ℕ) (s : ℂ) :
    eulerEtaPartialSum N 0 s = dqptAltPartialSum s N := by
  rw [eulerEtaPartialSum_eq_avg_dqptAltPartialSum, pow_zero, inv_one, one_mul,
    Finset.range_one, Finset.sum_singleton]
  simp

/-- **Pascal recurrence in Euler order:** increasing the order from `M` to `M + 1` averages adjacent
cutoffs `N` and `N + 1` at order `M`. -/
theorem eulerEtaPartialSum_succ_order (N M : ℕ) (s : ℂ) :
    eulerEtaPartialSum N (M + 1) s =
      (2 : ℂ)⁻¹ * (eulerEtaPartialSum N M s + eulerEtaPartialSum (N + 1) M s) := by
  rw [eulerEtaPartialSum_eq_avg_dqptAltPartialSum N (M + 1) s,
    eulerEtaPartialSum_eq_avg_dqptAltPartialSum N M s,
    eulerEtaPartialSum_eq_avg_dqptAltPartialSum (N + 1) M s]
  have hsum : (∑ r ∈ Finset.range (M + 2),
        (((M + 1).choose r : ℕ) : ℂ) * dqptAltPartialSum s (N + r)) =
      (∑ r ∈ Finset.range (M + 1), (M.choose r : ℂ) * dqptAltPartialSum s (N + r)) +
        ∑ r ∈ Finset.range (M + 1), (M.choose r : ℂ) * dqptAltPartialSum s (N + 1 + r) := by
    rw [Finset.sum_range_succ (fun r => (((M + 1).choose r : ℕ) : ℂ) * dqptAltPartialSum s (N + r)) (M + 1),
      Finset.sum_range_succ' (fun r => (((M + 1).choose r : ℕ) : ℂ) * dqptAltPartialSum s (N + r)) M,
      Finset.sum_range_succ' (fun r => (M.choose r : ℂ) * dqptAltPartialSum s (N + r)) M,
      Finset.sum_range_succ (fun r => (M.choose r : ℂ) * dqptAltPartialSum s (N + 1 + r)) M]
    have h0a : (((M + 1).choose 0 : ℕ) : ℂ) * dqptAltPartialSum s (N + 0) = dqptAltPartialSum s N := by
      simp
    have h0b : (M.choose 0 : ℂ) * dqptAltPartialSum s (N + 0) = dqptAltPartialSum s N := by
      simp
    have htop : (((M + 1).choose (M + 1) : ℕ) : ℂ) * dqptAltPartialSum s (N + (M + 1)) =
        (M.choose M : ℂ) * dqptAltPartialSum s (N + 1 + M) := by
      rw [Nat.choose_self, Nat.choose_self, Nat.cast_one, one_mul, one_mul,
        show N + (M + 1) = N + 1 + M by omega]
    have hmid : (∑ r ∈ Finset.range M,
          (((M + 1).choose (r + 1) : ℕ) : ℂ) * dqptAltPartialSum s (N + (r + 1))) =
        (∑ r ∈ Finset.range M, (M.choose (r + 1) : ℂ) * dqptAltPartialSum s (N + (r + 1))) +
          ∑ r ∈ Finset.range M, (M.choose r : ℂ) * dqptAltPartialSum s (N + 1 + r) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun r _ => ?_
      have hch : (((M + 1).choose (r + 1) : ℕ) : ℂ) =
          (M.choose r : ℂ) + (M.choose (r + 1) : ℂ) := by
        exact_mod_cast Nat.choose_succ_succ M r
      rw [hch, show N + 1 + r = N + (r + 1) by omega]
      ring
    rw [h0a, h0b, htop, hmid]
    ring
  rw [hsum, pow_succ, mul_inv]
  ring

/-- **Exact consecutive-cutoff increment:** shifting the cutoff `N ↦ N + 1` at Euler order `M` adds
`(-1)^N 2^{-M}` times the `M`-th unit falling difference of `x ↦ x^{-s}` at `N + 1`. -/
theorem eulerEtaPartialSum_add_one_sub (N M : ℕ) (s : ℂ) :
    eulerEtaPartialSum (N + 1) M s - eulerEtaPartialSum N M s =
      (-1 : ℂ) ^ N * ((2 : ℂ) ^ M)⁻¹ * (unitFallDiff^[M] (dqptRp s)) ((N : ℝ) + 1) := by
  rw [eulerEtaPartialSum_eq_avg_dqptAltPartialSum (N + 1) M s,
    eulerEtaPartialSum_eq_avg_dqptAltPartialSum N M s, ← mul_sub, ← Finset.sum_sub_distrib,
    iterate_unitFallDiff_eq_sum_choose M (dqptRp s) ((N : ℝ) + 1)]
  have hinner : (∑ r ∈ Finset.range (M + 1),
        ((M.choose r : ℂ) * dqptAltPartialSum s (N + 1 + r) -
          (M.choose r : ℂ) * dqptAltPartialSum s (N + r))) =
      (-1 : ℂ) ^ N * ∑ r ∈ Finset.range (M + 1),
        (-1 : ℂ) ^ r * (M.choose r : ℂ) * dqptRp s ((N : ℝ) + 1 + (r : ℝ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [show N + 1 + r = (N + r) + 1 by omega, dqptAltPartialSum_succ, pow_add]
    have harg : ((N + r : ℕ) : ℝ) + 1 = (N : ℝ) + 1 + (r : ℝ) := by push_cast; ring
    rw [harg]
    ring
  rw [hinner]
  ring

/-- **Exact consecutive-order increment:** increasing the Euler order `M ↦ M + 1` at fixed `N`
inserts `(-1)^N 2^{-(M+1)} (D^M(x^{-s}))(N+1)`. -/
theorem eulerEtaPartialSum_succ_order_sub (N M : ℕ) (s : ℂ) :
    eulerEtaPartialSum N (M + 1) s - eulerEtaPartialSum N M s =
      (-1 : ℂ) ^ N * ((2 : ℂ) ^ (M + 1))⁻¹ * (unitFallDiff^[M] (dqptRp s)) ((N : ℝ) + 1) := by
  have hrec := eulerEtaPartialSum_succ_order N M s
  have hstep := eulerEtaPartialSum_add_one_sub N M s
  have hhalf : eulerEtaPartialSum N (M + 1) s - eulerEtaPartialSum N M s =
      (2 : ℂ)⁻¹ * (eulerEtaPartialSum (N + 1) M s - eulerEtaPartialSum N M s) := by
    linear_combination hrec
  rw [hhalf, hstep, pow_succ, mul_inv]
  ring

/-- **All-order zero normal law (generalizing `DQPTReflectedSlope` to every `M ≥ 0`):** at any
hypothetical zero `ζ(s) = 0` (`0 < Re s`, `s ≠ 1`), `eulerEtaPartialSum N M s` equals
`-(-1)^N 2^{-(M+1)} (D^M(x^{-s}))(N+1)` up to `eulerEtaTailBound N (M + 1) s`. -/
theorem norm_eulerEtaPartialSum_add_leading_le_of_zeta_eq_zero
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s ≠ 1) (hz : riemannZeta s = 0) (N M : ℕ) :
    ‖eulerEtaPartialSum N M s +
        (-1 : ℂ) ^ N * ((2 : ℂ) ^ (M + 1))⁻¹ * (unitFallDiff^[M] (dqptRp s)) ((N : ℝ) + 1)‖ ≤
      eulerEtaTailBound N (M + 1) s := by
  have heq : eulerEtaPartialSum N M s +
      (-1 : ℂ) ^ N * ((2 : ℂ) ^ (M + 1))⁻¹ * (unitFallDiff^[M] (dqptRp s)) ((N : ℝ) + 1) =
        eulerEtaPartialSum N (M + 1) s := by
    linear_combination -(eulerEtaPartialSum_succ_order_sub N M s)
  rw [heq]
  exact (norm_eulerEtaPartialSum_le_tail_of_zeta_eq_zero hs0 hs1 hz).1 N (M + 1) (by omega)

/-- **Cutoff antitonicity of `eulerEtaTailBound`:** for `Re s > 0`, increasing `N` decreases the
explicit `ζ`-free remainder bound; hence every `N ≥ 2 M` inherits the `3 / 2^{M / 2}` bound. -/
theorem eulerEtaTailBound_antitone_cutoff {s : ℂ} (hs0 : 0 < s.re) (M : ℕ)
    {N₁ N₂ : ℕ} (hN : N₁ ≤ N₂) :
    eulerEtaTailBound N₂ M s ≤ eulerEtaTailBound N₁ M s := by
  unfold eulerEtaTailBound
  have hpos1 : (0 : ℝ) < (N₁ : ℝ) + 1 := by positivity
  have hle12 : (N₁ : ℝ) + 1 ≤ (N₂ : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hN 1
  have hrpow : ((N₂ : ℝ) + 1) ^ (-s.re - (M : ℝ)) ≤ ((N₁ : ℝ) + 1) ^ (-s.re - (M : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hpos1 hle12 (by linarith [Nat.cast_nonneg (α := ℝ) M])
  exact mul_le_mul_of_nonneg_left hrpow
    (mul_nonneg (by positivity) (Finset.prod_nonneg fun _ _ => norm_nonneg _))

theorem eulerEtaTailBound_le_three_div_two_pow_half_of_two_mul_le {s : ℂ} (hs0 : 0 < s.re)
    (hs1 : s.re ≤ 1) {M N : ℕ} (hM : 10 ≤ M) (him : |s.im| ≤ (M : ℝ)) (hN : 2 * M ≤ N) :
    eulerEtaTailBound N M s ≤ 3 / (2 : ℝ) ^ (M / 2) :=
  (eulerEtaTailBound_antitone_cutoff hs0 M hN).trans
    (eulerEtaTailBound_two_mul_le_three_div_two_pow_half hs0 hs1 hM him)

private lemma sum_Icc_rpow_neg_le_two_mul_rpow {σ : ℝ} (_hσ0 : 0 ≤ σ) (hσ_half : σ ≤ 1 / 2)
    {K : ℕ} (hK : 1 ≤ K) :
    (∑ n ∈ Finset.Icc 1 K, (n : ℝ) ^ (-σ)) ≤ 2 * (K : ℝ) ^ (1 - σ) := by
  have hterm : ∀ n ∈ Finset.Icc 1 K,
      (n : ℝ) ^ (-σ) ≤ 2 * (K : ℝ) ^ (1 / 2 - σ) * (Real.sqrt n - Real.sqrt ((n - 1 : ℕ) : ℝ)) := by
    intro n hn
    obtain ⟨hn1, hnK⟩ := Finset.mem_Icc.mp hn
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have hnR_le : (n : ℝ) ≤ (K : ℝ) := by exact_mod_cast hnK
    have hsplit_n : (n : ℝ) ^ (-σ) = (n : ℝ) ^ (1 / 2 - σ) * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_add hn_pos]; congr 1; ring
    have hmono : (n : ℝ) ^ (1 / 2 - σ) ≤ (K : ℝ) ^ (1 / 2 - σ) :=
      Real.rpow_le_rpow hn_pos.le hnR_le (by linarith)
    have hsqrt_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn_pos
    have hinv_sqrt : (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 2 * (Real.sqrt n - Real.sqrt ((n - 1 : ℕ) : ℝ)) := by
      rw [Real.rpow_neg hn_pos.le, ← Real.sqrt_eq_rpow]
      have hdiff_sq : (Real.sqrt n - Real.sqrt ((n - 1 : ℕ) : ℝ)) *
          (Real.sqrt n + Real.sqrt ((n - 1 : ℕ) : ℝ)) = 1 := by
        have hsub1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub hn1, Nat.cast_one]
        nlinarith [Real.sq_sqrt hn_pos.le, Real.sq_sqrt (Nat.cast_nonneg (n - 1)), hsub1]
      have hle_pred : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.sub_le n 1
      have hsum_le : Real.sqrt n + Real.sqrt ((n - 1 : ℕ) : ℝ) ≤ 2 * Real.sqrt n := by
        linarith [Real.sqrt_le_sqrt hle_pred]
      have hdiff_nn : 0 ≤ Real.sqrt n - Real.sqrt ((n - 1 : ℕ) : ℝ) := by
        linarith [Real.sqrt_le_sqrt hle_pred]
      rw [inv_le_iff_one_le_mul₀' hsqrt_pos]
      nlinarith
    rw [hsplit_n]
    calc (n : ℝ) ^ (1 / 2 - σ) * (n : ℝ) ^ (-(1 / 2 : ℝ))
        ≤ (K : ℝ) ^ (1 / 2 - σ) * (2 * (Real.sqrt n - Real.sqrt ((n - 1 : ℕ) : ℝ))) :=
          mul_le_mul hmono hinv_sqrt (by positivity) (by positivity)
      _ = 2 * (K : ℝ) ^ (1 / 2 - σ) * (Real.sqrt n - Real.sqrt ((n - 1 : ℕ) : ℝ)) := by ring
  have htel : ∀ m : ℕ, (∑ n ∈ Finset.Icc 1 m, (Real.sqrt n - Real.sqrt ((n - 1 : ℕ) : ℝ))) =
      Real.sqrt m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1), ih, Nat.add_sub_cancel]
      ring
  calc (∑ n ∈ Finset.Icc 1 K, (n : ℝ) ^ (-σ))
      ≤ ∑ n ∈ Finset.Icc 1 K,
          2 * (K : ℝ) ^ (1 / 2 - σ) * (Real.sqrt n - Real.sqrt ((n - 1 : ℕ) : ℝ)) :=
        Finset.sum_le_sum hterm
    _ = 2 * (K : ℝ) ^ (1 / 2 - σ) * Real.sqrt K := by rw [← Finset.mul_sum, htel K]
    _ = 2 * (K : ℝ) ^ (1 - σ) := by
        have hK_pos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
        rw [Real.sqrt_eq_rpow, mul_assoc, ← Real.rpow_add hK_pos]
        congr 2
        ring

/-- **Sub-quarter-Nyquist blindness and order-optimality of the `O(|Im s|)` prefix scale:**
for every `s : ℂ` with `0 ≤ Re s ≤ 1 / 2`, every cutoff `N : ℕ` with `4 (N + 1) ≤ |Im s|`, and
**every** Euler–Knopp order `M ≥ 1` (even when `ζ(s) ≠ 0`), `‖eulerEtaPartialSum N M s‖` is
strictly smaller than `eulerEtaTailBound N M s`. Hence any certificate beating `eulerEtaTailBound`
on `0 ≤ Re s ≤ 1 / 2` necessarily satisfies `|Im s| < 4 (N + 1)`. -/
theorem norm_eulerEtaPartialSum_lt_tail_of_sub_nyquist
    {s : ℂ} (hs0 : 0 ≤ s.re) (hs_half : s.re ≤ 1 / 2)
    {N M : ℕ} (hM : 1 ≤ M) (him : 4 * ((N : ℝ) + 1) ≤ |s.im|) :
    ‖eulerEtaPartialSum N M s‖ < eulerEtaTailBound N M s := by
  have hNM_pos : 1 ≤ N + M := by omega
  have hsum_norm : ‖eulerEtaPartialSum N M s‖ ≤ 2 * ((N + M : ℕ) : ℝ) ^ (1 - s.re) := by
    unfold eulerEtaPartialSum
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun n hn => ?_).trans
      (sum_Icc_rpow_neg_le_two_mul_rpow hs0 hs_half hNM_pos)
    obtain ⟨hn1, _⟩ := Finset.mem_Icc.mp hn
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      show (n : ℂ) = ((n : ℝ) : ℂ) by norm_cast,
      Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hn1), Complex.neg_re]
    exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      ((eulerEtaSign_properties N M).2.2 n)
  have hNM_le_prod : ((N + M : ℕ) : ℝ) ≤ ((N : ℝ) + 1) * (2 : ℝ) ^ M := by
    have hpow_gt : M + 1 ≤ 2 ^ M := Nat.lt_two_pow_self
    have hnat : N + M ≤ (N + 1) * 2 ^ M := by
      calc N + M ≤ (N + 1) * (M + 1) := by nlinarith
        _ ≤ (N + 1) * 2 ^ M := Nat.mul_le_mul_left (N + 1) hpow_gt
    calc ((N + M : ℕ) : ℝ) ≤ (((N + 1) * 2 ^ M : ℕ) : ℝ) := by exact_mod_cast hnat
      _ = ((N : ℝ) + 1) * (2 : ℝ) ^ M := by push_cast; ring
  have hupper : ‖eulerEtaPartialSum N M s‖ ≤ 2 * ((N : ℝ) + 1) ^ (1 - s.re) * (2 : ℝ) ^ M := by
    have hrpow1 : ((N + M : ℕ) : ℝ) ^ (1 - s.re) ≤
        (((N : ℝ) + 1) * (2 : ℝ) ^ M) ^ (1 - s.re) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hNM_le_prod (by linarith)
    have hrpow2 : (((N : ℝ) + 1) * (2 : ℝ) ^ M) ^ (1 - s.re) =
        ((N : ℝ) + 1) ^ (1 - s.re) * ((2 : ℝ) ^ M) ^ (1 - s.re) :=
      Real.mul_rpow (by positivity) (by positivity)
    have hrpow3 : ((2 : ℝ) ^ M) ^ (1 - s.re) ≤ (2 : ℝ) ^ M := by
      have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ M := one_le_pow₀ (by norm_num)
      calc ((2 : ℝ) ^ M) ^ (1 - s.re) ≤ ((2 : ℝ) ^ M) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
        _ = (2 : ℝ) ^ M := Real.rpow_one _
    calc ‖eulerEtaPartialSum N M s‖
        ≤ 2 * ((N + M : ℕ) : ℝ) ^ (1 - s.re) := hsum_norm
      _ ≤ 2 * (((N : ℝ) + 1) ^ (1 - s.re) * ((2 : ℝ) ^ M) ^ (1 - s.re)) := by
          rw [← hrpow2]; exact mul_le_mul_of_nonneg_left hrpow1 zero_le_two
      _ ≤ 2 * (((N : ℝ) + 1) ^ (1 - s.re) * (2 : ℝ) ^ M) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hrpow3 (Real.rpow_nonneg (by positivity) _)) zero_le_two
      _ = 2 * ((N : ℝ) + 1) ^ (1 - s.re) * (2 : ℝ) ^ M := by ring
  have hprod_ge : (4 * ((N : ℝ) + 1)) ^ (M + 1) ≤ ∏ m ∈ Finset.range (M + 1), ‖s + (m : ℂ)‖ := by
    calc (4 * ((N : ℝ) + 1)) ^ (M + 1)
        = ∏ _m ∈ Finset.range (M + 1), (4 * ((N : ℝ) + 1)) := by
          rw [Finset.prod_const, Finset.card_range]
      _ ≤ ∏ m ∈ Finset.range (M + 1), ‖s + (m : ℂ)‖ := by
          refine Finset.prod_le_prod (fun _ _ => by positivity) fun m _ => ?_
          have him_m : (s + (m : ℂ)).im = s.im := by simp
          exact him.trans (by rw [← him_m]; exact Complex.abs_im_le_norm (s + (m : ℂ)))
  have hlower : 6 * ((N : ℝ) + 1) ^ (1 - s.re) * (2 : ℝ) ^ M ≤ eulerEtaTailBound N M s := by
    unfold eulerEtaTailBound
    have hNpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have hrpow_join : ((N : ℝ) + 1) ^ (M + 1) * ((N : ℝ) + 1) ^ (-s.re - (M : ℝ)) =
        ((N : ℝ) + 1) ^ (1 - s.re) := by
      rw [← Real.rpow_natCast ((N : ℝ) + 1) (M + 1), ← Real.rpow_add hNpos]
      congr 1; push_cast; ring
    have h4pow : (3 / (2 : ℝ) ^ (M + 1)) * (4 * ((N : ℝ) + 1)) ^ (M + 1) *
          ((N : ℝ) + 1) ^ (-s.re - (M : ℝ)) =
        6 * ((N : ℝ) + 1) ^ (1 - s.re) * (2 : ℝ) ^ M := by
      rw [mul_pow, show (4 : ℝ) ^ (M + 1) = (2 : ℝ) ^ (M + 1) * (2 : ℝ) ^ (M + 1) by
        rw [← mul_pow]; norm_num]
      have h2ne : (2 : ℝ) ^ (M + 1) ≠ 0 := by positivity
      calc (3 / (2 : ℝ) ^ (M + 1)) *
              (((2 : ℝ) ^ (M + 1) * (2 : ℝ) ^ (M + 1)) * ((N : ℝ) + 1) ^ (M + 1)) *
              ((N : ℝ) + 1) ^ (-s.re - (M : ℝ))
          = 3 * (2 : ℝ) ^ (M + 1) *
              (((N : ℝ) + 1) ^ (M + 1) * ((N : ℝ) + 1) ^ (-s.re - (M : ℝ))) := by
            field_simp [h2ne]
        _ = 6 * ((N : ℝ) + 1) ^ (1 - s.re) * (2 : ℝ) ^ M := by
            rw [hrpow_join, pow_succ]; ring
    rw [← h4pow]
    refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hNpos.le _)
    exact mul_le_mul_of_nonneg_left hprod_ge (by positivity)
  have hpos_term : 0 < ((N : ℝ) + 1) ^ (1 - s.re) * (2 : ℝ) ^ M := by positivity
  linarith

/-! ### 2. Exact 2-Adic Floor-Parity Rigidity and Multi-Scale Stride-Euler Operators -/

/-- **Exact 2-adic floor-parity rigidity:** for positive integers `d` and `k`, the floor-quotient
increment `(X + k) / d - X / d` is odd at **every** `X : ℕ` if and only if `d ∣ k` and `Odd (k / d)`. -/
theorem odd_div_sub_div_forall_iff {d k : ℕ} (hd : 0 < d) :
    (∀ X : ℕ, Odd ((X + k) / d - X / d)) ↔ d ∣ k ∧ Odd (k / d) := by
  constructor
  · intro hall
    have h0 : Odd (k / d) := by
      simpa only [zero_add, Nat.zero_div, Nat.sub_zero] using hall 0
    refine ⟨?_, h0⟩
    rw [Nat.dvd_iff_mod_eq_zero]
    by_contra hmod_ne
    have hmod_pos : 1 ≤ k % d := Nat.pos_of_ne_zero hmod_ne
    have hmod_lt : k % d < d := Nat.mod_lt k hd
    have hd1_div : (d - 1) / d = 0 := Nat.div_eq_of_lt (by omega)
    have hsum_eq : d - 1 + k = (k % d - 1) + d * (k / d + 1) := by
      have hdiv := Nat.div_add_mod k d
      have hmul : d * (k / d + 1) = d * (k / d) + d := by ring
      omega
    have hshift_div : (d - 1 + k) / d = k / d + 1 := by
      rw [hsum_eq, Nat.add_mul_div_left _ _ hd, Nat.div_eq_of_lt (by omega : k % d - 1 < d), zero_add]
    have h1 : Odd (k / d + 1) := by
      have := hall (d - 1)
      rwa [hshift_div, hd1_div, Nat.sub_zero] at this
    obtain ⟨m, hm⟩ := h0
    obtain ⟨n, hn⟩ := h1
    omega
  · rintro ⟨⟨q, rfl⟩, hodd⟩ X
    rw [Nat.mul_div_cancel_left q hd] at hodd
    rw [Nat.add_mul_div_left X q hd, Nat.add_sub_cancel_left]
    exact hodd

/-- **Incompatibility of dyadically distinct channels under any single stride:** no single stride
`k : ℕ` can uniformly flip `(-1)^{⌊X / d⌋}` across both `d = 1` and `d = 2`. -/
theorem no_single_stride_flips_one_and_two (k : ℕ) :
    ¬ ((∀ X : ℕ, Odd ((X + k) / 1 - X / 1)) ∧ (∀ X : ℕ, Odd ((X + k) / 2 - X / 2))) := by
  rintro ⟨h1, h2⟩
  obtain ⟨_, hodd_k⟩ := (odd_div_sub_div_forall_iff one_pos).mp h1
  obtain ⟨hdvd2, _⟩ := (odd_div_sub_div_forall_iff two_pos).mp h2
  rw [Nat.div_one] at hodd_k
  obtain ⟨q, rfl⟩ := hdvd2
  obtain ⟨m, hm⟩ := hodd_k
  omega

/-- Stride-`d` two-point dyadic averaging operator on `ℕ → ℂ`. -/
def strideAvg (d : ℕ) (F : ℕ → ℂ) (X : ℕ) : ℂ :=
  (2 : ℂ)⁻¹ * (F X + F (X + d))

@[simp]
lemma strideAvg_apply (d : ℕ) (F : ℕ → ℂ) (X : ℕ) :
    strideAvg d F X = (2 : ℂ)⁻¹ * (F X + F (X + d)) := rfl

lemma strideAvg_const (d : ℕ) (c : ℂ) : strideAvg d (fun _ => c) = fun _ => c := by
  funext X
  simp only [strideAvg_apply]
  ring

lemma strideAvg_add (d : ℕ) (F G : ℕ → ℂ) :
    strideAvg d (fun X => F X + G X) = fun X => strideAvg d F X + strideAvg d G X := by
  funext X
  simp only [strideAvg_apply]
  ring

lemma strideAvg_smul (d : ℕ) (c : ℂ) (F : ℕ → ℂ) :
    strideAvg d (fun X => c * F X) = fun X => c * strideAvg d F X := by
  funext X
  simp only [strideAvg_apply]
  ring

/-- Commutativity of stride-averaging operators at arbitrary strides `d₁, d₂`. -/
theorem strideAvg_comm (d₁ d₂ : ℕ) (F : ℕ → ℂ) :
    strideAvg d₁ (strideAvg d₂ F) = strideAvg d₂ (strideAvg d₁ F) := by
  funext X
  simp only [strideAvg_apply, show X + d₁ + d₂ = X + d₂ + d₁ by omega]
  ring

private lemma strideAvg_iterate_comm_one (d₁ d₂ M₂ : ℕ) (F : ℕ → ℂ) :
    strideAvg d₁ ((strideAvg d₂)^[M₂] F) = (strideAvg d₂)^[M₂] (strideAvg d₁ F) := by
  induction M₂ generalizing F with
  | zero => rfl
  | succ M₂ ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', strideAvg_comm, ih]

theorem iterate_strideAvg_comm (d₁ d₂ M₁ M₂ : ℕ) (F : ℕ → ℂ) :
    (strideAvg d₁)^[M₁] ((strideAvg d₂)^[M₂] F) =
      (strideAvg d₂)^[M₂] ((strideAvg d₁)^[M₁] F) := by
  induction M₁ generalizing F with
  | zero => rfl
  | succ M₁ ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, strideAvg_iterate_comm_one]

private lemma iterate_strideAvg_add (d M : ℕ) (F G : ℕ → ℂ) :
    (strideAvg d)^[M] (fun X => F X + G X) =
      fun X => (strideAvg d)^[M] F X + (strideAvg d)^[M] G X := by
  induction M with
  | zero => rfl
  | succ M ih =>
    rw [Function.iterate_succ_apply', ih, strideAvg_add]
    funext X
    simp only [Function.iterate_succ_apply']

private lemma iterate_strideAvg_smul (d M : ℕ) (c : ℂ) (F : ℕ → ℂ) :
    (strideAvg d)^[M] (fun X => c * F X) = fun X => c * (strideAvg d)^[M] F X := by
  induction M with
  | zero => rfl
  | succ M ih =>
    rw [Function.iterate_succ_apply', ih, strideAvg_smul]
    funext X
    simp only [Function.iterate_succ_apply']

private lemma iterate_strideAvg_finset_sum {ι : Type*} (s : Finset ι) (d M : ℕ) (F : ι → ℕ → ℂ) :
    (strideAvg d)^[M] (fun X => ∑ i ∈ s, F i X) =
      fun X => ∑ i ∈ s, (strideAvg d)^[M] (F i) X := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have hempty : (fun X : ℕ => ∑ i ∈ (∅ : Finset ι), F i X) = fun _ => (0 : ℂ) := by
      funext X; exact Finset.sum_empty
    have hzero : (strideAvg d)^[M] (fun _ => (0 : ℂ)) = fun _ => (0 : ℂ) := by
      induction M with
      | zero => rfl
      | succ M ih => rw [Function.iterate_succ_apply', ih, strideAvg_const]
    rw [hempty, hzero]
    funext X
    exact Finset.sum_empty.symm
  | insert a s ha ih =>
    have hsplit : (fun X => ∑ i ∈ insert a s, F i X) =
        fun X => F a X + ∑ i ∈ s, F i X := by
      funext X; exact Finset.sum_insert ha
    rw [hsplit, iterate_strideAvg_add, ih]
    funext X
    exact (Finset.sum_insert (f := fun i => (strideAvg d)^[M] (F i) X) ha).symm

/-- **Exact quotient-channel Euler collapse:** iterating `strideAvg d` `M` times on the floor-quotient
alternating sum `Y ↦ dqptAltPartialSum w (Y / d)` produces `eulerEtaPartialSum (X / d) M w`
identically for every `d ≥ 1`, `M : ℕ`, `X : ℕ`, and `w : ℂ`. -/
theorem iterate_strideAvg_altPartialSum_div_eq_eulerEtaPartialSum
    {d : ℕ} (hd : 0 < d) (M : ℕ) (w : ℂ) :
    (strideAvg d)^[M] (fun Y => dqptAltPartialSum w (Y / d)) =
      fun X => eulerEtaPartialSum (X / d) M w := by
  induction M with
  | zero =>
    funext X
    exact (eulerEtaPartialSum_zero_order (X / d) w).symm
  | succ M ih =>
    funext X
    rw [Function.iterate_succ_apply', ih, strideAvg_apply, Nat.add_div_right X hd,
      ← eulerEtaPartialSum_succ_order (X / d) M w]

/-- Multi-scale commuting product of `M`-fold stride-Euler operators across a stride list `ds`. -/
def multiStrideEuler (ds : List ℕ) (M : ℕ) (F : ℕ → ℂ) : ℕ → ℂ :=
  ds.foldr (fun d G => (strideAvg d)^[M] G) F

lemma multiStrideEuler_nil (M : ℕ) (F : ℕ → ℂ) : multiStrideEuler [] M F = F := rfl

lemma multiStrideEuler_cons (d : ℕ) (ds : List ℕ) (M : ℕ) (F : ℕ → ℂ) :
    multiStrideEuler (d :: ds) M F = (strideAvg d)^[M] (multiStrideEuler ds M F) := rfl

lemma multiStrideEuler_add (ds : List ℕ) (M : ℕ) (F G : ℕ → ℂ) :
    multiStrideEuler ds M (fun X => F X + G X) =
      fun X => multiStrideEuler ds M F X + multiStrideEuler ds M G X := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    rw [multiStrideEuler_cons, ih, iterate_strideAvg_add]
    rfl

lemma multiStrideEuler_finset_sum {ι : Type*} (s : Finset ι) (ds : List ℕ) (M : ℕ)
    (F : ι → ℕ → ℂ) :
    multiStrideEuler ds M (fun X => ∑ i ∈ s, F i X) =
      fun X => ∑ i ∈ s, multiStrideEuler ds M (F i) X := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    rw [multiStrideEuler_cons, ih, iterate_strideAvg_finset_sum]
    rfl

lemma multiStrideEuler_smul (ds : List ℕ) (M : ℕ) (c : ℂ) (F : ℕ → ℂ) :
    multiStrideEuler ds M (fun X => c * F X) = fun X => c * multiStrideEuler ds M F X := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    rw [multiStrideEuler_cons, ih, iterate_strideAvg_smul]
    rfl

private lemma norm_iterate_strideAvg_sub_const_le_of_window (d M : ℕ) (F : ℕ → ℂ) (L : ℂ)
    {B : ℝ} {X₀ : ℕ} (hB : ∀ Y : ℕ, X₀ ≤ Y → Y ≤ X₀ + M * d → ‖F Y - L‖ ≤ B) :
    ‖(strideAvg d)^[M] F X₀ - L‖ ≤ B := by
  induction M generalizing X₀ with
  | zero => exact hB X₀ le_rfl (by omega)
  | succ M ih =>
    rw [Function.iterate_succ_apply', strideAvg_apply]
    have hsplit : (2 : ℂ)⁻¹ * ((strideAvg d)^[M] F X₀ + (strideAvg d)^[M] F (X₀ + d)) - L =
        (2 : ℂ)⁻¹ * (((strideAvg d)^[M] F X₀ - L) + ((strideAvg d)^[M] F (X₀ + d) - L)) := by
      ring
    have hb1 : ‖(strideAvg d)^[M] F X₀ - L‖ ≤ B :=
      ih fun Y hlo hhi => hB Y hlo (hhi.trans (by rw [Nat.succ_mul]; omega))
    have hb2 : ‖(strideAvg d)^[M] F (X₀ + d) - L‖ ≤ B :=
      ih fun Y hlo hhi => hB Y (by omega) (by rw [Nat.succ_mul]; omega)
    rw [hsplit, norm_mul, norm_inv, Complex.norm_ofNat]
    have htri := norm_add_le ((strideAvg d)^[M] F X₀ - L) ((strideAvg d)^[M] F (X₀ + d) - L)
    linarith

/-- **Exact support-window contractivity of `multiStrideEuler`:** on `[X₀, X₀ + M · ds.sum]`,
`multiStrideEuler ds M` preserves any uniform norm proximity `‖F Y - L‖ ≤ B`. -/
theorem norm_multiStrideEuler_sub_const_le_of_window (ds : List ℕ) (M : ℕ) (F : ℕ → ℂ) (L : ℂ)
    {B : ℝ} {X₀ : ℕ} (hB : ∀ Y : ℕ, X₀ ≤ Y → Y ≤ X₀ + M * ds.sum → ‖F Y - L‖ ≤ B) :
    ‖multiStrideEuler ds M F X₀ - L‖ ≤ B := by
  induction ds generalizing X₀ with
  | nil =>
    simpa only [multiStrideEuler_nil, List.sum_nil, mul_zero, add_zero] using hB X₀ le_rfl le_rfl
  | cons d ds ih =>
    rw [multiStrideEuler_cons]
    refine norm_iterate_strideAvg_sub_const_le_of_window d M (multiStrideEuler ds M F) L
      fun Y hlo hhi => ih fun Z hZlo hZhi => hB Z (hlo.trans hZlo) ?_
    rw [List.sum_cons, Nat.mul_add]
    omega

theorem norm_multiStrideEuler_le_of_window (ds : List ℕ) (M : ℕ) (F : ℕ → ℂ)
    {B : ℝ} {X₀ : ℕ} (hB : ∀ Y : ℕ, X₀ ≤ Y → Y ≤ X₀ + M * ds.sum → ‖F Y‖ ≤ B) :
    ‖multiStrideEuler ds M F X₀‖ ≤ B := by
  simpa only [sub_zero] using
    norm_multiStrideEuler_sub_const_le_of_window ds M F 0 (by simpa only [sub_zero] using hB)

private lemma multiStrideEuler_congr_of_window (ds : List ℕ) (M : ℕ) {F G : ℕ → ℂ} {X₀ : ℕ}
    (hFG : ∀ Y : ℕ, X₀ ≤ Y → Y ≤ X₀ + M * ds.sum → F Y = G Y) :
    multiStrideEuler ds M F X₀ = multiStrideEuler ds M G X₀ := by
  have h0 : ‖multiStrideEuler ds M (fun Y => F Y - G Y) X₀‖ ≤ 0 :=
    norm_multiStrideEuler_le_of_window ds M _ fun Y hlo hhi => by
      rw [hFG Y hlo hhi, sub_self, norm_zero]
  have hsub : multiStrideEuler ds M F X₀ =
      multiStrideEuler ds M G X₀ + multiStrideEuler ds M (fun Y => F Y - G Y) X₀ := by
    have h := congrFun (multiStrideEuler_add ds M G (fun Y => F Y - G Y)) X₀
    have hfg : (fun Y => G Y + (F Y - G Y)) = F := funext fun Y => by ring
    rwa [hfg] at h
  rw [hsub, norm_le_zero_iff.mp h0, add_zero]

private lemma iterate_strideAvg_multiStrideEuler_comm (d : ℕ) (ds : List ℕ) (M : ℕ) (F : ℕ → ℂ) :
    (strideAvg d)^[M] (multiStrideEuler ds M F) =
      multiStrideEuler ds M ((strideAvg d)^[M] F) := by
  induction ds with
  | nil => rfl
  | cons b tl ih =>
    rw [multiStrideEuler_cons, multiStrideEuler_cons, ← ih, iterate_strideAvg_comm]

private lemma exists_multiStrideEuler_pull_mem {d : ℕ} {ds : List ℕ} (hmem : d ∈ ds) (M : ℕ)
    (F : ℕ → ℂ) :
    ∃ rest : List ℕ, rest.sum + d = ds.sum ∧
      multiStrideEuler ds M F = multiStrideEuler rest M ((strideAvg d)^[M] F) := by
  induction ds with
  | nil => cases hmem
  | cons a tl ih =>
    rcases List.mem_cons.mp hmem with rfl | htl
    · exact ⟨tl, by rw [List.sum_cons]; omega, iterate_strideAvg_multiStrideEuler_comm d tl M F⟩
    · obtain ⟨rest, hsum, heq⟩ := ih htl
      exact ⟨a :: rest, by rw [List.sum_cons, List.sum_cons]; omega,
        by rw [multiStrideEuler_cons, heq, ← multiStrideEuler_cons]⟩

private lemma list_range'_one_sum_mul_two :
    ∀ D : ℕ, 2 * (List.range' 1 D).sum = D * (D + 1)
  | 0 => rfl
  | D + 1 => by
    rw [List.range'_concat, List.sum_append, List.sum_singleton, Nat.mul_add,
      list_range'_one_sum_mul_two D]
    ring

/-- **Simultaneous `D`-channel exponential annihilation:** for `D ≥ 1`, `M ≥ max 10 ⌈|Im w|⌉₊`,
and `X₀ ≥ 2 D M`, the commuting product `multiStrideEuler (List.range' 1 D) M` has exact shift
horizon `X₀ + M D (D + 1) / 2` and drives **every** divisor channel `1 ≤ d ≤ D` (and their weighted
Liouville sum) exponentially small whenever `ζ(w) = 0`. -/
theorem norm_multiStrideEuler_lowDivisors_le_of_zeta_eq_zero
    {w : ℂ} (hw0 : 0 < w.re) (hw1 : w.re ≤ 1) (hne1 : w ≠ 1) (hz : riemannZeta w = 0)
    {D M X₀ : ℕ} (hM10 : 10 ≤ M) (him : |w.im| ≤ (M : ℝ)) (hX₀ : 2 * D * M ≤ X₀) :
    (List.range' 1 D).sum = D * (D + 1) / 2 ∧
    (∀ d : ℕ, 1 ≤ d → d ≤ D →
      ‖multiStrideEuler (List.range' 1 D) M (fun Y => dqptAltPartialSum w (Y / d)) X₀‖ ≤
        3 / (2 : ℝ) ^ (M / 2)) ∧
    ‖multiStrideEuler (List.range' 1 D) M
        (fun Y => ∑ d ∈ Finset.Icc 1 D,
          _root_.RHTower.liouvilleC d * (d : ℂ) ^ (-w) * dqptAltPartialSum w (Y / d)) X₀‖ ≤
      3 * (D : ℝ) / (2 : ℝ) ^ (M / 2) := by
  have hsum_eq : (List.range' 1 D).sum = D * (D + 1) / 2 := by
    have h2 := list_range'_one_sum_mul_two D
    omega
  have hchan : ∀ d : ℕ, 1 ≤ d → d ≤ D →
      ‖multiStrideEuler (List.range' 1 D) M (fun Y => dqptAltPartialSum w (Y / d)) X₀‖ ≤
        3 / (2 : ℝ) ^ (M / 2) := by
    intro d hd1 hdD
    have hmem : d ∈ List.range' 1 D := List.mem_range'.mpr ⟨d - 1, by omega, by omega⟩
    obtain ⟨rest, _, hpull⟩ := exists_multiStrideEuler_pull_mem hmem M
      (fun Y => dqptAltPartialSum w (Y / d))
    rw [hpull, iterate_strideAvg_altPartialSum_div_eq_eulerEtaPartialSum hd1 M w]
    refine norm_multiStrideEuler_le_of_window rest M (fun Y => eulerEtaPartialSum (Y / d) M w)
      fun Y hYlo _ => ?_
    have h2M_le : 2 * M ≤ Y / d := by
      refine (Nat.le_div_iff_mul_le hd1).mpr ?_
      have hmul : 2 * M * d ≤ 2 * D * M := by
        calc 2 * M * d = 2 * d * M := by ring
          _ ≤ 2 * D * M := Nat.mul_le_mul_right M (Nat.mul_le_mul_left 2 hdD)
      exact hmul.trans (hX₀.trans hYlo)
    exact ((norm_eulerEtaPartialSum_le_tail_of_zeta_eq_zero hw0 hne1 hz).1 (Y / d) M
      (by omega)).trans
      (eulerEtaTailBound_le_three_div_two_pow_half_of_two_mul_le hw0 hw1 hM10 him h2M_le)
  refine ⟨hsum_eq, hchan, ?_⟩
  rw [multiStrideEuler_finset_sum]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ d ∈ Finset.Icc 1 D,
        ‖multiStrideEuler (List.range' 1 D) M
          (fun Y => _root_.RHTower.liouvilleC d * (d : ℂ) ^ (-w) * dqptAltPartialSum w (Y / d)) X₀‖
      ≤ ∑ _d ∈ Finset.Icc 1 D, (3 / (2 : ℝ) ^ (M / 2)) := by
        refine Finset.sum_le_sum fun d hd => ?_
        obtain ⟨hd1, hdD⟩ := Finset.mem_Icc.mp hd
        have hsmul : (fun Y => _root_.RHTower.liouvilleC d * (d : ℂ) ^ (-w) *
              dqptAltPartialSum w (Y / d)) =
            fun Y => (_root_.RHTower.liouvilleC d * (d : ℂ) ^ (-w)) *
              dqptAltPartialSum w (Y / d) := rfl
        rw [hsmul, multiStrideEuler_smul, norm_mul, norm_mul]
        have hliouv : ‖_root_.RHTower.liouvilleC d‖ ≤ 1 := _root_.RHTower.norm_liouvilleC_le_one d
        have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
        have hd_ge1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
        have hd_cpow : ‖(d : ℂ) ^ (-w)‖ ≤ 1 := by
          rw [show (d : ℂ) = ((d : ℝ) : ℂ) by norm_cast,
            Complex.norm_cpow_eq_rpow_re_of_pos hd_pos, Complex.neg_re]
          exact Real.rpow_le_one_of_one_le_of_nonpos hd_ge1 (by linarith)
        have hcoef : ‖_root_.RHTower.liouvilleC d‖ * ‖(d : ℂ) ^ (-w)‖ ≤ 1 := by
          nlinarith [norm_nonneg (_root_.RHTower.liouvilleC d), norm_nonneg ((d : ℂ) ^ (-w))]
        calc (‖_root_.RHTower.liouvilleC d‖ * ‖(d : ℂ) ^ (-w)‖) *
              ‖multiStrideEuler (List.range' 1 D) M (fun Y => dqptAltPartialSum w (Y / d)) X₀‖
            ≤ 1 * (3 / (2 : ℝ) ^ (M / 2)) :=
              mul_le_mul hcoef (hchan d hd1 hdD) (norm_nonneg _) zero_le_one
          _ = 3 / (2 : ℝ) ^ (M / 2) := one_mul _
    _ = 3 * (D : ℝ) / (2 : ℝ) ^ (M / 2) := by
        rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
        ring

/-! ### 3. All-Height Liouville Square Sieve and Height-Uniform Double-Energy Floor -/

/-- Exact square-sieved double-energy Dirichlet eta head on `[1, X]`. -/
def squareEtaHead (X : ℕ) (w : ℂ) : ℂ :=
  (∑ k ∈ Finset.Icc 1 (Nat.sqrt X), (k : ℂ) ^ (-(2 * w))) -
    (2 : ℂ) ^ (1 - w) * ∑ k ∈ Finset.Icc 1 (Nat.sqrt (X / 2)), (k : ℂ) ^ (-(2 * w))

private def harmonicPartialSum (K : ℕ) (w : ℂ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 K, (m : ℂ) ^ (-w)

private lemma dqptAltPartialSum_eq_harmonic_sub_even (w : ℂ) (K : ℕ) :
    dqptAltPartialSum w K =
      harmonicPartialSum K w - (2 : ℂ) ^ (1 - w) * harmonicPartialSum (K / 2) w := by
  induction K with
  | zero => simp [harmonicPartialSum]
  | succ K ih =>
    rw [dqptAltPartialSum_succ, ih]
    unfold harmonicPartialSum
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ K + 1)]
    have hcast : (((K : ℝ) + 1 : ℝ) : ℂ) = ((K + 1 : ℕ) : ℂ) := by push_cast; ring
    have hrp : dqptRp w ((K : ℝ) + 1) = ((K + 1 : ℕ) : ℂ) ^ (-w) := by
      rw [dqptRp, hcast]
    rw [hrp]
    rcases Nat.even_or_odd K with ⟨q, rfl⟩ | ⟨q, rfl⟩
    · have hdiv : (q + q + 1) / 2 = q := by omega
      have hdiv0 : (q + q) / 2 = q := by omega
      have hpow : (-1 : ℂ) ^ (q + q) = 1 := by
        rw [← two_mul, pow_mul, neg_one_sq, one_pow]
      rw [hdiv, hdiv0, hpow, one_mul]
      ring
    · have hdiv1 : (2 * q + 1 + 1) / 2 = q + 1 := by omega
      have hdiv0 : (2 * q + 1) / 2 = q := by omega
      have hpow : (-1 : ℂ) ^ (2 * q + 1) = -1 := by
        rw [pow_add, pow_mul, neg_one_sq, one_pow, one_mul, pow_one]
      have h2cpow : (2 : ℂ) ^ (1 - w) * ((q + 1 : ℕ) : ℂ) ^ (-w) =
          2 * ((2 * q + 1 + 1 : ℕ) : ℂ) ^ (-w) := by
        have h1w : (2 : ℂ) ^ (1 - w) = 2 * ((2 : ℝ) : ℂ) ^ (-w) := by
          rw [show (1 - w : ℂ) = 1 + (-w) by ring, Complex.cpow_add _ _ two_ne_zero,
            Complex.cpow_one]
          norm_num
        have hmul_nat : ((2 * q + 1 + 1 : ℕ) : ℂ) = ((2 : ℝ) : ℂ) * (((q + 1 : ℕ) : ℝ) : ℂ) := by
          push_cast; ring
        rw [h1w, hmul_nat, Complex.mul_cpow_ofReal_nonneg zero_le_two (Nat.cast_nonneg _)]
        norm_cast
        ring
      rw [hdiv1, hdiv0, Finset.sum_Icc_succ_top (by omega : 1 ≤ q + 1), hpow, neg_one_mul,
        mul_add, h2cpow]
      ring

private lemma sum_liouville_mul_harmonicPartialSum_div (Y : ℕ) (w : ℂ) :
    (∑ d ∈ Finset.Icc 1 Y, _root_.RHTower.liouvilleC d * (d : ℂ) ^ (-w) *
        harmonicPartialSum (Y / d) w) =
      ∑ k ∈ Finset.Icc 1 (Nat.sqrt Y), (k : ℂ) ^ (-(2 * w)) := by
  unfold harmonicPartialSum
  have hexpand : (∑ d ∈ Finset.Icc 1 Y, _root_.RHTower.liouvilleC d * (d : ℂ) ^ (-w) *
        ∑ m ∈ Finset.Icc 1 (Y / d), (m : ℂ) ^ (-w)) =
      ∑ p ∈ (Finset.Icc 1 Y).sigma (fun d => Finset.Icc 1 (Y / d)),
        _root_.RHTower.liouvilleC p.1 * ((p.1 * p.2 : ℕ) : ℂ) ^ (-w) := by
    rw [Finset.sum_sigma]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    have hmul : (d : ℂ) ^ (-w) * (m : ℂ) ^ (-w) = ((d * m : ℕ) : ℂ) ^ (-w) := by
      rw [show ((d * m : ℕ) : ℂ) = ((d : ℝ) : ℂ) * ((m : ℝ) : ℂ) by push_cast; ring,
        Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg d) (Nat.cast_nonneg m)]
      norm_cast
    rw [mul_assoc, hmul]
  have hbij : (∑ p ∈ (Finset.Icc 1 Y).sigma (fun d => Finset.Icc 1 (Y / d)),
        _root_.RHTower.liouvilleC p.1 * ((p.1 * p.2 : ℕ) : ℂ) ^ (-w)) =
      ∑ q ∈ (Finset.Icc 1 Y).sigma (fun n => n.divisors),
        _root_.RHTower.liouvilleC q.2 * (q.1 : ℂ) ^ (-w) := by
    refine Finset.sum_bij (fun p _ => ⟨p.1 * p.2, p.1⟩) ?_ ?_ ?_ ?_
    · rintro ⟨d, m⟩ hp
      obtain ⟨hd, hm⟩ := Finset.mem_sigma.mp hp
      obtain ⟨hd1, _⟩ := Finset.mem_Icc.mp hd
      obtain ⟨hm1, hmY⟩ := Finset.mem_Icc.mp hm
      have hdm_le : d * m ≤ Y := by
        rw [mul_comm]
        exact (Nat.le_div_iff_mul_le hd1).mp hmY
      have hdm_pos : 1 ≤ d * m := Nat.mul_pos hd1 hm1
      exact Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨hdm_pos, hdm_le⟩,
        Nat.mem_divisors.mpr ⟨dvd_mul_right d m, Nat.ne_of_gt hdm_pos⟩⟩
    · rintro ⟨d₁, m₁⟩ hp₁ ⟨d₂, m₂⟩ _ heq
      obtain ⟨hd₁, _⟩ := Finset.mem_sigma.mp hp₁
      have hd₁_pos : 0 < d₁ := (Finset.mem_Icc.mp hd₁).1
      injection heq with hprod hd_eq
      subst hd_eq
      have hm_eq : m₁ = m₂ := Nat.eq_of_mul_eq_mul_left hd₁_pos hprod
      subst hm_eq
      rfl
    · rintro ⟨n, d⟩ hq
      obtain ⟨hn, hd_div⟩ := Finset.mem_sigma.mp hq
      obtain ⟨hn1, hnY⟩ := Finset.mem_Icc.mp hn
      obtain ⟨⟨m, hm_eq⟩, _⟩ := Nat.mem_divisors.mp hd_div
      change n = d * m at hm_eq
      change 1 ≤ n at hn1
      change n ≤ Y at hnY
      subst hm_eq
      have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos (dvd_mul_right d m) hn1
      have hm1 : 1 ≤ m := Nat.pos_of_dvd_of_pos (dvd_mul_left m d) hn1
      have hm_le : m ≤ Y / d := (Nat.le_div_iff_mul_le hd1).mpr (by rwa [mul_comm])
      exact ⟨⟨d, m⟩, Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨hd1, by nlinarith⟩,
        Finset.mem_Icc.mpr ⟨hm1, hm_le⟩⟩, rfl⟩
    · rintro ⟨d, m⟩ _; rfl
  have hdiv_sum : (∑ q ∈ (Finset.Icc 1 Y).sigma (fun n => n.divisors),
        _root_.RHTower.liouvilleC q.2 * (q.1 : ℂ) ^ (-w)) =
      ∑ n ∈ (Finset.Icc 1 Y).filter IsSquare, (n : ℂ) ^ (-w) := by
    rw [Finset.sum_sigma, Finset.sum_filter]
    refine Finset.sum_congr rfl fun n hn => ?_
    dsimp only
    obtain ⟨hn1, _⟩ := Finset.mem_Icc.mp hn
    rw [← Finset.sum_mul, _root_.RHTower.sum_divisors_liouvilleC (by omega : n ≠ 0),
      _root_.RHTower.squareIndicator]
    split_ifs <;> simp
  have hsq_bij : (∑ n ∈ (Finset.Icc 1 Y).filter IsSquare, (n : ℂ) ^ (-w)) =
      ∑ k ∈ Finset.Icc 1 (Nat.sqrt Y), (k : ℂ) ^ (-(2 * w)) := by
    symm
    refine Finset.sum_bij (fun k _ => k * k) ?_ ?_ ?_ ?_
    · intro k hk
      obtain ⟨hk1, hksq⟩ := Finset.mem_Icc.mp hk
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.mul_pos hk1 hk1,
        Nat.le_sqrt.mp hksq⟩, ⟨k, rfl⟩⟩
    · intro k₁ _ k₂ _ heq
      exact Nat.mul_self_inj.mp heq
    · intro n hn
      obtain ⟨hn_lu, ⟨k, rfl⟩⟩ := Finset.mem_filter.mp hn
      obtain ⟨hn1, hnY⟩ := Finset.mem_Icc.mp hn_lu
      have hk1 : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with rfl | hkpos
        · simp at hn1
        · exact hkpos
      exact ⟨k, Finset.mem_Icc.mpr ⟨hk1, Nat.le_sqrt.mpr hnY⟩, rfl⟩
    · intro k hk
      obtain ⟨hk1, _⟩ := Finset.mem_Icc.mp hk
      have hk_ne : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hmul : ((k * k : ℕ) : ℂ) ^ (-w) = (k : ℂ) ^ (-w) * (k : ℂ) ^ (-w) := by
        rw [show ((k * k : ℕ) : ℂ) = ((k : ℝ) : ℂ) * ((k : ℝ) : ℂ) by push_cast; ring,
          Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg k) (Nat.cast_nonneg k)]
        norm_cast
      rw [hmul, show -(2 * w) = (-w) + (-w) by ring, Complex.cpow_add _ _ hk_ne]
  rw [hexpand, hbij, hdiv_sum, hsq_bij]

/-- **Exact all-height Liouville–eta square-sieve identity:** for every `X : ℕ` and `w : ℂ`,
convolving `dqptAltPartialSum w (X / d)` against Prime-Gas occupation parity `λ(d) d^{-w}`
annihilates every integer in `[1, X]` except squares `k²` and double-squares `2 k²`. -/
theorem sum_liouville_mul_dqptAltPartialSum_eq_squareEtaHead (X : ℕ) (w : ℂ) :
    (∑ d ∈ Finset.Icc 1 X,
        _root_.RHTower.liouvilleC d * (d : ℂ) ^ (-w) * dqptAltPartialSum w (X / d)) =
      squareEtaHead X w := by
  have hsplit : ∀ d ∈ Finset.Icc 1 X,
      _root_.RHTower.liouvilleC d * (d : ℂ) ^ (-w) * dqptAltPartialSum w (X / d) =
        _root_.RHTower.liouvilleC d * (d : ℂ) ^ (-w) * harmonicPartialSum (X / d) w -
          (2 : ℂ) ^ (1 - w) *
            (_root_.RHTower.liouvilleC d * (d : ℂ) ^ (-w) * harmonicPartialSum ((X / 2) / d) w) := by
    intro d _
    rw [dqptAltPartialSum_eq_harmonic_sub_even, Nat.div_div_eq_div_mul, mul_comm d 2,
      ← Nat.div_div_eq_div_mul]
    ring
  have htrim : (∑ d ∈ Finset.Icc 1 X,
        _root_.RHTower.liouvilleC d * (d : ℂ) ^ (-w) * harmonicPartialSum ((X / 2) / d) w) =
      ∑ d ∈ Finset.Icc 1 (X / 2),
        _root_.RHTower.liouvilleC d * (d : ℂ) ^ (-w) * harmonicPartialSum ((X / 2) / d) w := by
    refine (Finset.sum_subset (Finset.Icc_subset_Icc_right (Nat.div_le_self X 2)) ?_).symm
    intro d hd hnot
    rw [Finset.mem_Icc] at hd hnot
    have hgt : X / 2 < d := by omega
    rw [Nat.div_eq_of_lt hgt]
    simp [harmonicPartialSum]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib, ← Finset.mul_sum, htrim,
    sum_liouville_mul_harmonicPartialSum_div X w,
    sum_liouville_mul_harmonicPartialSum_div (X / 2) w]
  rfl

/-- Height-independent positive lower bound for `‖(1 - 2^{conj s}) ζ(2 - 2 conj s)‖` across all
`0 < Re s < 1/2` and all `Im s ∈ ℝ`. -/
def reflectedDoubleEtaFloor (σ : ℝ) : ℝ :=
  ((2 : ℝ) ^ σ - 1) * ((1 - 2 * σ) / (2 - 2 * σ))

/-- Explicit `Im s`-independent truncation majorant for `squareEtaHead X (1 - conj s)`. -/
def squareEtaTailBound (X : ℕ) (σ : ℝ) : ℝ :=
  ((1 + (2 : ℝ) ^ σ) / (1 - 2 * σ)) * (Nat.sqrt (X / 2) : ℝ) ^ (-(1 - 2 * σ))

/-- **Height-uniform reflected double-energy floor (`∀ Im s ∈ ℝ`):** for every `s : ℂ` with
`0 < Re s < 1 / 2` and `w = 1 - conj s`, `‖(1 - 2^{1 - w}) ζ(2 w)‖ ≥ reflectedDoubleEtaFloor s.re > 0`
unconditionally and independently of `Im s`. -/
theorem norm_eta_two_mul_refl_ge {s : ℂ} (hs0 : 0 < s.re) (hhi : s.re < 1 / 2) :
    0 < reflectedDoubleEtaFloor s.re ∧
      reflectedDoubleEtaFloor s.re ≤
        ‖(1 - (2 : ℂ) ^ (1 - (1 - conj s))) * riemannZeta (2 * (1 - conj s))‖ := by
  set w : ℂ := 1 - conj s
  have h2_gt1 : (1 : ℝ) < (2 : ℝ) ^ s.re := Real.one_lt_rpow one_lt_two hs0
  have hnum_pos : 0 < 1 - 2 * s.re := by linarith
  have hden_pos : 0 < 2 - 2 * s.re := by linarith
  have hfl_pos : 0 < reflectedDoubleEtaFloor s.re :=
    mul_pos (sub_pos.mpr h2_gt1) (div_pos hnum_pos hden_pos)
  have h2w_re : (2 * w).re = 2 - 2 * s.re := by
    simp [w, Complex.mul_re]
    ring
  have hσ₁ : 1 < 2 - 2 * s.re := by linarith
  have hinv_le := _root_.RHTower.norm_inv_riemannZeta_le_of_le_re hσ₁ (s := 2 * w)
    (by rw [h2w_re])
  have hfrac_eq : 1 + 1 / ((2 - 2 * s.re) - 1) = (2 - 2 * s.re) / (1 - 2 * s.re) := by
    rw [show (2 - 2 * s.re) - 1 = 1 - 2 * s.re by ring]
    field_simp [hnum_pos.ne']
    ring
  rw [hfrac_eq, norm_inv] at hinv_le
  have hζ_ne : riemannZeta (2 * w) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by rw [h2w_re]; linarith)
  have hζ_pos : 0 < ‖riemannZeta (2 * w)‖ := norm_pos_iff.mpr hζ_ne
  have hζ_ge : (1 - 2 * s.re) / (2 - 2 * s.re) ≤ ‖riemannZeta (2 * w)‖ := by
    rw [div_le_iff₀ hden_pos]
    have h1 := (inv_le_iff_one_le_mul₀' hζ_pos).mp hinv_le
    have hmul := mul_le_mul_of_nonneg_left h1 hnum_pos.le
    have hsimp : (1 - 2 * s.re) * ((2 - 2 * s.re) / (1 - 2 * s.re) * ‖riemannZeta (2 * w)‖) =
        ‖riemannZeta (2 * w)‖ * (2 - 2 * s.re) := by
      field_simp [hnum_pos.ne']
    linarith
  have hdyad_ge : (2 : ℝ) ^ s.re - 1 ≤ ‖1 - (2 : ℂ) ^ (1 - w)‖ := by
    have h1w : 1 - w = conj s := by dsimp [w]; ring
    rw [h1w]
    have hn : ‖(2 : ℂ) ^ (conj s)‖ = (2 : ℝ) ^ s.re := by
      rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
        Complex.norm_cpow_eq_rpow_re_of_pos two_pos, Complex.conj_re]
    have hrev := norm_sub_norm_le ((2 : ℂ) ^ (conj s)) 1
    rw [norm_sub_rev, hn, norm_one] at hrev
    linarith
  refine ⟨hfl_pos, ?_⟩
  rw [norm_mul]
  exact mul_le_mul hdyad_ge hζ_ge (by positivity) (norm_nonneg _)

private lemma norm_zeta_sub_harmonicPartialSum_le {z : ℂ} (hz : 1 < z.re) {R : ℕ} (hR : 1 ≤ R) :
    ‖riemannZeta z - ∑ k ∈ Finset.Icc 1 R, (k : ℂ) ^ (-z)‖ ≤
      (R : ℝ) ^ (-(z.re - 1)) / (z.re - 1) := by
  have hz0 : z ≠ 0 := fun h => by rw [h, Complex.zero_re] at hz; linarith
  have hsum_c : Summable (fun n : ℕ => (1 : ℂ) / (n : ℂ) ^ z) :=
    (Complex.summable_one_div_nat_cpow (p := z)).mpr hz
  have hsplit := hsum_c.sum_add_tsum_nat_add (R + 1)
  have hhead : (∑ n ∈ Finset.range (R + 1), (1 : ℂ) / (n : ℂ) ^ z) =
      ∑ k ∈ Finset.Icc 1 R, (k : ℂ) ^ (-z) := by
    rw [Finset.sum_range_succ', Nat.cast_zero, Complex.zero_cpow hz0, div_zero, add_zero,
      _root_.RHTower.sum_range_succ_eq_sum_Icc (fun k : ℕ => (1 : ℂ) / (k : ℂ) ^ z) R]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [one_div, Complex.cpow_neg]
  have hdiff : riemannZeta z - ∑ k ∈ Finset.Icc 1 R, (k : ℂ) ^ (-z) =
      ∑' j : ℕ, (1 : ℂ) / ((j + (R + 1) : ℕ) : ℂ) ^ z := by
    rw [zeta_eq_tsum_one_div_nat_cpow hz, ← hsplit, hhead, add_sub_cancel_left]
  have hnorm_term : ∀ j : ℕ, ‖(1 : ℂ) / ((j + (R + 1) : ℕ) : ℂ) ^ z‖ =
      ((j + (R + 1) : ℕ) : ℝ) ^ (-z.re) := by
    intro j
    rw [norm_div, norm_one, Complex.norm_natCast_cpow_of_pos (by omega : 0 < j + (R + 1)),
      Real.rpow_neg (Nat.cast_nonneg _), one_div]
  have hsum_r : Summable (fun j : ℕ => ((j + (R + 1) : ℕ) : ℝ) ^ (-z.re)) := by
    have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (-z.re)) :=
      Real.summable_nat_rpow.mpr (by linarith)
    exact (summable_nat_add_iff (R + 1)).mpr hbase
  have htsum_r : (∑' j : ℕ, ((j + (R + 1) : ℕ) : ℝ) ^ (-z.re)) ≤
      (R : ℝ) ^ (-(z.re - 1)) / (z.re - 1) := by
    refine Real.tsum_le_of_sum_range_le (fun j => Real.rpow_nonneg (Nat.cast_nonneg _) _) fun K => ?_
    have hreindex : (∑ j ∈ Finset.range K, ((j + (R + 1) : ℕ) : ℝ) ^ (-z.re)) =
        ∑ m ∈ Finset.Ico R (R + K), ((m + 1 : ℕ) : ℝ) ^ (-z.re) := by
      have hsh := Finset.sum_Ico_add' (fun m : ℕ => ((m + 1 : ℕ) : ℝ) ^ (-z.re)) 0 K R
      rw [zero_add, add_comm K R] at hsh
      rw [Finset.range_eq_Ico, ← hsh]
      refine Finset.sum_congr rfl fun j _ => ?_
      congr 1
      push_cast
    have hcomp := (_root_.RHTower.Sieve.antitoneOn_rpow_neg (by linarith : (0 : ℝ) ≤ z.re)
      R (R + K) hR).sum_le_integral_Ico (by omega : R ≤ R + K)
    have hRRK : (R : ℝ) ≤ ((R + K : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right R K
    have h0_not : (0 : ℝ) ∉ Set.uIcc (R : ℝ) ((R + K : ℕ) : ℝ) := by
      rw [Set.uIcc_of_le hRRK]
      intro hmem
      have hR1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
      linarith [hmem.1]
    have hint : (∫ x in (R : ℝ)..((R + K : ℕ) : ℝ), x ^ (-z.re)) ≤
        (R : ℝ) ^ (-(z.re - 1)) / (z.re - 1) := by
      rw [integral_rpow (Or.inr ⟨by linarith, h0_not⟩), show -z.re + 1 = -(z.re - 1) by ring]
      have hden : 0 < z.re - 1 := by linarith
      have hrw : (((R + K : ℕ) : ℝ) ^ (-(z.re - 1)) - (R : ℝ) ^ (-(z.re - 1))) / (-(z.re - 1)) =
          ((R : ℝ) ^ (-(z.re - 1)) - ((R + K : ℕ) : ℝ) ^ (-(z.re - 1))) / (z.re - 1) := by
        field_simp [hden.ne']
        ring
      rw [hrw]
      exact div_le_div_of_nonneg_right
        (by linarith [Real.rpow_nonneg (Nat.cast_nonneg (R + K)) (-(z.re - 1))]) hden.le
    rw [hreindex]
    exact hcomp.trans hint
  rw [hdiff]
  calc ‖∑' j : ℕ, (1 : ℂ) / ((j + (R + 1) : ℕ) : ℂ) ^ z‖
      ≤ ∑' j : ℕ, ‖(1 : ℂ) / ((j + (R + 1) : ℕ) : ℂ) ^ z‖ :=
        norm_tsum_le_tsum_norm (hsum_r.congr fun j => (hnorm_term j).symm)
    _ = ∑' j : ℕ, ((j + (R + 1) : ℕ) : ℝ) ^ (-z.re) := tsum_congr hnorm_term
    _ ≤ (R : ℝ) ^ (-(z.re - 1)) / (z.re - 1) := htsum_r

/-- **Height-independent truncation bound for `squareEtaHead X (1 - conj s)` (`X ≥ 2`):** the error
from `(1 - 2^{1-w}) ζ(2 w)` depends only on `X` and `Re s`, uniformly across all `Im s ∈ ℝ`. -/
theorem norm_squareEtaHead_refl_sub_le {s : ℂ} (_hs0 : 0 < s.re) (hhi : s.re < 1 / 2)
    {X : ℕ} (hX : 2 ≤ X) :
    ‖(1 - (2 : ℂ) ^ (1 - (1 - conj s))) * riemannZeta (2 * (1 - conj s)) -
        squareEtaHead X (1 - conj s)‖ ≤
      squareEtaTailBound X s.re := by
  set w : ℂ := 1 - conj s
  have h2w_re : (2 * w).re = 2 - 2 * s.re := by simp [w, Complex.mul_re]; ring
  have hz1 : 1 < (2 * w).re := by rw [h2w_re]; linarith
  have hden_pos : 0 < 1 - 2 * s.re := by linarith
  have hR2_pos : 1 ≤ Nat.sqrt (X / 2) :=
    Nat.le_sqrt.mpr (by have : 1 ≤ X / 2 := (Nat.le_div_iff_mul_le two_pos).mpr (by omega); omega)
  have hR2_le_R1 : Nat.sqrt (X / 2) ≤ Nat.sqrt X := Nat.sqrt_le_sqrt (Nat.div_le_self X 2)
  have hR1_pos : 1 ≤ Nat.sqrt X := hR2_pos.trans hR2_le_R1
  have hb1 := norm_zeta_sub_harmonicPartialSum_le hz1 hR1_pos
  have hb2 := norm_zeta_sub_harmonicPartialSum_le hz1 hR2_pos
  have hexp_eq : (2 * w).re - 1 = 1 - 2 * s.re := by rw [h2w_re]; ring
  rw [hexp_eq] at hb1 hb2
  have hrpow_mono : (Nat.sqrt X : ℝ) ^ (-(1 - 2 * s.re)) ≤
      (Nat.sqrt (X / 2) : ℝ) ^ (-(1 - 2 * s.re)) :=
    Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hR2_pos)
      (by exact_mod_cast hR2_le_R1) (by linarith)
  have hb1' : ‖riemannZeta (2 * w) - ∑ k ∈ Finset.Icc 1 (Nat.sqrt X), (k : ℂ) ^ (-(2 * w))‖ ≤
      (Nat.sqrt (X / 2) : ℝ) ^ (-(1 - 2 * s.re)) / (1 - 2 * s.re) :=
    hb1.trans (div_le_div_of_nonneg_right hrpow_mono hden_pos.le)
  have h2_norm : ‖(2 : ℂ) ^ (1 - w)‖ = (2 : ℝ) ^ s.re := by
    have h1w : 1 - w = conj s := by dsimp [w]; ring
    rw [h1w, show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
      Complex.norm_cpow_eq_rpow_re_of_pos two_pos, Complex.conj_re]
  have hdecomp : (1 - (2 : ℂ) ^ (1 - w)) * riemannZeta (2 * w) - squareEtaHead X w =
      (riemannZeta (2 * w) - ∑ k ∈ Finset.Icc 1 (Nat.sqrt X), (k : ℂ) ^ (-(2 * w))) -
        (2 : ℂ) ^ (1 - w) *
          (riemannZeta (2 * w) - ∑ k ∈ Finset.Icc 1 (Nat.sqrt (X / 2)), (k : ℂ) ^ (-(2 * w))) := by
    unfold squareEtaHead
    ring
  rw [hdecomp]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, h2_norm]
  calc ‖riemannZeta (2 * w) - ∑ k ∈ Finset.Icc 1 (Nat.sqrt X), (k : ℂ) ^ (-(2 * w))‖ +
        (2 : ℝ) ^ s.re *
          ‖riemannZeta (2 * w) - ∑ k ∈ Finset.Icc 1 (Nat.sqrt (X / 2)), (k : ℂ) ^ (-(2 * w))‖
      ≤ (Nat.sqrt (X / 2) : ℝ) ^ (-(1 - 2 * s.re)) / (1 - 2 * s.re) +
          (2 : ℝ) ^ s.re * ((Nat.sqrt (X / 2) : ℝ) ^ (-(1 - 2 * s.re)) / (1 - 2 * s.re)) :=
        add_le_add hb1' (mul_le_mul_of_nonneg_left hb2 (by positivity))
    _ = squareEtaTailBound X s.re := by
        unfold squareEtaTailBound
        ring

theorem squareEtaTailBound_antitone {σ : ℝ} (hhi : σ < 1 / 2) {X₁ X₂ : ℕ}
    (hX₁ : 2 ≤ X₁) (h12 : X₁ ≤ X₂) :
    squareEtaTailBound X₂ σ ≤ squareEtaTailBound X₁ σ := by
  unfold squareEtaTailBound
  have hR1 : 1 ≤ Nat.sqrt (X₁ / 2) :=
    Nat.le_sqrt.mpr (by have : 1 ≤ X₁ / 2 := (Nat.le_div_iff_mul_le two_pos).mpr (by omega); omega)
  have hR_le : Nat.sqrt (X₁ / 2) ≤ Nat.sqrt (X₂ / 2) :=
    Nat.sqrt_le_sqrt (Nat.div_le_div_right h12)
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hR1) (by exact_mod_cast hR_le) (by linarith))
    (div_nonneg (by positivity) (by linarith))

theorem tendsto_squareEtaHead_refl {s : ℂ} (hs0 : 0 < s.re) (hhi : s.re < 1 / 2) :
    Tendsto (fun X : ℕ => squareEtaHead X (1 - conj s)) atTop
      (𝓝 ((1 - (2 : ℂ) ^ (1 - (1 - conj s))) * riemannZeta (2 * (1 - conj s)))) := by
  have htend_sqrt : Tendsto (fun X : ℕ => (Nat.sqrt (X / 2) : ℝ)) atTop atTop := by
    refine tendsto_natCast_atTop_atTop.comp (tendsto_atTop.mpr fun B => ?_)
    refine eventually_atTop.mpr ⟨2 * (B * B), fun X hX => Nat.le_sqrt.mpr ?_⟩
    exact (Nat.le_div_iff_mul_le two_pos).mpr (by linarith)
  have hmaj : Tendsto (fun X : ℕ => squareEtaTailBound X s.re) atTop (𝓝 0) := by
    have h := ((tendsto_rpow_neg_atTop (by linarith : 0 < 1 - 2 * s.re)).comp htend_sqrt).const_mul
      ((1 + (2 : ℝ) ^ s.re) / (1 - 2 * s.re))
    rw [mul_zero] at h
    exact h.congr fun X => rfl
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hmaj
  filter_upwards [eventually_ge_atTop 2] with X hX
  rw [norm_sub_rev]
  exact norm_squareEtaHead_refl_sub_le hs0 hhi hX

/-- **Multi-stride preservation of the height-uniform double-energy floor:** for every stride list
`ds`, every order `M : ℕ`, every `X₀ ≥ 2`, and every `s` with `0 < Re s < 1/2` (uniformly across
all `Im s ∈ ℝ`), `multiStrideEuler ds M (squareEtaHead · (1 - conj s)) X₀` has modulus at least
`reflectedDoubleEtaFloor s.re - squareEtaTailBound X₀ s.re`. -/
theorem norm_multiStrideEuler_squareEtaHead_refl_ge (ds : List ℕ) (M : ℕ)
    {s : ℂ} (hs0 : 0 < s.re) (hhi : s.re < 1 / 2) {X₀ : ℕ} (hX₀ : 2 ≤ X₀) :
    reflectedDoubleEtaFloor s.re - squareEtaTailBound X₀ s.re ≤
      ‖multiStrideEuler ds M (fun Y => squareEtaHead Y (1 - conj s)) X₀‖ := by
  set L : ℂ := (1 - (2 : ℂ) ^ (1 - (1 - conj s))) * riemannZeta (2 * (1 - conj s))
  have hL_ge := (norm_eta_two_mul_refl_ge hs0 hhi).2
  have herr : ‖multiStrideEuler ds M (fun Y => squareEtaHead Y (1 - conj s)) X₀ - L‖ ≤
      squareEtaTailBound X₀ s.re := by
    refine norm_multiStrideEuler_sub_const_le_of_window ds M
      (fun Y => squareEtaHead Y (1 - conj s)) L fun Y hYlo _ => ?_
    rw [norm_sub_rev]
    exact (norm_squareEtaHead_refl_sub_le hs0 hhi (hX₀.trans hYlo)).trans
      (squareEtaTailBound_antitone hhi hX₀ hYlo)
  have htri : ‖L‖ ≤ ‖multiStrideEuler ds M (fun Y => squareEtaHead Y (1 - conj s)) X₀‖ +
      ‖multiStrideEuler ds M (fun Y => squareEtaHead Y (1 - conj s)) X₀ - L‖ := by
    have h := norm_add_le (multiStrideEuler ds M (fun Y => squareEtaHead Y (1 - conj s)) X₀)
      (L - multiStrideEuler ds M (fun Y => squareEtaHead Y (1 - conj s)) X₀)
    simpa only [add_sub_cancel, norm_sub_rev] using h
  linarith

/-! ### 4. Multi-Scale High-Divisor Concentration, 0–1 Defect Law, and `RiemannHypothesis` Equivalence -/

/-- **Pointwise multi-scale nonvanishing criterion across all heights:** if for some channel count
`D ≥ 1`, Euler order `M ≥ max 10 ⌈|Im s|⌉₊`, and `X₀ ≥ max 2 (2 D M)`, the `D`-stride-averaged
high-divisor Liouville hyperbola tail (`d > D`) falls strictly below
`reflectedDoubleEtaFloor s.re - squareEtaTailBound X₀ s.re - 3 D / 2^{M / 2}`, then `ζ(s) ≠ 0` and
some linear-scale Euler–Knopp partial sum at `s` strictly beats `3 / 2^{M' / 2}` (and its tail). -/
theorem exists_euler_beats_tail_of_multiStride_highDivisors_lt
    {s : ℂ} (hs0 : 0 < s.re) (hhi : s.re < 1 / 2)
    {D M X₀ : ℕ} (hM : max 10 (Nat.ceil |s.im|) ≤ M) (hX₀ : max 2 (2 * D * M) ≤ X₀)
    (hhigh : ‖multiStrideEuler (List.range' 1 D) M
        (fun Y => ∑ d ∈ Finset.Icc (D + 1) Y,
          _root_.RHTower.liouvilleC d * (d : ℂ) ^ (-(1 - conj s)) *
            dqptAltPartialSum (1 - conj s) (Y / d)) X₀‖ +
      3 * (D : ℝ) / (2 : ℝ) ^ (M / 2) + squareEtaTailBound X₀ s.re <
        reflectedDoubleEtaFloor s.re) :
    riemannZeta (1 - conj s) ≠ 0 ∧ riemannZeta s ≠ 0 ∧
      ∃ M' : ℕ, max 10 (Nat.ceil |s.im|) ≤ M' ∧
        eulerEtaTailBound (2 * M') M' s ≤ 3 / (2 : ℝ) ^ (M' / 2) ∧
        3 / (2 : ℝ) ^ (M' / 2) < ‖eulerEtaPartialSum (2 * M') M' s‖ := by
  set w : ℂ := 1 - conj s
  have hw_re : w.re = 1 - s.re := by simp [w]
  have hw_im : |w.im| = |s.im| := by simp [w]
  have hw0 : 0 < w.re := by linarith
  have hw1 : w.re < 1 := by linarith
  have hw_ne1 : w ≠ 1 := fun h => hw1.ne (by rw [h, Complex.one_re])
  have hM10 : 10 ≤ M := (le_max_left _ _).trans hM
  have him_w : |w.im| ≤ (M : ℝ) := by
    rw [hw_im]
    exact (Nat.le_ceil |s.im|).trans (by exact_mod_cast (le_max_right 10 _).trans hM)
  have hX2 : 2 ≤ X₀ := (le_max_left _ _).trans hX₀
  have hX2DM : 2 * D * M ≤ X₀ := (le_max_right _ _).trans hX₀
  have hζ_w : riemannZeta w ≠ 0 := by
    intro hz
    have hlow := (norm_multiStrideEuler_lowDivisors_le_of_zeta_eq_zero hw0 hw1.le hw_ne1 hz
      hM10 him_w hX2DM).2.2
    have hfl := norm_multiStrideEuler_squareEtaHead_refl_ge (List.range' 1 D) M hs0 hhi hX2
    set lowF : ℕ → ℂ := fun Y => ∑ d ∈ Finset.Icc 1 D,
      _root_.RHTower.liouvilleC d * (d : ℂ) ^ (-w) * dqptAltPartialSum w (Y / d)
    set highF : ℕ → ℂ := fun Y => ∑ d ∈ Finset.Icc (D + 1) Y,
      _root_.RHTower.liouvilleC d * (d : ℂ) ^ (-w) * dqptAltPartialSum w (Y / d)
    have hfun_split : ∀ Y : ℕ, D ≤ Y → squareEtaHead Y w = lowF Y + highF Y := by
      intro Y hDY
      rw [← sum_liouville_mul_dqptAltPartialSum_eq_squareEtaHead Y w]
      have hunion : Finset.Icc 1 Y = Finset.Icc 1 D ∪ Finset.Icc (D + 1) Y := by
        ext d; simp only [Finset.mem_Icc, Finset.mem_union]; omega
      have hdisj : Disjoint (Finset.Icc 1 D) (Finset.Icc (D + 1) Y) := by
        rw [Finset.disjoint_left]; intro d h1 h2; rw [Finset.mem_Icc] at h1 h2; omega
      rw [hunion, Finset.sum_union hdisj]
    have hDX₀ : D ≤ X₀ := by
      have hM1 : 1 ≤ M := by omega
      calc D = 1 * D * 1 := by ring
        _ ≤ 2 * D * M := Nat.mul_le_mul (Nat.mul_le_mul_right D (by norm_num)) hM1
        _ ≤ X₀ := hX2DM
    have heq_X₀ : multiStrideEuler (List.range' 1 D) M (fun Y => squareEtaHead Y w) X₀ =
        multiStrideEuler (List.range' 1 D) M lowF X₀ +
          multiStrideEuler (List.range' 1 D) M highF X₀ := by
      rw [multiStrideEuler_congr_of_window (List.range' 1 D) M
        (fun Y hYlo _ => hfun_split Y (hDX₀.trans hYlo))]
      exact congrFun (multiStrideEuler_add (List.range' 1 D) M lowF highF) X₀
    have htri := norm_add_le (multiStrideEuler (List.range' 1 D) M lowF X₀)
      (multiStrideEuler (List.range' 1 D) M highF X₀)
    rw [← heq_X₀] at htri
    linarith
  have hs_ne1 : s ≠ 1 := fun h => (by linarith : s.re < 1).ne (by rw [h, Complex.one_re])
  have hζ_s : riemannZeta s ≠ 0 := by
    intro hzs
    have hxi_s : _root_.RHTower.xi s = 0 := (_root_.RHTower.xi_eq_zero_iff hs0 hs_ne1).mpr hzs
    have hxi_w : _root_.RHTower.xi w = 0 := by
      rw [show w = 1 - conj s from rfl, _root_.RHTower.xi_one_sub, _root_.RHTower.xi_conj,
        hxi_s, map_zero]
    exact hζ_w ((_root_.RHTower.xi_eq_zero_iff hw0 hw_ne1).mp hxi_w)
  obtain ⟨M', hM', hbeat'⟩ :=
    (exists_linear_eulerEtaPartialSum_beats_tail_iff_zeta_ne_zero hs0 (by linarith)).1.mpr hζ_s
  have him' : |s.im| ≤ (M' : ℝ) :=
    (Nat.le_ceil |s.im|).trans (by exact_mod_cast (le_max_right 10 _).trans hM')
  exact ⟨hζ_w, hζ_s, M', hM',
    eulerEtaTailBound_two_mul_le_three_div_two_pow_half hs0 (by linarith)
      ((le_max_left _ _).trans hM') him', hbeat'⟩

/-- Finite Liouville Dirichlet polynomial `∑_{d=1}^N λ(d) d^{-w}`. -/
def liouvillePoly (N : ℕ) (w : ℂ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 N, _root_.RHTower.liouvilleC d * (d : ℂ) ^ (-w)

/-- **Exact dual hyperbola decomposition of the high-divisor Liouville zone (`d > D`):** for every
`Y, D : ℕ` and `w : ℂ`, reversing summation order rewrites the high-divisor sum `D < d ≤ Y` as a
short alternating sum over `1 ≤ m ≤ Y / (D + 1)` of incomplete Liouville Dirichlet blocks
`liouvillePoly (Y / m) w - liouvillePoly D w`. -/
theorem sum_highDivisors_liouville_altPartialSum_eq_dual (Y D : ℕ) (w : ℂ) :
    (∑ d ∈ Finset.Icc (D + 1) Y,
        _root_.RHTower.liouvilleC d * (d : ℂ) ^ (-w) * dqptAltPartialSum w (Y / d)) =
      ∑ m ∈ Finset.Icc 1 (Y / (D + 1)),
        (-1 : ℂ) ^ (m - 1) * (m : ℂ) ^ (-w) * (liouvillePoly (Y / m) w - liouvillePoly D w) := by
  have halt : ∀ K : ℕ, dqptAltPartialSum w K =
      ∑ m ∈ Finset.Icc 1 K, (-1 : ℂ) ^ (m - 1) * (m : ℂ) ^ (-w) := by
    intro K
    unfold dqptAltPartialSum dqptRp
    rw [← _root_.RHTower.sum_range_succ_eq_sum_Icc
      (fun m => (-1 : ℂ) ^ (m - 1) * (m : ℂ) ^ (-w)) K]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Nat.add_sub_cancel]
    congr 2; push_cast; ring
  simp_rw [halt]
  have hlhs : (∑ d ∈ Finset.Icc (D + 1) Y,
        _root_.RHTower.liouvilleC d * (d : ℂ) ^ (-w) *
          ∑ m ∈ Finset.Icc 1 (Y / d), (-1 : ℂ) ^ (m - 1) * (m : ℂ) ^ (-w)) =
      ∑ p ∈ (Finset.Icc (D + 1) Y).sigma (fun d => Finset.Icc 1 (Y / d)),
        _root_.RHTower.liouvilleC p.1 * (p.1 : ℂ) ^ (-w) *
          ((-1 : ℂ) ^ (p.2 - 1) * (p.2 : ℂ) ^ (-w)) := by
    rw [Finset.sum_sigma]
    exact Finset.sum_congr rfl fun d _ => Finset.mul_sum _ _ _
  have hblock : ∀ m ∈ Finset.Icc 1 (Y / (D + 1)),
      liouvillePoly (Y / m) w - liouvillePoly D w =
        ∑ d ∈ Finset.Icc (D + 1) (Y / m), _root_.RHTower.liouvilleC d * (d : ℂ) ^ (-w) := by
    intro m hm
    obtain ⟨hm1, hm_hi⟩ := Finset.mem_Icc.mp hm
    have hD_le : D ≤ Y / m := by
      have hmul : (D + 1) * m ≤ Y := by
        rw [mul_comm]; exact (Nat.le_div_iff_mul_le (by omega)).mp hm_hi
      have hDm : D * m ≤ Y := (Nat.mul_le_mul_right m (Nat.le_succ D)).trans hmul
      exact (Nat.le_div_iff_mul_le hm1).mpr hDm
    unfold liouvillePoly
    have hunion : Finset.Icc 1 (Y / m) = Finset.Icc 1 D ∪ Finset.Icc (D + 1) (Y / m) := by
      ext d; simp only [Finset.mem_Icc, Finset.mem_union]; omega
    have hdisj : Disjoint (Finset.Icc 1 D) (Finset.Icc (D + 1) (Y / m)) := by
      rw [Finset.disjoint_left]; intro d h1 h2; rw [Finset.mem_Icc] at h1 h2; omega
    rw [hunion, Finset.sum_union hdisj, add_sub_cancel_left]
  have hrhs_rw : (∑ m ∈ Finset.Icc 1 (Y / (D + 1)),
        (-1 : ℂ) ^ (m - 1) * (m : ℂ) ^ (-w) * (liouvillePoly (Y / m) w - liouvillePoly D w)) =
      ∑ m ∈ Finset.Icc 1 (Y / (D + 1)),
        (-1 : ℂ) ^ (m - 1) * (m : ℂ) ^ (-w) *
          ∑ d ∈ Finset.Icc (D + 1) (Y / m), _root_.RHTower.liouvilleC d * (d : ℂ) ^ (-w) :=
    Finset.sum_congr rfl fun m hm => by rw [hblock m hm]
  have hrhs : (∑ m ∈ Finset.Icc 1 (Y / (D + 1)),
        (-1 : ℂ) ^ (m - 1) * (m : ℂ) ^ (-w) *
          ∑ d ∈ Finset.Icc (D + 1) (Y / m), _root_.RHTower.liouvilleC d * (d : ℂ) ^ (-w)) =
      ∑ q ∈ (Finset.Icc 1 (Y / (D + 1))).sigma (fun m => Finset.Icc (D + 1) (Y / m)),
        (-1 : ℂ) ^ (q.1 - 1) * (q.1 : ℂ) ^ (-w) *
          (_root_.RHTower.liouvilleC q.2 * (q.2 : ℂ) ^ (-w)) := by
    rw [Finset.sum_sigma]
    exact Finset.sum_congr rfl fun m _ => Finset.mul_sum _ _ _
  rw [hlhs, hrhs_rw, hrhs]
  refine Finset.sum_bij (fun p _ => ⟨p.2, p.1⟩) ?_ ?_ ?_ ?_
  · rintro ⟨d, m⟩ hp
    obtain ⟨hd, hm⟩ := Finset.mem_sigma.mp hp
    obtain ⟨hd_lo, _⟩ := Finset.mem_Icc.mp hd
    obtain ⟨hm1, hm_hi⟩ := Finset.mem_Icc.mp hm
    change D + 1 ≤ d at hd_lo
    change 1 ≤ m at hm1
    change m ≤ Y / d at hm_hi
    have hdm : m * d ≤ Y := (Nat.le_div_iff_mul_le (by omega)).mp hm_hi
    have hm_top : m ≤ Y / (D + 1) :=
      (Nat.le_div_iff_mul_le (by omega)).mpr ((Nat.mul_le_mul_left m hd_lo).trans hdm)
    have hd_top : d ≤ Y / m :=
      (Nat.le_div_iff_mul_le hm1).mpr (by rwa [mul_comm])
    exact Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨hm1, hm_top⟩,
      Finset.mem_Icc.mpr ⟨hd_lo, hd_top⟩⟩
  · rintro ⟨d₁, m₁⟩ _ ⟨d₂, m₂⟩ _ heq
    injection heq with hm_eq hd_eq
    subst hm_eq; subst hd_eq; rfl
  · rintro ⟨m, d⟩ hq
    obtain ⟨hm, hd⟩ := Finset.mem_sigma.mp hq
    obtain ⟨hm1, _⟩ := Finset.mem_Icc.mp hm
    obtain ⟨hd_lo, hd_hi⟩ := Finset.mem_Icc.mp hd
    change 1 ≤ m at hm1
    change D + 1 ≤ d at hd_lo
    change d ≤ Y / m at hd_hi
    have hdm : d * m ≤ Y := (Nat.le_div_iff_mul_le hm1).mp hd_hi
    have hdY : d ≤ Y := by nlinarith
    have hm_div : m ≤ Y / d := (Nat.le_div_iff_mul_le (by omega)).mpr (by rwa [mul_comm])
    exact ⟨⟨d, m⟩, Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨hd_lo, hdY⟩,
      Finset.mem_Icc.mpr ⟨hm1, hm_div⟩⟩, rfl⟩
  · rintro ⟨d, m⟩ _
    change (-1 : ℂ) ^ (m - 1) * (m : ℂ) ^ (-w) * (_root_.RHTower.liouvilleC d * (d : ℂ) ^ (-w)) =
      _root_.RHTower.liouvilleC d * (d : ℂ) ^ (-w) * ((-1 : ℂ) ^ (m - 1) * (m : ℂ) ^ (-w))
    ring

/-- Exact Prime-Gas Liouville–Euler hyperbola defect separating `L_N(w) · E_{N, M}(w)` from
`squareEtaHead N w`. -/
def liouvilleEulerDefect (N M : ℕ) (w : ℂ) : ℂ :=
  liouvillePoly N w * eulerEtaPartialSum N M w - squareEtaHead N w

theorem liouvillePoly_mul_eulerEtaPartialSum_eq_head_add_defect (N M : ℕ) (w : ℂ) :
    liouvillePoly N w * eulerEtaPartialSum N M w =
      squareEtaHead N w + liouvilleEulerDefect N M w := by
  unfold liouvilleEulerDefect
  ring

theorem norm_liouvillePoly_le_of_nonneg_re {w : ℂ} (hw : 0 ≤ w.re) (N : ℕ) :
    ‖liouvillePoly N w‖ ≤ (N : ℝ) := by
  unfold liouvillePoly
  refine (norm_sum_le _ _).trans ?_
  calc ∑ d ∈ Finset.Icc 1 N, ‖_root_.RHTower.liouvilleC d * (d : ℂ) ^ (-w)‖
      ≤ ∑ _d ∈ Finset.Icc 1 N, (1 : ℝ) := by
        refine Finset.sum_le_sum fun d hd => ?_
        obtain ⟨hd1, _⟩ := Finset.mem_Icc.mp hd
        rw [norm_mul, show (d : ℂ) = ((d : ℝ) : ℂ) by norm_cast,
          Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hd1), Complex.neg_re]
        have h1 := _root_.RHTower.norm_liouvilleC_le_one d
        have h2 : (d : ℝ) ^ (-w.re) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hd1) (by linarith)
        nlinarith [norm_nonneg (_root_.RHTower.liouvilleC d),
          Real.rpow_nonneg (Nat.cast_nonneg d) (-w.re)]
    _ = (N : ℝ) := by simp

private lemma exists_abs_sourcePartialSum_liouvilleR_le_of_zeroFree
    {Θ : ℝ} (hΘ : (1 : ℝ) / 2 ≤ Θ) (hΘ1 : Θ ≤ 1)
    (hzf : ∀ z : ℂ, Θ < z.re → riemannZeta z ≠ 0) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      |_root_.RHTower.sourcePartialSum _root_.RHTower.liouvilleR N| ≤ C * (N : ℝ) ^ (Θ + δ) := by
  obtain ⟨CM, hCM0, hCM⟩ := _root_.RHTower.mobiusMertens_subpower_of_zeroFree hΘ hΘ1 hzf δ hδ
  set p : ℝ := Θ + δ
  have hp_pos : 0 < p := by linarith
  have hZs : Summable fun j : ℕ => 1 / (j : ℝ) ^ (2 * p) :=
    Real.summable_one_div_nat_rpow.2 (by linarith)
  set Z := ∑' j : ℕ, 1 / (j : ℝ) ^ (2 * p)
  have hZ0 : 0 ≤ Z := tsum_nonneg fun _ => by positivity
  refine ⟨CM * (2 : ℝ) ^ p * Z * (2 : ℝ) ^ p, by positivity, fun N => ?_⟩
  rcases Nat.eq_zero_or_pos N with rfl | hNpos
  · simp [_root_.RHTower.sourcePartialSum, Real.zero_rpow hp_pos.ne']
  · have hstep : |_root_.RHTower.sourcePartialSum _root_.RHTower.liouvilleR N| ≤
        CM * (2 : ℝ) ^ p * Z * ((N : ℝ) + 1) ^ p := by
      rw [_root_.RHTower.sourcePartialSum_liouvilleR_eq, _root_.RHTower.floorTransform]
      have hpt : ∀ d ∈ Finset.Icc 1 N,
          |_root_.RHTower.squareIndicatorR d *
              _root_.RHTower.sourcePartialSum _root_.RHTower.moebiusR (N / d)| ≤
            _root_.RHTower.squareIndicatorR d *
              (CM * (2 * ((N : ℝ) + 1)) ^ p * (1 / (d : ℝ) ^ p)) := by
        intro d hd
        obtain ⟨hd1, hdN⟩ := Finset.mem_Icc.1 hd
        have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
        have hsq : 0 ≤ _root_.RHTower.squareIndicatorR d := by
          unfold _root_.RHTower.squareIndicatorR; split_ifs <;> norm_num
        rw [abs_mul, abs_of_nonneg hsq]
        refine mul_le_mul_of_nonneg_left ?_ hsq
        rw [← _root_.RHTower.norm_mobiusMertensPartialSum_eq_abs_sourcePartialSum_moebiusR]
        refine (hCM (N / d)).trans ?_
        have hfl : ((N / d : ℕ) : ℝ) + 1 ≤ 2 * ((N : ℝ) + 1) / d := by
          have h1 : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / d := Nat.cast_div_le
          have h2 : (1 : ℝ) ≤ ((N : ℝ) + 1) / d := by
            rw [le_div_iff₀ hd0]
            have : (d : ℝ) ≤ N := by exact_mod_cast hdN
            linarith
          have h3 : (N : ℝ) / d ≤ ((N : ℝ) + 1) / d :=
            div_le_div_of_nonneg_right (by linarith) hd0.le
          rw [mul_div_assoc]
          linarith
        calc CM * (((N / d : ℕ) : ℝ) + 1) ^ p ≤ CM * (2 * ((N : ℝ) + 1) / d) ^ p :=
              mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hfl hp_pos.le) hCM0
          _ = CM * (2 * ((N : ℝ) + 1)) ^ p * (1 / (d : ℝ) ^ p) := by
              rw [Real.div_rpow (by positivity) hd0.le]; ring
      refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hpt).trans ?_)
      have hsum : ∑ i ∈ Finset.Icc 1 N, _root_.RHTower.squareIndicatorR i * (1 / (i : ℝ) ^ p) ≤ Z := by
        have e1 : ∑ i ∈ Finset.Icc 1 N, _root_.RHTower.squareIndicatorR i * (1 / (i : ℝ) ^ p) =
            ∑ i ∈ (Finset.Icc 1 N).filter IsSquare, 1 / (i : ℝ) ^ p := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun i _ => ?_
          unfold _root_.RHTower.squareIndicatorR; split_ifs <;> simp
        rw [e1]
        have hsub : (Finset.Icc 1 N).filter IsSquare ⊆ (Finset.Icc 1 N).image (fun j => j ^ 2) := by
          intro i hi
          obtain ⟨hi1, ⟨j, rfl⟩⟩ := Finset.mem_filter.1 hi
          obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hi1
          refine Finset.mem_image.2 ⟨j, Finset.mem_Icc.2 ⟨?_, ?_⟩, by ring⟩
          · rcases Nat.eq_zero_or_pos j with rfl | hj
            · simp at h1
            · exact hj
          · nlinarith
        refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity).trans ?_
        rw [Finset.sum_image fun _ _ _ _ h => Nat.pow_left_injective (by norm_num) h]
        have e2 : ∀ j ∈ Finset.Icc 1 N, 1 / (((j ^ 2 : ℕ) : ℝ)) ^ p = 1 / (j : ℝ) ^ (2 * p) := by
          intro j _
          rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg j)]
          norm_num
        rw [Finset.sum_congr rfl e2]
        exact hZs.sum_le_tsum _ fun _ _ => by positivity
      have e3 : ∑ i ∈ Finset.Icc 1 N, _root_.RHTower.squareIndicatorR i *
            (CM * (2 * ((N : ℝ) + 1)) ^ p * (1 / (i : ℝ) ^ p)) =
          CM * (2 * ((N : ℝ) + 1)) ^ p *
            ∑ i ∈ Finset.Icc 1 N, _root_.RHTower.squareIndicatorR i * (1 / (i : ℝ) ^ p) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
      rw [e3, Real.mul_rpow (by norm_num) (by positivity)]
      calc CM * ((2 : ℝ) ^ p * ((N : ℝ) + 1) ^ p) *
            ∑ i ∈ Finset.Icc 1 N, _root_.RHTower.squareIndicatorR i * (1 / (i : ℝ) ^ p)
          ≤ CM * ((2 : ℝ) ^ p * ((N : ℝ) + 1) ^ p) * Z :=
            mul_le_mul_of_nonneg_left hsum (by positivity)
        _ = CM * (2 : ℝ) ^ p * Z * ((N : ℝ) + 1) ^ p := by ring
    have hN1 : (N : ℝ) + 1 ≤ 2 * (N : ℝ) := by
      have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNpos
      linarith
    have hrpow : ((N : ℝ) + 1) ^ p ≤ (2 : ℝ) ^ p * (N : ℝ) ^ p :=
      (Real.rpow_le_rpow (by positivity) hN1 hp_pos.le).trans_eq
        (Real.mul_rpow zero_le_two (Nat.cast_nonneg N))
    calc |_root_.RHTower.sourcePartialSum _root_.RHTower.liouvilleR N|
        ≤ CM * (2 : ℝ) ^ p * Z * ((N : ℝ) + 1) ^ p := hstep
      _ ≤ CM * (2 : ℝ) ^ p * Z * ((2 : ℝ) ^ p * (N : ℝ) ^ p) :=
          mul_le_mul_of_nonneg_left hrpow (by positivity)
      _ = CM * (2 : ℝ) ^ p * Z * (2 : ℝ) ^ p * (N : ℝ) ^ p := by ring

private lemma differentiableOn_abelTailSeries_of_poly_bound {b : ℕ → ℝ} {C θ : ℝ}
    (hC : 0 ≤ C) (hθ : 0 ≤ θ) (hb : ∀ N : ℕ, |_root_.RHTower.sourcePartialSum b N| ≤ C * (N : ℝ) ^ θ) :
    DifferentiableOn ℂ (_root_.RHTower.abelTailSeries (_root_.RHTower.sourcePartialSum b))
      {z : ℂ | θ < z.re} := by
  intro z hz
  change θ < z.re at hz
  set σ₀ : ℝ := (z.re + θ) / 2
  set M : ℝ := ‖z‖ + 1
  have hσ₀_gt : θ < σ₀ := by dsimp [σ₀]; linarith
  have hσ₀_pos : 0 < σ₀ := lt_of_le_of_lt hθ hσ₀_gt
  set U : Set ℂ := {u : ℂ | σ₀ < u.re ∧ ‖u‖ < M}
  have hU : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_norm continuous_const)
  have hzU : z ∈ U := ⟨by dsimp [σ₀]; linarith, by dsimp [M]; linarith⟩
  have hdiff : ∀ k : ℕ, DifferentiableOn ℂ
      (fun u : ℂ => (_root_.RHTower.sourcePartialSum b (k + 1) : ℂ) *
        ((((k : ℝ) + 1 : ℝ) : ℂ) ^ (-u) - (((k : ℝ) + 2 : ℝ) : ℂ) ^ (-u))) U := by
    intro k u _
    have h1 : (((k : ℝ) + 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (show (k : ℝ) + 1 ≠ 0 by positivity)
    have h2 : (((k : ℝ) + 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (show (k : ℝ) + 2 ≠ 0 by positivity)
    exact ((differentiableAt_const _).mul
      ((differentiableAt_id.neg.const_cpow (Or.inl h1)).sub
        (differentiableAt_id.neg.const_cpow (Or.inl h2)))).differentiableWithinAt
  have hbound : ∀ k : ℕ, ∀ u ∈ U,
      ‖(_root_.RHTower.sourcePartialSum b (k + 1) : ℂ) *
          ((((k : ℝ) + 1 : ℝ) : ℂ) ^ (-u) - (((k : ℝ) + 2 : ℝ) : ℂ) ^ (-u))‖ ≤
        C * M * ((k : ℝ) + 1) ^ (θ - σ₀ - 1) := by
    intro k u hu
    have hu0 : 0 < u.re := lt_trans hσ₀_pos hu.1
    have hterm := _root_.RHTower.norm_abelTail_term_le hC hb hu0 k
    rw [_root_.RHTower.coeffPartial_ofReal] at hterm
    refine hterm.trans ?_
    have hrpow : ((k : ℝ) + 1) ^ (θ - u.re - 1) ≤ ((k : ℝ) + 1) ^ (θ - σ₀ - 1) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [Nat.cast_nonneg (α := ℝ) k]) (by linarith [hu.1])
    exact mul_le_mul (mul_le_mul_of_nonneg_left hu.2.le hC) hrpow
      (Real.rpow_nonneg (by positivity) _) (by positivity)
  have hDiffOn : DifferentiableOn ℂ (_root_.RHTower.abelTailSeries (_root_.RHTower.sourcePartialSum b)) U :=
    Complex.differentiableOn_tsum_of_summable_norm
      ((_root_.RHTower.summable_abelTail_majorant hσ₀_gt).mul_left (C * M)) hdiff hU hbound
  exact (hDiffOn.differentiableAt (hU.mem_nhds hzU)).differentiableWithinAt

private theorem tendsto_liouvillePoly_mul_zeta_of_zeroFree
    {Θ : ℝ} (hΘ : (1 : ℝ) / 2 ≤ Θ) (hΘ1 : Θ ≤ 1)
    (hzf : ∀ z : ℂ, Θ < z.re → riemannZeta z ≠ 0)
    {w : ℂ} (hw : Θ < w.re) (hw1 : w ≠ 1) :
    ∃ L : ℂ,
      Tendsto (fun N : ℕ => liouvillePoly N w) atTop (𝓝 L) ∧
      L * riemannZeta w = riemannZeta (2 * w) := by
  set δ : ℝ := min ((w.re - Θ) / 2) (1 / 4)
  have hδ : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδ_le1 : δ ≤ (w.re - Θ) / 2 := min_le_left _ _
  have hδ_le2 : δ ≤ 1 / 4 := min_le_right _ _
  set θ : ℝ := Θ + δ
  have hθ_lt : θ < w.re := by dsimp [θ]; linarith
  have hθ_gt_half : (1 : ℝ) / 2 < θ := by dsimp [θ]; linarith
  have hθ_le : θ ≤ 5 / 4 := by dsimp [θ]; linarith
  obtain ⟨C, hC0, hb⟩ := exists_abs_sourcePartialSum_liouvilleR_le_of_zeroFree hΘ hΘ1 hzf hδ
  set F : ℂ → ℂ := _root_.RHTower.abelTailSeries (_root_.RHTower.sourcePartialSum _root_.RHTower.liouvilleR)
  have hconv : Tendsto (fun N : ℕ => liouvillePoly N w) atTop (𝓝 (F w)) := by
    have hR := _root_.RHTower.summable_abelTail hC0 hb (by linarith : 0 < w.re) hθ_lt
    have hbd := _root_.RHTower.tendsto_abelTail_boundary hb hθ_lt
    have hRlim := hR.hasSum.tendsto_sum_nat.comp (tendsto_sub_atTop_nat 1)
    have hsum := hbd.add hRlim
    rw [zero_add] at hsum
    have heqF : (∑' k : ℕ, _root_.RHTower.coeffPartial
          (fun i => (_root_.RHTower.liouvilleR (i + 1) : ℂ)) (k + 1) *
            ((((k : ℝ) + 1 : ℝ) : ℂ) ^ (-w) - (((k : ℝ) + 2 : ℝ) : ℂ) ^ (-w))) = F w :=
      tsum_congr fun k => by rw [_root_.RHTower.coeffPartial_ofReal]
    rw [heqF] at hsum
    refine hsum.congr fun N => ?_
    dsimp only [Function.comp_apply]
    rw [← _root_.RHTower.sum_eq_abelPartial (fun i => (_root_.RHTower.liouvilleR (i + 1) : ℂ)) w N,
      _root_.RHTower.sum_range_succ_eq_sum_Icc
        (fun m => (((m : ℝ) : ℂ) ^ (-w) * (_root_.RHTower.liouvilleR m : ℂ))) N]
    unfold liouvillePoly
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [_root_.RHTower.liouvilleC_apply, _root_.RHTower.liouvilleR]
    push_cast
    ring
  refine ⟨F w, hconv, ?_⟩
  set U : Set ℂ := {z : ℂ | θ < z.re}
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hFa : AnalyticOnNhd ℂ (fun z => F z * _root_.RHTower.zetaResidueUnit z) U := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hUo
    exact ((differentiableOn_abelTailSeries_of_poly_bound hC0 (by linarith) hb z hz).mul
      (_root_.RHTower.analyticAt_zetaResidueUnit z).differentiableAt.differentiableWithinAt)
  have hGa : AnalyticOnNhd ℂ (fun z => (z - 1) * riemannZeta (2 * z)) U := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hUo
    have h2z_ne1 : 2 * z ≠ 1 := by
      intro h; have := congrArg Complex.re h; simp [Complex.mul_re] at this
      change θ < z.re at hz; linarith
    exact (((differentiableAt_id.sub (differentiableAt_const 1)).mul
      ((differentiableAt_riemannZeta h2z_ne1).comp z
        ((differentiableAt_const 2).mul differentiableAt_id)))).differentiableWithinAt
  have h2U : (2 : ℂ) ∈ U := by change θ < (2 : ℂ).re; simp; linarith
  have hev : (fun z => F z * _root_.RHTower.zetaResidueUnit z) =ᶠ[𝓝 (2 : ℂ)]
      (fun z => (z - 1) * riemannZeta (2 * z)) := by
    have hopen32 : IsOpen {z : ℂ | (3 / 2 : ℝ) < z.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen32.mem_nhds (by norm_num : (3 / 2 : ℝ) < (2 : ℂ).re)] with z hz32
    change (3 / 2 : ℝ) < z.re at hz32
    have hz1 : (1 : ℝ) < z.re := by linarith
    have hzne1 : z ≠ 1 := fun h => (ne_of_gt hz1) (by rw [h, Complex.one_re])
    have hlcast : (fun n : ℕ => (_root_.RHTower.liouvilleR n : ℂ)) =
        fun n : ℕ => _root_.RHTower.liouvilleC n := by
      funext n; rw [_root_.RHTower.liouvilleR, _root_.RHTower.liouvilleC_apply]; push_cast; rfl
    have hF_eq : F z = LSeries (fun n => _root_.RHTower.liouvilleC n) z := by
      have h := _root_.RHTower.abelTailSeries_sourcePartialSum hC0 hb (by linarith : 0 < z.re)
        (by linarith : θ < z.re)
        (hlcast.symm ▸ _root_.RHTower.LSeriesSummable_liouvilleC hz1)
      rwa [hlcast] at h
    rw [hF_eq, _root_.RHTower.zetaResidueUnit, Function.update_of_ne hzne1]
    linear_combination (z - 1) * _root_.RHTower.LSeries_liouvilleC_mul_riemannZeta hz1
  have hEq := hFa.eqOn_of_preconnected_of_eventuallyEq hGa
    (convex_halfSpace_re_gt θ).isPreconnected h2U hev
  have hwU : w ∈ U := hθ_lt
  have hval := hEq hwU
  dsimp only at hval
  rw [_root_.RHTower.zetaResidueUnit, Function.update_of_ne hw1] at hval
  have hw_sub : w - 1 ≠ 0 := sub_ne_zero.mpr hw1
  exact mul_left_cancel₀ hw_sub (by linear_combination hval)

/-- **Zero-abscissa convergence of `liouvilleEulerDefect` across all heights:** right of any
zero-free frontier `Θ ∈ [1/2, 1]`, at every `0 < Re s < 1 - Θ` and every `Im s ∈ ℝ`,
`liouvilleEulerDefect (2 * M) M (1 - conj s) → 0` as `M → ∞`. -/
theorem tendsto_liouvilleEulerDefect_zero_of_zeroFree
    {Θ : ℝ} (hΘ : (1 : ℝ) / 2 ≤ Θ) (hΘ1 : Θ ≤ 1)
    (hzf : ∀ z : ℂ, Θ < z.re → riemannZeta z ≠ 0)
    {s : ℂ} (hs0 : 0 < s.re) (hsΘ : s.re < 1 - Θ) :
    Tendsto (fun M : ℕ => liouvilleEulerDefect (2 * M) M (1 - conj s)) atTop (𝓝 0) := by
  set w : ℂ := 1 - conj s
  have hw_re : w.re = 1 - s.re := by simp [w]
  have hwΘ : Θ < w.re := by linarith
  have hw0 : 0 < w.re := by linarith
  have hw1 : w.re < 1 := by linarith
  have hw_ne1 : w ≠ 1 := fun h => hw1.ne (by rw [h, Complex.one_re])
  have hhi : s.re < 1 / 2 := by linarith
  obtain ⟨L, hL_conv, hL_zeta⟩ := tendsto_liouvillePoly_mul_zeta_of_zeroFree hΘ hΘ1 hzf hwΘ hw_ne1
  have h2M : Tendsto (fun M : ℕ => 2 * M) atTop atTop :=
    tendsto_atTop_mono (fun M => by omega : ∀ M : ℕ, M ≤ 2 * M) tendsto_id
  have hpoly : Tendsto (fun M : ℕ => liouvillePoly (2 * M) w) atTop (𝓝 L) :=
    hL_conv.comp h2M
  have heuler : Tendsto (fun M : ℕ => eulerEtaPartialSum (2 * M) M w) atTop
      (𝓝 ((1 - (2 : ℂ) ^ (1 - w)) * riemannZeta w)) := by
    have hmaj : Tendsto (fun M : ℕ => 3 / (2 : ℝ) ^ (M / 2)) atTop (𝓝 0) := by
      have hdiv2 : Tendsto (fun M : ℕ => M / 2) atTop atTop :=
        tendsto_atTop.mpr fun B => eventually_atTop.mpr ⟨2 * B, fun M hM => by omega⟩
      have hpow0 : Tendsto (fun k : ℕ => ((2 : ℝ)⁻¹) ^ k) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num)
      have h3 := (hpow0.comp hdiv2).const_mul (3 : ℝ)
      rw [mul_zero] at h3
      refine h3.congr fun M => ?_
      dsimp only [Function.comp_apply]
      rw [inv_pow, div_eq_mul_inv]
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hmaj
    filter_upwards [eventually_ge_atTop (max 10 (Nat.ceil |w.im|))] with M hM
    have hM10 : 10 ≤ M := (le_max_left _ _).trans hM
    have him : |w.im| ≤ (M : ℝ) :=
      (Nat.le_ceil |w.im|).trans (by exact_mod_cast (le_max_right 10 _).trans hM)
    rw [norm_sub_rev]
    exact (norm_eta_sub_eulerEtaPartialSum_le hw0 hw_ne1 (2 * M) M (by omega)).trans
      (eulerEtaTailBound_two_mul_le_three_div_two_pow_half hw0 hw1.le hM10 him)
  have hhead : Tendsto (fun M : ℕ => squareEtaHead (2 * M) w) atTop
      (𝓝 ((1 - (2 : ℂ) ^ (1 - w)) * riemannZeta (2 * w))) :=
    (tendsto_squareEtaHead_refl hs0 hhi).comp h2M
  have hprod_eq : L * ((1 - (2 : ℂ) ^ (1 - w)) * riemannZeta w) -
      (1 - (2 : ℂ) ^ (1 - w)) * riemannZeta (2 * w) = 0 := by
    linear_combination (1 - (2 : ℂ) ^ (1 - w)) * hL_zeta
  rw [← hprod_eq]
  exact (hpoly.mul heuler).sub hhead

/-- **Unconditional sub-`3001/24000` defect vanishing across all heights:** on the proven left
zero-free strip `0 < Re s < 3001 / 24000`, `liouvilleEulerDefect (2 * M) M (1 - conj s) → 0`
unconditionally for every `Im s ∈ ℝ`. -/
theorem tendsto_liouvilleEulerDefect_zero_of_re_lt_sub_one_eighth
    {s : ℂ} (hs0 : 0 < s.re) (hs_lt : s.re < 3001 / 24000) :
    Tendsto (fun M : ℕ => liouvilleEulerDefect (2 * M) M (1 - conj s)) atTop (𝓝 0) :=
  tendsto_liouvilleEulerDefect_zero_of_zeroFree (Θ := 20999 / 24000) (by norm_num) (by norm_num)
    (fun _z hz => MetaplecticMobiusDescent.CubicEisenstein.riemannZeta_ne_zero_of_sub_seven_eighths_lt_re hz)
    hs0 (by linarith)

private lemma tendsto_six_mul_two_inv_pow_div_two :
    Tendsto (fun M : ℕ => 6 * (M : ℝ) * ((2 : ℝ)⁻¹) ^ (M / 2)) atTop (𝓝 0) := by
  have hgeom : Tendsto (fun k : ℕ => (12 : ℝ) * ((k : ℝ) + 1) * ((2 : ℝ)⁻¹) ^ k) atTop (𝓝 0) := by
    have h1 := summable_pow_mul_geometric_of_norm_lt_one 1
      (by norm_num : ‖(2 : ℝ)⁻¹‖ < 1) |>.tendsto_atTop_zero
    have h0 := summable_geometric_of_lt_one (by positivity)
      (by norm_num : (2 : ℝ)⁻¹ < 1) |>.tendsto_atTop_zero
    have hlin := (h1.add h0).const_mul (12 : ℝ)
    rw [add_zero, mul_zero] at hlin
    exact hlin.congr fun k => by rw [pow_one]; ring
  have hdiv2 : Tendsto (fun M : ℕ => M / 2) atTop atTop :=
    tendsto_atTop.mpr fun B => eventually_atTop.mpr ⟨2 * B, fun M hM => by omega⟩
  refine squeeze_zero (fun M => by positivity) (fun M => ?_) (hgeom.comp hdiv2)
  dsimp only [Function.comp_apply]
  have hM_le : (M : ℝ) ≤ 2 * ((M / 2 : ℕ) : ℝ) + 2 := by
    have : M ≤ 2 * (M / 2) + 1 := by omega
    have hR : (M : ℝ) ≤ ((2 * (M / 2) + 1 : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at hR
    linarith
  exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)

/-- **Zero-point defect locking law across all heights:** at any hypothetical zero `ζ(s) = 0`
(`0 < Re s < 1/2`), `liouvilleEulerDefect (2 * M) M (1 - conj s)` converges to
`-(1 - 2^{conj s}) ζ(2 - 2 conj s) ≠ 0`, whose modulus is at least `reflectedDoubleEtaFloor s.re > 0`. -/
theorem tendsto_liouvilleEulerDefect_of_zeta_eq_zero
    {s : ℂ} (hs0 : 0 < s.re) (hhi : s.re < 1 / 2) (hz : riemannZeta s = 0) :
    Tendsto (fun M : ℕ => liouvilleEulerDefect (2 * M) M (1 - conj s)) atTop
      (𝓝 (-((1 - (2 : ℂ) ^ (1 - (1 - conj s))) * riemannZeta (2 * (1 - conj s))))) ∧
    reflectedDoubleEtaFloor s.re ≤
      ‖-((1 - (2 : ℂ) ^ (1 - (1 - conj s))) * riemannZeta (2 * (1 - conj s)))‖ := by
  set w : ℂ := 1 - conj s
  have hw_re : w.re = 1 - s.re := by simp [w]
  have hw0 : 0 < w.re := by linarith
  have hw1 : w.re < 1 := by linarith
  have hs_ne1 : s ≠ 1 := fun h => (by linarith : s.re < 1).ne (by rw [h, Complex.one_re])
  have hw_ne1 : w ≠ 1 := fun h => hw1.ne (by rw [h, Complex.one_re])
  have hζ_w : riemannZeta w = 0 := by
    have hxi_s : _root_.RHTower.xi s = 0 := (_root_.RHTower.xi_eq_zero_iff hs0 hs_ne1).mpr hz
    have hxi_w : _root_.RHTower.xi w = 0 := by
      rw [show w = 1 - conj s from rfl, _root_.RHTower.xi_one_sub, _root_.RHTower.xi_conj,
        hxi_s, map_zero]
    exact (_root_.RHTower.xi_eq_zero_iff hw0 hw_ne1).mp hxi_w
  have hprod0 : Tendsto (fun M : ℕ => liouvillePoly (2 * M) w * eulerEtaPartialSum (2 * M) M w)
      atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ tendsto_six_mul_two_inv_pow_div_two
    filter_upwards [eventually_ge_atTop (max 10 (Nat.ceil |w.im|))] with M hM
    have hM10 : 10 ≤ M := (le_max_left _ _).trans hM
    have him : |w.im| ≤ (M : ℝ) :=
      (Nat.le_ceil |w.im|).trans (by exact_mod_cast (le_max_right 10 _).trans hM)
    rw [norm_mul]
    have hL := norm_liouvillePoly_le_of_nonneg_re hw0.le (2 * M)
    have hE := ((norm_eulerEtaPartialSum_le_tail_of_zeta_eq_zero hw0 hw_ne1 hζ_w).1 (2 * M) M
      (by omega)).trans (eulerEtaTailBound_two_mul_le_three_div_two_pow_half hw0 hw1.le hM10 him)
    calc ‖liouvillePoly (2 * M) w‖ * ‖eulerEtaPartialSum (2 * M) M w‖
        ≤ ((2 * M : ℕ) : ℝ) * (3 / (2 : ℝ) ^ (M / 2)) :=
          mul_le_mul hL hE (norm_nonneg _) (by positivity)
      _ = 6 * (M : ℝ) * ((2 : ℝ)⁻¹) ^ (M / 2) := by
          push_cast
          rw [inv_pow, div_eq_mul_inv]
          ring
  have h2M : Tendsto (fun M : ℕ => 2 * M) atTop atTop :=
    tendsto_atTop_mono (fun M => by omega : ∀ M : ℕ, M ≤ 2 * M) tendsto_id
  have hhead := (tendsto_squareEtaHead_refl hs0 hhi).comp h2M
  have hsub := hprod0.sub hhead
  rw [zero_sub] at hsub
  exact ⟨hsub, by rw [norm_neg]; exact (norm_eta_two_mul_refl_ge hs0 hhi).2⟩

/-- **Single-order defect sufficiency:** at any `0 < Re s < 1/2` and any `M ≥ 1`, if
`‖liouvilleEulerDefect (2 * M) M (1 - conj s)‖ + ‖liouvillePoly (2 * M) (1 - conj s)‖ · eulerEtaTailBound (2 * M) M (1 - conj s)`
is strictly below `‖squareEtaHead (2 * M) (1 - conj s)‖`, then **at that exact same order `M`**,
`eulerEtaPartialSum (2 * M) M (1 - conj s)` strictly beats `eulerEtaTailBound (2 * M) M (1 - conj s)`,
hence `ζ(1 - conj s) ≠ 0` and `ζ(s) ≠ 0`. -/
theorem eulerEtaPartialSum_beats_tail_of_liouvilleEulerDefect_lt
    {s : ℂ} (hs0 : 0 < s.re) (hhi : s.re < 1 / 2) {M : ℕ} (hM : 1 ≤ M)
    (hdef : ‖liouvilleEulerDefect (2 * M) M (1 - conj s)‖ +
        ‖liouvillePoly (2 * M) (1 - conj s)‖ * eulerEtaTailBound (2 * M) M (1 - conj s) <
      ‖squareEtaHead (2 * M) (1 - conj s)‖) :
    eulerEtaTailBound (2 * M) M (1 - conj s) < ‖eulerEtaPartialSum (2 * M) M (1 - conj s)‖ ∧
    riemannZeta (1 - conj s) ≠ 0 ∧ riemannZeta s ≠ 0 := by
  set w : ℂ := 1 - conj s
  have hw0 : 0 < w.re := by simp [w]; linarith
  have hw1 : w.re < 1 := by simp [w]; linarith
  have hw_ne1 : w ≠ 1 := fun h => hw1.ne (by rw [h, Complex.one_re])
  have hs_ne1 : s ≠ 1 := fun h => (by linarith : s.re < 1).ne (by rw [h, Complex.one_re])
  have htri : ‖squareEtaHead (2 * M) w‖ ≤
      ‖liouvillePoly (2 * M) w‖ * ‖eulerEtaPartialSum (2 * M) M w‖ +
        ‖liouvilleEulerDefect (2 * M) M w‖ := by
    have hid : squareEtaHead (2 * M) w =
        liouvillePoly (2 * M) w * eulerEtaPartialSum (2 * M) M w -
          liouvilleEulerDefect (2 * M) M w := by
      unfold liouvilleEulerDefect; ring
    conv_lhs => rw [hid]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul]
  have hprod_gt : ‖liouvillePoly (2 * M) w‖ * eulerEtaTailBound (2 * M) M w <
      ‖liouvillePoly (2 * M) w‖ * ‖eulerEtaPartialSum (2 * M) M w‖ := by
    linarith
  have hL_pos : 0 < ‖liouvillePoly (2 * M) w‖ := by
    by_contra hle
    have hL0 : ‖liouvillePoly (2 * M) w‖ = 0 :=
      le_antisymm (not_lt.mp hle) (norm_nonneg _)
    rw [hL0, zero_mul, zero_mul] at hprod_gt
    exact lt_irrefl 0 hprod_gt
  have hbeat : eulerEtaTailBound (2 * M) M w < ‖eulerEtaPartialSum (2 * M) M w‖ :=
    lt_of_mul_lt_mul_left hprod_gt hL_pos.le
  have hζ_w := (zeta_ne_zero_of_eulerEtaPartialSum_beats_tail hw0 hw_ne1 hM hbeat).2
  have hζ_s : riemannZeta s ≠ 0 := by
    intro hzs
    have hxi_s : _root_.RHTower.xi s = 0 := (_root_.RHTower.xi_eq_zero_iff hs0 hs_ne1).mpr hzs
    have hxi_w : _root_.RHTower.xi w = 0 := by
      rw [show w = 1 - conj s from rfl, _root_.RHTower.xi_one_sub, _root_.RHTower.xi_conj,
        hxi_s, map_zero]
    exact hζ_w ((_root_.RHTower.xi_eq_zero_iff hw0 hw_ne1).mp hxi_w)
  exact ⟨hbeat, hζ_w, hζ_s⟩

/-- **All-height `RiemannHypothesis` equivalence with the Prime-Gas Liouville–Euler defect above
height `184`:** `RiemannHypothesis` holds if and only if at every remaining strip point
`3001 / 24000 ≤ Re s < 1 / 2`, `184 < |Im s|`, `liouvilleEulerDefect (2 * M) M (1 - conj s) → 0`
as `M → ∞` (and equivalently, at each such point some `M ≥ ⌈|Im s|⌉₊` beats the positive
square-sieve head `squareEtaHead (2 * M) (1 - conj s)`). -/
theorem rh_iff_liouvilleEulerDefect_above_oneHundredEightyFour :
    (RiemannHypothesis ↔
      ∀ s : ℂ, 3001 / 24000 ≤ s.re → s.re < 1 / 2 → 184 < |s.im| →
        Tendsto (fun M : ℕ => liouvilleEulerDefect (2 * M) M (1 - conj s)) atTop (𝓝 0)) ∧
    (RiemannHypothesis ↔
      ∀ s : ℂ, 3001 / 24000 ≤ s.re → s.re < 1 / 2 → 184 < |s.im| →
        ∃ M : ℕ, Nat.ceil |s.im| ≤ M ∧
          ‖liouvilleEulerDefect (2 * M) M (1 - conj s)‖ +
              ‖liouvillePoly (2 * M) (1 - conj s)‖ *
                eulerEtaTailBound (2 * M) M (1 - conj s) <
            ‖squareEtaHead (2 * M) (1 - conj s)‖) := by
  have hrh_base := rh_iff_linear_euler_signedPartialSum_above_oneHundredEightyFour.2
  have h1 : RiemannHypothesis ↔
      ∀ s : ℂ, 3001 / 24000 ≤ s.re → s.re < 1 / 2 → 184 < |s.im| →
        Tendsto (fun M : ℕ => liouvilleEulerDefect (2 * M) M (1 - conj s)) atTop (𝓝 0) := by
    constructor
    · intro hRH s hlo hhi _
      have hzf : ∀ z : ℂ, (1 : ℝ) / 2 < z.re → riemannZeta z ≠ 0 := by
        intro z hz
        rcases lt_or_ge z.re 1 with hz1 | hz1
        · exact _root_.RHTower.riemannHypothesis_iff_riemannZeta_ne_zero_of_mem_upper_strip.mp hRH z hz hz1
        · exact riemannZeta_ne_zero_of_one_le_re hz1
      exact tendsto_liouvilleEulerDefect_zero_of_zeroFree le_rfl (by norm_num) hzf
        (by linarith) (by linarith)
    · intro hall
      rw [hrh_base]
      intro s hlo hhi him
      have hs0 : 0 < s.re := by linarith
      have hs1 : s.re < 1 := by linarith
      have hceil185 : 185 ≤ Nat.ceil |s.im| := by
        have : 184 < Nat.ceil |s.im| := (Nat.lt_ceil).mpr (by exact_mod_cast him)
        omega
      have hζ_ne : riemannZeta s ≠ 0 := by
        intro hz
        have hzero_lim := (tendsto_liouvilleEulerDefect_of_zeta_eq_zero hs0 hhi hz).1
        have hfl_ge := (tendsto_liouvilleEulerDefect_of_zeta_eq_zero hs0 hhi hz).2
        have hfl_pos := (norm_eta_two_mul_refl_ge hs0 hhi).1
        have heq0 := tendsto_nhds_unique hzero_lim (hall s hlo hhi him)
        rw [heq0, norm_zero] at hfl_ge
        linarith
      have hres := (exists_linear_eulerEtaPartialSum_beats_tail_iff_zeta_ne_zero hs0 hs1).2.mpr hζ_ne
      rwa [max_eq_right (by omega : 1 ≤ Nat.ceil |s.im|)] at hres
  have h2 : RiemannHypothesis ↔
      ∀ s : ℂ, 3001 / 24000 ≤ s.re → s.re < 1 / 2 → 184 < |s.im| →
        ∃ M : ℕ, Nat.ceil |s.im| ≤ M ∧
          ‖liouvilleEulerDefect (2 * M) M (1 - conj s)‖ +
              ‖liouvillePoly (2 * M) (1 - conj s)‖ *
                eulerEtaTailBound (2 * M) M (1 - conj s) <
            ‖squareEtaHead (2 * M) (1 - conj s)‖ := by
    constructor
    · intro hRH s hlo hhi him
      have hs0 : 0 < s.re := by linarith
      set w : ℂ := 1 - conj s
      have hw0 : 0 < w.re := by simp [w]; linarith
      have hw1 : w.re < 1 := by simp [w]; linarith
      have hw_im : |w.im| = |s.im| := by simp [w]
      have hdef0 : Tendsto (fun M : ℕ => ‖liouvilleEulerDefect (2 * M) M w‖) atTop (𝓝 0) := by
        simpa only [norm_zero] using (h1.mp hRH s hlo hhi him).norm
      have htail0 : Tendsto (fun M : ℕ => ‖liouvillePoly (2 * M) w‖ *
          eulerEtaTailBound (2 * M) M w) atTop (𝓝 0) := by
        refine squeeze_zero' (Eventually.of_forall fun _ => mul_nonneg (norm_nonneg _)
          (mul_nonneg (mul_nonneg (by positivity) (Finset.prod_nonneg fun _ _ => norm_nonneg _))
            (Real.rpow_nonneg (by positivity) _))) ?_ tendsto_six_mul_two_inv_pow_div_two
        filter_upwards [eventually_ge_atTop (max 10 (Nat.ceil |w.im|))] with M hM
        have hM10 : 10 ≤ M := (le_max_left _ _).trans hM
        have him_le : |w.im| ≤ (M : ℝ) :=
          (Nat.le_ceil |w.im|).trans (by exact_mod_cast (le_max_right 10 _).trans hM)
        calc ‖liouvillePoly (2 * M) w‖ * eulerEtaTailBound (2 * M) M w
            ≤ ((2 * M : ℕ) : ℝ) * (3 / (2 : ℝ) ^ (M / 2)) :=
              mul_le_mul (norm_liouvillePoly_le_of_nonneg_re hw0.le (2 * M))
                (eulerEtaTailBound_two_mul_le_three_div_two_pow_half hw0 hw1.le hM10 him_le)
                (mul_nonneg (mul_nonneg (by positivity) (Finset.prod_nonneg fun _ _ => norm_nonneg _))
                  (Real.rpow_nonneg (by positivity) _))
                (Nat.cast_nonneg _)
          _ = 6 * (M : ℝ) * ((2 : ℝ)⁻¹) ^ (M / 2) := by
              push_cast; rw [inv_pow, div_eq_mul_inv]; ring
      have hlhs0 : Tendsto (fun M : ℕ => ‖liouvilleEulerDefect (2 * M) M w‖ +
          ‖liouvillePoly (2 * M) w‖ * eulerEtaTailBound (2 * M) M w) atTop (𝓝 0) := by
        simpa only [add_zero] using hdef0.add htail0
      have h2M : Tendsto (fun M : ℕ => 2 * M) atTop atTop :=
        tendsto_atTop_mono (fun M => by omega : ∀ M : ℕ, M ≤ 2 * M) tendsto_id
      have hrhs_lim := ((tendsto_squareEtaHead_refl hs0 hhi).comp h2M).norm
      obtain ⟨hfl_pos, hfl_le⟩ := norm_eta_two_mul_refl_ge hs0 hhi
      have hev1 := hlhs0.eventually (Iio_mem_nhds (half_pos hfl_pos))
      have hev2 := hrhs_lim.eventually (Ioi_mem_nhds (lt_of_lt_of_le (half_lt_self hfl_pos) hfl_le))
      obtain ⟨M, ⟨hM_ge, hlt1⟩, hgt2⟩ :=
        ((eventually_ge_atTop (Nat.ceil |s.im|)).and hev1 |>.and hev2).exists
      exact ⟨M, hM_ge, lt_trans hlt1 hgt2⟩
    · intro hall
      rw [hrh_base]
      intro s hlo hhi him
      have hs0 : 0 < s.re := by linarith
      have hs1 : s.re < 1 := by linarith
      have hceil185 : 185 ≤ Nat.ceil |s.im| := by
        have : 184 < Nat.ceil |s.im| := (Nat.lt_ceil).mpr (by exact_mod_cast him)
        omega
      obtain ⟨M, hM_ge, hdef⟩ := hall s hlo hhi him
      have hζ_ne := (eulerEtaPartialSum_beats_tail_of_liouvilleEulerDefect_lt hs0 hhi
        (by omega : 1 ≤ M) hdef).2.2
      have hres := (exists_linear_eulerEtaPartialSum_beats_tail_iff_zeta_ne_zero hs0 hs1).2.mpr hζ_ne
      rwa [max_eq_right (by omega : 1 ≤ Nat.ceil |s.im|)] at hres
  exact ⟨h1, h2⟩

/-! ### 5. Planted Quartet Euler-3 Obstruction to Purely Additive Acceleration -/

/-- Real quartet-symmetric Euler-3 deformation factor planting zeros at the full functional-equation
quartet `{s₀, conj s₀, 1 - s₀, 1 - conj s₀}` while keeping Dirichlet support on powers of `3`. -/
def plantedQuartetPoly (s₀ s : ℂ) : ℂ :=
  (1 - (3 : ℂ) ^ (s₀ - s)) * (1 - (3 : ℂ) ^ (conj s₀ - s)) *
    (1 - (3 : ℂ) ^ (1 - s₀ - s)) * (1 - (3 : ℂ) ^ (1 - conj s₀ - s))

/-- Euler–Knopp partial sum of the planted quartet Euler-3 deformation `Q_{s₀}(s) · η(s)`. -/
def plantedQuartetEulerSum (s₀ : ℂ) (N M : ℕ) (s : ℂ) : ℂ :=
  plantedQuartetPoly s₀ s * eulerEtaPartialSum N M s

/-- Explicit `ζ`-free Euler–Knopp remainder majorant for `plantedQuartetEulerSum s₀ N M s`. -/
def plantedQuartetTailBound (s₀ : ℂ) (N M : ℕ) (s : ℂ) : ℝ :=
  ‖plantedQuartetPoly s₀ s‖ * eulerEtaTailBound N M s

/-- **Planted quartet Euler-3 obstruction (`plantedQuartetEuler3_obstruction`):** for any
`s₀ : ℂ` (`0 < Re s₀ < 1 / 2`), `plantedQuartetPoly s₀` is conjugate-symmetric (`Q(conj s) = conj(Q(s))`),
satisfies the exact `O_{s₀}(2^{-M/2})` Euler–Knopp error bound everywhere on `Re s > 0` (`s ≠ 1`),
and yet at **all four quartet points** `z ∈ {s₀, conj s₀, 1 - s₀, 1 - conj s₀}` **no order `(N, M)`
(`M ≥ 1`) ever beats `plantedQuartetTailBound s₀ N M z`** — whereas the Prime-Gas reflected
square-sieve limit `Q_{s₀}(1 - conj s₀) · (1 - 2^{conj s₀}) ζ(2 - 2 conj s₀)` vanishes identically,
exposing the planted prime-3 zero by violating `reflectedDoubleEtaFloor s₀.re > 0`. -/
theorem plantedQuartetEuler3_obstruction {s₀ : ℂ} (hs₀0 : 0 < s₀.re) (hs₀_hi : s₀.re < 1 / 2) :
    (∀ s : ℂ, plantedQuartetPoly s₀ (conj s) = conj (plantedQuartetPoly s₀ s)) ∧
    (∀ s : ℂ, 0 < s.re → s ≠ 1 → ∀ N M : ℕ, 1 ≤ M →
      ‖plantedQuartetPoly s₀ s * ((1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s) -
          plantedQuartetEulerSum s₀ N M s‖ ≤
        plantedQuartetTailBound s₀ N M s) ∧
    (∀ z ∈ ({s₀, conj s₀, 1 - s₀, 1 - conj s₀} : Set ℂ),
      plantedQuartetPoly s₀ z = 0 ∧
      ∀ N M : ℕ, 1 ≤ M → ¬ (plantedQuartetTailBound s₀ N M z < ‖plantedQuartetEulerSum s₀ N M z‖)) ∧
    (plantedQuartetPoly s₀ (1 - conj s₀) *
        ((1 - (2 : ℂ) ^ (1 - (1 - conj s₀))) * riemannZeta (2 * (1 - conj s₀))) = 0 ∧
      0 < reflectedDoubleEtaFloor s₀.re) := by
  have hcpow3_conj : ∀ w : ℂ, (3 : ℂ) ^ (conj w) = conj ((3 : ℂ) ^ w) := fun w => by
    have hpos : (0 : ℝ) < 3 := by norm_num
    rw [show (3 : ℂ) = ((3 : ℝ) : ℂ) by norm_num,
      Complex.cpow_def_of_ne_zero (by norm_num), Complex.cpow_def_of_ne_zero (by norm_num),
      ← Complex.ofReal_log hpos.le, ← Complex.exp_conj, map_mul, Complex.conj_ofReal]
  have hconj : ∀ s : ℂ, plantedQuartetPoly s₀ (conj s) = conj (plantedQuartetPoly s₀ s) := by
    intro s
    unfold plantedQuartetPoly
    simp only [map_mul, map_sub, map_one, ← hcpow3_conj, Complex.conj_conj]
    have e1 : s₀ - conj s = conj (conj s₀ - s) := by simp
    have e2 : conj s₀ - conj s = conj (s₀ - s) := by simp
    have e3 : 1 - s₀ - conj s = conj (1 - conj s₀ - s) := by simp
    have e4 : 1 - conj s₀ - conj s = conj (1 - s₀ - s) := by simp
    rw [e1, e2, e3, e4]
    ring
  have hrem : ∀ s : ℂ, 0 < s.re → s ≠ 1 → ∀ N M : ℕ, 1 ≤ M →
      ‖plantedQuartetPoly s₀ s * ((1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s) -
          plantedQuartetEulerSum s₀ N M s‖ ≤
        plantedQuartetTailBound s₀ N M s := by
    intro s hs0 hs1 N M hM
    unfold plantedQuartetEulerSum plantedQuartetTailBound
    rw [← mul_sub, norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_eta_sub_eulerEtaPartialSum_le hs0 hs1 N M hM)
      (norm_nonneg _)
  have hvan : ∀ z ∈ ({s₀, conj s₀, 1 - s₀, 1 - conj s₀} : Set ℂ),
      plantedQuartetPoly s₀ z = 0 ∧
      ∀ N M : ℕ, 1 ≤ M → ¬ (plantedQuartetTailBound s₀ N M z < ‖plantedQuartetEulerSum s₀ N M z‖) := by
    intro z hz
    have hQz : plantedQuartetPoly s₀ z = 0 := by
      unfold plantedQuartetPoly
      rcases hz with rfl | rfl | rfl | rfl
      · simp
      · simp
      · simp
      · simp
    refine ⟨hQz, fun N M _ => ?_⟩
    unfold plantedQuartetTailBound plantedQuartetEulerSum
    rw [hQz, norm_zero, zero_mul, zero_mul, norm_zero]
    exact lt_irrefl 0
  have hQ_refl : plantedQuartetPoly s₀ (1 - conj s₀) = 0 := by
    unfold plantedQuartetPoly; simp
  exact ⟨hconj, hrem, hvan, ⟨by rw [hQ_refl, zero_mul], (norm_eta_two_mul_refl_ge hs₀0 hs₀_hi).1⟩⟩

#print axioms eulerEtaPartialSum_succ_order
#print axioms eulerEtaPartialSum_add_one_sub
#print axioms eulerEtaPartialSum_succ_order_sub
#print axioms norm_eulerEtaPartialSum_add_leading_le_of_zeta_eq_zero
#print axioms eulerEtaTailBound_antitone_cutoff
#print axioms norm_eulerEtaPartialSum_lt_tail_of_sub_nyquist
#print axioms odd_div_sub_div_forall_iff
#print axioms no_single_stride_flips_one_and_two
#print axioms strideAvg_comm
#print axioms iterate_strideAvg_altPartialSum_div_eq_eulerEtaPartialSum
#print axioms norm_multiStrideEuler_sub_const_le_of_window
#print axioms norm_multiStrideEuler_lowDivisors_le_of_zeta_eq_zero
#print axioms sum_liouville_mul_dqptAltPartialSum_eq_squareEtaHead
#print axioms norm_eta_two_mul_refl_ge
#print axioms norm_squareEtaHead_refl_sub_le
#print axioms norm_multiStrideEuler_squareEtaHead_refl_ge
#print axioms exists_euler_beats_tail_of_multiStride_highDivisors_lt
#print axioms sum_highDivisors_liouville_altPartialSum_eq_dual
#print axioms tendsto_liouvilleEulerDefect_zero_of_zeroFree
#print axioms tendsto_liouvilleEulerDefect_zero_of_re_lt_sub_one_eighth
#print axioms tendsto_liouvilleEulerDefect_of_zeta_eq_zero
#print axioms eulerEtaPartialSum_beats_tail_of_liouvilleEulerDefect_lt
#print axioms rh_iff_liouvilleEulerDefect_above_oneHundredEightyFour
#print axioms plantedQuartetEuler3_obstruction

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas

end
