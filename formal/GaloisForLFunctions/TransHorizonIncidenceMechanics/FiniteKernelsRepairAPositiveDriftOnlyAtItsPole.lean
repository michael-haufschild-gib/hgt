import GaloisForLFunctions.TransHorizonIncidenceMechanics.RealCharacterParityRowsAtEveryHorizon
import GaloisForLFunctions.HTGeometry.RpowHarmonicTailAsymptotic
import GaloisForLFunctions.RHTower.Sieve.ZetaRealBound

/-!
# Finite kernels repair a positive drift only at its pole

Pair a prefix discrepancy with the **Mellin cells** `Δ_n(σ) = n^{-σ} − (n+1)^{-σ}`:
`Φ_c(σ) = Σ_n A_c(n) Δ_n(σ)`, the Mellin transform of the step function `A_c(⌊x⌋)` at `σ`.

* **Dilation law.** Along the step `k ↦ jk` the cells telescope, `Σ_{r<j} Δ_{tj+r}(σ) = j^{-σ} Δ_t(σ)`,
  so `Σ_n A(⌊n/j⌋) Δ_n(σ) = j^{-σ} Φ(σ)`. With the convolution law of the prefixes this gives
  `Φ_{k⋆q}(σ) = K(σ) Φ_q(σ) + m_q Φ_k(σ)`, `K(σ) = Σ_j k(j) j^{-σ}`.
* **Receiver bound.** Cauchy–Schwarz against the pronic weights: a receiver bounded by `E` has
  `|Φ_c(σ)| ≤ √E · √(2σ²(1 + 1/(2σ − 1)))` for every `σ > 1/2`.
* **Drift.** A nonnegative weight with drift `n Σ_{(n,2n]} q(d)/d ≥ κ n^{1−ε}` has
  `Φ_q(1 − ε + δ) ≤ −(κσ/2)(N₀+1)^{-δ}/δ`: the pole of its Mellin transform at `1 − ε`.

At `σ = 1 − ε + δ` the receiver bound is `O(δ^{-1/2})` (for `ε ≤ 1/2`), while `K(σ) Φ_q(σ)` has exact
order `δ^{-1}` unless `K(1 − ε) = 0`. Hence **for a positive drift weight `q` and a finite kernel `k`,
the receiver of `k ⋆ q` is unbounded at every `ε ≤ 1/2` unless the Dirichlet polynomial of `k`
vanishes at the pole `s = 1 − ε`.** The separating observable is the single number `K(1 − ε)`: sign
changes of `k` that keep it nonzero cannot pay the receiver.
-/

open Finset Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ### Mellin cells -/

/-- The Mellin cell `Δ_n(σ) = n^{-σ} − (n+1)^{-σ}`. -/
def mellinCell (σ : ℝ) (n : ℕ) : ℝ := (n : ℝ) ^ (-σ) - ((n : ℝ) + 1) ^ (-σ)

theorem mellinCell_bounds {σ : ℝ} (hσ : 0 < σ) {n : ℕ} (hn : 1 ≤ n) :
    σ * ((n : ℝ) + 1) ^ (-σ - 1) ≤ mellinCell σ n ∧ mellinCell σ n ≤ σ * (n : ℝ) ^ (-σ - 1) := by
  have h := HTGeometry.rpow_unit_step_bounds (q := -σ) (by linarith) (x := (n : ℝ))
    (by exact_mod_cast hn)
  rw [neg_neg] at h
  exact h

theorem mellinCell_nonneg {σ : ℝ} (hσ : 0 < σ) {n : ℕ} (hn : 1 ≤ n) : 0 ≤ mellinCell σ n :=
  le_trans (by positivity) (mellinCell_bounds hσ hn).1

/-- The cells of `[M, M + j)` telescope. -/
theorem sum_range_mellinCell (σ : ℝ) (M j : ℕ) :
    ∑ r ∈ range j, mellinCell σ (M + r) = (M : ℝ) ^ (-σ) - ((M + j : ℕ) : ℝ) ^ (-σ) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_range_succ, ih, mellinCell]
    simp only [Nat.cast_add, Nat.cast_one, add_assoc]
    ring

/-- A sequence of polynomial growth `n^a`, `a < σ`, pairs absolutely with the cells. -/
theorem summable_mul_mellinCell {σ a C : ℝ} (hσ : 0 < σ) (haσ : a < σ) {f : ℕ → ℝ}
    (hf0 : f 0 = 0) (hf : ∀ n, 1 ≤ n → |f n| ≤ C * (n : ℝ) ^ a) :
    Summable (fun n => f n * mellinCell σ n) := by
  refine ((Real.summable_nat_rpow.mpr (show a - σ - 1 < -1 by linarith)).mul_left
    (C * σ)).of_norm_bounded fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [hf0, Real.zero_rpow (show a - σ - 1 ≠ 0 by linarith)]
  · have hb := mellinCell_bounds hσ hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hΔ := mellinCell_nonneg hσ hn
    have hC : 0 ≤ C * (n : ℝ) ^ a := (abs_nonneg _).trans (hf n hn)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hΔ]
    calc |f n| * mellinCell σ n ≤ C * (n : ℝ) ^ a * (σ * (n : ℝ) ^ (-σ - 1)) :=
          mul_le_mul (hf n hn) hb.2 hΔ hC
      _ = C * σ * (n : ℝ) ^ (a - σ - 1) := by
          rw [show a - σ - 1 = a + (-σ - 1) by ring, Real.rpow_add hn0]; ring

/-- **The dilation law of the cells**: `Σ_n f(⌊n/j⌋) Δ_n(σ) = j^{-σ} Σ_n f(n) Δ_n(σ)`. -/
theorem tsum_comp_div_mul_mellinCell {σ : ℝ} {f : ℕ → ℝ} (hf0 : f 0 = 0) {j : ℕ} (hj : 0 < j)
    (hs : Summable (fun n => f n * mellinCell σ n))
    (hsj : Summable (fun n => f (n / j) * mellinCell σ n)) :
    ∑' n, f (n / j) * mellinCell σ n = (j : ℝ) ^ (-σ) * ∑' n, f n * mellinCell σ n := by
  have hpart : ∀ T : ℕ, ∑ n ∈ range (T * j), f (n / j) * mellinCell σ n =
      (j : ℝ) ^ (-σ) * ∑ t ∈ range T, f t * mellinCell σ t := by
    intro T
    induction T with
    | zero => simp
    | succ T ih =>
      rw [add_mul, one_mul, Finset.sum_range_add, ih, Finset.sum_range_succ, mul_add]
      congr 1
      have hdiv : ∀ r ∈ range j, f ((T * j + r) / j) * mellinCell σ (T * j + r) =
          f T * mellinCell σ (T * j + r) := fun r hr => by
        rw [show (T * j + r) / j = T by
          rw [Nat.add_comm, Nat.add_mul_div_right _ _ hj, Nat.div_eq_of_lt (mem_range.mp hr),
            zero_add]]
      rw [sum_congr rfl hdiv, ← mul_sum, sum_range_mellinCell]
      rcases Nat.eq_zero_or_pos T with rfl | hT
      · simp [hf0]
      · rw [mellinCell]
        have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg T
        have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
        push_cast
        rw [show (T : ℝ) * j + j = ((T : ℝ) + 1) * j by ring, Real.mul_rpow hT0 hj0,
          Real.mul_rpow (by linarith) hj0]
        ring
  have h1 := (hsj.hasSum.tendsto_sum_nat).comp (tendsto_atTop_atTop_of_monotone
    (fun a b h => Nat.mul_le_mul_right j h) (fun b => ⟨b, Nat.le_mul_of_pos_right b hj⟩))
  have h2 := (hs.hasSum.tendsto_sum_nat).const_mul ((j : ℝ) ^ (-σ))
  refine tendsto_nhds_unique (h1.congr fun T => ?_) h2
  simp only [Function.comp_apply, hpart]

/-! ### The receiver bound -/

/-- Cell energies: `Δ_n(σ)² n(n+1) ≤ 2σ² n^{-2σ}`. -/
theorem mellinCell_sq_mul_pronic_le {σ : ℝ} (hσ : 0 < σ) {n : ℕ} (hn : 1 ≤ n) :
    mellinCell σ n ^ 2 * ((n : ℝ) * ((n : ℝ) + 1)) ≤ 2 * σ ^ 2 * (n : ℝ) ^ (-(2 * σ)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hΔ := mellinCell_nonneg hσ hn
  set P := (n : ℝ) ^ (-σ)
  have hP : P ^ 2 = (n : ℝ) ^ (-(2 * σ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]; congr 1; push_cast; ring
  have hup : mellinCell σ n ≤ σ * P / n := by
    have := (mellinCell_bounds hσ hn).2
    rwa [Real.rpow_sub_one hn0.ne', ← mul_div_assoc] at this
  rw [← hP]
  calc mellinCell σ n ^ 2 * ((n : ℝ) * ((n : ℝ) + 1))
      ≤ (σ * P / n) ^ 2 * ((n : ℝ) * ((n : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hΔ hup 2) (by positivity)
    _ = σ ^ 2 * P ^ 2 * (((n : ℝ) + 1) / n) := by field_simp
    _ ≤ σ ^ 2 * P ^ 2 * 2 :=
        mul_le_mul_of_nonneg_left (by rw [div_le_iff₀ hn0]; linarith) (by positivity)
    _ = 2 * σ ^ 2 * P ^ 2 := by ring

/-- **The receiver bounds the Mellin pairing**: if every pronic energy of `f` is at most `E`, then
`|Σ_n f(n) Δ_n(σ)| ≤ √E √(2σ²(1 + 1/(2σ−1)))` for `σ > 1/2`. -/
theorem abs_tsum_mul_mellinCell_le {σ E : ℝ} (hσ : 1 / 2 < σ) {f : ℕ → ℝ} (hf0 : f 0 = 0)
    (hs : Summable (fun n => f n * mellinCell σ n))
    (hE : ∀ T, ∑ n ∈ Icc 1 T, f n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤ E) :
    |∑' n, f n * mellinCell σ n| ≤ Real.sqrt E * Real.sqrt (2 * σ ^ 2 * (1 + 1 / (2 * σ - 1))) := by
  have hσ0 : 0 < σ := by linarith
  set B := 2 * σ ^ 2 * (1 + 1 / (2 * σ - 1))
  have hE0 : 0 ≤ E := by simpa using hE 0
  have hZ := Real.summable_nat_rpow.mpr (show -(2 * σ) < -1 by linarith)
  have hcells : ∀ T, ∑ n ∈ Icc 1 T, mellinCell σ n ^ 2 * ((n : ℝ) * ((n : ℝ) + 1)) ≤ B := by
    intro T
    calc ∑ n ∈ Icc 1 T, mellinCell σ n ^ 2 * ((n : ℝ) * ((n : ℝ) + 1))
        ≤ ∑ n ∈ Icc 1 T, 2 * σ ^ 2 * (n : ℝ) ^ (-(2 * σ)) :=
          sum_le_sum fun n hn => mellinCell_sq_mul_pronic_le hσ0 (mem_Icc.mp hn).1
      _ = 2 * σ ^ 2 * ∑ n ∈ Icc 1 T, (n : ℝ) ^ (-(2 * σ)) := by rw [mul_sum]
      _ ≤ 2 * σ ^ 2 * (1 + 1 / (2 * σ - 1)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact (hZ.sum_le_tsum _ fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _).trans
            (RHTower.Sieve.tsum_nat_rpow_neg_le (by linarith))
  have hpart : ∀ T, |∑ n ∈ range (T + 1), f n * mellinCell σ n| ≤ Real.sqrt E * Real.sqrt B := by
    intro T
    rw [dampedSign_sum_range_succ_eq_add_Icc, hf0, zero_mul, zero_add, ← Real.sqrt_mul hE0]
    refine Real.abs_le_sqrt ?_
    set w : ℕ → ℝ := fun n => (n : ℝ) * ((n : ℝ) + 1)
    have hw : ∀ n ∈ Icc 1 T, 0 < w n := fun n hn => by
      have : (1 : ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp hn).1
      simp only [w]; positivity
    have hcs := sum_mul_sq_le_sq_mul_sq (Icc 1 T) (fun n => f n / Real.sqrt (w n))
      (fun n => mellinCell σ n * Real.sqrt (w n))
    have h1 : ∑ n ∈ Icc 1 T, f n / Real.sqrt (w n) * (mellinCell σ n * Real.sqrt (w n)) =
        ∑ n ∈ Icc 1 T, f n * mellinCell σ n := sum_congr rfl fun n hn => by
      have := (Real.sqrt_pos.mpr (hw n hn)).ne'
      field_simp
    have h2 : ∑ n ∈ Icc 1 T, (f n / Real.sqrt (w n)) ^ 2 =
        ∑ n ∈ Icc 1 T, f n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) := sum_congr rfl fun n hn => by
      rw [div_pow, Real.sq_sqrt (hw n hn).le]
    have h3 : ∑ n ∈ Icc 1 T, (mellinCell σ n * Real.sqrt (w n)) ^ 2 =
        ∑ n ∈ Icc 1 T, mellinCell σ n ^ 2 * ((n : ℝ) * ((n : ℝ) + 1)) := sum_congr rfl fun n hn => by
      rw [mul_pow, Real.sq_sqrt (hw n hn).le]
    rw [h1, h2, h3] at hcs
    exact hcs.trans (mul_le_mul (hE T) (hcells T) (sum_nonneg fun n _ => by positivity) hE0)
  have hlim := (continuous_abs.tendsto _).comp
    ((hs.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1))
  exact le_of_tendsto' hlim fun T => hpart T

/-! ### The drift lower bound -/

/-- **A positive drift is a pole at `1 − ε`.** If `q ≥ 0` has drift
`n Σ_{(n,2n]} q(d)/d ≥ κ n^{1−ε}` from `N₀` on, then at `σ = 1 − ε + δ`
`Σ_n A_q(n) Δ_n(σ) ≤ −(κσ/2) (N₀+1)^{-δ}/δ`. -/
theorem tsum_mul_mellinCell_le_of_drift {q : ℕ → ℝ} {m κ ε δ : ℝ} (hq : ∀ d, 0 ≤ q d)
    (hm : HasSum (fun d : ℕ => q d / d) m) (hκ : 0 ≤ κ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hδ : 0 < δ)
    {N₀ : ℕ}
    (hN₀ : 1 ≤ N₀)
    (hdrift : ∀ n, N₀ ≤ n → κ * (n : ℝ) ^ (1 - ε) ≤ (n : ℝ) * ∑ d ∈ Ioc n (2 * n), q d / d)
    (hs : Summable (fun n => weightCenteredPrefix q m n * mellinCell (1 - ε + δ) n)) :
    ∑' n, weightCenteredPrefix q m n * mellinCell (1 - ε + δ) n ≤
      -(κ * (1 - ε + δ) / 2) * (((N₀ : ℝ) + 1) ^ (-δ) / δ) := by
  set σ := 1 - ε + δ
  have hσ : 0 < σ := by simp only [σ]; linarith
  have hneg : ∀ n, weightCenteredPrefix q m n * mellinCell σ n ≤ 0 := fun n => by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [weightCenteredPrefix_zero, zero_mul]
    · have hA := weightCenteredPrefix_le_neg_drift hq hm n
      have hS : 0 ≤ (n : ℝ) * ∑ d ∈ Ioc n (2 * n), q d / d :=
        mul_nonneg (Nat.cast_nonneg n) (sum_nonneg fun d _ => div_nonneg (hq d) (Nat.cast_nonneg d))
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (mellinCell_nonneg hσ hn)
  have hg := HTGeometry.summable_shift_rpow (q := -δ) (by linarith) N₀
  -- the tail cells
  have htail : ∀ k : ℕ, weightCenteredPrefix q m (k + N₀) * mellinCell σ (k + N₀) ≤
      -(κ * σ / 2) * ((N₀ : ℝ) + 1 + k) ^ (-δ - 1) := by
    intro k
    set n := k + N₀
    have hn : 1 ≤ n := by omega
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hA := (weightCenteredPrefix_le_neg_drift hq hm n).trans (neg_le_neg (hdrift n (by omega)))
    have hb := (mellinCell_bounds hσ hn).1
    have hpow : ((n : ℝ) + 1) ^ (1 - ε) / 2 ≤ (n : ℝ) ^ (1 - ε) := by
      have h1 : ((n : ℝ) + 1) / 2 ≤ n := by
        have : (1 : ℝ) ≤ n := by exact_mod_cast hn
        linarith
      have h2 : ((1 : ℝ) / 2) ≤ (1 / 2 : ℝ) ^ (1 - ε) := by
        simpa using Real.rpow_le_rpow_of_exponent_ge (x := 1 / 2) (by norm_num) (by norm_num)
          (show 1 - ε ≤ 1 by linarith)
      calc ((n : ℝ) + 1) ^ (1 - ε) / 2 ≤ ((n : ℝ) + 1) ^ (1 - ε) * (1 / 2 : ℝ) ^ (1 - ε) := by
            rw [div_eq_mul_one_div]
            exact mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = (((n : ℝ) + 1) / 2) ^ (1 - ε) := by
            rw [← Real.mul_rpow (by positivity) (by norm_num)]; ring_nf
        _ ≤ (n : ℝ) ^ (1 - ε) := Real.rpow_le_rpow (by positivity) h1 (by linarith)
    have hexp : ((n : ℝ) + 1) ^ (1 - ε) * ((n : ℝ) + 1) ^ (-σ - 1) = ((n : ℝ) + 1) ^ (-δ - 1) := by
      rw [← Real.rpow_add (by positivity)]; congr 1; simp only [σ]; ring
    have hcast : (n : ℝ) + 1 = (N₀ : ℝ) + 1 + k := by simp only [n]; push_cast; ring
    have hΔ := mellinCell_nonneg hσ hn
    have hκn : 0 ≤ κ * (n : ℝ) ^ (1 - ε) := by positivity
    calc weightCenteredPrefix q m n * mellinCell σ n ≤ -(κ * (n : ℝ) ^ (1 - ε)) * mellinCell σ n :=
          mul_le_mul_of_nonneg_right hA hΔ
      _ ≤ -(κ * (n : ℝ) ^ (1 - ε)) * (σ * ((n : ℝ) + 1) ^ (-σ - 1)) :=
          mul_le_mul_of_nonpos_left hb (by linarith)
      _ ≤ -(κ * (((n : ℝ) + 1) ^ (1 - ε) / 2)) * (σ * ((n : ℝ) + 1) ^ (-σ - 1)) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact neg_le_neg (mul_le_mul_of_nonneg_left hpow hκ)
      _ = -(κ * σ / 2) * (((n : ℝ) + 1) ^ (1 - ε) * ((n : ℝ) + 1) ^ (-σ - 1)) := by ring
      _ = -(κ * σ / 2) * ((N₀ : ℝ) + 1 + k) ^ (-δ - 1) := by rw [hexp, hcast]
  have hlow := HTGeometry.tsum_shift_rpow_ge (q := -δ) (by linarith) N₀
  rw [neg_neg] at hlow
  rw [← hs.sum_add_tsum_nat_add N₀]
  have hhead : ∑ n ∈ range N₀, weightCenteredPrefix q m n * mellinCell σ n ≤ 0 :=
    sum_nonpos fun n _ => hneg n
  have htsum : ∑' k : ℕ, weightCenteredPrefix q m (k + N₀) * mellinCell σ (k + N₀) ≤
      -(κ * σ / 2) * ∑' k : ℕ, ((N₀ : ℝ) + 1 + k) ^ (-δ - 1) := by
    rw [← tsum_mul_left]
    exact Summable.tsum_le_tsum htail ((summable_nat_add_iff N₀).mpr hs) (hg.mul_left _)
  have hκσ : 0 ≤ κ * σ / 2 := by positivity
  calc ∑ n ∈ range N₀, weightCenteredPrefix q m n * mellinCell σ n +
        ∑' k : ℕ, weightCenteredPrefix q m (k + N₀) * mellinCell σ (k + N₀)
      ≤ 0 + -(κ * σ / 2) * ∑' k : ℕ, ((N₀ : ℝ) + 1 + k) ^ (-δ - 1) := add_le_add hhead htsum
    _ ≤ -(κ * σ / 2) * (((N₀ : ℝ) + 1) ^ (-δ) / δ) := by
        rw [zero_add, neg_mul, neg_mul, neg_le_neg_iff]
        exact mul_le_mul_of_nonneg_left hlow hκσ

/-! ### Finite kernels -/

/-- The prefix of a finite kernel is bounded by its mass: `|A_k(n)| ≤ Σ_j |k(j)|`. -/
theorem abs_weightCenteredPrefix_finiteKernel_le {k : ℕ → ℝ} {J : ℕ} (hkJ : ∀ j, J < j → k j = 0)
    (n : ℕ) :
    |weightCenteredPrefix k (∑ j ∈ Icc 1 J, k j / j) n| ≤ ∑ j ∈ Icc 1 J, |k j| := by
  have hfloor : ∑ d ∈ Icc 1 n, k d * ((n / d : ℕ) : ℝ) = ∑ d ∈ Icc 1 J, k d * ((n / d : ℕ) : ℝ) := by
    have hsub1 : Icc 1 n ⊆ Icc 1 (n + J) := Icc_subset_Icc le_rfl (by omega)
    have hsub2 : Icc 1 J ⊆ Icc 1 (n + J) := Icc_subset_Icc le_rfl (by omega)
    rw [sum_subset hsub1 fun d hd hdn => ?_, sum_subset hsub2 fun d hd hdJ => ?_]
    · have : J < d := by simp only [mem_Icc] at hd hdJ; omega
      rw [hkJ d this, zero_mul]
    · have : n < d := by simp only [mem_Icc] at hd hdn; omega
      rw [Nat.div_eq_of_lt this, Nat.cast_zero, mul_zero]
  have hsplit : weightCenteredPrefix k (∑ j ∈ Icc 1 J, k j / j) n =
      ∑ j ∈ Icc 1 J, k j * (((n / j : ℕ) : ℝ) - (n : ℝ) / j) := by
    rw [weightCenteredPrefix, sum_Icc_sum_divisors_eq_floor, hfloor, sum_mul, ← sum_sub_distrib]
    exact sum_congr rfl fun j _ => by ring
  rw [hsplit]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j hj => ?_)
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (abs_natDiv_sub_div_le n j (mem_Icc.mp hj).1)

/-- **Finite kernels repair a positive drift only at its pole.** Let `0 < ε ≤ 1/2`, let `q ≥ 0` lie in
the damped class with drift `n Σ_{(n,2n]} q(d)/d ≥ κ n^{1−ε}` eventually, and let `k` be supported on
`[1, J]`. If `K(1 − ε) = Σ_j k(j) j^{-(1−ε)} ≠ 0`, the receiver of `k ⋆ q` is unbounded. -/
theorem not_receiverBounded_dirichletConv_of_drift {K ε κ : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    {q : ℕ → ℝ} (hq : ∀ d, 0 ≤ q d) (hclass : DampedClass K ε q) (hκ : 0 < κ)
    (hdrift : ∀ᶠ n : ℕ in atTop, κ * (n : ℝ) ^ (1 - ε) ≤ (n : ℝ) * ∑ d ∈ Ioc n (2 * n), q d / d)
    {k : ℕ → ℝ} {J : ℕ} (hkJ : ∀ j, J < j → k j = 0)
    (hK : ∑ j ∈ Icc 1 J, k j * (j : ℝ) ^ (-(1 - ε)) ≠ 0) :
    ¬ ReceiverBounded (RHTower.dirichletConv k q) := by
  rintro ⟨E, hE⟩
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp hdrift
  set N₀ := max N₁ 1
  have hN₀ : 1 ≤ N₀ := le_max_right _ _
  have hdrift' : ∀ n, N₀ ≤ n → κ * (n : ℝ) ^ (1 - ε) ≤ (n : ℝ) * ∑ d ∈ Ioc n (2 * n), q d / d :=
    fun n hn => hN₁ n ((le_max_left _ _).trans hn)
  have hK0 := nonneg_of_dampedClass hclass
  -- the means
  have hqs : Summable (fun d : ℕ => q d / d) := summable_div_of_dampedClass hε hclass
  set mq := ∑' d : ℕ, q d / d
  set mk := ∑ j ∈ Icc 1 J, k j / j
  have hkoff : ∀ j ∉ Icc 1 J, k j / j = 0 := fun j hj => by
    rw [mem_Icc, not_and_or] at hj
    rcases hj with hj | hj
    · rw [show j = 0 by omega, Nat.cast_zero, div_zero]
    · rw [hkJ j (by omega), zero_div]
  have hkhas : HasSum (fun j : ℕ => k j / j) mk := hasSum_sum_of_ne_finset_zero hkoff
  have hkabs : Summable (fun j : ℕ => |k j / j|) :=
    summable_of_ne_finset_zero (s := Icc 1 J) fun j hj => by rw [hkoff j hj, abs_zero]
  have hmean : ∑' n : ℕ, RHTower.dirichletConv k q n / n = mk * mq :=
    (hasSum_dirichletConv_div hkhas hqs.hasSum hkabs hqs.abs).tsum_eq
  have hE' : ∀ T, ∑ n ∈ Icc 1 T, weightCenteredPrefix (RHTower.dirichletConv k q) (mk * mq) n ^ 2 /
      ((n : ℝ) * ((n : ℝ) + 1)) ≤ E := fun T => by
    have := hE T; rwa [hmean] at this
  have hE0 : 0 ≤ E := by simpa using hE' 0
  -- the prefixes
  set A := weightCenteredPrefix q mq
  set Ak := weightCenteredPrefix k mk
  set Cq := K * (1 + 1 / (1 - ε) + 1 / ε)
  have hCq : 0 ≤ Cq := by
    have : 0 < 1 - ε := by linarith
    positivity
  have hA0 : A 0 = 0 := weightCenteredPrefix_zero _ _
  have hAk0 : Ak 0 = 0 := weightCenteredPrefix_zero _ _
  have hAbound : ∀ n, 1 ≤ n → |A n| ≤ Cq * (n : ℝ) ^ (1 - ε) := fun n hn =>
    abs_weightCenteredPrefix_le_of_dampedClass hε (by linarith) hclass hn
  set L1 := ∑ j ∈ Icc 1 J, |k j|
  have hAk : ∀ n, |Ak n| ≤ L1 := abs_weightCenteredPrefix_finiteKernel_le hkJ
  have hL1 : 0 ≤ L1 := sum_nonneg fun j _ => abs_nonneg _
  have hconv : ∀ n, weightCenteredPrefix (RHTower.dirichletConv k q) (mk * mq) n =
      ∑ j ∈ Icc 1 J, k j * A (n / j) + mq * Ak n := fun n => by
    rw [weightCenteredPrefix_dirichletConv]
    congr 1
    have hsub1 : Icc 1 n ⊆ Icc 1 (n + J) := Icc_subset_Icc le_rfl (by omega)
    have hsub2 : Icc 1 J ⊆ Icc 1 (n + J) := Icc_subset_Icc le_rfl (by omega)
    rw [sum_subset hsub1 fun d hd hdn => ?_, sum_subset hsub2 fun d hd hdJ => ?_]
    · have : J < d := by simp only [mem_Icc] at hd hdJ; omega
      rw [hkJ d this, zero_mul]
    · have : n < d := by simp only [mem_Icc] at hd hdn; omega
      rw [Nat.div_eq_of_lt this, weightCenteredPrefix_zero, mul_zero]
  -- the inequality at `σ = 1 − ε + δ`
  set Kσ : ℝ → ℝ := fun δ => ∑ j ∈ Icc 1 J, k j * (j : ℝ) ^ (-(1 - ε + δ))
  have hkey : ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 →
      |Kσ δ| * (κ * (1 - ε + δ) / 2 * ((N₀ : ℝ) + 1) ^ (-δ)) ≤
        Real.sqrt E * Real.sqrt (9 / 2 * (δ ^ 2 + δ / 2)) + δ * (|mq| * L1 * (2 - ε + δ)) := by
    intro δ hδ hδ2
    set σ := 1 - ε + δ
    have hσ : 1 / 2 < σ := by simp only [σ]; linarith
    have hσ0 : 0 < σ := by linarith
    have hsA : Summable (fun n => A n * mellinCell σ n) :=
      summable_mul_mellinCell hσ0 (show 1 - ε < σ by simp only [σ]; linarith) hA0 hAbound
    have hsAj : ∀ j ∈ Icc 1 J, Summable (fun n => A (n / j) * mellinCell σ n) := fun j hj => by
      have hj : 0 < j := (mem_Icc.mp hj).1
      refine summable_mul_mellinCell (C := Cq) hσ0 (show 1 - ε < σ by simp only [σ]; linarith)
        (by simp [hA0]) fun n hn => ?_
      rcases Nat.eq_zero_or_pos (n / j) with h0 | h1
      · rw [h0, hA0, abs_zero]; positivity
      · refine (hAbound _ h1).trans (mul_le_mul_of_nonneg_left ?_ hCq)
        exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast Nat.div_le_self n j)
          (by linarith)
    have hsAk : Summable (fun n => Ak n * mellinCell σ n) :=
      summable_mul_mellinCell (a := 0) hσ0 hσ0 hAk0 fun n _ => by
        rw [Real.rpow_zero, mul_one]; exact hAk n
    -- the convolution law of the pairings
    have hsplit : ∀ n, weightCenteredPrefix (RHTower.dirichletConv k q) (mk * mq) n * mellinCell σ n =
        ∑ j ∈ Icc 1 J, k j * (A (n / j) * mellinCell σ n) + mq * (Ak n * mellinCell σ n) :=
      fun n => by
        rw [hconv, add_mul, Finset.sum_mul]
        congr 1
        · exact sum_congr rfl fun j _ => by ring
        · ring
    have hsJ : Summable (fun n => ∑ j ∈ Icc 1 J, k j * (A (n / j) * mellinCell σ n)) :=
      summable_sum fun j hj => (hsAj j hj).mul_left _
    have hsc : Summable (fun n =>
        weightCenteredPrefix (RHTower.dirichletConv k q) (mk * mq) n * mellinCell σ n) := by
      simp_rw [hsplit]; exact hsJ.add (hsAk.mul_left _)
    have hlaw : ∑' n, weightCenteredPrefix (RHTower.dirichletConv k q) (mk * mq) n * mellinCell σ n =
        Kσ δ * ∑' n, A n * mellinCell σ n + mq * ∑' n, Ak n * mellinCell σ n := by
      simp_rw [hsplit]
      rw [hsJ.tsum_add (hsAk.mul_left _), Summable.tsum_finsetSum fun j hj => (hsAj j hj).mul_left _,
        tsum_mul_left]
      congr 1
      simp only [Kσ, sum_mul]
      refine sum_congr rfl fun j hj => ?_
      rw [tsum_mul_left, tsum_comp_div_mul_mellinCell hA0 (mem_Icc.mp hj).1 hsA (hsAj j hj)]
      ring
    -- the three bounds
    have hcs := abs_tsum_mul_mellinCell_le hσ (weightCenteredPrefix_zero _ _) hsc hE'
    have hPk : |∑' n, Ak n * mellinCell σ n| ≤ L1 * (σ + 1) := by
      have hZ := (Real.summable_nat_rpow.mpr (show -(σ + 1) < -1 by linarith)).mul_left (L1 * σ)
      have h := tsum_of_norm_bounded (f := fun n => Ak n * mellinCell σ n) hZ.hasSum fun n => by
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · rw [hAk0, zero_mul, norm_zero]
          exact mul_nonneg (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        · have hb := (mellinCell_bounds hσ0 hn).2
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mellinCell_nonneg hσ0 hn),
            show -(σ + 1) = -σ - 1 by ring, mul_assoc]
          exact mul_le_mul (hAk n) hb (mellinCell_nonneg hσ0 hn) hL1
      rw [Real.norm_eq_abs, tsum_mul_left] at h
      refine h.trans ?_
      have hzeta := RHTower.Sieve.tsum_nat_rpow_neg_le (show 1 < σ + 1 by linarith)
      calc L1 * σ * ∑' n : ℕ, (n : ℝ) ^ (-(σ + 1)) ≤ L1 * σ * (1 + 1 / (σ + 1 - 1)) :=
            mul_le_mul_of_nonneg_left hzeta (by positivity)
        _ = L1 * (σ + 1) := by
            have hσne : σ ≠ 0 := hσ0.ne'
            rw [add_sub_cancel_right]; field_simp
    have hdrift'' := tsum_mul_mellinCell_le_of_drift hq hqs.hasSum hκ.le hε.le (by linarith) hδ
      hN₀ hdrift' hsA
    -- assemble
    set Φ := ∑' n, A n * mellinCell σ n
    have hΦ : (κ * σ / 2) * (((N₀ : ℝ) + 1) ^ (-δ) / δ) ≤ |Φ| := by
      have := neg_le_abs Φ; linarith
    have h2σ0 : 0 < 2 * σ - 1 := by linarith
    have hBnn : 0 ≤ 1 + 1 / (2 * σ - 1) := by positivity
    have hB : Real.sqrt (2 * σ ^ 2 * (1 + 1 / (2 * σ - 1))) * δ ≤
        Real.sqrt (9 / 2 * (δ ^ 2 + δ / 2)) := by
      rw [show Real.sqrt (2 * σ ^ 2 * (1 + 1 / (2 * σ - 1))) * δ =
          Real.sqrt (2 * σ ^ 2 * (1 + 1 / (2 * σ - 1)) * δ ^ 2) by
        rw [Real.sqrt_mul (x := 2 * σ ^ 2 * (1 + 1 / (2 * σ - 1))) (by positivity) (δ ^ 2),
          Real.sqrt_sq hδ.le]]
      refine Real.sqrt_le_sqrt ?_
      have h2σ : 2 * δ ≤ 2 * σ - 1 := by simp only [σ]; linarith
      have hinv : 1 / (2 * σ - 1) ≤ 1 / (2 * δ) := one_div_le_one_div_of_le (by positivity) h2σ
      have hσ2 : σ ^ 2 ≤ 9 / 4 := by
        have : σ ≤ 3 / 2 := by simp only [σ]; linarith
        nlinarith
      calc 2 * σ ^ 2 * (1 + 1 / (2 * σ - 1)) * δ ^ 2 ≤ 2 * (9 / 4) * (1 + 1 / (2 * δ)) * δ ^ 2 := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            exact mul_le_mul (by linarith) (by linarith) hBnn (by norm_num)
        _ = 9 / 2 * (δ ^ 2 + δ / 2) := by field_simp; ring
    have habs : |Kσ δ| * |Φ| ≤
        Real.sqrt E * Real.sqrt (2 * σ ^ 2 * (1 + 1 / (2 * σ - 1))) + |mq| * (L1 * (σ + 1)) := by
      rw [← abs_mul, show Kσ δ * Φ = (Kσ δ * Φ + mq * ∑' n, Ak n * mellinCell σ n) -
        mq * ∑' n, Ak n * mellinCell σ n by ring, ← hlaw]
      refine (abs_sub _ _).trans (add_le_add hcs ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hPk (abs_nonneg _)
    have hKabs := abs_nonneg (Kσ δ)
    calc |Kσ δ| * (κ * (1 - ε + δ) / 2 * ((N₀ : ℝ) + 1) ^ (-δ))
        = δ * (|Kσ δ| * ((κ * σ / 2) * (((N₀ : ℝ) + 1) ^ (-δ) / δ))) := by
          simp only [σ]; field_simp
      _ ≤ δ * (|Kσ δ| * |Φ|) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hΦ hKabs) hδ.le
      _ ≤ δ * (Real.sqrt E * Real.sqrt (2 * σ ^ 2 * (1 + 1 / (2 * σ - 1))) +
            |mq| * (L1 * (σ + 1))) := mul_le_mul_of_nonneg_left habs hδ.le
      _ = Real.sqrt E * (Real.sqrt (2 * σ ^ 2 * (1 + 1 / (2 * σ - 1))) * δ) +
            δ * (|mq| * L1 * (2 - ε + δ)) := by simp only [σ]; ring
      _ ≤ Real.sqrt E * Real.sqrt (9 / 2 * (δ ^ 2 + δ / 2)) + δ * (|mq| * L1 * (2 - ε + δ)) :=
          add_le_add (mul_le_mul_of_nonneg_left hB (Real.sqrt_nonneg _)) le_rfl
  -- the limit `δ → 0⁺`
  have hKlim : Tendsto Kσ (𝓝 0) (𝓝 (∑ j ∈ Icc 1 J, k j * (j : ℝ) ^ (-(1 - ε)))) := by
    refine tendsto_finsetSum _ fun j hj => tendsto_const_nhds.mul ?_
    have hj0 : (j : ℝ) ≠ 0 := by have := (mem_Icc.mp hj).1; positivity
    have hc : Continuous (fun δ : ℝ => (j : ℝ) ^ (-(1 - ε + δ))) :=
      continuous_const.rpow (by fun_prop) fun _ => Or.inl hj0
    simpa using hc.tendsto 0
  have hN0 : ((N₀ : ℝ) + 1) ≠ 0 := by positivity
  have hPlim : Tendsto (fun δ : ℝ => ((N₀ : ℝ) + 1) ^ (-δ)) (𝓝 0) (𝓝 1) := by
    have hc : Continuous (fun δ : ℝ => ((N₀ : ℝ) + 1) ^ (-δ)) :=
      continuous_const.rpow (by fun_prop) fun _ => Or.inl hN0
    simpa using hc.tendsto 0
  set L₀ := |∑ j ∈ Icc 1 J, k j * (j : ℝ) ^ (-(1 - ε))| * (κ * (1 - ε + 0) / 2 * 1)
  have hL₀ : 0 < L₀ := by
    have : 0 < 1 - ε := by linarith
    simp only [L₀]; positivity
  have hLHS : Tendsto (fun δ : ℝ => |Kσ δ| * (κ * (1 - ε + δ) / 2 * ((N₀ : ℝ) + 1) ^ (-δ)))
      (𝓝 0) (𝓝 L₀) :=
    (continuous_abs.tendsto _ |>.comp hKlim).mul
      ((((tendsto_const_nhds.add tendsto_id).const_mul κ).div_const 2).mul hPlim)
  have hRHS : Tendsto (fun δ : ℝ =>
      Real.sqrt E * Real.sqrt (9 / 2 * (δ ^ 2 + δ / 2)) + δ * (|mq| * L1 * (2 - ε + δ)))
      (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun δ : ℝ =>
        Real.sqrt E * Real.sqrt (9 / 2 * (δ ^ 2 + δ / 2)) + δ * (|mq| * L1 * (2 - ε + δ))) := by
      fun_prop
    simpa using hc.tendsto 0
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), L₀ / 2 < |Kσ δ| * (κ * (1 - ε + δ) / 2 * ((N₀ : ℝ) + 1) ^ (-δ)) ∧
      Real.sqrt E * Real.sqrt (9 / 2 * (δ ^ 2 + δ / 2)) + δ * (|mq| * L1 * (2 - ε + δ)) < L₀ / 2 ∧
      0 < δ ∧ δ ≤ 1 / 2 := by
    refine (tendsto_nhdsWithin_of_tendsto_nhds hLHS |>.eventually (lt_mem_nhds (by linarith))).and
      ((tendsto_nhdsWithin_of_tendsto_nhds hRHS |>.eventually (gt_mem_nhds (by linarith))).and
      ((eventually_nhdsWithin_of_forall fun δ hδ => hδ).and ?_))
    exact tendsto_nhdsWithin_of_tendsto_nhds tendsto_id |>.eventually (eventually_le_nhds (by norm_num))
  obtain ⟨δ, h1, h2, hδ, hδ2⟩ := hev.exists
  linarith [hkey δ hδ hδ2]

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
