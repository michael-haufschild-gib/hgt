import GaloisForLFunctions.BezoutValuationIncidence.CanonicalPrimitiveSpectralFormAndJordanWindowEnergy

/-!
# The pronic tail of the primitive energy at the quadratic horizon

The canonical primitive `W` has its period energy `E` on every window up to `(2N² - 1) E`. Abel
summation against the decreasing pronic weight `w(k) = 1/(k(k+1))` converts this phase-uniform
window law into a second-order law for the pronic tail:

`|Σ_{k > H} W(k)² / (k(k+1)) - E/(H+1)| ≤ (2N² - 1) E / ((H+1)(H+2))`.

So beyond the quadratic horizon the pronic energy of every row is its primitive energy times the
pronic tail mass, with relative error `2N²/H`. The same law holds for the period-mean-centered
prefix discrepancy `L_N(M, c) - m`, `m = -W(0)`. In particular the pronic tail beyond any
`H ≥ 4N² - 4` lies between `E/(2(H+1))` and `3E/(2(H+1))`: the pronic energy is coercive for the
primitive energy, with constant of order `N^{-2}`.
-/

open Finset Filter Topology GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

/-- The pronic weight `1/(k(k+1))`. -/
def pronicWeight (k : ℕ) : ℝ := 1 / ((k : ℝ) * ((k : ℝ) + 1))

theorem pronicWeight_nonneg (k : ℕ) : 0 ≤ pronicWeight k := by
  unfold pronicWeight
  positivity

theorem pronicWeight_eq_sub {k : ℕ} (hk : 1 ≤ k) :
    pronicWeight k = 1 / (k : ℝ) - 1 / ((k : ℝ) + 1) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  unfold pronicWeight
  field_simp
  ring

theorem pronicWeight_succ_le {k : ℕ} (hk : 1 ≤ k) : pronicWeight (k + 1) ≤ pronicWeight k := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  unfold pronicWeight
  push_cast
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith

/-- The pronic tail mass: `Σ_{H < k ≤ H + n} 1/(k(k+1)) = 1/(H+1) - 1/(H+n+1)`. -/
theorem sum_range_pronicWeight (H n : ℕ) :
    ∑ i ∈ range n, pronicWeight (H + 1 + i) = 1 / ((H : ℝ) + 1) - 1 / ((H : ℝ) + 1 + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, pronicWeight_eq_sub (by omega)]
    push_cast
    ring

/-- **Abel's inequality for the pronic weight.** If every partial sum of `g` beyond `H` is at most
`B` in size, the pronic-weighted partial sums are at most `B / ((H+1)(H+2))`. -/
theorem abs_sum_range_mul_pronicWeight_le (H : ℕ) (g : ℕ → ℝ) {B : ℝ}
    (hR : ∀ n, |∑ i ∈ range n, g (H + 1 + i)| ≤ B) (n : ℕ) :
    |∑ i ∈ range n, g (H + 1 + i) * pronicWeight (H + 1 + i)| ≤ B * pronicWeight (H + 1) := by
  set w : ℕ → ℝ := fun i => pronicWeight (H + 1 + i) with hw
  set R : ℕ → ℝ := fun n => ∑ i ∈ range n, g (H + 1 + i) with hRdef
  have hmono : ∀ i, w (i + 1) ≤ w i := fun i => by
    simp only [hw, ← add_assoc]
    exact pronicWeight_succ_le (by omega)
  -- the Abel remainder `X(n) = Σ_{i<n} g w - R(n) w(n)` moves by `R(n+1)(w(n) - w(n+1))`
  have key : ∀ n, |∑ i ∈ range n, g (H + 1 + i) * w i - R n * w n| ≤ B * (w 0 - w n) := by
    intro n
    induction n with
    | zero => simp [hRdef]
    | succ n ih =>
      have e : ∑ i ∈ range (n + 1), g (H + 1 + i) * w i - R (n + 1) * w (n + 1) =
          (∑ i ∈ range n, g (H + 1 + i) * w i - R n * w n) + R (n + 1) * (w n - w (n + 1)) := by
        simp only [hRdef, Finset.sum_range_succ]
        ring
      have hd : 0 ≤ w n - w (n + 1) := sub_nonneg.mpr (hmono n)
      rw [e]
      calc _ ≤ |∑ i ∈ range n, g (H + 1 + i) * w i - R n * w n| +
            |R (n + 1) * (w n - w (n + 1))| := abs_add_le _ _
        _ ≤ B * (w 0 - w n) + B * (w n - w (n + 1)) := by
            refine add_le_add ih ?_
            rw [abs_mul, abs_of_nonneg hd]
            exact mul_le_mul_of_nonneg_right (hR _) hd
        _ = B * (w 0 - w (n + 1)) := by ring
  have hwn : 0 ≤ w n := pronicWeight_nonneg _
  have hX := key n
  have hRn := hR n
  have hsplit : ∑ i ∈ range n, g (H + 1 + i) * pronicWeight (H + 1 + i) =
      (∑ i ∈ range n, g (H + 1 + i) * w i - R n * w n) + R n * w n := by ring
  rw [hsplit]
  calc _ ≤ |∑ i ∈ range n, g (H + 1 + i) * w i - R n * w n| + |R n * w n| := abs_add_le _ _
    _ ≤ B * (w 0 - w n) + B * w n := by
        refine add_le_add hX ?_
        rw [abs_mul, abs_of_nonneg hwn]
        exact mul_le_mul_of_nonneg_right hRn hwn
    _ = B * pronicWeight (H + 1) := by simp only [hw, add_zero]; ring

/-! ## The canonical primitive -/

theorem sievePrimitiveEnergy_nonneg_of_two_le {N : ℕ} (hN : 2 ≤ N) (c : ℕ → ℝ) :
    0 ≤ sievePrimitiveEnergy N c := by
  have h := abs_window_sum_sq_weightedCenteredSawtoothSum_sub_le hN c 0 0
  simp only [Icc_eq_empty_of_lt (show 0 + 1 > 0 + 0 by omega), sum_empty, Nat.cast_zero,
    zero_mul, sub_zero, abs_zero] at h
  have hN2 : (0 : ℝ) < 2 * (N : ℝ) ^ 2 - 1 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith
  exact nonneg_of_mul_nonneg_right (by linarith) hN2

theorem sum_range_shift_eq_sum_Icc (H n : ℕ) (f : ℕ → ℝ) :
    ∑ i ∈ range n, f (H + 1 + i) = ∑ k ∈ Icc (H + 1) (H + n), f k := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range,
    show H + n + 1 - (H + 1) = n by omega]

/-- **Finite pronic tail law.** -/
theorem abs_pronicTail_sum_sq_weightedCenteredSawtoothSum_sub_le {N : ℕ} (hN : 2 ≤ N)
    (c : ℕ → ℝ) (H n : ℕ) :
    |∑ i ∈ range n, weightedCenteredSawtoothSum N c (H + 1 + i) ^ 2 * pronicWeight (H + 1 + i) -
        sievePrimitiveEnergy N c * (1 / ((H : ℝ) + 1) - 1 / ((H : ℝ) + 1 + n))| ≤
      (2 * (N : ℝ) ^ 2 - 1) * sievePrimitiveEnergy N c * pronicWeight (H + 1) := by
  set E := sievePrimitiveEnergy N c
  set g : ℕ → ℝ := fun k => weightedCenteredSawtoothSum N c k ^ 2 - E
  have hR : ∀ n, |∑ i ∈ range n, g (H + 1 + i)| ≤ (2 * (N : ℝ) ^ 2 - 1) * E := fun n => by
    have h := abs_window_sum_sq_weightedCenteredSawtoothSum_sub_le hN c H n
    simp only [g, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
    rwa [sum_range_shift_eq_sum_Icc H n (fun k => weightedCenteredSawtoothSum N c k ^ 2)]
  have hA := abs_sum_range_mul_pronicWeight_le H g hR n
  have e : ∑ i ∈ range n, weightedCenteredSawtoothSum N c (H + 1 + i) ^ 2 *
      pronicWeight (H + 1 + i) - E * (1 / ((H : ℝ) + 1) - 1 / ((H : ℝ) + 1 + n)) =
      ∑ i ∈ range n, g (H + 1 + i) * pronicWeight (H + 1 + i) := by
    rw [← sum_range_pronicWeight, mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun i _ => by simp only [g]; ring
  rwa [e]

/-- **Pronic tail law.** The pronic tail of `W²` beyond `H` is `E/(H+1)` up to
`(2N² - 1) E / ((H+1)(H+2))`. -/
theorem pronicTail_sq_weightedCenteredSawtoothSum {N : ℕ} (hN : 2 ≤ N) (c : ℕ → ℝ) (H : ℕ) :
    Summable (fun i => weightedCenteredSawtoothSum N c (H + 1 + i) ^ 2 *
      pronicWeight (H + 1 + i)) ∧
    |∑' i, weightedCenteredSawtoothSum N c (H + 1 + i) ^ 2 * pronicWeight (H + 1 + i) -
        sievePrimitiveEnergy N c / ((H : ℝ) + 1)| ≤
      (2 * (N : ℝ) ^ 2 - 1) * sievePrimitiveEnergy N c * pronicWeight (H + 1) := by
  set E := sievePrimitiveEnergy N c
  set B := (2 * (N : ℝ) ^ 2 - 1) * E * pronicWeight (H + 1)
  set f : ℕ → ℝ := fun i => weightedCenteredSawtoothSum N c (H + 1 + i) ^ 2 *
    pronicWeight (H + 1 + i)
  have hE := sievePrimitiveEnergy_nonneg_of_two_le hN c
  have hH : (0 : ℝ) < (H : ℝ) + 1 := by positivity
  have hfin := abs_pronicTail_sum_sq_weightedCenteredSawtoothSum_sub_le hN c H
  have hf0 : ∀ i, 0 ≤ f i := fun i => mul_nonneg (sq_nonneg _) (pronicWeight_nonneg _)
  have hsum : Summable f := by
    refine summable_of_sum_range_le hf0 (c := E / ((H : ℝ) + 1) + B) fun n => ?_
    have h := (abs_le.mp (hfin n)).2
    have hn : 0 ≤ E * (1 / ((H : ℝ) + 1 + n)) := mul_nonneg hE (by positivity)
    have : E * (1 / ((H : ℝ) + 1) - 1 / ((H : ℝ) + 1 + n)) ≤ E / ((H : ℝ) + 1) := by
      rw [mul_sub, mul_one_div]
      linarith
    linarith
  refine ⟨hsum, ?_⟩
  have hlim : Tendsto (fun n : ℕ => ∑ i ∈ range n, f i -
      E * (1 / ((H : ℝ) + 1) - 1 / ((H : ℝ) + 1 + n))) atTop
      (𝓝 (∑' i, f i - E / ((H : ℝ) + 1))) := by
    have h1 := hsum.hasSum.tendsto_sum_nat
    have h2 : Tendsto (fun n : ℕ => 1 / ((H : ℝ) + 1 + n)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        (tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop)
    have h3 := (tendsto_const_nhds (x := E)).mul
      ((tendsto_const_nhds (x := 1 / ((H : ℝ) + 1))).sub h2)
    rw [sub_zero, mul_one_div] at h3
    exact h1.sub h3
  exact le_of_tendsto' ((continuous_abs.tendsto _).comp hlim) fun n => hfin n

/-! ## Coercivity and the prefix discrepancy -/

/-- **Pronic coercivity beyond the quadratic horizon.** For `H ≥ 4N² - 4`, the pronic tail of `W²`
lies between `E/(2(H+1))` and `3E/(2(H+1))`. -/
theorem pronicTail_sq_weightedCenteredSawtoothSum_bounds {N : ℕ} (hN : 2 ≤ N) (c : ℕ → ℝ)
    {H : ℕ} (hH : 4 * N ^ 2 ≤ H + 4) :
    sievePrimitiveEnergy N c / (2 * ((H : ℝ) + 1)) ≤
        ∑' i, weightedCenteredSawtoothSum N c (H + 1 + i) ^ 2 * pronicWeight (H + 1 + i) ∧
      ∑' i, weightedCenteredSawtoothSum N c (H + 1 + i) ^ 2 * pronicWeight (H + 1 + i) ≤
        3 * sievePrimitiveEnergy N c / (2 * ((H : ℝ) + 1)) := by
  set E := sievePrimitiveEnergy N c
  have hE := sievePrimitiveEnergy_nonneg_of_two_le hN c
  have h := (pronicTail_sq_weightedCenteredSawtoothSum hN c H).2
  have hH1 : (0 : ℝ) < (H : ℝ) + 1 := by positivity
  have hHR : 4 * (N : ℝ) ^ 2 ≤ (H : ℝ) + 4 := by exact_mod_cast hH
  -- `(2N² - 1)/((H+1)(H+2)) ≤ 1/(2(H+1))`
  have hcoef : (2 * (N : ℝ) ^ 2 - 1) * E * pronicWeight (H + 1) ≤ E / (2 * ((H : ℝ) + 1)) := by
    unfold pronicWeight
    push_cast
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have : (2 * (N : ℝ) ^ 2 - 1) * 2 ≤ (H : ℝ) + 1 + 1 := by linarith
    have hE' : 0 ≤ E * ((H : ℝ) + 1) := mul_nonneg hE hH1.le
    nlinarith
  have hhalf : E / ((H : ℝ) + 1) = 2 * (E / (2 * ((H : ℝ) + 1))) := by field_simp
  have h3 : 3 * E / (2 * ((H : ℝ) + 1)) = 3 * (E / (2 * ((H : ℝ) + 1))) := by ring
  rw [abs_le] at h
  constructor <;> linarith [h.1, h.2]

/-- **Pronic tail law for the prefix discrepancy.** With `m = -W(0)` the period mean of the
prefix discrepancy, the pronic tail of `(L_N(M, c) - m)²` beyond `H` is `E/(H+1)` up to
`(2N² - 1) E / ((H+1)(H+2))`. -/
theorem pronicTail_sq_sievePrefixDiscrepancy {N : ℕ} (hN : 2 ≤ N) (c : ℕ → ℝ) (H : ℕ) :
    |∑' i, (sievePrefixDiscrepancy N (H + 1 + i) c + weightedCenteredSawtoothSum N c 0) ^ 2 *
          pronicWeight (H + 1 + i) - sievePrimitiveEnergy N c / ((H : ℝ) + 1)| ≤
      (2 * (N : ℝ) ^ 2 - 1) * sievePrimitiveEnergy N c * pronicWeight (H + 1) := by
  simp only [sievePrefixDiscrepancy_eq_sub, sub_add_cancel]
  exact (pronicTail_sq_weightedCenteredSawtoothSum hN c H).2

end

end GaloisForLFunctions.BezoutValuationIncidence
