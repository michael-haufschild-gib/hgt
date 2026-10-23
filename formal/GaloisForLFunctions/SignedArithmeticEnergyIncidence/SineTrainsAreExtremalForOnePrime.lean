import GaloisForLFunctions.ArithmeticIncidencePositivity.ResonantTrainWitness
import GaloisForLFunctions.SignedArithmeticEnergyIncidence.ChainLendingAndTrainCapacity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Sine trains are extremal for one prime

An **amplitude train** is `S = Σ_{k ≤ M} f_k g(· + kL)`: `M + 1` disjoint copies of one bump at the
spacing `L`, with amplitudes `f`.  At `L = log p` the train sits on the tower `{1, p, …, p^M}` and
its autocorrelation at the lag `log p` is the first-power prime charge of `p`.

* **Exact lag law** (`autoCorr_amplitudeTrain_first`, `autoCorr_amplitudeTrain_zero`):
  `A_S(L) = (Σ_{k<M} f_k f_{k+1}) A_g(0)` and `A_S(0) = (Σ_{k≤M} f_k²) A_g(0)` — the first-lag
  charge of a train is the chain form of its amplitudes.
* **Capacity** (`autoCorr_amplitudeTrain_first_le`, `..._ge`):
  `|A_S(L)| ≤ cos(π/(M+2)) A_S(0)` for every amplitude vector, by the sine certificate of
  `ChainLendingAndTrainCapacity`; the **sine train** `f_k = sin((k+1)π/(M+2))` attains it
  (`autoCorr_sineTrain_first`).
* **The resonant train is not extremal for one prime** (`resonant_ratio_lt_cos`): the unit train
  carries `M/(M+1)` of its mass at the first lag, strictly less than `cos(π/(M+2))` from `M = 2` on.
  The deficit of the extremal train is `1 − cos(π/(M+2)) ≍ π²/(2M²)`, not `1/(M+1)`: a single prime
  approaches the full mass envelope quadratically fast in the length of the train.
-/

open MeasureTheory Set Finset Real
open GaloisForLFunctions.ArithmeticCriticalityTheory GaloisForLFunctions.ArithmeticIncidencePositivity

namespace GaloisForLFunctions.SignedArithmeticEnergyIncidence

noncomputable section
set_option autoImplicit false

variable {g : ℝ → ℝ}

/-- The amplitude train `Σ_{k ≤ M} f_k g(· + kL)`. -/
def amplitudeTrain (g : ℝ → ℝ) (L : ℝ) (M : ℕ) (f : ℕ → ℝ) : ℝ → ℝ :=
  translateComb g (M + 1) f (fun k => (k : ℝ) * L)

/-- At the lag `mL` the train correlates its copy `j` with its copy `j + m` only. -/
theorem autoCorr_amplitudeTrain (hg : Continuous g) (hgc : HasCompactSupport g) {w L : ℝ}
    (hw : 0 ≤ w) (hL : 2 * w < L) (hsupp : ∀ x, w < |x| → g x = 0) (M m : ℕ) (f : ℕ → ℝ) :
    autoCorr (amplitudeTrain g L M f) ((m : ℝ) * L) =
      (∑ j ∈ range (M + 1), if j + m ≤ M then f (j + m) * f j else 0) * autoCorr g 0 := by
  have hgn : ContCompact g := ⟨hg, hgc⟩
  have hexp : autoCorr (amplitudeTrain g L M f) ((m : ℝ) * L)
      = ∑ k ∈ range (M + 1), ∑ j ∈ range (M + 1),
          f k * f j * autoCorr g (((j : ℝ) * L + (m : ℝ) * L) - (k : ℝ) * L) := by
    rw [autoCorr_eq_testPairing,
      show (fun u => amplitudeTrain g L M f (u + (m : ℝ) * L))
          = translateComb g (M + 1) f (fun j => (j : ℝ) * L + (m : ℝ) * L) by
        funext u
        simp only [amplitudeTrain, translateComb]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [show u + (m : ℝ) * L + (k : ℝ) * L = u + ((k : ℝ) * L + (m : ℝ) * L) by ring],
      amplitudeTrain, testPairing_comb hgn]
  have hterm : ∀ k j : ℕ, autoCorr g (((j : ℝ) * L + (m : ℝ) * L) - (k : ℝ) * L) =
      if k = j + m then autoCorr g 0 else 0 := by
    intro k j
    by_cases h : k = j + m
    · rw [if_pos h, h]
      push_cast
      rw [show ((j : ℝ) * L + (m : ℝ) * L) - ((j : ℝ) + (m : ℝ)) * L = 0 by ring]
    · rw [if_neg h]
      have hne : ((j : ℤ) + (m : ℤ) - (k : ℤ)) ≠ 0 := fun hc => h (by omega)
      have hcast : ((j : ℝ) * L + (m : ℝ) * L) - (k : ℝ) * L
          = (((j : ℤ) + (m : ℤ) - (k : ℤ) : ℤ) : ℝ) * L := by push_cast; ring
      rw [hcast]
      exact autoCorr_eq_zero_of_mul_spacing hw hL hsupp hne
  rw [hexp, sum_comm]
  simp only [hterm, mul_ite, mul_zero]
  rw [sum_mul]
  refine sum_congr rfl fun j _ => ?_
  by_cases hjm : j + m ≤ M
  · rw [if_pos hjm, sum_ite_eq' (range (M + 1)) (j + m)]
    rw [if_pos (Finset.mem_range.mpr (by omega))]
  · rw [if_neg hjm, zero_mul]
    refine sum_eq_zero fun k hk => ?_
    have : k ≠ j + m := by simp at hk; omega
    rw [if_neg this]

theorem autoCorr_amplitudeTrain_zero (hg : Continuous g) (hgc : HasCompactSupport g) {w L : ℝ}
    (hw : 0 ≤ w) (hL : 2 * w < L) (hsupp : ∀ x, w < |x| → g x = 0) (M : ℕ) (f : ℕ → ℝ) :
    autoCorr (amplitudeTrain g L M f) 0 = (∑ k ∈ range (M + 1), f k ^ 2) * autoCorr g 0 := by
  have h := autoCorr_amplitudeTrain hg hgc hw hL hsupp M 0 f
  rw [Nat.cast_zero, zero_mul] at h
  rw [h]
  congr 1
  refine sum_congr rfl fun k hk => ?_
  rw [if_pos (by simp at hk; omega), add_zero, sq]

theorem autoCorr_amplitudeTrain_first (hg : Continuous g) (hgc : HasCompactSupport g) {w L : ℝ}
    (hw : 0 ≤ w) (hL : 2 * w < L) (hsupp : ∀ x, w < |x| → g x = 0) (M : ℕ) (f : ℕ → ℝ) :
    autoCorr (amplitudeTrain g L M f) L = (∑ k ∈ range M, f k * f (k + 1)) * autoCorr g 0 := by
  have h := autoCorr_amplitudeTrain hg hgc hw hL hsupp M 1 f
  rw [Nat.cast_one, one_mul] at h
  rw [h, Finset.sum_range_succ, if_neg (by omega), add_zero]
  congr 1
  refine sum_congr rfl fun k hk => ?_
  rw [if_pos (by simp at hk; omega), mul_comm]

theorem autoCorr_self_zero_nonneg (g : ℝ → ℝ) : 0 ≤ autoCorr g 0 := by
  unfold autoCorr
  exact integral_nonneg fun x => by simp only [add_zero]; exact mul_self_nonneg _

/-- **First-lag capacity of a train**: `A_S(L) ≤ cos(π/(M+2)) A_S(0)`. -/
theorem autoCorr_amplitudeTrain_first_le (hg : Continuous g) (hgc : HasCompactSupport g)
    {w L : ℝ} (hw : 0 ≤ w) (hL : 2 * w < L) (hsupp : ∀ x, w < |x| → g x = 0) (M : ℕ)
    (f : ℕ → ℝ) :
    autoCorr (amplitudeTrain g L M f) L ≤
      Real.cos (π / (M + 2)) * autoCorr (amplitudeTrain g L M f) 0 := by
  rw [autoCorr_amplitudeTrain_first hg hgc hw hL hsupp, autoCorr_amplitudeTrain_zero hg hgc hw hL
    hsupp]
  have hcap := uniformTrain_capacity M f
  have hA := autoCorr_self_zero_nonneg g
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (by linarith) hA

/-- The alternating signs give the lower capacity: `−cos(π/(M+2)) A_S(0) ≤ A_S(L)`. -/
theorem autoCorr_amplitudeTrain_first_ge (hg : Continuous g) (hgc : HasCompactSupport g)
    {w L : ℝ} (hw : 0 ≤ w) (hL : 2 * w < L) (hsupp : ∀ x, w < |x| → g x = 0) (M : ℕ)
    (f : ℕ → ℝ) :
    -(Real.cos (π / (M + 2)) * autoCorr (amplitudeTrain g L M f) 0) ≤
      autoCorr (amplitudeTrain g L M f) L := by
  rw [autoCorr_amplitudeTrain_first hg hgc hw hL hsupp, autoCorr_amplitudeTrain_zero hg hgc hw hL
    hsupp]
  set f' : ℕ → ℝ := fun k => (-1) ^ k * f k with hf'
  have hcap := uniformTrain_capacity M f'
  have h1 : ∑ k ∈ range M, f' k * f' (k + 1) = -∑ k ∈ range M, f k * f (k + 1) := by
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun k _ => ?_
    have hsq : ((-1 : ℝ) ^ k) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    calc f' k * f' (k + 1) = -(((-1 : ℝ) ^ k) ^ 2) * (f k * f (k + 1)) := by
          simp only [hf', pow_succ]; ring
      _ = -(f k * f (k + 1)) := by rw [hsq]; ring
  have h2 : ∑ k ∈ range (M + 1), f' k ^ 2 = ∑ k ∈ range (M + 1), f k ^ 2 := by
    refine sum_congr rfl fun k _ => ?_
    simp only [hf', mul_pow]
    rw [show ((-1 : ℝ) ^ k) ^ 2 = 1 by rw [← pow_mul, mul_comm, pow_mul]; norm_num, one_mul]
  rw [h1, h2] at hcap
  have hA := autoCorr_self_zero_nonneg g
  have : -(Real.cos (π / (M + 2)) * ∑ k ∈ range (M + 1), f k ^ 2) ≤
      ∑ k ∈ range M, f k * f (k + 1) := by linarith
  calc -(Real.cos (π / (M + 2)) * ((∑ k ∈ range (M + 1), f k ^ 2) * autoCorr g 0))
      = -(Real.cos (π / (M + 2)) * ∑ k ∈ range (M + 1), f k ^ 2) * autoCorr g 0 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right this hA

/-- **The sine train attains the capacity.** -/
theorem autoCorr_sineTrain_first (hg : Continuous g) (hgc : HasCompactSupport g) {w L : ℝ}
    (hw : 0 ≤ w) (hL : 2 * w < L) (hsupp : ∀ x, w < |x| → g x = 0) (M : ℕ) :
    autoCorr (amplitudeTrain g L M (trainSine M)) L =
      Real.cos (π / (M + 2)) * autoCorr (amplitudeTrain g L M (trainSine M)) 0 := by
  rw [autoCorr_amplitudeTrain_first hg hgc hw hL hsupp, autoCorr_amplitudeTrain_zero hg hgc hw hL
    hsupp]
  have h := uniformTrain_capacity_attained M
  have : ∑ k ∈ range M, trainSine M k * trainSine M (k + 1) =
      Real.cos (π / (M + 2)) * ∑ k ∈ range (M + 1), trainSine M k ^ 2 := by linarith
  rw [this]
  ring

/-- **The resonant train is not extremal for one prime**: from `M = 2` on, its first-lag ratio
`M/(M+1)` is strictly below the capacity `cos(π/(M+2))`. -/
theorem resonant_ratio_lt_cos {M : ℕ} (hM : 2 ≤ M) :
    (M : ℝ) / (M + 1) < Real.cos (π / (M + 2)) := by
  have hM' : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hc := Real.one_sub_sq_div_two_le_cos (x := π / (M + 2))
  have hpi : π < 3.15 := Real.pi_lt_d2
  have hpi0 : 0 < π := Real.pi_pos
  have hpos : (0 : ℝ) < M + 2 := by positivity
  have hsq : (π / (M + 2)) ^ 2 / 2 < 1 / (M + 1) := by
    rw [div_pow, div_div, div_lt_div_iff₀ (by positivity) (by positivity)]
    have hpi2 : π ^ 2 < 9.93 := by nlinarith
    have h1 : π ^ 2 * ((M : ℝ) + 1) < 9.93 * ((M : ℝ) + 1) :=
      mul_lt_mul_of_pos_right hpi2 (by positivity)
    nlinarith
  have : (M : ℝ) / (M + 1) = 1 - 1 / (M + 1) := by field_simp; ring
  linarith

end

end GaloisForLFunctions.SignedArithmeticEnergyIncidence
