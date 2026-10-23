import GaloisForLFunctions.ArithmeticCompensationTheory.TheCompensationDefectDecaysLogarithmically

/-!
# The compensating projection moves summably across scales

At cutoff `P²` the literal complement `C_P` of the large-prime sector `L_P` is `−α_P L_P + R_P`,
and the compensation defect `(1 − α_P)² + ‖R_P‖²/‖L_P‖²` is at most `K/log⁶P`. A change of scale
moves the projection onto `L_P`; the connection term of that motion is the change of the amplitude.
This file bounds it on the actual source, `0 < ε < ½`:

* `abs_one_sub_pmCompensationAmplitude_le_sqrt`: `|1 − α_P| ≤ √(defect)`, because the transverse
  part is nonnegative;
* `exists_abs_one_sub_pmCompensationAmplitude_le`: `|1 − α_P| ≤ K/log³P` for all large `P`;
* `summable_abs_pmCompensationAmplitude_dyadic_sub`: the amplitude has bounded variation over the
  dyadic scales, `Σ_k |α_{2^{k+1}} − α_{2^k}| < ∞`;
* `summable_pmTransverseEnergy_div_sectorEnergy_dyadic`: the relative transverse energies are
  summable over the dyadic scales.

So the iteration over scales costs a summable connection term, with explicit constants. The
absolute complete energies still grow with the cutoff: what is summable is the relative geometry
of the compensation, not the critical energy.
-/

open Filter Topology Finset RHTower

noncomputable section

namespace GaloisForLFunctions.ArithmeticCompensationTheory

theorem pmRamanujanLargePrimeSectorEnergy_nonneg (ε : ℝ) (P : ℕ) :
    0 ≤ pmRamanujanLargePrimeSectorEnergy ε P := by
  unfold pmRamanujanLargePrimeSectorEnergy; positivity

/-- The relative transverse energy is nonnegative. -/
theorem pmTransverseEnergy_div_nonneg (ε : ℝ) {P : ℕ} (hP : 2 ≤ P) :
    0 ≤ pmTransverseEnergy ε P / pmRamanujanLargePrimeSectorEnergy ε P :=
  div_nonneg (pmCompleteHeadEnergy_eq_compensation hP ε).2
    (pmRamanujanLargePrimeSectorEnergy_nonneg ε P)

/-- The amplitude mismatch is at most the square root of the compensation defect. -/
theorem abs_one_sub_pmCompensationAmplitude_le_sqrt (ε : ℝ) {P : ℕ} (hP : 2 ≤ P) :
    |1 - pmCompensationAmplitude ε P| ≤ Real.sqrt (compensationDefect ε P) := by
  rw [← Real.sqrt_sq_eq_abs]
  refine Real.sqrt_le_sqrt ?_
  have := pmTransverseEnergy_div_nonneg ε hP
  simp only [compensationDefect]
  linarith

/-- **The amplitude converges at rate `log⁻³P`.** -/
theorem exists_abs_one_sub_pmCompensationAmplitude_le {ε : ℝ} (hε : 0 < ε) (hεhalf : ε < 1 / 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ P : ℕ in atTop,
      |1 - pmCompensationAmplitude ε P| ≤ K / Real.log P ^ 3 := by
  obtain ⟨K, hK⟩ := exists_compensationDefect_le_inv_log_pow_six hε hεhalf
  refine ⟨Real.sqrt |K|, Real.sqrt_nonneg _, ?_⟩
  filter_upwards [hK, eventually_ge_atTop 2] with P hP hP2
  have hlog : 0 < Real.log P := Real.log_pos (by exact_mod_cast (by omega : 1 < P))
  refine (abs_one_sub_pmCompensationAmplitude_le_sqrt ε hP2).trans ?_
  have hsq : Real.sqrt (Real.log P ^ 6) = Real.log P ^ 3 := by
    rw [show Real.log P ^ 6 = (Real.log P ^ 3) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  calc Real.sqrt (compensationDefect ε P) ≤ Real.sqrt (|K| / Real.log P ^ 6) :=
        Real.sqrt_le_sqrt (hP.trans (div_le_div_of_nonneg_right (le_abs_self K) (by positivity)))
    _ = Real.sqrt |K| / Real.log P ^ 3 := by rw [Real.sqrt_div' _ (by positivity), hsq]

/-- **The connection term is summable.** The compensation amplitude has bounded variation over the
dyadic scales. -/
theorem summable_abs_pmCompensationAmplitude_dyadic_sub {ε : ℝ} (hε : 0 < ε) (hεhalf : ε < 1 / 2) :
    Summable fun k : ℕ =>
      |pmCompensationAmplitude ε (2 ^ (k + 1)) - pmCompensationAmplitude ε (2 ^ k)| := by
  obtain ⟨K, hK0, hK⟩ := exists_abs_one_sub_pmCompensationAmplitude_le hε hεhalf
  have h2 : Tendsto (fun k : ℕ => 2 ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine Summable.of_norm_bounded_eventually_nat
    (g := fun k : ℕ => 2 * K / Real.log 2 ^ 3 * (1 / (k : ℝ) ^ 3))
    ((Real.summable_one_div_nat_pow.mpr (by norm_num)).mul_left _) ?_
  filter_upwards [h2.eventually hK, (h2.comp (tendsto_add_atTop_nat 1)).eventually hK,
    eventually_ge_atTop 1] with k hk hk' hk1
  simp only [Function.comp_apply] at hk'
  have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hlog : ∀ j : ℕ, Real.log ((2 ^ j : ℕ) : ℝ) = j * Real.log 2 := fun j => by
    simp [Real.log_pow]
  have hmono : K / Real.log ((2 ^ (k + 1) : ℕ) : ℝ) ^ 3 ≤ K / ((k : ℝ) * Real.log 2) ^ 3 := by
    rw [hlog]
    refine div_le_div_of_nonneg_left hK0 (by positivity) (pow_le_pow_left₀ (by positivity) ?_ 3)
    push_cast
    nlinarith
  rw [Real.norm_eq_abs, abs_abs]
  calc |pmCompensationAmplitude ε (2 ^ (k + 1)) - pmCompensationAmplitude ε (2 ^ k)|
      = |(1 - pmCompensationAmplitude ε (2 ^ k)) - (1 - pmCompensationAmplitude ε (2 ^ (k + 1)))| := by
        ring_nf
    _ ≤ |1 - pmCompensationAmplitude ε (2 ^ k)| + |1 - pmCompensationAmplitude ε (2 ^ (k + 1))| :=
        abs_sub _ _
    _ ≤ K / ((k : ℝ) * Real.log 2) ^ 3 + K / ((k : ℝ) * Real.log 2) ^ 3 := by
        refine add_le_add ?_ (hk'.trans hmono)
        have := hk
        rwa [hlog] at this
    _ = 2 * K / Real.log 2 ^ 3 * (1 / (k : ℝ) ^ 3) := by field_simp; ring

/-- The relative transverse energies are summable over the dyadic scales. -/
theorem summable_pmTransverseEnergy_div_sectorEnergy_dyadic {ε : ℝ} (hε : 0 < ε)
    (hεhalf : ε < 1 / 2) :
    Summable fun k : ℕ =>
      pmTransverseEnergy ε (2 ^ k) / pmRamanujanLargePrimeSectorEnergy ε (2 ^ k) := by
  refine Summable.of_norm_bounded_eventually_nat (summable_compensationDefect_dyadic hε hεhalf) ?_
  filter_upwards [eventually_ge_atTop 1] with k hk1
  have hk2 : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk1
  rw [Real.norm_eq_abs, abs_of_nonneg (pmTransverseEnergy_div_nonneg ε hk2), compensationDefect]
  linarith [sq_nonneg (1 - pmCompensationAmplitude ε (2 ^ k))]

end GaloisForLFunctions.ArithmeticCompensationTheory
