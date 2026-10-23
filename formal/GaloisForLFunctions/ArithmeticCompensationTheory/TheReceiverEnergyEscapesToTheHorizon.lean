import GaloisForLFunctions.ArithmeticCompensationTheory.TheCompensationDefectDecaysLogarithmically
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheDampedMobiusCriticalEnergy

/-!
# A blow-up of the receiver escapes to the horizon

The blow-up architecture for the critical receiver asks: if `E_T(ε)` were unbounded, where does its
unit energy go once normalized? This file proves the first exclusion theorem of that programme,
for the actual damped Möbius receiver at `0 < ε < ½`, from the source bound
`|A_ε(n)| ≤ C n^{1−ε}` (`exists_abs_centredPrefix_le`, the damped divisor remainder read at the
integers).

* **The energy grows at most at the trivial rate.** `E_N(ε) ≤ D(1 + N^{1−2ε})` for every `N`
  (`exists_dampedMobiusEnergy_le`): each cell carries at most `C² n^{−2ε}`.
* **Low scales are excluded.** Either the receiver is admitted at `ε`, or for every `θ < 1` the
  energy at scales below `E_T(ε)^{θ/(1−2ε)}` is a vanishing fraction of `E_T(ε)`
  (`admits_or_escapesToHorizon`); in particular every fixed window, and every single cell, carries
  a vanishing fraction (`admits_or_fixedWindowEnergy_vanishes`).

So a critical defect profile of the actual receiver cannot concentrate at bounded scales or at any
scale polynomially below `E_T^{1/(1−2ε)}`: the normalized energy escapes to the horizon, at a rate
read off from the source bound. What remains for a contradiction is to classify the profiles that
do live at the horizon, with their arithmetic constraints retained.
-/

open Filter Topology Finset RHTower
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section

namespace GaloisForLFunctions.ArithmeticCompensationTheory

/-- **The source bound.** `|A_ε(n)| ≤ C n^{1−ε}` for every `n ≥ 1`, when `0 < ε < ½`. -/
theorem exists_abs_centredPrefix_le {ε : ℝ} (hε : 0 < ε) (hεhalf : ε < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n →
      |pmPowerDampedCenteredDivisorPrefix ε n| ≤ C * (n : ℝ) ^ (1 - ε) := by
  obtain ⟨C, hC, h⟩ := divisorRemainder_le_global hε hεhalf
  refine ⟨C, hC, fun n hn => ?_⟩
  have he := pmPowerDampedDivisorRemainder_eq_centered_prefix hε (Nat.cast_nonneg (α := ℝ) n)
  rw [Nat.floor_natCast, Int.fract_natCast, Complex.ofReal_zero, mul_zero, sub_zero] at he
  have hn' := h n hn
  rw [he, Complex.norm_real, Real.norm_eq_abs] at hn'
  exact hn'

/-- **The receiver energy grows at most at the trivial rate** `N^{1−2ε}`. -/
theorem exists_dampedMobiusEnergy_le {ε : ℝ} (hε : 0 < ε) (hεhalf : ε < 1 / 2) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ N : ℕ, dampedMobiusEnergy ε N ≤ D * (1 + (N : ℝ) ^ (1 - 2 * ε)) := by
  obtain ⟨C, hC, h⟩ := exists_abs_centredPrefix_le hε hεhalf
  have hd : 0 < 1 - 2 * ε := by linarith
  refine ⟨C ^ 2 * (1 + 1 / (1 - 2 * ε)), by positivity, fun N => ?_⟩
  have hcell : ∀ n ∈ Icc 1 N, pmPowerDampedCenteredDivisorPrefix ε n ^ 2 /
      ((n : ℝ) * ((n : ℝ) + 1)) ≤ C ^ 2 * (n : ℝ) ^ (-(2 * ε)) := by
    intro n hn
    have hn1 := (mem_Icc.mp hn).1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hb := h n hn1
    have hsq : pmPowerDampedCenteredDivisorPrefix ε n ^ 2 ≤ C ^ 2 * ((n : ℝ) ^ (1 - ε)) ^ 2 := by
      rw [← mul_pow]
      exact (sq_abs _).symm.le.trans (pow_le_pow_left₀ (abs_nonneg _) hb 2)
    have hw := rpow_sq_div_pronic_le (ε := ε) hn1
    calc pmPowerDampedCenteredDivisorPrefix ε n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))
        ≤ C ^ 2 * ((n : ℝ) ^ (1 - ε)) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) :=
          div_le_div_of_nonneg_right hsq (by positivity)
      _ = C ^ 2 * (((n : ℝ) ^ (1 - ε)) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) := by ring
      _ ≤ C ^ 2 * (n : ℝ) ^ (-2 * ε) := mul_le_mul_of_nonneg_left hw (by positivity)
      _ = C ^ 2 * (n : ℝ) ^ (-(2 * ε)) := by rw [neg_mul]
  have hsum := sum_rpow_neg_head_le (by positivity : 0 < 2 * ε) (by linarith : 2 * ε < 1) N
  have hpow : 0 ≤ (N : ℝ) ^ (1 - 2 * ε) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  calc dampedMobiusEnergy ε N
      = ∑ n ∈ Icc 1 N, pmPowerDampedCenteredDivisorPrefix ε n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) :=
        rfl
    _ ≤ ∑ n ∈ Icc 1 N, C ^ 2 * (n : ℝ) ^ (-(2 * ε)) := sum_le_sum hcell
    _ = C ^ 2 * ∑ n ∈ Icc 1 N, (n : ℝ) ^ (-(2 * ε)) := by rw [mul_sum]
    _ ≤ C ^ 2 * (1 + (N : ℝ) ^ (1 - 2 * ε) / (1 - 2 * ε)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ C ^ 2 * (1 + 1 / (1 - 2 * ε)) * (1 + (N : ℝ) ^ (1 - 2 * ε)) := by
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have h1 : (N : ℝ) ^ (1 - 2 * ε) / (1 - 2 * ε) = 1 / (1 - 2 * ε) * (N : ℝ) ^ (1 - 2 * ε) := by
          ring
        have h2 : 0 ≤ 1 / (1 - 2 * ε) := by positivity
        rw [h1]
        nlinarith [mul_nonneg h2 hpow]

/-- **Admitted or unbounded.** At every damping the receiver energy is either bounded uniformly in
the horizon or tends to infinity with it. -/
theorem admits_or_tendsto_atTop (ε : ℝ) :
    Admits dampedMobiusEnergy ε ∨ Tendsto (dampedMobiusEnergy ε) atTop atTop := by
  by_cases h : Admits dampedMobiusEnergy ε
  · exact Or.inl h
  · refine Or.inr ((dampedMobiusEnergy_mono ε).tendsto_atTop_atTop fun B => ?_)
    by_contra hB
    push Not at hB
    exact h ⟨B, fun T => (hB T).le⟩

/-- **The blow-up dichotomy.** At every damping `0 < ε < ½`, either the receiver is admitted, or
for every `θ < 1` the energy below the scale `E_T^{θ/(1−2ε)}` is a vanishing fraction of `E_T`:
a blow-up escapes to the horizon. -/
theorem admits_or_escapesToHorizon {ε : ℝ} (hε : 0 < ε) (hεhalf : ε < 1 / 2) :
    Admits dampedMobiusEnergy ε ∨ ∀ θ : ℝ, θ < 1 →
      Tendsto (fun T : ℕ => dampedMobiusEnergy ε ⌊dampedMobiusEnergy ε T ^ (θ / (1 - 2 * ε))⌋₊ /
        dampedMobiusEnergy ε T) atTop (𝓝 0) := by
  rcases admits_or_tendsto_atTop ε with h | hE
  · exact Or.inl h
  refine Or.inr fun θ hθ => ?_
  obtain ⟨D, hD, hbound⟩ := exists_dampedMobiusEnergy_le hε hεhalf
  have hd : 0 < 1 - 2 * ε := by linarith
  -- the majorant `D (1 + E^{max θ 0}) / E → 0`
  set θ' := max θ 0
  have hθ' : θ' < 1 := max_lt hθ one_pos
  have hmaj : Tendsto (fun T : ℕ => D * (1 + dampedMobiusEnergy ε T ^ θ') /
      dampedMobiusEnergy ε T) atTop (𝓝 0) := by
    have h1 : Tendsto (fun E : ℝ => D * (1 + E ^ θ') / E) atTop (𝓝 0) := by
      have ha : Tendsto (fun E : ℝ => D / E) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_id
      have hb : Tendsto (fun E : ℝ => D * E ^ (θ' - 1)) atTop (𝓝 0) := by
        simpa using (tendsto_rpow_neg_atTop (by linarith : 0 < 1 - θ')).const_mul D
          |>.congr fun E => by rw [show -(1 - θ') = θ' - 1 by ring]
      refine (ha.add hb).congr' ?_ |>.trans (by rw [add_zero])
      filter_upwards [eventually_gt_atTop 0] with E hE0
      rw [Real.rpow_sub hE0, Real.rpow_one]
      field_simp
    exact h1.comp hE
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [hE.eventually_gt_atTop 0] with T hT
    exact div_nonneg (dampedMobiusEnergy_nonneg _ _) hT.le
  · filter_upwards [hE.eventually_gt_atTop 1] with T hT
    set E := dampedMobiusEnergy ε T
    have hE0 : 0 < E := by linarith
    set M := ⌊E ^ (θ / (1 - 2 * ε))⌋₊
    have hM : (M : ℝ) ≤ E ^ (θ / (1 - 2 * ε)) := Nat.floor_le (Real.rpow_nonneg hE0.le _)
    have hMd : (M : ℝ) ^ (1 - 2 * ε) ≤ E ^ θ' := by
      calc (M : ℝ) ^ (1 - 2 * ε) ≤ (E ^ (θ / (1 - 2 * ε))) ^ (1 - 2 * ε) :=
            Real.rpow_le_rpow (Nat.cast_nonneg M) hM hd.le
        _ = E ^ θ := by rw [← Real.rpow_mul hE0.le]; field_simp
        _ ≤ E ^ θ' := Real.rpow_le_rpow_of_exponent_le (by linarith) (le_max_left θ 0)
    rw [div_le_div_iff_of_pos_right hE0]
    calc dampedMobiusEnergy ε M ≤ D * (1 + (M : ℝ) ^ (1 - 2 * ε)) := hbound M
      _ ≤ D * (1 + E ^ θ') := by gcongr

/-- **Fixed windows carry a vanishing fraction of a blow-up.** At every damping, either the receiver
is admitted, or the energy of every fixed window `[1, N]` — in particular of every single cell —
is a vanishing fraction of `E_T`. -/
theorem admits_or_fixedWindowEnergy_vanishes (ε : ℝ) :
    Admits dampedMobiusEnergy ε ∨ ∀ N : ℕ,
      Tendsto (fun T => dampedMobiusEnergy ε N / dampedMobiusEnergy ε T) atTop (𝓝 0) := by
  rcases admits_or_tendsto_atTop ε with h | hE
  · exact Or.inl h
  · exact Or.inr fun N => tendsto_const_nhds.div_atTop hE

end GaloisForLFunctions.ArithmeticCompensationTheory
