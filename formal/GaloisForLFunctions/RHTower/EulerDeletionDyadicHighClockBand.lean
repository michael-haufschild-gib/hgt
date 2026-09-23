import GaloisForLFunctions.RHTower.EulerDeletionHighClockLayerTail

noncomputable section
set_option autoImplicit false
open Finset MeasureTheory Filter Topology
namespace RHTower.DeletionResidueMartingale

theorem tendsto_cube_div_clock_zero :
    Tendsto (fun L : ℕ => (L : ℝ) ^ 3 / (clock L : ℝ)) atTop (𝓝 0) := by
  have h4 : Tendsto (fun L : ℕ => (L : ℝ) ^ 4 / (2 : ℝ) ^ L) atTop (𝓝 0) :=
    tendsto_pow_const_div_const_pow_of_one_lt 4 (by norm_num)
  have h3 : Tendsto (fun L : ℕ => (L : ℝ) ^ 3 / (2 : ℝ) ^ L) atTop (𝓝 0) :=
    tendsto_pow_const_div_const_pow_of_one_lt 3 (by norm_num)
  have hmaj : Tendsto
      (fun L : ℕ => ((L : ℝ) ^ 4 + (L : ℝ) ^ 3) / (2 : ℝ) ^ L)
      atTop (𝓝 0) := by
    simpa only [add_div, add_zero] using h4.add h3
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmaj
  · exact Filter.Eventually.of_forall fun L => by positivity
  · exact Filter.Eventually.of_forall fun L => by
      have hC : (0 : ℝ) < clock L := Nat.cast_pos.mpr (clock_pos L)
      have htwo : (0 : ℝ) < (2 : ℝ) ^ L := pow_pos (by norm_num) L
      have hpow : (2 : ℝ) ^ L ≤ ((L : ℝ) + 1) * (clock L : ℝ) := by
        exact_mod_cast two_pow_le_mul_clock L
      apply (div_le_div_iff₀ hC htwo).2
      calc
        (L : ℝ) ^ 3 * (2 : ℝ) ^ L ≤
            (L : ℝ) ^ 3 * (((L : ℝ) + 1) * (clock L : ℝ)) :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
        _ = ((L : ℝ) ^ 4 + (L : ℝ) ^ 3) * (clock L : ℝ) := by ring

theorem predictableDrift_dyadic_upperHalf_energy_le (L : ℕ) :
    (∑ l ∈ Ico L (2 * L),
      ‖historyLayer l (predictableDrift (2 * L))‖ ^ (2 : ℕ)) ≤
      (L : ℝ) * (32 * (L : ℝ) ^ 2 + 2) / ((clock L : ℝ) + 1) := by
  have hterm (l : ℕ) (hl : l ∈ Ico L (2 * L)) :
      ‖historyLayer l (predictableDrift (2 * L))‖ ^ (2 : ℕ) ≤
        (32 * (L : ℝ) ^ 2 + 2) / ((clock L : ℝ) + 1) := by
    have hbounds := Finset.mem_Ico.mp hl
    have hE := predictableDrift_layer_energy_le_clock_tail (2 * L) l hbounds.2
    have hcNat : clock L ≤ clock l :=
      Nat.le_of_dvd (clock_pos l) (clock_dvd hbounds.1)
    have hc : ((clock L : ℝ) + 1) ≤ ((clock l : ℝ) + 1) := by
      exact_mod_cast (Nat.add_le_add_right hcNat 1)
    have hnum : 0 ≤ 32 * (L : ℝ) ^ 2 + 2 := by positivity
    calc
      _ ≤ (8 * ((2 * L : ℕ) : ℝ) ^ 2 + 2) / ((clock l : ℝ) + 1) := hE
      _ = (32 * (L : ℝ) ^ 2 + 2) / ((clock l : ℝ) + 1) := by push_cast; ring
      _ ≤ (32 * (L : ℝ) ^ 2 + 2) / ((clock L : ℝ) + 1) :=
        div_le_div_of_nonneg_left hnum (by positivity) hc
  calc
    _ ≤ ∑ _l ∈ Ico L (2 * L),
          (32 * (L : ℝ) ^ 2 + 2) / ((clock L : ℝ) + 1) :=
        Finset.sum_le_sum hterm
    _ = (L : ℝ) * (32 * (L : ℝ) ^ 2 + 2) / ((clock L : ℝ) + 1) := by
      simp [Nat.card_Ico, show 2 * L - L = L by omega]
      ring

theorem predictableDrift_dyadic_upperHalf_energy_tendsto_zero :
    Tendsto
      (fun L : ℕ => ∑ l ∈ Ico L (2 * L),
        ‖historyLayer l (predictableDrift (2 * L))‖ ^ (2 : ℕ))
      atTop (𝓝 0) := by
  have hupper : Tendsto (fun L : ℕ =>
      34 * ((L : ℝ) ^ 3 / (clock L : ℝ))) atTop (𝓝 0) := by
    simpa using tendsto_cube_div_clock_zero.const_mul (34 : ℝ)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · exact Filter.Eventually.of_forall fun L => Finset.sum_nonneg (fun l hl =>
      pow_nonneg (norm_nonneg _) _)
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with L hL
    have hLreal : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
    have hLsq : (1 : ℝ) ≤ (L : ℝ) ^ 2 := by nlinarith
    have hLcube : (L : ℝ) ≤ (L : ℝ) ^ 3 := by
      nlinarith [mul_nonneg (show 0 ≤ (L : ℝ) by positivity)
        (show 0 ≤ (L : ℝ) ^ 2 - 1 by linarith)]
    have hnum : (L : ℝ) * (32 * (L : ℝ) ^ 2 + 2) ≤ 34 * (L : ℝ) ^ 3 := by
      nlinarith
    have hC : (0 : ℝ) < clock L := Nat.cast_pos.mpr (clock_pos L)
    calc
      _ ≤ (L : ℝ) * (32 * (L : ℝ) ^ 2 + 2) / ((clock L : ℝ) + 1) :=
        predictableDrift_dyadic_upperHalf_energy_le L
      _ ≤ 34 * (L : ℝ) ^ 3 / ((clock L : ℝ) + 1) :=
        div_le_div_of_nonneg_right hnum (by positivity)
      _ ≤ 34 * (L : ℝ) ^ 3 / (clock L : ℝ) :=
        div_le_div_of_nonneg_left (by positivity) hC (by linarith)
      _ = 34 * ((L : ℝ) ^ 3 / (clock L : ℝ)) := by ring

end RHTower.DeletionResidueMartingale
