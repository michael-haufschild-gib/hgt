import GaloisForLFunctions.RHTower.EulerDeletionDyadicHighClockBand

/-!
# The predictable Möbius drift has vanishing energy in the upper half of the layers

Generalizes the dyadic high-clock band estimate to arbitrary bands. For `K ≤ N`, the energy of
the predictable Möbius drift `predictableDrift N` in the history layers `K ≤ l < N` is at most
`(N - K)(8N² + 2)/(lcm(1, ..., K) + 1)`. Taking `K = ⌊N/2⌋` and using
`L³ / lcm(1, ..., L) → 0`, the energy in the upper half of the layers tends to `0`.

## Main results

- `predictableDrift_highClock_band_energy_le`: the band bound
  `∑_{K ≤ l < N} ‖historyLayer l (predictableDrift N)‖² ≤ (N - K)(8N² + 2)/(lcm(1..K) + 1)`.
- `predictableDrift_upperHalf_band_energy_tendsto_zero`:
  `∑_{⌊N/2⌋ ≤ l < N} ‖historyLayer l (predictableDrift N)‖² → 0` as `N → ∞`.

## Hypotheses

All results are unconditional.
-/

noncomputable section
set_option autoImplicit false
open Finset MeasureTheory Filter Topology
namespace RHTower.DeletionResidueMartingale

/-- The energy of `predictableDrift N` in the history layers `K ≤ l < N` is at most
`(N - K)(8N² + 2)/(lcm(1, ..., K) + 1)`. -/
theorem predictableDrift_highClock_band_energy_le (N K : ℕ) :
    (∑ l ∈ Ico K N,
      ‖historyLayer l (predictableDrift N)‖ ^ (2 : ℕ)) ≤
      ((N - K : ℕ) : ℝ) * (8 * (N : ℝ) ^ 2 + 2) / ((clock K : ℝ) + 1) := by
  have hterm (l : ℕ) (hl : l ∈ Ico K N) :
      ‖historyLayer l (predictableDrift N)‖ ^ (2 : ℕ) ≤
        (8 * (N : ℝ) ^ 2 + 2) / ((clock K : ℝ) + 1) := by
    have hbounds := Finset.mem_Ico.mp hl
    have hE := predictableDrift_layer_energy_le_clock_tail N l hbounds.2
    have hcNat : clock K ≤ clock l :=
      Nat.le_of_dvd (clock_pos l) (clock_dvd hbounds.1)
    have hc : ((clock K : ℝ) + 1) ≤ ((clock l : ℝ) + 1) := by
      exact_mod_cast (Nat.add_le_add_right hcNat 1)
    exact hE.trans (div_le_div_of_nonneg_left (by positivity) (by positivity) hc)
  calc
    _ ≤ ∑ _l ∈ Ico K N,
          (8 * (N : ℝ) ^ 2 + 2) / ((clock K : ℝ) + 1) :=
        Finset.sum_le_sum hterm
    _ = ((N - K : ℕ) : ℝ) * (8 * (N : ℝ) ^ 2 + 2) / ((clock K : ℝ) + 1) := by
      simp [Nat.card_Ico]
      ring

/-- The energy of `predictableDrift N` in the upper half `⌊N/2⌋ ≤ l < N` of the history layers tends to `0`
as `N → ∞`. -/
theorem predictableDrift_upperHalf_band_energy_tendsto_zero :
    Tendsto
      (fun N : ℕ => ∑ l ∈ Ico (N / 2) N,
        ‖historyLayer l (predictableDrift N)‖ ^ (2 : ℕ))
      atTop (𝓝 0) := by
  have hdiv : Tendsto (fun N : ℕ => N / 2) atTop atTop := by
    apply Filter.tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop (2 * b)] with N hN
    omega
  have hupper : Tendsto
      (fun N : ℕ => 272 * ((((N / 2 : ℕ) : ℝ) ^ 3) / (clock (N / 2) : ℝ)))
      atTop (𝓝 0) := by
    simpa using (tendsto_cube_div_clock_zero.comp hdiv).const_mul (272 : ℝ)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · exact Filter.Eventually.of_forall fun N => Finset.sum_nonneg (fun l hl =>
      pow_nonneg (norm_nonneg _) _)
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
    let K := N / 2
    have hK : 1 ≤ K := by dsimp [K]; omega
    have hNbound : N ≤ 2 * (K + 1) := by dsimp [K]; omega
    have hspan : N - K ≤ K + 1 := by dsimp [K]; omega
    have hKdouble : K + 1 ≤ 2 * K := by omega
    have hNreal : (N : ℝ) ≤ 2 * (((K + 1 : ℕ) : ℝ)) := by exact_mod_cast hNbound
    have hspanReal : (((N - K : ℕ) : ℝ)) ≤ (((K + 1 : ℕ) : ℝ)) := by
      exact_mod_cast hspan
    have hKreal : (1 : ℝ) ≤ (((K + 1 : ℕ) : ℝ)) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le K)
    have hKdoubleReal : (((K + 1 : ℕ) : ℝ)) ≤ 2 * (K : ℝ) := by
      exact_mod_cast hKdouble
    have hNsq : (N : ℝ) ^ 2 ≤ 4 * ((((K + 1 : ℕ) : ℝ)) ^ 2) := by
      nlinarith [(sq_le_sq₀ (Nat.cast_nonneg (α := ℝ) N)
        (by positivity : 0 ≤ 2 * (((K + 1 : ℕ) : ℝ)))).mpr hNreal]
    have hKsq : (1 : ℝ) ≤ ((((K + 1 : ℕ) : ℝ)) ^ 2) := by nlinarith
    have hnum : 8 * (N : ℝ) ^ 2 + 2 ≤
        34 * ((((K + 1 : ℕ) : ℝ)) ^ 2) := by nlinarith
    have hprod : (((N - K : ℕ) : ℝ)) * (8 * (N : ℝ) ^ 2 + 2) ≤
        34 * ((((K + 1 : ℕ) : ℝ)) ^ 3) := by
      calc
        _ ≤ (((K + 1 : ℕ) : ℝ)) * (8 * (N : ℝ) ^ 2 + 2) :=
          mul_le_mul_of_nonneg_right hspanReal (by positivity)
        _ ≤ (((K + 1 : ℕ) : ℝ)) * (34 * ((((K + 1 : ℕ) : ℝ)) ^ 2)) :=
          mul_le_mul_of_nonneg_left hnum (by positivity)
        _ = 34 * ((((K + 1 : ℕ) : ℝ)) ^ 3) := by ring
    have hKcube : ((((K + 1 : ℕ) : ℝ)) ^ 3) ≤ (2 * (K : ℝ)) ^ 3 := by
      gcongr
    have hnum272 : (((N - K : ℕ) : ℝ)) * (8 * (N : ℝ) ^ 2 + 2) ≤
        272 * (K : ℝ) ^ 3 := by nlinarith
    have hC : (0 : ℝ) < clock K := Nat.cast_pos.mpr (clock_pos K)
    change (∑ l ∈ Ico K N, ‖historyLayer l (predictableDrift N)‖ ^ (2 : ℕ)) ≤ _
    calc
      _ ≤ (((N - K : ℕ) : ℝ)) * (8 * (N : ℝ) ^ 2 + 2) / ((clock K : ℝ) + 1) :=
        predictableDrift_highClock_band_energy_le N K
      _ ≤ 272 * (K : ℝ) ^ 3 / ((clock K : ℝ) + 1) :=
        div_le_div_of_nonneg_right hnum272 (by positivity)
      _ ≤ 272 * (K : ℝ) ^ 3 / (clock K : ℝ) :=
        div_le_div_of_nonneg_left (by positivity) hC (by linarith)
      _ = 272 * (((K : ℝ) ^ 3) / (clock K : ℝ)) := by ring

end RHTower.DeletionResidueMartingale
