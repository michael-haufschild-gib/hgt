import GaloisForLFunctions.RHTower.EulerDeletionGeneralHighClockBand

/-!
# The predictable Möbius drift localizes below a logarithmic clock threshold

In the residue-martingale model of Euler deletion, the predictable drift
`predictableDrift N = ∑_{i < N} μ(i+1) P_i(residue_{i+1})` decomposes orthogonally over the
history layers `P_{l+1} - P_l`, where `P_l` projects onto observables determined by residues
modulo `lcm(1, ..., l)`. With the threshold `K(N) = 5(⌊log₂(N + 1)⌋ + 1)`, the Chebyshev bound
`2^K ≤ (K + 1) lcm(1..K)` gives `(N + 1)^5 ≤ (K + 1) lcm(1..K)`. Hence the drift energy in the
layers `K(N) ≤ l < N` is at most `110/(N + 1)`, and it tends to `0`.

## Main results

- `logarithmicClockThreshold`: `K(N) = 5(⌊log₂(N + 1)⌋ + 1)`.
- `predictableDrift_logarithmic_highClock_energy_le`:
  `∑_{K(N) ≤ l < N} ‖historyLayer l (predictableDrift N)‖² ≤ 110/(N + 1)`.
- `predictableDrift_logarithmic_highClock_energy_tendsto_zero`: this energy tends to `0`.

## Hypotheses

All results are unconditional.
-/

noncomputable section
set_option autoImplicit false
open Finset MeasureTheory Filter Topology
namespace RHTower.DeletionResidueMartingale

/-- The logarithmic clock threshold `K(N) = 5(⌊log₂(N + 1)⌋ + 1)`. -/
def logarithmicClockThreshold (N : ℕ) : ℕ :=
  5 * (Nat.log2 (N + 1) + 1)

/-- The energy of `predictableDrift N` in the history layers `K(N) ≤ l < N` above the logarithmic clock
threshold is at most `110/(N + 1)`. -/
theorem predictableDrift_logarithmic_highClock_energy_le (N : ℕ) :
    (∑ l ∈ Ico (logarithmicClockThreshold N) N,
      ‖historyLayer l (predictableDrift N)‖ ^ (2 : ℕ)) ≤
      110 / (((N + 1 : ℕ) : ℝ)) := by
  let M := N + 1
  let H := Nat.log2 M + 1
  let K := logarithmicClockThreshold N
  have hMposNat : 1 ≤ M := by dsimp [M]; omega
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hMposNat
  have hNleM : (N : ℝ) ≤ M := by dsimp [M]; push_cast; linarith
  have hKdef : K = 5 * H := rfl
  have hMlt : M < 2 ^ H := by
    dsimp [H]
    exact Nat.lt_log2_self
  have hMpowNat : M ^ 5 ≤ 2 ^ K := by
    calc
      M ^ 5 ≤ (2 ^ H) ^ 5 := by gcongr
      _ = 2 ^ K := by rw [← pow_mul, hKdef]; congr 1; omega
  have hKboundNat : K + 1 ≤ 11 * M := by
    have hlog := Nat.log2_le_self (N + 1)
    change 5 * (Nat.log2 (N + 1) + 1) + 1 ≤ 11 * (N + 1)
    omega
  have hKbound : ((K : ℝ) + 1) ≤ 11 * (M : ℝ) := by
    exact_mod_cast hKboundNat
  have hclockNat : M ^ 5 ≤ (K + 1) * clock K :=
    hMpowNat.trans (two_pow_le_mul_clock K)
  have hclock : (M : ℝ) ^ 5 ≤ ((K : ℝ) + 1) * (clock K : ℝ) := by
    exact_mod_cast hclockNat
  have hMfour : (M : ℝ) ^ 4 ≤ 11 * (clock K : ℝ) := by
    apply (mul_le_mul_iff_left₀ hMpos).mp
    calc
      (M : ℝ) ^ 4 * (M : ℝ) = (M : ℝ) ^ 5 := by ring
      _ ≤ ((K : ℝ) + 1) * (clock K : ℝ) := hclock
      _ ≤ (11 * (M : ℝ)) * (clock K : ℝ) :=
        mul_le_mul_of_nonneg_right hKbound (by positivity)
      _ = (11 * (clock K : ℝ)) * (M : ℝ) := by ring
  have hspan : (((N - K : ℕ) : ℝ)) ≤ (M : ℝ) := by
    exact_mod_cast (show N - K ≤ M by dsimp [M]; omega)
  have hN2 : (N : ℝ) ^ 2 ≤ (M : ℝ) ^ 2 :=
    (sq_le_sq₀ (Nat.cast_nonneg (α := ℝ) N) hMpos.le).mpr hNleM
  have hM2 : (1 : ℝ) ≤ (M : ℝ) ^ 2 := by
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hMposNat
    nlinarith
  have hbracket : 8 * (N : ℝ) ^ 2 + 2 ≤ 10 * (M : ℝ) ^ 2 := by
    nlinarith
  have hnum : (((N - K : ℕ) : ℝ)) * (8 * (N : ℝ) ^ 2 + 2) ≤
      10 * (M : ℝ) ^ 3 := by
    calc
      _ ≤ (M : ℝ) * (8 * (N : ℝ) ^ 2 + 2) :=
        mul_le_mul_of_nonneg_right hspan (by positivity)
      _ ≤ (M : ℝ) * (10 * (M : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hbracket hMpos.le
      _ = 10 * (M : ℝ) ^ 3 := by ring
  have hC : (0 : ℝ) < (clock K : ℝ) + 1 := by positivity
  have hcross :
      (((N - K : ℕ) : ℝ)) * (8 * (N : ℝ) ^ 2 + 2) * (M : ℝ) ≤
        110 * ((clock K : ℝ) + 1) := by
    calc
      _ ≤ (10 * (M : ℝ) ^ 3) * (M : ℝ) :=
        mul_le_mul_of_nonneg_right hnum hMpos.le
      _ = 10 * (M : ℝ) ^ 4 := by ring
      _ ≤ 110 * (clock K : ℝ) := by
        nlinarith [hMfour]
      _ ≤ 110 * ((clock K : ℝ) + 1) := by linarith
  change (∑ l ∈ Ico K N,
    ‖historyLayer l (predictableDrift N)‖ ^ (2 : ℕ)) ≤ _
  calc
    _ ≤ (((N - K : ℕ) : ℝ)) * (8 * (N : ℝ) ^ 2 + 2) / ((clock K : ℝ) + 1) :=
      predictableDrift_highClock_band_energy_le N K
    _ ≤ 110 / (M : ℝ) := (div_le_div_iff₀ hC hMpos).mpr hcross
    _ = 110 / (((N + 1 : ℕ) : ℝ)) := rfl

/-- The energy of `predictableDrift N` above the logarithmic clock threshold tends to `0` as `N → ∞`. -/
theorem predictableDrift_logarithmic_highClock_energy_tendsto_zero :
    Tendsto
      (fun N : ℕ => ∑ l ∈ Ico (logarithmicClockThreshold N) N,
        ‖historyLayer l (predictableDrift N)‖ ^ (2 : ℕ))
      atTop (𝓝 0) := by
  have hupper : Tendsto
      (fun N : ℕ => 110 / (((N + 1 : ℕ) : ℝ))) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv, Nat.cast_add] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (110 : ℝ)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · exact Filter.Eventually.of_forall fun N => Finset.sum_nonneg (fun l hl =>
      pow_nonneg (norm_nonneg _) _)
  · exact Filter.Eventually.of_forall fun N =>
      predictableDrift_logarithmic_highClock_energy_le N

end RHTower.DeletionResidueMartingale
