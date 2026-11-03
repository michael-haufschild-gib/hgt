import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheConductorDecompositionHoldsOnAGrowingRange
import GaloisForLFunctions.ArithmeticDegenerationTheory.TheScalingFormOfTheDegeneration
import GaloisForLFunctions.CompletedArithmeticForms.CompleteWeilResidualLevelOfDistribution

/-!
# The count form ends at the resolution

How far can the conductor range `M(N)` of the critical-curve decomposition be pushed? The twisted
direction of conductor `m` carries the conductor energy `E_m(c)` of the complete tilted-spline matrix,
and `E_m(c) = J(m) c^{−7} R_m(c/m)` exactly (`rpow_seven_mul_completedConductorEnergy_eq_scaling`):
the count `J(m)c^{−7}` times the scaling function at the ratio of the resolution `c` to the conductor.
The count ratio `ρ_N(m) = c⁷E_m(c)/J(m) = R_m(c/m)` (`countRatio_eq`) decides:

* **Below the resolution the count form is uniform** (`eventually_abs_countRatio_sub_one_le`): if
  `M(N)/c_N → 0`, then `sup_{m ≤ M(N)} |ρ_N(m) − 1| → 0`.
* **At a multiple of the resolution it fails** (`exists_countRatio_le_half`): there is `λ₀` with
  `ρ ≤ ½` whenever `m ≥ λ₀ c`; along the critical curve `c_N = o(N)`, so for `M(N) = N` the count form
  fails at the conductor `N` (`eventually_countRatio_conductor_le_half`). The count description of
  the twisted directions holds exactly on the range `m = o(c_N)`, `c_N = (K log N)^{1/8}`.
* **What survives up to `N^θ`** (`tendsto_criticalCurve_quasimodes`): along the critical curve, for
  every `θ < ½`, the normalized Ramanujan horizon vectors of all conductors `m ≤ N^θ` are collective
  quasimodes of the complete matrix with the positive eigenvalues `E_m(c) = J(m)c^{−7}R_m(c/m)` —
  the orthogonal decomposition persists with the counts replaced by the scaled counts.
-/

noncomputable section

open Finset Filter Topology

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open SpacingScaleHarmonicAnalysis RenormalizedArithmeticPotentialTheory
  RenormalizedArithmeticPotentialTheory.CompletedShell ArithmeticDegenerationTheory

/-- The count ratio `c⁷E_m(c)/J(m)` of conductor `m` at resolution `c`. -/
def countRatio (c : ℝ) (m : ℕ) : ℝ :=
  c ^ (7 : ℝ) * completedConductorEnergy tiltedUnitSpline c m / jordanCoefficient m

/-- The count ratio is the scaling function at `c/m`. -/
theorem countRatio_eq {c : ℝ} (hc : 0 < c) {m : ℕ} (hm : 0 < m) :
    countRatio c m = scalingFunction m (c / m) := by
  rw [countRatio, rpow_seven_mul_completedConductorEnergy_eq_scaling hc hm,
    mul_div_cancel_left₀ _ (jordanCoefficient_pos hm).ne']

/-- **Below the resolution the count form is uniform**: if `M(N)/c_N → 0`, then for every `ε > 0`,
eventually `|c⁷E_m(c)/J(m) − 1| ≤ ε` for all conductors `1 ≤ m ≤ M(N)`. -/
theorem eventually_abs_countRatio_sub_one_le {c : ℕ → ℝ} (hc : ∀ N, 0 < c N) {M : ℕ → ℕ}
    (hM : Tendsto (fun N => (M N : ℝ) / c N) atTop (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ m : ℕ, 0 < m → m ≤ M N → |countRatio (c N) m - 1| ≤ ε := by
  obtain ⟨X, hX1, hX⟩ := abs_scalingFunction_sub_one_le hε
  have hX0 : 0 < X := lt_of_lt_of_le one_pos hX1
  filter_upwards [hM.eventually (gt_mem_nhds (inv_pos.mpr hX0))] with N hN m hm hmM
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hcN := hc N
  rw [countRatio_eq hcN hm]
  refine hX m hm _ ?_
  have hmM' : (m : ℝ) ≤ M N := by exact_mod_cast hmM
  have h1 : (m : ℝ) / c N < X⁻¹ := lt_of_le_of_lt (div_le_div_of_nonneg_right hmM' hcN.le) hN
  rw [div_lt_iff₀ hcN] at h1
  rw [le_div_iff₀ hm0]
  have := mul_lt_mul_of_pos_left h1 hX0
  rw [mul_inv_cancel_left₀ hX0.ne'] at this
  linarith

/-- **At a multiple of the resolution the count form fails**: `c⁷E_m(c)/J(m) ≤ ½` once `m ≥ λ₀c`. -/
theorem exists_countRatio_le_half :
    ∃ L : ℝ, 0 < L ∧ ∀ c : ℝ, 0 < c → ∀ m : ℕ, 0 < m → L * c ≤ m → countRatio c m ≤ 1 / 2 := by
  obtain ⟨C, hC0, hC⟩ := scalingFunction_le
  refine ⟨2 * C + 1, by positivity, fun c hc m hm hLm => ?_⟩
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  rw [countRatio_eq hc hm]
  have hx : c / m ≤ 1 / (2 * C + 1) := by
    rw [div_le_div_iff₀ hm0 (by positivity)]
    linarith
  calc scalingFunction m (c / m) ≤ C * (c / m) := hC m _ (by positivity)
    _ ≤ C * (1 / (2 * C + 1)) := mul_le_mul_of_nonneg_left hx hC0
    _ ≤ 1 / 2 := by
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith

/-- **The count form cannot be pushed to `N`**: along the critical curve, eventually the conductor
`m = N` has count ratio `≤ ½`. -/
theorem eventually_countRatio_conductor_le_half {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) {K : ℝ}
    (hK : 0 < K) (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 K)) :
    ∀ᶠ N : ℕ in atTop, 0 < N ∧ countRatio (c N) N ≤ 1 / 2 := by
  obtain ⟨L, hL, hLe⟩ := exists_countRatio_le_half
  obtain ⟨-, hclog⟩ := criticalCurve_facts hc1 hK hcrit
  have hcN := tendsto_div_of_log_sq hc1 hclog
  filter_upwards [hcN.eventually (gt_mem_nhds (inv_pos.mpr hL)), eventually_ge_atTop 1] with N hN hN1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  refine ⟨hN1, hLe (c N) (by linarith [hc1 N]) N hN1 ?_⟩
  rw [div_lt_iff₀ hN0] at hN
  have := mul_lt_mul_of_pos_left hN hL
  rw [mul_inv_cancel_left₀ hL.ne'] at this
  linarith

/-- The count ratio on the full range `1 ≤ m ≤ N` does not converge uniformly to `1`. -/
theorem not_uniform_countRatio_up_to_N {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) {K : ℝ} (hK : 0 < K)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 K)) :
    ¬ ∀ᶠ N : ℕ in atTop, ∀ m : ℕ, 0 < m → m ≤ N → |countRatio (c N) m - 1| ≤ 1 / 4 := by
  intro h
  obtain ⟨N, hN, hN'⟩ := ((eventually_countRatio_conductor_le_half hc1 hK hcrit).and h).exists
  have := hN' N hN.1 le_rfl
  rw [abs_le] at this
  linarith [hN.2, this.1]

/-- Along the critical curve the overlap is below `√log N`. -/
theorem tendsto_sq_div_log_of_criticalCurve {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) {K : ℝ}
    (hK : 0 < K) (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 K)) :
    Tendsto (fun N : ℕ => c N ^ 2 / Real.log N) atTop (𝓝 0) := by
  obtain ⟨hcinf, -⟩ := criticalCurve_facts hc1 hK hcrit
  -- `c² / log N = (c⁸ / log N) · c⁻⁶`
  have h6 : Tendsto (fun N : ℕ => (c N ^ 6)⁻¹) atTop (𝓝 0) :=
    (tendsto_pow_atTop (by norm_num : (6 : ℕ) ≠ 0)).comp hcinf |>.inv_tendsto_atTop
  have := hcrit.mul h6
  rw [mul_zero] at this
  refine this.congr fun N => ?_
  have hc0 : c N ≠ 0 := by linarith [hc1 N]
  field_simp

/-- **The exact decomposition up to `N^θ` along the critical curve**: for every `θ < ½` the
normalized Ramanujan horizon vectors of the conductors `m ≤ N^θ` are collective quasimodes of the
complete tilted-spline matrix with eigenvalues `E_m(c)`, and `c⁷E_m(c) = J(m)R_m(c/m) ≥ 0`. -/
theorem tendsto_criticalCurve_quasimodes {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) {K : ℝ} (hK : 0 < K)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 K)) {θ : ℝ} (hθ0 : 0 < θ)
    (hθ : θ < 1 / 2) :
    Tendsto (fun N : ℕ =>
      (∑ m ∈ Icc 1 ⌊(N : ℝ) ^ θ⌋₊,
        ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N)
            (normalizedRamanujanHorizonVector m N) -
          completedConductorEnergy tiltedUnitSpline (c N) m • normalizedRamanujanHorizonVector m N‖ ^ 2) /
      (∑ m ∈ Icc 1 ⌊(N : ℝ) ^ θ⌋₊, completedConductorEnergy tiltedUnitSpline (c N) m ^ 2))
      atTop (𝓝 0) :=
  CompletedArithmeticForms.tendsto_completeWeil_residual_levelOfDistribution contDiff_tiltedUnitSpline
    tiltedUnitSpline_support integral_tiltedUnitSpline_sq_pos hθ0 hθ (Eventually.of_forall hc1)
    (tendsto_sq_div_log_of_criticalCurve hc1 hK hcrit)

/-- The eigenvalue of conductor `m` is the scaled count `J(m)c^{−7}R_m(c/m)`, and it is positive
for the twisted directions as for the untwisted one. -/
theorem completedConductorEnergy_eq_scaledCount {c : ℝ} (hc : 0 < c) {m : ℕ} (hm : 0 < m) :
    completedConductorEnergy tiltedUnitSpline c m =
      jordanCoefficient m * c ^ (-(7 : ℝ)) * scalingFunction m (c / m) ∧
    0 ≤ completedConductorEnergy tiltedUnitSpline c m := by
  have h := rpow_seven_mul_completedConductorEnergy_eq_scaling hc hm
  refine ⟨?_, ?_⟩
  · rw [show jordanCoefficient m * c ^ (-(7 : ℝ)) * scalingFunction m (c / m) =
      c ^ (-(7 : ℝ)) * (jordanCoefficient m * scalingFunction m (c / m)) by ring, ← h, ← mul_assoc,
      ← Real.rpow_add hc]
    norm_num
  · have hR := scalingFunction_nonneg m (div_pos hc (by exact_mod_cast hm : (0 : ℝ) < m)).le
    have hJ := (jordanCoefficient_pos hm).le
    have hpos : 0 ≤ c ^ (7 : ℝ) * completedConductorEnergy tiltedUnitSpline c m := by
      rw [h]; exact mul_nonneg hJ hR
    exact (mul_nonneg_iff_of_pos_left (Real.rpow_pos_of_pos hc _)).mp hpos

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
