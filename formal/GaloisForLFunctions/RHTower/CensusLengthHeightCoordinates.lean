import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.OverlapCoordinates
import Zeta23.Defs

/-!
# Exact length and height coordinates for the census parameters

The census parameter uses height `T/(2π)`: its cutoff is `(T/(2π))^λ`.
Relative to physical height `T`, overlap is `(T/(2π))^(λ-1)/(2π)`.
Consequently bandwidth one and atomic touching differ by an exact constant;
their logarithmic exponents agree only asymptotically.
-/

noncomputable section

set_option autoImplicit false

open Filter Topology Zeta23

namespace GaloisForLFunctions.SpacingScaleHarmonicAnalysis.LengthHeight

/-- The cutoff in the actual census parameter structure retains the factor `2π`. -/
theorem census_length_eq_rpow (P : Params) {T : ℝ} (hT : 0 < T) :
    P.X T = (T / (2 * Real.pi)) ^ P.lam := by
  rw [Real.rpow_def_of_pos (div_pos hT (by positivity))]
  unfold Params.X Params.L Zeta23.l
  congr 1
  ring

/-- Exact physical overlap of a census test. -/
theorem census_overlap_eq (P : Params) {T : ℝ} (hT : 0 < T) :
    overlap (P.X T) T = (T / (2 * Real.pi)) ^ (P.lam - 1) / (2 * Real.pi) := by
  have hC : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  rw [census_length_eq_rpow P hT,
    Real.rpow_sub (div_pos hT (by positivity)), Real.rpow_one]
  dsimp only [overlap]
  field_simp

/-- Bandwidth is exactly the census parameter when measured against normalized height. -/
theorem census_normalized_bandwidth (P : Params) {T : ℝ} (hT : 2 * Real.pi < T) :
    bandwidth (P.X T) (T / (2 * Real.pi)) = P.lam := by
  have hC : (0 : ℝ) < 2 * Real.pi := by positivity
  rw [census_length_eq_rpow P (hC.trans hT)]
  exact bandwidth_rpow ((one_lt_div hC).mpr hT) P.lam

/-- Physical bandwidth includes a finite-height normalization correction. -/
theorem census_physical_bandwidth (P : Params) {T : ℝ} (hT : 1 < T) :
    bandwidth (P.X T) T = P.lam * (1 - Real.log (2 * Real.pi) / Real.log T) := by
  rw [bandwidth, Params.X, Real.log_exp, Params.L, Zeta23.l,
    Real.log_div (zero_lt_one.trans hT).ne' (by positivity : (2 * Real.pi : ℝ) ≠ 0)]
  field_simp [(Real.log_pos hT).ne']

theorem tendsto_census_physical_bandwidth (P : Params) :
    Tendsto (fun T : ℝ => bandwidth (P.X T) T) atTop (𝓝 P.lam) := by
  have hr : Tendsto (fun T : ℝ => Real.log (2 * Real.pi) / Real.log T) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have h : Tendsto (fun T : ℝ => P.lam * (1 - Real.log (2 * Real.pi) / Real.log T))
      atTop (𝓝 P.lam) := by
    have h1 : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    simpa only [sub_zero, mul_one] using
      (h1.sub hr).const_mul P.lam
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
  exact (census_physical_bandwidth P hT).symm

/-- The physical touching boundary is not exactly census bandwidth one. -/
theorem census_overlap_le_one_iff (P : Params) {T : ℝ} (hT : 2 * Real.pi < T) :
    overlap (P.X T) T ≤ 1 ↔ P.lam ≤ Real.log T / Real.log (T / (2 * Real.pi)) := by
  have hC : (0 : ℝ) < 2 * Real.pi := by positivity
  have hT0 := hC.trans hT
  have hb : 1 < T / (2 * Real.pi) := (one_lt_div hC).mpr hT
  rw [overlap_le_one_iff hT0, Params.X,
    ← Real.log_le_log_iff (Real.exp_pos (P.L T)) hT0,
    Real.log_exp, Params.L, Zeta23.l, le_div_iff₀ (Real.log_pos hb)]

theorem census_overlap_at_bandwidth_one (P : Params) (hlam : P.lam = 1)
    {T : ℝ} (hT : 0 < T) : overlap (P.X T) T = 1 / (2 * Real.pi) := by
  rw [census_overlap_eq P hT, hlam, sub_self, Real.rpow_zero]

/-- At census bandwidth `4/3`, physical overlap has power `1/3` with its exact constant. -/
theorem census_overlap_at_four_thirds (P : Params) (hlam : P.lam = 4 / 3)
    {T : ℝ} (hT : 0 < T) :
    overlap (P.X T) T = (T / (2 * Real.pi)) ^ (1 / 3 : ℝ) / (2 * Real.pi) := by
  rw [census_overlap_eq P hT, hlam]
  congr 2
  ring

end GaloisForLFunctions.SpacingScaleHarmonicAnalysis.LengthHeight

#print axioms GaloisForLFunctions.SpacingScaleHarmonicAnalysis.LengthHeight.census_overlap_eq
#print axioms GaloisForLFunctions.SpacingScaleHarmonicAnalysis.LengthHeight.census_overlap_le_one_iff
#print axioms GaloisForLFunctions.SpacingScaleHarmonicAnalysis.LengthHeight.census_overlap_at_four_thirds
