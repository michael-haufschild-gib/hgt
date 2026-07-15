import GaloisForLFunctions.HTGeometry.HarmonicResidueTransfer

/-!
# Complex harmonic residue transfer
-/

open Filter Topology Finset Asymptotics

namespace GaloisForLFunctions

noncomputable section

/-- A complex error tending to zero has harmonic weighted partial sums `o(log N)`. -/
theorem tendsto_complexHarmonicWeighted_error_zero {e : ℕ → ℂ}
    (he : Tendsto e atTop (nhds 0)) :
    Tendsto (fun N : ℕ =>
      (Real.log N)⁻¹ •
        (∑ n ∈ Finset.range N, (((n : ℝ) + 1)⁻¹ : ℝ) • e n))
      atTop (nhds 0) := by
  have heo : e =o[atTop] (fun _ : ℕ => (1 : ℝ)) :=
    (isLittleO_one_iff ℝ).2 he
  have hweightO : (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) =O[atTop]
      (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) := isBigO_refl _ _
  have heo' : (fun n : ℕ => (((n : ℝ) + 1)⁻¹ : ℝ) • e n) =o[atTop]
      (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) := by
    simpa only [one_div, smul_eq_mul, mul_one] using hweightO.smul_isLittleO heo
  have hweight : Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N, (1 : ℝ) / ((n : ℝ) + 1)) atTop atTop := by
    simpa [harmonic] using tendsto_harmonic_cast_atTop
  have hsum := heo'.sum_range (fun n => by positivity) hweight
  have hratio := hsum.tendsto_inv_smul_nhds_zero
  have hratio' : Tendsto (fun N : ℕ =>
      ((harmonic N : ℝ)⁻¹ : ℝ) •
        (∑ n ∈ Finset.range N, (((n : ℝ) + 1)⁻¹ : ℝ) • e n)) atTop (nhds 0) := by
    simpa [harmonic] using hratio
  have hproduct := tendsto_harmonic_div_log.smul hratio'
  simpa only [smul_zero] using hproduct.congr' (by
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hharm : (harmonic N : ℝ) ≠ 0 := by
      exact_mod_cast (harmonic_pos (by omega : N ≠ 0)).ne'
    have hlog : Real.log N ≠ 0 := (Real.log_pos (by exact_mod_cast hN)).ne'
    rw [smul_smul]
    congr 1
    field_simp)

end

end GaloisForLFunctions
