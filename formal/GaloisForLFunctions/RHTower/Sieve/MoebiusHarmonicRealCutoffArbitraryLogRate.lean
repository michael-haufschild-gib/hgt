import GaloisForLFunctions.RHTower.Sieve.MoebiusHarmonicArbitraryLogRate
import GaloisForLFunctions.RHTower.Sieve.MoebiusDoubleLogRealCutoff

/-!
# Arbitrary logarithmic decay at real cutoffs

The natural-floor interpolation of the Möbius harmonic partial sum retains every fixed
inverse-logarithmic rate.  This is the endpoint term in the binomial expansion of shifted
log-power kernels.
-/

open Filter Topology

namespace RHTower.Sieve

noncomputable section

/-- Every fixed real-cutoff logarithmic power kills the Möbius harmonic partial sum. -/
theorem tendsto_log_pow_mul_deningerHarmonicPartial_natFloor_zero (q : ℕ) :
    Tendsto (fun Y : ℝ => Real.log Y ^ q *
      RHTower.deningerHarmonicPartial ⌊Y⌋₊) atTop (nhds 0) := by
  have hfloor : Tendsto (fun Y : ℝ => ⌊Y⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop
  have hcore :=
    (tendsto_log_pow_mul_deningerHarmonicPartial_zero q).comp hfloor
  have hratio : Tendsto
      (fun Y : ℝ => Real.log Y / Real.log (⌊Y⌋₊ : ℝ)) atTop (nhds 1) := by
    have h := tendsto_log_natFloor_div_log_one.inv₀ (by norm_num)
    simpa [div_eq_mul_inv, mul_comm] using h
  have hmul := (hratio.pow q).mul hcore
  simp only [one_pow, one_mul] at hmul
  refine hmul.congr' ?_
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with Y hY
  have hfloor2 : 2 ≤ ⌊Y⌋₊ := Nat.le_floor (by exact_mod_cast hY)
  have hlogFloor : Real.log (⌊Y⌋₊ : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hfloor2)).ne'
  change (Real.log Y / Real.log (⌊Y⌋₊ : ℝ)) ^ q *
      (Real.log (⌊Y⌋₊ : ℝ) ^ q *
        RHTower.deningerHarmonicPartial ⌊Y⌋₊) = _
  rw [div_pow]
  field_simp [hlogFloor]

end

end RHTower.Sieve
