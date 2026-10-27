import GaloisForLFunctions.BiScaleUncertainty.FirstOrderEnergyCollar
import GaloisForLFunctions.BiScaleUncertainty.QuadraticPerturbedNodes

/-!
# Stability of actual correlation samples under node perturbation

Physical node errors become logarithmic sampling errors. The singular-energy
modulus controls the actual normalized source correlations in both directions.
A fixed jump from zero to one half forces logarithmic energy growth.
-/

noncomputable section
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm
namespace GaloisForLFunctions.BiScaleUncertainty
open FiniteHorizon EnergyCycle
set_option autoImplicit false

/-- The specified quadratic displacement has the exact uniform continuum sampling modulus. -/
theorem quadratic_correlation_samples_close {E δ : ℝ} (f : LevyEnergySource E)
    (hδ : 0 < δ) (hδ1 : δ < 1 / 4) {N n : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) :
    |f.correlation (quadraticPerturbedLogNode δ N n) - f.correlation (Real.log (n : ℝ))| ≤
      Real.sqrt (8 * E / (Real.exp (-(1 / 2 : ℝ)) * (-Real.log (δ / (N : ℝ))))) := by
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast (hn.trans hnN)
  have hN0 : (0 : ℝ) < N := zero_lt_one.trans_le hN
  apply correlation_logarithmic_modulus f (div_pos hδ hN0)
    ((div_lt_one hN0).mpr (by linarith only [hN, hδ1]))
  have hd := quadraticPerturbedLogNode_displacement hδ.le hn hnN
  rw [abs_of_nonneg hd.1]
  exact hd.2

/-- Exact integer-grid constraints give quantified approximate constraints on the perturbed grid. -/
theorem quadratic_correlation_of_integer_zero {E δ : ℝ} (f : LevyEnergySource E)
    (hδ : 0 < δ) (hδ1 : δ < 1 / 4) {N n : ℕ} (hn : 2 ≤ n) (hnN : n ≤ N)
    (hz : f.correlation (Real.log (n : ℝ)) = 0) :
    |f.correlation (quadraticPerturbedLogNode δ N n)| ≤
      Real.sqrt (8 * E / (Real.exp (-(1 / 2 : ℝ)) * (-Real.log (δ / (N : ℝ))))) := by
  simpa only [hz, sub_zero] using quadratic_correlation_samples_close f hδ hδ1
    (show 1 ≤ n by omega) hnN

/-- Exact perturbed constraints give the same quantified integer-grid defect for the same source. -/
theorem integer_correlation_of_quadratic_zero {E δ : ℝ} (f : LevyEnergySource E)
    (hδ : 0 < δ) (hδ1 : δ < 1 / 4) {N n : ℕ} (hn : 2 ≤ n) (hnN : n ≤ N)
    (hz : f.correlation (quadraticPerturbedLogNode δ N n) = 0) :
    |f.correlation (Real.log (n : ℝ))| ≤
      Real.sqrt (8 * E / (Real.exp (-(1 / 2 : ℝ)) * (-Real.log (δ / (N : ℝ))))) := by
  simpa only [hz, zero_sub, abs_neg] using quadratic_correlation_samples_close f hδ hδ1
    (show 1 ≤ n by omega) hnN

/-- A zero-to-half correlation jump at small separation has an explicit logarithmic energy cost. -/
theorem correlation_zero_half_energy_barrier {E x y : ℝ} (f : LevyEnergySource E)
    (hd : 0 < |x - y|) (hd1 : |x - y| ≤ 1)
    (hx : f.correlation x = 1 / 2) (hy : f.correlation y = 0) :
    Real.exp (-(1 / 2 : ℝ)) * (-Real.log |x - y|) / 32 ≤ E := by
  have hb := normalized_autocorr_difference_sq_mul_log_le
    f.smooth f.source.hasCompactSupport f.mass_pos hd hd1
  change Real.exp (-(1 / 2 : ℝ)) * (-Real.log |x - y|) *
    (f.correlation x - f.correlation y) ^ 2 ≤ 8 * normalizedArchEnergy f.source at hb
  rw [hx, hy] at hb
  have he := f.energy_le
  nlinarith only [hb, he]

/-- In the quadratic model, a half-sized violation forces the stated horizon-dependent energy cost. -/
theorem quadratic_correlation_half_energy_barrier {E δ : ℝ} (f : LevyEnergySource E)
    (hδ : 0 < δ) (hδ1 : δ < 1 / 4) {N n : ℕ} (hn : 2 ≤ n) (hnN : n ≤ N)
    (hz : f.correlation (Real.log (n : ℝ)) = 0)
    (hp : f.correlation (quadraticPerturbedLogNode δ N n) = 1 / 2) :
    Real.exp (-(1 / 2 : ℝ)) * (-Real.log (δ / (N : ℝ))) / 32 ≤ E := by
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hN0 := zero_lt_one.trans_le hN
  have hd := quadraticPerturbedLogNode_displacement hδ.le (by omega : 1 ≤ n) hnN
  have hdiff : quadraticPerturbedLogNode δ N n ≠ Real.log (n : ℝ) := by
    intro he
    rw [he, hz] at hp
    norm_num at hp
  have habs : 0 < |quadraticPerturbedLogNode δ N n - Real.log (n : ℝ)| :=
    abs_pos.mpr (sub_ne_zero.mpr hdiff)
  have hbound : |quadraticPerturbedLogNode δ N n - Real.log (n : ℝ)| ≤ δ / (N : ℝ) := by
    rw [abs_of_nonneg hd.1]
    exact hd.2
  have hsmall : δ / (N : ℝ) < 1 := (div_lt_one hN0).mpr (by linarith only [hN, hδ1])
  have hb := correlation_zero_half_energy_barrier f habs (hbound.trans hsmall.le) hp hz
  have hl := neg_le_neg (Real.log_le_log habs hbound)
  exact (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hl (Real.exp_pos _).le) (by norm_num)).trans hb

end GaloisForLFunctions.BiScaleUncertainty
