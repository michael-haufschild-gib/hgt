import GaloisForLFunctions.BiScaleUncertainty.FirstOrderEnergyCollar
import GaloisForLFunctions.BiScaleUncertainty.ControlledClosedCycleRecovery

/-!
# Exact finite-accuracy cycle recovery on the logarithmic zero grid

The first-order collar and squared-increment modulus give the specified
exponents eight and 128. The normalized grid tail requires radius
32 times energy divided by squared accuracy and the fixed Levy coefficient.
-/

noncomputable section
open MeasureTheory Set
open scoped CompactlySupported
open RHTower.ArchimedeanAnomaly
namespace GaloisForLFunctions.BiScaleUncertainty.EnergyCycle
set_option autoImplicit false

/-- The logarithmic zero grid gives the exact half-accuracy tail at the stated radius. -/
theorem grid_correlation_tail_le_half {E ε R : ℝ} (f : LevyEnergySource E)
    (hε : 0 < ε) (hR : 1 ≤ R)
    (hRE : 32 * E / (Real.exp (-(1 / 2 : ℝ)) * ε ^ 2) ≤ R)
    (hz : ∀ k : ℕ, 2 ≤ k → f.correlation (Real.log (k : ℝ)) = 0)
    {x : ℝ} (hx : R ≤ |x|) : |f.correlation x| ≤ ε / 2 := by
  let c := Real.exp (-(1 / 2 : ℝ))
  have hc : 0 < c := Real.exp_pos _
  have hε2 := sq_pos_of_pos hε
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hzero : ∀ k : ℕ, 2 ≤ k → autocorr f.source (Real.log (k : ℝ)) = 0 := by
    intro k hk
    have he := hz k hk
    change autocorr f.source (Real.log (k : ℝ)) / autocorr f.source 0 = 0 at he
    exact (div_eq_zero_iff.mp he).resolve_right f.mass_pos.ne'
  have hb := normalized_autocorr_sq_mul_abs_location_le_of_infinite_grid
    f.smooth f.source.hasCompactSupport f.mass_pos hzero x
  change c * |x| * (f.correlation x) ^ 2 ≤ 8 * normalizedArchEnergy f.source at hb
  have hbE := hb.trans (mul_le_mul_of_nonneg_left f.energy_le (by norm_num))
  have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hx hc.le)
    (sq_nonneg (f.correlation x))
  have he : 32 * E ≤ R * (c * ε ^ 2) :=
    (div_le_iff₀ (mul_pos hc hε2)).mp hRE
  have hbudget : 8 * E ≤ (c * R) * (ε / 2) ^ 2 := by nlinarith only [he]
  have hs : (f.correlation x) ^ 2 ≤ (ε / 2) ^ 2 :=
    (mul_le_mul_iff_right₀ (mul_pos hc hRp)).mp ((hm.trans hbE).trans hbudget)
  nlinarith only [hs, sq_abs (f.correlation x), abs_nonneg (f.correlation x), hε]

/-- At the stated mesh width each source contributes at most one quarter of the target error. -/
theorem correlation_quarter_accuracy {E ε : ℝ} (f : LevyEnergySource E) (hε : 0 < ε)
    {x y : ℝ}
    (hxy : |x - y| ≤ Real.exp (-1 - 128 * E /
      (Real.exp (-(1 / 2 : ℝ)) * ε ^ 2))) :
    |f.correlation x - f.correlation y| ≤ ε / 4 := by
  apply correlation_close_closed f (by positivity : 0 < ε / 4)
  rwa [continuityRadius_quarter_eq (energyCeiling_nonneg f)]

/-- Exact global recovery with separate pair and spoke discrepancies and explicit grid-tail constants. -/
theorem grid_finite_cycle_recovery_exact {E ε R : ℝ} (f g : LevyEnergySource E)
    (hε : 0 < ε) (hR : 1 ≤ R)
    (hRE : 32 * E / (Real.exp (-(1 / 2 : ℝ)) * ε ^ 2) ≤ R)
    (n : ℕ) (hn : R ≤ ((n : ℝ) + 1) * firstOrderCollarRadius E)
    (hfz : ∀ k : ℕ, 2 ≤ k → f.correlation (Real.log (k : ℝ)) = 0)
    (hgz : ∀ k : ℕ, 2 ≤ k → g.correlation (Real.log (k : ℝ)) = 0)
    (x : ℝ) :
    let η := Real.exp (-1 - 128 * E / (Real.exp (-(1 / 2 : ℝ)) * ε ^ 2))
    |f.correlation x - g.correlation x| ≤
      max ε ((2 : ℝ) ^ (n + 1) *
        (spokeMeshError f g R η n + ((n : ℝ) + 1) * pairMeshError f g R η n) + ε / 2) := by
  dsimp only
  let η := Real.exp (-1 - 128 * E / (Real.exp (-(1 / 2 : ℝ)) * ε ^ 2))
  by_cases hx : |x| ≤ R
  · have hb := controlled_window_recovery f g (zero_le_one.trans hR)
      (Real.exp_pos _ : 0 < η) (by norm_num : (0 : ℝ) < 1 / 2) n hn
      (fun _ ht => (correlation_firstOrderCollar f ht).le)
      (fun _ ht => (correlation_firstOrderCollar g ht).le)
      (fun _ => ε / 4)
      (fun _ _ ht => correlation_quarter_accuracy f hε ht)
      (fun _ _ ht => correlation_quarter_accuracy g hε ht) hx
    have he :
        (spokeMeshError f g R η n + ((n : ℝ) + 1) * pairMeshError f g R η n /
          (2 * (1 / 2))) / (1 / 2 : ℝ) ^ (n + 1) + 2 * (ε / 4) =
        (2 : ℝ) ^ (n + 1) *
          (spokeMeshError f g R η n + ((n : ℝ) + 1) * pairMeshError f g R η n) + ε / 2 := by
      norm_num only [show (2 : ℝ) * (1 / 2) = 1 by norm_num, div_one, div_pow, one_pow]
      rw [div_div_eq_mul_div, div_one]
      ring
    rw [he] at hb
    exact hb.trans (le_max_right _ _)
  · have hf := grid_correlation_tail_le_half f hε hR hRE hfz (le_of_not_ge hx)
    have hg := grid_correlation_tail_le_half g hε hR hRE hgz (le_of_not_ge hx)
    exact ((abs_sub _ _).trans (by linarith only [hf, hg])).trans (le_max_left _ _)

/-- The same explicit estimate controls the literal uniform norm of the actual correlations. -/
theorem grid_finite_cycle_recovery_norm_exact {E ε R : ℝ} (f g : LevyEnergySource E)
    (hε : 0 < ε) (hR : 1 ≤ R)
    (hRE : 32 * E / (Real.exp (-(1 / 2 : ℝ)) * ε ^ 2) ≤ R)
    (n : ℕ) (hn : R ≤ ((n : ℝ) + 1) * firstOrderCollarRadius E)
    (hfz : ∀ k : ℕ, 2 ≤ k → f.correlation (Real.log (k : ℝ)) = 0)
    (hgz : ∀ k : ℕ, 2 ≤ k → g.correlation (Real.log (k : ℝ)) = 0) :
    let η := Real.exp (-1 - 128 * E / (Real.exp (-(1 / 2 : ℝ)) * ε ^ 2))
    ‖f.complexCorrelation - g.complexCorrelation‖ ≤
      max ε ((2 : ℝ) ^ (n + 1) *
        (spokeMeshError f g R η n + ((n : ℝ) + 1) * pairMeshError f g R η n) + ε / 2) := by
  dsimp only
  apply BoundedContinuousFunction.norm_le_of_nonempty.mpr
  intro x
  change ‖(f.correlation x : ℂ) - (g.correlation x : ℂ)‖ ≤ _
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact grid_finite_cycle_recovery_exact f g hε hR hRE n hn hfz hgz x

end GaloisForLFunctions.BiScaleUncertainty.EnergyCycle
