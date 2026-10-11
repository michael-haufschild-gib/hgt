import GaloisForLFunctions.RHTower.WeilLogShiftTransportCorrectionLimit
import GaloisForLFunctions.RHTower.WeilLogShiftMixtureLogTransport

/-! Uniform first transport correction across the entire canonical probability fiber. -/

open Filter Topology

noncomputable section
namespace RHTower

def finiteWeilMixtureLogTransportCorrection (r k : ℕ) (a b : Set.Icc (0 : ℝ) 1) : ℝ :=
  (((k + 2 : ℕ) : ℝ) / ((r + 1 : ℕ) : ℝ)) *
    (|(a : ℝ) - (b : ℝ)| - ((k + 2 : ℕ) : ℝ) *
      finiteWeilCouplingCost (finiteWeilMixtureCoupling r k a b)
        (fun u v => |finiteWeilClusterLogNodes r k u - finiteWeilClusterLogNodes r k v|))

theorem finiteWeilMixtureLogTransportCorrection_eq (r k : ℕ) (a b : Set.Icc (0 : ℝ) 1) :
    finiteWeilMixtureLogTransportCorrection r k a b =
      |(a : ℝ) - (b : ℝ)| * finiteWeilCanonicalLogTransportCorrection r k := by
  rw [finiteWeilMixtureLogTransportCorrection, finiteWeilMixtureCoupling_log_cost,
    finiteWeilCanonicalLogTransportCorrection]
  ring

theorem finiteWeilMixtureLogTransportCorrection_quadratic_bound (r t : ℕ)
    (a b : Set.Icc (0 : ℝ) 1) :
    |finiteWeilMixtureLogTransportCorrection r (2 * (r + 1) ^ 2 + t) a b -
      |(a : ℝ) - (b : ℝ)| / 2| ≤
        4 * (Real.sqrt ((((r + 1 : ℕ) : ℝ) + 1) / 2) / ((r + 1 : ℕ) : ℝ)) := by
  have hd : |(a : ℝ) - (b : ℝ)| ≤ 1 := by
    apply abs_le.mpr
    constructor
    · linarith only [a.property.1, b.property.2]
    · linarith only [a.property.2, b.property.1]
  have hid : finiteWeilMixtureLogTransportCorrection r (2 * (r + 1) ^ 2 + t) a b -
      |(a : ℝ) - (b : ℝ)| / 2 = |(a : ℝ) - (b : ℝ)| *
        (finiteWeilCanonicalLogTransportCorrection r (2 * (r + 1) ^ 2 + t) - 1 / 2) := by
    rw [finiteWeilMixtureLogTransportCorrection_eq]
    ring
  rw [hid, abs_mul, abs_abs]
  calc
    _ ≤ |(a : ℝ) - (b : ℝ)| *
        (4 * (Real.sqrt ((((r + 1 : ℕ) : ℝ) + 1) / 2) / ((r + 1 : ℕ) : ℝ))) :=
      mul_le_mul_of_nonneg_left (finiteWeilCanonicalLogTransportCorrection_quadratic_bound r t)
        (abs_nonneg _)
    _ ≤ 1 * (4 * (Real.sqrt ((((r + 1 : ℕ) : ℝ) + 1) / 2) / ((r + 1 : ℕ) : ℝ))) :=
      mul_le_mul_of_nonneg_right hd (by positivity)
    _ = _ := one_mul _

theorem tendsto_finiteWeilMixtureLogTransportCorrection_error_zero (t : ℕ → ℕ)
    (a b : ℕ → Set.Icc (0 : ℝ) 1) :
    Tendsto (fun r : ℕ => finiteWeilMixtureLogTransportCorrection r (2 * (r + 1) ^ 2 + t r) (a r) (b r) -
      |(a r : ℝ) - (b r : ℝ)| / 2) atTop (𝓝 (0 : ℝ)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [sub_zero, Real.norm_eq_abs]
  apply squeeze_zero (fun r => abs_nonneg _)
    (fun r => finiteWeilMixtureLogTransportCorrection_quadratic_bound r (t r) (a r) (b r))
  have h := tendsto_finiteWeil_midpoint_binomial_error.const_mul (2 : ℝ)
  simpa only [mul_zero, ← mul_assoc, show (2 : ℝ) * 2 = 4 by norm_num] using h

end RHTower
