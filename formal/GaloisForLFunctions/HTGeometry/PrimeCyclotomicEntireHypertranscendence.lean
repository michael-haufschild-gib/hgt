import GaloisForLFunctions.HTGeometry.MahlerCoefficientFieldConfinement
import GaloisForLFunctions.HTGeometry.LogSuperlacunaryDoubleExponentialFamily

/-!
# Entire prime-cyclotomic hypertranscendental function

Primitive roots of injective prime orders, scaled by `1 / n!`, define an entire function.  Mahler
coefficient-field confinement proves this function hypertranscendental while its Taylor coefficient
norms agree termwise with those of `exp`.
-/

open Filter PowerSeries
open scoped Topology ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

def inverseFactorialRational (n : ℕ) : ℚ := (Nat.factorial n : ℚ)⁻¹

theorem inverseFactorialRational_ne_zero (n : ℕ) : inverseFactorialRational n ≠ 0 := by
  simp [inverseFactorialRational, Nat.factorial_ne_zero]

def primeCyclotomicFactorialCoeff (u : ℕ → ℂ) (n : ℕ) : ℂ :=
  (inverseFactorialRational n : ℂ) * u n

theorem norm_eq_one_of_isPrimitiveRoot_complex {p : ℕ} (hp : 0 < p) {u : ℂ}
    (hu : IsPrimitiveRoot u p) : ‖u‖ = 1 := by
  have hpow : ‖u‖ ^ p = 1 := by
    rw [← norm_pow, hu.pow_eq_one, norm_one]
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h := pow_lt_one₀ (norm_nonneg u) hlt (by omega : p ≠ 0)
    linarith
  · have h := one_lt_pow₀ hgt (by omega : p ≠ 0)
    linarith

theorem norm_primeCyclotomicFactorialCoeff
    (p : ℕ → ℕ) (u : ℕ → ℂ) (hp : ∀ n, (p n).Prime)
    (hu : ∀ n, IsPrimitiveRoot (u n) (p n)) (n : ℕ) :
    ‖primeCyclotomicFactorialCoeff u n‖ = (Nat.factorial n : ℝ)⁻¹ := by
  rw [primeCyclotomicFactorialCoeff, norm_mul,
    norm_eq_one_of_isPrimitiveRoot_complex (hp n).pos (hu n), mul_one]
  simp [inverseFactorialRational]

theorem primeCyclotomicFactorialCoeff_ne_zero
    (p : ℕ → ℕ) (u : ℕ → ℂ) (hp : ∀ n, (p n).Prime)
    (hu : ∀ n, IsPrimitiveRoot (u n) (p n)) (n : ℕ) :
    primeCyclotomicFactorialCoeff u n ≠ 0 := by
  apply mul_ne_zero
  · exact_mod_cast inverseFactorialRational_ne_zero n
  · exact (hu n).ne_zero (hp n).ne_zero

theorem primeCyclotomicFactorialCoeff_ratio_tendsto
    (p : ℕ → ℕ) (u : ℕ → ℂ) (hp : ∀ n, (p n).Prime)
    (hu : ∀ n, IsPrimitiveRoot (u n) (p n)) :
    Tendsto (fun n => ‖primeCyclotomicFactorialCoeff u n.succ‖ /
      ‖primeCyclotomicFactorialCoeff u n‖) atTop (𝓝 0) := by
  have hbase : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    simpa [one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  convert hbase using 1
  funext n
  rw [norm_primeCyclotomicFactorialCoeff p u hp hu,
    norm_primeCyclotomicFactorialCoeff p u hp hu, Nat.factorial_succ]
  push_cast
  field_simp

def primeCyclotomicFactorialFunction (u : ℕ → ℂ) : ℂ → ℂ :=
  FormalMultilinearSeries.ofScalarsSum (primeCyclotomicFactorialCoeff u)

theorem primeCyclotomicFactorialFunction_eq_tsum (u : ℕ → ℂ) (z : ℂ) :
    primeCyclotomicFactorialFunction u z =
      ∑' n, primeCyclotomicFactorialCoeff u n * z ^ n := by
  simpa [primeCyclotomicFactorialFunction, smul_eq_mul] using
    (FormalMultilinearSeries.ofScalars_sum_eq (primeCyclotomicFactorialCoeff u) z)

theorem primeCyclotomicFactorialSeries_radius_eq_top
    (p : ℕ → ℕ) (u : ℕ → ℂ) (hp : ∀ n, (p n).Prime)
    (hu : ∀ n, IsPrimitiveRoot (u n) (p n)) :
    (FormalMultilinearSeries.ofScalars ℂ (primeCyclotomicFactorialCoeff u)).radius = ⊤ := by
  exact FormalMultilinearSeries.ofScalars_radius_eq_top_of_tendsto ℂ
    (primeCyclotomicFactorialCoeff u)
    (Eventually.of_forall (primeCyclotomicFactorialCoeff_ne_zero p u hp hu))
    (primeCyclotomicFactorialCoeff_ratio_tendsto p u hp hu)

theorem contDiff_primeCyclotomicFactorialFunction
    (p : ℕ → ℕ) (u : ℕ → ℂ) (hp : ∀ n, (p n).Prime)
    (hu : ∀ n, IsPrimitiveRoot (u n) (p n)) :
    ContDiff ℂ (⊤ : ℕ∞) (primeCyclotomicFactorialFunction u) := by
  let q := FormalMultilinearSeries.ofScalars ℂ (primeCyclotomicFactorialCoeff u)
  have hr : q.radius = ⊤ := primeCyclotomicFactorialSeries_radius_eq_top p u hp hu
  have hq : HasFPowerSeriesOnBall q.sum q 0 q.radius :=
    q.hasFPowerSeriesOnBall (by rw [hr]; simp)
  have ha : AnalyticOnNhd ℂ q.sum Set.univ := by
    simpa [hr] using hq.analyticOnNhd
  exact ha.contDiff

theorem coeff_taylorPS_primeCyclotomicFactorialFunction
    (p : ℕ → ℕ) (u : ℕ → ℂ) (hp : ∀ n, (p n).Prime)
    (hu : ∀ n, IsPrimitiveRoot (u n) (p n)) (n : ℕ) :
    PowerSeries.coeff n (GaloisForLFunctions.taylorPS
      (primeCyclotomicFactorialFunction u)) =
      (inverseFactorialRational n : ℂ) * u n := by
  exact GaloisForLFunctions.taylorPS_ofScalarsSum_of_radius_eq_top
    (primeCyclotomicFactorialCoeff u)
    (primeCyclotomicFactorialSeries_radius_eq_top p u hp hu) n

/-- Exact fixed-modulus law: Taylor coefficient norms agree termwise with formal `exp`. -/
theorem norm_coeff_taylorPS_primeCyclotomicFactorialFunction_eq_exp
    (p : ℕ → ℕ) (u : ℕ → ℂ) (hp : ∀ n, (p n).Prime)
    (hu : ∀ n, IsPrimitiveRoot (u n) (p n)) (n : ℕ) :
    ‖PowerSeries.coeff n (GaloisForLFunctions.taylorPS
      (primeCyclotomicFactorialFunction u))‖ =
      ‖PowerSeries.coeff n (PowerSeries.exp ℂ)‖ := by
  rw [coeff_taylorPS_primeCyclotomicFactorialFunction p u hp hu,
    PowerSeries.coeff_exp]
  change ‖primeCyclotomicFactorialCoeff u n‖ = _
  rw [norm_primeCyclotomicFactorialCoeff p u hp hu]
  simp [norm_inv]

theorem hypertranscendental_primeCyclotomicFactorialFunction
    (p : ℕ → ℕ) (u : ℕ → ℂ) (hp_inj : Function.Injective p)
    (hp : ∀ n, (p n).Prime) (hu : ∀ n, IsPrimitiveRoot (u n) (p n)) :
    GaloisForLFunctions.Hypertranscendental (primeCyclotomicFactorialFunction u) := by
  apply hypertranscendental_of_taylorPS_scaledCyclotomic
    p u inverseFactorialRational hp_inj hp hu inverseFactorialRational_ne_zero
    (contDiff_primeCyclotomicFactorialFunction p u hp hu)
  exact coeff_taylorPS_primeCyclotomicFactorialFunction p u hp hu

end

end GaloisForLFunctions.HTGeometry
