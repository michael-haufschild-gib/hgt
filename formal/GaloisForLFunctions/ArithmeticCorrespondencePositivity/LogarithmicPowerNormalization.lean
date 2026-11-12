import GaloisForLFunctions.ArithmeticCorrespondencePositivity.StrictPowerGrowthHasAnOpenMellinHalfPlane
import GaloisForLFunctions.RHTower.BurnolCoPoissonGeneralSeedMellin

/-!
# Discrete and continuous power normalizations on logarithmic coordinates

The co-Poisson floor estimate bounds the difference between the two
negative powers by one additional inverse power. Strict growth of the
source then makes the normalized staircase error bounded and vanishing.
-/

noncomputable section

open Complex Filter Topology

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

/-- Difference between normalizing at the integer cutoff and at `exp u`. -/
def logarithmicPowerNormalizationError (f : ℕ → ℝ) (θ u : ℝ) : ℂ :=
  stepLaplaceIntegrand (fun N => (N : ℝ) ^ (-θ) * f N) 0 u -
    stepLaplaceIntegrand f (θ : ℂ) u

private theorem floor_negative_power_error
    {θ X : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (hX : 1 ≤ X) :
    |(⌊X⌋₊ : ℝ) ^ (-θ) - X ^ (-θ)| ≤
      2 * θ * (⌊X⌋₊ : ℝ) ^ (-θ - 1) := by
  have hN : (1 : ℝ) ≤ ⌊X⌋₊ := by
    exact_mod_cast (Nat.le_floor (by simpa only [Nat.cast_one] using hX) : 1 ≤ ⌊X⌋₊)
  have hnorm : ‖((-θ : ℝ) : ℂ)‖ = θ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_nonneg hθ]
  have hb := _root_.RHTower.norm_cpow_natFloor_sub_cpow_le
    (s := ((-θ : ℝ) : ℂ)) hX (by rw [hnorm]; exact hθ1.trans hN)
  calc
    _ = ‖(((⌊X⌋₊ : ℝ) ^ (-θ) : ℝ) : ℂ) - ((X ^ (-θ) : ℝ) : ℂ)‖ := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    _ = ‖((⌊X⌋₊ : ℝ) : ℂ) ^ ((-θ : ℝ) : ℂ) - (X : ℂ) ^ ((-θ : ℝ) : ℂ)‖ := by
      rw [Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_cpow (zero_le_one.trans hX)]
    _ ≤ 2 * ‖((-θ : ℝ) : ℂ)‖ * (⌊X⌋₊ : ℝ) ^ (((-θ : ℝ) : ℂ).re - 1) := hb
    _ = _ := by rw [hnorm, ofReal_re]

private theorem logarithmicPowerNormalizationError_eq (f : ℕ → ℝ) (θ u : ℝ) :
    logarithmicPowerNormalizationError f θ u =
      (((((⌊Real.exp u⌋₊ : ℝ) ^ (-θ) - (Real.exp u) ^ (-θ)) *
        f ⌊Real.exp u⌋₊ : ℝ)) : ℂ) := by
  have he : Complex.exp (-(θ : ℂ) * (u : ℂ)) =
      (((Real.exp u) ^ (-θ) : ℝ) : ℂ) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos u), Real.log_exp, Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  simp only [logarithmicPowerNormalizationError, stepLaplaceIntegrand,
    neg_zero, zero_mul, Complex.exp_zero, one_mul]
  rw [he]
  push_cast
  ring

/-- The normalization error decays by a half power of the integer cutoff. -/
theorem exists_decay_bound_logarithmicPowerNormalizationError
    {f : ℕ → ℝ} {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hf : _root_.HTGeometry.StrictNaturalPowerGrowth f θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, 0 < u →
      ‖logarithmicPowerNormalizationError f θ u‖ ≤ C * (⌊Real.exp u⌋₊ : ℝ) ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨B, hB, hb⟩ := hf (1 / 2) (by norm_num)
  refine ⟨2 * θ * B, by positivity, fun u hu => ?_⟩
  have hX : 1 ≤ Real.exp u := Real.one_le_exp hu.le
  have hN : 1 ≤ ⌊Real.exp u⌋₊ := Nat.le_floor
    (by simpa only [Nat.cast_one] using hX)
  have hN0 : (0 : ℝ) < ⌊Real.exp u⌋₊ := by exact_mod_cast hN
  rw [logarithmicPowerNormalizationError_eq, Complex.norm_real, Real.norm_eq_abs, abs_mul]
  calc
    _ ≤ (2 * θ * (⌊Real.exp u⌋₊ : ℝ) ^ (-θ - 1)) *
        (B * (⌊Real.exp u⌋₊ : ℝ) ^ (θ + 1 / 2)) :=
      mul_le_mul (floor_negative_power_error hθ hθ1 hX) (hb _ hN) (abs_nonneg _)
        (by positivity)
    _ = (2 * θ * B) * ((⌊Real.exp u⌋₊ : ℝ) ^ (-θ - 1) *
        (⌊Real.exp u⌋₊ : ℝ) ^ (θ + 1 / 2)) := by ring
    _ = _ := by
      rw [← Real.rpow_add hN0]
      congr 2
      ring

/-- Strict growth makes the change of normalization vanish on logarithmic coordinates. -/
theorem tendsto_logarithmicPowerNormalizationError_zero
    {f : ℕ → ℝ} {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hf : _root_.HTGeometry.StrictNaturalPowerGrowth f θ) :
    Tendsto (logarithmicPowerNormalizationError f θ) atTop (𝓝 0) := by
  obtain ⟨C, _, hb⟩ := exists_decay_bound_logarithmicPowerNormalizationError hθ hθ1 hf
  have hfloor : Tendsto (fun x : ℝ => ⌊x⌋₊) atTop atTop := by
    apply tendsto_atTop.mpr
    intro N
    filter_upwards [eventually_ge_atTop (N : ℝ)] with x hx
    exact Nat.le_floor hx
  have hN := (tendsto_natCast_atTop_atTop (R := ℝ)).comp (hfloor.comp Real.tendsto_exp_atTop)
  have htail := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp hN).const_mul C
  rw [mul_zero] at htail
  apply squeeze_zero_norm' _ htail
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with u hu
  exact hb u (zero_lt_one.trans_le hu)

/-- The same error is uniformly bounded on the positive logarithmic axis. -/
theorem exists_bound_logarithmicPowerNormalizationError
    {f : ℕ → ℝ} {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hf : _root_.HTGeometry.StrictNaturalPowerGrowth f θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, 0 < u →
      ‖logarithmicPowerNormalizationError f θ u‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := exists_decay_bound_logarithmicPowerNormalizationError hθ hθ1 hf
  refine ⟨C, hC, fun u hu => (hb u hu).trans ?_⟩
  have hN : (1 : ℝ) ≤ ⌊Real.exp u⌋₊ := by
    exact_mod_cast (Nat.le_floor
      (by simpa only [Nat.cast_one] using Real.one_le_exp hu.le) : 1 ≤ ⌊Real.exp u⌋₊)
  have hp := Real.rpow_le_rpow_of_exponent_le hN
    (by norm_num : -(1 / 2 : ℝ) ≤ 0)
  rw [Real.rpow_zero] at hp
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hp hC

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
