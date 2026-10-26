import GaloisForLFunctions.BiScaleUncertainty.CompactCorrelationDerivativeBounds
import GaloisForLFunctions.BiScaleUncertainty.ControlledClosedCycleRecovery

/-!
# Derivative-controlled conditioning of literal closed-cycle observations

At an order at least normalized derivative energy times squared observation
radius, Bernoulli's inequality bounds both inner correlation powers below by
one half. The resulting noise amplification is linear in order.
-/

noncomputable section
open MeasureTheory Set
open scoped CompactlySupported
namespace GaloisForLFunctions.BiScaleUncertainty.EnergyCycle
set_option autoImplicit false

/-- The exact derivative order condition bounds each inner value and its entire power below one half. -/
theorem derivative_inner_power_ge_half (f : C_c(ℝ, ℝ))
    (hf : ContDiff ℝ 2 (f : ℝ → ℝ)) (hne : f ≠ 0) {B R x : ℝ}
    (hB : normalizedDirichletEnergy f ≤ B) (hx : |x| ≤ R) (n : ℕ)
    (hn : B * R ^ 2 ≤ (n : ℝ) + 1) :
    1 / 2 ≤ nyquistNormalizedCorrelation f (x / ((n : ℝ) + 1)) ∧
      1 / 2 ≤ nyquistNormalizedCorrelation f (x / ((n : ℝ) + 1)) ^ (n + 1) := by
  let k : ℝ := (n : ℝ) + 1
  have hk1 : 1 ≤ k := by
    have hn0 := Nat.cast_nonneg (α := ℝ) n
    dsimp only [k]
    linarith only [hn0]
  have hk : 0 < k := zero_lt_one.trans_le hk1
  have hB0 := (normalizedDirichletEnergy_nonneg f hne).trans hB
  have hR : 0 ≤ R := (abs_nonneg x).trans hx
  have hx2 : x ^ 2 ≤ R ^ 2 := by nlinarith only [hx, sq_abs x, abs_nonneg x, hR]
  have hprod : normalizedDirichletEnergy f * x ^ 2 ≤ B * R ^ 2 :=
    mul_le_mul hB hx2 (sq_nonneg x) hB0
  have hscale : normalizedDirichletEnergy f * (x / k) ^ 2 ≤ 1 / k := by
    calc
      _ = (normalizedDirichletEnergy f * x ^ 2) / k ^ 2 := by ring
      _ ≤ (B * R ^ 2) / k ^ 2 := div_le_div_of_nonneg_right hprod (sq_nonneg k)
      _ ≤ k / k ^ 2 := div_le_div_of_nonneg_right hn (sq_nonneg k)
      _ = _ := by field_simp [hk.ne']
  have ht0 : 0 ≤ 1 / (2 * k) := by positivity
  have htHalf : 1 / (2 * k) ≤ 1 / 2 := by
    apply (div_le_iff₀ (mul_pos (by norm_num) hk)).mpr
    nlinarith only [hk1]
  have hlower : 1 - 1 / (2 * k) ≤ nyquistNormalizedCorrelation f (x / k) := by
    have hb := nyquistNormalizedCorrelation_ge_one_sub_dirichlet f hf hne (x / k)
    have he : normalizedDirichletEnergy f * (x / k) ^ 2 / 2 ≤ 1 / (2 * k) := by
      calc
        _ ≤ (1 / k) / 2 := div_le_div_of_nonneg_right hscale (by norm_num : (0 : ℝ) ≤ 2)
        _ = _ := by ring
    linarith only [hb, he]
  have hvalue : 1 / 2 ≤ nyquistNormalizedCorrelation f (x / k) := by
    linarith only [hlower, htHalf]
  refine ⟨hvalue, ?_⟩
  have hbern := one_sub_mul_le_pow_of_unit ht0 (htHalf.trans (by norm_num)) (n + 1)
  have hcoef : 1 - ((n + 1 : ℕ) : ℝ) * (1 / (2 * k)) = 1 / 2 := by
    rw [Nat.cast_add, Nat.cast_one]
    change 1 - k * (1 / (2 * k)) = 1 / 2
    field_simp [hk.ne']
    ring
  rw [hcoef] at hbern
  exact hbern.trans (pow_le_pow_left₀ (by linarith only [htHalf]) hlower (n + 1))

/-- A one-half power floor replaces exponential collar conditioning by the exact linear noise bound. -/
theorem scalar_cycle_recovery_of_power_half {a b u v : ℝ}
    (hu : 1 / 2 ≤ u) (hv : 1 / 2 ≤ v) (hu1 : |u| ≤ 1) (hv1 : |v| ≤ 1)
    (hb : |b| ≤ 1) (n : ℕ) (hun : 1 / 2 ≤ u ^ n) (hvn : 1 / 2 ≤ v ^ n) :
    |a - b| ≤ 2 * |a * u ^ n - b * v ^ n| + 2 * (n : ℝ) * |u ^ 2 - v ^ 2| := by
  let κ := min u v
  have hκhalf : 1 / 2 ≤ κ := le_min hu hv
  have hκ : 0 < κ := lt_of_lt_of_le (by norm_num) hκhalf
  have hκn : 1 / 2 ≤ κ ^ n := by
    rcases le_total u v with h | h
    · simpa only [κ, min_eq_left h] using hun
    · simpa only [κ, min_eq_right h] using hvn
  have h := scalar_cycle_recovery (a := a) hκ (min_le_left _ _) (min_le_right _ _) hu1 hv1 hb n
  apply h.trans
  apply (div_le_iff₀ (pow_pos hκ n)).mpr
  have hden : 1 ≤ 2 * κ := by linarith only [hκhalf]
  have hpair : (n : ℝ) * |u ^ 2 - v ^ 2| / (2 * κ) ≤ (n : ℝ) * |u ^ 2 - v ^ 2| := by
    apply (div_le_iff₀ (mul_pos (by norm_num) hκ)).mpr
    exact le_mul_of_one_le_right (mul_nonneg (Nat.cast_nonneg n) (abs_nonneg _)) hden
  have hsum : 0 ≤ 2 * |a * u ^ n - b * v ^ n| + 2 * (n : ℝ) * |u ^ 2 - v ^ 2| := by positivity
  have hm := mul_le_mul_of_nonneg_left hκn hsum
  nlinarith only [hpair, hm]

private theorem levy_source_ne_zero {E : ℝ} (f : LevyEnergySource E) : f.source ≠ 0 := by
  intro h
  have hp := f.mass_pos
  rw [h] at hp
  change (0 : ℝ) < ∫ _ : ℝ, (0 : ℝ) * 0 at hp
  norm_num at hp

/-- Actual sources satisfy the linearly conditioned two-cycle estimate at every lag in the window. -/
theorem derivative_correlation_recovery {E B R : ℝ} (f g : LevyEnergySource E)
    (hfB : normalizedDirichletEnergy f.source ≤ B)
    (hgB : normalizedDirichletEnergy g.source ≤ B)
    (n : ℕ) (hn : B * R ^ 2 ≤ (n : ℝ) + 1) {x : ℝ} (hx : |x| ≤ R) :
    |f.correlation x - g.correlation x| ≤
      2 * |value f (spoke n x) - value g (spoke n x)| +
      2 * ((n : ℝ) + 1) *
        |value f [x / ((n : ℝ) + 1), -(x / ((n : ℝ) + 1))] -
          value g [x / ((n : ℝ) + 1), -(x / ((n : ℝ) + 1))]| := by
  have hf := derivative_inner_power_ge_half f.source f.smooth (levy_source_ne_zero f) hfB hx n hn
  have hg := derivative_inner_power_ge_half g.source g.smooth (levy_source_ne_zero g) hgB hx n hn
  change 1 / 2 ≤ f.correlation (x / ((n : ℝ) + 1)) ∧
    1 / 2 ≤ f.correlation (x / ((n : ℝ) + 1)) ^ (n + 1) at hf
  change 1 / 2 ≤ g.correlation (x / ((n : ℝ) + 1)) ∧
    1 / 2 ≤ g.correlation (x / ((n : ℝ) + 1)) ^ (n + 1) at hg
  simp only [value_pair, value_spoke]
  simpa only [Nat.cast_add, Nat.cast_one] using scalar_cycle_recovery_of_power_half
    hf.1 hg.1 (f.abs_correlation_le_one _) (g.abs_correlation_le_one _)
    (g.abs_correlation_le_one x) (n + 1) hf.2 hg.2

/-- Every actual derivative-energy ceiling gives the exact common square-root Lipschitz modulus. -/
theorem derivative_correlation_modulus {E B : ℝ} (f : LevyEnergySource E)
    (hB : normalizedDirichletEnergy f.source ≤ B) (x y : ℝ) :
    |f.correlation x - f.correlation y| ≤ Real.sqrt B * |x - y| := by
  have h := abs_nyquistNormalizedCorrelation_sub_le_sqrt_dirichlet f.source f.smooth
    (levy_source_ne_zero f) x y
  exact h.trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hB) (abs_nonneg _))

/-- Exact linearly conditioned recovery across a finite mesh and its entire support window. -/
theorem derivative_global_recovery {E B R η : ℝ} (f g : LevyEnergySource E)
    (hR : 0 ≤ R) (hη : 0 < η)
    (hfB : normalizedDirichletEnergy f.source ≤ B)
    (hgB : normalizedDirichletEnergy g.source ≤ B)
    (n : ℕ) (hn : B * R ^ 2 ≤ (n : ℝ) + 1)
    (hsf : ∀ x, R < |x| → f.correlation x = 0)
    (hsg : ∀ x, R < |x| → g.correlation x = 0) (x : ℝ) :
    |f.correlation x - g.correlation x| ≤
      2 * spokeMeshError f g R η n + 2 * ((n : ℝ) + 1) * pairMeshError f g R η n +
        2 * Real.sqrt B * η := by
  by_cases hx : |x| ≤ R
  · have hm (i : Fin (meshLength R η)) :
        |f.correlation (meshPoint R η i) - g.correlation (meshPoint R η i)| ≤
          2 * spokeMeshError f g R η n + 2 * ((n : ℝ) + 1) * pairMeshError f g R η n := by
      apply (derivative_correlation_recovery f g hfB hgB n hn (meshPoint_mem hR hη i)).trans
      exact add_le_add
        (mul_le_mul_of_nonneg_left (spoke_discrepancy_le_meshError f g R η n i) (by norm_num))
        (mul_le_mul_of_nonneg_left (pair_discrepancy_le_meshError f g R η n i) (by positivity))
    have hfm (u v : ℝ) (huv : |u - v| ≤ η) :
        |f.correlation u - f.correlation v| ≤ Real.sqrt B * η :=
      (derivative_correlation_modulus f hfB u v).trans
        (mul_le_mul_of_nonneg_left huv (Real.sqrt_nonneg B))
    have hgm (u v : ℝ) (huv : |u - v| ≤ η) :
        |g.correlation u - g.correlation v| ≤ Real.sqrt B * η :=
      (derivative_correlation_modulus g hgB u v).trans
        (mul_le_mul_of_nonneg_left huv (Real.sqrt_nonneg B))
    simpa only [mul_assoc] using window_error_le_of_mesh_error f g hη hm hfm hgm hx
  · rw [hsf x (lt_of_not_ge hx), hsg x (lt_of_not_ge hx), sub_self, abs_zero]
    exact add_nonneg
      (add_nonneg (mul_nonneg (by norm_num) (spokeMeshError_nonneg f g R η n))
        (mul_nonneg (by positivity) (pairMeshError_nonneg f g R η n)))
      (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg B)) hη.le)

/-- The actual bounded correlation functions obey the stated global derivative-controlled norm bound. -/
theorem derivative_global_recovery_norm {E B R η : ℝ} (f g : LevyEnergySource E)
    (hR : 0 ≤ R) (hη : 0 < η)
    (hfB : normalizedDirichletEnergy f.source ≤ B)
    (hgB : normalizedDirichletEnergy g.source ≤ B)
    (n : ℕ) (hn : B * R ^ 2 ≤ (n : ℝ) + 1)
    (hsf : ∀ x, R < |x| → f.correlation x = 0)
    (hsg : ∀ x, R < |x| → g.correlation x = 0) :
    ‖f.complexCorrelation - g.complexCorrelation‖ ≤
      2 * spokeMeshError f g R η n + 2 * ((n : ℝ) + 1) * pairMeshError f g R η n +
        2 * Real.sqrt B * η := by
  apply BoundedContinuousFunction.norm_le_of_nonempty.mpr
  intro x
  change ‖(f.correlation x : ℂ) - (g.correlation x : ℂ)‖ ≤ _
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact derivative_global_recovery f g hR hη hfB hgB n hn hsf hsg x

end GaloisForLFunctions.BiScaleUncertainty.EnergyCycle
