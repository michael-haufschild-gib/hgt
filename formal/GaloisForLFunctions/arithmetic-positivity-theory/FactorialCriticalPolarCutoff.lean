import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialCriticalPhasePrimitive
import GaloisForLFunctions.RHTower.CCMEndpointFourierJet

/-! Critical polar endpoint with an explicit inverse-cutoff error.
The endpoint is defined by an absolutely convergent primitive integral. -/

open MeasureTheory Set Filter
open scoped BigOperators Topology
open GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar

noncomputable section
namespace GaloisForLFunctions.ArithmeticPositivityTheory
set_option autoImplicit false

private theorem bounded_primitive_weight_integrable {G : ℝ → ℝ} {C a : ℝ}
    (ha : 0 < a) (hGc : ContinuousOn G (Ioi 0)) (hGb : ∀ x, |G x| ≤ C) :
    IntegrableOn (fun x : ℝ => G x / x^2) (Ioi a) := by
  have hGm : AEStronglyMeasurable G (volume.restrict (Ioi a)) :=
    (hGc.mono (Ioi_subset_Ioi ha.le)).aestronglyMeasurable measurableSet_Ioi
  have h := (GaloisForLFunctions.RHTower.integrableOn_Ioi_inv_pow ha (by norm_num : 2 ≤ 2)).mul_bdd
    (c := C) hGm (Filter.Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs] using hGb x)
  simpa only [IntegrableOn, Pi.mul_def, div_eq_mul_inv, one_mul, mul_one, mul_comm] using h

private theorem bounded_primitive_weight_bound {G : ℝ → ℝ} {C a : ℝ}
    (ha : 0 < a) (hGb : ∀ x, |G x| ≤ C) :
    |∫ x : ℝ in Ioi a, G x / x^2| ≤ C / a := by
  have h := norm_integral_le_of_norm_le
    ((GaloisForLFunctions.RHTower.integrableOn_Ioi_inv_pow ha (by norm_num : 2 ≤ 2)).const_mul C)
    (f := fun x : ℝ => G x / x^2) ?_
  · rw [integral_const_mul, GaloisForLFunctions.RHTower.integral_Ioi_inv_sq ha] at h
    simpa only [Real.norm_eq_abs, div_eq_mul_inv, one_mul] using h
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (sq_nonneg x)]
    simpa only [div_eq_mul_inv, one_mul] using div_le_div_of_nonneg_right (hGb x) (sq_nonneg x)

private theorem primitive_interval_identity {F G : ℝ → ℝ} (hFc : Continuous F)
    (hGd : ∀ x, 0 < x → HasDerivAt G (F x) x) {T : ℝ} (hT : 1 ≤ T) :
    (∫ x in (1 : ℝ)..T, F x / x) = G T / T - G 1 + ∫ x in (1 : ℝ)..T, G x / x^2 := by
  have hu : ∀ x ∈ uIcc (1 : ℝ) T,
      HasDerivAt (fun v : ℝ => v⁻¹) (-(x^2)⁻¹) x := by
    intro x hx
    rw [uIcc_of_le hT] at hx
    simpa using hasDerivAt_inv (zero_lt_one.trans_le hx.1).ne'
  have hv : ∀ x ∈ uIcc (1 : ℝ) T, HasDerivAt G (F x) x := by
    intro x hx
    rw [uIcc_of_le hT] at hx
    exact hGd x (zero_lt_one.trans_le hx.1)
  have hui : IntervalIntegrable (fun x : ℝ => -(x^2)⁻¹) volume 1 T := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hT]
    intro x hx
    exact (((continuousAt_id.pow 2).inv₀
      (pow_ne_zero 2 (zero_lt_one.trans_le hx.1).ne')).neg).continuousWithinAt
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hui
    (hFc.intervalIntegrable 1 T)
  have hl : (∫ x in (1 : ℝ)..T, x⁻¹ * F x) = ∫ x in (1 : ℝ)..T, F x / x := by
    apply intervalIntegral.integral_congr
    intro x _
    ring
  have hr : (∫ x in (1 : ℝ)..T, -(x^2)⁻¹ * G x) =
      -∫ x in (1 : ℝ)..T, G x / x^2 := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro x _
    ring
  rw [hl, hr] at h
  simpa only [inv_one, one_mul, div_eq_inv_mul, sub_neg_eq_add] using h

/-- The conditionally convergent polar endpoint expressed through an absolutely convergent integral. -/
def criticalFactorialPolarEndpoint (S : Finset ℕ) (b : ℕ → ℝ) : ℝ :=
  -criticalFactorialPhasePrimitive S b 1 +
    ∫ v in Ioi (1 : ℝ), criticalFactorialPhasePrimitive S b v / v^2

theorem criticalFactorialPolarEndpoint_bound (S : Finset ℕ) (b : ℕ → ℝ) :
    |criticalFactorialPolarEndpoint S b| ≤ 24 * ∑ n ∈ S, |b n| / ((n+1 : ℕ) : ℝ) := by
  have hp := criticalFactorialPhasePrimitive_bound S b 1
  have hi := bounded_primitive_weight_bound (by norm_num : (0 : ℝ) < 1)
    (criticalFactorialPhasePrimitive_bound S b)
  have htri := abs_add_le (-criticalFactorialPhasePrimitive S b 1)
    (∫ v in Ioi (1 : ℝ), criticalFactorialPhasePrimitive S b v / v^2)
  rw [abs_neg] at htri
  dsimp [criticalFactorialPolarEndpoint]
  linarith

theorem criticalFactorialPolarEndpoint_cutoff_error (S : Finset ℕ) (b : ℕ → ℝ)
    {T : ℝ} (hT : 1 ≤ T) :
    |(∫ v in (1 : ℝ)..T, (factorialPhaseCombination S (fun n => (b n : ℂ)) v).re / v) -
      criticalFactorialPolarEndpoint S b| ≤
      (24 / T) * ∑ n ∈ S, |b n| / ((n+1 : ℕ) : ℝ) := by
  let G := criticalFactorialPhasePrimitive S b
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hGc : ContinuousOn G (Ioi 0) := fun x hx =>
    (criticalFactorialPhasePrimitive_hasDerivAt S b hx).continuousAt.continuousWithinAt
  have hI := primitive_interval_identity (Complex.continuous_re.comp
    (continuous_factorialPhaseCombination S (fun n => (b n : ℂ))))
    (fun x hx => criticalFactorialPhasePrimitive_hasDerivAt S b hx) hT
  simp only [Function.comp_def] at hI
  have hsplit := intervalIntegral.integral_Ioi_sub_Ioi
    (bounded_primitive_weight_integrable zero_lt_one hGc (criticalFactorialPhasePrimitive_bound S b)) hT
  have heq : (∫ v in (1 : ℝ)..T, (factorialPhaseCombination S (fun n => (b n : ℂ)) v).re / v) -
      criticalFactorialPolarEndpoint S b = G T / T - ∫ v in Ioi T, G v / v^2 := by
    rw [hI, ← hsplit]
    dsimp [criticalFactorialPolarEndpoint, G]
    ring
  rw [heq]
  have hpoint : |G T / T| ≤ (12 * ∑ n ∈ S, |b n| / ((n+1 : ℕ) : ℝ)) / T := by
    rw [abs_div, abs_of_pos hT0]
    exact div_le_div_of_nonneg_right (criticalFactorialPhasePrimitive_bound S b T) hT0.le
  have htail := bounded_primitive_weight_bound hT0 (criticalFactorialPhasePrimitive_bound S b)
  calc
    _ ≤ |G T / T| + |∫ v in Ioi T, G v / v^2| := abs_sub _ _
    _ ≤ (12 * ∑ n ∈ S, |b n| / ((n+1 : ℕ) : ℝ)) / T +
        (12 * ∑ n ∈ S, |b n| / ((n+1 : ℕ) : ℝ)) / T := add_le_add hpoint htail
    _ = _ := by ring

theorem criticalFactorialPolarEndpoint_tendsto (S : Finset ℕ) (b : ℕ → ℝ) :
    Tendsto (fun T : ℝ => ∫ v in (1 : ℝ)..T,
      (factorialPhaseCombination S (fun n => (b n : ℂ)) v).re / v)
      atTop (𝓝 (criticalFactorialPolarEndpoint S b)) := by
  let C := ∑ n ∈ S, |b n| / ((n+1 : ℕ) : ℝ)
  have hrate : Tendsto (fun T : ℝ => (24 / T) * C) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, zero_mul] using
      ((tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul 24).mul_const C
  have hzero : Tendsto (fun T : ℝ => (∫ v in (1 : ℝ)..T,
      (factorialPhaseCombination S (fun n => (b n : ℂ)) v).re / v) -
      criticalFactorialPolarEndpoint S b) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun T : ℝ => (24 / T) * C) ?_ hrate
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    simpa only [Real.norm_eq_abs] using criticalFactorialPolarEndpoint_cutoff_error S b hT
  simpa only [sub_add_cancel, zero_add] using hzero.add_const (criticalFactorialPolarEndpoint S b)

end GaloisForLFunctions.ArithmeticPositivityTheory
