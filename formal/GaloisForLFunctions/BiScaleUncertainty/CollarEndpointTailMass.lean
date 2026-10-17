import GaloisForLFunctions.BiScaleUncertainty.CollarMeshBounds

/-!
# Leading physical tail mass at the logarithmic cutoff

The Lévy weight is twice the half-rate exponential plus a nonnegative remainder
bounded by four times the five-halves-rate exponential. Its physical tail has
leading term 4/sqrt(N), with an explicit error no larger than 1/N.
-/

set_option autoImplicit false
open MeasureTheory Set Filter
open scoped Topology
namespace GaloisForLFunctions.BiScaleUncertainty
noncomputable section

def collarEndpointTailMass (n : ℕ) : ℝ :=
  ∫ x in Ioi (logarithmicCollarEndpoint n), archLevySinhWeight x

theorem integrableOn_archWeight_endpoint_tail (n : ℕ) :
    IntegrableOn archLevySinhWeight (Ioi (logarithmicCollarEndpoint n)) :=
  (integrableOn_archWeight_retention_tail n).mono_set (fun _ hx =>
    (logarithmicCollarRetention_lt_endpoint n).trans hx)

theorem collarEndpointTailMass_nonneg (n : ℕ) : 0 ≤ collarEndpointTailMass n := by
  apply setIntegral_nonneg measurableSet_Ioi
  intro x hx
  exact (archLevySinhWeight_pos ((logarithmicCollarRadius_pos.trans_le
    (logarithmicCollarRadius_le_retention n)).trans
      ((logarithmicCollarRetention_lt_endpoint n).trans hx))).le

theorem archWeight_half_exponential_remainder {x : ℝ} (hx : logarithmicCollarRadius ≤ x) :
    0 ≤ archLevySinhWeight x - 2 * Real.exp (-x / 2) ∧
    archLevySinhWeight x - 2 * Real.exp (-x / 2) ≤ 4 * Real.exp (-(5 / 2) * x) := by
  have hxp : 0 < x := logarithmicCollarRadius_pos.trans_le hx
  have hd : 0 < 1 - Real.exp (-2 * x) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have hq : Real.exp (-2 * x) ≤ (1 / 2 : ℝ) := by
    rw [← exp_neg_two_collarRadius]
    exact Real.exp_le_exp.mpr (by linarith)
  have he : Real.exp (-(5 / 2) * x) = Real.exp (-x / 2) * Real.exp (-2 * x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hid : archLevySinhWeight x - 2 * Real.exp (-x / 2) =
      (2 * Real.exp (-(5 / 2) * x)) / (1 - Real.exp (-2 * x)) := by
    rw [archLevySinhWeight, RHTower.ArchimedeanAnomaly.exp_half_div_sinh_eq hxp,
      RHTower.archLevyDensity, he]
    field_simp [hd.ne']
    ring
  rw [hid]
  constructor
  · positivity
  · have h := div_le_div_of_nonneg_left (by positivity : 0 ≤ 2 * Real.exp (-(5 / 2) * x))
      (by norm_num : (0 : ℝ) < 1 / 2) (show (1 / 2 : ℝ) ≤ 1 - Real.exp (-2 * x) by linarith)
    convert h using 1 <;> ring

theorem collarEndpointTailMass_exponential_error (n : ℕ) :
    0 ≤ collarEndpointTailMass n - 4 * Real.exp (-logarithmicCollarEndpoint n / 2) ∧
    collarEndpointTailMass n - 4 * Real.exp (-logarithmicCollarEndpoint n / 2) ≤
      (8 / 5) * Real.exp (-(5 / 2) * logarithmicCollarEndpoint n) := by
  let a := logarithmicCollarEndpoint n
  have hi := integrableOn_archWeight_endpoint_tail n
  have he := (integrableOn_exp_mul_Ioi (a := -(1 / 2 : ℝ)) (by norm_num) a).const_mul 2
  have hu := (integrableOn_exp_mul_Ioi (a := -(5 / 2 : ℝ)) (by norm_num) a).const_mul 4
  have hd : IntegrableOn (fun x => archLevySinhWeight x - 2 * Real.exp (-(1 / 2) * x)) (Ioi a) :=
    hi.sub he
  have hpoint (x : ℝ) (hx : x ∈ Ioi a) :
      0 ≤ archLevySinhWeight x - 2 * Real.exp (-(1 / 2) * x) ∧
      archLevySinhWeight x - 2 * Real.exp (-(1 / 2) * x) ≤ 4 * Real.exp (-(5 / 2) * x) := by
    have h := archWeight_half_exponential_remainder
      ((logarithmicCollarRadius_le_retention n).trans
        ((logarithmicCollarRetention_lt_endpoint n).le.trans hx.le))
    simpa only [show -(1 / 2 : ℝ) * x = -x / 2 by ring] using h
  have hlo : 0 ≤ ∫ x in Ioi a, (archLevySinhWeight x - 2 * Real.exp (-(1 / 2) * x)) :=
    setIntegral_nonneg measurableSet_Ioi (fun x hx => (hpoint x hx).1)
  have hhi := setIntegral_mono_on hd hu measurableSet_Ioi (fun x hx => (hpoint x hx).2)
  have hlead : (∫ x in Ioi a, 2 * Real.exp (-(1 / 2) * x)) = 4 * Real.exp (-a / 2) := by
    rw [integral_const_mul, integral_exp_mul_Ioi (by norm_num),
      show -(1 / 2 : ℝ) * a = -a / 2 by ring]
    ring
  have hrem : (∫ x in Ioi a, 4 * Real.exp (-(5 / 2) * x)) =
      (8 / 5) * Real.exp (-(5 / 2) * a) := by
    rw [integral_const_mul, integral_exp_mul_Ioi (by norm_num)]
    ring
  rw [integral_sub hi he, hlead] at hlo hhi
  rw [hrem] at hhi
  exact ⟨hlo, hhi⟩

theorem exp_neg_collarEndpoint_half (n : ℕ) :
    Real.exp (-logarithmicCollarEndpoint n / 2) = 1 / Real.sqrt ((n + 2 : ℕ) : ℝ) := by
  rw [show -logarithmicCollarEndpoint n / 2 = -(logarithmicCollarNode n / 2) by
    unfold logarithmicCollarEndpoint logarithmicCollarNode; ring,
    Real.exp_neg, exp_logarithmicCollarNode_half, one_div]

theorem exp_neg_two_collarEndpoint (n : ℕ) :
    Real.exp (-2 * logarithmicCollarEndpoint n) = 1 / (((n + 2 : ℕ) : ℝ) ^ 2) := by
  have hN : 0 < ((n + 2 : ℕ) : ℝ) := by positivity
  rw [show -2 * logarithmicCollarEndpoint n =
    -(logarithmicCollarEndpoint n + logarithmicCollarEndpoint n) by ring,
    Real.exp_neg, Real.exp_add,
    show Real.exp (logarithmicCollarEndpoint n) = ((n + 2 : ℕ) : ℝ) from Real.exp_log hN]
  simp only [one_div, pow_two]

theorem collarEndpointTailMass_error (n : ℕ) :
    0 ≤ collarEndpointTailMass n - 4 / Real.sqrt ((n + 2 : ℕ) : ℝ) ∧
    collarEndpointTailMass n - 4 / Real.sqrt ((n + 2 : ℕ) : ℝ) ≤
      1 / ((n + 2 : ℕ) : ℝ) := by
  have h := collarEndpointTailMass_exponential_error n
  rw [exp_neg_collarEndpoint_half] at h
  have hN : 0 < ((n + 2 : ℕ) : ℝ) := by positivity
  have hN2 : (2 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ n + 2 by omega)
  have ha : 0 ≤ logarithmicCollarEndpoint n := Real.log_nonneg (by linarith)
  have he : Real.exp (-(5 / 2) * logarithmicCollarEndpoint n) ≤
      1 / (((n + 2 : ℕ) : ℝ) ^ 2) := by
    rw [← exp_neg_two_collarEndpoint]
    exact Real.exp_le_exp.mpr (by linarith)
  have hrest : (8 / 5 : ℝ) * Real.exp (-(5 / 2) * logarithmicCollarEndpoint n) ≤
      1 / ((n + 2 : ℕ) : ℝ) := by
    calc
      _ ≤ (8 / 5 : ℝ) * (1 / (((n + 2 : ℕ) : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left he (by norm_num)
      _ ≤ ((n + 2 : ℕ) : ℝ) * (1 / (((n + 2 : ℕ) : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by field_simp [hN.ne']; ring
  constructor
  · simpa only [mul_one_div] using h.1
  · have h' : collarEndpointTailMass n - 4 / Real.sqrt ((n + 2 : ℕ) : ℝ) ≤
        (8 / 5) * Real.exp (-(5 / 2) * logarithmicCollarEndpoint n) := by
      simpa only [mul_one_div] using h.2
    exact h'.trans hrest

theorem tendsto_inverse_collarCutoff :
    Tendsto (fun n : ℕ => 1 / ((n + 2 : ℕ) : ℝ)) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => by positivity) (fun n => ?_)
    tendsto_one_div_add_atTop_nhds_zero_nat
  apply div_le_div_of_nonneg_left zero_le_one (by positivity)
  push_cast
  linarith

theorem tendsto_inverse_sqrt_collarCutoff :
    Tendsto (fun n : ℕ => 1 / Real.sqrt ((n + 2 : ℕ) : ℝ)) atTop (𝓝 0) := by
  have h := (Real.continuous_sqrt.tendsto 0).comp tendsto_inverse_collarCutoff
  simpa only [Real.sqrt_div zero_le_one, Real.sqrt_one, Real.sqrt_zero] using h

theorem collarEndpointTailMass_tendsto : Tendsto collarEndpointTailMass atTop (𝓝 0) := by
  have h := (tendsto_inverse_sqrt_collarCutoff.const_mul 4).add tendsto_inverse_collarCutoff
  simp only [mul_zero, zero_add, mul_one_div] at h
  apply squeeze_zero collarEndpointTailMass_nonneg (fun n => ?_) h
  have hb := (collarEndpointTailMass_error n).2
  linarith

/-- Common transported mass is the complete collar tail minus its endpoint tail. -/
theorem physicalMass_eq_tail_sub_endpoint (n : ℕ) :
    (∫ x in Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n), archLevySinhWeight x) =
      collarTailMass - collarEndpointTailMass n := by
  have hle := (logarithmicCollarRadius_le_retention n).trans
    (logarithmicCollarRetention_lt_endpoint n).le
  rw [collarTailMass, collarEndpointTailMass,
    intervalIntegral.integral_Ioi_sub_Ioi integrableOn_archWeight_collar_tail hle,
    intervalIntegral.integral_of_le hle, integral_Ioc_eq_integral_Ioo]

end
end GaloisForLFunctions.BiScaleUncertainty
