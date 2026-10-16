import GaloisForLFunctions.RHTower.PaperThetaConfluentAdmission

/-! # Full confluent currents of the literal compact theta family

Every parameter derivative is an admitted BV function with its actual L1
derivative density. The only singular current is its differentiated Xi
connection charge. At full multiplicity this is the original Meyer source.
-/

noncomputable section
open MeasureTheory Set Filter Topology Complex
open scoped SchwartzMap

namespace RHTower.PaperThetaEndpoint
open HedenmalmThetaSource HedenmalmQuantile

private theorem complex_ac_integration_by_parts {f : ℝ → ℂ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (φ : 𝓢(ℝ, ℂ)) :
    (∫ t in a..b, f t*deriv φ t) = f b*φ b-f a*φ a-
      ∫ t in a..b, deriv f t*φ t := by
  have hφ : AbsolutelyContinuousOnInterval φ a b :=
    (φ.smooth 1).contDiffOn.absolutelyContinuousOnInterval
  have hp : AbsolutelyContinuousOnInterval (fun t => f t*φ t) a b := hf.fun_smul hφ
  have he := hp.integral_deriv_eq_sub_vector
  have hi1 := hf.intervalIntegrable_deriv_vector.mul_continuousOn φ.continuous.continuousOn
  have hφ' : Continuous (deriv φ) := (SchwartzMap.derivCLM ℂ ℂ φ).continuous
  have hi2 : IntervalIntegrable (fun t => f t*deriv φ t) volume a b :=
    (hf.continuousOn.mul hφ'.continuousOn).intervalIntegrable
  have hd : (∫ t in a..b, deriv (fun x => f x*φ x) t) =
      ∫ t in a..b, deriv f t*φ t+f t*deriv φ t := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hf.boundedVariationOn.ae_differentiableAt_of_mem_uIcc] with t ht htab
    exact ((ht (uIoc_subset_uIcc htab)).hasDerivAt.mul (φ.hasDerivAt t)).deriv
  rw [hd, intervalIntegral.integral_add hi1 hi2] at he
  linear_combination he

theorem cutQuantileParameterJet_eventuallyEq_left (n : ℕ) (z : ℂ) (c : Ioo (0 : ℝ) 1)
    {t : ℝ} (ht : t < c.val) :
    cutQuantileParameterJet n z c =ᶠ[𝓝 t] leftClosedParameterJet n z := by
  filter_upwards [Iio_mem_nhds ht] with x hx
  exact cutQuantileParameterJet_left n z c hx

theorem cutQuantileParameterJet_eventuallyEq_right (n : ℕ) (z : ℂ) (c : Ioo (0 : ℝ) 1)
    {t : ℝ} (ht : c.val < t) :
    cutQuantileParameterJet n z c =ᶠ[𝓝 t] closedParameterJet n z := by
  filter_upwards [Ioi_mem_nhds ht] with x hx
  exact cutQuantileParameterJet_right n z c hx.le

theorem intervalIntegrable_deriv_cutQuantileParameterJet_left
    (n : ℕ) (z : ℂ) (c : Ioo (0 : ℝ) 1) :
    IntervalIntegrable (deriv (cutQuantileParameterJet n z c)) volume 0 c.val := by
  apply (intervalIntegrable_deriv_leftClosedParameterJet n z c).congr_uIoo
  intro t ht
  rw [uIoo_of_le c.property.1.le] at ht
  exact (cutQuantileParameterJet_eventuallyEq_left n z c ht.2).deriv_eq.symm

theorem intervalIntegrable_deriv_cutQuantileParameterJet_right
    (n : ℕ) (z : ℂ) (c : Ioo (0 : ℝ) 1) :
    IntervalIntegrable (deriv (cutQuantileParameterJet n z c)) volume c.val 1 := by
  apply (intervalIntegrable_deriv_closedParameterJet_right n z c).congr_uIoo
  intro t ht
  rw [uIoo_of_le c.property.2.le] at ht
  exact (cutQuantileParameterJet_eventuallyEq_right n z c ht.1).deriv_eq.symm

/-- Admission pays the actual derivative density for every parameter order. -/
theorem intervalIntegrable_deriv_cutQuantileParameterJet
    (n : ℕ) (z : ℂ) (c : Ioo (0 : ℝ) 1) :
    IntervalIntegrable (deriv (cutQuantileParameterJet n z c)) volume 0 1 :=
  (intervalIntegrable_deriv_cutQuantileParameterJet_left n z c).trans
    (intervalIntegrable_deriv_cutQuantileParameterJet_right n z c)

private theorem jetIntegral_left (n : ℕ) (z : ℂ) (c : Ioo (0 : ℝ) 1) (f : ℝ → ℂ) :
    (∫ t in (0 : ℝ)..c.val, cutQuantileParameterJet n z c t*f t) =
      ∫ t in (0 : ℝ)..c.val, leftClosedParameterJet n z t*f t :=
  intervalIntegral.integral_congr_Ioo_of_le c.property.1.le fun t ht => by
    rw [cutQuantileParameterJet_left n z c ht.2]

private theorem jetIntegral_right (n : ℕ) (z : ℂ) (c : Ioo (0 : ℝ) 1) (f : ℝ → ℂ) :
    (∫ t in c.val..1, cutQuantileParameterJet n z c t*f t) =
      ∫ t in c.val..1, closedParameterJet n z t*f t :=
  intervalIntegral.integral_congr_Ioo_of_le c.property.2.le fun t ht => by
    rw [cutQuantileParameterJet_right n z c ht.1.le]

private theorem jetDerivIntegral_left (n : ℕ) (z : ℂ) (c : Ioo (0 : ℝ) 1) (f : ℝ → ℂ) :
    (∫ t in (0 : ℝ)..c.val, deriv (cutQuantileParameterJet n z c) t*f t) =
      ∫ t in (0 : ℝ)..c.val, deriv (leftClosedParameterJet n z) t*f t :=
  intervalIntegral.integral_congr_Ioo_of_le c.property.1.le fun t ht => by
    rw [(cutQuantileParameterJet_eventuallyEq_left n z c ht.2).deriv_eq]

private theorem jetDerivIntegral_right (n : ℕ) (z : ℂ) (c : Ioo (0 : ℝ) 1) (f : ℝ → ℂ) :
    (∫ t in c.val..1, deriv (cutQuantileParameterJet n z c) t*f t) =
      ∫ t in c.val..1, deriv (closedParameterJet n z) t*f t :=
  intervalIntegral.integral_congr_Ioo_of_le c.property.2.le fun t ht => by
    rw [(cutQuantileParameterJet_eventuallyEq_right n z c ht.1).deriv_eq]

/-- Complete compact weak current of every actual parameter jet, including the atom. -/
theorem cutQuantileParameterJet_weak_current (n : ℕ) (z : ℂ)
    (c : Ioo (0 : ℝ) 1) (φ : 𝓢(ℝ, ℂ)) :
    (∫ t in (0 : ℝ)..1, cutQuantileParameterJet n z c t*deriv φ t) =
      parameterEndpointTrace n*(φ 1-φ 0) -
        (∫ t in (0 : ℝ)..1, deriv (cutQuantileParameterJet n z c) t*φ t) -
          iteratedDeriv n (fun w => cutCharge w (thetaSource.quantileFun c.val)) z * φ c.val := by
  have hL := (absolutelyContinuousOnInterval_leftClosedParameterJet n z c).continuousOn
  have hR := (absolutelyContinuousOnInterval_closedParameterJet_right n z c).continuousOn
  have hφ' : Continuous (deriv φ) := (SchwartzMap.derivCLM ℂ ℂ φ).continuous
  have hleft := complex_ac_integration_by_parts
    (absolutelyContinuousOnInterval_leftClosedParameterJet n z c) φ
  have hright := complex_ac_integration_by_parts
    (absolutelyContinuousOnInterval_closedParameterJet_right n z c) φ
  have hML : IntervalIntegrable (fun t => cutQuantileParameterJet n z c t*deriv φ t)
      volume 0 c.val := by
    apply (hL.mul hφ'.continuousOn).intervalIntegrable.congr_uIoo
    intro t ht
    rw [uIoo_of_le c.property.1.le] at ht
    change leftClosedParameterJet n z t*deriv φ t = cutQuantileParameterJet n z c t*deriv φ t
    rw [cutQuantileParameterJet_left n z c ht.2]
  have hMR : IntervalIntegrable (fun t => cutQuantileParameterJet n z c t*deriv φ t)
      volume c.val 1 := by
    apply (hR.mul hφ'.continuousOn).intervalIntegrable.congr_uIoo
    intro t ht
    rw [uIoo_of_le c.property.2.le] at ht
    change closedParameterJet n z t*deriv φ t = cutQuantileParameterJet n z c t*deriv φ t
    rw [cutQuantileParameterJet_right n z c ht.1.le]
  have hJL := (intervalIntegrable_deriv_cutQuantileParameterJet_left n z c).mul_continuousOn
    φ.continuous.continuousOn
  have hJR := (intervalIntegrable_deriv_cutQuantileParameterJet_right n z c).mul_continuousOn
    φ.continuous.continuousOn
  rw [← intervalIntegral.integral_add_adjacent_intervals hML hMR,
    ← intervalIntegral.integral_add_adjacent_intervals hJL hJR,
    jetIntegral_left, jetIntegral_right, jetDerivIntegral_left, jetDerivIntegral_right,
    hleft, hright, leftClosedParameterJet_zero, (closedParameterJet_endpoints n z).2,
    ← closedParameterJet_sub_left n z c]
  ring

/-- The terminal admitted jet retains the full original Meyer source, with its signed cut gauge. -/
theorem terminal_cutQuantileParameterJet_meyer_current (rho : XiDivisorSupport)
    (c : Ioo (0 : ℝ) 1) (φ : 𝓢(ℝ, ℂ)) :
    (∫ t in (0 : ℝ)..1,
      cutQuantileParameterJet (xiSupportMultiplicity rho) (xiSpectralPointSupport rho) c t*deriv φ t) =
      -(∫ t in (0 : ℝ)..1,
        deriv (cutQuantileParameterJet (xiSupportMultiplicity rho) (xiSpectralPointSupport rho) c) t*φ t) -
      ((-(I*xiSpectralPointSupport rho)*
        Complex.exp (-(I*xiSpectralPointSupport rho)*(thetaSource.quantileFun c.val : ℂ)) /
          (thetaSource.k (thetaSource.quantileFun c.val) : ℂ)) * (xiSupportMultiplicity rho).factorial *
        deningerMeyerCenteredMellin
          (deningerMeyerHedenmalmSource rho ⟨xiSupportMultiplicity rho, Nat.lt_succ_self _⟩)
          (xiSpectralPointSupport rho)) * φ c.val := by
  rw [cutQuantileParameterJet_weak_current, cutCharge_terminal_meyer_source]
  simp only [parameterEndpointTrace, ne_of_gt (xiSupportMultiplicity_pos rho),
    if_false, zero_mul, zero_sub]

end RHTower.PaperThetaEndpoint
