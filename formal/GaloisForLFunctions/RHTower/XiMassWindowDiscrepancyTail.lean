import GaloisForLFunctions.RHTower.XiMassPrimeWindowAbel
import GaloisForLFunctions.RHTower.XiMassBesselDerivativeEnvelope
import GaloisForLFunctions.RHTower.XiMassAnnulusPhaseProjection

/-!
# The exterior discrepancy on a window

Abel summation on a logarithmic prime window expresses the quadrature defect between the moving
prime cone and its continuum density as

`E(T) G(T) − E(H) G(H) − ∫_H^T E(h) G'(h) dh`.

The differentiated exterior envelope bounds `|G|` and `|G'|` by `C u^{-1/2} e^{-h/2 − a√(h²−u²)}`,
so every term is bounded by

`C·C_E·u^{-1/2} e^{g_u(h)} e^{-c h^{1/10}}`,  `g_u(h) = h/2 − a√(h²−u²)`.

The action `g_u` decreases with slope at least `a − 1/2` outside the cone while the
prime-discrepancy exponent `h^{1/10}` increases, so the whole window is controlled by its inner
endpoint.  This converts the power-log prime number theorem into a subcaustic penetration
estimate.
-/

open Complex MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-! ## Monotonicity of the exterior action -/

/-- **The exterior action decreases with slope at least `a − 1/2`.** -/
theorem xiMassExteriorAction_le {a u H h : ℝ} (ha : 1 / 2 < a) (hu : 0 < u) (hHu : u < H)
    (hHh : H ≤ h) :
    h / 2 - a * Real.sqrt (h ^ 2 - u ^ 2)
      ≤ (H / 2 - a * Real.sqrt (H ^ 2 - u ^ 2)) - (a - 1 / 2) * (h - H) := by
  have hkappa : (1 : ℝ) < H / u := (one_lt_div hu).2 hHu
  have hku : H / u * u = H := div_mul_cancel₀ H hu.ne'
  have hbase := xiMassBessel_exterior_exponent_le (a := a) (kappa := H / u) (u := u) (h := h)
    ha hkappa hu.le (by rw [hku]; exact hHh)
  have hgap : (0 : ℝ) ≤ H ^ 2 - u ^ 2 := by nlinarith
  have hexp : xiMassBesselConeExponent a (H / u) * u
      = a * Real.sqrt (H ^ 2 - u ^ 2) - H / 2 := by
    have hval : (H / u) ^ 2 - 1 = (H ^ 2 - u ^ 2) / u ^ 2 := by field_simp
    have hroot : Real.sqrt ((H ^ 2 - u ^ 2) / u ^ 2) = Real.sqrt (H ^ 2 - u ^ 2) / u := by
      rw [Real.sqrt_div hgap, Real.sqrt_sq hu.le]
    rw [xiMassBesselConeExponent, hval, hroot]
    field_simp
  rw [hexp, hku] at hbase
  linarith

/-! ## The exterior envelopes of the damped profile and its derivative -/

theorem norm_xiMassCriticalDampedFourierProfile_exterior_le {a sigma kappa u h : ℝ}
    (ha : 0 < a) (hsigma : 0 < sigma) (hkappa : 1 < kappa) (hu : 0 < u) (hcone : kappa * u ≤ h) :
    ‖xiMassCriticalDampedFourierProfile a sigma u h‖
      ≤ xiMassBesselExteriorSqrtConstant a sigma kappa / Real.sqrt u
        * Real.exp (-h / 2) * Real.exp (-(a * Real.sqrt (h ^ 2 - u ^ 2))) := by
  have hF := norm_stripFourier_xiMass_le_besselExteriorSqrt ha hsigma hkappa hu hcone
  have hnorm : ‖xiMassCriticalDampedFourierProfile a sigma u h‖
      = Real.exp (-h / 2)
        * ‖stripFourier (xiMassAnalyticTest a ((sigma : ℂ) + (u : ℂ) * I)) (h : ℂ)‖ := by
    rw [xiMassCriticalDampedFourierProfile, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
  rw [hnorm]
  have hstep := mul_le_mul_of_nonneg_left hF (Real.exp_nonneg (-h / 2))
  refine hstep.trans (le_of_eq ?_)
  ring

theorem norm_xiMassDampedProfileDeriv_exterior_le {a sigma kappa u h : ℝ}
    (ha : 0 < a) (hsigma : 0 < sigma) (hkappa : 1 < kappa) (hu : 0 < u) (hcone : kappa * u ≤ h) :
    ‖-((Real.exp (-h / 2) : ℂ) * xiMassCriticalOutgoingDerivative a sigma u h)‖
      ≤ xiMassOutgoingDerivExteriorSqrtConstant a sigma kappa / Real.sqrt u
        * Real.exp (-h / 2) * Real.exp (-(a * Real.sqrt (h ^ 2 - u ^ 2))) := by
  have hD := norm_xiMassCriticalOutgoingDerivative_le ha hsigma hkappa hu hcone
  have hnorm : ‖-((Real.exp (-h / 2) : ℂ) * xiMassCriticalOutgoingDerivative a sigma u h)‖
      = Real.exp (-h / 2) * ‖xiMassCriticalOutgoingDerivative a sigma u h‖ := by
    rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [hnorm]
  have hstep := mul_le_mul_of_nonneg_left hD (Real.exp_nonneg (-h / 2))
  refine hstep.trans (le_of_eq ?_)
  ring

/-- The window defect constant dominates both exterior envelopes. -/
def xiMassWindowDefectConstant (a sigma kappa : ℝ) : ℝ :=
  xiMassBesselExteriorSqrtConstant a sigma kappa
    + xiMassOutgoingDerivExteriorSqrtConstant a sigma kappa

theorem xiMassOutgoingDerivExteriorSqrtConstant_nonneg {a sigma kappa : ℝ}
    (ha : 0 < a) (hsigma : 0 < sigma) (hkappa : 1 < kappa) :
    0 ≤ xiMassOutgoingDerivExteriorSqrtConstant a sigma kappa := by
  rw [xiMassOutgoingDerivExteriorSqrtConstant]
  have h1 := xiMassBesselDerivExteriorSqrtConstant_nonneg ha hsigma hkappa
  have h2 := xiMassBesselExteriorSqrtConstant_nonneg (a := a) (sigma := sigma) ha hkappa
  linarith

theorem xiMassWindowDefectConstant_nonneg {a sigma kappa : ℝ}
    (ha : 0 < a) (hsigma : 0 < sigma) (hkappa : 1 < kappa) :
    0 ≤ xiMassWindowDefectConstant a sigma kappa := by
  rw [xiMassWindowDefectConstant]
  have h1 := xiMassBesselExteriorSqrtConstant_nonneg (a := a) (sigma := sigma) ha hkappa
  have h2 := xiMassOutgoingDerivExteriorSqrtConstant_nonneg ha hsigma hkappa
  linarith

/-! ## The window discrepancy estimate -/

/-- The uniform pointwise bound for a discrepancy-weighted exterior factor. -/
private theorem window_pointwise_bound {a sigma kappa u H CE cE h : ℝ} {X : ℂ}
    (ha : 1 / 2 < a) (hsigma : 0 < sigma) (hkappa : 1 < kappa) (hu : 0 < u)
    (hcone : kappa * u ≤ H) (hCE : 0 ≤ CE) (hcE : 0 ≤ cE) (hHh : H ≤ h)
    (hEh : |xiMassThetaLogDiscrepancy h|
      ≤ CE * Real.exp h * Real.exp (-(cE * h ^ ((1 : ℝ) / 10))))
    (hX : ‖X‖ ≤ xiMassWindowDefectConstant a sigma kappa / Real.sqrt u
      * Real.exp (-h / 2) * Real.exp (-(a * Real.sqrt (h ^ 2 - u ^ 2)))) :
    ‖((xiMassThetaLogDiscrepancy h : ℝ) : ℂ) * X‖
      ≤ CE * (xiMassWindowDefectConstant a sigma kappa / Real.sqrt u)
        * Real.exp (H / 2 - a * Real.sqrt (H ^ 2 - u ^ 2))
        * Real.exp (-(cE * H ^ ((1 : ℝ) / 10))) := by
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  have hkappa0 : (0 : ℝ) < kappa := lt_trans zero_lt_one hkappa
  have hHu : u < H := lt_of_lt_of_le (by nlinarith) hcone
  have hH0 : (0 : ℝ) ≤ H := le_of_lt (lt_trans hu hHu)
  have hDnn : 0 ≤ xiMassWindowDefectConstant a sigma kappa :=
    xiMassWindowDefectConstant_nonneg ha0 hsigma hkappa
  have hcoef : (0 : ℝ) ≤ CE * (xiMassWindowDefectConstant a sigma kappa / Real.sqrt u) := by
    have : (0 : ℝ) ≤ xiMassWindowDefectConstant a sigma kappa / Real.sqrt u := by positivity
    exact mul_nonneg hCE this
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hstep : |xiMassThetaLogDiscrepancy h| * ‖X‖
      ≤ (CE * Real.exp h * Real.exp (-(cE * h ^ ((1 : ℝ) / 10))))
        * (xiMassWindowDefectConstant a sigma kappa / Real.sqrt u
          * Real.exp (-h / 2) * Real.exp (-(a * Real.sqrt (h ^ 2 - u ^ 2)))) :=
    mul_le_mul hEh hX (norm_nonneg _) (by positivity)
  refine hstep.trans ?_
  have hcollect : Real.exp (h / 2 - a * Real.sqrt (h ^ 2 - u ^ 2))
      = Real.exp h * Real.exp (-h / 2) * Real.exp (-(a * Real.sqrt (h ^ 2 - u ^ 2))) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hval : (CE * Real.exp h * Real.exp (-(cE * h ^ ((1 : ℝ) / 10))))
      * (xiMassWindowDefectConstant a sigma kappa / Real.sqrt u
        * Real.exp (-h / 2) * Real.exp (-(a * Real.sqrt (h ^ 2 - u ^ 2))))
      = CE * (xiMassWindowDefectConstant a sigma kappa / Real.sqrt u)
        * Real.exp (h / 2 - a * Real.sqrt (h ^ 2 - u ^ 2))
        * Real.exp (-(cE * h ^ ((1 : ℝ) / 10))) := by
    rw [hcollect]
    ring
  rw [hval]
  have haction : Real.exp (h / 2 - a * Real.sqrt (h ^ 2 - u ^ 2))
      ≤ Real.exp (H / 2 - a * Real.sqrt (H ^ 2 - u ^ 2)) := by
    refine Real.exp_le_exp.2 ?_
    have hstep2 := xiMassExteriorAction_le ha hu hHu hHh
    nlinarith [hstep2, sub_nonneg.2 hHh]
  have hpow : Real.exp (-(cE * h ^ ((1 : ℝ) / 10)))
      ≤ Real.exp (-(cE * H ^ ((1 : ℝ) / 10))) := by
    refine Real.exp_le_exp.2 ?_
    have hmono : H ^ ((1 : ℝ) / 10) ≤ h ^ ((1 : ℝ) / 10) :=
      Real.rpow_le_rpow hH0 hHh (by norm_num)
    nlinarith [hmono]
  have hfirst : CE * (xiMassWindowDefectConstant a sigma kappa / Real.sqrt u)
      * Real.exp (h / 2 - a * Real.sqrt (h ^ 2 - u ^ 2))
      ≤ CE * (xiMassWindowDefectConstant a sigma kappa / Real.sqrt u)
        * Real.exp (H / 2 - a * Real.sqrt (H ^ 2 - u ^ 2)) :=
    mul_le_mul_of_nonneg_left haction hcoef
  exact mul_le_mul hfirst hpow (Real.exp_nonneg _) (by positivity)

/-- **(19.3) The exterior discrepancy on a logarithmic window.** -/
theorem norm_primeLogWindow_quadratureDefect_le {a sigma kappa u H T CE cE : ℝ}
    (ha : 1 / 2 < a) (hsigma : 0 < sigma) (hkappa : 1 < kappa) (hu : 0 < u)
    (hcone : kappa * u ≤ H) (hHT : H ≤ T) (hCE : 0 ≤ CE) (hcE : 0 ≤ cE)
    (hE : ∀ h : ℝ, H ≤ h → h ≤ T →
      |xiMassThetaLogDiscrepancy h| ≤ CE * Real.exp h * Real.exp (-(cE * h ^ ((1 : ℝ) / 10)))) :
    ‖(∑ p ∈ primeLogWindow H T, xiMassCenteredPrimeAtom a ((sigma : ℂ) + (u : ℂ) * I) p)
        - ∫ h in H..T, xiMassCriticalGrowingFourierProfile a sigma u h‖
      ≤ (2 + (T - H)) * (CE * (xiMassWindowDefectConstant a sigma kappa / Real.sqrt u)
        * Real.exp (H / 2 - a * Real.sqrt (H ^ 2 - u ^ 2))
        * Real.exp (-(cE * H ^ ((1 : ℝ) / 10)))) := by
  classical
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  have hkappa0 : (0 : ℝ) < kappa := lt_trans zero_lt_one hkappa
  have hDnn : 0 ≤ xiMassWindowDefectConstant a sigma kappa :=
    xiMassWindowDefectConstant_nonneg ha0 hsigma hkappa
  have hbess : xiMassBesselExteriorSqrtConstant a sigma kappa
      ≤ xiMassWindowDefectConstant a sigma kappa := by
    rw [xiMassWindowDefectConstant]
    linarith [xiMassOutgoingDerivExteriorSqrtConstant_nonneg ha0 hsigma hkappa]
  have hout : xiMassOutgoingDerivExteriorSqrtConstant a sigma kappa
      ≤ xiMassWindowDefectConstant a sigma kappa := by
    rw [xiMassWindowDefectConstant]
    linarith [xiMassBesselExteriorSqrtConstant_nonneg (a := a) (sigma := sigma) ha0 hkappa]
  have hrootpos : (0 : ℝ) < Real.sqrt u := Real.sqrt_pos.2 hu
  -- rewrite both sides of the defect
  have hsum : (∑ p ∈ primeLogWindow H T, xiMassCenteredPrimeAtom a ((sigma : ℂ) + (u : ℂ) * I) p)
      = ∑ p ∈ primeLogWindow H T, ((Real.log p : ℝ) : ℂ)
          * xiMassCriticalDampedFourierProfile a sigma u (Real.log p) :=
    Finset.sum_congr rfl fun p hp =>
      xiMassCenteredPrimeAtom_eq_log_mul (mem_primeLogWindow.1 hp).2
  have hint : (∫ h in H..T, xiMassCriticalGrowingFourierProfile a sigma u h)
      = ∫ h in H..T,
          xiMassCriticalDampedFourierProfile a sigma u h * ((Real.exp h : ℝ) : ℂ) := by
    refine intervalIntegral.integral_congr fun h _ => ?_
    have hexp : Real.exp (-h / 2) * Real.exp h = Real.exp (h / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [xiMassCriticalGrowingFourierProfile, xiMassCriticalDampedFourierProfile, ← hexp]
    push_cast
    ring
  have hG : ∀ x ∈ Set.Icc H T, HasDerivAt (xiMassCriticalDampedFourierProfile a sigma u)
      (-((Real.exp (-x / 2) : ℂ) * xiMassCriticalOutgoingDerivative a sigma u x)) x :=
    fun x _ => hasDerivAt_xiMassCriticalDampedFourierProfile ha0 hsigma u x
  have hG'c : Continuous (fun x : ℝ =>
      -(((Real.exp (-x / 2) : ℝ) : ℂ) * xiMassCriticalOutgoingDerivative a sigma u x)) := by
    have h1 : Continuous (fun x : ℝ => ((Real.exp (-x / 2) : ℝ) : ℂ)) := by fun_prop
    exact (h1.mul (continuous_xiMassCriticalOutgoingDerivative ha0 hsigma u)).neg
  have hG' : IntervalIntegrable (fun x : ℝ =>
      -(((Real.exp (-x / 2) : ℝ) : ℂ) * xiMassCriticalOutgoingDerivative a sigma u x))
      volume H T := hG'c.continuousOn.intervalIntegrable
  rw [hsum, hint, primeLogWindow_quadrature_eq hHT hG hG']
  -- the three terms
  obtain ⟨B, hB⟩ : ∃ B : ℝ, CE * (xiMassWindowDefectConstant a sigma kappa / Real.sqrt u)
      * Real.exp (H / 2 - a * Real.sqrt (H ^ 2 - u ^ 2))
      * Real.exp (-(cE * H ^ ((1 : ℝ) / 10))) = B := ⟨_, rfl⟩
  have hBnn : 0 ≤ B := by
    rw [← hB]
    have : (0 : ℝ) ≤ CE * (xiMassWindowDefectConstant a sigma kappa / Real.sqrt u) :=
      mul_nonneg hCE (by positivity)
    positivity
  have hterm : ∀ h : ℝ, H ≤ h → h ≤ T →
      ‖((xiMassThetaLogDiscrepancy h : ℝ) : ℂ)
        * xiMassCriticalDampedFourierProfile a sigma u h‖ ≤ B := by
    intro h hHh hhT
    rw [← hB]
    refine window_pointwise_bound ha hsigma hkappa hu hcone hCE hcE hHh (hE h hHh hhT) ?_
    refine (norm_xiMassCriticalDampedFourierProfile_exterior_le ha0 hsigma hkappa hu
      (le_trans hcone hHh)).trans ?_
    have hnn : (0 : ℝ) ≤ Real.exp (-h / 2) * Real.exp (-(a * Real.sqrt (h ^ 2 - u ^ 2))) := by
      positivity
    have hstep : xiMassBesselExteriorSqrtConstant a sigma kappa / Real.sqrt u
        ≤ xiMassWindowDefectConstant a sigma kappa / Real.sqrt u :=
      div_le_div_of_nonneg_right hbess hrootpos.le
    nlinarith [hstep, hnn, Real.exp_pos (-h / 2),
      Real.exp_pos (-(a * Real.sqrt (h ^ 2 - u ^ 2)))]
  have htermD : ∀ h : ℝ, H ≤ h → h ≤ T →
      ‖((xiMassThetaLogDiscrepancy h : ℝ) : ℂ)
        * -(((Real.exp (-h / 2) : ℝ) : ℂ)
          * xiMassCriticalOutgoingDerivative a sigma u h)‖ ≤ B := by
    intro h hHh hhT
    rw [← hB]
    refine window_pointwise_bound ha hsigma hkappa hu hcone hCE hcE hHh (hE h hHh hhT) ?_
    refine (norm_xiMassDampedProfileDeriv_exterior_le ha0 hsigma hkappa hu
      (le_trans hcone hHh)).trans ?_
    have hnn : (0 : ℝ) ≤ Real.exp (-h / 2) * Real.exp (-(a * Real.sqrt (h ^ 2 - u ^ 2))) := by
      positivity
    have hstep : xiMassOutgoingDerivExteriorSqrtConstant a sigma kappa / Real.sqrt u
        ≤ xiMassWindowDefectConstant a sigma kappa / Real.sqrt u :=
      div_le_div_of_nonneg_right hout hrootpos.le
    nlinarith [hstep, hnn, Real.exp_pos (-h / 2),
      Real.exp_pos (-(a * Real.sqrt (h ^ 2 - u ^ 2)))]
  have hintbound : ‖∫ h in H..T, ((xiMassThetaLogDiscrepancy h : ℝ) : ℂ)
      * -(((Real.exp (-h / 2) : ℝ) : ℂ)
        * xiMassCriticalOutgoingDerivative a sigma u h)‖ ≤ B * |T - H| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
    intro x hx
    rw [Set.uIoc_of_le hHT] at hx
    exact htermD x hx.1.le hx.2
  have habs : |T - H| = T - H := abs_of_nonneg (by linarith)
  rw [habs] at hintbound
  have h1 := hterm T hHT le_rfl
  have h2 := hterm H le_rfl hHT
  have hsplit : ‖((xiMassThetaLogDiscrepancy T : ℝ) : ℂ)
        * xiMassCriticalDampedFourierProfile a sigma u T
      - ((xiMassThetaLogDiscrepancy H : ℝ) : ℂ)
        * xiMassCriticalDampedFourierProfile a sigma u H
      - ∫ h in H..T, ((xiMassThetaLogDiscrepancy h : ℝ) : ℂ)
        * -(((Real.exp (-h / 2) : ℝ) : ℂ)
          * xiMassCriticalOutgoingDerivative a sigma u h)‖
      ≤ B + B + B * (T - H) := by
    refine (norm_sub_le _ _).trans ?_
    have := (norm_sub_le (((xiMassThetaLogDiscrepancy T : ℝ) : ℂ)
      * xiMassCriticalDampedFourierProfile a sigma u T)
      (((xiMassThetaLogDiscrepancy H : ℝ) : ℂ)
        * xiMassCriticalDampedFourierProfile a sigma u H))
    linarith [this, h1, h2, hintbound]
  refine hsplit.trans (le_of_eq ?_)
  rw [← hB]
  ring

end

end RHTower
