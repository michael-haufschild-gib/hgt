import GaloisForLFunctions.RHTower.ThetaFullArithmeticGroundForm
import GaloisForLFunctions.RHTower.ThetaGammaPolarKernelOrientation

/-!
# Polarization of the full arithmetic form on separated real profiles

For ordered disjoint profiles whose support differences avoid every prime
translation, all diagonal and prime cross differences cancel. The complete
quadratic difference is four times the continuous cross pairing. This retains
the Gamma and both pole terms in the literal arithmetic form.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped SchwartzMap

namespace RHTower.ThetaSourceWard

def thetaComplexify (phi : 𝓢(ℝ, ℝ)) : 𝓢(ℝ, ℂ) :=
  phi.postcompCLM Complex.ofRealCLM

@[simp] theorem thetaComplexify_apply (phi : 𝓢(ℝ, ℝ)) (x : ℝ) :
    thetaComplexify phi x = (phi x : ℂ) := rfl

def thetaRealArithmeticQuadratic (phi : 𝓢(ℝ, ℝ)) : ℝ :=
  thetaFullArithmeticQuadratic (thetaComplexify phi)

private theorem disjoint_product_zero (phi psi : 𝓢(ℝ, ℝ))
    (hsep : ∀ x ∈ Function.support psi, ∀ y ∈ Function.support phi, 0 < x - y)
    (x : ℝ) : phi x * psi x = 0 := by
  by_cases hp : phi x = 0
  · rw [hp, zero_mul]
  by_cases hq : psi x = 0
  · rw [hq, mul_zero]
  have := hsep x hq x hp
  linarith

private theorem reverse_product_zero (phi psi : 𝓢(ℝ, ℝ))
    (hsep : ∀ x ∈ Function.support psi, ∀ y ∈ Function.support phi, 0 < x - y)
    (x u : ℝ) (hu : 0 ≤ u) : phi (x + u) * psi x = 0 := by
  by_cases hp : phi (x + u) = 0
  · rw [hp, zero_mul]
  by_cases hq : psi x = 0
  · rw [hq, mul_zero]
  have := hsep x hq (x + u) hp
  linarith

private theorem prime_product_zero (phi psi : 𝓢(ℝ, ℝ))
    (hsep : ∀ x ∈ Function.support psi, ∀ y ∈ Function.support phi, 0 < x - y)
    (hatom : ∀ x ∈ Function.support psi, ∀ y ∈ Function.support phi,
      ∀ n : ℕ, 2 ≤ n → x - y ≠ Real.log n)
    (x : ℝ) (n : ℕ) : phi x * psi (x + Real.log n) = 0 := by
  by_cases hn : 2 ≤ n
  · by_cases hp : phi x = 0
    · rw [hp, zero_mul]
    by_cases hq : psi (x + Real.log n) = 0
    · rw [hq, mul_zero]
    exact False.elim (hatom _ hq _ hp n hn (by ring))
  · have hn' : n = 0 ∨ n = 1 := by omega
    rcases hn' with rfl | rfl <;>
      simpa using disjoint_product_zero phi psi hsep x

private theorem log_nat_nonneg (n : ℕ) : 0 ≤ Real.log n := by
  by_cases hn : n = 0
  · simp [hn]
  exact Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)

theorem thetaRealArithmeticQuadratic_ordered_difference
    (phi psi : 𝓢(ℝ, ℝ))
    (hsep : ∀ x ∈ Function.support psi, ∀ y ∈ Function.support phi, 0 < x - y)
    (hatom : ∀ x ∈ Function.support psi, ∀ y ∈ Function.support phi,
      ∀ n : ℕ, 2 ≤ n → x - y ≠ Real.log n) :
    thetaRealArithmeticQuadratic (phi + psi) -
        thetaRealArithmeticQuadratic (phi - psi) =
      4 * ∫ p : ℝ × ℝ, thetaGammaPolarScalingKernel p.1 *
        thetaCuspFullSource p.2 * thetaCuspFullSource (p.2 + p.1) *
          phi p.2 * psi (p.2 + p.1) ∂thetaContinuousLinkMeasure := by
  have hsq (x : ℝ) :
      ‖thetaComplexify (phi + psi) x‖ ^ 2 =
        ‖thetaComplexify (phi - psi) x‖ ^ 2 := by
    simp only [thetaComplexify_apply, add_apply, sub_apply,
      Complex.norm_real, Real.norm_eq_abs, sq_abs]
    nlinarith [disjoint_product_zero phi psi hsep x]
  have hnorm : thetaGroundNormSq (thetaComplexify (phi + psi)) =
      thetaGroundNormSq (thetaComplexify (phi - psi)) := by
    unfold thetaGroundNormSq thetaGroundNormDensity
    simp_rw [hsq]
  have hprime : thetaPrimeScalingCross thetaCuspTiltSource thetaCuspTiltSource
        (thetaComplexify (phi + psi)).toBoundedContinuousFunction =
      thetaPrimeScalingCross thetaCuspTiltSource thetaCuspTiltSource
        (thetaComplexify (phi - psi)).toBoundedContinuousFunction := by
    unfold thetaPrimeScalingCross
    apply integral_congr_ae
    filter_upwards with p
    have h₁ := reverse_product_zero phi psi hsep p.2 (Real.log p.1) (log_nat_nonneg p.1)
    have h₂ := prime_product_zero phi psi hsep hatom p.2 p.1
    simp only [thetaPrimeScalingCrossDensity, SchwartzMap.toBoundedContinuousFunction_apply,
      thetaComplexify_apply, add_apply, sub_apply,
      Complex.conj_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re]
    congr 1
    nlinarith
  have hpoint (p : ℝ × ℝ) (hp : 0 < p.1) :
      thetaGammaPolarQuadraticDensity thetaCuspTiltSource (thetaComplexify (phi + psi)) p -
        thetaGammaPolarQuadraticDensity thetaCuspTiltSource (thetaComplexify (phi - psi)) p =
      4 * (thetaGammaPolarScalingKernel p.1 * thetaCuspFullSource p.2 *
        thetaCuspFullSource (p.2 + p.1) * phi p.2 * psi (p.2 + p.1)) := by
    have hr := reverse_product_zero phi psi hsep p.2 p.1 hp.le
    unfold thetaGammaPolarQuadraticDensity
    rw [hsq, hsq]
    simp only [thetaCuspTiltSource_k,
      thetaComplexify_apply, add_apply, sub_apply,
      Complex.conj_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re]
    linear_combination 4 * thetaGammaPolarScalingKernel p.1 * thetaCuspFullSource p.2 *
      thetaCuspFullSource (p.2 + p.1) * hr
  unfold thetaRealArithmeticQuadratic thetaFullArithmeticQuadratic
  rw [hnorm, hprime]
  rw [show ∀ A B C D : ℝ, A - C - D - (B - C - D) = A - B by intros; ring]
  rw [← integral_sub (integrable_thetaGammaPolarQuadraticDensity _)
    (integrable_thetaGammaPolarQuadraticDensity _), ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [thetaContinuousLinkMeasure_ae_pos] with p hp
  exact hpoint p hp

private def groundCrossShear : ℝ × ℝ ≃ᵐ ℝ × ℝ where
  toFun p := (p.1 + p.2, p.2)
  invFun p := (p.1 - p.2, p.2)
  left_inv := by intro p; ext <;> simp
  right_inv := by intro p; ext <;> simp
  measurable_toFun := by change Measurable (fun p : ℝ × ℝ => (p.1 + p.2, p.2)); fun_prop
  measurable_invFun := by change Measurable (fun p : ℝ × ℝ => (p.1 - p.2, p.2)); fun_prop

theorem thetaOrderedGroundCross_eq_pairing (phi psi : 𝓢(ℝ, ℝ))
    (hsep : ∀ x ∈ Function.support psi, ∀ y ∈ Function.support phi, 0 < x - y) :
    (∫ p : ℝ × ℝ, thetaGammaPolarScalingKernel p.1 *
      thetaCuspFullSource p.2 * thetaCuspFullSource (p.2 + p.1) *
        phi p.2 * psi (p.2 + p.1) ∂thetaContinuousLinkMeasure) =
      thetaGammaPolarGroundCrossPairing phi psi := by
  let F : ℝ × ℝ → ℝ := fun p => thetaGammaPolarScalingKernel p.1 *
    thetaCuspFullSource p.2 * thetaCuspFullSource (p.2 + p.1) *
      phi p.2 * psi (p.2 + p.1)
  have hz (p : ℝ × ℝ) (hp : p ∉ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) : F p = 0 := by
    have hp' : p.1 ≤ 0 := by simpa using hp
    by_cases hphi : phi p.2 = 0
    · simp [F, hphi]
    by_cases hpsi : psi (p.2 + p.1) = 0
    · simp [F, hpsi]
    have := hsep _ hpsi _ hphi
    linarith
  change (∫ p, F p ∂thetaContinuousLinkMeasure) = _
  rw [thetaContinuousLinkMeasure, Measure.restrict_prod_eq_prod_univ,
    setIntegral_eq_integral_of_forall_compl_eq_zero hz]
  have hmp : MeasurePreserving groundCrossShear (volume.prod volume) (volume.prod volume) :=
    measurePreserving_add_prod volume volume
  rw [thetaGammaPolarGroundCrossPairing, Measure.volume_eq_prod]
  rw [← hmp.integral_comp' (fun p : ℝ × ℝ => thetaGammaPolarScalingKernel (p.1 - p.2) *
    thetaCuspFullSource p.1 * thetaCuspFullSource p.2 * phi p.2 * psi p.1)]
  apply integral_congr_ae
  filter_upwards with p
  simp only [groundCrossShear, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, add_sub_cancel_right, F]
  rw [add_comm p.1 p.2]
  ring

/-- Exact polarization after every arithmetic channel has been included. -/
theorem thetaRealArithmeticQuadratic_disjoint_polarization
    (phi psi : 𝓢(ℝ, ℝ))
    (hsep : ∀ x ∈ Function.support psi, ∀ y ∈ Function.support phi, 0 < x - y)
    (hatom : ∀ x ∈ Function.support psi, ∀ y ∈ Function.support phi,
      ∀ n : ℕ, 2 ≤ n → x - y ≠ Real.log n) :
    thetaRealArithmeticQuadratic (phi + psi) -
        thetaRealArithmeticQuadratic (phi - psi) =
      4 * thetaGammaPolarGroundCrossPairing phi psi := by
  rw [thetaRealArithmeticQuadratic_ordered_difference phi psi hsep hatom,
    thetaOrderedGroundCross_eq_pairing phi psi hsep]

end RHTower.ThetaSourceWard
