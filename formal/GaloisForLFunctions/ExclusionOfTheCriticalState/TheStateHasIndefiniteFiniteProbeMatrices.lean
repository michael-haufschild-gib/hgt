import GaloisForLFunctions.BiScaleUncertainty.Observation.BoundedCoordinateSignCone
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheStateChangesSignOnEveryRay

/-!
# Finite probe matrices detect both signs on every critical-state tail

The compact coordinate `exp(u+T)` turns a tail into a bounded moment problem.
Polynomial-square sign detection converts the critical state's sign changes into
positive and negative finite Hankel quadratic forms of actual tail integrals.
These are multiplication-by-state forms; they are distinct from the Weil energy.
-/

open MeasureTheory Filter Set Polynomial
open scoped BigOperators
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations BiScaleUncertainty.Observation
noncomputable section

/-- Damped moments of the actual state on the ray `u < -T`. -/
def tailProbeMoment (F : ℝ → ℝ) (T : ℝ) (n : ℕ) : ℝ :=
  ∫ u in Iio (-T), F u * Real.exp ((10+(n:ℝ))*(u+T))

/-- A finite Hankel quadratic form in tail probe moments, indexed by a polynomial's support. -/
def tailProbeQuadratic (F : ℝ → ℝ) (T : ℝ) (P : Polynomial ℝ) : ℝ :=
  ∑ i ∈ P.support, ∑ j ∈ P.support,
    P.coeff i * P.coeff j * tailProbeMoment F T (i+j)

private lemma tail_coordinate_bound (T : ℝ) :
    ∀ᵐ u ∂volume.restrict (Iio (-T)), |Real.exp (u+T)| ≤ 1 := by
  filter_upwards [ae_restrict_mem measurableSet_Iio] with u hu
  rw [abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_one_iff.mpr
  change u < -T at hu
  linarith

private lemma tail_density_integrable {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) (T : ℝ) :
    Integrable (fun u => F u*Real.exp (10*(u+T))) (volume.restrict (Iio (-T))) := by
  have h := hF.integrable.integrableOn.bdd_mul
    (by fun_prop : AEStronglyMeasurable (fun u : ℝ => Real.exp (10*(u+T)))
      (volume.restrict (Iio (-T))))
    (c := 1) (by
      filter_upwards [ae_restrict_mem measurableSet_Iio] with u hu
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      apply Real.exp_le_one_iff.mpr
      change u < -T at hu
      linarith)
  simpa only [mul_comm] using h

private lemma tail_power_integrable {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (T : ℝ) (n : ℕ) : Integrable
      (fun u => Real.exp (u+T)^n*(F u*Real.exp (10*(u+T)))) (volume.restrict (Iio (-T))) := by
  apply (tail_density_integrable hF T).bdd_mul
    (by fun_prop : AEStronglyMeasurable (fun u : ℝ => Real.exp (u+T)^n)
      (volume.restrict (Iio (-T))))
  filter_upwards [tail_coordinate_bound T] with u hu
  simpa only [norm_pow,Real.norm_eq_abs] using pow_le_one₀ (abs_nonneg _) hu

lemma tailProbeMoment_eq_coordinate (F : ℝ → ℝ) (T : ℝ) (n : ℕ) :
    tailProbeMoment F T n =
      ∫ u in Iio (-T), Real.exp (u+T)^n*(F u*Real.exp (10*(u+T))) := by
  apply integral_congr_ae
  filter_upwards [] with u
  rw [← Real.exp_nat_mul]
  calc
    F u*Real.exp ((10+(n:ℝ))*(u+T)) =
        F u*(Real.exp ((n:ℝ)*(u+T))*Real.exp (10*(u+T))) := by
      rw [← Real.exp_add]
      congr 2
      ring
    _ = _ := by ring

/-- The finite moment matrix is exactly the integral of a polynomial-coordinate square. -/
theorem tailProbeQuadratic_eq_integral {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (T : ℝ) (P : Polynomial ℝ) :
    tailProbeQuadratic F T P =
      ∫ u in Iio (-T), (P.eval (Real.exp (u+T)))^2*(F u*Real.exp (10*(u+T))) := by
  have he (u : ℝ) : (P.eval (Real.exp (u+T)))^2*(F u*Real.exp (10*(u+T))) =
      ∑ i ∈ P.support, ∑ j ∈ P.support, P.coeff i*P.coeff j*
        (Real.exp (u+T)^(i+j)*(F u*Real.exp (10*(u+T)))) := by
    simp only [sq,Polynomial.eval_eq_sum,Polynomial.sum,Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [pow_add]
    ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun j _ => (tail_power_integrable hF T (i+j)).const_mul _))]
  unfold tailProbeQuadratic
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => (tail_power_integrable hF T (i+j)).const_mul _)]
  simp only [integral_const_mul,← tailProbeMoment_eq_coordinate]

/-- Every tail admits a finite moment quadratic form of each strict sign. -/
theorem criticalState_tailProbeQuadratic_both_signs {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A)=(W₀:EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) (T : ℝ) :
    (∃ P : Polynomial ℝ, tailProbeQuadratic F T P < 0) ∧
      ∃ P : Polynomial ℝ, 0 < tailProbeQuadratic F T P := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hs := criticalState_changes_sign_on_every_ray hW ht hF T
  have hφ : MeasurableEmbedding (fun u : ℝ => Real.exp (u+T)) :=
    (by fun_prop : Continuous (fun u : ℝ => Real.exp (u+T))).measurableEmbedding
      (fun u v h => add_right_cancel (Real.exp_injective h))
  let f : ℝ → ℝ := fun u => F u*Real.exp (10*(u+T))
  have hfm : Measurable f := hd.meas.mul (by fun_prop)
  have hfi : Integrable f (volume.restrict (Iio (-T))) := tail_density_integrable hd T
  constructor
  · by_contra h
    push Not at h
    have hp : ∀ P : Polynomial ℝ, 0 ≤ ∫ u in Iio (-T),
        P.eval (Real.exp (u+T))^2*f u := by
      intro P
      exact (tailProbeQuadratic_eq_integral hd T P) ▸ h P
    have hfpos := (density_nonnegative_iff_coordinate_squares hφ (tail_coordinate_bound T) hfm hfi).mp hp
    apply hs.1
    filter_upwards [hfpos] with u hu
    exact (mul_nonneg_iff_of_pos_right (Real.exp_pos _)).mp hu
  · by_contra h
    push Not at h
    have hp : ∀ P : Polynomial ℝ, 0 ≤ ∫ u in Iio (-T),
        P.eval (Real.exp (u+T))^2*(-f u) := by
      intro P
      simp_rw [mul_neg,integral_neg]
      have hq := h P
      rw [tailProbeQuadratic_eq_integral hd T P] at hq
      exact neg_nonneg.mpr hq
    have hfneg := (density_nonnegative_iff_coordinate_squares hφ (tail_coordinate_bound T)
      hfm.neg hfi.neg).mp hp
    apply hs.2
    filter_upwards [hfneg] with u hu
    change 0 ≤ -(F u*Real.exp (10*(u+T))) at hu
    rw [← neg_mul] at hu
    exact neg_nonneg.mp ((mul_nonneg_iff_of_pos_right (Real.exp_pos _)).mp hu)

/-- Unconditionally, RH holds or every critical-state tail has indefinite finite probe forms. -/
theorem riemannHypothesis_or_indefinite_tailProbeQuadratic :
    RiemannHypothesis ∨ ∃ (W₀ : ℝ) (F : ℝ → ℝ), 0 < W₀ ∧
      (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A)=(W₀:EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧ ∀ T : ℝ,
        (∃ P : Polynomial ℝ, tailProbeQuadratic F T P < 0) ∧
          ∃ P : Polynomial ℝ, 0 < tailProbeQuadratic F T P := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with hRH | ⟨W₀,F,hW,ht,hF⟩
  · exact Or.inl hRH
  · exact Or.inr ⟨W₀,F,hW,ht,hF,criticalState_tailProbeQuadratic_both_signs hW ht hF⟩

#print axioms tailProbeQuadratic_eq_integral
#print axioms criticalState_tailProbeQuadratic_both_signs
#print axioms riemannHypothesis_or_indefinite_tailProbeQuadratic
end
end GaloisForLFunctions.ExclusionOfTheCriticalState
