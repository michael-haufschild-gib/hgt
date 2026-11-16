import GaloisForLFunctions.HTGeometry.BurnolDepthCompletion
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheCriticalHalfLineStateIsUniqueUpToSign

/-!
# Critical-state probe samples have no finite recurrence

Exponential compactification turns arithmetic probe samples into moments of an
integrable signed density. A finite recurrence would annihilate that density by
a polynomial. Injectivity of the coordinate and the finite root set of a nonzero
polynomial force the density to vanish, contradicting state normalization.

Thus constant-coefficient recurrences cannot encode the sampled transform exactly:
every nonzero polynomial recurrence fails at arbitrarily late finite probe indices.
The complete arithmetic probe sequence nevertheless determines every energy-domain profile.
-/

open MeasureTheory Filter Set Polynomial
open scoped BigOperators
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations
noncomputable section

private lemma coordinate_power_integrable {μ : Measure ℝ} {φ f : ℝ → ℝ}
    (hφ : MeasurableEmbedding φ) (hb : ∀ᵐ x ∂μ, |φ x| ≤ 1) (hf : Integrable f μ) (n : ℕ) :
    Integrable (fun x => φ x^n*f x) μ := by
  apply hf.bdd_mul (hφ.measurable.pow_const n).aestronglyMeasurable
  filter_upwards [hb] with x hx
  simpa only [norm_pow,Real.norm_eq_abs] using pow_le_one₀ (abs_nonneg (φ x)) hx

/-- An atomless signed moment law in an injective bounded coordinate has no nonzero annihilator. -/
theorem ae_eq_zero_of_coordinate_recurrence {μ : Measure ℝ} [NullSingletonClass μ] {φ f : ℝ → ℝ}
    (hφ : MeasurableEmbedding φ) (hb : ∀ᵐ x ∂μ, |φ x| ≤ 1) (hf : Integrable f μ)
    {P : Polynomial ℝ} (hP : P ≠ 0)
    (hrec : ∀ n : ℕ, ∑ j ∈ P.support, P.coeff j * (∫ x, φ x^(n+j)*f x ∂μ)=0) :
    f =ᵐ[μ] 0 := by
  have heval (x : ℝ) : P.eval (φ x)*f x =
      ∑ j ∈ P.support, P.coeff j*(φ x^j*f x) := by
    rw [Polynomial.eval_eq_sum,Polynomial.sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hpoly : Integrable (fun x => P.eval (φ x)*f x) μ := by
    simp_rw [heval]
    exact integrable_finsetSum _ fun j _ => (coordinate_power_integrable hφ hb hf j).const_mul _
  have hzero : (fun x => P.eval (φ x)*f x) =ᵐ[μ] 0 := by
    apply _root_.HTGeometry.ae_eq_zero_of_boundedCoordinate_moments hφ hb hpoly
    intro n
    have hterm (x : ℝ) : φ x^n*(P.eval (φ x)*f x)=
        ∑ j ∈ P.support, P.coeff j*(φ x^(n+j)*f x) := by
      rw [heval,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [pow_add]
      ring
    simp_rw [hterm]
    rw [integral_finsetSum _ (fun j _ => (coordinate_power_integrable hφ hb hf (n+j)).const_mul _)]
    simp_rw [integral_const_mul]
    exact hrec n
  have hfinite : {x : ℝ | P.eval (φ x)=0}.Finite :=
    (Polynomial.finite_setOf_isRoot hP).preimage hφ.injective.injOn
  have hne : ∀ᵐ x ∂μ, P.eval (φ x) ≠ 0 := by
    apply ae_iff.mpr
    simpa only [not_not] using hfinite.measure_zero (μ := μ)
  filter_upwards [hzero,hne] with x hx hn
  exact (mul_eq_zero.mp hx).resolve_left hn

/-- Arithmetic samples on the actual probe line `p=5+n`, inside the energy domain. -/
def criticalProbeSample (F : ℝ → ℝ) (n : ℕ) : ℝ :=
  ∫ u, F u*Real.exp ((5+(n:ℝ))*u)

lemma criticalProbeSample_eq_coordinate {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (n : ℕ) :
    criticalProbeSample F n =
      ∫ u in Iio (0:ℝ), Real.exp u^n*(F u*Real.exp (5*u)) := by
  rw [criticalProbeSample,← integral_indicator measurableSet_Iio]
  apply integral_congr_ae
  filter_upwards [] with u
  by_cases hu : u < 0
  · simp only [Set.indicator,mem_Iio,hu,if_true]
    rw [← Real.exp_nat_mul]
    calc
      F u*Real.exp ((5+(n:ℝ))*u) = F u*(Real.exp ((n:ℝ)*u)*Real.exp (5*u)) := by
        rw [← Real.exp_add]
        congr 2
        ring
      _ = Real.exp ((n:ℝ)*u)*(F u*Real.exp (5*u)) := by ring
  · simp only [Set.indicator,mem_Iio,hu,if_false,hF.support u (le_of_not_gt hu),zero_mul]

/-- A polynomial recurrence would force an energy-domain profile itself to vanish. -/
theorem ae_eq_zero_of_criticalProbeSample_recurrence {F : ℝ → ℝ}
    (hd : CriticalHalfLineEnergyDomain F) {P : Polynomial ℝ} (hP : P ≠ 0) (N : ℕ)
    (hrec : ∀ n : ℕ, ∑ j ∈ P.support, P.coeff j*criticalProbeSample F (N+n+j)=0) :
    F =ᵐ[volume] 0 := by
  have hφ : MeasurableEmbedding Real.exp := Real.continuous_exp.measurableEmbedding Real.exp_injective
  have hb : ∀ᵐ u ∂(volume.restrict (Iio (0:ℝ))), |Real.exp u| ≤ 1 := by
    filter_upwards [ae_restrict_mem measurableSet_Iio] with u hu
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (le_of_lt hu)
  have hint : Integrable (fun u => F u*Real.exp (5*u)) (volume.restrict (Iio (0:ℝ))) :=
    (integrable_halfLineLaplace_of_domain hd (s := 5) (by norm_num)).integrableOn
  have hrec' (n : ℕ) : ∑ j ∈ P.support, P.coeff j *
      (∫ u in Iio (0:ℝ), Real.exp u^(n+j)*(Real.exp u^N*(F u*Real.exp (5*u))))=0 := by
    calc
      _ = ∑ j ∈ P.support, P.coeff j*criticalProbeSample F (N+n+j) := ?_
      _ = 0 := hrec n
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    rw [criticalProbeSample_eq_coordinate hd]
    apply integral_congr_ae
    filter_upwards [] with u
    simp only [pow_add]
    ring
  have hz := ae_eq_zero_of_coordinate_recurrence hφ hb
    (coordinate_power_integrable hφ hb hint N) hP hrec' 
  show F =ᵐ[volume] 0
  have hr := (ae_restrict_iff' measurableSet_Iio).mp hz
  filter_upwards [hr] with u hu
  by_cases hneg : u < 0
  · have hz' := (mul_eq_zero.mp (hu hneg)).resolve_left (pow_ne_zero N (Real.exp_ne_zero u))
    exact (mul_eq_zero.mp hz').resolve_right (Real.exp_ne_zero _)
  · exact hd.support u (le_of_not_gt hneg)


/-- Every finite recurrence fails arbitrarily far along the critical state's probe sequence. -/
theorem criticalProbeSample_recurrence_fails_after {W₀ : ℝ} {F : ℝ → ℝ}
    (hF : IsCriticalHalfLineGroundState W₀ F) {P : Polynomial ℝ} (hP : P ≠ 0) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ (∑ j ∈ P.support, P.coeff j*criticalProbeSample F (n+j)) ≠ 0 := by
  by_contra h
  push Not at h
  have hzero := ae_eq_zero_of_criticalProbeSample_recurrence
    (criticalHalfLineEnergyDomain_of_groundState hF) hP N
    (fun n => h (N+n) (Nat.le_add_right N n))
  have hnorm : (∫ u, F u^2)=0 := by
    calc
      _ = ∫ _u : ℝ, (0:ℝ) := by
        apply integral_congr_ae
        filter_upwards [hzero] with u hu
        rw [hu]
        norm_num
      _ = 0 := integral_zero _ _
  rw [hF.2.2.2.1] at hnorm
  exact one_ne_zero hnorm

/-- No exact finite recurrence holds for the normalized critical state. -/
theorem criticalProbeSample_no_recurrence {W₀ : ℝ} {F : ℝ → ℝ}
    (hF : IsCriticalHalfLineGroundState W₀ F) {P : Polynomial ℝ} (hP : P ≠ 0) :
    ∃ n : ℕ, (∑ j ∈ P.support, P.coeff j*criticalProbeSample F (n+j)) ≠ 0 := by
  obtain ⟨n,_,hn⟩ := criticalProbeSample_recurrence_fails_after hF hP 0
  exact ⟨n,hn⟩

/-- Unconditionally, RH holds or the critical state's sample sequence defeats every finite recurrence. -/
theorem riemannHypothesis_or_criticalProbeSamples_no_recurrence :
    RiemannHypothesis ∨ ∃ (W₀ : ℝ) (F : ℝ → ℝ), 0 < W₀ ∧
      (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A)=(W₀:EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧
      ∀ P : Polynomial ℝ, P ≠ 0 → ∀ N : ℕ,
        ∃ n : ℕ, N ≤ n ∧ (∑ j ∈ P.support, P.coeff j*criticalProbeSample F (n+j)) ≠ 0 := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with hRH | ⟨W₀,F,hW,ht,hF⟩
  · exact Or.inl hRH
  · exact Or.inr ⟨W₀,F,hW,ht,hF,fun _ hP N => criticalProbeSample_recurrence_fails_after hF hP N⟩


/-- The complete arithmetic probe sequence determines every energy-domain profile almost everywhere. -/
theorem criticalProbeSample_eq_iff_ae {F G : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hG : CriticalHalfLineEnergyDomain G) :
    criticalProbeSample F=criticalProbeSample G ↔ F =ᵐ[volume] G := by
  constructor
  · intro h
    have hd : CriticalHalfLineEnergyDomain (fun u => F u-G u) := by
      simpa only [neg_one_mul,← sub_eq_add_neg] using hF.add_const_mul hG (-1)
    have hz : ∀ n : ℕ, criticalProbeSample (fun u => F u-G u) n=0 := by
      intro n
      unfold criticalProbeSample
      simp_rw [sub_mul]
      rw [integral_sub
        (integrable_halfLineLaplace_of_domain hF (s := 5+n) (by positivity))
        (integrable_halfLineLaplace_of_domain hG (s := 5+n) (by positivity))]
      exact sub_eq_zero.mpr (congrFun h n)
    have hzero := ae_eq_zero_of_criticalProbeSample_recurrence hd
      (P := (1 : Polynomial ℝ)) one_ne_zero 0 (fun n => by
        classical
        simpa [Polynomial.coeff_one,ite_mul] using hz n)
    filter_upwards [hzero] with u hu
    exact sub_eq_zero.mp hu
  · intro h
    funext n
    apply integral_congr_ae
    filter_upwards [h] with u hu
    rw [hu]

#print axioms criticalProbeSample_eq_iff_ae

#print axioms ae_eq_zero_of_coordinate_recurrence
#print axioms criticalProbeSample_recurrence_fails_after
#print axioms criticalProbeSample_no_recurrence
#print axioms riemannHypothesis_or_criticalProbeSamples_no_recurrence
end
end GaloisForLFunctions.ExclusionOfTheCriticalState
