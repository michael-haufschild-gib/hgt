import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.LargestPrime.Conditioning.Law
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.LargestPrime.Conditioning.Fluctuations
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Probability.Moments.Variance

/-! # Exponential integrability and the moments of the limiting orientation law -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime

open Filter Topology Set MeasureTheory ProbabilityTheory _root_.RHTower _root_.RHTower.BAGTrace
open scoped ENNReal

theorem conditional_integral (c : ℝ) (h : Ioi (0:ℝ)) (f : ℝ → ℝ) :
    ∫ x, f x ∂(conditionalLaw c h : Measure ℝ) =
      ∑ d : CutStates c h, conditionalWeight c h d*f (measuredEnergy c h d) := by
  change (∫ x, f x ∂Measure.sum (fun d : CutStates c h =>
    ENNReal.ofReal (conditionalWeight c h d) • Measure.dirac (measuredEnergy c h d))) = _
  rw [integral_sum_dirac (by simp),tsum_fintype]
  exact Finset.sum_congr rfl fun d _ => by
    rw [ENNReal.toReal_ofReal (conditionalWeight_pos c h d).le,smul_eq_mul]

/-- The exponential probes are integrals against the finite conditioned probability measure. -/
theorem conditional_integral_probe (c : ℝ) (h : Ioi (0:ℝ)) (k : ℕ) (z : ℂ) :
    (∫ x : ℝ, (x:ℂ)^k*Complex.exp (z*(x:ℂ)) ∂(conditionalLaw c h : Measure ℝ)) = momentProbe c h k z := by
  change (∫ x : ℝ, (x:ℂ)^k*Complex.exp (z*(x:ℂ)) ∂Measure.sum (fun d : CutStates c h =>
    ENNReal.ofReal (conditionalWeight c h d) • Measure.dirac (measuredEnergy c h d))) = _
  rw [integral_sum_dirac (by simp),tsum_fintype,momentProbe]
  apply Finset.sum_congr rfl
  intro d _
  rw [ENNReal.toReal_ofReal (conditionalWeight_pos c h d).le,Complex.real_smul,mul_assoc]

private theorem real_probe (c r : ℝ) (h : Ioi (0:ℝ)) :
    (momentProbe c h 0 (r:ℂ)).re = ∑ d, conditionalWeight c h d*Real.exp (r*measuredEnergy c h d) := by
  have he : momentProbe c h 0 (r:ℂ) =
      ((∑ d, conditionalWeight c h d*Real.exp (r*measuredEnergy c h d):ℝ):ℂ) := by
    simp only [momentProbe,pow_zero,mul_one,Complex.ofReal_sum,Complex.ofReal_mul,Complex.ofReal_exp]
  rw [he,Complex.ofReal_re]

/-- Weak convergence transfers uniform finite exponential readings to integrability at every rate. -/
theorem cutoffLaw_exp_integrable {c : ℝ} (hc : 0 < c) (r : ℝ) :
    Integrable (fun x : ℝ => Real.exp (r*x)) (cutoffLaw c : Measure ℝ) := by
  letI : NeBot criticalApproach := criticalApproach_neBot
  let μ : Measure ℝ := cutoffLaw c
  let f := fun x : ℝ => Real.exp (r*x)
  have hf : Continuous f := Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have hp (x : ℝ) : 0 ≤ f x := (Real.exp_pos _).le
  let b := (limitTransform c (r:ℂ)).re+1
  have hlim := (Complex.continuous_re.tendsto _).comp (conditioned_transform_limit hc (r:ℂ))
  have hb : ∀ᶠ h in criticalApproach, (∑ d, conditionalWeight c h d*f (measuredEnergy c h d)) ≤ b := by
    filter_upwards [hlim.eventually_lt_const (lt_add_of_pos_right _ zero_lt_one)] with h hlim'
    have hh : (momentProbe c h 0 (r:ℂ)).re < b := hlim'
    rw [real_probe] at hh
    exact hh.le
  let test (j : ℕ) : BoundedContinuousFunction ℝ ℝ :=
    BoundedContinuousFunction.ofNormedAddCommGroup (fun x => min (f x) (j:ℝ)) (hf.min continuous_const)
      j (fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (le_min (hp x) (Nat.cast_nonneg j))]; exact min_le_right _ _)
  have hcap (j : ℕ) : ∫ x, test j x ∂μ ≤ b := by
    have H := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp (conditioned_weak_limit hc) (test j)
    apply le_of_tendsto H
    filter_upwards [hb] with h hh
    rw [conditional_integral]
    exact (Finset.sum_le_sum fun d _ => mul_le_mul_of_nonneg_left (min_le_left _ _) (conditionalWeight_pos c h d).le).trans hh
  let g := fun (j : ℕ) (x : ℝ) => ENNReal.ofReal (min (f x) (j:ℝ))
  have hmeas (j : ℕ) : Measurable (g j) := ENNReal.measurable_ofReal.comp (hf.measurable.min measurable_const)
  have hmono : Monotone g := fun i j hij x => ENNReal.ofReal_le_ofReal (min_le_min le_rfl (by exact_mod_cast hij))
  have hsup : (fun x => ⨆ j, g j x) = fun x => ENNReal.ofReal (f x) := by
    funext x
    apply le_antisymm (iSup_le fun j => ENNReal.ofReal_le_ofReal (min_le_left _ _))
    obtain ⟨j,hj⟩ := exists_nat_ge (f x)
    exact (show ENNReal.ofReal (f x) = g j x by dsimp [g]; rw [min_eq_left hj]).le.trans
      (le_iSup (fun j => g j x) j)
  change Integrable f μ
  refine ⟨hf.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (Eventually.of_forall hp)).mpr ?_⟩
  change (∫⁻ x, ENNReal.ofReal (f x) ∂μ) < ⊤
  rw [← hsup,lintegral_iSup hmeas hmono]
  refine lt_of_le_of_lt (iSup_le fun j => ?_) (ENNReal.ofReal_lt_top (r := b))
  have he := ofReal_integral_eq_lintegral_ofReal ((test j).integrable μ)
    (Eventually.of_forall fun x => (show 0 ≤ test j x from le_min (hp x) (Nat.cast_nonneg j)))
  exact he.ge.trans (ENNReal.ofReal_le_ofReal (hcap j))

private theorem exp_set {c : ℝ} (hc : 0 < c) :
    integrableExpSet id (cutoffLaw c : Measure ℝ) = univ :=
  eq_univ_of_forall fun r => cutoffLaw_exp_integrable hc r

/-- The entire limit of the finite transforms is the moment generating function of the limiting law. -/
theorem complexMGF_cutoffLaw {c : ℝ} (hc : 0 < c) :
    complexMGF id (cutoffLaw c : Measure ℝ) = limitTransform c := by
  have he : AnalyticOnNhd ℂ (complexMGF id (cutoffLaw c : Measure ℝ)) univ := by
    intro z _
    apply analyticAt_complexMGF
    simp [exp_set hc]
  have hF : Differentiable ℂ criticalEulerCarrier := fun u => ((criticalEulerExponent_hasDerivAt u).cexp).differentiableAt
  have hg : Differentiable ℂ (limitTransform c) := by
    unfold limitTransform
    have ha : Differentiable ℂ (fun z : ℂ => (c:ℂ)*(z-1)) := by fun_prop
    exact (hF.comp ha).div_const _
  apply he.eq_of_frequently_eq (hg.differentiableOn.analyticOnNhd isOpen_univ) (z₀ := 0)
  have hi : Tendsto (fun t : ℝ => (t:ℂ)*Complex.I) (𝓝[>] 0) (𝓝[≠] (0:ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hh : Continuous (fun t : ℝ => (t:ℂ)*Complex.I) := Complex.continuous_ofReal.mul continuous_const
      simpa only [Complex.ofReal_zero,zero_mul] using (hh.tendsto 0).mono_left
        (show 𝓝[>] (0:ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
    · filter_upwards [self_mem_nhdsWithin] with t ht
      change (t:ℂ)*Complex.I ≠ 0
      exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (show 0 < t from ht).ne') Complex.I_ne_zero
  apply hi.frequently
  exact Frequently.of_forall fun t => (complexMGF_id_mul_I t).trans (charFun_cutoffLaw c t)

/-- The measured moments converge to the corresponding integrals of the weak limit. -/
theorem true_moment_limit {c : ℝ} (hc : 0 < c) (k : ℕ) (z : ℂ) :
    Tendsto (fun h => momentProbe c h k z) criticalApproach
      (𝓝 (∫ x : ℝ, (x:ℂ)^k*Complex.exp (z*(x:ℂ)) ∂(cutoffLaw c : Measure ℝ))) := by
  have hz : z.re ∈ interior (integrableExpSet id (cutoffLaw c : Measure ℝ)) := by simp [exp_set hc]
  have H := conditioned_jet_limit hc k (tendsto_const_nhds (x := z))
  rw [← complexMGF_cutoffLaw hc,iteratedDeriv_complexMGF hz] at H
  exact H

/-- Real raw moments of the limiting probability law are the derivatives at zero. -/
theorem cutoffLaw_moment {c : ℝ} (hc : 0 < c) (k : ℕ) :
    ((∫ x : ℝ, x^k ∂(cutoffLaw c : Measure ℝ) : ℝ):ℂ) = iteratedDeriv k (limitTransform c) 0 := by
  have hz : (0:ℝ) ∈ interior (integrableExpSet id (cutoffLaw c : Measure ℝ)) := by simp [exp_set hc]
  rw [← complexMGF_cutoffLaw hc,iteratedDeriv_complexMGF (z := 0) hz]
  simp only [id_eq,zero_mul,Complex.exp_zero,mul_one,← Complex.ofReal_pow,integral_complex_ofReal]

theorem cutoffLaw_mean {c : ℝ} (hc : 0 < c) :
    (∫ x : ℝ, x ∂(cutoffLaw c : Measure ℝ)) = 1-Real.exp (-c) := by
  apply Complex.ofReal_injective
  simpa only [pow_one] using (cutoffLaw_moment hc 1).trans (first_jet hc)

theorem cutoffLaw_variance {c : ℝ} (hc : 0 < c) :
    variance id (cutoffLaw c : Measure ℝ) = 1-(1+c)*Real.exp (-c) := by
  have hz : (0:ℝ) ∈ interior (integrableExpSet id (cutoffLaw c : Measure ℝ)) := by simp [exp_set hc]
  have hsq : Integrable (fun x : ℝ => x^2) (cutoffLaw c : Measure ℝ) := by
    simpa only [id_eq,zero_mul,Real.exp_zero,mul_one] using
      integrable_pow_mul_exp_of_mem_interior_integrableExpSet hz 2
  rw [variance_eq_sub ((memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).mpr hsq)]
  change (∫ x : ℝ, x^2 ∂(cutoffLaw c : Measure ℝ))-(∫ x : ℝ, x ∂(cutoffLaw c : Measure ℝ))^2 = _
  have hm : (∫ x : ℝ, x^2 ∂(cutoffLaw c : Measure ℝ)) =
      (1-(1+c)*Real.exp (-c))+(1-Real.exp (-c))^2 :=
    Complex.ofReal_injective ((cutoffLaw_moment hc 2).trans (second_jet hc))
  rw [cutoffLaw_mean hc,hm,add_sub_cancel_right]

#print axioms conditional_integral
#print axioms conditional_integral_probe
#print axioms cutoffLaw_exp_integrable
#print axioms complexMGF_cutoffLaw
#print axioms true_moment_limit
#print axioms cutoffLaw_moment
#print axioms cutoffLaw_mean
#print axioms cutoffLaw_variance

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime
