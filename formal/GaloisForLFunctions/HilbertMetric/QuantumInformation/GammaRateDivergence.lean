import GaloisForLFunctions.HilbertMetric.QuantumInformation.GammaCauchyAffinity
import Mathlib.InformationTheory.KullbackLeibler.Basic

/-!
# Relative entropy of the Gamma realization of Cauchy dephasing

At fixed shape, the log likelihood ratio is affine in the observation.
Size bias increases shape by one, giving its expectation directly. The
symmetrized Kullback–Leibler divergence is determined by the same Cauchy
coherence that governs the scattering phase.
-/

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real
open scoped ENNReal
namespace GaloisForLFunctions.HilbertMetric.CauchyDephasing.GammaAffinity

def law (a : Shape) (s : ℝ) := gammaMeasure a.val (exp s)

instance law_probability (a : Shape) (s : ℝ) : IsProbabilityMeasure (law a s) :=
  isProbabilityMeasure_gammaMeasure a.property (exp_pos s)

private def pdf (a : Shape) (s x : ℝ) := ENNReal.ofReal (density a s x)
private theorem pdf_measurable (a : Shape) (s : ℝ) : Measurable (pdf a s) :=
  ENNReal.measurable_ofReal.comp (measurable_gammaPDFReal _ _)

private def raised (a : Shape) : Shape := ⟨a.val+1,by linarith only [a.property]⟩

private theorem size_bias (a : Shape) (s : ℝ) :
    (fun x => density a s x*x) =ᵐ[volume] fun x => a.val/exp s*density (raised a) s x := by
  filter_upwards [Measure.ae_ne volume (0:ℝ)] with x hx
  by_cases hp : 0<x
  · have hxpow : x^(a.val-1)*x=x^a.val := by rw [← Real.rpow_add_one hp.ne',sub_add_cancel]
    simp only [density,gammaPDFReal,if_pos hp.le,raised,add_sub_cancel_right,
      Real.Gamma_add_one a.property.ne',Real.rpow_add_one (exp_pos s).ne']
    rw [← hxpow]
    field_simp [(Real.Gamma_pos_of_pos a.property).ne',a.property.ne',Real.exp_ne_zero]
    ring
  · have hn : ¬0≤x := not_le.mpr (lt_of_le_of_ne (le_of_not_gt hp) hx)
    simp [density,gammaPDFReal,hn]

private theorem mean_integrable (a : Shape) (s : ℝ) : Integrable (fun x : ℝ => x) (law a s) := by
  change Integrable _ (volume.withDensity (pdf a s))
  rw [integrable_withDensity_iff_integrable_smul' (pdf_measurable _ _)
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  have h := ((density_integrable (raised a) s).const_mul (a.val/exp s)).congr (size_bias a s).symm
  simpa only [pdf,ENNReal.toReal_ofReal (gammaPDFReal_nonneg a.property (exp_pos s) _),smul_eq_mul] using h

/-- Size bias by the observed position raises the shape by one. -/
theorem mean (a : Shape) (s : ℝ) : (∫ x : ℝ, x ∂law a s)=a.val/exp s := by
  change (∫ x : ℝ, x ∂volume.withDensity (pdf a s))=_
  rw [integral_withDensity_eq_integral_toReal_smul (pdf_measurable _ _)
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  have h := integral_congr_ae (size_bias a s)
  rw [integral_const_mul,density_mass,mul_one] at h
  simpa only [pdf,ENNReal.toReal_ofReal (gammaPDFReal_nonneg a.property (exp_pos s) _),smul_eq_mul] using h

private def score (a : Shape) (s t x : ℝ) := a.val*(s-t)+(exp t-exp s)*x

private theorem change_law (a : Shape) (s t : ℝ) :
    law a s=(law a t).withDensity (fun x => ENNReal.ofReal (exp (score a s t x))) := by
  change volume.withDensity (pdf a s)=(volume.withDensity (pdf a t)).withDensity _
  rw [← withDensity_mul volume (pdf_measurable _ _) (by unfold score; fun_prop)]
  apply withDensity_congr_ae
  apply ae_of_all
  intro x
  simp only [pdf,Pi.mul_apply,density_change_rate a s t,score,ENNReal.ofReal_mul (exp_pos _).le,mul_comm]

/-- The actual log likelihood ratio under the probability measure. -/
theorem log_likelihood (a : Shape) (s t : ℝ) : llr (law a s) (law a t) =ᵐ[law a s] score a s t := by
  have ac : law a s ≪ law a t := by rw [change_law a s t]; exact withDensity_absolutelyContinuous _ _
  have h : (law a s).rnDeriv (law a t) =ᵐ[law a t] fun x => ENNReal.ofReal (exp (score a s t x)) := by
    conv_lhs => rw [change_law a s t]
    exact Measure.rnDeriv_withDensity _ (by unfold score; fun_prop)
  filter_upwards [ac.ae_le h] with x hx
  simp only [llr,hx,ENNReal.toReal_ofReal (exp_pos _).le,log_exp]

/-- Relative entropy of the two actual Gamma laws at arbitrary log-rates. -/
theorem rate_kl (a : Shape) (s t : ℝ) :
    let D := klDiv (law a s) (law a t)
    D≠⊤ ∧ D.toReal=a.val*(s-t+exp (t-s)-1) := by
  have ac : law a s ≪ law a t := by rw [change_law a s t]; exact withDensity_absolutelyContinuous _ _
  have hlin := (mean_integrable a s).const_mul (exp t-exp s)
  have hi : Integrable (score a s t) (law a s) := (integrable_const _).add hlin
  have hl := log_likelihood a s t
  refine ⟨klDiv_ne_top ac (hi.congr hl.symm),?_⟩
  rw [toReal_klDiv_of_measure_eq ac (by simp),integral_congr_ae hl]
  unfold score
  rw [integral_add (integrable_const _) hlin,integral_const,probReal_univ,one_smul,
    integral_const_mul,mean,exp_sub]
  field_simp [exp_ne_zero] <;> ring

/-- The symmetrized true divergence is four times shape times the
squared reciprocal coherence defect. -/
theorem jeffreys_coherence (a : Shape) (s t : ℝ) :
    (klDiv (law a s) (law a t)).toReal+(klDiv (law a t) (law a s)).toReal =
      4*a.val*((coherence s t)⁻¹^2-1) := by
  rw [(rate_kl a s t).2,(rate_kl a t s).2,coherence_eq_cosh_inv,inv_inv]
  rw [Real.cosh_eq,exp_sub,exp_sub]
  let u := exp ((s-t)/2)
  have hu : u^2=exp s/exp t := by rw [← exp_sub]; unfold u; rw [pow_two,← exp_add,add_halves]
  have hu' : exp t/exp s=(u^2)⁻¹ := by rw [hu,inv_div]
  change _=4*a.val*(((u+exp (-((s-t)/2)))/2)^2-1)
  rw [exp_neg,hu',← hu]
  change _=4*a.val*(((u+u⁻¹)/2)^2-1)
  field_simp [show u≠0 from exp_ne_zero _] <;> ring

end GaloisForLFunctions.HilbertMetric.CauchyDephasing.GammaAffinity
