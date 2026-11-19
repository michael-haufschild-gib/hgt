import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.Analysis.LogCellGaussianGrid
import GaloisForLFunctions.HTGeometry.GaussianFormationRateRegion
import GaloisForLFunctions.HTGeometry.ConstitutiveGlobalFormationInformationProperness

/-!
# An entropy obstruction invisible to weak convergence

A randomized one-bit test records a cosine Fourier coefficient. At reciprocal
mesh frequency it gives distinct Bernoulli laws for the uniform position cell
and its Gaussian mixture, at every refinement. Data processing gives an explicit
strictly positive lower bound on the full forward relative entropy.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells.GaussianGrid
open MeasureTheory ProbabilityTheory InformationTheory Set HTGeometry
open scoped ENNReal ProbabilityTheory

private def acceptance (t x : ℝ) : unitInterval :=
  ⟨(1+Real.cos (t*x))/2,by
    constructor <;> linarith only [Real.neg_one_le_cos (t*x),Real.cos_le_one (t*x)]⟩

private theorem acceptance_mass (p : unitInterval) :
    (unitInterval.toNNReal p : ℝ≥0∞) = ENNReal.ofReal (p:ℝ) :=
  ENNReal.ofReal_coe_nnreal.symm

/-- The binary Fourier experiment accepts x with probability (1+cos(tx))/2. -/
def cosineSensor (t : ℝ) : Kernel ℝ Bool where
  toFun x := bernoulliMeasure true false (acceptance t x)
  measurable' := by
    classical
    apply Measure.measurable_of_measurable_coe
    intro s hs
    simp_rw [bernoulliMeasure_apply _ hs]
    split_ifs <;> first
      | exact measurable_const
      | simp only [acceptance_mass,unitInterval.coe_symm_eq,acceptance]; fun_prop

instance (t : ℝ) : IsMarkovKernel (cosineSensor t) :=
  ⟨fun x => inferInstanceAs (IsProbabilityMeasure (bernoulliMeasure true false (acceptance t x)))⟩

/-- Acceptance probability averaged over a general input measure. -/
def cosineProbability (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) : unitInterval :=
  ⟨(1+(charFun μ t).re)/2,by
    have ha := (Complex.abs_re_le_norm (charFun μ t)).trans (norm_charFun_le_one t)
    constructor <;> linarith only [(abs_le.mp ha).1,(abs_le.mp ha).2]⟩

private theorem integral_cosine (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) :
    ∫ x, Real.cos (t*x) ∂μ = (charFun μ t).re := by
  let f := fun x : ℝ => Complex.exp ((t:ℂ)*x*Complex.I)
  have hf : Integrable f μ := (integrable_const (1:ℝ)).mono' (by dsimp [f]; fun_prop)
    (Filter.Eventually.of_forall fun x => by simp [f,Complex.norm_exp])
  rw [charFun_apply_real]
  change _ = (∫ x, f x ∂μ).re
  calc
    _ = ∫ x, (f x).re ∂μ := integral_congr_ae (Filter.Eventually.of_forall fun x => by
      simp [f,← Complex.ofReal_mul,Complex.exp_mul_I])
    _ = _ := integral_re hf

/-- The binary output is determined by one characteristic-function value. -/
theorem cosine_output (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) :
    cosineSensor t ∘ₘ μ = bernoulliMeasure true false (cosineProbability μ t) := by
  have hi : Integrable (fun x : ℝ => Real.cos (t*x)) μ :=
    (integrable_const (1:ℝ)).mono' (by fun_prop) <|
      Filter.Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs] using abs_le.mpr ⟨Real.neg_one_le_cos _,Real.cos_le_one _⟩
  have ha : Integrable (fun x => (1+Real.cos (t*x))/2) μ := ((integrable_const 1).add hi).div_const 2
  have hval (x : ℝ) : cosineSensor t x {true} = ENNReal.ofReal ((1+Real.cos (t*x))/2) := by
    change bernoulliMeasure true false (acceptance t x) {true} = _
    rw [bernoulliMeasure_apply_of_mem_of_notMem _ (measurableSet_singleton _) (by simp) (by simp)]
    exact acceptance_mass (acceptance t x)
  have htrue : (cosineSensor t ∘ₘ μ).real {true} = cosineProbability μ t := by
    rw [Measure.real,Measure.bind_apply (measurableSet_singleton _) (cosineSensor t).aemeasurable]
    simp_rw [hval]
    have pos (x : ℝ) : 0 ≤ (1+Real.cos (t*x))/2 := (acceptance t x).2.1
    have ipos : 0 ≤ ∫ x, (1+Real.cos (t*x))/2 ∂μ := integral_nonneg pos
    rw [← ofReal_integral_eq_lintegral_ofReal ha (Filter.Eventually.of_forall pos),
      ENNReal.toReal_ofReal ipos,
      integral_div,integral_add (integrable_const _) hi,integral_const,integral_cosine]
    simp [cosineProbability]
  apply Measure.ext_of_measureReal_singleton
  rintro (_|_)
  · have hc : ({false} : Set Bool) = {true}ᶜ := by ext b; cases b <;> simp
    rw [hc,measureReal_compl (measurableSet_singleton _),measureReal_compl (measurableSet_singleton _),htrue]
    simp only [probReal_univ]
    simp
  · rw [htrue]
    simp

/-- Binary relative entropy of any cosine observation bounds the full relative entropy. -/
theorem cosine_information (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (t : ℝ) :
    klDiv (bernoulliMeasure true false (cosineProbability μ t))
      (bernoulliMeasure true false (cosineProbability ν t)) ≤ klDiv μ ν := by
  rw [← cosine_output,← cosine_output]
  exact klDiv_comp_le _ _ _

/-- The exact Bernoulli lower bound is independent of how fine the mesh is. -/
def aliasCost : ℝ := -Real.log (1-Real.exp (-Real.pi^2/6)^2)/2

theorem aliasCost_pos : 0 < aliasCost := by
  have h : Real.exp (-Real.pi^2/6) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith only [Real.pi_pos,sq_pos_of_pos Real.pi_pos])
  have h0 := Real.exp_pos (-Real.pi^2/6)
  have h1 := Real.log_neg
    (show 0 < 1-Real.exp (-Real.pi^2/6)^2 by nlinarith only [mul_pos (sub_pos.mpr h) (add_pos zero_lt_one h0)])
    (show 1-Real.exp (-Real.pi^2/6)^2 < 1 by linarith only [sq_pos_of_pos h0])
  unfold aliasCost
  linarith only [h1]

/-- Weak convergence of the projected mixtures coexists with a positive KL gap. -/
theorem mesh_entropy_gap (n : ℕ) :
    ENNReal.ofReal aliasCost ≤ klDiv (unitIntervalProbabilityMeasure : Measure ℝ) (mixture n) := by
  let a := Real.exp (-Real.pi^2/6)
  have ha : 0 < a := Real.exp_pos _
  have hb : a < 1 := Real.exp_lt_one_iff.mpr (by nlinarith only [sq_pos_of_pos Real.pi_pos])
  let U : Measure ℝ := unitIntervalProbabilityMeasure
  let p := cosineProbability U (reciprocal n)
  let q := cosineProbability (mixture n) (reciprocal n)
  have hp : (p:ℝ) = 1/2 := by
    simp [p,U,cosineProbability,(mesh_characteristic n).1]
  have hq : (q:ℝ) = (1-a)/2 := by
    change (1+(charFun (mixture n) (reciprocal n)).re)/2=(1-a)/2
    rw [(mesh_characteristic n).2,Complex.neg_re,Complex.ofReal_re]
    change (1+-a)/2=(1-a)/2
    ring
  have hq0 : 0 < (q:ℝ) := by linarith only [hb,hq]
  have hq1 : (q:ℝ) < 1 := by linarith only [ha,hq]
  have hfin := klDiv_bernoulli_ne_top p q (by rw [hp]; norm_num) (by rw [hp]; norm_num) hq0 hq1
  have he := toReal_klDiv_bernoulli p q (by rw [hp]; norm_num) (by rw [hp]; norm_num) hq0 hq1
  rw [hp,hq] at he
  have hA : 0 < 1-a := sub_pos.mpr hb
  have hB : 0 < 1+a := add_pos zero_lt_one ha
  have hcost : (klDiv (bernoulliMeasure true false p) (bernoulliMeasure true false q)).toReal = aliasCost := by
    rw [he,show (1:ℝ)-1/2 = 1/2 by norm_num,show (1/2:ℝ)/((1-a)/2) = (1-a)⁻¹ by field_simp,
      show 1-(1-a)/2=(1+a)/2 by ring,show (1/2:ℝ)/((1+a)/2) = (1+a)⁻¹ by field_simp,
      Real.log_inv,Real.log_inv]
    change _ = -Real.log (1-a^2)/2
    rw [show 1-a^2 = (1-a)*(1+a) by ring,Real.log_mul hA.ne' hB.ne']
    ring
  rw [← hcost,ENNReal.ofReal_toReal hfin]
  exact cosine_information U (mixture n) (reciprocal n)

#print axioms cosine_output
#print axioms cosine_information
#print axioms aliasCost_pos
#print axioms mesh_entropy_gap
end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells.GaussianGrid
