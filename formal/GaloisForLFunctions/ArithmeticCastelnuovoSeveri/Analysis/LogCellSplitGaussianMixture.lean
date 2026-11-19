import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.Analysis.LogCellPositionGaussianKL
import GaloisForLFunctions.HTGeometry.ReflectedExponentialFisher

/-!
# Strict information gain from splitting a uniform position cell

Split an interval into two adjacent cells and approximate their positions
by two Gaussian densities. The length-weighted mixture has strictly smaller
forward KL than the weighted average of the two component divergences:
each Gaussian also has positive density throughout the other cell. Fitting
the component moments therefore improves strictly on the optimal single
Gaussian, for every choice of the split point.
-/

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells

def positionGaussianDensity (θ : ℝ × ℝ) := gaussianPDFReal θ.1 (Real.toNNReal (Real.exp θ.2))
private theorem var_ne (s : ℝ) : Real.toNNReal (Real.exp s) ≠ 0 :=
  (Real.toNNReal_pos.mpr (Real.exp_pos s)).ne'
theorem positionGaussianDensity_pos (θ : ℝ × ℝ) (x : ℝ) : 0 < positionGaussianDensity θ x :=
  gaussianPDFReal_pos _ _ _ (var_ne _)
theorem positionGaussianDensity_cont (θ : ℝ × ℝ) : Continuous (positionGaussianDensity θ) := by
  unfold positionGaussianDensity gaussianPDFReal
  fun_prop

/-- Probability of the first subinterval under uniform sampling of their union. -/
def lengthRatio (u v : ℝ) := Real.exp u/(Real.exp u+Real.exp v)
theorem lengthRatio_pos (u v : ℝ) : 0 < lengthRatio u v :=
  div_pos (Real.exp_pos _) (add_pos (Real.exp_pos _) (Real.exp_pos _))
theorem lengthRatio_sum (u v : ℝ) : lengthRatio u v+lengthRatio v u = 1 := by
  unfold lengthRatio
  rw [add_comm (Real.exp v) (Real.exp u),← add_div,div_self (add_pos (Real.exp_pos _) (Real.exp_pos _)).ne']

def splitGaussianDensity (u v : ℝ) (θ η : ℝ × ℝ) (x : ℝ) :=
  lengthRatio u v*positionGaussianDensity θ x+lengthRatio v u*positionGaussianDensity η x

/-- Gaussian mixture weighted by the two physical lengths. The pairs
of parameters give the mean and the logarithm of the variance. -/
def splitGaussian (u v : ℝ) (θ η : ℝ × ℝ) : Measure ℝ :=
  volume.withDensity fun x => ENNReal.ofReal (splitGaussianDensity u v θ η x)

/-- The density construction is exactly the convex sum of Gaussian measures. -/
theorem splitGaussian_components (u v : ℝ) (θ η : ℝ × ℝ) :
    splitGaussian u v θ η =
      ENNReal.ofReal (lengthRatio u v) • positionGaussian θ.1 θ.2 +
      ENNReal.ofReal (lengthRatio v u) • positionGaussian η.1 η.2 := by
  let p := ENNReal.ofReal (lengthRatio u v)
  let q := ENNReal.ofReal (lengthRatio v u)
  let g := gaussianPDF θ.1 (Real.toNNReal (Real.exp θ.2))
  let h := gaussianPDF η.1 (Real.toNNReal (Real.exp η.2))
  have he : (fun x => ENNReal.ofReal (splitGaussianDensity u v θ η x)) = p • g + q • h := by
    funext x
    simp only [splitGaussianDensity,ENNReal.ofReal_add (mul_pos (lengthRatio_pos _ _) (positionGaussianDensity_pos _ _)).le
      (mul_pos (lengthRatio_pos _ _) (positionGaussianDensity_pos _ _)).le,
      ENNReal.ofReal_mul (lengthRatio_pos _ _).le,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    rfl
  rw [splitGaussian,he,withDensity_add_left ((measurable_gaussianPDF _ _).const_smul p),
    withDensity_smul p (measurable_gaussianPDF _ _),withDensity_smul q (measurable_gaussianPDF _ _)]
  simp only [positionGaussian,gaussianReal_of_var_ne_zero _ (var_ne _),p,q]

instance splitGaussian_probability (u v : ℝ) (θ η : ℝ × ℝ) :
    IsProbabilityMeasure (splitGaussian u v θ η) where
  measure_univ := by
    rw [splitGaussian_components,Measure.add_apply,Measure.smul_apply,Measure.smul_apply]
    simp only [measure_univ,smul_eq_mul,mul_one,← ENNReal.ofReal_add (lengthRatio_pos _ _).le
      (lengthRatio_pos _ _).le,lengthRatio_sum,ENNReal.ofReal_one]

private theorem single_score (t w : ℝ) (θ : ℝ × ℝ) :
    (klDiv (positionLaw t w) (positionGaussian θ.1 θ.2)).toReal =
      (∫ x in t..t+Real.exp w, -w-Real.log (positionGaussianDensity θ x))/Real.exp w :=
  (position_kl_from_density t w (positionGaussianDensity_cont θ) (positionGaussianDensity_pos θ)
    (gaussianReal_absolutelyContinuous _ (var_ne _)) (gaussianReal_absolutelyContinuous' _ (var_ne _))
    (rnDeriv_gaussianReal _ _)).2

theorem splitGaussianDensity_cont (u v : ℝ) (θ η : ℝ × ℝ) : Continuous (splitGaussianDensity u v θ η) :=
  (continuous_const.mul (positionGaussianDensity_cont θ)).add (continuous_const.mul (positionGaussianDensity_cont η))
theorem splitGaussianDensity_pos (u v : ℝ) (θ η : ℝ × ℝ) (x : ℝ) : 0 < splitGaussianDensity u v θ η x :=
  add_pos (mul_pos (lengthRatio_pos _ _) (positionGaussianDensity_pos _ _))
    (mul_pos (lengthRatio_pos _ _) (positionGaussianDensity_pos _ _))

private theorem mix_score (t w u v : ℝ) (θ η : ℝ × ℝ) :
    klDiv (positionLaw t w) (splitGaussian u v θ η) ≠ ⊤ ∧
    (klDiv (positionLaw t w) (splitGaussian u v θ η)).toReal =
      (∫ x in t..t+Real.exp w, -w-Real.log (splitGaussianDensity u v θ η x))/Real.exp w := by
  let g := fun x => ENNReal.ofReal (splitGaussianDensity u v θ η x)
  have hg : Measurable g := ENNReal.measurable_ofReal.comp (splitGaussianDensity_cont u v θ η).measurable
  exact position_kl_from_density t w (splitGaussianDensity_cont _ _ _ _) (splitGaussianDensity_pos _ _ _ _)
    (withDensity_absolutelyContinuous _ _) (HTGeometry.ReflectedExponentialFamily.absolutelyContinuous_withDensity_of_pos
      hg (fun x => (ENNReal.ofReal_pos.mpr (splitGaussianDensity_pos _ _ _ _ x)).ne'))
    (Measure.rnDeriv_withDensity _ hg)

private theorem integral_strict {a b : ℝ} (hab : a < b) {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) (h : ∀ x, f x < g x) :
    (∫ x in a..b, f x) < ∫ x in a..b, g x := by
  have hp := intervalIntegral.intervalIntegral_pos_of_pos ((hg.sub hf).intervalIntegrable _ _)
    (fun x => sub_pos.mpr (h x)) hab
  change 0 < ∫ x in a..b, g x-f x at hp
  rwa [intervalIntegral.integral_sub (hg.intervalIntegrable _ _) (hf.intervalIntegrable _ _),sub_pos] at hp

/-- The overlap correction is strictly positive on both adjacent cells.
This strict version of the mixture KL bound holds at arbitrary component
parameters, before optimizing either Gaussian. -/
theorem split_position_kl_strict (t u v : ℝ) (θ η : ℝ × ℝ) :
    let a := Real.exp u
    let b := Real.exp v
    let D := klDiv (positionLaw t (Real.log (a+b))) (splitGaussian u v θ η)
    D ≠ ⊤ ∧ (a+b)*D.toReal <
      a*(klDiv (positionLaw t u) (positionGaussian θ.1 θ.2)).toReal +
      b*(klDiv (positionLaw (t+a) v) (positionGaussian η.1 η.2)).toReal := by
  intro a b D
  have ha : 0 < a := Real.exp_pos _
  have hb : 0 < b := Real.exp_pos _
  have hs := add_pos ha hb
  obtain ⟨hfin,hm⟩ := mix_score t (Real.log (a+b)) u v θ η
  rw [Real.exp_log hs] at hm
  let f := fun x => -Real.log (a+b)-Real.log (splitGaussianDensity u v θ η x)
  have hf : Continuous f := continuous_const.sub ((splitGaussianDensity_cont _ _ _ _).log fun x => (splitGaussianDensity_pos _ _ _ _ x).ne')
  have bound (x w : ℝ) (ζ : ℝ × ℝ)
      (h : Real.exp w/(a+b)*positionGaussianDensity ζ x < splitGaussianDensity u v θ η x) :
      f x < -w-Real.log (positionGaussianDensity ζ x) := by
    have hz := Real.log_lt_log (mul_pos (div_pos (Real.exp_pos w) hs) (positionGaussianDensity_pos ζ x)) h
    rw [Real.log_mul (div_pos (Real.exp_pos w) hs).ne' (positionGaussianDensity_pos ζ x).ne',
      Real.log_div (Real.exp_ne_zero _) hs.ne',Real.log_exp] at hz
    dsimp only [f]
    linarith only [hz]
  have h1 : (∫ x in t..t+a, f x) < ∫ x in t..t+a, -u-Real.log (positionGaussianDensity θ x) := by
    apply integral_strict (lt_add_of_pos_right _ ha) hf
      (continuous_const.sub ((positionGaussianDensity_cont _).log fun x => (positionGaussianDensity_pos _ x).ne'))
    exact fun x => bound x u θ (lt_add_of_pos_right _ (mul_pos (lengthRatio_pos _ _) (positionGaussianDensity_pos η x)))
  have h2 : (∫ x in t+a..t+a+b, f x) < ∫ x in t+a..t+a+b, -v-Real.log (positionGaussianDensity η x) := by
    apply integral_strict (lt_add_of_pos_right _ hb) hf
      (continuous_const.sub ((positionGaussianDensity_cont _).log fun x => (positionGaussianDensity_pos _ x).ne'))
    intro x
    apply bound x v η
    change b/(a+b)*_ < lengthRatio u v*positionGaussianDensity θ x+b/(b+a)*positionGaussianDensity η x
    rw [add_comm b a]
    exact lt_add_of_pos_left _ (mul_pos (lengthRatio_pos _ _) (positionGaussianDensity_pos _ _))
  refine ⟨hfin,?_⟩
  change (a+b)*(klDiv _ _).toReal < _
  rw [hm,single_score t u θ,single_score (t+a) v η]
  change (a+b)*((∫ x in t..t+(a+b), f x)/(a+b)) <
    a*((∫ x in t..t+a, -u-Real.log (positionGaussianDensity θ x))/a) +
    b*((∫ x in t+a..t+a+b, -v-Real.log (positionGaussianDensity η x))/b)
  rw [mul_div_cancel₀ _ hs.ne',mul_div_cancel₀ _ ha.ne',mul_div_cancel₀ _ hb.ne',
    ← add_assoc,← intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable (t) (t+a)) (hf.intervalIntegrable (t+a) (t+a+b))]
  exact add_lt_add h1 h2

/-- Two locally fitted Gaussian components beat every single Gaussian, even
the globally fitted one, for every nontrivial split of a position interval. -/
theorem split_fit_beats_every_gaussian (t u v m l : ℝ) :
    let a := Real.exp u
    let b := Real.exp v
    let P := positionLaw t (Real.log (a+b))
    let θ := (t+a/2,Real.log (a^2/12))
    let η := (t+a+b/2,Real.log (b^2/12))
    (klDiv P (splitGaussian u v θ η)).toReal < (klDiv P (positionGaussian m l)).toReal := by
  intro a b P θ η
  have h := (split_position_kl_strict t u v θ η).2
  have h1 := (position_projection_exact t u θ.1 θ.2).2.mpr ⟨rfl,rfl⟩
  have h2 := (position_projection_exact (t+a) v η.1 η.2).2.mpr ⟨rfl,rfl⟩
  have hb := (position_projection_exact t (Real.log (a+b)) m l).1
  have h' : (a+b)*(2*(klDiv P (splitGaussian u v θ η)).toReal) <
      (a+b)*(Real.log (2*Real.pi)-Real.log 12+1) := by
    change (a+b)*(klDiv P (splitGaussian u v θ η)).toReal <
      a*(klDiv (positionLaw t u) (positionGaussian θ.1 θ.2)).toReal +
      b*(klDiv (positionLaw (t+a) v) (positionGaussian η.1 η.2)).toReal at h
    linear_combination 2*h + a*h1 + b*h2
  have hsum : 0 < a+b := add_pos (Real.exp_pos _) (Real.exp_pos _)
  have hl := (lt_of_mul_lt_mul_left h' hsum.le)
  linarith only [hl,hb]

#print axioms splitGaussian_components
#print axioms split_position_kl_strict
#print axioms split_fit_beats_every_gaussian
end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
