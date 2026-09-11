import GaloisForLFunctions.RHTower.FZZCigarPlaneScreeningBeta
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv

/-!
# Original logarithmic marks in the plane screening integral

For the original kernel `K_delta(z)=|z|^(-2(a+delta))*|z-1|^(-2b)`,
the insertion is `X(z)=-2 log|z|`. At every base point in the ordinary
convergence chamber, all integrals of `X^n*K_0` converge absolutely.
Differentiating the original moment adds one mark, and the original unmarked
family is analytic near zero with all derivatives equal to these moments.

The proof weights plane volume by `K_0`. The exact identity
`K_delta=exp(delta*X)*K_0` holds almost everywhere. Openness of the proved
convergence chamber supplies an open exponential-moment interval for this
specific measure. Mathlib's moment-generating-function theorems then justify
the original derivatives, independently of the displayed Gamma formula.

The normalized first insertion is the four-term logarithmic Gamma derivative.
It vanishes on `2a+b=2`, represented by the chart's `y=0` line. The second
insertion is strictly positive everywhere in the chamber; consequently the
normalized first response has positive derivative on its cancellation line.

Here `delta` shifts an independent position exponent. It is not a claimed
finite-deficit CFT deformation. Physical collision exponents lie outside this
ordinary convergence chamber. Continued cutoff matching, higher screening
correlators, the phase frame and the complete Ward producer remain unproved.
-/

open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
noncomputable section
namespace GaloisForLFunctions.RHTower

private def planeWeight (a b : ℝ) (z : ℂ) : ℝ := ‖z‖^(-2*a)*‖z-1‖^(-2*b)

/-- The actual logarithmic insertion from differentiating the first position exponent. -/
def fzzScreeningPlaneLogMark (z : ℂ) : ℝ := -2*Real.log ‖z‖

private theorem planeWeight_nonneg (a b : ℝ) (z : ℂ) : 0 ≤ planeWeight a b z := by
  unfold planeWeight
  positivity

private theorem planeWeight_integrable {a b : ℝ} (ha0 : 0 < a) (ha : a < 1)
    (hb0 : 0 < b) (hb : b < 1) (hab : 1 < a+b) : Integrable (planeWeight a b) := by
  obtain ⟨x,y,hx,hy⟩ := (fzzScreeningBeta_chart_iff a b).mpr ⟨ha0,ha,hb0,hb,hab⟩
  unfold planeWeight
  simpa only [hx,hy] using fzzScreeningBetaKernel_integrable x y

private def planeMeasure (a b : ℝ) : Measure ℂ :=
  volume.withDensity (fun z => ENNReal.ofReal (planeWeight a b z))

private theorem planeMeasure_integrable_iff (a b : ℝ) (g : ℂ → ℝ) :
    Integrable g (planeMeasure a b) ↔ Integrable (fun z => planeWeight a b z*g z) := by
  rw [planeMeasure, integrable_withDensity_iff_integrable_smul' (by unfold planeWeight; fun_prop)
    (by filter_upwards with z; exact ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (planeWeight_nonneg a b _), smul_eq_mul]

private theorem planeMeasure_integral (a b : ℝ) (g : ℂ → ℝ) :
    (∫ z, g z ∂planeMeasure a b) = ∫ z : ℂ, planeWeight a b z*g z := by
  rw [planeMeasure, integral_withDensity_eq_integral_toReal_smul (by unfold planeWeight; fun_prop)
    (by filter_upwards with z; exact ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (planeWeight_nonneg a b _), smul_eq_mul]

private theorem planeWeight_shift (a b δ : ℝ) {z : ℂ} (hz : z ≠ 0) :
    planeWeight a b z*Real.exp (δ*fzzScreeningPlaneLogMark z) = planeWeight (a+δ) b z := by
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have he : Real.exp (δ*fzzScreeningPlaneLogMark z) = ‖z‖^(-2*δ) := by
    rw [Real.rpow_def_of_pos hn]
    unfold fzzScreeningPlaneLogMark
    congr 1
    ring
  unfold planeWeight
  rw [he, show -2*(a+δ) = -2*a + -2*δ by ring, Real.rpow_add hn]
  ring

private theorem mark_exp_integrable {a b δ : ℝ} (ha0 : 0 < a+δ) (ha : a+δ < 1)
    (hb0 : 0 < b) (hb : b < 1) (hab : 1 < (a+δ)+b) :
    Integrable (fun z => Real.exp (δ*fzzScreeningPlaneLogMark z)) (planeMeasure a b) := by
  rw [planeMeasure_integrable_iff]
  apply (planeWeight_integrable ha0 ha hb0 hb hab).congr
  filter_upwards [volume.ae_ne (0 : ℂ)] with z hz
  exact (planeWeight_shift a b δ hz).symm

private theorem shift_chamber {a b : ℝ} (ha0 : 0 < a) (ha : a < 1)
    (hab : 1 < a+b) : ∀ᶠ δ : ℝ in 𝓝 0, 0 < a+δ ∧ a+δ < 1 ∧ 1 < (a+δ)+b := by
  have h1 : IsOpen {δ : ℝ | 0 < a+δ} := isOpen_lt continuous_const (by fun_prop)
  have h2 : IsOpen {δ : ℝ | a+δ < 1} := isOpen_lt (by fun_prop) continuous_const
  have h3 : IsOpen {δ : ℝ | 1 < (a+δ)+b} := isOpen_lt continuous_const (by fun_prop)
  exact (h1.inter (h2.inter h3)).mem_nhds (by simpa using And.intro ha0 (And.intro ha hab))

private theorem mark_exp_interior {a b : ℝ} (ha0 : 0 < a) (ha : a < 1)
    (hb0 : 0 < b) (hb : b < 1) (hab : 1 < a+b) :
    (0 : ℝ) ∈ interior (integrableExpSet fzzScreeningPlaneLogMark (planeMeasure a b)) := by
  apply mem_interior_iff_mem_nhds.mpr
  filter_upwards [shift_chamber ha0 ha hab] with δ hδ
  exact mark_exp_integrable hδ.1 hδ.2.1 hb0 hb hδ.2.2

private def markedMoment (a b : ℝ) (n : ℕ) (δ : ℝ) : ℝ :=
  ∫ z : ℂ, fzzScreeningPlaneLogMark z^n*planeWeight (a+δ) b z

private theorem markedMoment_eq_expMoment (a b : ℝ) (n : ℕ) (δ : ℝ) :
    markedMoment a b n δ =
      ∫ z, fzzScreeningPlaneLogMark z^n*Real.exp (δ*fzzScreeningPlaneLogMark z) ∂planeMeasure a b := by
  rw [planeMeasure_integral]
  unfold markedMoment
  apply integral_congr_ae
  filter_upwards [volume.ae_ne (0 : ℂ)] with z hz
  rw [← planeWeight_shift a b δ hz]
  ring

private theorem markedMoment_integrable {a b : ℝ} (ha0 : 0 < a) (ha : a < 1)
    (hb0 : 0 < b) (hb : b < 1) (hab : 1 < a+b) (n : ℕ) :
    Integrable (fun z : ℂ => fzzScreeningPlaneLogMark z^n*planeWeight a b z) := by
  have hi := integrable_pow_mul_exp_of_mem_interior_integrableExpSet
    (mark_exp_interior ha0 ha hb0 hb hab) n
  simp only [zero_mul, Real.exp_zero, mul_one] at hi
  have hh := (planeMeasure_integrable_iff a b (fun z => fzzScreeningPlaneLogMark z^n)).mp hi
  simpa only [mul_comm] using hh

private theorem markedMoment_hasDerivAt {a b : ℝ} (ha0 : 0 < a) (ha : a < 1)
    (hb0 : 0 < b) (hb : b < 1) (hab : 1 < a+b) (n : ℕ) :
    HasDerivAt (markedMoment a b n) (markedMoment a b (n+1) 0) 0 := by
  have hd := hasDerivAt_integral_pow_mul_exp_real (mark_exp_interior ha0 ha hb0 hb hab) n
  simpa only [← markedMoment_eq_expMoment] using hd

private theorem markedMoment_zero_eq_mgf (a b : ℝ) :
    markedMoment a b 0 = mgf fzzScreeningPlaneLogMark (planeMeasure a b) := by
  funext δ
  rw [markedMoment_eq_expMoment]
  simp [mgf]

private theorem markedMoment_analyticAt {a b : ℝ} (ha0 : 0 < a) (ha : a < 1)
    (hb0 : 0 < b) (hb : b < 1) (hab : 1 < a+b) : AnalyticAt ℝ (markedMoment a b 0) 0 := by
  rw [markedMoment_zero_eq_mgf]
  exact analyticAt_mgf (mark_exp_interior ha0 ha hb0 hb hab)


private def planeGammaValue (a b : ℝ) : ℝ :=
  Real.pi*Real.Gamma (a+b-1)*Real.Gamma (1-a)*Real.Gamma (1-b) /
    (Real.Gamma a*Real.Gamma b*Real.Gamma (2-a-b))

private theorem planeWeight_integral {a b : ℝ} (ha0 : 0 < a) (ha : a < 1)
    (hb0 : 0 < b) (hb : b < 1) (hab : 1 < a+b) :
    (∫ z : ℂ, planeWeight a b z) = planeGammaValue a b := by
  obtain ⟨x,y,hx,hy⟩ := (fzzScreeningBeta_chart_iff a b).mpr ⟨ha0,ha,hb0,hb,hab⟩
  simpa only [fzzScreeningBetaIntegral,hx,hy,planeWeight,planeGammaValue]
    using fzzScreeningBetaIntegral_eq_gamma x y

private theorem planeWeight_integral_pos {a b : ℝ} (ha0 : 0 < a) (ha : a < 1)
    (hb0 : 0 < b) (hb : b < 1) (hab : 1 < a+b) : 0 < markedMoment a b 0 0 := by
  obtain ⟨x,y,hx,hy⟩ := (fzzScreeningBeta_chart_iff a b).mpr ⟨ha0,ha,hb0,hb,hab⟩
  simpa only [markedMoment, pow_zero, one_mul, add_zero, fzzScreeningBetaIntegral,hx,hy,planeWeight]
    using fzzScreeningBetaIntegral_pos x y

private def gammaLogValue (a b : ℝ) : ℝ :=
  Real.log Real.pi + Real.log (Real.Gamma (a+b-1)) + Real.log (Real.Gamma (1-a)) +
    Real.log (Real.Gamma (1-b)) - Real.log (Real.Gamma a) - Real.log (Real.Gamma b) -
      Real.log (Real.Gamma (2-a-b))

private theorem log_planeGammaValue {a b : ℝ} (ha0 : 0 < a) (ha : a < 1)
    (hb0 : 0 < b) (hb : b < 1) (hab : 1 < a+b) :
    Real.log (planeGammaValue a b) = gammaLogValue a b := by
  have hs := (Real.Gamma_pos_of_pos (by linarith : 0 < a+b-1)).ne'
  have h1a := (Real.Gamma_pos_of_pos (by linarith : 0 < 1-a)).ne'
  have h1b := (Real.Gamma_pos_of_pos (by linarith : 0 < 1-b)).ne'
  have hga := (Real.Gamma_pos_of_pos ha0).ne'
  have hgb := (Real.Gamma_pos_of_pos hb0).ne'
  have h2 := (Real.Gamma_pos_of_pos (by linarith : 0 < 2-a-b)).ne'
  unfold planeGammaValue gammaLogValue
  rw [Real.log_div, Real.log_mul, Real.log_mul, Real.log_mul,
    Real.log_mul, Real.log_mul] <;> try positivity
  · ring

/-- Real logarithmic Gamma derivative; response formulas below use only positive arguments. -/
def fzzScreeningPlaneGammaLogSlope (s : ℝ) : ℝ := deriv Real.Gamma s / Real.Gamma s

private theorem gamma_log_hasDerivAt {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun r : ℝ => Real.log (Real.Gamma r)) (fzzScreeningPlaneGammaLogSlope s) s := by
  have hd := Real.differentiableAt_Gamma (s := s) (fun n => by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith)
  exact hd.hasDerivAt.log (Real.Gamma_pos_of_pos hs).ne'

private theorem gamma_log_affine {s : ℝ} (hs : 0 < s) (m : ℝ) :
    HasDerivAt (fun δ : ℝ => Real.log (Real.Gamma (s+m*δ))) (m*fzzScreeningPlaneGammaLogSlope s) 0 := by
  have hh := (hasDerivAt_const (0 : ℝ) s).add ((hasDerivAt_id (0 : ℝ)).const_mul m)
  have hd := (gamma_log_hasDerivAt (s := s+m*0) (by simpa using hs)).comp 0 hh
  convert! hd using 1
  simp [mul_comm]

private theorem gammaLogValue_hasDerivAt {a b : ℝ} (ha0 : 0 < a) (ha : a < 1)
    (hb : b < 1) (hab : 1 < a+b) :
    HasDerivAt (fun δ : ℝ => gammaLogValue (a+δ) b)
      (fzzScreeningPlaneGammaLogSlope (a+b-1)-fzzScreeningPlaneGammaLogSlope (1-a)-fzzScreeningPlaneGammaLogSlope a+fzzScreeningPlaneGammaLogSlope (2-a-b)) 0 := by
  have h1 := gamma_log_affine (by linarith : 0 < a+b-1) 1
  have h2 := gamma_log_affine (by linarith : 0 < 1-a) (-1)
  have h3 := gamma_log_affine ha0 1
  have h4 := gamma_log_affine (by linarith : 0 < 2-a-b) (-1)
  have hd := (((((hasDerivAt_const (0 : ℝ) (Real.log Real.pi)).add h1).add h2).add_const
    (Real.log (Real.Gamma (1-b)))).sub h3 |>.sub_const (Real.log (Real.Gamma b))).sub h4
  convert! hd using 1
  · funext δ
    dsimp only [gammaLogValue, Pi.add_apply, Pi.sub_apply]
    simp only [one_mul, neg_one_mul,
      show a+δ+b-1 = a+b-1+δ by ring,
      show 1-(a+δ) = 1-a+ -δ by ring,
      show 2-(a+δ)-b = 2-a-b+ -δ by ring]
  · ring

private theorem markedMoment_logResponse {a b : ℝ} (ha0 : 0 < a) (ha : a < 1)
    (hb0 : 0 < b) (hb : b < 1) (hab : 1 < a+b) :
    markedMoment a b 1 0 / markedMoment a b 0 0 =
      fzzScreeningPlaneGammaLogSlope (a+b-1)-fzzScreeningPlaneGammaLogSlope (1-a)-fzzScreeningPlaneGammaLogSlope a+fzzScreeningPlaneGammaLogSlope (2-a-b) := by
  have hm := (markedMoment_hasDerivAt ha0 ha hb0 hb hab 0).log
    (planeWeight_integral_pos ha0 ha hb0 hb hab).ne'
  have he : (fun δ : ℝ => Real.log (markedMoment a b 0 δ)) =ᶠ[𝓝 0]
      (fun δ => gammaLogValue (a+δ) b) := by
    filter_upwards [shift_chamber ha0 ha hab] with δ hδ
    simp only [markedMoment, pow_zero, one_mul]
    rw [planeWeight_integral hδ.1 hδ.2.1 hb0 hb hδ.2.2,
      log_planeGammaValue hδ.1 hδ.2.1 hb0 hb hδ.2.2]
  exact hm.unique ((gammaLogValue_hasDerivAt ha0 ha hb hab).congr_of_eventuallyEq he)


private theorem markedMoment_iteratedDeriv {a b : ℝ} (ha0 : 0 < a) (ha : a < 1)
    (hb0 : 0 < b) (hb : b < 1) (hab : 1 < a+b) (n : ℕ) :
    iteratedDeriv n (markedMoment a b 0) 0 = markedMoment a b n 0 := by
  rw [markedMoment_zero_eq_mgf, iteratedDeriv_mgf_zero (mark_exp_interior ha0 ha hb0 hb hab),
    markedMoment_eq_expMoment]
  simp

/-- The original plane integral with `n` logarithmic marks and a first-exponent shift. -/
def fzzScreeningPlaneMarkedMoment (x y : ℝ) (n : ℕ) (δ : ℝ) : ℝ :=
  ∫ z : ℂ, fzzScreeningPlaneLogMark z^n *
    (‖z‖^(-2*(fzzScreeningBetaA x y+δ))*‖z-1‖^(-2*fzzScreeningBetaB x y))

/-- The unmarked base is exactly the previously evaluated whole-plane source. -/
theorem fzzScreeningPlaneMarkedMoment_zero (x y : ℝ) :
    fzzScreeningPlaneMarkedMoment x y 0 0 = fzzScreeningBetaIntegral x y := by
  simp [fzzScreeningPlaneMarkedMoment, fzzScreeningBetaIntegral]

/-- Every actual logarithmic insertion is absolutely integrable at the base point. -/
theorem fzzScreeningPlaneMarkedMoment_integrable (x y : ℝ) (n : ℕ) :
    Integrable (fun z : ℂ => fzzScreeningPlaneLogMark z^n *
      (‖z‖^(-2*fzzScreeningBetaA x y)*‖z-1‖^(-2*fzzScreeningBetaB x y))) := by
  obtain ⟨ha0,ha,hb0,hb,hab⟩ := fzzScreeningBeta_chamber x y
  exact markedMoment_integrable ha0 ha hb0 hb hab n

/-- Differentiation passes through the original position integral and adds one mark. -/
theorem fzzScreeningPlaneMarkedMoment_hasDerivAt (x y : ℝ) (n : ℕ) :
    HasDerivAt (fzzScreeningPlaneMarkedMoment x y n)
      (fzzScreeningPlaneMarkedMoment x y (n+1) 0) 0 := by
  obtain ⟨ha0,ha,hb0,hb,hab⟩ := fzzScreeningBeta_chamber x y
  exact markedMoment_hasDerivAt ha0 ha hb0 hb hab n

/-- The original shifted position integral is analytic near its convergent base point. -/
theorem fzzScreeningPlaneMarkedMoment_analyticAt (x y : ℝ) :
    AnalyticAt ℝ (fzzScreeningPlaneMarkedMoment x y 0) 0 := by
  obtain ⟨ha0,ha,hb0,hb,hab⟩ := fzzScreeningBeta_chamber x y
  exact markedMoment_analyticAt ha0 ha hb0 hb hab

/-- All derivatives of the original family are the corresponding original moments. -/
theorem fzzScreeningPlaneMarkedMoment_iteratedDeriv (x y : ℝ) (n : ℕ) :
    iteratedDeriv n (fzzScreeningPlaneMarkedMoment x y 0) 0 =
      fzzScreeningPlaneMarkedMoment x y n 0 := by
  obtain ⟨ha0,ha,hb0,hb,hab⟩ := fzzScreeningBeta_chamber x y
  exact markedMoment_iteratedDeriv ha0 ha hb0 hb hab n

/-- The normalized first original insertion retains all four logarithmic Gamma terms. -/
theorem fzzScreeningPlaneMarkedMoment_logResponse (x y : ℝ) :
    fzzScreeningPlaneMarkedMoment x y 1 0 / fzzScreeningBetaIntegral x y =
      fzzScreeningPlaneGammaLogSlope (fzzScreeningBetaA x y+fzzScreeningBetaB x y-1) -
        fzzScreeningPlaneGammaLogSlope (1-fzzScreeningBetaA x y) -
          fzzScreeningPlaneGammaLogSlope (fzzScreeningBetaA x y) +
            fzzScreeningPlaneGammaLogSlope (2-fzzScreeningBetaA x y-fzzScreeningBetaB x y) := by
  rw [← fzzScreeningPlaneMarkedMoment_zero]
  obtain ⟨ha0,ha,hb0,hb,hab⟩ := fzzScreeningBeta_chamber x y
  exact markedMoment_logResponse ha0 ha hb0 hb hab

/-- Along `2a+b=2` (the chart's `y=0` line), the original first insertion cancels. -/
theorem fzzScreeningPlaneMarkedMoment_first_zero (x : ℝ) :
    fzzScreeningPlaneMarkedMoment x 0 1 0 = 0 := by
  have hb : 2*fzzScreeningBetaA x 0+fzzScreeningBetaB x 0 = 2 := by
    unfold fzzScreeningBetaA fzzScreeningBetaB
    rw [Real.exp_zero]
    field_simp
    ring
  have hs : fzzScreeningBetaA x 0+fzzScreeningBetaB x 0-1 = 1-fzzScreeningBetaA x 0 := by
    linarith
  have hc : 2-fzzScreeningBetaA x 0-fzzScreeningBetaB x 0 = fzzScreeningBetaA x 0 := by
    linarith
  have h := fzzScreeningPlaneMarkedMoment_logResponse x 0
  rw [hs,hc] at h
  have hz : fzzScreeningPlaneMarkedMoment x 0 1 0 / fzzScreeningBetaIntegral x 0 = 0 := by
    simpa using h
  have hn := (fzzScreeningBetaIntegral_pos x 0).ne'
  exact (div_eq_zero_iff.mp hz).resolve_right hn


/-- A zero first mark does not eliminate the next insertion: its integral is strictly positive. -/
theorem fzzScreeningPlaneMarkedMoment_second_pos (x y : ℝ) :
    0 < fzzScreeningPlaneMarkedMoment x y 2 0 := by
  let a := fzzScreeningBetaA x y
  let b := fzzScreeningBetaB x y
  let f : ℂ → ℝ := fun z => fzzScreeningPlaneLogMark z^2*planeWeight a b z
  have hi : Integrable f := fzzScreeningPlaneMarkedMoment_integrable x y 2
  have hn : 0 ≤ f := by
    intro z
    exact mul_nonneg (sq_nonneg _) (planeWeight_nonneg a b z)
  have hc : ContinuousAt f (2 : ℂ) := by
    dsimp [f, fzzScreeningPlaneLogMark, planeWeight]
    fun_prop (disch := norm_num)
  have hp : 0 < f (2 : ℂ) := by
    have hl : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    dsimp [f, fzzScreeningPlaneLogMark, planeWeight]
    norm_num only [show (2 : ℂ)-1 = 1 by norm_num, norm_one, Real.one_rpow,
      Complex.norm_ofNat, mul_one]
    exact mul_pos (sq_pos_of_ne_zero (by nlinarith)) (Real.rpow_pos_of_pos (by norm_num) _)
  change 0 < ∫ z : ℂ, fzzScreeningPlaneLogMark z^2 *
    (‖z‖^(-2*(a+0))*‖z-1‖^(-2*b))
  simp only [add_zero]
  change 0 < ∫ z : ℂ, f z
  rw [integral_pos_iff_support_of_nonneg hn hi]
  apply volume.measure_pos_of_mem_nhds (x := (2 : ℂ))
  filter_upwards [hc.eventually (Ioi_mem_nhds hp)] with z hz
  exact ne_of_gt hz


/-- On the first-mark cancellation line, the normalized response has positive derivative. -/
theorem fzzScreeningPlaneMarkedMoment_first_zero_response_deriv_pos (x : ℝ) :
    0 < deriv (fun δ : ℝ => fzzScreeningPlaneMarkedMoment x 0 1 δ /
      fzzScreeningPlaneMarkedMoment x 0 0 δ) 0 := by
  have hm0 : 0 < fzzScreeningPlaneMarkedMoment x 0 0 0 := by
    rw [fzzScreeningPlaneMarkedMoment_zero]
    exact fzzScreeningBetaIntegral_pos x 0
  have hd := (fzzScreeningPlaneMarkedMoment_hasDerivAt x 0 1).div
    (fzzScreeningPlaneMarkedMoment_hasDerivAt x 0 0) hm0.ne'
  have he : HasDerivAt (fun δ : ℝ => fzzScreeningPlaneMarkedMoment x 0 1 δ /
      fzzScreeningPlaneMarkedMoment x 0 0 δ)
      (fzzScreeningPlaneMarkedMoment x 0 2 0 / fzzScreeningPlaneMarkedMoment x 0 0 0) 0 := by
    convert! hd using 1
    rw [fzzScreeningPlaneMarkedMoment_first_zero]
    field_simp
    ring
  rw [he.deriv]
  exact div_pos (fzzScreeningPlaneMarkedMoment_second_pos x 0) hm0

end GaloisForLFunctions.RHTower
