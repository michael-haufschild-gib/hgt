import GaloisForLFunctions.RHTower.ThetaRenewalCausalArithmetic

/-!
# Native arithmetic action on all renewal causal moments

The causal moment `W_j(w,x)` is the right source tail weighted by
`(t-x)^j exp(w*(t-x))`. Every prime, compensated Gamma, and pole action
commutes with this tail on its absolute domain. The forward action is
`x*W_j + W_(j+1)`. Reflection retains the complete polynomial source
moment. If the source moments through order `j` vanish, the literal
forward-plus-backward action is the next whole source moment multiplied
by `exp(-w*x)`.

The statements allow arbitrary finite order and keep both pole kernels.
They establish arithmetic action and admission, without a positivity
assertion for the mixed form.
-/

noncomputable section
open MeasureTheory Set Filter Topology HurwitzZeta
namespace RHTower.ThetaSourceWard

private theorem causalJet_pow_bound (j : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    y ^ j ≤ 4 ^ j * (j.factorial : ℝ) * Real.exp (y / 4) := by
  have hf : (0 : ℝ) < j.factorial := by exact_mod_cast Nat.factorial_pos j
  have h := (div_le_iff₀ hf).mp
    (Real.pow_div_factorial_le_exp (y / 4) (show 0 ≤ y / 4 by positivity) j)
  calc
    y ^ j = 4 ^ j * (y / 4) ^ j := by rw [← mul_pow]; congr 1; ring
    _ ≤ 4 ^ j * (Real.exp (y / 4) * (j.factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by ring

private theorem causalJet_weight_norm_le
    (j : ℕ) {r : ℝ} {w : ℂ} (hw : w.re ≤ r - 1 / 4)
    {x t : ℝ} (ht : x < t) (a : ℂ) :
    ‖((t - x : ℝ) : ℂ) ^ j * a * Complex.exp (w * t)‖ ≤
      (4 ^ j * (j.factorial : ℝ) * Real.exp ((w.re - r) * x)) *
        ‖a * Complex.exp ((r : ℂ) * t)‖ := by
  have he : Real.exp ((t - x) / 4) * Real.exp (w.re * t) ≤
      Real.exp ((w.re - r) * x) * Real.exp (r * t) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hb : (t - x) ^ j * Real.exp (w.re * t) ≤
      (4 ^ j * (j.factorial : ℝ) * Real.exp ((w.re - r) * x)) * Real.exp (r * t) := by
    calc
      _ ≤ (4 ^ j * (j.factorial : ℝ) * Real.exp ((t - x) / 4)) *
          Real.exp (w.re * t) :=
        mul_le_mul_of_nonneg_right (causalJet_pow_bound j (by linarith)) (Real.exp_pos _).le
      _ = (4 ^ j * (j.factorial : ℝ)) *
          (Real.exp ((t - x) / 4) * Real.exp (w.re * t)) := by ring
      _ ≤ (4 ^ j * (j.factorial : ℝ)) *
          (Real.exp ((w.re - r) * x) * Real.exp (r * t)) :=
        mul_le_mul_of_nonneg_left he (by positivity)
      _ = _ := by ring
  simpa only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (sub_pos.mpr ht), Complex.norm_exp, Complex.re_mul_ofReal,
    Complex.ofReal_re, mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_left hb (norm_nonneg a)

/-- Polynomial causal weights are admitted by a quarter-unit exponential margin. -/
theorem integrable_prod_causalJet_weight
    {ι : Type*} [MeasurableSpace ι] (μ : Measure ι) [SFinite μ]
    (f : ι × ℝ → ℂ) (j : ℕ) {r : ℝ} {w : ℂ} (hw : w.re ≤ r - 1 / 4) (x : ℝ)
    (hf : Integrable (fun p => f p * Complex.exp ((r : ℂ) * p.2)) (μ.prod volume))
    (hm : AEStronglyMeasurable
      (fun p => ((p.2 - x : ℝ) : ℂ) ^ j * f p * Complex.exp (w * p.2))
      (μ.prod (volume.restrict (Ioi x)))) :
    Integrable (fun p => ((p.2 - x : ℝ) : ℂ) ^ j * f p * Complex.exp (w * p.2))
      (μ.prod (volume.restrict (Ioi x))) := by
  have hi := hf.integrableOn (s := (univ : Set ι) ×ˢ Ioi x)
  rw [IntegrableOn, ← Measure.prod_restrict, Measure.restrict_univ] at hi
  apply (hi.norm.const_mul
    (4 ^ j * (j.factorial : ℝ) * Real.exp ((w.re - r) * x))).mono' hm
  have hmem : ∀ᵐ p : ι × ℝ ∂μ.prod (volume.restrict (Ioi x)), x < p.2 := by
    apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
    exact Eventually.of_forall fun _ => ae_restrict_mem measurableSet_Ioi
  filter_upwards [hmem] with p hp
  exact causalJet_weight_norm_le j hw hp (f p)

theorem integrableOn_causalJet_weight
    (f : ℝ → ℂ) (j : ℕ) {r : ℝ} {w : ℂ} (hw : w.re ≤ r - 1 / 4) (x : ℝ)
    (hf : Integrable (fun t => f t * Complex.exp ((r : ℂ) * t)))
    (hm : AEStronglyMeasurable
      (fun t => ((t - x : ℝ) : ℂ) ^ j * f t * Complex.exp (w * t))
      (volume.restrict (Ioi x))) :
    IntegrableOn (fun t => ((t - x : ℝ) : ℂ) ^ j * f t * Complex.exp (w * t)) (Ioi x) := by
  apply ((hf.integrableOn (s := Ioi x)).norm.const_mul
    (4 ^ j * (j.factorial : ℝ) * Real.exp ((w.re - r) * x))).mono' hm
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact causalJet_weight_norm_le j hw ht (f t)

/-- The unnormalised causal parameter moment. Division by `j!` gives the jet. -/
def thetaCausalMoment (j : ℕ) (w : ℂ) (x : ℝ) : ℂ :=
  Complex.exp (-(w * x)) * ∫ t in Ioi x,
    ((t - x : ℝ) : ℂ) ^ j * (thetaCuspFullSource t : ℂ) * Complex.exp (w * t)

theorem thetaCausalMoment_zero (w : ℂ) (x : ℝ) :
    thetaCausalMoment 0 w x = thetaCausalField w x := by
  simp [thetaCausalMoment, thetaCausalField_eq_tail]

theorem integrableOn_thetaCausalMoment_integrand (j : ℕ) (w : ℂ) (x u : ℝ) :
    IntegrableOn (fun t : ℝ =>
      ((t - x : ℝ) : ℂ) ^ j * (thetaCuspFullSource (t + u) : ℂ) * Complex.exp (w * t))
      (Ioi x) := by
  let r : ℝ := w.re + 1 / 4
  have hi := (integrable_laplaceIntegrand thetaCuspTiltSource (r : ℂ)).comp_add_right u
  have hf : Integrable (fun t : ℝ =>
      (thetaCuspFullSource (t + u) : ℂ) * Complex.exp ((r : ℂ) * t)) := by
    apply (hi.const_mul (Complex.exp (-((r : ℂ) * u)))).congr
    filter_upwards with t
    simp only [laplaceIntegrand, thetaCuspTiltSource_k]
    have he : Complex.exp (-((r : ℂ) * u)) *
        Complex.exp ((r : ℂ) * ((t + u : ℝ) : ℂ)) = Complex.exp ((r : ℂ) * t) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    linear_combination (thetaCuspFullSource (t + u) : ℂ) * he
  apply integrableOn_causalJet_weight
    (fun t : ℝ => (thetaCuspFullSource (t + u) : ℂ)) j
    (r := r) (by dsimp [r]; linarith) x hf
  have hc : Continuous (fun t : ℝ =>
      ((t - x : ℝ) : ℂ) ^ j * (thetaCuspFullSource (t + u) : ℂ) * Complex.exp (w * t)) := by
    have hk := thetaCuspTiltSource.cont
    change Continuous (fun t : ℝ =>
      ((t - x : ℝ) : ℂ) ^ j * (thetaCuspTiltSource.k (t + u) : ℂ) * Complex.exp (w * t))
    fun_prop
  exact hc.aestronglyMeasurable

private theorem causalMoment_integral_Ioi_translate (f : ℝ → ℂ) (x u : ℝ) :
    (∫ t in Ioi x, f (t + u)) = ∫ t in Ioi (x + u), f t := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
  have he : (Ioi x).indicator (fun t => f (t + u)) =
      fun t => (Ioi (x + u)).indicator f (t + u) := by
    funext t
    simp only [Set.indicator, Set.mem_Ioi, add_lt_add_iff_right]
  rw [he, integral_add_right_eq_self]

theorem thetaCausalMoment_shift (j : ℕ) (w : ℂ) (x u : ℝ) :
    thetaCausalMoment j w (x + u) = Complex.exp (-(w * x)) *
      ∫ t in Ioi x, ((t - x : ℝ) : ℂ) ^ j *
        (thetaCuspFullSource (t + u) : ℂ) * Complex.exp (w * t) := by
  rw [thetaCausalMoment, ← causalMoment_integral_Ioi_translate _ x u,
    ← integral_const_mul, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  have hsub : (t + u) - (x + u) = t - x := by ring
  dsimp only
  rw [hsub]
  have he : Complex.exp (-(w * ((x + u : ℝ) : ℂ))) *
      Complex.exp (w * ((t + u : ℝ) : ℂ)) =
      Complex.exp (-(w * x)) * Complex.exp (w * t) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  linear_combination ((t - x : ℝ) : ℂ) ^ j * (thetaCuspFullSource (t + u) : ℂ) * he

def causalMomentGammaTerm (j : ℕ) (w : ℂ) (x u : ℝ) : ℂ :=
  ((Real.exp (-2 * u) : ℂ) * thetaCausalMoment j w x -
    (Real.exp (-u / 2) : ℂ) * thetaCausalMoment j w (x + u)) /
      ((1 - Real.exp (-2 * u) : ℝ) : ℂ)

def causalMomentPolarTerm (j : ℕ) (a : ℝ) (w : ℂ) (x u : ℝ) : ℂ :=
  (Real.exp (a * u) : ℂ) * thetaCausalMoment j w (x + u)

def causalMomentPrimeTerm (j : ℕ) (w : ℂ) (x : ℝ) (n : ℕ) : ℂ :=
  primeCoefficient n * thetaCausalMoment j w (x + Real.log n)

theorem causalMomentGammaTerm_eq_tail (j : ℕ) (w : ℂ) (x u : ℝ) :
    causalMomentGammaTerm j w x u = Complex.exp (-(w * x)) *
      ∫ t in Ioi x, ((t - x : ℝ) : ℂ) ^ j * gammaLaplaceTerm w u t := by
  have h₀ := integrableOn_thetaCausalMoment_integrand j w x 0
  simp only [add_zero] at h₀
  have h₁ := integrableOn_thetaCausalMoment_integrand j w x u
  have hf : (fun t : ℝ => ((t - x : ℝ) : ℂ) ^ j * gammaLaplaceTerm w u t) = fun t =>
      ((Real.exp (-2 * u) : ℂ) *
          (((t - x : ℝ) : ℂ) ^ j * (thetaCuspFullSource t : ℂ) * Complex.exp (w * t)) -
        (Real.exp (-u / 2) : ℂ) *
          (((t - x : ℝ) : ℂ) ^ j * (thetaCuspFullSource (t + u) : ℂ) *
            Complex.exp (w * t))) / ((1 - Real.exp (-2 * u) : ℝ) : ℂ) := by
    funext t
    simp only [gammaLaplaceTerm, gammaSourceTerm, Complex.ofReal_div,
      Complex.ofReal_sub, Complex.ofReal_mul]
    ring
  rw [hf, integral_div, integral_sub (h₀.const_mul _) (h₁.const_mul _),
    integral_const_mul, integral_const_mul, causalMomentGammaTerm,
    thetaCausalMoment_shift, thetaCausalMoment]
  ring

theorem causalMomentPolarTerm_eq_tail (j : ℕ) (a : ℝ) (w : ℂ) (x u : ℝ) :
    causalMomentPolarTerm j a w x u = Complex.exp (-(w * x)) *
      ∫ t in Ioi x, ((t - x : ℝ) : ℂ) ^ j *
        polarSourceTerm a t u * Complex.exp (w * t) := by
  rw [causalMomentPolarTerm, thetaCausalMoment_shift]
  simp only [polarSourceTerm]
  have he : (fun t : ℝ => ((t - x : ℝ) : ℂ) ^ j *
      ((Real.exp (a * u) : ℂ) * (thetaCuspFullSource (t + u) : ℂ)) * Complex.exp (w * t)) =
      fun t => (Real.exp (a * u) : ℂ) *
        (((t - x : ℝ) : ℂ) ^ j * (thetaCuspFullSource (t + u) : ℂ) * Complex.exp (w * t)) := by
    funext t
    ring
  rw [he, integral_const_mul]
  ring

theorem causalMomentPrimeTerm_eq_tail (j : ℕ) (w : ℂ) (x : ℝ) (n : ℕ) :
    causalMomentPrimeTerm j w x n = Complex.exp (-(w * x)) *
      ∫ t in Ioi x, ((t - x : ℝ) : ℂ) ^ j *
        primeSourceTerm thetaCuspTiltSource n t * Complex.exp (w * t) := by
  rw [causalMomentPrimeTerm, thetaCausalMoment_shift]
  simp only [primeSourceTerm, thetaCuspTiltSource_k]
  have he : (fun t : ℝ => ((t - x : ℝ) : ℂ) ^ j *
      (primeCoefficient n * (thetaCuspFullSource (t + Real.log n) : ℂ)) * Complex.exp (w * t)) =
      fun t => primeCoefficient n *
        (((t - x : ℝ) : ℂ) ^ j * (thetaCuspFullSource (t + Real.log n) : ℂ) *
          Complex.exp (w * t)) := by
    funext t
    ring
  rw [he, integral_const_mul]
  ring

theorem integrable_gammaLaplace_causalMoment (j : ℕ) {w : ℂ}
    (hw : w.re ≤ 1 / 2) (x : ℝ) :
    Integrable (fun p : ℝ × ℝ =>
      ((p.2 - x : ℝ) : ℂ) ^ j * gammaLaplaceTerm w p.1 p.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi x))) := by
  have hm : Measurable (fun p : ℝ × ℝ =>
      ((p.2 - x : ℝ) : ℂ) ^ j * gammaLaplaceTerm w p.1 p.2) :=
    (by fun_prop : Continuous (fun p : ℝ × ℝ => ((p.2 - x : ℝ) : ℂ) ^ j)).measurable.mul
      (gammaLaplaceTerm_measurable w)
  simpa only [gammaLaplaceTerm, mul_assoc] using
    integrable_prod_causalJet_weight (volume.restrict (Ioi (0 : ℝ)))
      (fun p : ℝ × ℝ => (gammaSourceTerm p.2 p.1 : ℂ)) j
      (r := 3 / 4) (w := w) (by linarith) x
      (gammaLaplaceTerm_integrable_prod (w := (3 / 4 : ℝ)) (by norm_num) (by norm_num))
      (by simpa only [gammaLaplaceTerm, mul_assoc] using hm.aestronglyMeasurable)

theorem integrable_polarLaplace_causalMoment (j : ℕ) {a : ℝ} (ha : a < 3 / 4)
    {w : ℂ} (hw : w.re ≤ 1 / 2) (x : ℝ) :
    Integrable (fun p : ℝ × ℝ => ((p.2 - x : ℝ) : ℂ) ^ j *
      polarSourceTerm a p.2 p.1 * Complex.exp (w * p.2))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi x))) := by
  apply integrable_prod_causalJet_weight (volume.restrict (Ioi (0 : ℝ)))
    (fun p : ℝ × ℝ => polarSourceTerm a p.2 p.1) j
    (r := 3 / 4) (by linarith) x
    (polarSourceTerm_laplace_integrable_prod a (w := (3 / 4 : ℝ)) (by simpa using ha))
  exact (((by fun_prop : Continuous (fun p : ℝ × ℝ => ((p.2 - x : ℝ) : ℂ) ^ j)).mul
    ((polarSourceTerm_continuous a).comp continuous_swap)).mul
    (by fun_prop)).aestronglyMeasurable

theorem integrable_primeLaplace_causalMoment (j : ℕ) (w : ℂ) (x : ℝ) :
    Integrable (fun p : ℕ × ℝ => ((p.2 - x : ℝ) : ℂ) ^ j *
      primeSourceTerm thetaCuspTiltSource p.1 p.2 * Complex.exp (w * p.2))
      (Measure.count.prod (volume.restrict (Ioi x))) := by
  let r : ℝ := max w.re 1 + 1
  have hr : 1 / 2 < (r : ℂ).re := by
    simp only [Complex.ofReal_re]
    dsimp [r]
    linarith [le_max_right w.re 1]
  have hc (z : ℂ) : Continuous (fun p : ℕ × ℝ =>
      primeSourceTerm thetaCuspTiltSource p.1 p.2 * Complex.exp (z * p.2)) := by
    have hcoef : Continuous primeCoefficient := continuous_of_discreteTopology
    have hlog : Continuous (fun n : ℕ => Real.log n) := continuous_of_discreteTopology
    have hk := thetaCuspTiltSource.cont
    unfold primeSourceTerm
    exact ((hcoef.comp continuous_fst).mul
      ((Complex.continuous_ofReal.comp hk).comp
        (continuous_snd.add (hlog.comp continuous_fst)))).mul (by fun_prop)
  have hp : Integrable (fun p : ℕ × ℝ =>
      primeSourceTerm thetaCuspTiltSource p.1 p.2 * Complex.exp ((r : ℂ) * p.2))
      (Measure.count.prod volume) := by
    rw [integrable_prod_iff (hc r).aestronglyMeasurable]
    constructor
    · exact Eventually.of_forall (integrable_primeSourceTerm_laplace thetaCuspTiltSource r)
    · rw [integrable_count_iff]
      simpa only [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))] using
        summable_integral_norm_primeSourceTerm_laplace thetaCuspTiltSource hr
  apply integrable_prod_causalJet_weight Measure.count
    (fun p : ℕ × ℝ => primeSourceTerm thetaCuspTiltSource p.1 p.2) j
    (by dsimp [r]; linarith [le_max_left w.re 1]) x hp
  have hcont : Continuous (fun p : ℕ × ℝ => ((p.2 - x : ℝ) : ℂ) ^ j *
      primeSourceTerm thetaCuspTiltSource p.1 p.2 * Complex.exp (w * p.2)) := by
    convert ((by fun_prop : Continuous (fun p : ℕ × ℝ =>
      ((p.2 - x : ℝ) : ℂ) ^ j)).mul (hc w)) using 1
    funext p
    dsimp only [Pi.mul_apply]
    ring
  exact hcont.aestronglyMeasurable

theorem integrableOn_causalMomentGammaTerm (j : ℕ) {w : ℂ}
    (hw : w.re ≤ 1 / 2) (x : ℝ) :
    IntegrableOn (causalMomentGammaTerm j w x) (Ioi 0) := by
  apply ((integrable_gammaLaplace_causalMoment j hw x).integral_prod_left.const_mul
    (Complex.exp (-(w * x)))).congr
  exact Eventually.of_forall fun u => (causalMomentGammaTerm_eq_tail j w x u).symm

theorem integrableOn_causalMomentPolarTerm (j : ℕ) {a : ℝ} (ha : a < 3 / 4)
    {w : ℂ} (hw : w.re ≤ 1 / 2) (x : ℝ) :
    IntegrableOn (causalMomentPolarTerm j a w x) (Ioi 0) := by
  apply ((integrable_polarLaplace_causalMoment j ha hw x).integral_prod_left.const_mul
    (Complex.exp (-(w * x)))).congr
  exact Eventually.of_forall fun u => (causalMomentPolarTerm_eq_tail j a w x u).symm

theorem summable_norm_causalMomentPrimeTerm (j : ℕ) (w : ℂ) (x : ℝ) :
    Summable (fun n => ‖causalMomentPrimeTerm j w x n‖) := by
  have h := (integrable_primeLaplace_causalMoment j w x).integral_prod_left.const_mul
    (Complex.exp (-(w * x)))
  rw [integrable_count_iff] at h
  simpa only [causalMomentPrimeTerm_eq_tail] using h

theorem integral_causalMomentGammaTerm (j : ℕ) {w : ℂ}
    (hw : w.re ≤ 1 / 2) (x : ℝ) :
    (∫ u in Ioi (0 : ℝ), causalMomentGammaTerm j w x u) =
      Complex.exp (-(w * x)) * ∫ t in Ioi x,
        ((t - x : ℝ) : ℂ) ^ j * gammaSource t * Complex.exp (w * t) := by
  simp_rw [causalMomentGammaTerm_eq_tail]
  rw [integral_const_mul, integral_integral_swap (integrable_gammaLaplace_causalMoment j hw x)]
  simp only [gammaLaplaceTerm, integral_const_mul, integral_mul_const, gammaSource, mul_assoc]

theorem integral_causalMomentPolarTerm (j : ℕ) {a : ℝ} (ha : a < 3 / 4)
    {w : ℂ} (hw : w.re ≤ 1 / 2) (x : ℝ) :
    (∫ u in Ioi (0 : ℝ), causalMomentPolarTerm j a w x u) =
      Complex.exp (-(w * x)) * ∫ t in Ioi x,
        ((t - x : ℝ) : ℂ) ^ j * polarSource a t * Complex.exp (w * t) := by
  simp_rw [causalMomentPolarTerm_eq_tail]
  rw [integral_const_mul, integral_integral_swap (integrable_polarLaplace_causalMoment j ha hw x)]
  simp only [integral_mul_const, integral_const_mul, polarSource]

theorem tsum_causalMomentPrimeTerm (j : ℕ) (w : ℂ) (x : ℝ) :
    (∑' n, causalMomentPrimeTerm j w x n) =
      Complex.exp (-(w * x)) * ∫ t in Ioi x,
        ((t - x : ℝ) : ℂ) ^ j * fullPrimeSource thetaCuspTiltSource t * Complex.exp (w * t) := by
  have hn : Summable (fun n : ℕ => ∫ t in Ioi x,
      ‖((t - x : ℝ) : ℂ) ^ j * primeSourceTerm thetaCuspTiltSource n t * Complex.exp (w * t)‖) := by
    have h := (integrable_primeLaplace_causalMoment j w x).integral_norm_prod_left
    rw [integrable_count_iff] at h
    simpa only [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))] using h
  have hi (n : ℕ) : IntegrableOn (fun t : ℝ =>
      ((t - x : ℝ) : ℂ) ^ j * primeSourceTerm thetaCuspTiltSource n t * Complex.exp (w * t))
      (Ioi x) := by
    simpa only [IntegrableOn, primeSourceTerm, thetaCuspTiltSource_k, mul_assoc, mul_left_comm, mul_comm] using
      (integrableOn_thetaCausalMoment_integrand j w x (Real.log n)).const_mul (primeCoefficient n)
  simp_rw [causalMomentPrimeTerm_eq_tail]
  rw [tsum_mul_left, integral_tsum_of_summable_integral_norm hi hn]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  simp only [fullPrimeSource, tsum_mul_left, tsum_mul_right]

/-- The original forward Gamma, two pole, and full prime actions on every causal moment. -/
def causalMomentArithmeticAction (j : ℕ) (w : ℂ) (x : ℝ) : ℂ :=
  -archConstant * thetaCausalMoment j w x +
    (∫ u in Ioi (0 : ℝ), causalMomentGammaTerm j w x u) +
    (∫ u in Ioi (0 : ℝ), causalMomentPolarTerm j (1 / 2) w x u) +
    (∫ u in Ioi (0 : ℝ), causalMomentPolarTerm j (-1 / 2) w x u) -
    ∑' n, causalMomentPrimeTerm j w x n

/-- Forward arithmetic action raises the causal moment order and retains the coordinate term. -/
theorem causalMomentArithmeticAction_eq_succ (j : ℕ) {w : ℂ}
    (hw : w.re ≤ 1 / 2) (x : ℝ) :
    causalMomentArithmeticAction j w x =
      (x : ℂ) * thetaCausalMoment j w x + thetaCausalMoment (j + 1) w x := by
  have hg : IntegrableOn (fun t : ℝ =>
      ((t - x : ℝ) : ℂ) ^ j * gammaSource t * Complex.exp (w * t)) (Ioi x) := by
    apply (integrable_gammaLaplace_causalMoment j hw x).integral_prod_right.congr
    filter_upwards with t
    simp only [gammaLaplaceTerm, integral_const_mul, integral_mul_const, gammaSource, mul_assoc]
  have hp : IntegrableOn (fun t : ℝ =>
      ((t - x : ℝ) : ℂ) ^ j * polarSource (1 / 2) t * Complex.exp (w * t)) (Ioi x) := by
    apply (integrable_polarLaplace_causalMoment j (a := 1 / 2) (by norm_num) hw x).integral_prod_right.congr
    filter_upwards with t
    simp only [integral_const_mul, integral_mul_const, polarSource]
  have hm : IntegrableOn (fun t : ℝ =>
      ((t - x : ℝ) : ℂ) ^ j * polarSource (-1 / 2) t * Complex.exp (w * t)) (Ioi x) := by
    apply (integrable_polarLaplace_causalMoment j (a := -1 / 2) (by norm_num) hw x).integral_prod_right.congr
    filter_upwards with t
    simp only [integral_const_mul, integral_mul_const, polarSource]
  have hk := integrableOn_thetaCausalMoment_integrand j w x 0
  have hs := integrableOn_thetaCausalMoment_integrand (j + 1) w x 0
  simp only [add_zero] at hk hs
  have ht : IntegrableOn (fun t : ℝ =>
      ((t - x : ℝ) : ℂ) ^ j * (t : ℂ) *
        (thetaCuspFullSource t : ℂ) * Complex.exp (w * t)) (Ioi x) := by
    apply ((hk.const_mul (x : ℂ)).fun_add hs).congr
    filter_upwards with t
    push_cast
    rw [pow_succ]
    ring
  have hkg := (hk.const_mul (-archConstant)).fun_add hg
  have hkgp := hkg.fun_add hp
  have hkgpm := hkgp.fun_add hm
  have he : (∫ t in Ioi x, ((t - x : ℝ) : ℂ) ^ j *
      fullPrimeSource thetaCuspTiltSource t * Complex.exp (w * t)) =
      -archConstant * (∫ t in Ioi x, ((t - x : ℝ) : ℂ) ^ j *
        (thetaCuspFullSource t : ℂ) * Complex.exp (w * t)) +
      (∫ t in Ioi x, ((t - x : ℝ) : ℂ) ^ j * gammaSource t * Complex.exp (w * t)) +
      (∫ t in Ioi x, ((t - x : ℝ) : ℂ) ^ j * polarSource (1 / 2) t * Complex.exp (w * t)) +
      (∫ t in Ioi x, ((t - x : ℝ) : ℂ) ^ j * polarSource (-1 / 2) t * Complex.exp (w * t)) -
      (∫ t in Ioi x, ((t - x : ℝ) : ℂ) ^ j * (t : ℂ) *
        (thetaCuspFullSource t : ℂ) * Complex.exp (w * t)) := by
    rw [← integral_const_mul, ← integral_add (hk.const_mul (-archConstant)) hg,
      ← integral_add hkg hp, ← integral_add hkgp hm, ← integral_sub hkgpm ht]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    linear_combination -(((t - x : ℝ) : ℂ) ^ j * Complex.exp (w * t)) *
      complete_theta_source_equation t
  have hj : (∫ t in Ioi x, ((t - x : ℝ) : ℂ) ^ j * (t : ℂ) *
      (thetaCuspFullSource t : ℂ) * Complex.exp (w * t)) =
      (x : ℂ) * (∫ t in Ioi x, ((t - x : ℝ) : ℂ) ^ j *
        (thetaCuspFullSource t : ℂ) * Complex.exp (w * t)) +
      ∫ t in Ioi x, ((t - x : ℝ) : ℂ) ^ (j + 1) *
        (thetaCuspFullSource t : ℂ) * Complex.exp (w * t) := by
    rw [← integral_const_mul, ← integral_add (hk.const_mul (x : ℂ)) hs]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    push_cast
    rw [pow_succ]
    ring
  rw [causalMomentArithmeticAction, integral_causalMomentGammaTerm j hw,
    integral_causalMomentPolarTerm j (by norm_num : (1 / 2 : ℝ) < 3 / 4) hw,
    integral_causalMomentPolarTerm j (by norm_num : (-1 / 2 : ℝ) < 3 / 4) hw,
    tsum_causalMomentPrimeTerm, he, hj, thetaCausalMoment, thetaCausalMoment]
  ring

/-- Every shifted polynomial source moment is absolutely integrable. -/
theorem integrable_thetaCausalMoment_whole (j : ℕ) (w : ℂ) (x : ℝ) :
    Integrable (fun t : ℝ =>
      ((t - x : ℝ) : ℂ) ^ j * (thetaCuspFullSource t : ℂ) * Complex.exp (w * t)) := by
  have h := integrable_finsetSum (Finset.range (j + 1)) (fun i _ =>
    (thetaCuspTiltSource.integrable_mul_exp w i).const_mul
      ((-(x : ℂ)) ^ (j - i) * (j.choose i : ℂ)))
  apply h.congr
  filter_upwards with t
  simp only [thetaCuspTiltSource_k, Complex.ofReal_sub]
  simp only [sub_eq_add_neg, add_pow, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Reflection retains the whole polynomial source moment, without a zero assumption. -/
theorem thetaCausalMoment_reflection_defect (j : ℕ) (w : ℂ) (x : ℝ) :
    thetaCausalMoment j w x + (-1 : ℂ) ^ j * thetaCausalMoment j (-w) (-x) =
      Complex.exp (-(w * x)) * ∫ t : ℝ,
        ((t - x : ℝ) : ℂ) ^ j * (thetaCuspFullSource t : ℂ) * Complex.exp (w * t) := by
  have hi : (-1 : ℂ) ^ j * (∫ t in Ioi (-x),
      ((t - (-x) : ℝ) : ℂ) ^ j * (thetaCuspFullSource t : ℂ) * Complex.exp ((-w) * t)) =
      ∫ t in Iic x, ((t - x : ℝ) : ℂ) ^ j *
        (thetaCuspFullSource t : ℂ) * Complex.exp (w * t) := by
    calc
      _ = ∫ t in Ioi (-x), ((-t - x : ℝ) : ℂ) ^ j *
          (thetaCuspFullSource (-t) : ℂ) * Complex.exp (w * ((-t : ℝ) : ℂ)) := by
        rw [← integral_const_mul]
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t _
        dsimp only
        have hpow : ((-t - x : ℝ) : ℂ) = (-1 : ℂ) * ((t - (-x) : ℝ) : ℂ) := by
          push_cast
          ring
        rw [hpow, mul_pow]
        simp only [thetaCuspFullSource_neg, Complex.ofReal_neg, mul_neg, neg_mul]
        ring
      _ = _ := by
        simpa only [neg_neg] using integral_comp_neg_Ioi (-x)
          (fun t : ℝ => ((t - x : ℝ) : ℂ) ^ j *
            (thetaCuspFullSource t : ℂ) * Complex.exp (w * t))
  have hs := integral_add_compl (s := Iic x) measurableSet_Iic
    (integrable_thetaCausalMoment_whole j w x)
  simp only [compl_Iic] at hs
  rw [← hi] at hs
  simp only [thetaCausalMoment, Complex.ofReal_neg, neg_mul_neg]
  linear_combination Complex.exp (-(w * x)) * hs

/-- Vanishing lower source moments give the graded reflection of a causal moment. -/
theorem thetaCausalMoment_reflection {j : ℕ} {w : ℂ}
    (hvan : ∀ x : ℝ, (∫ t : ℝ,
      ((t - x : ℝ) : ℂ) ^ j * (thetaCuspFullSource t : ℂ) * Complex.exp (w * t)) = 0)
    (x : ℝ) :
    thetaCausalMoment j w x = (-1 : ℂ) ^ (j + 1) * thetaCausalMoment j (-w) (-x) := by
  have h := thetaCausalMoment_reflection_defect j w x
  rw [hvan x, mul_zero] at h
  rw [pow_succ]
  linear_combination h

/-- The regularised reflected action keeps the full shifted source moment. -/
theorem causalMomentArithmeticAction_add_reflected (j : ℕ) {w : ℂ}
    (hlo : -1 / 2 ≤ w.re) (hhi : w.re ≤ 1 / 2) (x : ℝ) :
    causalMomentArithmeticAction j w x +
      (-1 : ℂ) ^ (j + 1) * causalMomentArithmeticAction j (-w) (-x) =
      (x : ℂ) * Complex.exp (-(w * x)) *
        (∫ t : ℝ, ((t - x : ℝ) : ℂ) ^ j *
          (thetaCuspFullSource t : ℂ) * Complex.exp (w * t)) +
      Complex.exp (-(w * x)) *
        ∫ t : ℝ, ((t - x : ℝ) : ℂ) ^ (j + 1) *
          (thetaCuspFullSource t : ℂ) * Complex.exp (w * t) := by
  have hn : (-w).re ≤ 1 / 2 := by simp only [Complex.neg_re]; linarith
  rw [causalMomentArithmeticAction_eq_succ j hhi,
    causalMomentArithmeticAction_eq_succ j hn]
  have h₀ := thetaCausalMoment_reflection_defect j w x
  have h₁ := thetaCausalMoment_reflection_defect (j + 1) w x
  simp only [Complex.ofReal_neg, pow_succ] at *
  linear_combination (x : ℂ) * h₀ + h₁

def reflectedCausalMomentGammaTerm (j : ℕ) (w : ℂ) (x u : ℝ) : ℂ :=
  ((Real.exp (-2 * u) : ℂ) * thetaCausalMoment j w x -
    (Real.exp (-u / 2) : ℂ) * thetaCausalMoment j w (x - u)) /
      ((1 - Real.exp (-2 * u) : ℝ) : ℂ)

def reflectedCausalMomentPolarTerm (j : ℕ) (a : ℝ) (w : ℂ) (x u : ℝ) : ℂ :=
  (Real.exp (a * u) : ℂ) * thetaCausalMoment j w (x - u)

def reflectedCausalMomentPrimeTerm (j : ℕ) (w : ℂ) (x : ℝ) (n : ℕ) : ℂ :=
  primeCoefficient n * thetaCausalMoment j w (x - Real.log n)

section VanishingMoments

variable {j : ℕ} {w : ℂ}
variable (hvan : ∀ x : ℝ, (∫ t : ℝ,
  ((t - x : ℝ) : ℂ) ^ j * (thetaCuspFullSource t : ℂ) * Complex.exp (w * t)) = 0)

include hvan

theorem reflectedCausalMomentGammaTerm_eq (x u : ℝ) :
    reflectedCausalMomentGammaTerm j w x u =
      (-1 : ℂ) ^ (j + 1) * causalMomentGammaTerm j (-w) (-x) u := by
  rw [reflectedCausalMomentGammaTerm, causalMomentGammaTerm,
    thetaCausalMoment_reflection hvan x, thetaCausalMoment_reflection hvan (x - u)]
  have he : -(x - u) = -x + u := by ring
  rw [he]
  ring

theorem reflectedCausalMomentPolarTerm_eq (a x u : ℝ) :
    reflectedCausalMomentPolarTerm j a w x u =
      (-1 : ℂ) ^ (j + 1) * causalMomentPolarTerm j a (-w) (-x) u := by
  rw [reflectedCausalMomentPolarTerm, causalMomentPolarTerm,
    thetaCausalMoment_reflection hvan (x - u)]
  have he : -(x - u) = -x + u := by ring
  rw [he]
  ring

theorem reflectedCausalMomentPrimeTerm_eq (x : ℝ) (n : ℕ) :
    reflectedCausalMomentPrimeTerm j w x n =
      (-1 : ℂ) ^ (j + 1) * causalMomentPrimeTerm j (-w) (-x) n := by
  rw [reflectedCausalMomentPrimeTerm, causalMomentPrimeTerm,
    thetaCausalMoment_reflection hvan (x - Real.log n)]
  have he : -(x - Real.log n) = -x + Real.log n := by ring
  rw [he]
  ring

theorem integrableOn_reflectedCausalMomentGammaTerm
    (hlo : -1 / 2 ≤ w.re) (x : ℝ) :
    IntegrableOn (reflectedCausalMomentGammaTerm j w x) (Ioi 0) := by
  have hn : (-w).re ≤ 1 / 2 := by simp only [Complex.neg_re]; linarith
  apply ((integrableOn_causalMomentGammaTerm j hn (-x)).const_mul
    ((-1 : ℂ) ^ (j + 1))).congr
  exact Eventually.of_forall fun u => (reflectedCausalMomentGammaTerm_eq hvan x u).symm

theorem integrableOn_reflectedCausalMomentPolarTerm
    {a : ℝ} (ha : a < 3 / 4) (hlo : -1 / 2 ≤ w.re) (x : ℝ) :
    IntegrableOn (reflectedCausalMomentPolarTerm j a w x) (Ioi 0) := by
  have hn : (-w).re ≤ 1 / 2 := by simp only [Complex.neg_re]; linarith
  apply ((integrableOn_causalMomentPolarTerm j ha hn (-x)).const_mul
    ((-1 : ℂ) ^ (j + 1))).congr
  exact Eventually.of_forall fun u => (reflectedCausalMomentPolarTerm_eq hvan a x u).symm

theorem summable_norm_reflectedCausalMomentPrimeTerm (x : ℝ) :
    Summable (fun n => ‖reflectedCausalMomentPrimeTerm j w x n‖) := by
  simpa only [reflectedCausalMomentPrimeTerm_eq hvan, norm_mul, norm_pow, norm_neg,
    norm_one, one_pow, one_mul] using summable_norm_causalMomentPrimeTerm j (-w) (-x)

end VanishingMoments

/-- The literal backward Gamma, both pole, and full prime actions on a causal moment. -/
def reflectedCausalMomentArithmeticAction (j : ℕ) (w : ℂ) (x : ℝ) : ℂ :=
  -archConstant * thetaCausalMoment j w x +
    (∫ u in Ioi (0 : ℝ), reflectedCausalMomentGammaTerm j w x u) +
    (∫ u in Ioi (0 : ℝ), reflectedCausalMomentPolarTerm j (1 / 2) w x u) +
    (∫ u in Ioi (0 : ℝ), reflectedCausalMomentPolarTerm j (-1 / 2) w x u) -
    ∑' n, reflectedCausalMomentPrimeTerm j w x n

theorem reflectedCausalMomentArithmeticAction_eq {j : ℕ} {w : ℂ}
    (hvan : ∀ x : ℝ, (∫ t : ℝ,
      ((t - x : ℝ) : ℂ) ^ j * (thetaCuspFullSource t : ℂ) * Complex.exp (w * t)) = 0)
    (x : ℝ) :
    reflectedCausalMomentArithmeticAction j w x =
      (-1 : ℂ) ^ (j + 1) * causalMomentArithmeticAction j (-w) (-x) := by
  rw [reflectedCausalMomentArithmeticAction, causalMomentArithmeticAction,
    thetaCausalMoment_reflection hvan x]
  simp_rw [reflectedCausalMomentGammaTerm_eq hvan,
    reflectedCausalMomentPolarTerm_eq hvan, reflectedCausalMomentPrimeTerm_eq hvan,
    integral_const_mul, tsum_mul_left]
  ring

/-- The complete literal action on a vanishing-moment causal chain is its next whole moment. -/
theorem fullCausalMomentArithmeticAction_eq {j : ℕ} {w : ℂ}
    (hvan : ∀ x : ℝ, (∫ t : ℝ,
      ((t - x : ℝ) : ℂ) ^ j * (thetaCuspFullSource t : ℂ) * Complex.exp (w * t)) = 0)
    (hlo : -1 / 2 ≤ w.re) (hhi : w.re ≤ 1 / 2) (x : ℝ) :
    causalMomentArithmeticAction j w x + reflectedCausalMomentArithmeticAction j w x =
      Complex.exp (-(w * x)) *
        ∫ t : ℝ, ((t - x : ℝ) : ℂ) ^ (j + 1) *
          (thetaCuspFullSource t : ℂ) * Complex.exp (w * t) := by
  rw [reflectedCausalMomentArithmeticAction_eq hvan,
    causalMomentArithmeticAction_add_reflected j hlo hhi, hvan x, mul_zero, zero_add]

theorem thetaCausalMoment_whole_eq_sum (j : ℕ) (w : ℂ) (x : ℝ) :
    (∫ t : ℝ, ((t - x : ℝ) : ℂ) ^ j *
      (thetaCuspFullSource t : ℂ) * Complex.exp (w * t)) =
      ∑ i ∈ Finset.range (j + 1), (-(x : ℂ)) ^ (j - i) * (j.choose i : ℂ) *
        ∫ t : ℝ, (t : ℂ) ^ i * (thetaCuspFullSource t : ℂ) * Complex.exp (w * t) := by
  have hi (i : ℕ) : Integrable (fun t : ℝ =>
      (-(x : ℂ)) ^ (j - i) * (j.choose i : ℂ) *
        ((t : ℂ) ^ i * (thetaCuspFullSource t : ℂ) * Complex.exp (w * t))) :=
    (thetaCuspTiltSource.integrable_mul_exp w i).const_mul _
  have he (t : ℝ) : ((t - x : ℝ) : ℂ) ^ j *
      (thetaCuspFullSource t : ℂ) * Complex.exp (w * t) =
      ∑ i ∈ Finset.range (j + 1), (-(x : ℂ)) ^ (j - i) * (j.choose i : ℂ) *
        ((t : ℂ) ^ i * (thetaCuspFullSource t : ℂ) * Complex.exp (w * t)) := by
    simp only [Complex.ofReal_sub]
    simp only [sub_eq_add_neg, add_pow, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun i _ => hi i)]
  simp only [integral_const_mul]

/-- Lower zero moments remove all dependence on the causal cut from the first surviving moment. -/
theorem thetaCausalMoment_whole_eq_of_lower_vanish {j : ℕ} {w : ℂ}
    (hvan : ∀ i : ℕ, i < j → (∫ t : ℝ,
      (t : ℂ) ^ i * (thetaCuspFullSource t : ℂ) * Complex.exp (w * t)) = 0) (x : ℝ) :
    (∫ t : ℝ, ((t - x : ℝ) : ℂ) ^ j *
      (thetaCuspFullSource t : ℂ) * Complex.exp (w * t)) =
      ∫ t : ℝ, (t : ℂ) ^ j * (thetaCuspFullSource t : ℂ) * Complex.exp (w * t) := by
  rw [thetaCausalMoment_whole_eq_sum, Finset.sum_eq_single j]
  · simp
  · intro i hi hij
    have hi' : i < j := by
      have := Finset.mem_range.mp hi
      omega
    rw [hvan i hi', mul_zero]
  · intro hj
    exact (hj (Finset.mem_range.mpr (Nat.lt_succ_self j))).elim

/-- Every order of a zero contributes its exact next moment to the literal complete action. -/
theorem fullCausalMomentArithmeticAction_eq_nextMoment {j : ℕ} {w : ℂ}
    (hvan : ∀ i : ℕ, i ≤ j → (∫ t : ℝ,
      (t : ℂ) ^ i * (thetaCuspFullSource t : ℂ) * Complex.exp (w * t)) = 0)
    (hlo : -1 / 2 ≤ w.re) (hhi : w.re ≤ 1 / 2) (x : ℝ) :
    causalMomentArithmeticAction j w x + reflectedCausalMomentArithmeticAction j w x =
      Complex.exp (-(w * x)) *
        ∫ t : ℝ, (t : ℂ) ^ (j + 1) * (thetaCuspFullSource t : ℂ) * Complex.exp (w * t) := by
  have hv (y : ℝ) : (∫ t : ℝ, ((t - y : ℝ) : ℂ) ^ j *
      (thetaCuspFullSource t : ℂ) * Complex.exp (w * t)) = 0 := by
    rw [thetaCausalMoment_whole_eq_of_lower_vanish (fun i hi => hvan i (by omega)), hvan j le_rfl]
  rw [fullCausalMomentArithmeticAction_eq hv hlo hhi,
    thetaCausalMoment_whole_eq_of_lower_vanish (fun i hi => hvan i (by omega))]

end RHTower.ThetaSourceWard
