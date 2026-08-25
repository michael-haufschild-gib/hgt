import GaloisForLFunctions.RHTower.RapidExponentialFockPotentialGeometry
import GaloisForLFunctions.RHTower.MomentFockEntire

/-!
# Exact rapid exponential radial moment Fock model

For `a > 0`, this file constructs the coefficient RKHS whose monomial weights are the literal
radial moments of `exp (-2 exp (2 a r))`.  Ordinary exponential domination proves finiteness;
one fixed annulus beyond each evaluation point proves bounded evaluation everywhere.
-/

open Filter Topology Set MeasureTheory
open scoped Real

namespace RHTower

noncomputable section

/-- Polar radial integrand for the squared norm of the `n`th rapid-Fock monomial. -/
def rapidExponentialFockMomentIntegrand (a : ℝ) (n : ℕ) (r : ℝ) : ℝ :=
  |r| ^ (2 * n + 1) * Real.exp (-2 * rapidExponentialFockPotential a r)

/-- Exact squared monomial norm, including the polar factor `2π`. -/
def rapidExponentialFockMoment (a : ℝ) (n : ℕ) : ℝ :=
  2 * Real.pi * ∫ r in Ioi 0, rapidExponentialFockMomentIntegrand a n r

theorem continuous_rapidExponentialFockPotential (a : ℝ) :
    Continuous (rapidExponentialFockPotential a) := by
  unfold rapidExponentialFockPotential
  fun_prop

theorem continuous_rapidExponentialFockMomentIntegrand (a : ℝ) (n : ℕ) :
    Continuous (rapidExponentialFockMomentIntegrand a n) := by
  unfold rapidExponentialFockMomentIntegrand
  exact (continuous_abs.pow _).mul
    (Real.continuous_exp.comp
      (continuous_const.mul (continuous_rapidExponentialFockPotential a)))

theorem rapidExponentialFockPotential_monoOn_nonneg
    {a r s : ℝ} (ha : 0 ≤ a) (hrs : r ≤ s) :
    rapidExponentialFockPotential a r ≤ rapidExponentialFockPotential a s := by
  unfold rapidExponentialFockPotential
  rw [Real.exp_le_exp]
  nlinarith

private theorem integrableOn_pow_mul_exp_neg_mul_Ioi
    {c : ℝ} (hc : 0 < c) (j : ℕ) :
    IntegrableOn (fun r : ℝ => r ^ j * Real.exp (-(c * r))) (Ioi (0 : ℝ)) := by
  have hGamma : IntegrableOn
      (fun x : ℝ => Real.exp (-x) * x ^ (((j : ℝ) + 1) - 1)) (Ioi (0 : ℝ)) :=
    Real.GammaIntegral_convergent (by positivity)
  have hscale := (integrableOn_Ioi_comp_mul_left_iff
      (fun x : ℝ => Real.exp (-x) * x ^ (((j : ℝ) + 1) - 1)) 0 hc).mpr
      (by simpa using hGamma)
  have hmul : IntegrableOn
      (fun x : ℝ => (c ^ j)⁻¹ *
        (Real.exp (-(c * x)) * (c * x) ^ (((j : ℝ) + 1) - 1))) (Ioi (0 : ℝ)) :=
    hscale.const_mul _
  refine hmul.congr_fun ?_ measurableSet_Ioi
  intro x hx
  have hx0 : 0 < x := hx
  have hcj : c ^ j ≠ 0 := by positivity
  have hpow : (c * x) ^ (((j : ℝ) + 1) - 1) = c ^ j * x ^ j := by
    rw [show ((j : ℝ) + 1) - 1 = (j : ℝ) by ring,
      Real.rpow_natCast, mul_pow]
  simp only [hpow]
  field_simp

theorem integrableOn_rapidExponentialFockMomentIntegrand
    {a : ℝ} (ha : 0 < a) (n : ℕ) :
    IntegrableOn (rapidExponentialFockMomentIntegrand a n) (Ioi 0) := by
  have hdom := integrableOn_pow_mul_exp_neg_mul_Ioi (j := 2 * n + 1)
    (show 0 < 4 * a by positivity)
  apply hdom.mono'
  · exact (continuous_rapidExponentialFockMomentIntegrand a n).aestronglyMeasurable
  · rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with r hr
    have hr0 : 0 ≤ r := hr.le
    have hlinear : 2 * a * r ≤ Real.exp (2 * a * r) := by
      linarith [Real.add_one_le_exp (2 * a * r)]
    have hexp :
        Real.exp (-2 * rapidExponentialFockPotential a r) ≤
          Real.exp (-(4 * a * r)) := by
      rw [Real.exp_le_exp]
      unfold rapidExponentialFockPotential
      linarith
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · unfold rapidExponentialFockMomentIntegrand
      rw [abs_of_pos hr]
      exact mul_le_mul_of_nonneg_left hexp (by positivity)
    · unfold rapidExponentialFockMomentIntegrand
      positivity

theorem rapidExponentialFockMomentIntegrand_pos
    (a : ℝ) (n : ℕ) {r : ℝ} (hr : 0 < r) :
    0 < rapidExponentialFockMomentIntegrand a n r := by
  unfold rapidExponentialFockMomentIntegrand
  positivity

theorem rapidExponentialFockMoment_pos
    {a : ℝ} (ha : 0 < a) (n : ℕ) :
    0 < rapidExponentialFockMoment a n := by
  have hfi := integrableOn_rapidExponentialFockMomentIntegrand ha n
  have hsupport : 0 < (volume.restrict (Ioi 0))
      (Function.support (rapidExponentialFockMomentIntegrand a n)) := by
    have hsubset : Ioc (1 / 2 : ℝ) (3 / 2) ⊆
        Function.support (rapidExponentialFockMomentIntegrand a n) := by
      intro r hr
      exact Function.mem_support.mpr
        (rapidExponentialFockMomentIntegrand_pos a n
          ((by norm_num : (0 : ℝ) < 1 / 2).trans hr.1)).ne'
    have hinterval : 0 < (volume.restrict (Ioi 0)) (Ioc (1 / 2 : ℝ) (3 / 2)) := by
      rw [Measure.restrict_apply measurableSet_Ioc]
      norm_num [Ioc_inter_Ioi]
    exact hinterval.trans_le (measure_mono hsubset)
  have hwhole : 0 < ∫ r in Ioi 0, rapidExponentialFockMomentIntegrand a n r :=
    (integral_pos_iff_support_of_nonneg
      (fun r => by unfold rapidExponentialFockMomentIntegrand; positivity) hfi).2 hsupport
  rw [rapidExponentialFockMoment]
  positivity

/-- A unit annulus supplies a geometric moment lower bound uniform in degree. -/
theorem rapidExponentialFockMoment_lower_geometric
    {a R : ℝ} (ha : 0 < a) (hR : 1 ≤ R) (n : ℕ) :
    2 * Real.pi * Real.exp (-2 * rapidExponentialFockPotential a (R + 1)) *
        R ^ (2 * n) ≤ rapidExponentialFockMoment a n := by
  let c : ℝ := Real.exp (-2 * rapidExponentialFockPotential a (R + 1)) * R ^ (2 * n)
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hpoint : ∀ r ∈ Ioc R (R + 1), c ≤ rapidExponentialFockMomentIntegrand a n r := by
    intro r hr
    have hr0 : 0 < r := hR0.trans hr.1
    have hpot := rapidExponentialFockPotential_monoOn_nonneg ha.le hr.2
    have hexp : Real.exp (-2 * rapidExponentialFockPotential a (R + 1)) ≤
        Real.exp (-2 * rapidExponentialFockPotential a r) := by
      rw [Real.exp_le_exp]
      linarith
    have hpow : R ^ (2 * n) ≤ |r| ^ (2 * n + 1) := by
      rw [abs_of_pos hr0, pow_succ]
      calc
        R ^ (2 * n) ≤ r ^ (2 * n) := pow_le_pow_left₀ hR0.le hr.1.le _
        _ = r ^ (2 * n) * 1 := by ring
        _ ≤ r ^ (2 * n) * r :=
          mul_le_mul_of_nonneg_left (hR.trans hr.1.le) (by positivity)
    calc
      c ≤ Real.exp (-2 * rapidExponentialFockPotential a r) * |r| ^ (2 * n + 1) :=
        mul_le_mul hexp hpow (by positivity) (by positivity)
      _ = rapidExponentialFockMomentIntegrand a n r := by
        rw [rapidExponentialFockMomentIntegrand, mul_comm]
  have hconstInt : ∫ _r in Ioc R (R + 1), c = c := by
    rw [setIntegral_const]
    simp [c]
  have hfint := integrableOn_rapidExponentialFockMomentIntegrand ha n
  have hcint : IntegrableOn (fun _r : ℝ => c) (Ioc R (R + 1)) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)]
    exact continuous_const.intervalIntegrable _ _
  have hinterInt : ∫ r in Ioc R (R + 1), c ≤
      ∫ r in Ioc R (R + 1), rapidExponentialFockMomentIntegrand a n r := by
    apply setIntegral_mono_ae_restrict hcint
      (hfint.mono_set (fun r hr => hR0.trans hr.1))
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact hpoint r hr
  have hsubset : Ioc R (R + 1) ⊆ Ioi (0 : ℝ) :=
    fun r hr => hR0.trans hr.1
  have htoWhole : ∫ r in Ioc R (R + 1), rapidExponentialFockMomentIntegrand a n r ≤
      ∫ r in Ioi 0, rapidExponentialFockMomentIntegrand a n r :=
    integral_mono_measure (Measure.restrict_mono hsubset le_rfl)
      (ae_of_all _ fun r => by unfold rapidExponentialFockMomentIntegrand; positivity) hfint
  rw [rapidExponentialFockMoment]
  calc
    2 * Real.pi * Real.exp (-2 * rapidExponentialFockPotential a (R + 1)) *
        R ^ (2 * n) = (2 * Real.pi) * c := by dsimp [c]; ring
    _ = (2 * Real.pi) * (∫ r in Ioc R (R + 1), c) := by rw [hconstInt]
    _ ≤ (2 * Real.pi) *
        (∫ r in Ioi 0, rapidExponentialFockMomentIntegrand a n r) :=
      mul_le_mul_of_nonneg_left (hinterInt.trans htoWhole) (by positivity)

theorem norm_momentFockKernelCoeff_rapidExponential_sq
    {a : ℝ} (ha : 0 < a) (z : ℂ) (n : ℕ) :
    ‖momentFockKernelCoeff (rapidExponentialFockMoment a) z n‖ ^ (2 : ℝ) =
      ‖z‖ ^ (2 * n) / rapidExponentialFockMoment a n := by
  have hmoment := rapidExponentialFockMoment_pos ha n
  have hsqrt : Real.sqrt (rapidExponentialFockMoment a n) ≠ 0 :=
    (Real.sqrt_pos.2 hmoment).ne'
  rw [Real.rpow_two]
  simp only [momentFockKernelCoeff, norm_div, norm_pow, Complex.norm_conj,
    Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  rw [div_pow, ← pow_mul]
  field_simp [hsqrt]
  rw [Real.sq_sqrt hmoment.le]
  ring

/-- Literal rapid exponential radial moments instantiate the coefficient RKHS. -/
def rapidExponentialMomentFockData (a : ℝ) (ha : 0 < a) : MomentFockData where
  weight := rapidExponentialFockMoment a
  weight_pos := rapidExponentialFockMoment_pos ha
  kernel_summable := by
    intro z
    let R : ℝ := ‖z‖ + 1
    let A : ℝ := 2 * Real.pi *
      Real.exp (-2 * rapidExponentialFockPotential a (R + 1))
    let q : ℝ := (‖z‖ / R) ^ 2
    have hR : 1 ≤ R := by dsimp [R]; linarith [norm_nonneg z]
    have hR0 : 0 < R := zero_lt_one.trans_le hR
    have hA : 0 < A := by dsimp [A]; positivity
    have hratio : ‖z‖ / R < 1 := (div_lt_one hR0).2 (by dsimp [R]; linarith)
    have hq : ‖q‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp [q]; positivity)]
      dsimp [q]
      nlinarith [div_nonneg (norm_nonneg z) hR0.le]
    have hgeom : Summable fun n : ℕ => A⁻¹ * q ^ n :=
      (summable_geometric_of_norm_lt_one hq).mul_left A⁻¹
    refine Summable.of_nonneg_of_le
      (f := fun n : ℕ => A⁻¹ * q ^ n)
      (g := fun n : ℕ =>
        ‖momentFockKernelCoeff (rapidExponentialFockMoment a) z n‖ ^ (2 : ℝ))
      (fun n => by positivity) ?_ hgeom
    intro n
    rw [norm_momentFockKernelCoeff_rapidExponential_sq ha]
    have hlower : A * R ^ (2 * n) ≤ rapidExponentialFockMoment a n := by
      simpa [A] using rapidExponentialFockMoment_lower_geometric ha hR n
    have hden : 0 < A * R ^ (2 * n) := mul_pos hA (pow_pos hR0 _)
    calc
      ‖z‖ ^ (2 * n) / rapidExponentialFockMoment a n ≤
          ‖z‖ ^ (2 * n) / (A * R ^ (2 * n)) :=
        div_le_div_of_nonneg_left (by positivity) hden hlower
      _ = A⁻¹ * q ^ n := by
        dsimp [q]
        rw [← pow_mul, div_pow]
        field_simp [hA.ne', hR0.ne']

/-- Bounded evaluation in the rapid exponential moment carrier. -/
def rapidExponentialMomentFockEvaluation
    (a : ℝ) (ha : 0 < a) (z : ℂ) : MomentFock →L[ℂ] ℂ :=
  momentFockEvaluation (rapidExponentialMomentFockData a ha) z

/-- Distinguished constant vector in the rapid exponential carrier. -/
def rapidExponentialMomentFockOne (a : ℝ) (ha : 0 < a) : MomentFock :=
  momentFockOne (rapidExponentialMomentFockData a ha)

theorem rapidExponentialMomentFockEvaluation_one
    (a : ℝ) (ha : 0 < a) (z : ℂ) :
    rapidExponentialMomentFockEvaluation a ha z
      (rapidExponentialMomentFockOne a ha) = 1 :=
  momentFockEvaluation_one _ _

/-- Entire function represented by a rapid exponential moment vector. -/
def rapidExponentialMomentFockFunction
    (a : ℝ) (ha : 0 < a) (f : MomentFock) : ℂ → ℂ :=
  momentFockFunction (rapidExponentialMomentFockData a ha) f

theorem differentiable_rapidExponentialMomentFockFunction
    (a : ℝ) (ha : 0 < a) (f : MomentFock) :
    Differentiable ℂ (rapidExponentialMomentFockFunction a ha f) :=
  differentiable_momentFockFunction _ _

theorem rapidExponentialMomentFockFunction_eq_evaluation
    (a : ℝ) (ha : 0 < a) (f : MomentFock) (z : ℂ) :
    rapidExponentialMomentFockFunction a ha f z =
      rapidExponentialMomentFockEvaluation a ha z f :=
  momentFockFunction_eq_evaluation _ _ _

theorem rapidExponentialMomentFockFunction_one
    (a : ℝ) (ha : 0 < a) (z : ℂ) :
    rapidExponentialMomentFockFunction a ha
      (rapidExponentialMomentFockOne a ha) z = 1 :=
  momentFockFunction_one _ _

/-- Unit normalized kernel at every critical prime-log node in the rapid model. -/
def criticalPrimeRapidExponentialMomentFockKernel
    (a : ℝ) (ha : 0 < a) (p : Nat.Primes) : MomentFock :=
  criticalPrimeMomentFockKernel (rapidExponentialMomentFockData a ha) p

theorem norm_criticalPrimeRapidExponentialMomentFockKernel
    (a : ℝ) (ha : 0 < a) (p : Nat.Primes) :
    ‖criticalPrimeRapidExponentialMomentFockKernel a ha p‖ = 1 :=
  norm_criticalPrimeMomentFockKernel _ _

end

end RHTower
