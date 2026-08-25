import GaloisForLFunctions.RHTower.MomentFockEntire
import GaloisForLFunctions.RHTower.GaussianMonomialTailAsymptotic

/-!
# Exact polynomial radial moment Fock model

For `m ≥ 2`, this file constructs the literal radial monomial moments of the weight
`exp (-2 (1 + r²)^(m/2))`.  Gaussian domination proves finiteness.  A unit-width annulus outside
any prescribed point gives a geometric lower bound in monomial degree, hence every point kernel is
in `ℓ²`.  The resulting coefficient Hilbert space has bounded evaluations, a distinguished
constant vector, and unit normalized kernels at all prime-log nodes.
-/

open Filter Topology Set MeasureTheory
open scoped Real

namespace RHTower

noncomputable section

/-- Exact polynomial doubling-Fock potential on a radial ray. -/
def polynomialFockPotential (m r : ℝ) : ℝ :=
  (1 + r ^ 2) ^ (m / 2)

/-- Polar radial integrand for the squared norm of the `n`th monomial. -/
def polynomialFockMomentIntegrand (m : ℝ) (n : ℕ) (r : ℝ) : ℝ :=
  |r| ^ (2 * n + 1) * Real.exp (-2 * polynomialFockPotential m r)

/-- Exact squared radial norm of the `n`th monomial, with polar factor `2π`. -/
def polynomialFockMoment (m : ℝ) (n : ℕ) : ℝ :=
  2 * Real.pi * ∫ r in Ioi 0, polynomialFockMomentIntegrand m n r

theorem continuous_polynomialFockPotential (m : ℝ) :
    Continuous (polynomialFockPotential m) := by
  unfold polynomialFockPotential
  apply Continuous.rpow_const
  · fun_prop
  · intro r
    left
    positivity

theorem continuous_polynomialFockMomentIntegrand (m : ℝ) (n : ℕ) :
    Continuous (polynomialFockMomentIntegrand m n) := by
  unfold polynomialFockMomentIntegrand
  exact (continuous_abs.pow _).mul
    (Real.continuous_exp.comp
      (continuous_const.mul (continuous_polynomialFockPotential m)))

theorem polynomialFockPotential_ge_sq
    {m r : ℝ} (hm : 2 ≤ m) :
    r ^ 2 ≤ polynomialFockPotential m r := by
  have hbase : 1 ≤ 1 + r ^ 2 := by nlinarith [sq_nonneg r]
  have hexp : (1 : ℝ) ≤ m / 2 := by linarith
  calc
    r ^ 2 ≤ 1 + r ^ 2 := by linarith
    _ = (1 + r ^ 2) ^ (1 : ℝ) := by rw [Real.rpow_one]
    _ ≤ (1 + r ^ 2) ^ (m / 2) :=
      Real.rpow_le_rpow_of_exponent_le hbase hexp
    _ = polynomialFockPotential m r := rfl

theorem polynomialFockPotential_monoOn_nonneg
    {m r s : ℝ} (hm : 0 ≤ m) (hr : 0 ≤ r) (hrs : r ≤ s) :
    polynomialFockPotential m r ≤ polynomialFockPotential m s := by
  have hs : 0 ≤ s := hr.trans hrs
  have hbase : 1 + r ^ 2 ≤ 1 + s ^ 2 := by nlinarith
  unfold polynomialFockPotential
  exact Real.rpow_le_rpow (by positivity) hbase (by positivity)

theorem integrableOn_polynomialFockMomentIntegrand
    {m : ℝ} (hm : 2 ≤ m) (n : ℕ) :
    IntegrableOn (polynomialFockMomentIntegrand m n) (Ioi 0) := by
  have hgauss := integrableOn_pow_mul_exp_neg_mul_sq_Ioi_zero (2 * n + 1)
    (b := 2) (by norm_num)
  apply hgauss.mono'
  · exact (continuous_polynomialFockMomentIntegrand m n).aestronglyMeasurable
  · rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with r hr
    have hr0 : 0 ≤ r := hr.le
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · unfold polynomialFockMomentIntegrand
      rw [abs_of_pos hr]
      have hpot := polynomialFockPotential_ge_sq (m := m) (r := r) hm
      have hexp : Real.exp (-2 * polynomialFockPotential m r) ≤
          Real.exp (-(2 * r ^ 2)) := by
        rw [Real.exp_le_exp]
        linarith
      exact mul_le_mul_of_nonneg_left hexp (by positivity)
    · unfold polynomialFockMomentIntegrand
      positivity

theorem polynomialFockMomentIntegrand_pos
    (m : ℝ) (n : ℕ) {r : ℝ} (hr : 0 < r) :
    0 < polynomialFockMomentIntegrand m n r := by
  unfold polynomialFockMomentIntegrand
  positivity

theorem polynomialFockMoment_pos
    {m : ℝ} (hm : 2 ≤ m) (n : ℕ) :
    0 < polynomialFockMoment m n := by
  have hfi := integrableOn_polynomialFockMomentIntegrand hm n
  have hsupport : 0 < (volume.restrict (Ioi 0))
      (Function.support (polynomialFockMomentIntegrand m n)) := by
    have hsubset : Ioc (1 / 2 : ℝ) (3 / 2) ⊆
        Function.support (polynomialFockMomentIntegrand m n) := by
      intro r hr
      exact Function.mem_support.mpr
        (polynomialFockMomentIntegrand_pos m n
          ((by norm_num : (0 : ℝ) < 1 / 2).trans hr.1)).ne'
    have hinterval : 0 < (volume.restrict (Ioi 0)) (Ioc (1 / 2 : ℝ) (3 / 2)) := by
      rw [Measure.restrict_apply measurableSet_Ioc]
      norm_num [Ioc_inter_Ioi]
    exact hinterval.trans_le (measure_mono hsubset)
  have hwhole : 0 < ∫ r in Ioi 0, polynomialFockMomentIntegrand m n r :=
    (integral_pos_iff_support_of_nonneg
      (fun r => by unfold polynomialFockMomentIntegrand; positivity) hfi).2 hsupport
  rw [polynomialFockMoment]
  positivity

/-- Integrating over one annulus gives a geometric lower bound uniform in monomial degree. -/
theorem polynomialFockMoment_lower_geometric
    {m R : ℝ} (hm : 2 ≤ m) (hR : 1 ≤ R) (n : ℕ) :
    2 * Real.pi * Real.exp (-2 * polynomialFockPotential m (R + 1)) *
        R ^ (2 * n) ≤ polynomialFockMoment m n := by
  let c : ℝ := Real.exp (-2 * polynomialFockPotential m (R + 1)) * R ^ (2 * n)
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hpoint : ∀ r ∈ Ioc R (R + 1), c ≤ polynomialFockMomentIntegrand m n r := by
    intro r hr
    have hr0 : 0 < r := hR0.trans hr.1
    have hrs : r ≤ R + 1 := hr.2
    have hpot := polynomialFockPotential_monoOn_nonneg
      (m := m) (r := r) (s := R + 1) (by linarith) hr0.le hrs
    have hexp : Real.exp (-2 * polynomialFockPotential m (R + 1)) ≤
        Real.exp (-2 * polynomialFockPotential m r) := by
      rw [Real.exp_le_exp]
      linarith
    have hpow : R ^ (2 * n) ≤ |r| ^ (2 * n + 1) := by
      rw [abs_of_pos hr0, pow_succ]
      calc
        R ^ (2 * n) ≤ r ^ (2 * n) :=
          pow_le_pow_left₀ hR0.le hr.1.le (2 * n)
        _ = r ^ (2 * n) * 1 := by ring
        _ ≤ r ^ (2 * n) * r :=
          mul_le_mul_of_nonneg_left (hR.trans hr.1.le) (by positivity)
    calc
      c ≤ Real.exp (-2 * polynomialFockPotential m r) * |r| ^ (2 * n + 1) := by
        exact mul_le_mul hexp hpow (by positivity) (by positivity)
      _ = polynomialFockMomentIntegrand m n r := by
        rw [polynomialFockMomentIntegrand, mul_comm]
  have hconstInt : ∫ _r in Ioc R (R + 1), c = c := by
    rw [setIntegral_const]
    simp [c]
  have hfint := integrableOn_polynomialFockMomentIntegrand hm n
  have hcint : IntegrableOn (fun _r : ℝ => c) (Ioc R (R + 1)) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)]
    exact continuous_const.intervalIntegrable _ _
  have hinterInt : ∫ r in Ioc R (R + 1), c ≤
      ∫ r in Ioc R (R + 1), polynomialFockMomentIntegrand m n r := by
    apply setIntegral_mono_ae_restrict hcint
      (hfint.mono_set (by
        intro r hr
        exact hR0.trans hr.1))
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact hpoint r hr
  have hsubset : Ioc R (R + 1) ⊆ Ioi (0 : ℝ) := by
    intro r hr
    exact hR0.trans hr.1
  have htoWhole : ∫ r in Ioc R (R + 1), polynomialFockMomentIntegrand m n r ≤
      ∫ r in Ioi 0, polynomialFockMomentIntegrand m n r :=
    integral_mono_measure (Measure.restrict_mono hsubset le_rfl)
      (ae_of_all _ fun r => by unfold polynomialFockMomentIntegrand; positivity) hfint
  rw [polynomialFockMoment]
  have hpi : 0 ≤ 2 * Real.pi := by positivity
  calc
    2 * Real.pi * Real.exp (-2 * polynomialFockPotential m (R + 1)) * R ^ (2 * n) =
        (2 * Real.pi) * c := by dsimp [c]; ring
    _ = (2 * Real.pi) * (∫ r in Ioc R (R + 1), c) := by rw [hconstInt]
    _ ≤ (2 * Real.pi) *
        (∫ r in Ioi 0, polynomialFockMomentIntegrand m n r) :=
      mul_le_mul_of_nonneg_left (hinterInt.trans htoWhole) hpi

theorem norm_momentFockKernelCoeff_polynomial_sq
    {m : ℝ} (hm : 2 ≤ m) (z : ℂ) (n : ℕ) :
    ‖momentFockKernelCoeff (polynomialFockMoment m) z n‖ ^ (2 : ℝ) =
      ‖z‖ ^ (2 * n) / polynomialFockMoment m n := by
  have hmoment := polynomialFockMoment_pos hm n
  have hsqrt : Real.sqrt (polynomialFockMoment m n) ≠ 0 :=
    (Real.sqrt_pos.2 hmoment).ne'
  rw [Real.rpow_two]
  simp only [momentFockKernelCoeff, norm_div, norm_pow, Complex.norm_conj,
    Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  rw [div_pow, ← pow_mul]
  field_simp [hsqrt]
  rw [Real.sq_sqrt hmoment.le]
  ring

/-- Exact polynomial radial moments instantiate the coefficient RKHS at every point. -/
def polynomialMomentFockData (m : ℝ) (hm : 2 ≤ m) : MomentFockData where
  weight := polynomialFockMoment m
  weight_pos := polynomialFockMoment_pos hm
  kernel_summable := by
    intro z
    let R : ℝ := ‖z‖ + 1
    let A : ℝ := 2 * Real.pi * Real.exp (-2 * polynomialFockPotential m (R + 1))
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
        ‖momentFockKernelCoeff (polynomialFockMoment m) z n‖ ^ (2 : ℝ)) ?_ ?_ hgeom
    · intro n
      positivity
    · intro n
      rw [norm_momentFockKernelCoeff_polynomial_sq hm]
      have hlower : A * R ^ (2 * n) ≤ polynomialFockMoment m n := by
        simpa [A] using polynomialFockMoment_lower_geometric hm hR n
      have hden : 0 < A * R ^ (2 * n) := mul_pos hA (pow_pos hR0 _)
      calc
        ‖z‖ ^ (2 * n) / polynomialFockMoment m n ≤
            ‖z‖ ^ (2 * n) / (A * R ^ (2 * n)) :=
          div_le_div_of_nonneg_left (by positivity) hden hlower
        _ = A⁻¹ * q ^ n := by
          dsimp [q]
          rw [← pow_mul, div_pow]
          field_simp [hA.ne', hR0.ne']

/-- Exact polynomial Fock evaluation in the radial moment coefficient model. -/
def polynomialMomentFockEvaluation
    (m : ℝ) (hm : 2 ≤ m) (z : ℂ) : MomentFock →L[ℂ] ℂ :=
  momentFockEvaluation (polynomialMomentFockData m hm) z

/-- Distinguished constant vector in the exact polynomial radial moment model. -/
def polynomialMomentFockOne (m : ℝ) (hm : 2 ≤ m) : MomentFock :=
  momentFockOne (polynomialMomentFockData m hm)

theorem polynomialMomentFockEvaluation_one
    (m : ℝ) (hm : 2 ≤ m) (z : ℂ) :
    polynomialMomentFockEvaluation m hm z (polynomialMomentFockOne m hm) = 1 :=
  momentFockEvaluation_one _ _

/-- Entire function represented by a vector in the exact polynomial radial moment carrier. -/
def polynomialMomentFockFunction
    (m : ℝ) (hm : 2 ≤ m) (f : MomentFock) : ℂ → ℂ :=
  momentFockFunction (polynomialMomentFockData m hm) f

theorem differentiable_polynomialMomentFockFunction
    (m : ℝ) (hm : 2 ≤ m) (f : MomentFock) :
    Differentiable ℂ (polynomialMomentFockFunction m hm f) :=
  differentiable_momentFockFunction _ _

theorem polynomialMomentFockFunction_eq_evaluation
    (m : ℝ) (hm : 2 ≤ m) (f : MomentFock) (z : ℂ) :
    polynomialMomentFockFunction m hm f z = polynomialMomentFockEvaluation m hm z f :=
  momentFockFunction_eq_evaluation _ _ _

theorem polynomialMomentFockFunction_one
    (m : ℝ) (hm : 2 ≤ m) (z : ℂ) :
    polynomialMomentFockFunction m hm (polynomialMomentFockOne m hm) z = 1 :=
  momentFockFunction_one _ _

/-- Normalized kernel family at every critical prime-log node in the exact polynomial model. -/
def criticalPrimePolynomialMomentFockKernel
    (m : ℝ) (hm : 2 ≤ m) (p : Nat.Primes) : MomentFock :=
  criticalPrimeMomentFockKernel (polynomialMomentFockData m hm) p

theorem norm_criticalPrimePolynomialMomentFockKernel
    (m : ℝ) (hm : 2 ≤ m) (p : Nat.Primes) :
    ‖criticalPrimePolynomialMomentFockKernel m hm p‖ = 1 :=
  norm_criticalPrimeMomentFockKernel _ _

end

end RHTower
