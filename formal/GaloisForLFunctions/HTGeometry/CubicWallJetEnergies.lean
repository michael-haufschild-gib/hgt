import GaloisForLFunctions.HTGeometry.KummerPhaseWallOverlap

/-!
# Nuclear homotopy jets of the cubic wall

Let `X` be multiplication by the wall coordinate on `H = L²((0, ∞), e^{-x} dx)`.  On the core of
functions carried by a bounded window `[0, R]` the iterated commutators of the wall operator
`A` with `X` are the kernel operators `K_n` of `(x - y)ⁿ κ(x, y)`:

`K_0 = A`,  `K_{n+1} f = X K_n f - K_n X f`,

and `K_n` is the unique bounded operator agreeing with `adⁿ_X(A)` on the core.  Their
Hilbert–Schmidt energies are

`‖K_n‖²_HS = ∬ (x - y)^{2n} κ² e^{-(x+y)} = 48 (2n)!/((2n+3)(2n+5)(2n+7))`,

by the ratio substitution `y = xt`, the Gamma integral in `x` and the Cayley substitution
`t = (1 - v)/(1 + v)`, which turns the energy into `(2n+1)! ∫₀¹ v^{2n}(1 - v²)³ dv`.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory ContinuousLinearMap
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower

local instance isProbabilityMeasure_expMeasure_one_jets : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure one_pos

local instance factTwoNeTopJets : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩

/-! ## Moments of the exponential law -/

theorem integrable_pow_expMeasure_one (k : ℕ) : Integrable (fun x : ℝ => x ^ k) (expMeasure 1) := by
  refine ⟨(continuous_pow k).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm, lintegral_expMeasure_one (by fun_prop)]
  have hint : IntegrableOn (fun x : ℝ => x ^ k * Real.exp (-(1 * x))) (Ioi 0) :=
    integrableOn_pow_mul_exp_neg_mul_Ioi k one_pos
  have hcongr : ∀ x ∈ Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-x)) * ‖x ^ k‖ₑ
      = ENNReal.ofReal (x ^ k * Real.exp (-(1 * x))) := fun x hx => by
    have hx0 : (0 : ℝ) < x := hx
    rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hx0.le k),
      ← ENNReal.ofReal_mul (Real.exp_pos _).le, one_mul, mul_comm]
  rw [setLIntegral_congr_fun measurableSet_Ioi hcongr,
    ← ofReal_integral_eq_lintegral_ofReal hint (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact mul_nonneg (pow_nonneg (le_of_lt hx) _) (Real.exp_pos _).le)]
  exact ENNReal.ofReal_lt_top

theorem integrable_add_pow_expMeasure_prod (m : ℕ) :
    Integrable (fun z : ℝ × ℝ => (z.1 + z.2) ^ m) ((expMeasure 1).prod (expMeasure 1)) := by
  simp_rw [add_pow]
  refine integrable_finsetSum _ fun k _ => ?_
  have h := ((integrable_pow_expMeasure_one k).mul_prod (integrable_pow_expMeasure_one (m - k)))
  have h' := h.mul_const (m.choose k : ℝ)
  refine h'.congr (Eventually.of_forall fun z => ?_)
  simp only

/-! ## The jet integral -/

/-- The jet integrand in ratio coordinates. -/
def jetRatioIntegrand (n : ℕ) (x t : ℝ) : ℝ :=
  routePPrimitiveGammaJuliaStokesWallExponentialRatioKernel t * (1 - t) ^ (2 * n) *
    (x ^ (2 * n + 1) * Real.exp (-((1 + t) * x)))

theorem inner_jet_ratio (n : ℕ) {x : ℝ} (hx : 0 < x) :
    Real.exp (-x) * ∫ y, routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence x y *
        (x - y) ^ (2 * n) ∂(expMeasure 1)
      = ∫ t in Ioi (0 : ℝ), jetRatioIntegrand n x t := by
  rw [integral_expMeasure_one]
  have h := integral_comp_mul_left_Ioi (fun y : ℝ => Real.exp (-y) •
    (routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence x y * (x - y) ^ (2 * n))) 0 hx
  simp only [mul_zero] at h
  rw [show (∫ y in Ioi (0 : ℝ), Real.exp (-y) •
      (routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence x y * (x - y) ^ (2 * n)))
      = x • ∫ t in Ioi (0 : ℝ), Real.exp (-(x * t)) •
        (routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence x (x * t) *
          (x - x * t) ^ (2 * n)) by
    rw [h, smul_smul, mul_inv_cancel₀ hx.ne', one_smul], smul_eq_mul, ← mul_assoc,
    ← smul_eq_mul, ← integral_smul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [smul_eq_mul, jetRatioIntegrand]
  rw [routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence_scale_right hx,
    show x - x * t = x * (1 - t) by ring, mul_pow]
  have hexp : Real.exp (-x) * Real.exp (-(x * t)) = Real.exp (-((1 + t) * x)) := by
    rw [← Real.exp_add]; ring_nf
  rw [← hexp]
  ring

theorem integrableOn_jetRatio_x (n : ℕ) {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun x => jetRatioIntegrand n x t) (Ioi 0) := by
  have h := (integrableOn_pow_mul_exp_neg_mul_Ioi (2 * n + 1)
    (by linarith : (0 : ℝ) < 1 + t)).const_mul
    (routePPrimitiveGammaJuliaStokesWallExponentialRatioKernel t * (1 - t) ^ (2 * n))
  exact h

theorem integral_jetRatio_x (n : ℕ) {t : ℝ} (ht : 0 < t) :
    ∫ x in Ioi (0 : ℝ), jetRatioIntegrand n x t
      = routePPrimitiveGammaJuliaStokesWallExponentialRatioKernel t * (1 - t) ^ (2 * n) *
          ((2 * n + 1).factorial / (1 + t) ^ (2 * n + 1 + 1)) := by
  simp only [jetRatioIntegrand]
  rw [integral_const_mul, integral_pow_mul_exp_neg_mul_Ioi (2 * n + 1) (by linarith)]

theorem integrable_jetRatioIntegrand (n : ℕ) :
    Integrable (Function.uncurry (jetRatioIntegrand n))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hmeas : Measurable (Function.uncurry (jetRatioIntegrand n)) := by
    unfold jetRatioIntegrand routePPrimitiveGammaJuliaStokesWallExponentialRatioKernel
    fun_prop
  rw [integrable_prod_iff' hmeas.aestronglyMeasurable]
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact integrableOn_jetRatio_x n ht
  · refine (integrableOn_routePPrimitiveGammaJuliaStokesWallExponentialRatioKernel.const_mul
      ((2 * n + 1).factorial : ℝ)).mono' ?_ ?_
    · exact (hmeas.norm.stronglyMeasurable.integral_prod_left').aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : (0 : ℝ) < t := ht
      have hR := routePPrimitiveGammaJuliaStokesWallExponentialRatioKernel_nonneg ht0.le
      have hnorm : ∀ x ∈ Ioi (0 : ℝ), ‖jetRatioIntegrand n x t‖
          = routePPrimitiveGammaJuliaStokesWallExponentialRatioKernel t * |1 - t| ^ (2 * n) *
            (x ^ (2 * n + 1) * Real.exp (-((1 + t) * x))) := fun x hx => by
        have hx0 : (0 : ℝ) < x := hx
        rw [jetRatioIntegrand, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hR, abs_pow,
          abs_of_nonneg (mul_nonneg (pow_nonneg hx0.le _) (Real.exp_pos _).le)]
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      simp only [Function.uncurry_apply_pair]
      rw [setIntegral_congr_fun measurableSet_Ioi hnorm, integral_const_mul,
        integral_pow_mul_exp_neg_mul_Ioi (2 * n + 1) (by linarith)]
      have h1 : |1 - t| ^ (2 * n) ≤ (1 + t) ^ (2 * n) :=
        pow_le_pow_left₀ (abs_nonneg _) (abs_le.mpr ⟨by linarith, by linarith⟩) _
      have hpos : (0 : ℝ) < (1 + t) ^ (2 * n + 1 + 1) := by positivity
      rw [mul_comm ((2 * n + 1).factorial : ℝ)]
      calc routePPrimitiveGammaJuliaStokesWallExponentialRatioKernel t * |1 - t| ^ (2 * n) *
            ((2 * n + 1).factorial / (1 + t) ^ (2 * n + 1 + 1))
          ≤ routePPrimitiveGammaJuliaStokesWallExponentialRatioKernel t * (1 + t) ^ (2 * n) *
            ((2 * n + 1).factorial / (1 + t) ^ (2 * n + 1 + 1)) := by gcongr
        _ ≤ routePPrimitiveGammaJuliaStokesWallExponentialRatioKernel t *
            (2 * n + 1).factorial := by
          rw [mul_assoc]
          refine mul_le_mul_of_nonneg_left ?_ hR
          rw [mul_div_assoc', div_le_iff₀ hpos]
          have : (1 + t) ^ (2 * n) ≤ (1 + t) ^ (2 * n + 1 + 1) :=
            pow_le_pow_right₀ (by linarith) (by omega)
          have hf : (0 : ℝ) ≤ (2 * n + 1).factorial := Nat.cast_nonneg _
          nlinarith

theorem integral_pow_mul_one_sub_sq_cube (k : ℕ) :
    ∫ v in (0 : ℝ)..1, v ^ (2 * k) * (1 - v ^ 2) ^ 3
      = 48 / ((2 * (k : ℝ) + 1) * (2 * k + 3) * (2 * k + 5) * (2 * k + 7)) := by
  have hexp : ∀ v : ℝ, v ^ (2 * k) * (1 - v ^ 2) ^ 3
      = v ^ (2 * k) - 3 * v ^ (2 * k + 2) + 3 * v ^ (2 * k + 4) - v ^ (2 * k + 6) := fun v => by
    ring
  simp_rw [hexp]
  rw [intervalIntegral.integral_sub, intervalIntegral.integral_add, intervalIntegral.integral_sub,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, integral_pow,
    integral_pow, integral_pow, integral_pow]
  · push_cast
    field_simp
    ring
  all_goals first
    | exact (continuous_pow _).intervalIntegrable _ _
    | exact ((continuous_pow _).const_mul _).intervalIntegrable _ _
    | exact ((continuous_pow _).sub ((continuous_pow _).const_mul _)).intervalIntegrable _ _
    | exact (((continuous_pow _).sub ((continuous_pow _).const_mul _)).add
        ((continuous_pow _).const_mul _)).intervalIntegrable _ _

theorem integral_Ioo_neg_one_one_of_even {h : ℝ → ℝ} (hc : Continuous h)
    (heven : ∀ v, h (-v) = h v) :
    ∫ v in Ioo (-1 : ℝ) 1, h v = 2 * ∫ v in (0 : ℝ)..1, h v := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num),
    ← intervalIntegral.integral_add_adjacent_intervals (b := 0) (hc.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _)]
  have hneg : ∫ v in (-1 : ℝ)..0, h v = ∫ v in (0 : ℝ)..1, h v := by
    have := intervalIntegral.integral_comp_neg (a := 0) (b := 1) h
    simp only [heven, neg_zero] at this
    exact this.symm
  rw [hneg]
  ring

/-- **(DHNJ.1), integral form.**  `∬ κ² (x - y)^{2n} dμ dμ = 48 (2n)!/((2n+3)(2n+5)(2n+7))`. -/
theorem integral_coherence_mul_sub_pow (n : ℕ) :
    ∫ z, routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence z.1 z.2 *
        (z.1 - z.2) ^ (2 * n) ∂((expMeasure 1).prod (expMeasure 1))
      = 48 * (2 * n).factorial / ((2 * n + 3) * (2 * n + 5) * (2 * n + 7)) := by
  have hint : Integrable (fun z : ℝ × ℝ =>
      routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence z.1 z.2 * (z.1 - z.2) ^ (2 * n))
      ((expMeasure 1).prod (expMeasure 1)) := by
    refine (integrable_add_pow_expMeasure_prod (2 * n)).mono' ?_ ?_
    · unfold routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence
      exact (by fun_prop : Measurable _).aestronglyMeasurable
    · filter_upwards [ae_nonneg_fst_prod (expMeasure 1) (expMeasure 1) expMeasure_one_Iio_zero,
        ae_nonneg_snd_prod (expMeasure 1) (expMeasure 1) expMeasure_one_Iio_zero] with z h1 h2
      have hc := routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence_zero_le_one h1 h2
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hc.1, abs_pow]
      have hle : |z.1 - z.2| ^ (2 * n) ≤ (z.1 + z.2) ^ (2 * n) :=
        pow_le_pow_left₀ (abs_nonneg _) (abs_le.mpr ⟨by linarith, by linarith⟩) _
      calc routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence z.1 z.2 *
            |z.1 - z.2| ^ (2 * n) ≤ 1 * |z.1 - z.2| ^ (2 * n) :=
            mul_le_mul_of_nonneg_right hc.2 (by positivity)
        _ ≤ (z.1 + z.2) ^ (2 * n) := by rw [one_mul]; exact hle
  rw [integral_prod _ hint, integral_expMeasure_one]
  simp only [smul_eq_mul]
  rw [setIntegral_congr_fun measurableSet_Ioi fun x hx => inner_jet_ratio n hx,
    integral_integral_swap (integrable_jetRatioIntegrand n),
    setIntegral_congr_fun measurableSet_Ioi fun t ht => integral_jetRatio_x n ht,
    integral_Ioi_eq_cayley]
  have hpt : ∀ v ∈ Ioo (-1 : ℝ) 1,
      2 / (1 + v) ^ 2 * (routePPrimitiveGammaJuliaStokesWallExponentialRatioKernel
        ((1 - v) / (1 + v)) * (1 - (1 - v) / (1 + v)) ^ (2 * n) *
          ((2 * n + 1).factorial / (1 + (1 - v) / (1 + v)) ^ (2 * n + 1 + 1)))
        = (2 * n + 1).factorial * (v ^ (2 * n) * (1 - v ^ 2) ^ 3 / 2) := by
    intro v hv
    have hv1 : (1 : ℝ) + v ≠ 0 := (show (0 : ℝ) < 1 + v by linarith [hv.1]).ne'
    have h1 : 1 + (1 - v) / (1 + v) = 2 / (1 + v) := by field_simp; ring
    have h2 : 1 - (1 - v) / (1 + v) = 2 * v / (1 + v) := by field_simp; ring
    have hR : routePPrimitiveGammaJuliaStokesWallExponentialRatioKernel ((1 - v) / (1 + v))
        = (1 - v) ^ 3 * (1 + v) ^ 3 := by
      rw [routePPrimitiveGammaJuliaStokesWallExponentialRatioKernel, h1]
      field_simp
      ring
    have hA : (2 * v / (1 + v)) ^ (2 * n) = 2 ^ (2 * n) * v ^ (2 * n) / (1 + v) ^ (2 * n) := by
      rw [div_pow, mul_pow]
    have hB : (2 / (1 + v)) ^ (2 * n + 1 + 1)
        = 2 ^ (2 * n) * 4 / ((1 + v) ^ (2 * n) * (1 + v) ^ 2) := by
      rw [div_pow, pow_succ, pow_succ, pow_succ (1 + v), pow_succ (1 + v)]
      ring
    rw [hR, h2, hA, h1, hB]
    set X := (1 + v) ^ (2 * n)
    set Y := (2 : ℝ) ^ (2 * n)
    have hX : X ≠ 0 := pow_ne_zero _ hv1
    have hY : Y ≠ 0 := pow_ne_zero _ two_ne_zero
    field_simp
    ring
  rw [setIntegral_congr_fun measurableSet_Ioo hpt, integral_const_mul,
    integral_Ioo_neg_one_one_of_even (by fun_prop) (fun v => by simp only [neg_sq, Even.neg_pow
      (even_two_mul n)]), intervalIntegral.integral_div, integral_pow_mul_one_sub_sq_cube,
    Nat.factorial_succ]
  push_cast
  have h1 : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
  have h3 : (2 * (n : ℝ) + 3) ≠ 0 := by positivity
  have h5 : (2 * (n : ℝ) + 5) ≠ 0 := by positivity
  have h7 : (2 * (n : ℝ) + 7) ≠ 0 := by positivity
  field_simp

/-! ## The jet kernels -/

theorem jetEnergyValue_pos (n : ℕ) :
    (0 : ℝ) < 48 * ((2 * n).factorial : ℝ) / ((2 * (n : ℝ) + 3) * (2 * n + 5) * (2 * n + 7)) :=
  div_pos (mul_pos (by norm_num) (by exact_mod_cast Nat.factorial_pos _)) (by positivity)

theorem enorm_jet_sq (n : ℕ) (x y : ℝ) :
    ‖((((x - y) ^ n * wallCubicKernel x y : ℝ)) : ℂ)‖ₑ ^ 2
      = ENNReal.ofReal ((x - y) ^ (2 * n) * wallCubicKernel x y ^ 2) := by
  rw [enorm_ofReal_sq, mul_pow, ← pow_mul, mul_comm n 2]

theorem lintegral_lintegral_jet (n : ℕ) :
    ∫⁻ x, ∫⁻ y, ‖((((x - y) ^ n * wallCubicKernel x y : ℝ)) : ℂ)‖ₑ ^ 2
        ∂(expMeasure 1) ∂(expMeasure 1)
      = ENNReal.ofReal (48 * (2 * n).factorial / ((2 * n + 3) * (2 * n + 5) * (2 * n + 7))) := by
  simp_rw [enorm_jet_sq]
  have hm : Measurable fun z : ℝ × ℝ =>
      (z.1 - z.2) ^ (2 * n) * wallCubicKernel z.1 z.2 ^ 2 :=
    (by fun_prop : Measurable fun z : ℝ × ℝ => (z.1 - z.2) ^ (2 * n)).mul
      (continuous_wallCubicKernel_sq.pow_const 2)
  rw [← lintegral_prod _ hm.ennreal_ofReal.aemeasurable]
  have hae : (fun z : ℝ × ℝ => ENNReal.ofReal ((z.1 - z.2) ^ (2 * n) * wallCubicKernel z.1 z.2 ^ 2))
      =ᵐ[(expMeasure 1).prod (expMeasure 1)] fun z => ENNReal.ofReal
        (routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence z.1 z.2 *
          (z.1 - z.2) ^ (2 * n)) := by
    filter_upwards [ae_nonneg_fst_prod (expMeasure 1) (expMeasure 1) expMeasure_one_Iio_zero,
      ae_nonneg_snd_prod (expMeasure 1) (expMeasure 1) expMeasure_one_Iio_zero] with z h1 h2
    rw [wallCubicKernel_sq h1 h2, mul_comm]
  rw [lintegral_congr_ae hae, ← integral_coherence_mul_sub_pow n]
  refine (ofReal_integral_eq_lintegral_ofReal ?_ ?_).symm
  · have hint := integral_coherence_mul_sub_pow n
    by_contra hni
    rw [integral_undef hni] at hint
    linarith [jetEnergyValue_pos n]
  · filter_upwards [ae_nonneg_fst_prod (expMeasure 1) (expMeasure 1) expMeasure_one_Iio_zero,
      ae_nonneg_snd_prod (expMeasure 1) (expMeasure 1) expMeasure_one_Iio_zero] with z h1 h2
    exact mul_nonneg (routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence_zero_le_one
      h1 h2).1 ((even_two_mul n).pow_nonneg _)

/-- The jet kernel `(x - y)ⁿ κ(x, y)`. -/
def jetKernel (n : ℕ) : SqIntKernel (expMeasure 1) (expMeasure 1) where
  toFun x y := ((((x - y) ^ n * wallCubicKernel x y : ℝ)) : ℂ)
  measurable := Complex.measurable_ofReal.comp
    ((by fun_prop : Measurable fun z : ℝ × ℝ => (z.1 - z.2) ^ n).mul continuous_wallCubicKernel_sq)
  energy_lt_top := by rw [lintegral_lintegral_jet]; exact ENNReal.ofReal_lt_top

/-- **(DHNJ.1).**  `‖K_n‖²_HS = 48 (2n)!/((2n+3)(2n+5)(2n+7))`. -/
theorem hsNormSq_jetKernel (n : ℕ) :
    ContinuousLinearMap.hsNormSq (jetKernel n).op
      = 48 * (2 * n).factorial / ((2 * n + 3) * (2 * n + 5) * (2 * n + 7)) := by
  rw [SqIntKernel.hsNormSq_op]
  change (∫⁻ x, ∫⁻ y, ‖((((x - y) ^ n * wallCubicKernel x y : ℝ)) : ℂ)‖ₑ ^ 2
    ∂(expMeasure 1) ∂(expMeasure 1)).toReal = _
  rw [lintegral_lintegral_jet, ENNReal.toReal_ofReal (jetEnergyValue_pos n).le]

theorem jetKernel_zero_op : (jetKernel 0).op = wallOperator :=
  SqIntKernel.op_congr _ (Eventually.of_forall fun x => Eventually.of_forall fun y => by
    change ((((x - y) ^ 0 * wallCubicKernel x y : ℝ)) : ℂ) = ((wallCubicKernel x y : ℝ) : ℂ)
    rw [pow_zero, one_mul])

/-! ## The commutator recursion on the bounded-window core -/

/-- A function carried by a bounded window `[0, R]`. -/
def IsWindowCarried (f : Lp ℂ 2 (expMeasure 1)) : Prop :=
  ∃ R : ℝ, ∀ᵐ x ∂(expMeasure 1), R < x → (f : ℝ → ℂ) x = 0

theorem memLp_coordMul {f : Lp ℂ 2 (expMeasure 1)} (hf : IsWindowCarried f) :
    MemLp (fun x : ℝ => (x : ℂ) * f x) 2 (expMeasure 1) := by
  obtain ⟨R, hR⟩ := hf
  refine ((Lp.memLp f).const_mul ((max R 0 : ℝ) : ℂ)).of_le
    ((Complex.continuous_ofReal.aestronglyMeasurable).mul (Lp.aestronglyMeasurable f)) ?_
  filter_upwards [hR, ae_pos_expMeasure_one] with x hx hpos
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (le_max_right R 0)]
  by_cases hxR : R < x
  · rw [hx hxR, norm_zero, mul_zero, mul_zero]
  · exact mul_le_mul_of_nonneg_right ((not_lt.mp hxR).trans (le_max_left R 0)) (norm_nonneg _)

/-- The coordinate multiplication `X f = x f(x)` on the core. -/
def coordMul (f : Lp ℂ 2 (expMeasure 1)) (hf : IsWindowCarried f) : Lp ℂ 2 (expMeasure 1) :=
  (memLp_coordMul hf).toLp _

theorem coordMul_ae (f : Lp ℂ 2 (expMeasure 1)) (hf : IsWindowCarried f) :
    (coordMul f hf : ℝ → ℂ) =ᵐ[expMeasure 1] fun x : ℝ => (x : ℂ) * f x :=
  (memLp_coordMul hf).coeFn_toLp

/-- The core is stable under `X`. -/
theorem isWindowCarried_coordMul (f : Lp ℂ 2 (expMeasure 1)) (hf : IsWindowCarried f) :
    IsWindowCarried (coordMul f hf) := by
  obtain ⟨R, hR⟩ := hf
  refine ⟨R, ?_⟩
  filter_upwards [hR, coordMul_ae f ⟨R, hR⟩] with x hx hc hxR
  rw [hc, hx hxR, mul_zero]

/-- **The commutator recursion.**  On the core, `K_{n+1} f = X K_n f - K_n X f`. -/
theorem jetKernel_succ_op_ae (n : ℕ) (f : Lp ℂ 2 (expMeasure 1)) (hf : IsWindowCarried f) :
    ((jetKernel (n + 1)).op f : ℝ → ℂ) =ᵐ[expMeasure 1]
      fun x => (x : ℂ) * ((jetKernel n).op f : ℝ → ℂ) x
        - ((jetKernel n).op (coordMul f hf) : ℝ → ℂ) x := by
  filter_upwards [(jetKernel (n + 1)).op_coeFn f, (jetKernel n).op_coeFn f,
    (jetKernel n).op_coeFn (coordMul f hf), (jetKernel n).ae_integrable f,
    (jetKernel n).ae_integrable (coordMul f hf)] with x h1 h2 h3 hi1 hi2
  rw [h1, h2, h3]
  change ∫ y, ((((x - y) ^ (n + 1) * wallCubicKernel x y : ℝ)) : ℂ) * f y ∂(expMeasure 1)
    = (x : ℂ) * ∫ y, ((((x - y) ^ n * wallCubicKernel x y : ℝ)) : ℂ) * f y ∂(expMeasure 1)
      - ∫ y, ((((x - y) ^ n * wallCubicKernel x y : ℝ)) : ℂ) * (coordMul f hf) y ∂(expMeasure 1)
  have hc : ∫ y, ((((x - y) ^ n * wallCubicKernel x y : ℝ)) : ℂ) * (coordMul f hf) y
      ∂(expMeasure 1)
      = ∫ y, ((((x - y) ^ n * wallCubicKernel x y : ℝ)) : ℂ) * ((y : ℂ) * f y)
        ∂(expMeasure 1) :=
    integral_congr_ae ((coordMul_ae f hf).mono fun y hy => by simp only [hy])
  have hi2' : Integrable (fun y => ((((x - y) ^ n * wallCubicKernel x y : ℝ)) : ℂ) *
      ((y : ℂ) * f y)) (expMeasure 1) :=
    hi2.congr ((coordMul_ae f hf).mono fun y hy => by simp only [hy]; rfl)
  have hi1' : Integrable (fun y => (x : ℂ) * ((((x - y) ^ n * wallCubicKernel x y : ℝ)) : ℂ) *
      f y) (expMeasure 1) := by
    have := hi1.const_mul (x : ℂ)
    refine this.congr (Eventually.of_forall fun y => ?_)
    simp only
    rw [← mul_assoc]
    rfl
  rw [hc, show (x : ℂ) * ∫ y, ((((x - y) ^ n * wallCubicKernel x y : ℝ)) : ℂ) * f y ∂(expMeasure 1)
      = ∫ y, (x : ℂ) * ((((x - y) ^ n * wallCubicKernel x y : ℝ)) : ℂ) * f y ∂(expMeasure 1) by
    rw [← integral_const_mul]; simp only [mul_assoc], ← integral_sub hi1' hi2']
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  push_cast
  ring

/-- Truncation to the window `[0, R]`. -/
def windowTruncation (f : Lp ℂ 2 (expMeasure 1)) (R : ℝ) : Lp ℂ 2 (expMeasure 1) :=
  ((Lp.memLp f).indicator measurableSet_Iic (s := Iic R)).toLp _

theorem windowTruncation_ae (f : Lp ℂ 2 (expMeasure 1)) (R : ℝ) :
    (windowTruncation f R : ℝ → ℂ) =ᵐ[expMeasure 1] (Iic R).indicator f :=
  ((Lp.memLp f).indicator measurableSet_Iic).coeFn_toLp

theorem isWindowCarried_windowTruncation (f : Lp ℂ 2 (expMeasure 1)) (R : ℝ) :
    IsWindowCarried (windowTruncation f R) :=
  ⟨R, (windowTruncation_ae f R).mono fun x hx hxR => by
    rw [hx, Set.indicator_of_notMem (show x ∉ Iic R from not_le.mpr hxR)]⟩

theorem tendsto_windowTruncation (f : Lp ℂ 2 (expMeasure 1)) :
    Tendsto (fun R : ℕ => windowTruncation f R) atTop (𝓝 f) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hae : ∀ R : ℕ, ((windowTruncation f R - f : Lp ℂ 2 (expMeasure 1)) : ℝ → ℂ)
      =ᵐ[expMeasure 1] fun x => -(Ioi (R : ℝ)).indicator (f : ℝ → ℂ) x := fun R => by
    filter_upwards [Lp.coeFn_sub (windowTruncation f R) f, windowTruncation_ae f R] with x h1 h2
    rw [h1, Pi.sub_apply, h2]
    by_cases hx : x ≤ R
    · rw [Set.indicator_of_mem (show x ∈ Iic (R : ℝ) from hx),
        Set.indicator_of_notMem (show x ∉ Ioi (R : ℝ) from not_lt.mpr hx), sub_self, neg_zero]
    · rw [Set.indicator_of_notMem (show x ∉ Iic (R : ℝ) from hx),
        Set.indicator_of_mem (show x ∈ Ioi (R : ℝ) from not_le.mp hx), zero_sub]
  have hg := SqIntKernel.lintegral_enorm_sq_lt_top f
  have hlint : Tendsto (fun R : ℕ => ∫⁻ x, ‖-(Ioi (R : ℝ)).indicator (f : ℝ → ℂ) x‖ₑ ^ 2
      ∂(expMeasure 1)) atTop (𝓝 0) := by
    have h := tendsto_lintegral_filter_of_dominated_convergence (l := (atTop : Filter ℕ))
      (μ := expMeasure 1) (f := fun _ => (0 : ℝ≥0∞))
      (F := fun (R : ℕ) x => ‖-(Ioi (R : ℝ)).indicator (f : ℝ → ℂ) x‖ₑ ^ 2)
      (fun x => ‖(f : ℝ → ℂ) x‖ₑ ^ 2)
      (Eventually.of_forall fun R =>
        (((Lp.stronglyMeasurable f).measurable.indicator measurableSet_Ioi).neg.enorm).pow_const 2)
      (Eventually.of_forall fun R => Eventually.of_forall fun x => by
        rw [enorm_neg]
        by_cases hx : x ∈ Ioi (R : ℝ)
        · rw [Set.indicator_of_mem hx]
        · rw [Set.indicator_of_notMem hx, enorm_zero]; simp)
      hg.ne
      (Eventually.of_forall fun x => by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop ⌈x⌉₊] with R hR
        have hxR : x ∉ Ioi (R : ℝ) := not_lt.mpr ((Nat.le_ceil x).trans (by exact_mod_cast hR))
        rw [Set.indicator_of_notMem hxR, neg_zero, enorm_zero]
        simp)
    simpa using h
  have hrpow := ((ENNReal.continuous_rpow_const (y := (1 : ℝ) / 2)).tendsto 0).comp hlint
  rw [ENNReal.zero_rpow_of_pos (by norm_num)] at hrpow
  have htoReal := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hrpow
  rw [ENNReal.toReal_zero] at htoReal
  refine htoReal.congr fun R => ?_
  simp only [Function.comp_apply]
  rw [Lp.norm_def, eLpNorm_congr_ae (hae R), SchurKernel.eLpNorm_two_eq]

/-- **Unique extension.**  A bounded operator agreeing with `K_n` on the core is `K_n`. -/
theorem eq_jetKernel_op_of_eqOn_core (n : ℕ) {T : Lp ℂ 2 (expMeasure 1) →L[ℂ] Lp ℂ 2 (expMeasure 1)}
    (hT : ∀ f, IsWindowCarried f → T f = (jetKernel n).op f) : T = (jetKernel n).op := by
  ext1 f
  have h1 := (T.continuous.tendsto f).comp (tendsto_windowTruncation f)
  have h2 := ((jetKernel n).op.continuous.tendsto f).comp (tendsto_windowTruncation f)
  refine tendsto_nhds_unique h1 (h2.congr fun R => ?_)
  simp only [Function.comp_apply]
  exact (hT _ (isWindowCarried_windowTruncation f R)).symm

end GaloisForLFunctions.HTGeometry
