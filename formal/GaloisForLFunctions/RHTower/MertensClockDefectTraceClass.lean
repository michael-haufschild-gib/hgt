import GaloisForLFunctions.RHTower.PoissonPrimeKernelCalkinModel
import GaloisForLFunctions.HTGeometry.SchurKernelComposition
import GaloisForLFunctions.RHTower.TraceNormBound
import GaloisForLFunctions.RHTower.TraceClassOperatorTrace

/-!
# The Mertens-clock defect is trace class with zero trace

Let `ψ` be the Mertens step clock on the half-line, `|ψ(y) - y| ≤ D e^{-y}`, and let `g` be a
`C²` profile whose first two derivatives are bounded by `M e^{-α|s|}`.  The clock defect kernel

`e(y,z) = g(ψ(y) - ψ(z)) - g(y - z)`

splits as `e = e₂ + e₃ + r`, where

`e₂(y,z) = ∫_y^{ψ y} g'(a - z) da`,  `e₃(y,z) = -∫_z^{ψ z} g'(y - b) db`,
`r(y,z) = -∫_y^{ψ y} ∫_z^{ψ z} g''(a - b) db da`.

Write `R(a, y)` for the oriented indicator of the displacement interval `(y, ψ y]`, shifted by `D`
to the half-line.  It is square integrable, because `∫ |ψ(y) - y| dy < ∞`, and it stays square
integrable after the weight `e^{εa}` with `ε ≤ 1/4`.  Consequently

`T₂ = R_ε† ∘ W_ε[g']`,  `T₃ = W_ε[g'(-·)]† ∘ R_ε`,  `T₅ = R† ∘ (C[-g''] ∘ R)`

are products of two Hilbert–Schmidt operators, where `W_ε[F](a,z) = e^{-εa} F(a - z)` and
`C[F](a,b) = F(a - b)`.  The defect operator is their sum: it is trace class, and its trace is
`∫ e(y,y) dy = 0`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal ComplexConjugate Interval

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section
set_option autoImplicit false

local notation "L²₊" => Lp ℂ 2 halfLineMeasure

/-! ### Half-line exponential integrals -/

theorem lintegral_Ici_ofReal_exp_neg_lt_top {c : ℝ} (hc : 0 < c) :
    ∫⁻ t in Ici (0 : ℝ), ENNReal.ofReal (Real.exp (-(c * t))) < ∞ := by
  have h : IntegrableOn (fun t : ℝ => Real.exp (-c * t)) (Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi (by simp)).mpr (exp_neg_integrableOn_Ioi 0 hc)
  have h2 : IntegrableOn (fun t : ℝ => Real.exp (-(c * t))) (Ici 0) := by simpa [neg_mul] using h
  exact h2.lintegral_lt_top

theorem lintegral_ofReal_exp_neg_abs_sub_le {β : ℝ} (hβ : 0 < β) (c : ℝ) :
    ∫⁻ a, ENNReal.ofReal (Real.exp (-(β * |c - a|))) = ENNReal.ofReal (2 / β) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_exp_neg_mul_abs_sub hβ c)
    (Eventually.of_forall fun a => (Real.exp_pos _).le), integral_exp_neg_mul_abs_sub hβ]

/-! ### The clock displacement -/

theorem poissonClock_of_neg {y : ℝ} (hy : y < 0) : poissonClock y = y := by
  rw [poissonClock, if_neg (not_le.mpr hy)]

theorem neg_poissonClockConst_le_min {y : ℝ} (hy : 0 ≤ y) :
    -poissonClockConst ≤ min y (poissonClock y) := by
  have h := abs_poissonClock_sub_le hy
  have he : Real.exp (-y) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hD := poissonClockConst_nonneg
  have h2 : poissonClockConst * Real.exp (-y) ≤ poissonClockConst := by
    nlinarith [Real.exp_pos (-y)]
  have h3 := (abs_le.mp (h.trans h2)).1
  exact le_min (by linarith) (by linarith)

theorem abs_sub_le_of_mem_uIoc {y b a : ℝ} (h : a ∈ Ι y b) : |a - y| ≤ |b - y| := by
  rw [Set.mem_uIoc] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]; linarith
  · rw [abs_of_nonpos (by linarith), abs_of_neg (by linarith)]; linarith

/-! ### The oriented displacement indicator -/

/-- The oriented indicator of the clock displacement interval: `1` on `(y, ψ y]` and `-1` on
`(ψ y, y]`, so that `∫ clockOrient y a · G(a) da = ∫_y^{ψ y} G`. -/
def clockOrient (y a : ℝ) : ℝ :=
  (Ioc y (poissonClock y)).indicator 1 a - (Ioc (poissonClock y) y).indicator 1 a

theorem measurable_clockOrient : Measurable (Function.uncurry clockOrient) := by
  have hψ := measurable_poissonClock
  have h1 : MeasurableSet {p : ℝ × ℝ | p.1 < p.2 ∧ p.2 ≤ poissonClock p.1} :=
    (measurableSet_lt measurable_fst measurable_snd).inter
      (measurableSet_le measurable_snd (hψ.comp measurable_fst))
  have h2 : MeasurableSet {p : ℝ × ℝ | poissonClock p.1 < p.2 ∧ p.2 ≤ p.1} :=
    (measurableSet_lt (hψ.comp measurable_fst) measurable_snd).inter
      (measurableSet_le measurable_snd measurable_fst)
  have e : Function.uncurry clockOrient = fun p =>
      {p : ℝ × ℝ | p.1 < p.2 ∧ p.2 ≤ poissonClock p.1}.indicator 1 p -
        {p : ℝ × ℝ | poissonClock p.1 < p.2 ∧ p.2 ≤ p.1}.indicator 1 p := by
    funext p
    simp only [Function.uncurry, clockOrient, Set.indicator, Set.mem_Ioc, Set.mem_setOf_eq,
      Pi.one_apply]
  rw [e]
  exact (measurable_one.indicator h1).sub (measurable_one.indicator h2)

theorem clockOrient_eq_zero_of_notMem {y a : ℝ} (h : a ∉ Ι y (poissonClock y)) :
    clockOrient y a = 0 := by
  rw [Set.mem_uIoc, not_or] at h
  have h1 : a ∉ Ioc y (poissonClock y) := fun ha => h.1 ⟨ha.1, ha.2⟩
  have h2 : a ∉ Ioc (poissonClock y) y := fun ha => h.2 ⟨ha.1, ha.2⟩
  simp [clockOrient, h1, h2]

theorem abs_clockOrient_le (y a : ℝ) : |clockOrient y a| ≤ 1 := by
  by_cases h1 : a ∈ Ioc y (poissonClock y)
  · have h2 : a ∉ Ioc (poissonClock y) y := fun h2 => by linarith [h1.1, h2.2]
    simp [clockOrient, h1, h2]
  · by_cases h2 : a ∈ Ioc (poissonClock y) y <;> simp [clockOrient, h1, h2]

theorem clockOrient_of_neg {y : ℝ} (hy : y < 0) (a : ℝ) : clockOrient y a = 0 := by
  refine clockOrient_eq_zero_of_notMem ?_
  rw [poissonClock_of_neg hy, Set.mem_uIoc]
  rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> linarith

theorem clockOrient_eq_zero_of_le {y a : ℝ} (hy : 0 ≤ y) (ha : a ≤ -poissonClockConst) :
    clockOrient y a = 0 := by
  refine clockOrient_eq_zero_of_notMem fun hmem => ?_
  have hmin := neg_poissonClockConst_le_min hy
  rw [Set.mem_uIoc] at hmem
  rcases hmem with ⟨h1, _⟩ | ⟨h1, _⟩
  · have := min_le_left y (poissonClock y); linarith
  · have := min_le_right y (poissonClock y); linarith

theorem enorm_clockOrient_le (y a : ℝ) :
    ‖(clockOrient y a : ℂ)‖ₑ ≤ (Ι y (poissonClock y)).indicator (fun _ => (1 : ℝ≥0∞)) a := by
  by_cases h : a ∈ Ι y (poissonClock y)
  · rw [Set.indicator_of_mem h, ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs]
    exact ENNReal.ofReal_le_one.mpr (abs_clockOrient_le y a)
  · rw [Set.indicator_of_notMem h, clockOrient_eq_zero_of_notMem h]
    simp

/-- `∫ clockOrient y a · G(a) da = ∫_y^{ψ y} G`. -/
theorem integral_clockOrient_mul (y : ℝ) {G : ℝ → ℂ} (hG : Continuous G) :
    ∫ a, (clockOrient y a : ℂ) * G a = ∫ a in y..poissonClock y, G a := by
  have e : (fun a => (clockOrient y a : ℂ) * G a) = fun a =>
      (Ioc y (poissonClock y)).indicator G a - (Ioc (poissonClock y) y).indicator G a := by
    funext a
    by_cases h1 : a ∈ Ioc y (poissonClock y)
    · have h2 : a ∉ Ioc (poissonClock y) y := fun h2 => by linarith [h1.1, h2.2]
      simp [clockOrient, h1, h2]
    · by_cases h2 : a ∈ Ioc (poissonClock y) y <;> simp [clockOrient, h1, h2]
  rw [e, integral_sub (hG.integrableOn_Ioc.integrable_indicator measurableSet_Ioc)
      (hG.integrableOn_Ioc.integrable_indicator measurableSet_Ioc),
    integral_indicator measurableSet_Ioc, integral_indicator measurableSet_Ioc]
  rfl

/-- The shifted version on the half-line: for `y ≥ 0` the displacement interval lies in
`(-D, ∞)`, so the shift by `D` places it in `(0, ∞)`. -/
theorem integral_halfLine_clockOrient {y : ℝ} (hy : 0 ≤ y) {G : ℝ → ℂ} (hG : Continuous G) :
    ∫ a', (clockOrient y (a' - poissonClockConst) : ℂ) * G (a' - poissonClockConst)
        ∂halfLineMeasure = ∫ a in y..poissonClock y, G a := by
  show ∫ a' in Ici (0 : ℝ), _ = _
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero,
    integral_sub_right_eq_self (fun a => (clockOrient y a : ℂ) * G a) poissonClockConst]
  · exact integral_clockOrient_mul y hG
  · intro a' ha'
    have ha'0 : a' < 0 := not_le.mp ha'
    rw [clockOrient_eq_zero_of_le hy (by linarith), Complex.ofReal_zero, zero_mul]

/-! ### The unweighted displacement kernel `R` -/

theorem enorm_clockOrient_le_Icc (y a : ℝ) :
    ‖(clockOrient y a : ℂ)‖ₑ ≤
      (Icc (a - poissonClockConst) (a + poissonClockConst)).indicator (fun _ => (1 : ℝ≥0∞)) y := by
  by_cases h : a ∈ Ι y (poissonClock y)
  · have h1 := (abs_sub_le_of_mem_uIoc h).trans (abs_poissonClock_sub_le_const y)
    have hmem : y ∈ Icc (a - poissonClockConst) (a + poissonClockConst) := by
      rw [abs_le] at h1; constructor <;> linarith [h1.1, h1.2]
    rw [Set.indicator_of_mem hmem, ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs]
    exact ENNReal.ofReal_le_one.mpr (abs_clockOrient_le y a)
  · rw [clockOrient_eq_zero_of_notMem h]
    simp

theorem lintegral_enorm_clockOrient_shift (y : ℝ) :
    ∫⁻ a', ‖(clockOrient y (a' - poissonClockConst) : ℂ)‖ₑ ≤
      ENNReal.ofReal |poissonClock y - y| := by
  refine (lintegral_mono fun a' => enorm_clockOrient_le y (a' - poissonClockConst)).trans
    (le_of_eq ?_)
  rw [lintegral_sub_right_eq_self (fun a => (Ι y (poissonClock y)).indicator
      (fun _ => (1 : ℝ≥0∞)) a),
    lintegral_indicator_const measurableSet_uIoc, one_mul, Real.volume_uIoc]

/-- The shifted oriented displacement kernel `R(a', y) = clockOrient y (a' - D)`. -/
def clockOrientKernel : SchurKernel halfLineMeasure where
  toFun a' y := (clockOrient y (a' - poissonClockConst) : ℂ)
  measurable := Complex.measurable_ofReal.comp
    (measurable_clockOrient.comp (measurable_snd.prodMk (measurable_fst.sub_const _)))
  bound := Real.toNNReal (2 * poissonClockConst)
  row a' := by
    refine (setLIntegral_le_lintegral _ _).trans ?_
    refine (lintegral_mono fun y => enorm_clockOrient_le_Icc y _).trans (le_of_eq ?_)
    rw [lintegral_indicator_const measurableSet_Icc, one_mul, Real.volume_Icc]
    exact congrArg ENNReal.ofReal (by ring)
  col y := by
    refine (setLIntegral_le_lintegral _ _).trans ((lintegral_enorm_clockOrient_shift y).trans ?_)
    refine ENNReal.ofReal_le_ofReal ?_
    have := abs_poissonClock_sub_le_const y
    have := poissonClockConst_nonneg
    linarith

theorem clockOrientKernel_toFun (a' y : ℝ) :
    clockOrientKernel.toFun a' y = (clockOrient y (a' - poissonClockConst) : ℂ) := rfl

/-- `∬ |R|² ≤ ∫_0^∞ D e^{-y} dy < ∞`. -/
theorem lintegral_clockOrientKernel_sq_lt_top :
    ∫⁻ a', ∫⁻ y, ‖clockOrientKernel.toFun a' y‖ₑ ^ 2 ∂halfLineMeasure ∂halfLineMeasure < ∞ := by
  rw [lintegral_lintegral_swap ((clockOrientKernel.measurable_enorm.pow_const 2).aemeasurable)]
  have hpt : ∀ y ∈ Ici (0 : ℝ), ∫⁻ a', ‖clockOrientKernel.toFun a' y‖ₑ ^ 2 ∂halfLineMeasure ≤
      ENNReal.ofReal (poissonClockConst * Real.exp (-(1 * y))) := by
    intro y hy
    refine (setLIntegral_le_lintegral _ _).trans ?_
    have hsq : ∀ a', ‖clockOrientKernel.toFun a' y‖ₑ ^ 2 ≤
        ‖(clockOrient y (a' - poissonClockConst) : ℂ)‖ₑ := by
      intro a'
      rw [clockOrientKernel_toFun, ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
        ← ENNReal.ofReal_pow (abs_nonneg _)]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 := abs_clockOrient_le y (a' - poissonClockConst)
      nlinarith [abs_nonneg (clockOrient y (a' - poissonClockConst))]
    refine (lintegral_mono hsq).trans ((lintegral_enorm_clockOrient_shift y).trans ?_)
    rw [one_mul]
    exact ENNReal.ofReal_le_ofReal (abs_poissonClock_sub_le hy)
  refine lt_of_le_of_lt (setLIntegral_mono' measurableSet_Ici hpt) ?_
  have h := lintegral_Ici_ofReal_exp_neg_lt_top (c := 1) one_pos
  have e : ∀ y, ENNReal.ofReal (poissonClockConst * Real.exp (-(1 * y))) =
      ENNReal.ofReal poissonClockConst * ENNReal.ofReal (Real.exp (-(1 * y))) := fun y =>
    ENNReal.ofReal_mul poissonClockConst_nonneg
  simp_rw [e]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top h

/-! ### The weighted displacement kernel `R_ε` -/

section Weighted

variable {ε : ℝ}

/-- Row estimate: for `y ≥ 0`, `a ∈ (y, ψ y]` forces `|a - y| ≤ D e^{D - a}`. -/
theorem abs_sub_le_of_clockOrient_ne_zero {y a : ℝ} (hy : 0 ≤ y) (h : clockOrient y a ≠ 0) :
    |a - y| ≤ poissonClockConst * Real.exp (poissonClockConst - a) := by
  have hmem : a ∈ Ι y (poissonClock y) := by
    by_contra hn; exact h (clockOrient_eq_zero_of_notMem hn)
  have h1 := abs_sub_le_of_mem_uIoc hmem
  have h2 := h1.trans (abs_poissonClock_sub_le hy)
  have h3 := h1.trans (abs_poissonClock_sub_le_const y)
  have hya : a - poissonClockConst ≤ y := by rw [abs_le] at h3; linarith [h3.2]
  have hexp : Real.exp (-y) ≤ Real.exp (poissonClockConst - a) :=
    Real.exp_le_exp.mpr (by linarith)
  exact h2.trans (mul_le_mul_of_nonneg_left hexp poissonClockConst_nonneg)

theorem enorm_weight_clockOrient_le {y a : ℝ} (hε0 : 0 ≤ ε) :
    ‖((Real.exp (ε * a) * clockOrient y a : ℝ) : ℂ)‖ₑ ≤
      ENNReal.ofReal (Real.exp (ε * (y + poissonClockConst))) * ‖(clockOrient y a : ℂ)‖ₑ := by
  by_cases h0 : clockOrient y a = 0
  · rw [h0]; simp
  · have hmem : a ∈ Ι y (poissonClock y) := by
      by_contra hn; exact h0 (clockOrient_eq_zero_of_notMem hn)
    have h1 := (abs_sub_le_of_mem_uIoc hmem).trans (abs_poissonClock_sub_le_const y)
    have hay : a ≤ y + poissonClockConst := by rw [abs_le] at h1; linarith [h1.2]
    rw [← ofReal_norm, ← ofReal_norm, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _),
      ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hay hε0)) (abs_nonneg _))

/-- The weighted displacement kernel `R_ε(a', y) = e^{ε(a' - D)} clockOrient y (a' - D)`. -/
def clockOrientWeightKernel (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    SchurKernel halfLineMeasure where
  toFun a' y := ((Real.exp (ε * (a' - poissonClockConst)) *
    clockOrient y (a' - poissonClockConst) : ℝ) : ℂ)
  measurable := Complex.measurable_ofReal.comp
    ((Real.measurable_exp.comp ((measurable_fst.sub_const _).const_mul ε)).mul
      (measurable_clockOrient.comp (measurable_snd.prodMk (measurable_fst.sub_const _))))
  bound := Real.toNNReal (2 * poissonClockConst * Real.exp (2 * poissonClockConst))
  row a' := by
    set D := poissonClockConst with hD
    have hD0 : 0 ≤ D := poissonClockConst_nonneg
    set a := a' - D with ha
    by_cases hneg : a ≤ -D
    · have hzero : ∀ y ∈ Ici (0 : ℝ),
          ‖((Real.exp (ε * a) * clockOrient y a : ℝ) : ℂ)‖ₑ = 0 := by
        intro y hy
        rw [clockOrient_eq_zero_of_le hy hneg, mul_zero, Complex.ofReal_zero, enorm_zero]
      refine le_of_eq_of_le (setLIntegral_congr_fun measurableSet_Ici hzero) ?_
      simp
    · push Not at hneg
      set r := D * Real.exp (D - a) with hr
      have hpt : ∀ y ∈ Ici (0 : ℝ), ‖((Real.exp (ε * a) * clockOrient y a : ℝ) : ℂ)‖ₑ ≤
          (Icc (a - r) (a + r)).indicator (fun _ => ENNReal.ofReal (Real.exp (ε * a))) y := by
        intro y hy
        by_cases h0 : clockOrient y a = 0
        · rw [h0, mul_zero, Complex.ofReal_zero, enorm_zero]; exact bot_le
        · have h1 := abs_sub_le_of_clockOrient_ne_zero hy h0
          have hmem : y ∈ Icc (a - r) (a + r) := by
            rw [abs_le] at h1; constructor <;> linarith [h1.1, h1.2]
          rw [Set.indicator_of_mem hmem, ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
            abs_mul, abs_of_pos (Real.exp_pos _)]
          refine ENNReal.ofReal_le_ofReal ?_
          have := abs_clockOrient_le y a
          nlinarith [Real.exp_pos (ε * a)]
      refine (setLIntegral_mono' measurableSet_Ici hpt).trans ?_
      refine (setLIntegral_le_lintegral _ _).trans ?_
      rw [lintegral_indicator_const measurableSet_Icc, Real.volume_Icc,
        ← ENNReal.ofReal_mul (Real.exp_pos _).le]
      refine ENNReal.ofReal_le_ofReal ?_
      have hexp : Real.exp (ε * a) * Real.exp (D - a) ≤ Real.exp (2 * D) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr (by nlinarith)
      calc Real.exp (ε * a) * (a + r - (a - r)) =
            2 * D * (Real.exp (ε * a) * Real.exp (D - a)) := by rw [hr]; ring
        _ ≤ 2 * D * Real.exp (2 * D) := mul_le_mul_of_nonneg_left hexp (by positivity)
  col y := by
    refine (setLIntegral_le_lintegral _ _).trans ?_
    by_cases hy : y < 0
    · simp only [clockOrient_of_neg hy, mul_zero, Complex.ofReal_zero, enorm_zero, lintegral_zero]
      exact bot_le
    · push Not at hy
      refine (lintegral_mono fun a' => enorm_weight_clockOrient_le hε0).trans ?_
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      calc ENNReal.ofReal (Real.exp (ε * (y + poissonClockConst))) *
            ∫⁻ a', ‖(clockOrient y (a' - poissonClockConst) : ℂ)‖ₑ
          ≤ ENNReal.ofReal (Real.exp (ε * (y + poissonClockConst))) *
              ENNReal.ofReal |poissonClock y - y| := by
            gcongr; exact lintegral_enorm_clockOrient_shift y
        _ ≤ _ := by
            rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
            refine ENNReal.ofReal_le_ofReal ?_
            have h1 := abs_poissonClock_sub_le hy
            have hD0 := poissonClockConst_nonneg
            have hexp : Real.exp (ε * (y + poissonClockConst)) * Real.exp (-y) ≤
                Real.exp (2 * poissonClockConst) := by
              rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by nlinarith)
            calc Real.exp (ε * (y + poissonClockConst)) * |poissonClock y - y|
                ≤ Real.exp (ε * (y + poissonClockConst)) * (poissonClockConst * Real.exp (-y)) :=
                  mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
              _ = poissonClockConst * (Real.exp (ε * (y + poissonClockConst)) * Real.exp (-y)) := by
                  ring
              _ ≤ poissonClockConst * Real.exp (2 * poissonClockConst) :=
                  mul_le_mul_of_nonneg_left hexp hD0
              _ ≤ 2 * poissonClockConst * Real.exp (2 * poissonClockConst) := by
                  nlinarith [Real.exp_pos (2 * poissonClockConst)]

theorem clockOrientWeightKernel_toFun (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (a' y : ℝ) :
    (clockOrientWeightKernel ε hε0 hε1).toFun a' y =
      ((Real.exp (ε * (a' - poissonClockConst)) * clockOrient y (a' - poissonClockConst) : ℝ) :
        ℂ) := rfl

/-- `∬ |R_ε|² ≤ D e^{2εD} ∫_0^∞ e^{-(1-2ε) y} dy < ∞`. -/
theorem lintegral_clockOrientWeightKernel_sq_lt_top (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 4) :
    ∫⁻ a', ∫⁻ y, ‖(clockOrientWeightKernel ε hε0 (by linarith)).toFun a' y‖ₑ ^ 2
      ∂halfLineMeasure ∂halfLineMeasure < ∞ := by
  set k := clockOrientWeightKernel ε hε0 (by linarith)
  set D := poissonClockConst with hD
  have hD0 : 0 ≤ D := poissonClockConst_nonneg
  rw [lintegral_lintegral_swap ((k.measurable_enorm.pow_const 2).aemeasurable)]
  have hpt : ∀ y ∈ Ici (0 : ℝ), ∫⁻ a', ‖k.toFun a' y‖ₑ ^ 2 ∂halfLineMeasure ≤
      ENNReal.ofReal (D * Real.exp (2 * ε * D)) *
        ENNReal.ofReal (Real.exp (-((1 - 2 * ε) * y))) := by
    intro y hy
    refine (setLIntegral_le_lintegral _ _).trans ?_
    have hsq : ∀ a', ‖k.toFun a' y‖ₑ ^ 2 ≤
        ENNReal.ofReal (Real.exp (2 * ε * (y + D))) * ‖(clockOrient y (a' - D) : ℂ)‖ₑ := by
      intro a'
      have h1 : ‖k.toFun a' y‖ₑ ≤ ENNReal.ofReal (Real.exp (ε * (y + D))) *
          ‖(clockOrient y (a' - D) : ℂ)‖ₑ := enorm_weight_clockOrient_le hε0
      have h2 : ‖(clockOrient y (a' - D) : ℂ)‖ₑ ≤ 1 := by
        rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs]
        exact ENNReal.ofReal_le_one.mpr (abs_clockOrient_le _ _)
      calc ‖k.toFun a' y‖ₑ ^ 2 ≤ (ENNReal.ofReal (Real.exp (ε * (y + D))) *
            ‖(clockOrient y (a' - D) : ℂ)‖ₑ) ^ 2 := by gcongr
        _ = ENNReal.ofReal (Real.exp (ε * (y + D))) ^ 2 *
            (‖(clockOrient y (a' - D) : ℂ)‖ₑ * ‖(clockOrient y (a' - D) : ℂ)‖ₑ) := by ring
        _ ≤ ENNReal.ofReal (Real.exp (ε * (y + D))) ^ 2 *
            (1 * ‖(clockOrient y (a' - D) : ℂ)‖ₑ) := by gcongr
        _ = ENNReal.ofReal (Real.exp (2 * ε * (y + D))) * ‖(clockOrient y (a' - D) : ℂ)‖ₑ := by
            rw [one_mul, ← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul]
            congr 3
            push_cast; ring
    refine (lintegral_mono hsq).trans ?_
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc ENNReal.ofReal (Real.exp (2 * ε * (y + D))) * ∫⁻ a', ‖(clockOrient y (a' - D) : ℂ)‖ₑ
        ≤ ENNReal.ofReal (Real.exp (2 * ε * (y + D))) * ENNReal.ofReal |poissonClock y - y| := by
          gcongr; exact lintegral_enorm_clockOrient_shift y
      _ ≤ _ := by
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,
            ← ENNReal.ofReal_mul (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          have h1 := abs_poissonClock_sub_le hy
          have e : Real.exp (2 * ε * (y + D)) * (D * Real.exp (-y)) =
              D * Real.exp (2 * ε * D) * Real.exp (-((1 - 2 * ε) * y)) := by
            rw [mul_left_comm, mul_assoc, ← Real.exp_add, mul_assoc, ← Real.exp_add]
            congr 2; ring
          rw [← e]
          exact mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
  refine lt_of_le_of_lt (setLIntegral_mono' measurableSet_Ici hpt) ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (lintegral_Ici_ofReal_exp_neg_lt_top (by linarith))

end Weighted

/-! ### Translation kernels -/

theorem lintegral_enorm_translate_le {F : ℝ → ℝ} {M α : ℝ} (hM : 0 ≤ M) (hα : 0 < α)
    (hFb : ∀ s, |F s| ≤ M * Real.exp (-(α * |s|))) (c : ℝ) :
    ∫⁻ z, ‖((F (c - z) : ℝ) : ℂ)‖ₑ ≤ ENNReal.ofReal (M * (2 / α)) := by
  have h := lintegral_enorm_clock_kernel_le (φ := id) (D := 0) hM hα hFb (fun y => by simp) c
  simpa using h

theorem lintegral_enorm_translate_le' {F : ℝ → ℝ} {M α : ℝ} (hM : 0 ≤ M) (hα : 0 < α)
    (hFb : ∀ s, |F s| ≤ M * Real.exp (-(α * |s|))) (c : ℝ) :
    ∫⁻ y, ‖((F (y - c) : ℝ) : ℂ)‖ₑ ≤ ENNReal.ofReal (M * (2 / α)) := by
  have h := lintegral_enorm_clock_kernel_le' (φ := id) (D := 0) hM hα hFb (fun y => by simp) c
  simpa using h

/-- The half-line weight `e^{-ε(a' - D)}` on `a' ≥ 0`, zero on `a' < 0`. -/
def clockDecayWeight (ε a' : ℝ) : ℝ :=
  (Ici (0 : ℝ)).indicator (fun a' => Real.exp (-(ε * (a' - poissonClockConst)))) a'

theorem clockDecayWeight_nonneg (ε a' : ℝ) : 0 ≤ clockDecayWeight ε a' :=
  Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) a'

theorem clockDecayWeight_le {ε : ℝ} (hε : 0 ≤ ε) (a' : ℝ) :
    clockDecayWeight ε a' ≤ Real.exp (ε * poissonClockConst) := by
  by_cases ha : a' ∈ Ici (0 : ℝ)
  · rw [clockDecayWeight, Set.indicator_of_mem ha]
    exact Real.exp_le_exp.mpr (by have : (0 : ℝ) ≤ a' := ha; nlinarith)
  · rw [clockDecayWeight, Set.indicator_of_notMem ha]; exact (Real.exp_pos _).le

theorem clockDecayWeight_of_nonneg (ε : ℝ) {a' : ℝ} (ha : 0 ≤ a') :
    clockDecayWeight ε a' = Real.exp (-(ε * (a' - poissonClockConst))) := by
  rw [clockDecayWeight, Set.indicator_of_mem (show a' ∈ Ici (0 : ℝ) from ha)]

theorem measurable_clockDecayWeight (ε : ℝ) : Measurable (clockDecayWeight ε) :=
  (Real.measurable_exp.comp ((measurable_id.sub_const _).const_mul ε).neg).indicator
    measurableSet_Ici

section DecayConv

variable {ε : ℝ} {F : ℝ → ℝ} {M α : ℝ}

/-- The weighted translation kernel `W_ε[F](a', z) = e^{-ε(a' - D)} F(a' - D - z)`. -/
def clockDecayConvKernel (ε : ℝ) (hε : 0 ≤ ε) (F : ℝ → ℝ) (hF : Continuous F) (hM : 0 ≤ M)
    (hα : 0 < α) (hFb : ∀ s, |F s| ≤ M * Real.exp (-(α * |s|))) : SchurKernel halfLineMeasure where
  toFun a' z := ((clockDecayWeight ε a' * F (a' - poissonClockConst - z) : ℝ) : ℂ)
  measurable := Complex.measurable_ofReal.comp
    (((measurable_clockDecayWeight ε).comp measurable_fst).mul
      (hF.measurable.comp ((measurable_fst.sub_const _).sub measurable_snd)))
  bound := Real.toNNReal (Real.exp (ε * poissonClockConst) * (M * (2 / α)))
  row a' := by
    refine (setLIntegral_le_lintegral _ _).trans ?_
    have hpt : ∀ z, ‖((clockDecayWeight ε a' * F (a' - poissonClockConst - z) : ℝ) : ℂ)‖ₑ =
        ENNReal.ofReal (clockDecayWeight ε a') * ‖((F (a' - poissonClockConst - z) : ℝ) : ℂ)‖ₑ := by
      intro z
      rw [Complex.ofReal_mul, enorm_mul, ← ofReal_norm (Complex.ofReal _), Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (clockDecayWeight_nonneg ε a')]
    simp_rw [hpt]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc ENNReal.ofReal (clockDecayWeight ε a') *
          ∫⁻ z, ‖((F (a' - poissonClockConst - z) : ℝ) : ℂ)‖ₑ
        ≤ ENNReal.ofReal (Real.exp (ε * poissonClockConst)) * ENNReal.ofReal (M * (2 / α)) := by
          gcongr
          · exact clockDecayWeight_le hε a'
          · exact lintegral_enorm_translate_le hM hα hFb _
      _ = _ := (ENNReal.ofReal_mul (Real.exp_pos _).le).symm
  col z := by
    refine (setLIntegral_le_lintegral _ _).trans ?_
    have hpt : ∀ a', ‖((clockDecayWeight ε a' * F (a' - poissonClockConst - z) : ℝ) : ℂ)‖ₑ ≤
        ENNReal.ofReal (Real.exp (ε * poissonClockConst)) *
          ‖((F (a' - (poissonClockConst + z)) : ℝ) : ℂ)‖ₑ := by
      intro a'
      rw [show a' - poissonClockConst - z = a' - (poissonClockConst + z) by ring,
        Complex.ofReal_mul, enorm_mul, ← ofReal_norm (Complex.ofReal (clockDecayWeight ε a')),
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (clockDecayWeight_nonneg ε a')]
      gcongr
      exact clockDecayWeight_le hε a'
    refine (lintegral_mono hpt).trans ?_
    show _ ≤ ENNReal.ofReal (Real.exp (ε * poissonClockConst) * (M * (2 / α)))
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ENNReal.ofReal_mul (Real.exp_pos _).le]
    gcongr
    exact lintegral_enorm_translate_le' hM hα hFb _

theorem clockDecayConvKernel_toFun (hε : 0 ≤ ε) (hF : Continuous F) (hM : 0 ≤ M) (hα : 0 < α)
    (hFb : ∀ s, |F s| ≤ M * Real.exp (-(α * |s|))) (a' z : ℝ) :
    (clockDecayConvKernel ε hε F hF hM hα hFb).toFun a' z =
      ((clockDecayWeight ε a' * F (a' - poissonClockConst - z) : ℝ) : ℂ) := rfl

/-- `|W_ε[F]|² ≤ M² e^{εD} e^{-εa'} e^{-εz}` on the quadrant, once `2ε ≤ α`. -/
theorem lintegral_clockDecayConvKernel_sq_lt_top (hε : 0 < ε) (hF : Continuous F) (hM : 0 ≤ M)
    (hα : 0 < α) (hεα : 2 * ε ≤ α) (hFb : ∀ s, |F s| ≤ M * Real.exp (-(α * |s|))) :
    ∫⁻ a', ∫⁻ z, ‖(clockDecayConvKernel ε hε.le F hF hM hα hFb).toFun a' z‖ₑ ^ 2
      ∂halfLineMeasure ∂halfLineMeasure < ∞ := by
  set D := poissonClockConst with hD
  have hpt : ∀ a' ∈ Ici (0 : ℝ), ∀ z,
      ‖(clockDecayConvKernel ε hε.le F hF hM hα hFb).toFun a' z‖ₑ ^ 2 ≤
        ENNReal.ofReal (M ^ 2 * Real.exp (ε * D) * Real.exp (-(ε * a'))) *
          ENNReal.ofReal (Real.exp (-(ε * z))) := by
    intro a' ha' z
    have ha0 : (0 : ℝ) ≤ a' := ha'
    rw [clockDecayConvKernel_toFun, clockDecayWeight_of_nonneg ε ha0, ← ofReal_norm,
      Complex.norm_real, Real.norm_eq_abs, ← ENNReal.ofReal_pow (abs_nonneg _),
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hFz := hFb (a' - D - z)
    have habs : |Real.exp (-(ε * (a' - D))) * F (a' - D - z)| ≤
        Real.exp (-(ε * (a' - D))) * (M * Real.exp (-(α * |a' - D - z|))) := by
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left hFz (Real.exp_pos _).le
    have hsq := pow_le_pow_left₀ (abs_nonneg _) habs 2
    set t := a' - D with ht
    set u := |a' - D - z| with hu
    have e1 : Real.exp (-(2 * ε * t) - 2 * α * u) =
        Real.exp (-(ε * t)) ^ 2 * Real.exp (-(α * u)) ^ 2 := by
      rw [sq, sq, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have e2 : M ^ 2 * Real.exp (ε * D) * Real.exp (-(ε * a')) * Real.exp (-(ε * z)) =
        M ^ 2 * Real.exp (ε * D - ε * a' - ε * z) := by
      rw [mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add]; congr 2; ring
    have hineq : -(2 * ε * t) - 2 * α * u ≤ ε * D - ε * a' - ε * z := by
      have h1 : z - t ≤ u := by rw [hu, abs_sub_comm]; exact le_abs_self _
      have h2 : 0 ≤ u := abs_nonneg _
      have h3 : ε * u ≤ 2 * α * u := mul_le_mul_of_nonneg_right (by linarith) h2
      rw [ht] at h1 ⊢
      nlinarith
    calc |Real.exp (-(ε * t)) * F (a' - D - z)| ^ 2
        ≤ (Real.exp (-(ε * t)) * (M * Real.exp (-(α * u)))) ^ 2 := hsq
      _ = M ^ 2 * Real.exp (-(2 * ε * t) - 2 * α * u) := by rw [e1]; ring
      _ ≤ M ^ 2 * Real.exp (ε * D - ε * a' - ε * z) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hineq) (sq_nonneg M)
      _ = _ := e2.symm
  have hbound : ∫⁻ a', ∫⁻ z, ‖(clockDecayConvKernel ε hε.le F hF hM hα hFb).toFun a' z‖ₑ ^ 2
      ∂halfLineMeasure ∂halfLineMeasure ≤
      ∫⁻ a' in Ici (0 : ℝ), ∫⁻ z in Ici (0 : ℝ),
        ENNReal.ofReal (M ^ 2 * Real.exp (ε * D) * Real.exp (-(ε * a'))) *
          ENNReal.ofReal (Real.exp (-(ε * z))) :=
    setLIntegral_mono' measurableSet_Ici fun a' ha' =>
      lintegral_mono fun z => hpt a' ha' z
  refine lt_of_le_of_lt hbound ?_
  simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [lintegral_mul_const' _ _ (lintegral_Ici_ofReal_exp_neg_lt_top hε).ne]
  refine ENNReal.mul_lt_top ?_ (lintegral_Ici_ofReal_exp_neg_lt_top hε)
  have e : ∀ a', ENNReal.ofReal (M ^ 2 * Real.exp (ε * D) * Real.exp (-(ε * a'))) =
      ENNReal.ofReal (M ^ 2 * Real.exp (ε * D)) * ENNReal.ofReal (Real.exp (-(ε * a'))) :=
    fun a' => ENNReal.ofReal_mul (by positivity)
  simp_rw [e]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lintegral_Ici_ofReal_exp_neg_lt_top hε)

/-- The translation kernel `C[F](a', b') = F(a' - b')`. -/
def clockConvKernel (F : ℝ → ℝ) (hF : Continuous F) (hM : 0 ≤ M) (hα : 0 < α)
    (hFb : ∀ s, |F s| ≤ M * Real.exp (-(α * |s|))) : SchurKernel halfLineMeasure where
  toFun a' b' := ((F (a' - b') : ℝ) : ℂ)
  measurable := Complex.measurable_ofReal.comp
    (hF.measurable.comp (measurable_fst.sub measurable_snd))
  bound := Real.toNNReal (M * (2 / α))
  row a' := (setLIntegral_le_lintegral _ _).trans (lintegral_enorm_translate_le hM hα hFb a')
  col b' := (setLIntegral_le_lintegral _ _).trans (lintegral_enorm_translate_le' hM hα hFb b')

end DecayConv

/-! ### Clock-defect profiles -/

/-- A `C²` profile whose first two derivatives are bounded by `M e^{-α|s|}`. -/
structure ClockDefectProfile where
  g : ℝ → ℝ
  d1 : ℝ → ℝ
  d2 : ℝ → ℝ
  hasDerivAt_g : ∀ s, HasDerivAt g (d1 s) s
  hasDerivAt_d1 : ∀ s, HasDerivAt d1 (d2 s) s
  continuous_d2 : Continuous d2
  M : ℝ
  α : ℝ
  M_nonneg : 0 ≤ M
  α_pos : 0 < α
  abs_d1_le : ∀ s, |d1 s| ≤ M * Real.exp (-(α * |s|))
  abs_d2_le : ∀ s, |d2 s| ≤ M * Real.exp (-(α * |s|))

namespace ClockDefectProfile

variable (P : ClockDefectProfile)

@[fun_prop]
theorem continuous_g : Continuous P.g :=
  continuous_iff_continuousAt.2 fun s => (P.hasDerivAt_g s).continuousAt

@[fun_prop]
theorem continuous_d1 : Continuous P.d1 :=
  continuous_iff_continuousAt.2 fun s => (P.hasDerivAt_d1 s).continuousAt

@[fun_prop]
theorem continuous_d2' : Continuous P.d2 := P.continuous_d2

/-- The exponential weight rate `ε = min (1/4) (α/2)`. -/
def ε : ℝ := min (1 / 4) (P.α / 2)

theorem ε_pos : 0 < P.ε := lt_min (by norm_num) (by linarith [P.α_pos])

theorem ε_le_quarter : P.ε ≤ 1 / 4 := min_le_left _ _

theorem two_ε_le_α : 2 * P.ε ≤ P.α := by
  have := min_le_right (1 / 4 : ℝ) (P.α / 2)
  unfold ε; linarith

theorem abs_neg_d1_neg_le (s : ℝ) : |(fun s => -P.d1 (-s)) s| ≤ P.M * Real.exp (-(P.α * |s|)) := by
  simpa [abs_neg] using P.abs_d1_le (-s)

theorem abs_neg_d2_le (s : ℝ) : |(fun s => -P.d2 s) s| ≤ P.M * Real.exp (-(P.α * |s|)) := by
  simpa [abs_neg] using P.abs_d2_le s

/-- `R_ε`, the weighted displacement kernel. -/
def weightKernel : SchurKernel halfLineMeasure :=
  clockOrientWeightKernel P.ε P.ε_pos.le (by linarith [P.ε_le_quarter])

/-- `W_ε[g']`. -/
def firstKernel : SchurKernel halfLineMeasure :=
  clockDecayConvKernel P.ε P.ε_pos.le P.d1 P.continuous_d1 P.M_nonneg P.α_pos P.abs_d1_le

/-- `W_ε[-g'(-·)]`. -/
def firstKernelRev : SchurKernel halfLineMeasure :=
  clockDecayConvKernel P.ε P.ε_pos.le (fun s => -P.d1 (-s))
    (P.continuous_d1.comp continuous_neg).neg P.M_nonneg P.α_pos P.abs_neg_d1_neg_le

/-- `C[-g'']`. -/
def secondKernel : SchurKernel halfLineMeasure :=
  clockConvKernel (fun s => -P.d2 s) P.continuous_d2.neg P.M_nonneg P.α_pos P.abs_neg_d2_le

theorem weightKernel_sq_lt_top :
    ∫⁻ a', ∫⁻ y, ‖P.weightKernel.toFun a' y‖ₑ ^ 2 ∂halfLineMeasure ∂halfLineMeasure < ∞ :=
  lintegral_clockOrientWeightKernel_sq_lt_top P.ε_pos.le P.ε_le_quarter

theorem firstKernel_sq_lt_top :
    ∫⁻ a', ∫⁻ z, ‖P.firstKernel.toFun a' z‖ₑ ^ 2 ∂halfLineMeasure ∂halfLineMeasure < ∞ :=
  lintegral_clockDecayConvKernel_sq_lt_top P.ε_pos _ _ _ P.two_ε_le_α _

theorem firstKernelRev_sq_lt_top :
    ∫⁻ a', ∫⁻ z, ‖P.firstKernelRev.toFun a' z‖ₑ ^ 2 ∂halfLineMeasure ∂halfLineMeasure < ∞ :=
  lintegral_clockDecayConvKernel_sq_lt_top P.ε_pos _ _ _ P.two_ε_le_α _

/-! #### The three composed kernels -/

theorem hasDerivAt_g_sub_const (z a : ℝ) :
    HasDerivAt (fun a => ((P.g (a - z) : ℝ) : ℂ)) ((P.d1 (a - z) : ℝ) : ℂ) a :=
  ((P.hasDerivAt_g (a - z)).comp_sub_const a z).ofReal_comp

theorem hasDerivAt_g_const_sub (y b : ℝ) :
    HasDerivAt (fun b => ((P.g (y - b) : ℝ) : ℂ)) ((-P.d1 (y - b) : ℝ) : ℂ) b :=
  ((P.hasDerivAt_g (y - b)).comp_const_sub y b).ofReal_comp

theorem hasDerivAt_d1_const_sub (c b : ℝ) :
    HasDerivAt (fun b => ((P.d1 (c - b) : ℝ) : ℂ)) ((-P.d2 (c - b) : ℝ) : ℂ) b :=
  ((P.hasDerivAt_d1 (c - b)).comp_const_sub c b).ofReal_comp

/-- `e₂(y,z) = g(ψ y - z) - g(y - z)` is the kernel of `R_ε† ∘ W_ε[g']`. -/
theorem comp_weight_first {y : ℝ} (hy : 0 ≤ y) (z : ℝ) :
    (SchurKernel.comp P.weightKernel.adjoint P.firstKernel).toFun y z =
      ((P.g (poissonClock y - z) - P.g (y - z) : ℝ) : ℂ) := by
  rw [SchurKernel.comp_toFun]
  have hpt : ∀ a' ∈ Ici (0 : ℝ),
      P.weightKernel.adjoint.toFun y a' * P.firstKernel.toFun a' z =
        (clockOrient y (a' - poissonClockConst) : ℂ) *
          (fun a => ((P.d1 (a - z) : ℝ) : ℂ)) (a' - poissonClockConst) := by
    intro a' ha'
    have ha0 : (0 : ℝ) ≤ a' := ha'
    rw [SchurKernel.adjoint_toFun, weightKernel, clockOrientWeightKernel_toFun, Complex.conj_ofReal,
      firstKernel, clockDecayConvKernel_toFun, clockDecayWeight_of_nonneg _ ha0]
    have hexp : Real.exp (P.ε * (a' - poissonClockConst)) *
        Real.exp (-(P.ε * (a' - poissonClockConst))) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    simp only
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
    congr 1
    rw [show Real.exp (P.ε * (a' - poissonClockConst)) * clockOrient y (a' - poissonClockConst) *
        (Real.exp (-(P.ε * (a' - poissonClockConst))) * P.d1 (a' - poissonClockConst - z)) =
        (Real.exp (P.ε * (a' - poissonClockConst)) *
          Real.exp (-(P.ε * (a' - poissonClockConst)))) *
          (clockOrient y (a' - poissonClockConst) * P.d1 (a' - poissonClockConst - z)) by ring,
      hexp, one_mul]
  show ∫ a' in Ici (0 : ℝ), _ = _
  rw [setIntegral_congr_fun measurableSet_Ici hpt]
  show ∫ a', (clockOrient y (a' - poissonClockConst) : ℂ) *
      (fun a => ((P.d1 (a - z) : ℝ) : ℂ)) (a' - poissonClockConst) ∂halfLineMeasure = _
  rw [integral_halfLine_clockOrient hy (G := fun a => ((P.d1 (a - z) : ℝ) : ℂ)) (by fun_prop),
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun a _ => P.hasDerivAt_g_sub_const z a)
      ((by fun_prop : Continuous fun a => ((P.d1 (a - z) : ℝ) : ℂ)).intervalIntegrable _ _)]
  push_cast; ring

/-- `e₃(y,z) = g(y - ψ z) - g(y - z)` is the kernel of `W_ε[-g'(-·)]† ∘ R_ε`. -/
theorem comp_firstRev_weight {z : ℝ} (hz : 0 ≤ z) (y : ℝ) :
    (SchurKernel.comp P.firstKernelRev.adjoint P.weightKernel).toFun y z =
      ((P.g (y - poissonClock z) - P.g (y - z) : ℝ) : ℂ) := by
  rw [SchurKernel.comp_toFun]
  have hpt : ∀ b' ∈ Ici (0 : ℝ),
      P.firstKernelRev.adjoint.toFun y b' * P.weightKernel.toFun b' z =
        (clockOrient z (b' - poissonClockConst) : ℂ) *
          (fun b => ((-P.d1 (y - b) : ℝ) : ℂ)) (b' - poissonClockConst) := by
    intro b' hb'
    have hb0 : (0 : ℝ) ≤ b' := hb'
    rw [SchurKernel.adjoint_toFun, firstKernelRev, clockDecayConvKernel_toFun, Complex.conj_ofReal,
      weightKernel, clockOrientWeightKernel_toFun, clockDecayWeight_of_nonneg _ hb0]
    have hexp : Real.exp (-(P.ε * (b' - poissonClockConst))) *
        Real.exp (P.ε * (b' - poissonClockConst)) = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    simp only
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
    congr 1
    rw [show -(b' - poissonClockConst - y) = y - (b' - poissonClockConst) by ring]
    rw [show Real.exp (-(P.ε * (b' - poissonClockConst))) * -P.d1 (y - (b' - poissonClockConst)) *
        (Real.exp (P.ε * (b' - poissonClockConst)) * clockOrient z (b' - poissonClockConst)) =
        (Real.exp (-(P.ε * (b' - poissonClockConst))) *
          Real.exp (P.ε * (b' - poissonClockConst))) *
          (clockOrient z (b' - poissonClockConst) * -P.d1 (y - (b' - poissonClockConst))) by ring,
      hexp, one_mul]
  show ∫ b' in Ici (0 : ℝ), _ = _
  rw [setIntegral_congr_fun measurableSet_Ici hpt]
  show ∫ b', (clockOrient z (b' - poissonClockConst) : ℂ) *
      (fun b => ((-P.d1 (y - b) : ℝ) : ℂ)) (b' - poissonClockConst) ∂halfLineMeasure = _
  rw [integral_halfLine_clockOrient hz (G := fun b => ((-P.d1 (y - b) : ℝ) : ℂ)) (by fun_prop),
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun b _ => P.hasDerivAt_g_const_sub y b)
      ((by fun_prop : Continuous fun b => ((-P.d1 (y - b) : ℝ) : ℂ)).intervalIntegrable _ _)]
  push_cast; ring

/-- The kernel of `C[-g''] ∘ R`: `d1(a' - D - ψ z) - d1(a' - D - z)`. -/
theorem comp_second_orient {z : ℝ} (hz : 0 ≤ z) (a' : ℝ) :
    (SchurKernel.comp P.secondKernel clockOrientKernel).toFun a' z =
      ((P.d1 (a' - poissonClockConst - poissonClock z) -
        P.d1 (a' - poissonClockConst - z) : ℝ) : ℂ) := by
  rw [SchurKernel.comp_toFun]
  have hpt : ∀ b', P.secondKernel.toFun a' b' * clockOrientKernel.toFun b' z =
      (clockOrient z (b' - poissonClockConst) : ℂ) *
        (fun b => ((-P.d2 (a' - poissonClockConst - b) : ℝ) : ℂ)) (b' - poissonClockConst) := by
    intro b'
    rw [clockOrientKernel_toFun]
    show ((-P.d2 (a' - b') : ℝ) : ℂ) * _ = _
    simp only
    rw [show a' - poissonClockConst - (b' - poissonClockConst) = a' - b' by ring]
    ring
  rw [integral_congr_ae (Eventually.of_forall hpt),
    integral_halfLine_clockOrient hz (G := fun b => ((-P.d2 (a' - poissonClockConst - b) : ℝ) : ℂ))
      (by fun_prop),
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun b _ => P.hasDerivAt_d1_const_sub (a' - poissonClockConst) b)
      ((by fun_prop : Continuous fun b =>
        ((-P.d2 (a' - poissonClockConst - b) : ℝ) : ℂ)).intervalIntegrable _ _)]
  push_cast; ring

/-- `r(y,z) = g(ψy - ψz) - g(y - ψz) - g(ψy - z) + g(y - z)` is the kernel of
`R† ∘ C[-g''] ∘ R`. -/
theorem comp_orient_second {y z : ℝ} (hy : 0 ≤ y) (hz : 0 ≤ z) :
    (SchurKernel.comp clockOrientKernel.adjoint
        (SchurKernel.comp P.secondKernel clockOrientKernel)).toFun y z =
      ((P.g (poissonClock y - poissonClock z) - P.g (y - poissonClock z) -
        (P.g (poissonClock y - z) - P.g (y - z)) : ℝ) : ℂ) := by
  rw [SchurKernel.comp_toFun]
  have hpt : ∀ a', clockOrientKernel.adjoint.toFun y a' *
      (SchurKernel.comp P.secondKernel clockOrientKernel).toFun a' z =
      (clockOrient y (a' - poissonClockConst) : ℂ) *
        (fun a => ((P.d1 (a - poissonClock z) : ℝ) : ℂ) - ((P.d1 (a - z) : ℝ) : ℂ))
          (a' - poissonClockConst) := by
    intro a'
    rw [SchurKernel.adjoint_toFun, clockOrientKernel_toFun, Complex.conj_ofReal,
      P.comp_second_orient hz a']
    push_cast
    ring_nf
  have hderiv : ∀ a, HasDerivAt
      (fun a => ((P.g (a - poissonClock z) : ℝ) : ℂ) - ((P.g (a - z) : ℝ) : ℂ))
      (((P.d1 (a - poissonClock z) : ℝ) : ℂ) - ((P.d1 (a - z) : ℝ) : ℂ)) a := fun a =>
    (P.hasDerivAt_g_sub_const (poissonClock z) a).sub (P.hasDerivAt_g_sub_const z a)
  rw [integral_congr_ae (Eventually.of_forall hpt),
    integral_halfLine_clockOrient hy
      (G := fun a => ((P.d1 (a - poissonClock z) : ℝ) : ℂ) - ((P.d1 (a - z) : ℝ) : ℂ))
      (by fun_prop),
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun a _ => hderiv a)
      ((by fun_prop : Continuous fun a =>
        ((P.d1 (a - poissonClock z) : ℝ) : ℂ) - ((P.d1 (a - z) : ℝ) : ℂ)).intervalIntegrable _ _)]
  push_cast; ring

/-- The composed kernel `C[-g''] ∘ R` is square integrable. -/
theorem comp_second_orient_sq_lt_top :
    ∫⁻ a', ∫⁻ z, ‖(SchurKernel.comp P.secondKernel clockOrientKernel).toFun a' z‖ₑ ^ 2
      ∂halfLineMeasure ∂halfLineMeasure < ∞ := by
  set k := SchurKernel.comp P.secondKernel clockOrientKernel
  set D := poissonClockConst with hD
  have hD0 : 0 ≤ D := poissonClockConst_nonneg
  rw [lintegral_lintegral_swap ((k.measurable_enorm.pow_const 2).aemeasurable)]
  set K : ℝ := (P.M * Real.exp (P.α * D) * D) ^ 2 with hK
  have hpt : ∀ z ∈ Ici (0 : ℝ), ∫⁻ a', ‖k.toFun a' z‖ₑ ^ 2 ∂halfLineMeasure ≤
      ENNReal.ofReal (K * (2 / (2 * P.α))) * ENNReal.ofReal (Real.exp (-(2 * z))) := by
    intro z hz
    have hz0 : (0 : ℝ) ≤ z := hz
    have hδ := abs_poissonClock_sub_le hz0
    have hδ' := abs_poissonClock_sub_le_const z
    have hpt2 : ∀ a', ‖k.toFun a' z‖ₑ ^ 2 ≤ ENNReal.ofReal (K * Real.exp (-(2 * z))) *
        ENNReal.ofReal (Real.exp (-(2 * P.α * |(D + z) - a'|))) := by
      intro a'
      rw [P.comp_second_orient hz0 a', ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
        ← ENNReal.ofReal_pow (abs_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hmv := abs_sub_le_of_deriv_exp P.hasDerivAt_d1 P.M_nonneg P.α_pos.le P.abs_d2_le
        (a' - D - poissonClock z) (a' - D - z)
      have hab : |a' - D - poissonClock z - (a' - D - z)| = |poissonClock z - z| := by
        rw [show a' - D - poissonClock z - (a' - D - z) = -(poissonClock z - z) by ring, abs_neg]
      rw [hab, show |a' - D - z| = |(D + z) - a'| by rw [abs_sub_comm]; ring_nf] at hmv
      have hb : |P.d1 (a' - D - poissonClock z) - P.d1 (a' - D - z)| ≤
          P.M * Real.exp (P.α * D) * Real.exp (-(P.α * |(D + z) - a'|)) *
            (D * Real.exp (-z)) := by
        refine hmv.trans ?_
        have h1 : Real.exp (P.α * |poissonClock z - z|) ≤ Real.exp (P.α * D) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hδ' P.α_pos.le)
        have hM := P.M_nonneg
        gcongr
      have hsq := pow_le_pow_left₀ (abs_nonneg _) hb 2
      refine hsq.trans (le_of_eq ?_)
      have e1 : Real.exp (-(P.α * |(D + z) - a'|)) ^ 2 =
          Real.exp (-(2 * P.α * |(D + z) - a'|)) := by
        rw [sq, ← Real.exp_add]; ring_nf
      have e2 : Real.exp (-z) ^ 2 = Real.exp (-(2 * z)) := by
        rw [sq, ← Real.exp_add]; ring_nf
      calc (P.M * Real.exp (P.α * D) * Real.exp (-(P.α * |(D + z) - a'|)) *
            (D * Real.exp (-z))) ^ 2
          = K * Real.exp (-z) ^ 2 * Real.exp (-(P.α * |(D + z) - a'|)) ^ 2 := by rw [hK]; ring
        _ = K * Real.exp (-(2 * z)) * Real.exp (-(2 * P.α * |(D + z) - a'|)) := by rw [e1, e2]
    refine (setLIntegral_le_lintegral _ _).trans ((lintegral_mono hpt2).trans ?_)
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have hβ : 0 < 2 * P.α := by linarith [P.α_pos]
    have h2 := lintegral_ofReal_exp_neg_abs_sub_le hβ (D + z)
    rw [h2, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    ring
  refine lt_of_le_of_lt (setLIntegral_mono' measurableSet_Ici hpt) ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lintegral_Ici_ofReal_exp_neg_lt_top two_pos)

/-! #### Trace class and zero trace -/

local instance fact_two_ne_top_clockDefect : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩

theorem hs_weight_adjoint : ContinuousLinearMap.IsHilbertSchmidt P.weightKernel.adjoint.op :=
  P.weightKernel.adjoint.isHilbertSchmidt_op
    ((SchurKernel.lintegral_adjoint_sq _).trans_lt P.weightKernel_sq_lt_top)

theorem hs_weight : ContinuousLinearMap.IsHilbertSchmidt P.weightKernel.op :=
  P.weightKernel.isHilbertSchmidt_op P.weightKernel_sq_lt_top

theorem hs_first : ContinuousLinearMap.IsHilbertSchmidt P.firstKernel.op :=
  P.firstKernel.isHilbertSchmidt_op P.firstKernel_sq_lt_top

theorem hs_firstRev_adjoint : ContinuousLinearMap.IsHilbertSchmidt P.firstKernelRev.adjoint.op :=
  P.firstKernelRev.adjoint.isHilbertSchmidt_op
    ((SchurKernel.lintegral_adjoint_sq _).trans_lt P.firstKernelRev_sq_lt_top)

theorem hs_orient_adjoint : ContinuousLinearMap.IsHilbertSchmidt clockOrientKernel.adjoint.op :=
  clockOrientKernel.adjoint.isHilbertSchmidt_op
    ((SchurKernel.lintegral_adjoint_sq _).trans_lt lintegral_clockOrientKernel_sq_lt_top)

theorem hs_second_orient :
    ContinuousLinearMap.IsHilbertSchmidt (SchurKernel.comp P.secondKernel clockOrientKernel).op :=
  (SchurKernel.comp P.secondKernel clockOrientKernel).isHilbertSchmidt_op
    P.comp_second_orient_sq_lt_top

/-- The three trace-class pieces `T₂ = R_ε† W_ε[g']`, `T₃ = W_ε[-g'(-·)]† R_ε`,
`T₅ = R† (C[-g''] R)`. -/
theorem memSchattenClass_one_pieces :
    MemSchattenClass 1 (P.weightKernel.adjoint.op ∘L P.firstKernel.op) ∧
      MemSchattenClass 1 (P.firstKernelRev.adjoint.op ∘L P.weightKernel.op) ∧
      MemSchattenClass 1 (clockOrientKernel.adjoint.op ∘L
        (SchurKernel.comp P.secondKernel clockOrientKernel).op) :=
  ⟨IsTraceClass.memSchattenClass_one
      (ContinuousLinearMap.IsHilbertSchmidt.comp_isTraceClass P.hs_weight_adjoint P.hs_first),
    IsTraceClass.memSchattenClass_one
      (ContinuousLinearMap.IsHilbertSchmidt.comp_isTraceClass P.hs_firstRev_adjoint P.hs_weight),
    IsTraceClass.memSchattenClass_one
      (ContinuousLinearMap.IsHilbertSchmidt.comp_isTraceClass hs_orient_adjoint
        P.hs_second_orient)⟩

variable (k : SchurKernel halfLineMeasure)
  (hk : ∀ y z, k.toFun y z = ((P.g (poissonClock y - poissonClock z) - P.g (y - z) : ℝ) : ℂ))
include hk

/-- **The three-term factorization of the clock-defect operator.** -/
theorem op_eq_sum :
    k.op = P.weightKernel.adjoint.op ∘L P.firstKernel.op +
      P.firstKernelRev.adjoint.op ∘L P.weightKernel.op +
      clockOrientKernel.adjoint.op ∘L (SchurKernel.comp P.secondKernel clockOrientKernel).op := by
  rw [← SchurKernel.comp_op, ← SchurKernel.comp_op, ← SchurKernel.comp_op,
    ← SchurKernel.add_op, ← SchurKernel.add_op]
  refine SchurKernel.op_eq_of_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ici] with y hy
  filter_upwards [ae_restrict_mem measurableSet_Ici] with z hz
  have hy0 : (0 : ℝ) ≤ y := hy
  have hz0 : (0 : ℝ) ≤ z := hz
  show k.toFun y z = (SchurKernel.comp P.weightKernel.adjoint P.firstKernel).toFun y z +
    (SchurKernel.comp P.firstKernelRev.adjoint P.weightKernel).toFun y z +
    (SchurKernel.comp clockOrientKernel.adjoint
      (SchurKernel.comp P.secondKernel clockOrientKernel)).toFun y z
  rw [hk, P.comp_weight_first hy0, P.comp_firstRev_weight hz0, P.comp_orient_second hy0 hz0]
  push_cast; ring

/-- **The clock-defect operator is trace class.** -/
theorem memSchattenClass_one_op : MemSchattenClass 1 k.op := by
  obtain ⟨h2, h3, h5⟩ := P.memSchattenClass_one_pieces
  rw [P.op_eq_sum k hk]
  have h23 := memSchattenClass_one_add (h2.isCompactOperator one_pos) (h3.isCompactOperator one_pos)
    h2 h3
  exact memSchattenClass_one_add (h23.isCompactOperator one_pos) (h5.isCompactOperator one_pos)
    h23 h5

theorem isTraceClass_op : ContinuousLinearMap.IsTraceClass k.op :=
  (P.memSchattenClass_one_op k hk).one_isTraceClass

/-- **The clock defect has zero trace**: `Tr = ∫ e(y,y) dy = 0`. -/
theorem opTrace_op : ContinuousLinearMap.opTrace k.op = 0 := by
  haveI : TopologicalSpace.SeparableSpace L²₊ := inferInstance
  obtain ⟨h2, h3, h5⟩ := P.memSchattenClass_one_pieces
  have h23 := memSchattenClass_one_add (h2.isCompactOperator one_pos) (h3.isCompactOperator one_pos)
    h2 h3
  rw [P.op_eq_sum k hk, opTrace_add_of_memSchattenClass_one h23 h5,
    opTrace_add_of_memSchattenClass_one h2 h3,
    SchurKernel.opTrace_adjoint_comp_op _ _ P.weightKernel_sq_lt_top P.firstKernel_sq_lt_top,
    SchurKernel.opTrace_adjoint_comp_op _ _ P.firstKernelRev_sq_lt_top P.weightKernel_sq_lt_top,
    SchurKernel.opTrace_adjoint_comp_op _ _ lintegral_clockOrientKernel_sq_lt_top
      P.comp_second_orient_sq_lt_top]
  have hA := SchurKernel.integrable_comp_adjoint_diag _ _ P.weightKernel_sq_lt_top
    P.firstKernel_sq_lt_top
  have hB := SchurKernel.integrable_comp_adjoint_diag _ _ P.firstKernelRev_sq_lt_top
    P.weightKernel_sq_lt_top
  have hC := SchurKernel.integrable_comp_adjoint_diag _ _ lintegral_clockOrientKernel_sq_lt_top
    P.comp_second_orient_sq_lt_top
  have hAB : Integrable (fun y =>
      (SchurKernel.comp P.weightKernel.adjoint P.firstKernel).toFun y y +
        (SchurKernel.comp P.firstKernelRev.adjoint P.weightKernel).toFun y y) halfLineMeasure :=
    hA.add hB
  rw [← integral_add hA hB, ← integral_add hAB hC]
  rw [← integral_zero ℝ ℂ (μ := halfLineMeasure)]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ici] with y hy
  have hy0 : (0 : ℝ) ≤ y := hy
  show _ + _ + _ = (0 : ℂ)
  rw [P.comp_weight_first hy0, P.comp_firstRev_weight hy0, P.comp_orient_second hy0 hy0]
  simp only [sub_self]
  push_cast; ring

end ClockDefectProfile

/-! ### The Poisson profile `h = sech²(·/2)` and its tilt `j(s) = s h(s)` -/

/-- `h''(s) = 4 e^s (1 - 4 e^s + e^{2s}) / (1 + e^s)^4`. -/
def sechSqHalfDeriv2 (s : ℝ) : ℝ :=
  4 * Real.exp s * (1 - 4 * Real.exp s + Real.exp s ^ 2) / (1 + Real.exp s) ^ 4

theorem hasDerivAt_sechSqHalfDeriv (s : ℝ) :
    HasDerivAt sechSqHalfDeriv (sechSqHalfDeriv2 s) s := by
  have hx := Real.hasDerivAt_exp s
  have h1 : HasDerivAt (fun s => 4 * Real.exp s * (1 - Real.exp s))
      (4 * Real.exp s * (1 - Real.exp s) + 4 * Real.exp s * (-Real.exp s)) s :=
    (hx.const_mul 4).mul (hx.const_sub 1)
  have h2 : HasDerivAt (fun s => (1 + Real.exp s) ^ 3)
      ((3 : ℕ) * (1 + Real.exp s) ^ (3 - 1) * Real.exp s) s :=
    (hx.const_add 1).fun_pow 3
  have h := h1.div h2 (by positivity)
  show HasDerivAt (fun y => 4 * Real.exp y * (1 - Real.exp y) / (1 + Real.exp y) ^ 3) _ s
  refine h.congr_deriv ?_
  unfold sechSqHalfDeriv2
  have := Real.exp_pos s
  field_simp
  ring

theorem continuous_sechSqHalfDeriv2 : Continuous sechSqHalfDeriv2 := by
  unfold sechSqHalfDeriv2
  refine Continuous.div (by fun_prop) (by fun_prop) fun s => by positivity

/-- `|h''| ≤ h`. -/
theorem abs_sechSqHalfDeriv2_le (s : ℝ) : |sechSqHalfDeriv2 s| ≤ sechSqHalf s := by
  have hx := Real.exp_pos s
  have hq : sechSqHalfDeriv2 s =
      sechSqHalf s * ((1 - 4 * Real.exp s + Real.exp s ^ 2) / (1 + Real.exp s) ^ 2) := by
    unfold sechSqHalfDeriv2 sechSqHalf
    field_simp
  rw [hq, abs_mul, abs_of_pos (sechSqHalf_pos s)]
  refine mul_le_of_le_one_right (sechSqHalf_pos s).le ?_
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (1 + Real.exp s) ^ 2),
    div_le_one (by positivity)]
  rw [abs_le]; constructor <;> nlinarith [sq_nonneg (Real.exp s - 1)]

/-- The Poisson profile `h = sech²(·/2)`: `M = 4`, `α = 1`. -/
def sechSqHalfProfile : ClockDefectProfile where
  g := sechSqHalf
  d1 := sechSqHalfDeriv
  d2 := sechSqHalfDeriv2
  hasDerivAt_g := hasDerivAt_sechSqHalf
  hasDerivAt_d1 := hasDerivAt_sechSqHalfDeriv
  continuous_d2 := continuous_sechSqHalfDeriv2
  M := 4
  α := 1
  M_nonneg := by norm_num
  α_pos := one_pos
  abs_d1_le := abs_sechSqHalfDeriv_le_exp
  abs_d2_le s := (abs_sechSqHalfDeriv2_le s).trans (by rw [one_mul]; exact sechSqHalf_le_exp_neg_abs s)

/-- `j''(s) = 2 h'(s) + s h''(s)`. -/
def sechSqHalfTiltDeriv2 (s : ℝ) : ℝ := 2 * sechSqHalfDeriv s + s * sechSqHalfDeriv2 s

theorem hasDerivAt_sechSqHalfTiltDeriv (s : ℝ) :
    HasDerivAt sechSqHalfTiltDeriv (sechSqHalfTiltDeriv2 s) s := by
  have h := (hasDerivAt_sechSqHalf s).add ((hasDerivAt_id' s).mul (hasDerivAt_sechSqHalfDeriv s))
  show HasDerivAt (fun y => sechSqHalf y + y * sechSqHalfDeriv y) _ s
  exact h.congr_deriv (by rw [sechSqHalfTiltDeriv2]; ring)

theorem continuous_sechSqHalfTiltDeriv2 : Continuous sechSqHalfTiltDeriv2 := by
  have hd : Continuous sechSqHalfDeriv :=
    continuous_iff_continuousAt.2 fun s => (hasDerivAt_sechSqHalfDeriv s).continuousAt
  unfold sechSqHalfTiltDeriv2
  exact (continuous_const.mul hd).add (continuous_id.mul continuous_sechSqHalfDeriv2)

theorem abs_sechSqHalfTiltDeriv2_le (s : ℝ) :
    |sechSqHalfTiltDeriv2 s| ≤ 16 * Real.exp (-((1 / 2) * |s|)) := by
  unfold sechSqHalfTiltDeriv2
  have hd := abs_sechSqHalfDeriv_le s
  have hd2 := abs_sechSqHalfDeriv2_le s
  have hh := sechSqHalf_le_exp_neg_abs s
  have hpos := sechSqHalf_pos s
  have h2 := one_add_mul_exp_neg_le_two_mul_exp_half |s|
  calc |2 * sechSqHalfDeriv s + s * sechSqHalfDeriv2 s|
      ≤ 2 * sechSqHalf s + |s| * sechSqHalf s := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_two]
        gcongr
    _ ≤ 2 * ((1 + |s|) * sechSqHalf s) := by nlinarith [abs_nonneg s]
    _ ≤ 2 * ((1 + |s|) * (4 * Real.exp (-|s|))) := by gcongr
    _ = 8 * ((1 + |s|) * Real.exp (-|s|)) := by ring
    _ ≤ 8 * (2 * Real.exp (-(|s| / 2))) := by gcongr
    _ = 16 * Real.exp (-((1 / 2) * |s|)) := by ring_nf

/-- The tilted profile `j(s) = s h(s)`: `M = 16`, `α = 1/2`. -/
def sechSqHalfTiltProfile : ClockDefectProfile where
  g := sechSqHalfTilt
  d1 := sechSqHalfTiltDeriv
  d2 := sechSqHalfTiltDeriv2
  hasDerivAt_g := hasDerivAt_sechSqHalfTilt
  hasDerivAt_d1 := hasDerivAt_sechSqHalfTiltDeriv
  continuous_d2 := continuous_sechSqHalfTiltDeriv2
  M := 16
  α := 1 / 2
  M_nonneg := by norm_num
  α_pos := by norm_num
  abs_d1_le s := (abs_sechSqHalfTiltDeriv_le s).trans (by
    gcongr; norm_num)
  abs_d2_le := abs_sechSqHalfTiltDeriv2_le

/-! ### The Mertens-clock Poisson defect `E = A - W` -/

theorem sub_mertensStepSechKernel_toFun (y z : ℝ) :
    (SchurKernel.sub mertensStepSechKernel wienerHopfSechKernel).toFun y z =
      ((sechSqHalfProfile.g (poissonClock y - poissonClock z) - sechSqHalfProfile.g (y - z) : ℝ) :
        ℂ) := by
  show ((sechSqHalf (poissonClock y - poissonClock z) : ℝ) : ℂ) - ((sechSqHalf (y - z) : ℝ) : ℂ) = _
  push_cast; rfl

theorem sub_mertensStepTiltKernel_toFun (y z : ℝ) :
    (SchurKernel.sub mertensStepTiltKernel wienerHopfTiltKernel).toFun y z =
      ((sechSqHalfTiltProfile.g (poissonClock y - poissonClock z) -
        sechSqHalfTiltProfile.g (y - z) : ℝ) : ℂ) := by
  show ((sechSqHalfTilt (poissonClock y - poissonClock z) : ℝ) : ℂ) -
    ((sechSqHalfTilt (y - z) : ℝ) : ℂ) = _
  push_cast; rfl

/-- **Arithmetic trace-class upgrade.**  `E = A - W` is trace class. -/
theorem memSchattenClass_one_mertensStepSechOp_sub :
    MemSchattenClass 1 (mertensStepSechOp - wienerHopfSechOp) := by
  rw [mertensStepSechOp, wienerHopfSechOp, ← SchurKernel.sub_op]
  exact sechSqHalfProfile.memSchattenClass_one_op _ sub_mertensStepSechKernel_toFun

theorem isTraceClass_mertensStepSechOp_sub :
    ContinuousLinearMap.IsTraceClass (mertensStepSechOp - wienerHopfSechOp) :=
  memSchattenClass_one_mertensStepSechOp_sub.one_isTraceClass

/-- **`Tr E = 0`.** -/
theorem opTrace_mertensStepSechOp_sub :
    ContinuousLinearMap.opTrace (mertensStepSechOp - wienerHopfSechOp) = 0 := by
  rw [mertensStepSechOp, wienerHopfSechOp, ← SchurKernel.sub_op]
  exact sechSqHalfProfile.opTrace_op _ sub_mertensStepSechKernel_toFun

/-- The tilted defect `A_j - W_j` is trace class. -/
theorem memSchattenClass_one_mertensStepTiltOp_sub :
    MemSchattenClass 1 (mertensStepTiltOp - wienerHopfTiltOp) := by
  rw [mertensStepTiltOp, wienerHopfTiltOp, ← SchurKernel.sub_op]
  exact sechSqHalfTiltProfile.memSchattenClass_one_op _ sub_mertensStepTiltKernel_toFun

theorem opTrace_mertensStepTiltOp_sub :
    ContinuousLinearMap.opTrace (mertensStepTiltOp - wienerHopfTiltOp) = 0 := by
  rw [mertensStepTiltOp, wienerHopfTiltOp, ← SchurKernel.sub_op]
  exact sechSqHalfTiltProfile.opTrace_op _ sub_mertensStepTiltKernel_toFun

end

end RHTower
