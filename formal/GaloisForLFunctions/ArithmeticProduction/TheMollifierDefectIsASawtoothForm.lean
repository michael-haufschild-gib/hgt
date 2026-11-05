import GaloisForLFunctions.RHTower.ZetaFractionalPartGramCriterion

/-!
# The mollifier defect is a real-variable form in fractional parts

For a real Dirichlet polynomial `D(s) = Σ_{n ∈ S} a_n n^{−s}`, Plancherel on the critical line turns the mollifier defect
into a mean square of one explicit real function:

  `(2π)⁻¹ ∫ |1 − ζ(½+it) D(½+it)|² dt/(¼+t²) = ∫_ℝ e^{−u} F(e^u)² du = ∫_0^∞ F(x)² dx/x²`,
  `F(x) = 1_{x ≥ 1} + Σ_{n ∈ S} a_n {x/n}`
  (`mollifierDefect_eq`).

No normalization of `D(1)` is imposed: the pole of `ζ` is carried by `F` on `(0, 1)`, where `F(x) = x D(1)`
(`sawtoothDefect_of_lt_one`).  The band `u ∈ [0, L]` and the half-line `u < 0` give the lower bound
`mollifierDefect_ge_band`.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology
open scoped FourierTransform

namespace GaloisForLFunctions.ArithmeticProduction

/-- The pullback of the target `1/s`: `e^{−u/2} 1_{u ≥ 0}`. -/
def targetPull (u : ℝ) : ℂ := if 0 ≤ u then ((Real.exp (-(u / 2)) : ℝ) : ℂ) else 0

/-- The pullback of the defect. -/
def defectPull (S : Finset ℕ) (a : ℕ → ℝ) (u : ℝ) : ℂ :=
  targetPull u + _root_.RHTower.fractGramPull S a u

/-- The mollifier defect in the logarithmic coordinate. -/
def mollifierDefect (S : Finset ℕ) (a : ℕ → ℝ) : ℝ := ∫ u : ℝ, ‖defectPull S a u‖ ^ 2

/-- The sawtooth function `F(x) = 1_{x ≥ 1} + Σ a_n {x/n}`. -/
def sawtoothDefect (S : Finset ℕ) (a : ℕ → ℝ) (x : ℝ) : ℝ :=
  (if 1 ≤ x then 1 else 0) + ∑ n ∈ S, a n * Int.fract (x / n)

private theorem exp_lt_one_of_neg {u : ℝ} (hu : u < 0) : Real.exp u < 1 := by
  rw [← Real.exp_zero]
  exact Real.exp_lt_exp.mpr hu

theorem defectPull_eq_ofReal (S : Finset ℕ) (a : ℕ → ℝ) (u : ℝ) :
    defectPull S a u = ((Real.exp (-(u / 2)) * sawtoothDefect S a (Real.exp u) : ℝ) : ℂ) := by
  have hsum : ∑ n ∈ S, a n * (Real.exp (-(u / 2)) * Int.fract (Real.exp u / n)) =
      Real.exp (-(u / 2)) * ∑ n ∈ S, a n * Int.fract (Real.exp u / n) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by ring
  unfold defectPull
  rw [_root_.RHTower.fractGramPull_eq_ofReal, hsum]
  by_cases hu : 0 ≤ u
  · have h1 : 1 ≤ Real.exp u := Real.one_le_exp hu
    simp only [targetPull, sawtoothDefect, if_pos hu, if_pos h1]
    push_cast
    ring
  · have h1 : ¬ 1 ≤ Real.exp u := not_le.mpr (exp_lt_one_of_neg (not_le.mp hu))
    simp only [targetPull, sawtoothDefect, if_neg hu, if_neg h1]
    push_cast
    ring

theorem norm_sq_defectPull (S : Finset ℕ) (a : ℕ → ℝ) (u : ℝ) :
    ‖defectPull S a u‖ ^ 2 = Real.exp (-u) * sawtoothDefect S a (Real.exp u) ^ 2 := by
  rw [defectPull_eq_ofReal, Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow, ← Real.exp_nat_mul]
  congr 2
  push_cast
  ring

/-! ### The target -/

private theorem targetPull_eq_indicator :
    targetPull = (Ici (0 : ℝ)).indicator fun u => ((Real.exp (-(u / 2)) : ℝ) : ℂ) := by
  funext u
  by_cases hu : 0 ≤ u <;> simp [targetPull, indicator, hu]

private theorem integrableOn_exp_half : IntegrableOn (fun u : ℝ => Real.exp (-(u / 2))) (Ioi 0) := by
  have h := exp_neg_integrableOn_Ioi 0 (b := 1 / 2) (by norm_num)
  refine h.congr_fun (fun u _ => ?_) measurableSet_Ioi
  simp only
  congr 1
  ring

theorem integrable_targetPull : Integrable targetPull := by
  rw [targetPull_eq_indicator, integrable_indicator_iff measurableSet_Ici,
    integrableOn_Ici_iff_integrableOn_Ioi]
  exact integrableOn_exp_half.ofReal

theorem measurable_targetPull : Measurable targetPull := by
  rw [targetPull_eq_indicator]
  exact (Complex.measurable_ofReal.comp
    (Real.measurable_exp.comp (measurable_id.div_const 2).neg)).indicator measurableSet_Ici

theorem memLp_two_targetPull : MemLp targetPull 2 := by
  rw [memLp_two_iff_integrable_sq_norm measurable_targetPull.aestronglyMeasurable]
  have hval : (fun u => ‖targetPull u‖ ^ 2) =
      (Ici (0 : ℝ)).indicator fun u => Real.exp (-1 * u) := by
    funext u
    by_cases hu : 0 ≤ u
    · simp only [targetPull, if_pos hu, indicator, mem_Ici, Complex.norm_real, Real.norm_eq_abs,
        sq_abs, ← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    · simp [targetPull, indicator, hu]
  rw [hval, integrable_indicator_iff measurableSet_Ici, integrableOn_Ici_iff_integrableOn_Ioi]
  exact exp_neg_integrableOn_Ioi 0 one_pos

/-- **The Fourier transform of the target is `1/s`.** -/
theorem fourier_targetPull (t : ℝ) :
    𝓕 targetPull (t / (2 * Real.pi)) = 1 / (1 / 2 + t * I) := by
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [Real.fourier_real_eq]
  have hpt : ∀ v : ℝ, Real.fourierChar (-(v * (t / (2 * Real.pi)))) • targetPull v =
      (Ici (0 : ℝ)).indicator (fun v : ℝ => Complex.exp ((-(1 / 2 + t * I)) * v)) v := by
    intro v
    by_cases hv : 0 ≤ v
    · simp only [targetPull, if_pos hv, indicator, mem_Ici, Circle.smul_def, smul_eq_mul,
        Real.fourierChar_apply]
      push_cast
      rw [← Complex.exp_add]
      congr 1
      field_simp
      ring
    · simp [targetPull, indicator, hv]
  simp_rw [hpt]
  rw [integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi,
    integral_exp_mul_complex_Ioi (by simp) 0]
  simp only [ofReal_zero, mul_zero, Complex.exp_zero]
  rw [neg_div_neg_eq]

/-! ### The defect -/

theorem integrable_defectPull {S : Finset ℕ} (hS : ∀ n ∈ S, 1 ≤ n) (a : ℕ → ℝ) :
    Integrable (defectPull S a) :=
  integrable_targetPull.add (_root_.RHTower.integrable_fractGramPull hS a)

theorem memLp_two_defectPull {S : Finset ℕ} (hS : ∀ n ∈ S, 1 ≤ n) (a : ℕ → ℝ) :
    MemLp (defectPull S a) 2 :=
  memLp_two_targetPull.add (_root_.RHTower.memLp_two_fractGramPull hS a)

/-- **The Fourier transform of the defect is `(1 − ζD)/s`.** -/
theorem fourier_defectPull {S : Finset ℕ} (hS : ∀ n ∈ S, 1 ≤ n) (a : ℕ → ℝ) (t : ℝ) :
    𝓕 (defectPull S a) (t / (2 * Real.pi)) =
      (1 - riemannZeta (1 / 2 + t * I) * _root_.RHTower.realDirichletPoly S a (1 / 2 + t * I)) /
        (1 / 2 + t * I) := by
  have hadd : 𝓕 (defectPull S a) (t / (2 * Real.pi)) =
      𝓕 targetPull (t / (2 * Real.pi)) +
        𝓕 (_root_.RHTower.fractGramPull S a) (t / (2 * Real.pi)) := by
    simp only [Real.fourier_real_eq]
    unfold defectPull
    simp_rw [smul_add]
    refine integral_add ?_ ?_
    · refine Integrable.mono' integrable_targetPull.norm ?_
        (Filter.Eventually.of_forall fun v => by rw [Circle.norm_smul])
      exact ((Real.continuous_fourierChar.comp (by fun_prop)).aestronglyMeasurable).smul
        integrable_targetPull.aestronglyMeasurable
    · have hi := _root_.RHTower.integrable_fractGramPull hS a
      refine Integrable.mono' hi.norm ?_
        (Filter.Eventually.of_forall fun v => by rw [Circle.norm_smul])
      exact ((Real.continuous_fourierChar.comp (by fun_prop)).aestronglyMeasurable).smul
        hi.aestronglyMeasurable
  rw [hadd, fourier_targetPull, _root_.RHTower.fourier_fractGramPull hS]
  ring

/-- **The sawtooth form.**  `(2π)⁻¹ ∫ |1 − ζD|² dt/(¼+t²)` is the mean square of `F` against `dx/x²`. -/
theorem mollifierDefect_eq {S : Finset ℕ} (hS : ∀ n ∈ S, 1 ≤ n) (a : ℕ → ℝ) :
    (2 * Real.pi)⁻¹ * ∫ t : ℝ,
        ‖1 - riemannZeta (1 / 2 + t * I) * _root_.RHTower.realDirichletPoly S a (1 / 2 + t * I)‖ ^ 2 /
          (1 / 4 + t ^ 2) = mollifierDefect S a := by
  have hπ : 0 < 2 * Real.pi := by positivity
  have hP := GaloisForLFunctions.HTGeometry.integral_norm_sq_fourier
    (integrable_defectPull hS a) (memLp_two_defectPull hS a)
  have hpt : ∀ t : ℝ,
      ‖1 - riemannZeta (1 / 2 + t * I) * _root_.RHTower.realDirichletPoly S a (1 / 2 + t * I)‖ ^ 2 /
          (1 / 4 + t ^ 2) = ‖𝓕 (defectPull S a) (t / (2 * Real.pi))‖ ^ 2 := by
    intro t
    rw [fourier_defectPull hS, norm_div, div_pow, _root_.RHTower.norm_half_add_mul_I,
      Real.sq_sqrt (by positivity)]
  simp_rw [hpt]
  rw [Measure.integral_comp_div (fun ξ : ℝ => ‖𝓕 (defectPull S a) ξ‖ ^ 2) (2 * Real.pi), hP,
    abs_of_pos hπ, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hπ.ne', one_mul]
  rfl

theorem integrable_norm_sq_defectPull {S : Finset ℕ} (hS : ∀ n ∈ S, 1 ≤ n) (a : ℕ → ℝ) :
    Integrable fun u => ‖defectPull S a u‖ ^ 2 :=
  (memLp_two_iff_integrable_sq_norm (integrable_defectPull hS a).aestronglyMeasurable).mp
    (memLp_two_defectPull hS a)

/-- The value of the polynomial at `s = 1`. -/
def valueAtOne (S : Finset ℕ) (a : ℕ → ℝ) : ℝ := ∑ n ∈ S, a n / n

/-- Below `1` the sawtooth function is linear with slope `D(1)`: this is where the pole of `ζ` lives. -/
theorem sawtoothDefect_of_lt_one {S : Finset ℕ} (hS : ∀ n ∈ S, 1 ≤ n) (a : ℕ → ℝ) {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x < 1) : sawtoothDefect S a x = x * valueAtOne S a := by
  unfold sawtoothDefect valueAtOne
  rw [if_neg (not_le.mpr hx1), zero_add, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hS n hn
  have hn0 : (0 : ℝ) < n := by linarith
  rw [Int.fract_eq_self.mpr ⟨by positivity, (div_lt_one hn0).mpr (by linarith)⟩]
  ring

/-- **The band bound.**  If `F(e^u) = f(u)` on `[0, L]`, the defect dominates `D(1)²` plus the band integral. -/
theorem mollifierDefect_ge_band {S : Finset ℕ} (hS : ∀ n ∈ S, 1 ≤ n) (a : ℕ → ℝ) {L : ℝ} {f : ℝ → ℝ}
    (hf : ∀ u ∈ Icc 0 L, sawtoothDefect S a (Real.exp u) = f u) :
    valueAtOne S a ^ 2 + ∫ u in Icc 0 L, Real.exp (-u) * f u ^ 2 ≤ mollifierDefect S a := by
  have hint := integrable_norm_sq_defectPull hS a
  have hnn : ∀ u, 0 ≤ ‖defectPull S a u‖ ^ 2 := fun u => by positivity
  have hdisj : Disjoint (Iio (0 : ℝ)) (Icc 0 L) := by
    rw [Set.disjoint_left]
    intro u hu hu'
    exact absurd hu'.1 (not_le.mpr hu)
  have hsub : ∫ u in Iio (0 : ℝ) ∪ Icc 0 L, ‖defectPull S a u‖ ^ 2 ≤ mollifierDefect S a :=
    setIntegral_le_integral hint (Filter.Eventually.of_forall hnn)
  rw [setIntegral_union hdisj measurableSet_Icc hint.integrableOn hint.integrableOn] at hsub
  have hneg : ∫ u in Iio (0 : ℝ), ‖defectPull S a u‖ ^ 2 = valueAtOne S a ^ 2 := by
    have hpt : ∀ u ∈ Iio (0 : ℝ), ‖defectPull S a u‖ ^ 2 =
        valueAtOne S a ^ 2 * Real.exp u := by
      intro u hu
      have hu' : u < 0 := hu
      rw [norm_sq_defectPull, sawtoothDefect_of_lt_one hS a (Real.exp_pos u).le (exp_lt_one_of_neg hu'),
        mul_pow, ← mul_assoc]
      have h1 : Real.exp (-u) * Real.exp u ^ 2 = Real.exp u := by
        rw [sq, ← mul_assoc, ← Real.exp_add]
        simp
      rw [h1]
      ring
    rw [setIntegral_congr_fun measurableSet_Iio hpt, integral_const_mul,
      ← integral_Iic_eq_integral_Iio, integral_exp_Iic_zero, mul_one]
  have hband : ∫ u in Icc 0 L, ‖defectPull S a u‖ ^ 2 = ∫ u in Icc 0 L, Real.exp (-u) * f u ^ 2 := by
    refine setIntegral_congr_fun measurableSet_Icc fun u hu => ?_
    rw [norm_sq_defectPull, hf u hu]
  rw [hneg, hband] at hsub
  exact hsub

end GaloisForLFunctions.ArithmeticProduction
