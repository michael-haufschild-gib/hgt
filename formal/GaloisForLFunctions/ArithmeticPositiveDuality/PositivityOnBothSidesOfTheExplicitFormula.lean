import GaloisForLFunctions.MultiplicativePositivityGeometry.ZetaBoundaryDivisor
import GaloisForLFunctions.RHTower.AllIntegerPoissonCountertermAndBochnerPBAPBridge
import GaloisForLFunctions.RHTower.WeilFullConeExposedPoint

/-!
# Positivity on both sides of the explicit formula

The explicit formula pairs the prime measure with the zero measure. The two positivities of the
corpus are the Bochner statements of these two measures.

* **The prime side is positive, unconditionally** (`charFun_primeMeasure`). For `x > 0` the damped
  symmetric prime measure `ν_x = ½ Σ_n Λ(n) n^{−1−x} (δ_{log n} + δ_{−log n})` is a finite positive
  measure whose characteristic function is the height function
  `u ↦ Re(−ζ'/ζ)(1 + x + iu)` of multiplicative positivity.
* **The zero side is positive exactly under RH** (`riemannHypothesis_iff_forall_spectralMeasure`).
  RH holds iff for every `C²` compactly supported test `f` the scale function
  `y ↦ W(τ_y(f ⋆ f̃))` is the characteristic function of a finite positive measure (Weil's
  criterion in Bochner form).
* **The gap is on the prime side** (`weilFullFunctional_of_prime_free`). On tests vanishing for
  `|x| ≥ log 2` the prime side of Weil's functional is empty: only the pole and the archimedean
  term remain. Positivity and the prime-free gap sit on the same side of the Weil pair, which is why
  the Poisson rigidity of `PositiveSelfDualMeasuresWithAGapAreDiracCombs` gives only density
  statements there.

`positive_duality_of_the_explicit_formula` states the first two items together.
-/

open Complex MeasureTheory Set
open scoped Real

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality

open MultiplicativePositivityGeometry ArithmeticCastelnuovoSeveri

/-- The damped symmetric prime measure `½ Σ_n Λ(n) n^{−1−x} (δ_{log n} + δ_{−log n})`. -/
def primeMeasure (x : ℝ) : Measure ℝ :=
  Measure.sum (fun n : ℕ => ENNReal.ofReal (zetaBoundaryWeight x n / 2) •
      Measure.dirac (logFrequency n)) +
    Measure.sum (fun n : ℕ => ENNReal.ofReal (zetaBoundaryWeight x n / 2) •
      Measure.dirac (-logFrequency n))

theorem summable_half_weight {x : ℝ} (hx : 0 < x) :
    Summable fun n : ℕ => zetaBoundaryWeight x n / 2 :=
  (summable_zetaBoundaryWeight hx).div_const 2

theorem toReal_half_weight (x : ℝ) (n : ℕ) :
    (ENNReal.ofReal (zetaBoundaryWeight x n / 2)).toReal = zetaBoundaryWeight x n / 2 :=
  ENNReal.toReal_ofReal (by have := zetaBoundaryWeight_nonneg x n; positivity)

theorem isFiniteMeasure_primeMeasure {x : ℝ} (hx : 0 < x) : IsFiniteMeasure (primeMeasure x) := by
  have hw : ∀ n, 0 ≤ zetaBoundaryWeight x n / 2 := fun n => by
    have := zetaBoundaryWeight_nonneg x n; positivity
  have hfin : (Measure.sum fun n : ℕ => ENNReal.ofReal (zetaBoundaryWeight x n / 2) •
      Measure.dirac (logFrequency n)) univ < ⊤ := by
    rw [Measure.sum_apply _ MeasurableSet.univ]
    simp only [Measure.smul_apply, Measure.dirac_apply_of_mem (mem_univ _), smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_tsum_of_nonneg hw (summable_half_weight hx)]
    exact ENNReal.ofReal_lt_top
  have hfin' : (Measure.sum fun n : ℕ => ENNReal.ofReal (zetaBoundaryWeight x n / 2) •
      Measure.dirac (-logFrequency n)) univ < ⊤ := by
    rw [Measure.sum_apply _ MeasurableSet.univ]
    simp only [Measure.smul_apply, Measure.dirac_apply_of_mem (mem_univ _), smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_tsum_of_nonneg hw (summable_half_weight hx)]
    exact ENNReal.ofReal_lt_top
  refine ⟨?_⟩
  rw [primeMeasure, Measure.add_apply]
  exact ENNReal.add_lt_top.mpr ⟨hfin, hfin'⟩

/-- **The prime side is positive.** The characteristic function of the prime measure is the
height function of multiplicative positivity. -/
theorem charFun_primeMeasure {x : ℝ} (hx : 0 < x) (u : ℝ) :
    charFun (primeMeasure x) u = (zetaRealLogDeriv (1 + x) u : ℂ) := by
  set w := zetaBoundaryWeight x
  have hint : ∀ s : ℝ, Integrable (fun y : ℝ => cexp (u * y * I))
      (Measure.sum fun n : ℕ => ENNReal.ofReal (w n / 2) • Measure.dirac (s * logFrequency n)) := by
    intro s
    rw [integrable_sum_dirac_iff (fun _ => ENNReal.ofReal_ne_top)]
    refine (summable_half_weight hx).congr fun n => ?_
    rw [toReal_half_weight, show (u : ℂ) * ((s * logFrequency n : ℝ) : ℂ) * I =
      ((u * (s * logFrequency n) : ℝ) : ℂ) * I by push_cast; ring, Complex.norm_exp_ofReal_mul_I,
      mul_one]
  have hsum : ∀ s : ℝ, Summable fun n : ℕ => (ENNReal.ofReal (w n / 2)).toReal •
      cexp (u * ((s * logFrequency n : ℝ) : ℂ) * I) := by
    intro s
    refine Summable.of_norm ((summable_half_weight hx).congr fun n => ?_)
    rw [norm_smul, toReal_half_weight, show (u : ℂ) * ((s * logFrequency n : ℝ) : ℂ) * I =
      ((u * (s * logFrequency n) : ℝ) : ℂ) * I by push_cast; ring, Complex.norm_exp_ofReal_mul_I,
      mul_one, Real.norm_of_nonneg (by have := zetaBoundaryWeight_nonneg x n; positivity)]
  have e1 : (Measure.sum fun n : ℕ => ENNReal.ofReal (w n / 2) •
      Measure.dirac (logFrequency n)) = Measure.sum fun n : ℕ =>
        ENNReal.ofReal (w n / 2) • Measure.dirac (1 * logFrequency n) := by
    simp only [one_mul]
  have e2 : (Measure.sum fun n : ℕ => ENNReal.ofReal (w n / 2) •
      Measure.dirac (-logFrequency n)) = Measure.sum fun n : ℕ =>
        ENNReal.ofReal (w n / 2) • Measure.dirac ((-1) * logFrequency n) := by
    simp only [neg_one_mul]
  rw [charFun_apply_real, primeMeasure, e1, e2, integral_add_measure (hint 1) (hint (-1)),
    integral_sum_dirac (fun _ => ENNReal.ofReal_ne_top),
    integral_sum_dirac (fun _ => ENNReal.ofReal_ne_top), ← (hsum 1).tsum_add (hsum (-1)),
    zetaRealLogDeriv_eq_cosineTrace hx, cosineTrace, Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  have hθ1 : (u : ℂ) * ((1 * logFrequency n : ℝ) : ℂ) * I = ((logFrequency n * u : ℝ) : ℂ) * I := by
    push_cast; ring
  have hθ2 : (u : ℂ) * (((-1) * logFrequency n : ℝ) : ℂ) * I =
      -((logFrequency n * u : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [hθ1, hθ2, toReal_half_weight, Complex.real_smul, Complex.real_smul,
    show ((zetaBoundaryWeight x n * Real.cos (logFrequency n * u) : ℝ) : ℂ) =
      (zetaBoundaryWeight x n : ℂ) * Complex.cos ((logFrequency n * u : ℝ) : ℂ) by push_cast; ring,
    Complex.cos]
  push_cast
  ring

/-- **Positivity on both sides of the explicit formula.** The prime side is the characteristic
function of a finite positive measure at every damping, unconditionally; the zero side is one, for
every test, exactly under RH. -/
theorem positive_duality_of_the_explicit_formula :
    (∀ x : ℝ, 0 < x → IsFiniteMeasure (primeMeasure x) ∧
      ∀ u, charFun (primeMeasure x) u = (zetaRealLogDeriv (1 + x) u : ℂ)) ∧
    (RiemannHypothesis ↔ ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f →
      ∃ ν : Measure ℝ, IsFiniteMeasure ν ∧
        ∀ y, charFun ν y = RHTower.WeilSpectral.spectralKernel
          (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) f y) :=
  ⟨fun _ hx => ⟨isFiniteMeasure_primeMeasure hx, charFun_primeMeasure hx⟩,
    RHTower.riemannHypothesis_iff_weilPositiveFull_vonMangoldt.trans
      (RHTower.weilPositiveFull_iff_forall_exists_spectralMeasure _)⟩

/-- **The gap is on the prime side.** On tests vanishing for `|x| ≥ log 2`, Weil's functional has
no prime term: only the pole and the archimedean term remain. -/
theorem weilFullFunctional_of_prime_free (lam : ℕ → ℝ) {k : ℝ → ℂ}
    (hk : ∀ x, Real.log 2 ≤ |x| → k x = 0) :
    RHTower.weilFullFunctional lam k = Zeta23.paperFT k (I / 2) + Zeta23.paperFT k (-I / 2) +
      (1 / (2 * π) : ℂ) * ∫ r : ℝ, Zeta23.paperFT k r * (Zeta23.EF.gammaBracket r : ℂ) := by
  unfold RHTower.weilFullFunctional
  have hzero : ∀ n : ℕ, ((if 2 ≤ n then lam n / Real.sqrt n else 0 : ℝ) : ℂ) *
      (k (Real.log n) + k (-Real.log n)) = 0 := by
    intro n
    by_cases hn : 2 ≤ n
    · have hlog : Real.log 2 ≤ |Real.log n| := by
        rw [abs_of_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n)))]
        exact Real.log_le_log (by norm_num) (by exact_mod_cast hn)
      rw [hk _ hlog, hk _ (by rwa [abs_neg]), add_zero, mul_zero]
    · rw [if_neg hn, Complex.ofReal_zero, zero_mul]
  simp only [hzero, tsum_zero, sub_zero]

end GaloisForLFunctions.ArithmeticPositiveDuality
