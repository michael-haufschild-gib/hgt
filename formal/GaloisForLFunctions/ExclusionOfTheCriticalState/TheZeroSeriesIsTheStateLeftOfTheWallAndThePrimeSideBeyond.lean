import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import GaloisForLFunctions.ExclusionOfTheCriticalState.TwoVerticalLinesCutOutTheZeroSeriesOfTheState
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheStateChangesSignOnEveryRay
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheLeftContinuationHasSquareIntegrableVerticalTraces

/-!
# The zero series is the state left of the wall and the prime side beyond it

Let `k_ε(x) = (4πε)^{-1/2} e^{-x²/(4ε)}` be the heat kernel of the line. For the critical state `F`,
every `ε > 0` and every real `T`,

  `Σ_z L F(z) e^{εz² − zT} = a (∫_{x>0} k_ε(x − T) F⁺(x) dx − ∫_{u<0} k_ε(u − T) e^{−8u} F(u) du)`,

the sum over the centred zeros with multiplicity. Here `F⁺` is the profile whose Laplace transform
is the continuation of `L F` beyond the zero strip: the archimedean head and the prime heads of
`F` minus its two charges. The left side is the series `Σ_z L F(z) e^{−zu}` heated for time `ε`, so
as distributions on the line

  `Σ_z L F(z) e^{−zu} = a (F⁺(u) 1_{u>0} − e^{−8u} F(u) 1_{u<0})`:

one series, the state on one side of the wall and the prime side on the other.

Left of the wall the prime side enters through a Gaussian only: for `T ≤ −4ε`,

  `|∫ k_ε(u − T) e^{−8u} F(u) du + a⁻¹ Σ_z L F(z) e^{εz² − zT}| ≤ ‖F⁺ e^{−x}‖₂ · k_ε(T)`.

Mechanism. The two lines `Re p = 5` and `Re p = −2` weigh the zero values against the entire test
`e^{εp² − pT}`. On each line the transform is a Laplace integral, and
`∫ e^{ε(σ+it)² + (σ+it)(x − T)} dt = 2π k_ε(x − T)` for every `σ`, so by Fubini each line integral is
a heat average. For the Gaussian bound the left line is moved to `Re p = T/(2ε)`, where the
continuation is bounded by the `L²` norm of its datum.
-/

noncomputable section
open MeasureTheory Set Filter Zeta23 Complex Metric Topology

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-! ### The Gaussian test and the heat kernel -/

/-- The Gaussian test `e^{εp² − pT}` in the transform variable. -/
def stateHeatSymbol (ε T : ℝ) (p : ℂ) : ℂ := Complex.exp ((ε : ℂ) * p ^ 2 - p * (T : ℂ))

theorem differentiable_stateHeatSymbol (ε T : ℝ) : Differentiable ℂ (stateHeatSymbol ε T) := by
  unfold stateHeatSymbol
  fun_prop

/-- Real and imaginary part of the exponent on a vertical line. -/
theorem stateHeatSymbol_line (ε T σ t : ℝ) :
    stateHeatSymbol ε T (σ + t * I) = Complex.exp (((ε * (σ ^ 2 - t ^ 2) - σ * T : ℝ) : ℂ) +
      ((2 * ε * σ * t - t * T : ℝ) : ℂ) * I) := by
  unfold stateHeatSymbol
  congr 1
  push_cast
  linear_combination (ε : ℂ) * (t : ℂ) ^ 2 * Complex.I_sq

theorem norm_stateHeatSymbol (ε T σ t : ℝ) :
    ‖stateHeatSymbol ε T (σ + t * I)‖ = Real.exp (ε * (σ ^ 2 - t ^ 2) - σ * T) := by
  rw [stateHeatSymbol_line, Complex.norm_exp, Complex.add_re, Complex.ofReal_re,
    Complex.re_ofReal_mul, Complex.I_re, mul_zero, add_zero]

/-- A Gaussian decays at fourth order: `e^{−εt²} ≤ min(1, ε/2)⁻² (1 + t²)⁻²`. -/
theorem exp_neg_mul_sq_le_inv_sq {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    Real.exp (-(ε * t ^ 2)) ≤ ((min 1 (ε / 2)) ^ 2)⁻¹ / (1 + t ^ 2) ^ 2 := by
  have hm0 : 0 < min 1 (ε / 2) := lt_min one_pos (by linarith)
  have hm1 : min 1 (ε / 2) ≤ 1 := min_le_left _ _
  have hm2 : min 1 (ε / 2) ≤ ε / 2 := min_le_right _ _
  have ht : 0 ≤ t ^ 2 := sq_nonneg t
  have h1 : min 1 (ε / 2) * (1 + t ^ 2) ≤ Real.exp (ε * t ^ 2 / 2) := by
    have e : min 1 (ε / 2) * (1 + t ^ 2) = min 1 (ε / 2) + min 1 (ε / 2) * t ^ 2 := by ring
    rw [e]
    linarith [mul_le_mul_of_nonneg_right hm2 ht, Real.add_one_le_exp (ε * t ^ 2 / 2)]
  have h2 : (min 1 (ε / 2) * (1 + t ^ 2)) ^ 2 ≤ Real.exp (ε * t ^ 2) := by
    have h3 := pow_le_pow_left₀ (by positivity) h1 2
    have e : Real.exp (ε * t ^ 2 / 2) ^ 2 = Real.exp (ε * t ^ 2) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rwa [e] at h3
  rw [Real.exp_neg, div_eq_mul_inv, ← mul_inv, ← mul_pow]
  exact inv_anti₀ (by positivity) h2

/-- Fourth-order decay of the Gaussian test, uniformly on a vertical strip. -/
theorem norm_stateHeatSymbol_strip_le {ε : ℝ} (hε : 0 < ε) (T : ℝ) {a b σ : ℝ} (ha : a ≤ σ)
    (hb : σ ≤ b) (t : ℝ) :
    ‖stateHeatSymbol ε T (σ + t * I)‖ ≤
      Real.exp (ε * (a ^ 2 + b ^ 2) + (|a| + |b|) * |T|) * ((min 1 (ε / 2)) ^ 2)⁻¹ /
        (1 + t ^ 2) ^ 2 := by
  have hσ2 : σ ^ 2 ≤ a ^ 2 + b ^ 2 := by
    rcases le_total 0 σ with h | h
    · nlinarith [sq_nonneg a]
    · nlinarith [sq_nonneg b]
  have hσabs : |σ| ≤ |a| + |b| :=
    abs_le.mpr ⟨by linarith [neg_abs_le a, abs_nonneg b], by linarith [le_abs_self b, abs_nonneg a]⟩
  have hσT : -(σ * T) ≤ (|a| + |b|) * |T| := by
    have h1 : -(σ * T) ≤ |σ| * |T| := by
      rw [← abs_mul]
      exact neg_le_abs (σ * T)
    exact h1.trans (mul_le_mul_of_nonneg_right hσabs (abs_nonneg T))
  have hexp : Real.exp (ε * (σ ^ 2 - t ^ 2) - σ * T) ≤
      Real.exp (ε * (a ^ 2 + b ^ 2) + (|a| + |b|) * |T|) * Real.exp (-(ε * t ^ 2)) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    nlinarith [mul_le_mul_of_nonneg_left hσ2 hε.le]
  rw [norm_stateHeatSymbol, mul_div_assoc]
  exact hexp.trans (mul_le_mul_of_nonneg_left (exp_neg_mul_sq_le_inv_sq hε t) (Real.exp_pos _).le)

/-- The heat kernel of the line, `(4πε)^{-1/2} e^{−x²/(4ε)}`. -/
def stateHeatKernel (ε x : ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * Real.sqrt (Real.pi / ε) * Real.exp (-(x ^ 2 / (4 * ε)))

/-- On every vertical line the Gaussian test against an exponential integrates to the heat
kernel: `∫ e^{ε(σ+it)² + (σ+it)(x − T)} dt = 2π k_ε(x − T)`. -/
theorem integral_stateHeatSymbol_mul_cexp {ε : ℝ} (hε : 0 < ε) (T σ x : ℝ) :
    ∫ t : ℝ, stateHeatSymbol ε T (σ + t * I) * Complex.exp (((σ : ℂ) + t * I) * x) =
      2 * Real.pi * ((stateHeatKernel ε (x - T) : ℝ) : ℂ) := by
  have key : ∀ t : ℝ, stateHeatSymbol ε T (σ + t * I) * Complex.exp (((σ : ℂ) + t * I) * x) =
      Complex.exp (-(ε : ℂ) * (t : ℂ) ^ 2 + (I * (2 * ε * σ + (x - T))) * t +
        (ε * σ ^ 2 + σ * (x - T))) := by
    intro t
    unfold stateHeatSymbol
    rw [← Complex.exp_add]
    congr 1
    linear_combination (ε : ℂ) * (t : ℂ) ^ 2 * Complex.I_sq
  have hb : (-(ε : ℂ)).re < 0 := by
    rw [Complex.neg_re, Complex.ofReal_re]
    linarith
  have hε' : (ε : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hε.ne'
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hsq : ((Real.pi : ℂ) / -(-(ε : ℂ))) ^ (1 / 2 : ℂ) = ((Real.sqrt (Real.pi / ε) : ℝ) : ℂ) := by
    rw [neg_neg, ← Complex.ofReal_div, Real.sqrt_eq_rpow,
      Complex.ofReal_cpow (div_nonneg Real.pi_pos.le hε.le)]
    norm_num
  have hI : (I * (2 * (ε : ℂ) * σ + ((x : ℂ) - T))) ^ 2 = -((2 * (ε : ℂ) * σ + ((x : ℂ) - T)) ^ 2) := by
    rw [mul_pow, Complex.I_sq]
    ring
  have hexp : ((ε : ℂ) * σ ^ 2 + σ * ((x : ℂ) - T)) -
      (I * (2 * (ε : ℂ) * σ + ((x : ℂ) - T))) ^ 2 / (4 * -(ε : ℂ)) =
        ((-((x - T) ^ 2 / (4 * ε)) : ℝ) : ℂ) := by
    rw [hI]
    push_cast
    field_simp
    ring
  rw [integral_congr_ae (Eventually.of_forall key), integral_cexp_quadratic hb, hsq, hexp,
    ← Complex.ofReal_exp]
  unfold stateHeatKernel
  push_cast
  field_simp

/-- **A Gaussian line integral of a Laplace integral is a heat average.** If `e^{σx} |φ(x)|` is
integrable for `μ`, then `∫ e^{εp² − pT} (∫ e^{px} φ(x) dμ) dt = 2π ∫ k_ε(x − T) φ(x) dμ` on `p = σ + it`. -/
theorem integral_stateHeatSymbol_mul_laplace {μ : Measure ℝ} [SFinite μ] {ε : ℝ} (hε : 0 < ε)
    (T σ : ℝ) {φ : ℝ → ℂ} (hφm : AEStronglyMeasurable φ μ)
    (hφ : Integrable (fun x => Real.exp (σ * x) * ‖φ x‖) μ) :
    ∫ t : ℝ, stateHeatSymbol ε T (σ + t * I) * ∫ x : ℝ, Complex.exp (((σ : ℂ) + t * I) * x) * φ x ∂μ =
      2 * Real.pi * ∫ x : ℝ, ((stateHeatKernel ε (x - T) : ℝ) : ℂ) * φ x ∂μ := by
  have hG : Integrable (Function.uncurry fun (t x : ℝ) =>
      stateHeatSymbol ε T (σ + t * I) * (Complex.exp (((σ : ℂ) + t * I) * x) * φ x))
      ((volume : Measure ℝ).prod μ) := by
    have hg1 : Integrable (fun t : ℝ => Real.exp (ε * σ ^ 2 - σ * T) * Real.exp (-ε * t ^ 2)) :=
      (integrable_exp_neg_mul_sq hε).const_mul _
    have hmaj := hg1.mul_prod hφ
    refine hmaj.mono' ?_ (Eventually.of_forall fun z => ?_)
    · have hK : Continuous fun z : ℝ × ℝ =>
          stateHeatSymbol ε T (σ + z.1 * I) * Complex.exp (((σ : ℂ) + z.1 * I) * z.2) := by
        unfold stateHeatSymbol
        fun_prop
      have hm := (hK.aestronglyMeasurable (μ := (volume : Measure ℝ).prod μ)).mul hφm.comp_snd
      refine hm.congr (Eventually.of_forall fun z => ?_)
      show stateHeatSymbol ε T (σ + z.1 * I) * Complex.exp (((σ : ℂ) + z.1 * I) * z.2) * φ z.2 =
        stateHeatSymbol ε T (σ + z.1 * I) * (Complex.exp (((σ : ℂ) + z.1 * I) * z.2) * φ z.2)
      ring
    · show ‖stateHeatSymbol ε T (σ + z.1 * I) * (Complex.exp (((σ : ℂ) + z.1 * I) * z.2) * φ z.2)‖ ≤
        Real.exp (ε * σ ^ 2 - σ * T) * Real.exp (-ε * z.1 ^ 2) * (Real.exp (σ * z.2) * ‖φ z.2‖)
      have hre : (((σ : ℂ) + z.1 * I) * z.2).re = σ * z.2 := by simp
      rw [norm_mul, norm_mul, norm_stateHeatSymbol, Complex.norm_exp, hre,
        show ε * (σ ^ 2 - z.1 ^ 2) - σ * T = (ε * σ ^ 2 - σ * T) + -ε * z.1 ^ 2 by ring,
        Real.exp_add]
  calc ∫ t : ℝ, stateHeatSymbol ε T (σ + t * I) * ∫ x : ℝ, Complex.exp (((σ : ℂ) + t * I) * x) * φ x ∂μ
      = ∫ t : ℝ, ∫ x : ℝ, stateHeatSymbol ε T (σ + t * I) *
          (Complex.exp (((σ : ℂ) + t * I) * x) * φ x) ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun t => ?_)
        exact (integral_const_mul _ _).symm
    _ = ∫ x : ℝ, (∫ t : ℝ, stateHeatSymbol ε T (σ + t * I) *
          (Complex.exp (((σ : ℂ) + t * I) * x) * φ x)) ∂μ := integral_integral_swap hG
    _ = ∫ x : ℝ, 2 * Real.pi * ((stateHeatKernel ε (x - T) : ℝ) : ℂ) * φ x ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        show (∫ t : ℝ, stateHeatSymbol ε T (σ + t * I) *
            (Complex.exp (((σ : ℂ) + t * I) * x) * φ x)) =
          2 * Real.pi * ((stateHeatKernel ε (x - T) : ℝ) : ℂ) * φ x
        rw [← integral_stateHeatSymbol_mul_cexp hε T σ x, ← integral_mul_const]
        refine integral_congr_ae (Eventually.of_forall fun t => ?_)
        show stateHeatSymbol ε T (σ + t * I) * (Complex.exp (((σ : ℂ) + t * I) * x) * φ x) =
          stateHeatSymbol ε T (σ + t * I) * Complex.exp (((σ : ℂ) + t * I) * x) * φ x
        ring
    _ = 2 * Real.pi * ∫ x : ℝ, ((stateHeatKernel ε (x - T) : ℝ) : ℂ) * φ x ∂μ := by
        rw [← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        show 2 * Real.pi * ((stateHeatKernel ε (x - T) : ℝ) : ℂ) * φ x =
          2 * Real.pi * (((stateHeatKernel ε (x - T) : ℝ) : ℂ) * φ x)
        ring

/-! ### The right line: the state -/

/-- The state weighted by `e^{−8u}` and heated for time `ε`: `∫ k_ε(u − T) e^{−8u} F(u) du`. -/
def heatedState (ε : ℝ) (F : ℝ → ℝ) (T : ℝ) : ℝ :=
  ∫ u : ℝ, stateHeatKernel ε (u - T) * (Real.exp (-(8 * u)) * F u)

theorem aestronglyMeasurable_dampedState {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) :
    AEStronglyMeasurable (fun u : ℝ => ((Real.exp (-(8 * u)) * F u : ℝ) : ℂ)) volume :=
  (Complex.measurable_ofReal.comp
    ((by fun_prop : Measurable fun u : ℝ => Real.exp (-(8 * u))).mul hF.meas)).aestronglyMeasurable

/-- The state in the weight of the confinement has a Laplace integral right of `Re p = 4`. -/
theorem integrable_exp_mul_dampedState {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {b : ℝ}
    (hb : 4 < b) :
    Integrable (fun u : ℝ => Real.exp (b * u) * ‖((Real.exp (-(8 * u)) * F u : ℝ) : ℂ)‖) := by
  refine (integrable_abs_mul_exp_of_domain hF (c := b - 8) (by linarith)).congr
    (Eventually.of_forall fun u => ?_)
  show |F u| * Real.exp ((b - 8) * u) =
    Real.exp (b * u) * ‖((Real.exp (-(8 * u)) * F u : ℝ) : ℂ)‖
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _),
    show (b - 8) * u = b * u + -(8 * u) by ring, Real.exp_add]
  ring

/-- The transform shifted by `8` is the Laplace integral of `e^{−8u} F(u)`. -/
theorem laplace_sub_eight_eq_integral (F : ℝ → ℝ) (b t : ℝ) :
    negativeHalfLineLaplace (cx F) (b + t * I - 8) =
      ∫ u : ℝ, Complex.exp (((b : ℂ) + t * I) * u) * ((Real.exp (-(8 * u)) * F u : ℝ) : ℂ) := by
  unfold negativeHalfLineLaplace
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  show Complex.exp (((b : ℂ) + t * I - 8) * (u : ℂ)) * ((F u : ℝ) : ℂ) =
    Complex.exp (((b : ℂ) + t * I) * u) * ((Real.exp (-(8 * u)) * F u : ℝ) : ℂ)
  have hx : ((b : ℂ) + t * I - 8) * (u : ℂ) =
      ((b : ℂ) + t * I) * u + ((-(8 * u) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [Complex.ofReal_mul, Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add, hx]

/-- Right of `Re p = 4` the Gaussian line integral of the shifted transform is the heated state. -/
theorem integral_stateHeatSymbol_mul_laplace_right {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {ε : ℝ} (hε : 0 < ε) (T : ℝ) {b : ℝ} (hb : 4 < b) :
    ∫ t : ℝ, stateHeatSymbol ε T (b + t * I) * negativeHalfLineLaplace (cx F) (b + t * I - 8) =
      2 * Real.pi * ((heatedState ε F T : ℝ) : ℂ) := by
  have h := integral_stateHeatSymbol_mul_laplace (μ := volume) hε T b
    (aestronglyMeasurable_dampedState hF) (integrable_exp_mul_dampedState hF hb)
  have e2 : (∫ u : ℝ, ((stateHeatKernel ε (u - T) : ℝ) : ℂ) *
        ((Real.exp (-(8 * u)) * F u : ℝ) : ℂ)) = ((heatedState ε F T : ℝ) : ℂ) := by
    have h1 : (∫ u : ℝ, ((stateHeatKernel ε (u - T) * (Real.exp (-(8 * u)) * F u) : ℝ) : ℂ)) =
        ((heatedState ε F T : ℝ) : ℂ) := integral_ofReal
    rw [← h1]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    show ((stateHeatKernel ε (u - T) : ℝ) : ℂ) * ((Real.exp (-(8 * u)) * F u : ℝ) : ℂ) =
      ((stateHeatKernel ε (u - T) * (Real.exp (-(8 * u)) * F u) : ℝ) : ℂ)
    rw [Complex.ofReal_mul (stateHeatKernel ε (u - T))]
  rw [← e2, ← h]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  show stateHeatSymbol ε T (b + t * I) * negativeHalfLineLaplace (cx F) (b + t * I - 8) =
    stateHeatSymbol ε T (b + t * I) *
      ∫ u : ℝ, Complex.exp (((b : ℂ) + t * I) * u) * ((Real.exp (-(8 * u)) * F u : ℝ) : ℂ)
  rw [laplace_sub_eight_eq_integral F b t]

/-! ### The left line: the prime side beyond the wall -/

/-- The half-line datum of the continuation, damped at rate `1`. -/
def unitLeftDatum (W₀ : ℝ) {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) :
    Lp ℂ 2 halfLineLaplaceMeasure :=
  leftContinuationDatum hF (c := 1) (by norm_num) (by norm_num) W₀

/-- The profile beyond the wall: the archimedean head and the prime heads of the profile minus its
two charges, divided by `−a`. The continuation of the transform beyond the zero strip is its
Laplace transform, `∫_{x>0} F⁺(x) e^{(w + 8)x} dx` for `Re w < −9`. -/
def beyondWallProfile (W₀ : ℝ) {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) (x : ℝ) : ℂ :=
  Complex.exp (x : ℂ) * (unitLeftDatum W₀ hF : ℝ → ℂ) x

/-- The profile beyond the wall heated for time `ε`: `∫_{x>0} k_ε(x − T) F⁺(x) dx`. -/
def heatedBeyondWall (ε W₀ : ℝ) {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) (T : ℝ) : ℂ :=
  ∫ x : ℝ in Ioi (0 : ℝ), ((stateHeatKernel ε (x - T) : ℝ) : ℂ) * beyondWallProfile W₀ hF x

theorem aestronglyMeasurable_beyondWallProfile (W₀ : ℝ) {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) :
    AEStronglyMeasurable (beyondWallProfile W₀ hF) (volume.restrict (Ioi (0 : ℝ))) := by
  have hD : MemLp (unitLeftDatum W₀ hF : ℝ → ℂ) 2 (volume.restrict (Ioi (0 : ℝ))) :=
    Lp.memLp (unitLeftDatum W₀ hF)
  have h : AEStronglyMeasurable
      (fun x : ℝ => Complex.exp (x : ℂ) * (unitLeftDatum W₀ hF : ℝ → ℂ) x)
      (volume.restrict (Ioi (0 : ℝ))) :=
    ((by fun_prop : Continuous fun x : ℝ => Complex.exp (x : ℂ)).aestronglyMeasurable).mul
      hD.aestronglyMeasurable
  exact h

/-- The profile beyond the wall has a Laplace integral left of `Re p = −1`. -/
theorem integrable_exp_mul_beyondWallProfile (W₀ : ℝ) {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {a : ℝ} (ha : a < -1) :
    Integrable (fun x : ℝ => Real.exp (a * x) * ‖beyondWallProfile W₀ hF x‖)
      (volume.restrict (Ioi (0 : ℝ))) := by
  have hD : MemLp (unitLeftDatum W₀ hF : ℝ → ℂ) 2 (volume.restrict (Ioi (0 : ℝ))) :=
    Lp.memLp (unitLeftDatum W₀ hF)
  have hw : 0 < ((-a - 1 : ℝ) : ℂ).re := by
    rw [Complex.ofReal_re]
    linarith
  have hI : Integrable
      (fun x : ℝ => (unitLeftDatum W₀ hF : ℝ → ℂ) x * expRay ((-a - 1 : ℝ) : ℂ) x)
      (volume.restrict (Ioi (0 : ℝ))) := integrableOn_laplaceRay hD hw
  refine hI.norm.congr (Eventually.of_forall fun x => ?_)
  show ‖(unitLeftDatum W₀ hF : ℝ → ℂ) x * expRay ((-a - 1 : ℝ) : ℂ) x‖ =
    Real.exp (a * x) * ‖beyondWallProfile W₀ hF x‖
  unfold beyondWallProfile
  rw [norm_mul, norm_mul, norm_expRay, Complex.norm_exp, Complex.ofReal_re, Complex.ofReal_re,
    show -((-a - 1) * x) = a * x + x by ring, Real.exp_add]
  ring

/-- Left of `Re p = −1` the continuation is the Laplace integral of the profile beyond the wall. -/
theorem stateMeromorphic_eq_integral_beyondWallProfile {W₀ : ℝ} {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {a : ℝ} (ha : a < -1) (t : ℝ) :
    stateMeromorphic W₀ F (a + t * I - 8) =
      ∫ x : ℝ in Ioi (0 : ℝ), Complex.exp (((a : ℂ) + t * I) * x) * beyondWallProfile W₀ hF x := by
  have hzre : (-((a : ℂ) + t * I) - 1).re = -a - 1 := by simp
  have hz : 0 < (-((a : ℂ) + t * I) - 1).re := by
    rw [hzre]
    linarith
  have hs := stateMeromorphic_eq_laplaceRay_left (W₀ := W₀) hF (c := 1) (by norm_num)
    (by norm_num) hz
  have hp : -(-((a : ℂ) + t * I) - 1 + ((1 : ℝ) : ℂ)) - 8 = (a : ℂ) + t * I - 8 := by
    push_cast
    ring
  rw [hp] at hs
  rw [hs]
  unfold laplaceRay
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  show (unitLeftDatum W₀ hF : ℝ → ℂ) x * expRay (-((a : ℂ) + t * I) - 1) x =
    Complex.exp (((a : ℂ) + t * I) * x) * beyondWallProfile W₀ hF x
  unfold beyondWallProfile expRay
  have hx : -((-((a : ℂ) + t * I) - 1) * (x : ℂ)) = ((a : ℂ) + t * I) * x + x := by ring
  rw [hx, Complex.exp_add]
  ring

/-- Left of `Re p = −1` the Gaussian line integral of the continuation is the heated profile beyond
the wall. -/
theorem integral_stateHeatSymbol_mul_stateMeromorphic_left {W₀ : ℝ} {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {ε : ℝ} (hε : 0 < ε) (T : ℝ) {a : ℝ} (ha : a < -1) :
    ∫ t : ℝ, stateHeatSymbol ε T (a + t * I) * stateMeromorphic W₀ F (a + t * I - 8) =
      2 * Real.pi * heatedBeyondWall ε W₀ hF T := by
  have h := integral_stateHeatSymbol_mul_laplace (μ := volume.restrict (Ioi (0 : ℝ))) hε T a
    (φ := beyondWallProfile W₀ hF) (aestronglyMeasurable_beyondWallProfile W₀ hF)
    (integrable_exp_mul_beyondWallProfile W₀ hF ha)
  unfold heatedBeyondWall
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  show stateHeatSymbol ε T (a + t * I) * stateMeromorphic W₀ F (a + t * I - 8) =
    stateHeatSymbol ε T (a + t * I) *
      ∫ x : ℝ in Ioi (0 : ℝ), Complex.exp (((a : ℂ) + t * I) * x) * beyondWallProfile W₀ hF x
  rw [stateMeromorphic_eq_integral_beyondWallProfile hF ha t]

/-! ### The zero series on both sides of the wall -/

/-- **The zero series is the state left of the wall and the prime side beyond it.** For the
critical state, every `ε > 0` and every real `T`:
`Σ_z L F(z) e^{εz² − zT} = a (∫_{x>0} k_ε(x − T) F⁺(x) dx − ∫_{u<0} k_ε(u − T) e^{−8u} F(u) du)`. -/
theorem criticalState_hasSum_heated_zeroSeries {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {ε : ℝ} (hε : 0 < ε) (T : ℝ) :
    HasSum (fun q : XiZeroCopy =>
        negativeHalfLineLaplace (cx F) (centredZero q) * stateHeatSymbol ε T (centredZero q))
      ((criticalAliasCoefficient W₀ : ℂ) *
        (heatedBeyondWall ε W₀ (criticalHalfLineEnergyDomain_of_groundState hF) T -
          ((heatedState ε F T : ℝ) : ℂ))) := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have h := criticalState_hasSum_zeroValues_two_lines hW hthreshold hF
    (differentiable_stateHeatSymbol ε T) (a := -2) (b := 5) (by norm_num) (by norm_num)
    (fun σ t h1 h2 => norm_stateHeatSymbol_strip_le hε T h1 h2 t)
  have hR := integral_stateHeatSymbol_mul_laplace_right hd hε T (b := 5) (by norm_num)
  have hL := integral_stateHeatSymbol_mul_stateMeromorphic_left (W₀ := W₀) hd hε T (a := -2)
    (by norm_num)
  rw [hR, hL] at h
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hc : (criticalAliasCoefficient W₀ : ℂ) / (2 * Real.pi) * (2 * Real.pi) =
      (criticalAliasCoefficient W₀ : ℂ) := by
    field_simp
  convert h using 1
  linear_combination (((heatedState ε F T : ℝ) : ℂ) - heatedBeyondWall ε W₀ hd T) * hc

/-- Left of the wall the prime side is a Gaussian: for `T ≤ −4ε` the heated profile beyond the
wall is at most `‖F⁺ e^{−x}‖₂ · k_ε(T)`. The left line is moved to `Re p = T/(2ε)`. -/
theorem norm_heatedBeyondWall_le {W₀ : ℝ} {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    {ε : ℝ} (hε : 0 < ε) {T : ℝ} (hT : T ≤ -(4 * ε)) :
    ‖heatedBeyondWall ε W₀ hF T‖ ≤ rayL2Norm (unitLeftDatum W₀ hF) * stateHeatKernel ε T := by
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = T / (2 * ε) := ⟨_, rfl⟩
  have hT2 : T = a * (2 * ε) := (div_eq_iff (by positivity)).mp ha.symm
  have hq : T ^ 2 / (4 * ε) = ε * a ^ 2 := by
    rw [div_eq_iff (by positivity)]
    linear_combination (T + a * (2 * ε)) * hT2
  have hE : ε * a ^ 2 - a * T = -(T ^ 2 / (4 * ε)) := by
    rw [hq]
    linear_combination (-a) * hT2
  have ha2 : a ≤ -2 := by
    by_contra hcon
    have h3 := mul_lt_mul_of_pos_right (not_le.mp hcon) (by positivity : (0 : ℝ) < 2 * ε)
    rw [← hT2] at h3
    linarith
  have hL := integral_stateHeatSymbol_mul_stateMeromorphic_left (W₀ := W₀) hF hε T (a := a)
    (by linarith)
  have hN := rayL2Norm_nonneg (unitLeftDatum W₀ hF : ℝ → ℂ)
  have hbound : ‖∫ t : ℝ, stateHeatSymbol ε T (a + t * I) *
        stateMeromorphic W₀ F (a + t * I - 8)‖ ≤
      ∫ t : ℝ, Real.exp (ε * a ^ 2 - a * T) * rayL2Norm (unitLeftDatum W₀ hF) *
        Real.exp (-ε * t ^ 2) := by
    refine norm_integral_le_of_norm_le ((integrable_exp_neg_mul_sq hε).const_mul _)
      (Eventually.of_forall fun t => ?_)
    show ‖stateHeatSymbol ε T (a + t * I) * stateMeromorphic W₀ F (a + t * I - 8)‖ ≤
      Real.exp (ε * a ^ 2 - a * T) * rayL2Norm (unitLeftDatum W₀ hF) * Real.exp (-ε * t ^ 2)
    have hre : ((a : ℂ) + t * I - 8).re = a - 8 := by simp
    have hM := norm_stateMeromorphic_left_le (W₀ := W₀) hF (c := 1) (by norm_num) (by norm_num)
      (w := (a : ℂ) + t * I - 8) (by rw [hre]; linarith)
    have hsqrt : 1 ≤ Real.sqrt (2 * (-((a : ℂ) + t * I - 8).re - 1 - 8)) := by
      rw [Real.one_le_sqrt, hre]
      linarith
    have hM' : ‖stateMeromorphic W₀ F (a + t * I - 8)‖ ≤ rayL2Norm (unitLeftDatum W₀ hF) :=
      hM.trans (div_le_self hN hsqrt)
    rw [norm_mul, norm_stateHeatSymbol,
      show ε * (a ^ 2 - t ^ 2) - a * T = (ε * a ^ 2 - a * T) + -ε * t ^ 2 by ring, Real.exp_add]
    calc Real.exp (ε * a ^ 2 - a * T) * Real.exp (-ε * t ^ 2) *
          ‖stateMeromorphic W₀ F (a + t * I - 8)‖
        ≤ Real.exp (ε * a ^ 2 - a * T) * Real.exp (-ε * t ^ 2) *
          rayL2Norm (unitLeftDatum W₀ hF) :=
          mul_le_mul_of_nonneg_left hM' (by positivity)
      _ = Real.exp (ε * a ^ 2 - a * T) * rayL2Norm (unitLeftDatum W₀ hF) *
          Real.exp (-ε * t ^ 2) := by ring
  have h2π : ‖(2 : ℂ) * Real.pi * heatedBeyondWall ε W₀ hF T‖ =
      2 * Real.pi * ‖heatedBeyondWall ε W₀ hF T‖ := by
    rw [norm_mul, norm_mul, Complex.norm_two, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le]
  rw [hL, h2π, integral_const_mul, integral_gaussian, hE] at hbound
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have h3 : ‖heatedBeyondWall ε W₀ hF T‖ ≤
      (Real.exp (-(T ^ 2 / (4 * ε))) * rayL2Norm (unitLeftDatum W₀ hF) *
        Real.sqrt (Real.pi / ε)) / (2 * Real.pi) := by
    rw [le_div_iff₀ hpi, mul_comm]
    exact hbound
  unfold stateHeatKernel
  calc ‖heatedBeyondWall ε W₀ hF T‖
      ≤ (Real.exp (-(T ^ 2 / (4 * ε))) * rayL2Norm (unitLeftDatum W₀ hF) *
        Real.sqrt (Real.pi / ε)) / (2 * Real.pi) := h3
    _ = rayL2Norm (unitLeftDatum W₀ hF) *
        ((2 * Real.pi)⁻¹ * Real.sqrt (Real.pi / ε) * Real.exp (-(T ^ 2 / (4 * ε)))) := by
        rw [div_eq_mul_inv]
        ring

/-- **Left of the wall the heated state is its zero series up to a Gaussian.** For the critical
state, `ε > 0` and `T ≤ −4ε`:
`|∫ k_ε(u − T) e^{−8u} F(u) du + a⁻¹ Σ_z L F(z) e^{εz² − zT}| ≤ ‖F⁺ e^{−x}‖₂ · k_ε(T)`. -/
theorem criticalState_heatedState_add_zeroSeries_le {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {ε : ℝ} (hε : 0 < ε) {T : ℝ}
    (hT : T ≤ -(4 * ε)) :
    ‖((heatedState ε F T : ℝ) : ℂ) + (criticalAliasCoefficient W₀ : ℂ)⁻¹ *
        ∑' q : XiZeroCopy, negativeHalfLineLaplace (cx F) (centredZero q) *
          stateHeatSymbol ε T (centredZero q)‖ ≤
      rayL2Norm (unitLeftDatum W₀ (criticalHalfLineEnergyDomain_of_groundState hF)) *
        stateHeatKernel ε T := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hS := (criticalState_hasSum_heated_zeroSeries hW hthreshold hF hε T).tsum_eq
  have ha0 : (criticalAliasCoefficient W₀ : ℂ) ≠ 0 := by
    exact_mod_cast (criticalAliasCoefficient_positive hW).ne'
  have e : ((heatedState ε F T : ℝ) : ℂ) + (criticalAliasCoefficient W₀ : ℂ)⁻¹ *
      ((criticalAliasCoefficient W₀ : ℂ) * (heatedBeyondWall ε W₀ hd T -
        ((heatedState ε F T : ℝ) : ℂ))) = heatedBeyondWall ε W₀ hd T := by
    rw [← mul_assoc, inv_mul_cancel₀ ha0, one_mul]
    ring
  rw [hS, e]
  exact norm_heatedBeyondWall_le hd hε hT

end GaloisForLFunctions.ExclusionOfTheCriticalState
