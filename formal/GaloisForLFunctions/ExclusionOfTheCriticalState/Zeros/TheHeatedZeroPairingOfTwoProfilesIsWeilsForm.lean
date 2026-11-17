import GaloisForLFunctions.ExclusionOfTheCriticalState.Zeros.TheExplicitFormulaHoldsForTwoSidedTests
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheZeroValuesOfTheStateAreANegativeVectorOfTheZeroPairing
import GaloisForLFunctions.RHTower.WeilConeXiDivisibleBlindTest
import GaloisForLFunctions.ExclusionOfTheCriticalState.ThePrimeHeadsAreHardyTransforms
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# The heated zero pairing of two profiles is Weil's form

For two profiles `F, G` of the energy domain, with Gaussian summation over the centred zeros
(`tendsto_heatedZeroPairing`):

  `lim_{ε→0⁺} Σ_z L F(z) L G(−z) e^{εz²} = W(F, G)`.

No unit tilt and no square-summability of the zero values is assumed.

Mechanism. Fix `ε > 0`. The heated pairing is the zero pairing of `F` against the two-sided test
`k_ε * G`, since `∫ k_ε(y) e^{−zy} dy = e^{εz²}`. Cut the heat kernel by a plateau,
`κ_k = k_ε ψ(·/(k+1))`, and `G` at `−k`: `H_k = κ_k * G_k` is smooth with compact support, so the
explicit formula for two-sided tests gives `Σ_z L F(z) L H_k(−z) = W(F, H_k)`. Two integrations by parts
bound the cut transforms by `M/|z|²` uniformly in `k`, so the zero side tends to the heated pairing.
On the form side the Gamma part tends to `(2π)^{-1}∫ e^{−εr²} Re(F̂ Ĝ̄) γ`, each prime term to the heat
average `∫ k_ε(y) c(±log n + y) dy` of the correlation `c(s) = ∫ F(t) G(t − s) dt`, and the charges
acquire `e^{ε/4}` (`heatedZeroPairing_eq_heatedForm`). As `ε → 0⁺` the factor `e^{−εr²}` tends to
`1` under the Gamma energies, the heat averages tend to `c(±log n)` because `c` is continuous, and the
prime terms are dominated by `Λ(n) n^{−9/2}` since `|c(s)| ≤ C e^{−4|s|}`.
-/

noncomputable section
open MeasureTheory Set Filter Complex Topology Zeta23
open scoped ContDiff

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-! ### Laplace transforms on the zero strip -/

theorem norm_cexp_mul_ofReal_le {w : ℂ} (hw : |w.re| ≤ 1 / 2) (u : ℝ) :
    ‖cexp (w * u)‖ ≤ Real.exp (|u| / 2) := by
  rw [Complex.norm_exp, show (w * (u : ℂ)).re = w.re * u by simp]
  refine Real.exp_le_exp.mpr ((le_abs_self _).trans ?_)
  rw [abs_mul]
  nlinarith [abs_nonneg u]

theorem norm_cexp_mul_cx_le {w : ℂ} (hw : |w.re| ≤ 1 / 2) (f : ℝ → ℝ) (u : ℝ) :
    ‖cexp (w * u) * cx f u‖ ≤ |f u| * Real.exp (|u| / 2) := by
  change ‖cexp (w * u) * ((f u : ℝ) : ℂ)‖ ≤ _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
  exact mul_le_mul_of_nonneg_left (norm_cexp_mul_ofReal_le hw u) (abs_nonneg _)

theorem integrable_cexp_mul_cx {f : ℝ → ℝ} (hfm : AEStronglyMeasurable f volume)
    (hf : Integrable fun u => |f u| * Real.exp (|u| / 2)) {w : ℂ} (hw : |w.re| ≤ 1 / 2) :
    Integrable fun u : ℝ => cexp (w * u) * cx f u :=
  hf.mono' ((by fun_prop : Continuous fun u : ℝ => cexp (w * u)).aestronglyMeasurable.mul
    (Complex.continuous_ofReal.comp_aestronglyMeasurable hfm))
    (Eventually.of_forall fun u => norm_cexp_mul_cx_le hw f u)

theorem norm_laplace_le {f : ℝ → ℝ} (hf : Integrable fun u => |f u| * Real.exp (|u| / 2))
    {w : ℂ} (hw : |w.re| ≤ 1 / 2) :
    ‖negativeHalfLineLaplace (cx f) w‖ ≤ ∫ u, |f u| * Real.exp (|u| / 2) := by
  unfold negativeHalfLineLaplace
  exact (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun u => norm_nonneg _) hf
    (Eventually.of_forall fun u => norm_cexp_mul_cx_le hw f u))

theorem integrable_abs_mul_exp_abs_half_of_domain {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) :
    Integrable fun u => |F u| * Real.exp (|u| / 2) := by
  refine (integrable_abs_mul_exp_of_domain hF (c := -(1 / 2)) (by norm_num)).congr
    (Eventually.of_forall fun u => ?_)
  show |F u| * Real.exp (-(1 / 2) * u) = |F u| * Real.exp (|u| / 2)
  rcases lt_or_ge u 0 with hu | hu
  · rw [abs_of_neg hu]; congr 2; ring
  · rw [hF.support u hu, abs_zero, zero_mul, zero_mul]

/-- **The Laplace transform of a convolution is the product of the transforms.** -/
theorem laplace_convolution {f g : ℝ → ℝ} {w : ℂ}
    (hf : Integrable fun u : ℝ => cexp (w * u) * cx f u)
    (hg : Integrable fun u : ℝ => cexp (w * u) * cx g u) :
    negativeHalfLineLaplace (cx (convolution f g (ContinuousLinearMap.mul ℝ ℝ) volume)) w =
      negativeHalfLineLaplace (cx f) w * negativeHalfLineLaplace (cx g) w := by
  have h := integral_convolution (L := ContinuousLinearMap.mul ℝ ℂ) (μ := volume) (ν := volume)
    hf hg
  rw [ContinuousLinearMap.mul_apply'] at h
  unfold negativeHalfLineLaplace
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [convolution_def, ContinuousLinearMap.mul_apply', cx]
  rw [← integral_complex_ofReal, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  have he : cexp (w * x) = cexp (w * t) * cexp (w * ((x : ℂ) - t)) := by
    rw [← Complex.exp_add]; congr 1; ring
  simp only
  push_cast
  rw [he]
  ring

/-! ### The heat kernel -/

/-- **The heat kernel is the Laplace transform of the Gaussian:** `∫ k_ε(y) e^{wy} dy = e^{εw²}`. -/
theorem laplace_stateHeatKernel {ε : ℝ} (hε : 0 < ε) (w : ℂ) :
    negativeHalfLineLaplace (cx (stateHeatKernel ε)) w = cexp (ε * w ^ 2) := by
  set A : ℝ := (2 * Real.pi)⁻¹ * Real.sqrt (Real.pi / ε) with hA
  have hb : (((-(1 / (4 * ε)) : ℝ) : ℂ)).re < 0 := by
    rw [Complex.ofReal_re]
    have : 0 < 1 / (4 * ε) := by positivity
    linarith
  have h := integral_cexp_quadratic hb w 0
  have e1 : ∀ u : ℝ, cexp (w * u) * cx (stateHeatKernel ε) u =
      (A : ℂ) * cexp (((-(1 / (4 * ε)) : ℝ) : ℂ) * (u : ℂ) ^ 2 + w * u + 0) := fun u => by
    change cexp (w * u) * ((A * Real.exp (-(u ^ 2 / (4 * ε))) : ℝ) : ℂ) = _
    push_cast
    rw [mul_left_comm, ← Complex.exp_add]
    congr 2
    ring
  unfold negativeHalfLineLaplace
  simp_rw [e1]
  rw [integral_const_mul, h]
  have e2 : (Real.pi : ℂ) / -((-(1 / (4 * ε)) : ℝ) : ℂ) = ((4 * Real.pi * ε : ℝ) : ℂ) := by
    push_cast
    field_simp
  have e3 : ((4 * Real.pi * ε : ℝ) : ℂ) ^ (1 / 2 : ℂ) =
      ((Real.sqrt (4 * Real.pi * ε) : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity)]
    push_cast
    rfl
  have e4 : (0 : ℂ) - w ^ 2 / (4 * ((-(1 / (4 * ε)) : ℝ) : ℂ)) = (ε : ℂ) * w ^ 2 := by
    push_cast
    field_simp
  have e5 : A * Real.sqrt (4 * Real.pi * ε) = 1 := by
    rw [hA, mul_assoc, ← Real.sqrt_mul (by positivity),
      show Real.pi / ε * (4 * Real.pi * ε) = (2 * Real.pi) ^ 2 by field_simp; ring,
      Real.sqrt_sq (by positivity)]
    field_simp
  rw [e2, e3, e4, ← mul_assoc, ← Complex.ofReal_mul, e5, Complex.ofReal_one, one_mul]

theorem stateHeatKernel_pos {ε : ℝ} (hε : 0 < ε) (y : ℝ) : 0 < stateHeatKernel ε y := by
  unfold stateHeatKernel
  have : 0 < Real.sqrt (Real.pi / ε) := Real.sqrt_pos.mpr (by positivity)
  positivity

theorem integrable_stateHeatKernel_mul_exp_abs {ε : ℝ} (hε : 0 < ε) (c : ℝ) :
    Integrable fun y => stateHeatKernel ε y * Real.exp (c * |y|) := by
  refine ((integrable_tiltedHeatKernel hε c).add (integrable_tiltedHeatKernel hε (-c))).mono'
    ((continuous_stateHeatKernel ε).mul (by fun_prop)).aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  unfold tiltedHeatKernel
  rw [Real.norm_of_nonneg (mul_nonneg (stateHeatKernel_pos hε y).le (Real.exp_pos _).le),
    ← mul_add]
  refine mul_le_mul_of_nonneg_left ?_ (stateHeatKernel_pos hε y).le
  rcases le_total 0 y with hy | hy
  · rw [abs_of_nonneg hy]; linarith [Real.exp_pos (-c * y)]
  · rw [abs_of_nonpos hy, show c * -y = -c * y by ring]; linarith [Real.exp_pos (c * y)]

/-- The heat kernel against `e^{4|y|}`: at most `2 e^{16ε}`. -/
theorem integral_stateHeatKernel_mul_exp_four_le {ε : ℝ} (hε : 0 < ε) :
    ∫ y, stateHeatKernel ε y * Real.exp (4 * |y|) ≤ 2 * Real.exp (16 * ε) := by
  have hl : ∀ c : ℝ, ∫ y, stateHeatKernel ε y * Real.exp (c * y) = Real.exp (ε * c ^ 2) := by
    intro c
    have h := laplace_stateHeatKernel hε (c : ℂ)
    rw [negativeHalfLineLaplace_ofReal] at h
    have h2 : ((∫ u, stateHeatKernel ε u * Real.exp (c * u) : ℝ) : ℂ) =
        ((Real.exp (ε * c ^ 2) : ℝ) : ℂ) := by rw [h]; push_cast; ring_nf
    exact_mod_cast h2
  calc ∫ y, stateHeatKernel ε y * Real.exp (4 * |y|)
      ≤ ∫ y, (stateHeatKernel ε y * Real.exp (4 * y) + stateHeatKernel ε y * Real.exp (-4 * y)) := by
        refine integral_mono (integrable_stateHeatKernel_mul_exp_abs hε 4)
          ((integrable_tiltedHeatKernel hε 4).add (integrable_tiltedHeatKernel hε (-4))) fun y => ?_
        rw [← mul_add]
        refine mul_le_mul_of_nonneg_left ?_ (stateHeatKernel_pos hε y).le
        rcases le_total 0 y with hy | hy
        · rw [abs_of_nonneg hy]; linarith [Real.exp_pos (-4 * y)]
        · rw [abs_of_nonpos hy, show 4 * -y = -4 * y by ring]; linarith [Real.exp_pos (4 * y)]
    _ = 2 * Real.exp (16 * ε) := by
        rw [integral_add (integrable_tiltedHeatKernel hε 4) (integrable_tiltedHeatKernel hε (-4))]
        have h1 := hl 4
        have h2 := hl (-4)
        unfold tiltedHeatKernel at *
        rw [h1, h2]
        ring_nf

theorem hasDerivAt_stateHeatKernel (ε y : ℝ) :
    HasDerivAt (stateHeatKernel ε) (-(y / (2 * ε)) * stateHeatKernel ε y) y := by
  have h := (((hasDerivAt_pow 2 y).div_const (4 * ε)).neg.exp).const_mul
    ((2 * Real.pi)⁻¹ * Real.sqrt (Real.pi / ε))
  refine h.congr_deriv ?_
  unfold stateHeatKernel
  simp only [Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
  ring

/-- The derivative `k_ε' = −(y/2ε) k_ε` of the heat kernel. -/
def heatKernel₁ (ε y : ℝ) : ℝ := -(y / (2 * ε)) * stateHeatKernel ε y

/-- The second derivative of the heat kernel, in product-rule form. -/
def heatKernel₂ (ε y : ℝ) : ℝ :=
  -(1 / (2 * ε)) * stateHeatKernel ε y + -(y / (2 * ε)) * heatKernel₁ ε y

theorem hasDerivAt_heatKernel₁ (ε y : ℝ) :
    HasDerivAt (heatKernel₁ ε) (heatKernel₂ ε y) y :=
  ((hasDerivAt_id y).div_const (2 * ε)).neg.mul (hasDerivAt_stateHeatKernel ε y)

/-! ### The plateau cut of the heat kernel -/

/-- A smooth plateau: `1` on `[−1, 1]`, supported in `(−2, 2)`, with values in `[0, 1]`. -/
def plateauBump : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The plateau as a function. -/
def plateau (y : ℝ) : ℝ := plateauBump y

def plateau₁ : ℝ → ℝ := deriv plateau

def plateau₂ : ℝ → ℝ := deriv plateau₁

theorem contDiff_plateau : ContDiff ℝ ∞ plateau := plateauBump.contDiff

theorem hasCompactSupport_plateau : HasCompactSupport plateau := plateauBump.hasCompactSupport

theorem plateau_nonneg (y : ℝ) : 0 ≤ plateau y := plateauBump.nonneg

theorem plateau_le_one (y : ℝ) : plateau y ≤ 1 := plateauBump.le_one

theorem plateau_eq_one {y : ℝ} (hy : |y| ≤ 1) : plateau y = 1 :=
  plateauBump.one_of_mem_closedBall (show y ∈ Metric.closedBall (0 : ℝ) 1 by
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]; exact hy)

theorem contDiff_plateau₁ : ContDiff ℝ ∞ plateau₁ := by
  have h := ContDiff.iterate_deriv 1 contDiff_plateau
  simpa [plateau₁] using h

theorem contDiff_plateau₂ : ContDiff ℝ ∞ plateau₂ := by
  have h := ContDiff.iterate_deriv 2 contDiff_plateau
  simpa [plateau₂, plateau₁] using h

theorem one_le_infty : (1 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top

theorem hasDerivAt_plateau (y : ℝ) : HasDerivAt plateau (plateau₁ y) y :=
  ((contDiff_plateau.differentiable one_le_infty) y).hasDerivAt

theorem hasDerivAt_plateau₁ (y : ℝ) : HasDerivAt plateau₁ (plateau₂ y) y :=
  ((contDiff_plateau₁.differentiable one_le_infty) y).hasDerivAt

theorem hasCompactSupport_plateau₁ : HasCompactSupport plateau₁ := hasCompactSupport_plateau.deriv

theorem hasCompactSupport_plateau₂ : HasCompactSupport plateau₂ := hasCompactSupport_plateau₁.deriv

theorem hasCompactSupport_comp_div {f : ℝ → ℝ} (hf : HasCompactSupport f) {c : ℝ} (hc : c ≠ 0) :
    HasCompactSupport fun y => f (y / c) := by
  have h := hf.comp_homeomorph (Homeomorph.mulRight₀ c⁻¹ (inv_ne_zero hc))
  convert h using 1
  funext y
  simp [div_eq_mul_inv]

/-- The heat kernel cut by the plateau at scale `k + 1`. -/
def cutHeatKernel (ε : ℝ) (k : ℕ) (y : ℝ) : ℝ := stateHeatKernel ε y * plateau (y / ((k : ℝ) + 1))

/-- The first derivative of the cut kernel. -/
def cutHeatKernel₁ (ε : ℝ) (k : ℕ) (y : ℝ) : ℝ :=
  heatKernel₁ ε y * plateau (y / ((k : ℝ) + 1)) +
    stateHeatKernel ε y * (plateau₁ (y / ((k : ℝ) + 1)) * (1 / ((k : ℝ) + 1)))

/-- The second derivative of the cut kernel. -/
def cutHeatKernel₂ (ε : ℝ) (k : ℕ) (y : ℝ) : ℝ :=
  (heatKernel₂ ε y * plateau (y / ((k : ℝ) + 1)) +
      heatKernel₁ ε y * (plateau₁ (y / ((k : ℝ) + 1)) * (1 / ((k : ℝ) + 1)))) +
    (heatKernel₁ ε y * (plateau₁ (y / ((k : ℝ) + 1)) * (1 / ((k : ℝ) + 1))) +
      stateHeatKernel ε y * (plateau₂ (y / ((k : ℝ) + 1)) * (1 / ((k : ℝ) + 1)) * (1 / ((k : ℝ) + 1))))

theorem hasDerivAt_plateau_div (k : ℕ) (y : ℝ) :
    HasDerivAt (fun x => plateau (x / ((k : ℝ) + 1)))
      (plateau₁ (y / ((k : ℝ) + 1)) * (1 / ((k : ℝ) + 1))) y :=
  (hasDerivAt_plateau _).comp y ((hasDerivAt_id y).div_const _)

theorem hasDerivAt_plateau₁_div (k : ℕ) (y : ℝ) :
    HasDerivAt (fun x => plateau₁ (x / ((k : ℝ) + 1)) * (1 / ((k : ℝ) + 1)))
      (plateau₂ (y / ((k : ℝ) + 1)) * (1 / ((k : ℝ) + 1)) * (1 / ((k : ℝ) + 1))) y :=
  ((hasDerivAt_plateau₁ _).comp y ((hasDerivAt_id y).div_const _)).mul_const _

theorem hasDerivAt_cutHeatKernel (ε : ℝ) (k : ℕ) (y : ℝ) :
    HasDerivAt (cutHeatKernel ε k) (cutHeatKernel₁ ε k y) y :=
  (hasDerivAt_stateHeatKernel ε y).mul (hasDerivAt_plateau_div k y)

theorem hasDerivAt_cutHeatKernel₁ (ε : ℝ) (k : ℕ) (y : ℝ) :
    HasDerivAt (cutHeatKernel₁ ε k) (cutHeatKernel₂ ε k y) y :=
  ((hasDerivAt_heatKernel₁ ε y).mul (hasDerivAt_plateau_div k y)).add
    ((hasDerivAt_stateHeatKernel ε y).mul (hasDerivAt_plateau₁_div k y))

theorem continuous_heatKernel₁ (ε : ℝ) : Continuous (heatKernel₁ ε) :=
  (continuous_id.div_const _).neg.mul (continuous_stateHeatKernel ε)

theorem continuous_heatKernel₂ (ε : ℝ) : Continuous (heatKernel₂ ε) :=
  (continuous_const.mul (continuous_stateHeatKernel ε)).add
    ((continuous_id.div_const _).neg.mul (continuous_heatKernel₁ ε))

theorem continuous_cutHeatKernel (ε : ℝ) (k : ℕ) : Continuous (cutHeatKernel ε k) :=
  (continuous_stateHeatKernel ε).mul (contDiff_plateau.continuous.comp (continuous_id.div_const _))

theorem continuous_cutHeatKernel₁ (ε : ℝ) (k : ℕ) : Continuous (cutHeatKernel₁ ε k) :=
  ((continuous_heatKernel₁ ε).mul (contDiff_plateau.continuous.comp (continuous_id.div_const _))).add
    ((continuous_stateHeatKernel ε).mul
      ((contDiff_plateau₁.continuous.comp (continuous_id.div_const _)).mul continuous_const))

theorem continuous_cutHeatKernel₂ (ε : ℝ) (k : ℕ) : Continuous (cutHeatKernel₂ ε k) :=
  (((continuous_heatKernel₂ ε).mul (contDiff_plateau.continuous.comp (continuous_id.div_const _))).add
    ((continuous_heatKernel₁ ε).mul
      ((contDiff_plateau₁.continuous.comp (continuous_id.div_const _)).mul continuous_const))).add
  (((continuous_heatKernel₁ ε).mul
      ((contDiff_plateau₁.continuous.comp (continuous_id.div_const _)).mul continuous_const)).add
    ((continuous_stateHeatKernel ε).mul
      (((contDiff_plateau₂.continuous.comp (continuous_id.div_const _)).mul continuous_const).mul
        continuous_const)))

theorem kplus_ne_zero (k : ℕ) : ((k : ℝ) + 1) ≠ 0 := by positivity

theorem hasCompactSupport_cutHeatKernel (ε : ℝ) (k : ℕ) : HasCompactSupport (cutHeatKernel ε k) :=
  (hasCompactSupport_comp_div hasCompactSupport_plateau (kplus_ne_zero k)).mul_left

theorem hasCompactSupport_cutHeatKernel₁ (ε : ℝ) (k : ℕ) :
    HasCompactSupport (cutHeatKernel₁ ε k) :=
  (hasCompactSupport_comp_div hasCompactSupport_plateau (kplus_ne_zero k)).mul_left.add
    ((hasCompactSupport_comp_div hasCompactSupport_plateau₁ (kplus_ne_zero k)).mul_right.mul_left)

theorem hasCompactSupport_cutHeatKernel₂ (ε : ℝ) (k : ℕ) :
    HasCompactSupport (cutHeatKernel₂ ε k) :=
  ((hasCompactSupport_comp_div hasCompactSupport_plateau (kplus_ne_zero k)).mul_left.add
    ((hasCompactSupport_comp_div hasCompactSupport_plateau₁ (kplus_ne_zero k)).mul_right.mul_left)).add
  ((hasCompactSupport_comp_div hasCompactSupport_plateau₁ (kplus_ne_zero k)).mul_right.mul_left.add
    ((hasCompactSupport_comp_div hasCompactSupport_plateau₂ (kplus_ne_zero k)).mul_right.mul_right.mul_left))

theorem contDiff_cutHeatKernel (ε : ℝ) (k : ℕ) : ContDiff ℝ ∞ (cutHeatKernel ε k) := by
  unfold cutHeatKernel stateHeatKernel
  exact (contDiff_const.mul (by fun_prop)).mul (contDiff_plateau.comp (contDiff_id.div_const _))

theorem cutHeatKernel_nonneg {ε : ℝ} (hε : 0 < ε) (k : ℕ) (y : ℝ) : 0 ≤ cutHeatKernel ε k y :=
  mul_nonneg (stateHeatKernel_pos hε y).le (plateau_nonneg _)

theorem cutHeatKernel_le {ε : ℝ} (hε : 0 < ε) (k : ℕ) (y : ℝ) :
    cutHeatKernel ε k y ≤ stateHeatKernel ε y :=
  mul_le_of_le_one_right (stateHeatKernel_pos hε y).le (plateau_le_one _)

theorem tendsto_cutHeatKernel (ε y : ℝ) :
    Tendsto (fun k : ℕ => cutHeatKernel ε k y) atTop (𝓝 (stateHeatKernel ε y)) := by
  refine tendsto_const_nhds.congr' ?_
  obtain ⟨N, hN⟩ := exists_nat_ge |y|
  filter_upwards [eventually_ge_atTop N] with k hk
  have hk' : |y| ≤ (k : ℝ) + 1 := by
    have : (N : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  unfold cutHeatKernel
  rw [plateau_eq_one, mul_one]
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (k : ℝ) + 1), div_le_one (by positivity)]
  exact hk'

/-! ### Two integrations by parts -/

theorem laplace_eq_of_hasDerivAt {u u' : ℝ → ℝ} (hu : ∀ y, HasDerivAt u (u' y) y)
    (hcu : Continuous u) (hcs : HasCompactSupport u) (hcu' : Continuous u')
    (hcs' : HasCompactSupport u') {w : ℂ} (hw : w ≠ 0) :
    negativeHalfLineLaplace (cx u) w = -(w⁻¹ * negativeHalfLineLaplace (cx u') w) := by
  have hV : ∀ y : ℝ, HasDerivAt (fun x : ℝ => w⁻¹ * cexp (w * x)) (cexp (w * y)) y := fun y => by
    have h := ((((hasDerivAt_id y).ofReal_comp).const_mul w).cexp).const_mul w⁻¹
    refine h.congr_deriv ?_
    simp only [id, mul_one]
    field_simp
  have hU : ∀ y : ℝ, HasDerivAt (cx u) (cx u' y) y := fun y => (hu y).ofReal_comp
  have hcU : HasCompactSupport (cx u) := hcs.comp_left Complex.ofReal_zero
  have hcU' : HasCompactSupport (cx u') := hcs'.comp_left Complex.ofReal_zero
  have hcont : Continuous fun x : ℝ => cexp (w * x) := by fun_prop
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable (u := cx u) (u' := cx u')
    (v := fun x : ℝ => w⁻¹ * cexp (w * x)) (v' := fun x : ℝ => cexp (w * x))
    (fun y _ => hU y) (fun y _ => hV y)
    (((Complex.continuous_ofReal.comp hcu).mul hcont).integrable_of_hasCompactSupport
      hcU.mul_right)
    (((Complex.continuous_ofReal.comp hcu').mul (hcont.const_mul _)).integrable_of_hasCompactSupport
      hcU'.mul_right)
    (((Complex.continuous_ofReal.comp hcu).mul (hcont.const_mul _)).integrable_of_hasCompactSupport
      hcU.mul_right)
  unfold negativeHalfLineLaplace
  rw [show (∫ x : ℝ, cexp (w * x) * cx u x) = ∫ x : ℝ, cx u x * cexp (w * x) from
    integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _), h, ← integral_const_mul]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  show cx u' x * (w⁻¹ * cexp (w * x)) = w⁻¹ * (cexp (w * x) * cx u' x)
  ring

/-- Two integrations by parts: `L κ(w) = w^{−2} L κ''(w)` for the cut kernel. -/
theorem laplace_cutHeatKernel_eq (ε : ℝ) (k : ℕ) {w : ℂ} (hw : w ≠ 0) :
    negativeHalfLineLaplace (cx (cutHeatKernel ε k)) w =
      (w ^ 2)⁻¹ * negativeHalfLineLaplace (cx (cutHeatKernel₂ ε k)) w := by
  rw [laplace_eq_of_hasDerivAt (hasDerivAt_cutHeatKernel ε k) (continuous_cutHeatKernel ε k)
      (hasCompactSupport_cutHeatKernel ε k) (continuous_cutHeatKernel₁ ε k)
      (hasCompactSupport_cutHeatKernel₁ ε k) hw,
    laplace_eq_of_hasDerivAt (hasDerivAt_cutHeatKernel₁ ε k) (continuous_cutHeatKernel₁ ε k)
      (hasCompactSupport_cutHeatKernel₁ ε k) (continuous_cutHeatKernel₂ ε k)
      (hasCompactSupport_cutHeatKernel₂ ε k) hw]
  rw [inv_pow]
  ring

/-- A pointwise Gaussian majorant for the second derivative of the cut kernels, uniform in `k`. -/
theorem exists_cutHeatKernel₂_majorant {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ (k : ℕ) (y : ℝ),
      |cutHeatKernel₂ ε k y| * Real.exp (|y| / 2) ≤ C * Real.exp (-(1 / (16 * ε)) * y ^ 2) := by
  obtain ⟨A₁, hA₁⟩ := contDiff_plateau₁.continuous.bounded_above_of_compact_support
    hasCompactSupport_plateau₁
  obtain ⟨A₂, hA₂⟩ := contDiff_plateau₂.continuous.bounded_above_of_compact_support
    hasCompactSupport_plateau₂
  have hA₁0 : 0 ≤ A₁ := (norm_nonneg _).trans (hA₁ 0)
  have hA₂0 : 0 ≤ A₂ := (norm_nonneg _).trans (hA₂ 0)
  set A : ℝ := (2 * Real.pi)⁻¹ * Real.sqrt (Real.pi / ε)
  have hA0 : 0 ≤ A := by positivity
  set C₀ : ℝ := 1 / (2 * ε) + 1 / (4 * ε ^ 2) + A₁ / ε + A₂
  have hC₀ : 0 ≤ C₀ := by positivity
  refine ⟨A * Real.exp (ε / 2) * C₀ * (1 + 16 * ε), fun k y => ?_⟩
  set c : ℝ := 1 / ((k : ℝ) + 1)
  have hc0 : 0 < c := by positivity
  have hc1 : c ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith [Nat.cast_nonneg (α := ℝ) k]
  set g := stateHeatKernel ε y
  have hg : 0 < g := stateHeatKernel_pos hε y
  have hp0 := plateau_nonneg (y / ((k : ℝ) + 1))
  have hp1 := plateau_le_one (y / ((k : ℝ) + 1))
  have hq1 : |plateau₁ (y / ((k : ℝ) + 1))| ≤ A₁ := by
    have := hA₁ (y / ((k : ℝ) + 1)); rwa [Real.norm_eq_abs] at this
  have hq2 : |plateau₂ (y / ((k : ℝ) + 1))| ≤ A₂ := by
    have := hA₂ (y / ((k : ℝ) + 1)); rwa [Real.norm_eq_abs] at this
  have hy1 : |y| ≤ 1 + y ^ 2 := by nlinarith [abs_nonneg y, sq_abs y, sq_nonneg (|y| - 1)]
  -- the polynomial factor
  have hpoly : |cutHeatKernel₂ ε k y| ≤ C₀ * (1 + y ^ 2) * g := by
    have h1 : |heatKernel₁ ε y| = |y| / (2 * ε) * g := by
      unfold heatKernel₁
      rw [abs_mul, abs_neg, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * ε),
        abs_of_pos hg]
    have h2 : |heatKernel₂ ε y| ≤ (1 / (2 * ε) + y ^ 2 / (4 * ε ^ 2)) * g := by
      unfold heatKernel₂ heatKernel₁
      have e : -(1 / (2 * ε)) * g + -(y / (2 * ε)) * (-(y / (2 * ε)) * g) =
          (y ^ 2 / (4 * ε ^ 2) - 1 / (2 * ε)) * g := by field_simp; ring
      rw [e, abs_mul, abs_of_pos hg]
      refine mul_le_mul_of_nonneg_right ?_ hg.le
      have : 0 ≤ y ^ 2 / (4 * ε ^ 2) := by positivity
      have : 0 ≤ 1 / (2 * ε) := by positivity
      rw [abs_le]; constructor <;> linarith
    unfold cutHeatKernel₂
    set p := plateau (y / ((k : ℝ) + 1))
    set q₁ := plateau₁ (y / ((k : ℝ) + 1))
    set q₂ := plateau₂ (y / ((k : ℝ) + 1))
    have t1 : |heatKernel₂ ε y * p| ≤ (1 / (2 * ε) + y ^ 2 / (4 * ε ^ 2)) * g := by
      rw [abs_mul, abs_of_nonneg hp0]
      exact (mul_le_of_le_one_right (abs_nonneg _) hp1).trans h2
    have t2 : |heatKernel₁ ε y * (q₁ * c)| ≤ |y| / (2 * ε) * g * A₁ := by
      rw [abs_mul, abs_mul, h1, abs_of_pos hc0]
      have : |q₁| * c ≤ A₁ := (mul_le_of_le_one_right (abs_nonneg _) hc1).trans hq1
      exact mul_le_mul_of_nonneg_left this (by positivity)
    have t3 : |g * (q₂ * c * c)| ≤ g * A₂ := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos hg, abs_of_pos hc0]
      have : |q₂| * c * c ≤ A₂ := by
        have hcc : c * c ≤ 1 := by nlinarith
        calc |q₂| * c * c = |q₂| * (c * c) := by ring
          _ ≤ |q₂| * 1 := mul_le_mul_of_nonneg_left hcc (abs_nonneg _)
          _ ≤ A₂ := by rw [mul_one]; exact hq2
      exact mul_le_mul_of_nonneg_left this hg.le
    calc |heatKernel₂ ε y * p + heatKernel₁ ε y * (q₁ * c) +
          (heatKernel₁ ε y * (q₁ * c) + g * (q₂ * c * c))|
        ≤ |heatKernel₂ ε y * p| + |heatKernel₁ ε y * (q₁ * c)| +
            (|heatKernel₁ ε y * (q₁ * c)| + |g * (q₂ * c * c)|) :=
          (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) (abs_add_le _ _))
      _ ≤ (1 / (2 * ε) + y ^ 2 / (4 * ε ^ 2)) * g + |y| / (2 * ε) * g * A₁ +
            (|y| / (2 * ε) * g * A₁ + g * A₂) := by gcongr
      _ = (1 / (2 * ε) + y ^ 2 / (4 * ε ^ 2) + |y| * A₁ / ε + A₂) * g := by field_simp; ring
      _ ≤ C₀ * (1 + y ^ 2) * g := by
          refine mul_le_mul_of_nonneg_right ?_ hg.le
          have e1 : y ^ 2 / (4 * ε ^ 2) ≤ 1 / (4 * ε ^ 2) * (1 + y ^ 2) := by
            rw [div_le_iff₀ (by positivity)]; field_simp; nlinarith
          have e2 : |y| * A₁ / ε ≤ A₁ / ε * (1 + y ^ 2) := by
            rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hε]; nlinarith
          have e3 : 1 / (2 * ε) ≤ 1 / (2 * ε) * (1 + y ^ 2) := le_mul_of_one_le_right
            (by positivity) (by nlinarith)
          have e4 : A₂ ≤ A₂ * (1 + y ^ 2) := le_mul_of_one_le_right hA₂0 (by nlinarith)
          simp only [C₀]
          nlinarith
  -- the Gaussian factor
  have hgauss : g * Real.exp (|y| / 2) ≤ A * Real.exp (ε / 2) * Real.exp (-(1 / (8 * ε)) * y ^ 2) := by
    show A * Real.exp (-(y ^ 2 / (4 * ε))) * Real.exp (|y| / 2) ≤ _
    rw [mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hA0
    have hsq : 0 ≤ (|y| - 2 * ε) ^ 2 / (8 * ε) := by positivity
    have e : -(y ^ 2 / (4 * ε)) + |y| / 2 =
        ε / 2 + -(1 / (8 * ε)) * y ^ 2 - (|y| - 2 * ε) ^ 2 / (8 * ε) := by
      rw [← sq_abs y]; field_simp; ring
    rw [e]; linarith
  have hpoly2 : (1 + y ^ 2) * Real.exp (-(1 / (8 * ε)) * y ^ 2) ≤
      (1 + 16 * ε) * Real.exp (-(1 / (16 * ε)) * y ^ 2) := by
    set x := y ^ 2 / (16 * ε)
    have hx : 0 ≤ x := by positivity
    have hex : 1 + x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
    have e1 : Real.exp (-(1 / (8 * ε)) * y ^ 2) = Real.exp (-(1 / (16 * ε)) * y ^ 2) * Real.exp (-x) := by
      rw [← Real.exp_add]; congr 1; simp only [x]; field_simp; ring
    have e2 : 1 + y ^ 2 = 1 + 16 * ε * x := by simp only [x]; field_simp
    rw [e1, e2]
    have hE : 0 < Real.exp (-(1 / (16 * ε)) * y ^ 2) := Real.exp_pos _
    have hmx : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
    have key : (1 + 16 * ε * x) * Real.exp (-x) ≤ 1 + 16 * ε := by
      have h1 : (1 + 16 * ε * x) ≤ (1 + 16 * ε) * Real.exp x := by nlinarith [Real.exp_pos x]
      calc (1 + 16 * ε * x) * Real.exp (-x) ≤ (1 + 16 * ε) * Real.exp x * Real.exp (-x) :=
            mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
        _ = 1 + 16 * ε := by rw [mul_assoc, mul_comm (Real.exp x), hmx, mul_one]
    calc (1 + 16 * ε * x) * (Real.exp (-(1 / (16 * ε)) * y ^ 2) * Real.exp (-x))
        = ((1 + 16 * ε * x) * Real.exp (-x)) * Real.exp (-(1 / (16 * ε)) * y ^ 2) := by ring
      _ ≤ (1 + 16 * ε) * Real.exp (-(1 / (16 * ε)) * y ^ 2) :=
          mul_le_mul_of_nonneg_right key hE.le
  calc |cutHeatKernel₂ ε k y| * Real.exp (|y| / 2)
      ≤ C₀ * (1 + y ^ 2) * g * Real.exp (|y| / 2) :=
        mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le
    _ = C₀ * (1 + y ^ 2) * (g * Real.exp (|y| / 2)) := by ring
    _ ≤ C₀ * (1 + y ^ 2) * (A * Real.exp (ε / 2) * Real.exp (-(1 / (8 * ε)) * y ^ 2)) :=
        mul_le_mul_of_nonneg_left hgauss (by positivity)
    _ = A * Real.exp (ε / 2) * C₀ * ((1 + y ^ 2) * Real.exp (-(1 / (8 * ε)) * y ^ 2)) := by ring
    _ ≤ A * Real.exp (ε / 2) * C₀ * ((1 + 16 * ε) * Real.exp (-(1 / (16 * ε)) * y ^ 2)) :=
        mul_le_mul_of_nonneg_left hpoly2 (by positivity)
    _ = _ := by ring

/-- **The cut kernels decay like `|w|^{−2}` on the zero strip, uniformly in the cut.** -/
theorem exists_laplace_cutHeatKernel_le {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (k : ℕ) (w : ℂ), |w.re| ≤ 1 / 2 → w ≠ 0 →
      ‖negativeHalfLineLaplace (cx (cutHeatKernel ε k)) w‖ ≤ M * ‖w‖⁻¹ ^ 2 := by
  obtain ⟨C, hC⟩ := exists_cutHeatKernel₂_majorant hε
  have hb : (0 : ℝ) < 1 / (16 * ε) := by positivity
  have hint : Integrable fun y : ℝ => C * Real.exp (-(1 / (16 * ε)) * y ^ 2) :=
    (integrable_exp_neg_mul_sq hb).const_mul C
  have hC0 : 0 ≤ C := by
    have h := hC 0 0
    have : 0 ≤ |cutHeatKernel₂ ε 0 0| * Real.exp (|(0 : ℝ)| / 2) := by positivity
    have hE : 0 < Real.exp (-(1 / (16 * ε)) * (0 : ℝ) ^ 2) := Real.exp_pos _
    nlinarith
  refine ⟨∫ y, C * Real.exp (-(1 / (16 * ε)) * y ^ 2),
    integral_nonneg fun y => by positivity, fun k w hw hw0 => ?_⟩
  rw [laplace_cutHeatKernel_eq ε k hw0, norm_mul, norm_inv, norm_pow, inv_pow, mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  unfold negativeHalfLineLaplace
  refine norm_integral_le_of_norm_le hint (Eventually.of_forall fun y => ?_)
  exact (norm_cexp_mul_cx_le hw _ y).trans (hC k y)

theorem norm_laplace_cutHeatKernel_le {ε : ℝ} (hε : 0 < ε) (k : ℕ) {w : ℂ} (hw : |w.re| ≤ 1 / 2) :
    ‖negativeHalfLineLaplace (cx (cutHeatKernel ε k)) w‖ ≤
      ∫ y, stateHeatKernel ε y * Real.exp (|y| / 2) := by
  have hint := integrable_stateHeatKernel_mul_exp_abs hε (1 / 2)
  unfold negativeHalfLineLaplace
  refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun u => norm_nonneg _) (hint.congr (Eventually.of_forall fun y => ?_))
    (Eventually.of_forall fun y => (norm_cexp_mul_cx_le hw _ y).trans ?_))
  · show stateHeatKernel ε y * Real.exp (1 / 2 * |y|) = stateHeatKernel ε y * Real.exp (|y| / 2)
    congr 2; ring
  · rw [abs_of_nonneg (cutHeatKernel_nonneg hε k y)]
    exact mul_le_mul_of_nonneg_right (cutHeatKernel_le hε k y) (Real.exp_pos _).le

theorem tendsto_laplace_cutHeatKernel {ε : ℝ} (hε : 0 < ε) {w : ℂ} (hw : |w.re| ≤ 1 / 2) :
    Tendsto (fun k : ℕ => negativeHalfLineLaplace (cx (cutHeatKernel ε k)) w) atTop
      (𝓝 (cexp (ε * w ^ 2))) := by
  rw [← laplace_stateHeatKernel hε w]
  unfold negativeHalfLineLaplace
  refine tendsto_integral_of_dominated_convergence (fun y => stateHeatKernel ε y * Real.exp (|y| / 2))
    (fun k => ((by fun_prop : Continuous fun u : ℝ => cexp (w * u)).mul
      (Complex.continuous_ofReal.comp (continuous_cutHeatKernel ε k))).aestronglyMeasurable)
    ((integrable_stateHeatKernel_mul_exp_abs hε (1 / 2)).congr
      (Eventually.of_forall fun y => by simp only; congr 2; ring))
    (fun k => Eventually.of_forall fun y => (norm_cexp_mul_cx_le hw _ y).trans ?_)
    (Eventually.of_forall fun y => ?_)
  · rw [abs_of_nonneg (cutHeatKernel_nonneg hε k y)]
    exact mul_le_mul_of_nonneg_right (cutHeatKernel_le hε k y) (Real.exp_pos _).le
  · exact tendsto_const_nhds.mul ((Complex.continuous_ofReal.tendsto _).comp
      (tendsto_cutHeatKernel ε y))

/-! ### The heated tests -/

/-- The profile cut at `−k`. -/
def leftCut (G : ℝ → ℝ) (k : ℕ) : ℝ → ℝ := (Ioi (-(k : ℝ))).indicator G

theorem abs_leftCut_le (G : ℝ → ℝ) (k : ℕ) (u : ℝ) : |leftCut G k u| ≤ |G u| := by
  unfold leftCut
  by_cases h : u ∈ Ioi (-(k : ℝ))
  · rw [indicator_of_mem h]
  · rw [indicator_of_notMem h, abs_zero]; exact abs_nonneg _

theorem measurable_leftCut {G : ℝ → ℝ} (hG : Measurable G) (k : ℕ) : Measurable (leftCut G k) :=
  hG.indicator measurableSet_Ioi

theorem leftCut_eventually_eq (G : ℝ → ℝ) (u : ℝ) : ∀ᶠ k : ℕ in atTop, leftCut G k u = G u := by
  obtain ⟨N, hN⟩ := exists_nat_gt (-u)
  filter_upwards [eventually_ge_atTop N] with k hk
  unfold leftCut
  have : (N : ℝ) ≤ k := by exact_mod_cast hk
  exact indicator_of_mem (show u ∈ Ioi (-(k : ℝ)) by rw [mem_Ioi]; linarith) _

theorem leftCut_eq_zero {G : ℝ → ℝ} (hG : ∀ u, 0 ≤ u → G u = 0) (k : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    leftCut G k u = 0 := by
  unfold leftCut
  by_cases h : u ∈ Ioi (-(k : ℝ))
  · rw [indicator_of_mem h]; exact hG u hu
  · exact indicator_of_notMem h _

theorem hasCompactSupport_leftCut {G : ℝ → ℝ} (hG : CriticalHalfLineEnergyDomain G) (k : ℕ) :
    HasCompactSupport (leftCut G k) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -(k : ℝ)) (b := 0)) fun x hx => ?_
  rw [mem_Icc, not_and_or, not_le, not_le] at hx
  rcases hx with hx | hx
  · unfold leftCut
    exact indicator_of_notMem (by rw [mem_Ioi, not_lt]; exact hx.le) _
  · exact leftCut_eq_zero hG.support k hx.le

theorem integrable_leftCut {G : ℝ → ℝ} (hG : CriticalHalfLineEnergyDomain G) (k : ℕ) :
    Integrable (leftCut G k) := hG.integrable.indicator measurableSet_Ioi

theorem integrable_abs_leftCut_mul_exp {G : ℝ → ℝ} (hG : CriticalHalfLineEnergyDomain G) (k : ℕ) :
    Integrable fun u => |leftCut G k u| * Real.exp (|u| / 2) :=
  (integrable_abs_mul_exp_abs_half_of_domain hG).mono'
    ((continuous_abs.measurable.comp (measurable_leftCut hG.meas k)).mul
      (by fun_prop : Measurable fun u : ℝ => Real.exp (|u| / 2))).aestronglyMeasurable
    (Eventually.of_forall fun u => by
      rw [Real.norm_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_right (abs_leftCut_le G k u) (Real.exp_pos _).le)

theorem tendsto_laplace_leftCut {G : ℝ → ℝ} (hG : CriticalHalfLineEnergyDomain G) {w : ℂ}
    (hw : |w.re| ≤ 1 / 2) :
    Tendsto (fun k : ℕ => negativeHalfLineLaplace (cx (leftCut G k)) w) atTop
      (𝓝 (negativeHalfLineLaplace (cx G) w)) := by
  unfold negativeHalfLineLaplace
  refine tendsto_integral_of_dominated_convergence (fun u => |G u| * Real.exp (|u| / 2))
    (fun k => (integrable_cexp_mul_cx (measurable_leftCut hG.meas k).aestronglyMeasurable
      (integrable_abs_leftCut_mul_exp hG k) hw).aestronglyMeasurable)
    (integrable_abs_mul_exp_abs_half_of_domain hG)
    (fun k => Eventually.of_forall fun u => (norm_cexp_mul_cx_le hw _ u).trans
      (mul_le_mul_of_nonneg_right (abs_leftCut_le G k u) (Real.exp_pos _).le))
    (Eventually.of_forall fun u => tendsto_const_nhds.congr'
      ((leftCut_eventually_eq G u).mono fun k hk => by simp only [cx, hk]))

/-- The smooth compactly supported heated test `κ_k * G_k`. -/
def heatedCut (ε : ℝ) (G : ℝ → ℝ) (k : ℕ) : ℝ → ℝ :=
  convolution (cutHeatKernel ε k) (leftCut G k) (ContinuousLinearMap.mul ℝ ℝ) volume

theorem contDiff_heatedCut (ε : ℝ) {G : ℝ → ℝ} (hG : CriticalHalfLineEnergyDomain G) (k : ℕ) :
    ContDiff ℝ ∞ (heatedCut ε G k) :=
  (hasCompactSupport_cutHeatKernel ε k).contDiff_convolution_left _ (contDiff_cutHeatKernel ε k)
    (integrable_leftCut hG k).locallyIntegrable

theorem hasCompactSupport_heatedCut (ε : ℝ) {G : ℝ → ℝ} (hG : CriticalHalfLineEnergyDomain G)
    (k : ℕ) : HasCompactSupport (heatedCut ε G k) :=
  (hasCompactSupport_cutHeatKernel ε k).convolution _ (hasCompactSupport_leftCut hG k)

theorem integrable_cexp_mul_cx_cutHeatKernel (ε : ℝ) (k : ℕ) (w : ℂ) :
    Integrable fun u : ℝ => cexp (w * u) * cx (cutHeatKernel ε k) u :=
  ((by fun_prop : Continuous fun u : ℝ => cexp (w * u)).mul
    (Complex.continuous_ofReal.comp (continuous_cutHeatKernel ε k))).integrable_of_hasCompactSupport
    ((hasCompactSupport_cutHeatKernel ε k).comp_left Complex.ofReal_zero).mul_left

theorem laplace_heatedCut (ε : ℝ) {G : ℝ → ℝ} (hG : CriticalHalfLineEnergyDomain G) (k : ℕ)
    {w : ℂ} (hw : |w.re| ≤ 1 / 2) :
    negativeHalfLineLaplace (cx (heatedCut ε G k)) w =
      negativeHalfLineLaplace (cx (cutHeatKernel ε k)) w *
        negativeHalfLineLaplace (cx (leftCut G k)) w :=
  laplace_convolution (integrable_cexp_mul_cx_cutHeatKernel ε k w)
    (integrable_cexp_mul_cx (measurable_leftCut hG.meas k).aestronglyMeasurable
      (integrable_abs_leftCut_mul_exp hG k) hw)

/-! ### The zero side -/

theorem norm_laplace_leftCut_le {G : ℝ → ℝ} (hG : CriticalHalfLineEnergyDomain G) (k : ℕ) {w : ℂ}
    (hw : |w.re| ≤ 1 / 2) :
    ‖negativeHalfLineLaplace (cx (leftCut G k)) w‖ ≤ ∫ u, |G u| * Real.exp (|u| / 2) :=
  (norm_laplace_le (integrable_abs_leftCut_mul_exp hG k) hw).trans
    (integral_mono (integrable_abs_leftCut_mul_exp hG k)
      (integrable_abs_mul_exp_abs_half_of_domain hG)
      fun u => mul_le_mul_of_nonneg_right (abs_leftCut_le G k u) (Real.exp_pos _).le)

/-- On the zero side the heated tests give the Gaussian-summed zero pairing. -/
theorem tendsto_zeroPairing_heatedCut {ε : ℝ} (hε : 0 < ε) {F G : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hG : CriticalHalfLineEnergyDomain G) :
    Tendsto (fun k : ℕ => ∑' q : XiZeroCopy, negativeHalfLineLaplace (cx F) (centredZero q) *
        negativeHalfLineLaplace (cx (heatedCut ε G k)) (-centredZero q)) atTop
      (𝓝 (∑' q : XiZeroCopy, negativeHalfLineLaplace (cx F) (centredZero q) *
        negativeHalfLineLaplace (cx G) (-centredZero q) *
          Complex.exp ((ε : ℂ) * centredZero q ^ 2))) := by
  obtain ⟨M, hM0, hM⟩ := exists_laplace_cutHeatKernel_le hε
  set CF := ∫ u, |F u| * Real.exp (|u| / 2)
  set CG := ∫ u, |G u| * Real.exp (|u| / 2)
  have hCF : 0 ≤ CF := integral_nonneg fun u => by positivity
  have hCG : 0 ≤ CG := integral_nonneg fun u => by positivity
  have hre : ∀ q : XiZeroCopy, |(-centredZero q).re| ≤ 1 / 2 := fun q => by
    rw [Complex.neg_re, abs_neg]; exact (abs_re_centredZero_lt q).le
  have hre' : ∀ q : XiZeroCopy, |(centredZero q).re| ≤ 1 / 2 := fun q =>
    (abs_re_centredZero_lt q).le
  refine tendsto_tsum_of_dominated_convergence
    (bound := fun q => CF * M * CG * ‖centredZero q‖⁻¹ ^ 2)
    (summable_inv_sq_centredZero.mul_left (CF * M * CG)) (fun q => ?_)
    (Eventually.of_forall fun k q => ?_)
  · have e : ∀ k : ℕ, negativeHalfLineLaplace (cx F) (centredZero q) *
        negativeHalfLineLaplace (cx (heatedCut ε G k)) (-centredZero q) =
        negativeHalfLineLaplace (cx F) (centredZero q) *
          (negativeHalfLineLaplace (cx (cutHeatKernel ε k)) (-centredZero q) *
            negativeHalfLineLaplace (cx (leftCut G k)) (-centredZero q)) := fun k => by
      rw [laplace_heatedCut ε hG k (hre q)]
    have hlim : negativeHalfLineLaplace (cx F) (centredZero q) *
        negativeHalfLineLaplace (cx G) (-centredZero q) *
          Complex.exp ((ε : ℂ) * centredZero q ^ 2) =
        negativeHalfLineLaplace (cx F) (centredZero q) *
          (cexp (ε * (-centredZero q) ^ 2) * negativeHalfLineLaplace (cx G) (-centredZero q)) := by
      rw [neg_sq]; ring
    simp only [e]
    rw [hlim]
    exact ((tendsto_laplace_cutHeatKernel hε (hre q)).mul
      (tendsto_laplace_leftCut hG (hre q))).const_mul _
  · rw [laplace_heatedCut ε hG k (hre q), norm_mul, norm_mul]
    have b1 := norm_laplace_le (integrable_abs_mul_exp_abs_half_of_domain hF) (hre' q)
    have b2 := hM k (-centredZero q) (hre q) (neg_ne_zero.mpr (centredZero_ne_zero q))
    rw [norm_neg] at b2
    have b3 := norm_laplace_leftCut_le hG k (hre q)
    calc ‖negativeHalfLineLaplace (cx F) (centredZero q)‖ *
          (‖negativeHalfLineLaplace (cx (cutHeatKernel ε k)) (-centredZero q)‖ *
            ‖negativeHalfLineLaplace (cx (leftCut G k)) (-centredZero q)‖)
        ≤ CF * (M * ‖centredZero q‖⁻¹ ^ 2 * CG) :=
          mul_le_mul b1 (mul_le_mul b2 b3 (norm_nonneg _) (by positivity)) (by positivity) hCF
      _ = CF * M * CG * ‖centredZero q‖⁻¹ ^ 2 := by ring

/-! ### The correlation of two profiles -/

/-- The correlation `c(s) = ∫ F(t) G(t − s) dt`. -/
def profileCorr (F G : ℝ → ℝ) (s : ℝ) : ℝ := ∫ t, F t * G (t - s)

/-- **The correlation decays like `e^{−4|s|}`.** Both profiles vanish on `u ≥ 0`, so on the support
`8t − 4s ≤ −4|s|`; Cauchy–Schwarz in the confinement weight. -/
theorem abs_profileCorr_le {F G : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (hGm : Measurable G) (hGs : ∀ u, 0 ≤ u → G u = 0)
    (hGe : Integrable fun u => G u ^ 2 * Real.exp (-(8 * u))) (s : ℝ) :
    |profileCorr F G s| ≤ Real.exp (-(4 * |s|)) *
      (Real.sqrt (∫ t, F t ^ 2 * Real.exp (-(8 * t))) *
        Real.sqrt (∫ u, G u ^ 2 * Real.exp (-(8 * u)))) := by
  set f : ℝ → ℝ := fun t => |F t| * Real.exp (-(4 * t))
  set g : ℝ → ℝ := fun t => |G (t - s)| * Real.exp (-(4 * (t - s)))
  have hf2 : ∀ t, f t ^ 2 = F t ^ 2 * Real.exp (-(8 * t)) := fun t => by
    simp only [f]; rw [mul_pow, sq_abs, sq, ← Real.exp_add]; congr 2; ring
  have hg2 : ∀ t, g t ^ 2 = G (t - s) ^ 2 * Real.exp (-(8 * (t - s))) := fun t => by
    simp only [g]; rw [mul_pow, sq_abs, sq, ← Real.exp_add]; congr 2; ring
  have hfm : AEStronglyMeasurable f volume :=
    ((continuous_abs.measurable.comp hF.meas).mul (by fun_prop)).aestronglyMeasurable
  have hgm : AEStronglyMeasurable g volume :=
    ((continuous_abs.measurable.comp (hGm.comp (measurable_sub_const s))).mul
      (by fun_prop)).aestronglyMeasurable
  have hfi : Integrable fun t => f t ^ 2 := by simp_rw [hf2]; exact hF.exponential
  have hgi : Integrable fun t => g t ^ 2 := by
    simp_rw [hg2]; exact hGe.comp_sub_right s
  have hfg := GaloisForLFunctions.HTGeometry.integrable_mul_of_sq_integrable hfm hgm hfi hgi
  have hpt : ∀ t, |F t * G (t - s)| ≤ Real.exp (-(4 * |s|)) * (f t * g t) := by
    intro t
    by_cases h1 : 0 ≤ t
    · rw [hF.support t h1, zero_mul, abs_zero]; positivity
    by_cases h2 : 0 ≤ t - s
    · rw [hGs _ h2, mul_zero, abs_zero]; positivity
    push_neg at h1 h2
    simp only [f, g]
    rw [abs_mul]
    have he : Real.exp (-(4 * |s|)) * (|F t| * Real.exp (-(4 * t)) *
        (|G (t - s)| * Real.exp (-(4 * (t - s))))) =
        |F t| * |G (t - s)| * Real.exp (-(4 * |s|) + -(4 * t) + -(4 * (t - s))) := by
      rw [Real.exp_add, Real.exp_add]; ring
    rw [he]
    have hexp : 1 ≤ Real.exp (-(4 * |s|) + -(4 * t) + -(4 * (t - s))) := by
      apply Real.one_le_exp
      rcases le_total 0 s with hs | hs
      · rw [abs_of_nonneg hs]; linarith
      · rw [abs_of_nonpos hs]; linarith
    nlinarith [abs_nonneg (F t), abs_nonneg (G (t - s)), mul_nonneg (abs_nonneg (F t)) (abs_nonneg (G (t - s)))]
  have hint : Integrable fun t => F t * G (t - s) :=
    (hfg.const_mul (Real.exp (-(4 * |s|)))).mono'
      (hF.meas.mul (hGm.comp (measurable_sub_const s))).aestronglyMeasurable
      (Eventually.of_forall fun t => by rw [Real.norm_eq_abs]; exact hpt t)
  have hcs := abs_integral_mul_le_sqrt_massMul hfm hgm hfi hgi
  have htr : ∫ t, g t ^ 2 = ∫ u, G u ^ 2 * Real.exp (-(8 * u)) := by
    simp_rw [hg2]
    exact integral_sub_right_eq_self (fun u => G u ^ 2 * Real.exp (-(8 * u))) s
  simp_rw [hf2] at hcs
  rw [htr] at hcs
  unfold profileCorr
  calc |∫ t, F t * G (t - s)| ≤ ∫ t, |F t * G (t - s)| := abs_integral_le_integral_abs
    _ ≤ ∫ t, Real.exp (-(4 * |s|)) * (f t * g t) :=
        integral_mono hint.abs (hfg.const_mul _) hpt
    _ = Real.exp (-(4 * |s|)) * ∫ t, f t * g t := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left ((le_abs_self _).trans hcs) (Real.exp_pos _).le

theorem integrable_leftCut_sq_exp {G : ℝ → ℝ} (hG : CriticalHalfLineEnergyDomain G) (k : ℕ) :
    Integrable fun u => leftCut G k u ^ 2 * Real.exp (-(8 * u)) :=
  hG.exponential.mono' (((measurable_leftCut hG.meas k).pow_const 2).mul
    (by fun_prop)).aestronglyMeasurable (Eventually.of_forall fun u => by
      rw [Real.norm_of_nonneg (by positivity)]
      refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
      rw [← sq_abs, ← sq_abs (G u)]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_leftCut_le G k u) 2)

theorem integral_leftCut_sq_exp_le {G : ℝ → ℝ} (hG : CriticalHalfLineEnergyDomain G) (k : ℕ) :
    ∫ u, leftCut G k u ^ 2 * Real.exp (-(8 * u)) ≤ ∫ u, G u ^ 2 * Real.exp (-(8 * u)) :=
  integral_mono (integrable_leftCut_sq_exp hG k) hG.exponential fun u => by
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    rw [← sq_abs, ← sq_abs (G u)]
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_leftCut_le G k u) 2

/-- The common decay constant of the correlations with the cut profiles. -/
def corrConst (F G : ℝ → ℝ) : ℝ :=
  Real.sqrt (∫ t, F t ^ 2 * Real.exp (-(8 * t))) * Real.sqrt (∫ u, G u ^ 2 * Real.exp (-(8 * u)))

theorem abs_profileCorr_leftCut_le {F G : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (hG : CriticalHalfLineEnergyDomain G) (k : ℕ) (s : ℝ) :
    |profileCorr F (leftCut G k) s| ≤ Real.exp (-(4 * |s|)) * corrConst F G := by
  refine (abs_profileCorr_le hF (measurable_leftCut hG.meas k) (fun u hu => leftCut_eq_zero hG.support k hu)
    (integrable_leftCut_sq_exp hG k) s).trans ?_
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (integral_leftCut_sq_exp_le hG k)) (Real.sqrt_nonneg _)) (Real.exp_pos _).le

theorem abs_profileCorr_le' {F G : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (hG : CriticalHalfLineEnergyDomain G) (s : ℝ) :
    |profileCorr F G s| ≤ Real.exp (-(4 * |s|)) * corrConst F G :=
  abs_profileCorr_le hF hG.meas hG.support hG.exponential s

theorem corrConst_nonneg (F G : ℝ → ℝ) : 0 ≤ corrConst F G := by unfold corrConst; positivity

theorem tendsto_profileCorr_leftCut {F G : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (hG : CriticalHalfLineEnergyDomain G) (s : ℝ) :
    Tendsto (fun k : ℕ => profileCorr F (leftCut G k) s) atTop (𝓝 (profileCorr F G s)) := by
  unfold profileCorr
  have hint : Integrable fun t => |F t| * |G (t - s)| :=
    GaloisForLFunctions.HTGeometry.integrable_mul_of_sq_integrable
      (continuous_abs.measurable.comp hF.meas).aestronglyMeasurable
      (continuous_abs.measurable.comp (hG.meas.comp (measurable_sub_const s))).aestronglyMeasurable
      (by simp_rw [sq_abs]; exact hF.sq) (by simp_rw [sq_abs]; exact hG.sq.comp_sub_right s)
  refine tendsto_integral_of_dominated_convergence (fun t => |F t| * |G (t - s)|)
    (fun k => (hF.meas.mul ((measurable_leftCut hG.meas k).comp
      (measurable_sub_const s))).aestronglyMeasurable) hint
    (fun k => Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (abs_leftCut_le G k _) (abs_nonneg _))
    (Eventually.of_forall fun t => tendsto_const_nhds.congr'
      ((leftCut_eventually_eq G (t - s)).mono fun k hk => by rw [hk]))

/-! ### The prime side of the heated tests -/

/-- **Fubini.** A prime term of the heated test is the cut heat average of the correlation. -/
theorem integral_mul_heatedCut (ε : ℝ) {F G : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (hG : CriticalHalfLineEnergyDomain G) (k : ℕ) (s : ℝ) :
    ∫ t, F t * heatedCut ε G k (t - s) =
      ∫ y, cutHeatKernel ε k y * profileCorr F (leftCut G k) (s + y) := by
  obtain ⟨B, hB⟩ := (continuous_cutHeatKernel ε k).bounded_above_of_compact_support
    (hasCompactSupport_cutHeatKernel ε k)
  set Φ : ℝ × ℝ → ℝ := fun p => F p.1 * (cutHeatKernel ε k p.2 * leftCut G k (p.1 - s - p.2))
  have hΦm : AEStronglyMeasurable Φ (volume.prod volume) :=
    ((hF.meas.comp measurable_fst).mul (((continuous_cutHeatKernel ε k).measurable.comp
      measurable_snd).mul ((measurable_leftCut hG.meas k).comp
        ((measurable_fst.sub_const s).sub measurable_snd)))).aestronglyMeasurable
  have hΦ : Integrable Φ (volume.prod volume) := by
    refine (integrable_prod_iff hΦm).mpr ⟨Eventually.of_forall fun t => ?_, ?_⟩
    · refine (((integrable_leftCut hG k).comp_sub_left (t - s)).const_mul (B * |F t|)).mono'
        (((continuous_cutHeatKernel ε k).measurable.mul ((measurable_leftCut hG.meas k).comp
          (measurable_const.sub measurable_id))).const_mul _).aestronglyMeasurable
        (Eventually.of_forall fun y => ?_)
      simp only [Φ]
      rw [Real.norm_eq_abs, abs_mul, abs_mul, Real.norm_eq_abs]
      have := hB y
      rw [Real.norm_eq_abs] at this
      calc |F t| * (|cutHeatKernel ε k y| * |leftCut G k (t - s - y)|)
          ≤ |F t| * (B * |leftCut G k (t - s - y)|) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right this (abs_nonneg _)) (abs_nonneg _)
        _ = B * |F t| * |leftCut G k (t - s - y)| := by ring
    · refine ((hF.integrable.norm.const_mul (B * ∫ u, |leftCut G k u|))).mono'
        hΦm.norm.integral_prod_right' (Eventually.of_forall fun t => ?_)
      rw [Real.norm_of_nonneg (integral_nonneg fun y => norm_nonneg _)]
      calc ∫ y, ‖Φ (t, y)‖ ≤ ∫ y, B * |F t| * |leftCut G k (t - s - y)| := by
            refine integral_mono_of_nonneg (Eventually.of_forall fun y => norm_nonneg _)
              (((integrable_leftCut hG k).comp_sub_left (t - s)).norm.const_mul _)
              (Eventually.of_forall fun y => ?_)
            simp only [Φ]
            rw [Real.norm_eq_abs, abs_mul, abs_mul]
            have := hB y
            rw [Real.norm_eq_abs] at this
            calc |F t| * (|cutHeatKernel ε k y| * |leftCut G k (t - s - y)|)
                ≤ |F t| * (B * |leftCut G k (t - s - y)|) :=
                  mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right this (abs_nonneg _))
                    (abs_nonneg _)
              _ = B * |F t| * |leftCut G k (t - s - y)| := by ring
        _ = B * |F t| * ∫ y, |leftCut G k (t - s - y)| := integral_const_mul _ _
        _ = B * |F t| * ∫ u, |leftCut G k u| := by
            congr 1
            exact integral_sub_left_eq_self (fun u => |leftCut G k u|) (t - s)
        _ = B * (∫ u, |leftCut G k u|) * ‖F t‖ := by rw [Real.norm_eq_abs]; ring
  have hswap := integral_integral_swap (f := fun t y => Φ (t, y)) hΦ
  have hL : ∫ t, F t * heatedCut ε G k (t - s) = ∫ t, ∫ y, Φ (t, y) := by
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [heatedCut, convolution_def, ContinuousLinearMap.mul_apply', Φ]
    rw [← integral_const_mul]
  have hR : ∫ y, ∫ t, Φ (t, y) = ∫ y, cutHeatKernel ε k y * profileCorr F (leftCut G k) (s + y) := by
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [Φ, profileCorr]
    rw [← integral_const_mul]
    congr 1; funext t
    rw [show t - s - y = t - (s + y) by ring]; ring
  rw [hL, hswap, hR]

/-- The cut heat average of the cut correlation. -/
def cutHeatAverage (ε : ℝ) (F G : ℝ → ℝ) (k : ℕ) (s : ℝ) : ℝ :=
  ∫ y, cutHeatKernel ε k y * profileCorr F (leftCut G k) (s + y)

/-- The heat average of the correlation. -/
def heatAverage (ε : ℝ) (F G : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ y, stateHeatKernel ε y * profileCorr F G (s + y)

theorem abs_cutHeatAverage_le {ε : ℝ} (hε : 0 < ε) {F G : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hG : CriticalHalfLineEnergyDomain G) (k : ℕ) (s : ℝ) :
    |cutHeatAverage ε F G k s| ≤
      Real.exp (-(4 * |s|)) * corrConst F G * ∫ y, stateHeatKernel ε y * Real.exp (4 * |y|) := by
  have hint := integrable_stateHeatKernel_mul_exp_abs hε 4
  have hpt : ∀ y, |cutHeatKernel ε k y * profileCorr F (leftCut G k) (s + y)| ≤
      Real.exp (-(4 * |s|)) * corrConst F G * (stateHeatKernel ε y * Real.exp (4 * |y|)) := by
    intro y
    rw [abs_mul, abs_of_nonneg (cutHeatKernel_nonneg hε k y)]
    have h1 := abs_profileCorr_leftCut_le hF hG k (s + y)
    have h2 : Real.exp (-(4 * |s + y|)) ≤ Real.exp (-(4 * |s|)) * Real.exp (4 * |y|) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have := abs_add_le s y
      have := abs_sub_abs_le_abs_sub s (-y)
      rw [sub_neg_eq_add, abs_neg] at this
      linarith
    calc cutHeatKernel ε k y * |profileCorr F (leftCut G k) (s + y)|
        ≤ stateHeatKernel ε y * (Real.exp (-(4 * |s + y|)) * corrConst F G) :=
          mul_le_mul (cutHeatKernel_le hε k y) h1 (abs_nonneg _) (stateHeatKernel_pos hε y).le
      _ ≤ stateHeatKernel ε y * (Real.exp (-(4 * |s|)) * Real.exp (4 * |y|) * corrConst F G) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 (corrConst_nonneg F G))
            (stateHeatKernel_pos hε y).le
      _ = _ := by ring
  unfold cutHeatAverage
  calc |∫ y, cutHeatKernel ε k y * profileCorr F (leftCut G k) (s + y)|
      ≤ ∫ y, |cutHeatKernel ε k y * profileCorr F (leftCut G k) (s + y)| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ y, Real.exp (-(4 * |s|)) * corrConst F G * (stateHeatKernel ε y * Real.exp (4 * |y|)) :=
        integral_mono_of_nonneg (Eventually.of_forall fun y => abs_nonneg _) (hint.const_mul _)
          (Eventually.of_forall hpt)
    _ = _ := integral_const_mul _ _

theorem abs_heatAverage_le {ε : ℝ} (hε : 0 < ε) {F G : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hG : CriticalHalfLineEnergyDomain G) (s : ℝ) :
    |heatAverage ε F G s| ≤
      Real.exp (-(4 * |s|)) * corrConst F G * ∫ y, stateHeatKernel ε y * Real.exp (4 * |y|) := by
  have hint := integrable_stateHeatKernel_mul_exp_abs hε 4
  have hpt : ∀ y, |stateHeatKernel ε y * profileCorr F G (s + y)| ≤
      Real.exp (-(4 * |s|)) * corrConst F G * (stateHeatKernel ε y * Real.exp (4 * |y|)) := by
    intro y
    rw [abs_mul, abs_of_pos (stateHeatKernel_pos hε y)]
    have h1 := abs_profileCorr_le' hF hG (s + y)
    have h2 : Real.exp (-(4 * |s + y|)) ≤ Real.exp (-(4 * |s|)) * Real.exp (4 * |y|) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have := abs_sub_abs_le_abs_sub s (-y)
      rw [sub_neg_eq_add, abs_neg] at this
      linarith
    calc stateHeatKernel ε y * |profileCorr F G (s + y)|
        ≤ stateHeatKernel ε y * (Real.exp (-(4 * |s|)) * Real.exp (4 * |y|) * corrConst F G) :=
          mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_right h2 (corrConst_nonneg F G)))
            (stateHeatKernel_pos hε y).le
      _ = _ := by ring
  unfold heatAverage
  calc |∫ y, stateHeatKernel ε y * profileCorr F G (s + y)|
      ≤ ∫ y, |stateHeatKernel ε y * profileCorr F G (s + y)| := abs_integral_le_integral_abs
    _ ≤ ∫ y, Real.exp (-(4 * |s|)) * corrConst F G * (stateHeatKernel ε y * Real.exp (4 * |y|)) :=
        integral_mono_of_nonneg (Eventually.of_forall fun y => abs_nonneg _) (hint.const_mul _)
          (Eventually.of_forall hpt)
    _ = _ := integral_const_mul _ _

theorem tendsto_cutHeatAverage {ε : ℝ} (hε : 0 < ε) {F G : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hG : CriticalHalfLineEnergyDomain G) (s : ℝ) :
    Tendsto (fun k : ℕ => cutHeatAverage ε F G k s) atTop (𝓝 (heatAverage ε F G s)) := by
  unfold cutHeatAverage heatAverage
  refine tendsto_integral_of_dominated_convergence (fun y => stateHeatKernel ε y * corrConst F G)
    (fun k => ((continuous_cutHeatKernel ε k).measurable.mul
      (measurable_profileCorr_leftCut hF hG k s)).aestronglyMeasurable)
    ((integrable_stateHeatKernel_mul_exp_abs hε 0).mul_const _ |>.congr
      (Eventually.of_forall fun y => by simp))
    (fun k => Eventually.of_forall fun y => ?_)
    (Eventually.of_forall fun y => (tendsto_cutHeatKernel ε y).mul
      (tendsto_profileCorr_leftCut hF hG (s + y)))
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (cutHeatKernel_nonneg hε k y)]
  refine mul_le_mul (cutHeatKernel_le hε k y) ((abs_profileCorr_leftCut_le hF hG k (s + y)).trans ?_)
    (abs_nonneg _) (stateHeatKernel_pos hε y).le
  exact mul_le_of_le_one_left (corrConst_nonneg F G) (Real.exp_le_one_iff.mpr (by positivity))

theorem continuous_profileCorr {F G : ℝ → ℝ} (hFm : Measurable F) (hGm : Measurable G)
    (hF2 : Integrable fun t => F t ^ 2) (hG2 : Integrable fun t => G t ^ 2) :
    Continuous (profileCorr F G) := by
  have h := continuous_profileCorrelation (p := cx F) (q := cx G)
    (Complex.measurable_ofReal.comp hFm) (Complex.measurable_ofReal.comp hGm)
    (by simpa [cx, Complex.norm_real, Real.norm_eq_abs, sq_abs] using hF2)
    (by simpa [cx, Complex.norm_real, Real.norm_eq_abs, sq_abs] using hG2)
  have e : profileCorr F G = fun s => (profileCorrelation (cx F) (cx G) (-s)).re := by
    funext s
    unfold profileCorr profileCorrelation
    rw [show (∫ T, cx F T * cx G (T + -s)) = ((∫ t, F t * G (t - s) : ℝ) : ℂ) by
      rw [← integral_complex_ofReal]
      exact integral_congr_ae (Eventually.of_forall fun t => by
        simp only [cx, sub_eq_add_neg]; push_cast; ring)]
    rw [Complex.ofReal_re]
  rw [e]
  exact Complex.continuous_re.comp (h.comp continuous_neg)

theorem measurable_profileCorr_leftCut {F G : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (hG : CriticalHalfLineEnergyDomain G) (k : ℕ) (s : ℝ) :
    Measurable fun y => profileCorr F (leftCut G k) (s + y) := by
  have hG2 : Integrable fun t => leftCut G k t ^ 2 :=
    hG.sq.mono' ((measurable_leftCut hG.meas k).pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun u => by
        rw [Real.norm_of_nonneg (sq_nonneg _), ← sq_abs, ← sq_abs (G u)]
        exact pow_le_pow_left₀ (abs_nonneg _) (abs_leftCut_le G k u) 2)
  exact ((continuous_profileCorr hF.meas (measurable_leftCut hG.meas k) hF.sq hG2).comp
    (continuous_const.add continuous_id)).measurable

/-! ### The form side of the heated tests -/

private theorem atomNonneg (n : ℕ) : 0 ≤ vonMangoldtAtom n := by
  unfold vonMangoldtAtom
  split_ifs
  · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
  · exact le_rfl

theorem primePairTerm_comm (a b : ℝ → ℝ) (n : ℕ) : primePairTerm b a n = primePairTerm a b n := by
  unfold primePairTerm
  have h1 : ∫ t, b t * a (t - Real.log n) = ∫ t, a t * b (t + Real.log n) := by
    rw [← integral_add_right_eq_self (fun t => b t * a (t - Real.log n)) (Real.log n)]
    congr 1; funext t; simp only [add_sub_cancel_right]; ring
  have h2 : ∫ t, b t * a (t + Real.log n) = ∫ t, a t * b (t - Real.log n) := by
    rw [← integral_sub_right_eq_self (fun t => b t * a (t + Real.log n)) (Real.log n)]
    congr 1; funext t; simp only [sub_add_cancel]; ring
  rw [h1, h2, add_comm]

theorem primeMixedForm_comm (a b : ℝ → ℝ) : primeMixedForm b a = primeMixedForm a b := by
  unfold primeMixedForm
  exact tsum_congr fun n => primePairTerm_comm a b n

theorem primeMixedForm_heatedCut (ε : ℝ) {F G : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (hG : CriticalHalfLineEnergyDomain G) (k : ℕ) :
    primeMixedForm F (heatedCut ε G k) = ∑' n : ℕ, vonMangoldtAtom n *
      (cutHeatAverage ε F G k (Real.log n) + cutHeatAverage ε F G k (-Real.log n)) := by
  unfold primeMixedForm
  refine tsum_congr fun n => ?_
  unfold primePairTerm cutHeatAverage
  rw [integral_mul_heatedCut ε hF hG k (Real.log n),
    show (∫ t, F t * heatedCut ε G k (t + Real.log n)) =
      ∫ t, F t * heatedCut ε G k (t - -Real.log n) by simp_rw [sub_neg_eq_add],
    integral_mul_heatedCut ε hF hG k (-Real.log n)]

/-- The heat average of the prime side. -/
def heatedPrime (ε : ℝ) (F G : ℝ → ℝ) : ℝ :=
  ∑' n : ℕ, vonMangoldtAtom n * (heatAverage ε F G (Real.log n) + heatAverage ε F G (-Real.log n))

theorem tendsto_primeMixedForm_heatedCut {ε : ℝ} (hε : 0 < ε) {F G : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hG : CriticalHalfLineEnergyDomain G) :
    Tendsto (fun k : ℕ => primeMixedForm F (heatedCut ε G k)) atTop (𝓝 (heatedPrime ε F G)) := by
  set T := ∫ y, stateHeatKernel ε y * Real.exp (4 * |y|)
  have hT : 0 ≤ T :=
    integral_nonneg fun y => mul_nonneg (stateHeatKernel_pos hε y).le (Real.exp_pos _).le
  simp only [primeMixedForm_heatedCut ε hF hG]
  unfold heatedPrime
  refine tendsto_tsum_of_dominated_convergence
    (bound := fun n => vonMangoldtAtom n * Real.exp (-4 * Real.log n) * (2 * corrConst F G * T))
    ((summable_primeHead_damping (c := 4) (by norm_num)).mul_right _) (fun n => ?_)
    (Eventually.of_forall fun k n => ?_)
  · exact ((tendsto_cutHeatAverage hε hF hG _).add (tendsto_cutHeatAverage hε hF hG _)).const_mul _
  · have hL : |Real.log n| = Real.log n := abs_of_nonneg (Real.log_natCast_nonneg n)
    have b1 := abs_cutHeatAverage_le hε hF hG k (Real.log n)
    have b2 := abs_cutHeatAverage_le hε hF hG k (-Real.log n)
    rw [abs_neg, hL] at b2
    rw [hL] at b1
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (atomNonneg n)]
    have h3 := abs_add_le (cutHeatAverage ε F G k (Real.log n)) (cutHeatAverage ε F G k (-Real.log n))
    calc vonMangoldtAtom n * |cutHeatAverage ε F G k (Real.log n) + cutHeatAverage ε F G k (-Real.log n)|
        ≤ vonMangoldtAtom n * (2 * (Real.exp (-(4 * Real.log n)) * corrConst F G * T)) :=
          mul_le_mul_of_nonneg_left (by linarith) (atomNonneg n)
      _ = vonMangoldtAtom n * Real.exp (-4 * Real.log n) * (2 * corrConst F G * T) := by
          rw [show -(4 * Real.log n) = -4 * Real.log n by ring]; ring

/-- The heated Gamma part. -/
def heatedGamma (ε : ℝ) (F G : ℝ → ℝ) : ℝ :=
  1 / (2 * Real.pi) * ∫ r, Real.exp (-(ε * r ^ 2)) * gammaFourierPair F G r * EF.gammaBracket r

theorem paperFT_eq_laplace (f : ℝ → ℝ) (r : ℝ) :
    paperFT (cx f) r = negativeHalfLineLaplace (cx f) (I * r) := by
  unfold paperFT negativeHalfLineLaplace
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  show cx f u * cexp (I * r * u) = cexp (I * r * u) * cx f u
  ring

theorem norm_paperFT_le_integral_abs (f : ℝ → ℝ) (r : ℝ) : ‖paperFT (cx f) r‖ ≤ ∫ u, |f u| := by
  unfold paperFT
  refine (norm_integral_le_integral_norm _).trans_eq
    (integral_congr_ae (Eventually.of_forall fun u => ?_))
  change ‖((f u : ℝ) : ℂ) * cexp (I * r * u)‖ = |f u|
  rw [norm_mul, show I * (r : ℂ) * u = ((r * u : ℝ) : ℂ) * I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

theorem continuous_gammaFourierPair {f g : ℝ → ℝ} (hf : Integrable f) (hg : Integrable g) :
    Continuous (gammaFourierPair f g) := by
  unfold gammaFourierPair
  have h1 := continuous_paperFT_cx hf
  have h2 := continuous_paperFT_cx hg
  exact ((Complex.continuous_re.comp h1).mul (Complex.continuous_re.comp h2)).add
    ((Complex.continuous_im.comp h1).mul (Complex.continuous_im.comp h2))

/-- The Gamma bracket against a quadratic decay is integrable: `|γ(r)| = O(√|r|)`. -/
theorem integrable_gammaGrowth (c : ℝ) :
    Integrable fun r : ℝ => (1 + r ^ 2)⁻¹ * (c + 2 * Real.sqrt (1 + |r|)) := by
  have h2 : Integrable fun r : ℝ => (1 + |r|) ^ (-(3 / 2 : ℝ)) := by
    have := integrable_one_add_norm (E := ℝ) (r := 3 / 2) (by norm_num)
    simpa [Real.norm_eq_abs] using this
  refine ((integrable_inv_one_add_sq.mul_const |c|).add (h2.const_mul 4)).mono'
    (by fun_prop) (Eventually.of_forall fun r => ?_)
  have hx : 0 < 1 + |r| := by positivity
  have hs : 0 ≤ Real.sqrt (1 + |r|) := Real.sqrt_nonneg _
  have e : Real.sqrt (1 + |r|) / (1 + |r|) ^ 2 = (1 + |r|) ^ (-(3 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_sub hx]; norm_num
  have hle : (1 + r ^ 2)⁻¹ ≤ 2 / (1 + |r|) ^ 2 := by
    rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_abs r, abs_nonneg r]
  rw [Real.norm_eq_abs]
  calc |(1 + r ^ 2)⁻¹ * (c + 2 * Real.sqrt (1 + |r|))|
      ≤ (1 + r ^ 2)⁻¹ * (|c| + 2 * Real.sqrt (1 + |r|)) := by
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (1 + r ^ 2)⁻¹)]
        refine mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans ?_) (by positivity)
        rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.sqrt (1 + |r|))]
    _ = (1 + r ^ 2)⁻¹ * |c| + (1 + r ^ 2)⁻¹ * (2 * Real.sqrt (1 + |r|)) := by ring
    _ ≤ (1 + r ^ 2)⁻¹ * |c| + 2 / (1 + |r|) ^ 2 * (2 * Real.sqrt (1 + |r|)) := by gcongr
    _ = (1 + r ^ 2)⁻¹ * |c| + 4 * (Real.sqrt (1 + |r|) / (1 + |r|) ^ 2) := by ring
    _ = (1 + r ^ 2)⁻¹ * |c| + 4 * (1 + |r|) ^ (-(3 / 2 : ℝ)) := by rw [e]

theorem tendsto_gammaMixedForm_heatedCut {ε : ℝ} (hε : 0 < ε) {F G : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hG : CriticalHalfLineEnergyDomain G) :
    Tendsto (fun k : ℕ => gammaMixedForm F (heatedCut ε G k)) atTop (𝓝 (heatedGamma ε F G)) := by
  obtain ⟨M, hM0, hM⟩ := exists_laplace_cutHeatKernel_le hε
  set A' := ∫ y, stateHeatKernel ε y * Real.exp (|y| / 2)
  have hA' : 0 ≤ A' :=
    integral_nonneg fun y => mul_nonneg (stateHeatKernel_pos hε y).le (Real.exp_pos _).le
  set CF := ∫ u, |F u|
  set CG := ∫ u, |G u|
  have hCF : 0 ≤ CF := integral_nonneg fun u => abs_nonneg _
  have hCG : 0 ≤ CG := integral_nonneg fun u => abs_nonneg _
  obtain ⟨c₀, hγ⟩ : ∃ c : ℝ, ∀ r, |EF.gammaBracket r| ≤ c + 2 * Real.sqrt (1 + |r|) :=
    ⟨_, RHTower.WeilSpectral.abs_gammaBracket_le_sqrt⟩
  have hIr : ∀ r : ℝ, |(I * (r : ℂ)).re| ≤ 1 / 2 := fun r => by simp
  have hker : ∀ (k : ℕ) (r : ℝ),
      ‖negativeHalfLineLaplace (cx (cutHeatKernel ε k)) (I * r)‖ ≤ 2 * (A' + M) / (1 + r ^ 2) := by
    intro k r
    rw [le_div_iff₀ (by positivity)]
    have hn := norm_nonneg (negativeHalfLineLaplace (cx (cutHeatKernel ε k)) (I * r))
    rcases le_or_gt |r| 1 with hr | hr
    · have h1 := norm_laplace_cutHeatKernel_le hε k (hIr r)
      have : r ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg r]
      nlinarith
    · have hr' : r ≠ 0 := by intro h; rw [h, abs_zero] at hr; linarith
      have hr0 : I * (r : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (Complex.ofReal_ne_zero.mpr hr')
      have h1 := hM k (I * r) (hIr r) hr0
      have hn' : ‖I * (r : ℂ)‖ = |r| := by
        rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
      rw [hn'] at h1
      have hrr : |r|⁻¹ ^ 2 * r ^ 2 = 1 := by
        rw [inv_pow, sq_abs, inv_mul_cancel₀ (pow_ne_zero 2 hr')]
      have h2 : ‖negativeHalfLineLaplace (cx (cutHeatKernel ε k)) (I * r)‖ * r ^ 2 ≤ M := by
        calc _ ≤ M * |r|⁻¹ ^ 2 * r ^ 2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
          _ = M := by rw [mul_assoc, hrr, mul_one]
      have : 1 ≤ r ^ 2 := by rw [← sq_abs]; nlinarith
      nlinarith
  have hGk : ∀ (k : ℕ) (r : ℝ), ‖negativeHalfLineLaplace (cx (leftCut G k)) (I * r)‖ ≤ CG := by
    intro k r
    rw [← paperFT_eq_laplace]
    exact (norm_paperFT_le_integral_abs _ r).trans (integral_mono (integrable_leftCut hG k).abs
      hG.integrable.abs fun u => abs_leftCut_le G k u)
  have hdom : ∀ (k : ℕ) (r : ℝ), ‖gammaFourierPair F (heatedCut ε G k) r * EF.gammaBracket r‖ ≤
      CF * CG * (2 * (A' + M)) * ((1 + r ^ 2)⁻¹ * (|c₀| + 2 * Real.sqrt (1 + |r|))) := by
    intro k r
    rw [Real.norm_eq_abs, abs_mul]
    have h1 := abs_gammaFourierPair_le_mul F (heatedCut ε G k) r
    have h2 : ‖paperFT (cx (heatedCut ε G k)) r‖ ≤ 2 * (A' + M) / (1 + r ^ 2) * CG := by
      rw [paperFT_eq_laplace, laplace_heatedCut ε hG k (hIr r), norm_mul]
      exact mul_le_mul (hker k r) (hGk k r) (norm_nonneg _) (by positivity)
    have h3 := norm_paperFT_le_integral_abs F r
    have h4 : |EF.gammaBracket r| ≤ |c₀| + 2 * Real.sqrt (1 + |r|) :=
      (hγ r).trans (by linarith [le_abs_self c₀])
    calc |gammaFourierPair F (heatedCut ε G k) r| * |EF.gammaBracket r|
        ≤ (CF * (2 * (A' + M) / (1 + r ^ 2) * CG)) * (|c₀| + 2 * Real.sqrt (1 + |r|)) :=
          mul_le_mul (h1.trans (mul_le_mul h3 h2 (norm_nonneg _) hCF)) h4 (abs_nonneg _)
            (by positivity)
      _ = _ := by ring
  have hlim : ∀ r : ℝ, Tendsto (fun k : ℕ => gammaFourierPair F (heatedCut ε G k) r *
      EF.gammaBracket r) atTop
      (𝓝 (Real.exp (-(ε * r ^ 2)) * gammaFourierPair F G r * EF.gammaBracket r)) := by
    intro r
    have hH : Tendsto (fun k : ℕ => paperFT (cx (heatedCut ε G k)) r) atTop
        (𝓝 (((Real.exp (-(ε * r ^ 2)) : ℝ) : ℂ) * paperFT (cx G) r)) := by
      have h := (tendsto_laplace_cutHeatKernel hε (hIr r)).mul (tendsto_laplace_leftCut hG (hIr r))
      have e1 : cexp (ε * (I * r) ^ 2) = ((Real.exp (-(ε * r ^ 2)) : ℝ) : ℂ) := by
        push_cast; congr 1; rw [mul_pow, I_sq]; ring
      rw [e1, ← paperFT_eq_laplace] at h
      exact h.congr fun k => by rw [paperFT_eq_laplace, laplace_heatedCut ε hG k (hIr r)]
    unfold gammaFourierPair
    have hre := (Complex.continuous_re.tendsto _).comp hH
    have him := (Complex.continuous_im.tendsto _).comp hH
    have h := ((hre.const_mul (paperFT (cx F) r).re).add
      (him.const_mul (paperFT (cx F) r).im)).mul_const (EF.gammaBracket r)
    convert h using 2
    simp only [Complex.re_ofReal_mul, Complex.im_ofReal_mul]
    ring
  unfold gammaMixedForm heatedGamma
  refine Tendsto.const_mul _ (tendsto_integral_of_dominated_convergence _
    (fun k => ((continuous_gammaFourierPair hF.integrable
      (((contDiff_heatedCut ε hG k).continuous).integrable_of_hasCompactSupport
        (hasCompactSupport_heatedCut ε hG k))).mul
      WeilHerglotz.continuous_gammaBracket).aestronglyMeasurable)
    ((integrable_gammaGrowth |c₀|).const_mul _)
    (fun k => Eventually.of_forall fun r => hdom k r) (Eventually.of_forall hlim))

/-! ### The charges of the heated tests -/

theorem coshHalfMoment_eq_laplace {f : ℝ → ℝ} (h1 : Integrable fun x => f x * Real.exp (1 / 2 * x))
    (h2 : Integrable fun x => f x * Real.exp (-(1 / 2) * x)) :
    coshHalfMoment f = ((∫ x, f x * Real.exp (1 / 2 * x)) + ∫ x, f x * Real.exp (-(1 / 2) * x)) / 2 := by
  unfold coshHalfMoment
  rw [← integral_add h1 h2, ← integral_div]
  congr 1; funext x
  rw [Real.cosh_eq, show x / 2 = 1 / 2 * x by ring, show -(1 / 2 * x) = -(1 / 2) * x by ring]
  ring

theorem sinhHalfMoment_eq_laplace {f : ℝ → ℝ} (h1 : Integrable fun x => f x * Real.exp (1 / 2 * x))
    (h2 : Integrable fun x => f x * Real.exp (-(1 / 2) * x)) :
    sinhHalfMoment f = ((∫ x, f x * Real.exp (1 / 2 * x)) - ∫ x, f x * Real.exp (-(1 / 2) * x)) / 2 := by
  unfold sinhHalfMoment
  rw [← integral_sub h1 h2, ← integral_div]
  congr 1; funext x
  rw [Real.sinh_eq, show x / 2 = 1 / 2 * x by ring, show -(1 / 2 * x) = -(1 / 2) * x by ring]
  ring

theorem integrable_mul_rexp_of_domain {G : ℝ → ℝ} (hG : CriticalHalfLineEnergyDomain G) {p : ℝ}
    (hp : -4 < p) : Integrable fun x => G x * Real.exp (p * x) :=
  (integrable_abs_mul_exp_of_domain hG hp).mono' (hG.meas.mul (by fun_prop)).aestronglyMeasurable
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)])

theorem integrable_heatedCut_mul_exp (ε : ℝ) {G : ℝ → ℝ} (hG : CriticalHalfLineEnergyDomain G)
    (k : ℕ) (p : ℝ) : Integrable fun x => heatedCut ε G k x * Real.exp (p * x) :=
  (((contDiff_heatedCut ε hG k).continuous).mul (by fun_prop)).integrable_of_hasCompactSupport
    (hasCompactSupport_heatedCut ε hG k).mul_right

theorem tendsto_realLaplace_heatedCut {ε : ℝ} (hε : 0 < ε) {G : ℝ → ℝ}
    (hG : CriticalHalfLineEnergyDomain G) {p : ℝ} (hp : |p| ≤ 1 / 2) :
    Tendsto (fun k : ℕ => ∫ x, heatedCut ε G k x * Real.exp (p * x)) atTop
      (𝓝 (Real.exp (ε / 4 * (4 * p ^ 2)) * ∫ x, G x * Real.exp (p * x))) := by
  have hpr : |((p : ℂ)).re| ≤ 1 / 2 := by rw [Complex.ofReal_re]; exact hp
  have h := (tendsto_laplace_cutHeatKernel hε hpr).mul (tendsto_laplace_leftCut hG hpr)
  have e1 : ∀ k : ℕ, negativeHalfLineLaplace (cx (cutHeatKernel ε k)) p *
      negativeHalfLineLaplace (cx (leftCut G k)) p =
      ((∫ x, heatedCut ε G k x * Real.exp (p * x) : ℝ) : ℂ) := fun k => by
    rw [← laplace_heatedCut ε hG k hpr, negativeHalfLineLaplace_ofReal]
  have e2 : cexp (ε * (p : ℂ) ^ 2) * negativeHalfLineLaplace (cx G) p =
      ((Real.exp (ε / 4 * (4 * p ^ 2)) * ∫ x, G x * Real.exp (p * x) : ℝ) : ℂ) := by
    rw [negativeHalfLineLaplace_ofReal]
    push_cast
    congr 2
    ring
  rw [e2] at h
  have h' := h.congr e1
  simpa using (Complex.continuous_re.tendsto _).comp h'

theorem tendsto_coshHalfMoment_heatedCut {ε : ℝ} (hε : 0 < ε) {G : ℝ → ℝ}
    (hG : CriticalHalfLineEnergyDomain G) :
    Tendsto (fun k : ℕ => coshHalfMoment (heatedCut ε G k)) atTop
      (𝓝 (Real.exp (ε / 4) * coshHalfMoment G)) := by
  have hp := tendsto_realLaplace_heatedCut hε hG (p := 1 / 2) (by norm_num [abs_of_pos])
  have hm := tendsto_realLaplace_heatedCut hε hG (p := -(1 / 2)) (by norm_num [abs_of_pos])
  rw [coshHalfMoment_eq_laplace (integrable_mul_rexp_of_domain hG (by norm_num))
    (integrable_mul_rexp_of_domain hG (by norm_num))]
  have e : ∀ k : ℕ, coshHalfMoment (heatedCut ε G k) =
      ((∫ x, heatedCut ε G k x * Real.exp (1 / 2 * x)) +
        ∫ x, heatedCut ε G k x * Real.exp (-(1 / 2) * x)) / 2 := fun k =>
    coshHalfMoment_eq_laplace (integrable_heatedCut_mul_exp ε hG k _)
      (integrable_heatedCut_mul_exp ε hG k _)
  simp only [e]
  convert (hp.add hm).div_const 2 using 2
  norm_num
  ring

theorem tendsto_sinhHalfMoment_heatedCut {ε : ℝ} (hε : 0 < ε) {G : ℝ → ℝ}
    (hG : CriticalHalfLineEnergyDomain G) :
    Tendsto (fun k : ℕ => sinhHalfMoment (heatedCut ε G k)) atTop
      (𝓝 (Real.exp (ε / 4) * sinhHalfMoment G)) := by
  have hp := tendsto_realLaplace_heatedCut hε hG (p := 1 / 2) (by norm_num [abs_of_pos])
  have hm := tendsto_realLaplace_heatedCut hε hG (p := -(1 / 2)) (by norm_num [abs_of_pos])
  rw [sinhHalfMoment_eq_laplace (integrable_mul_rexp_of_domain hG (by norm_num))
    (integrable_mul_rexp_of_domain hG (by norm_num))]
  have e : ∀ k : ℕ, sinhHalfMoment (heatedCut ε G k) =
      ((∫ x, heatedCut ε G k x * Real.exp (1 / 2 * x)) -
        ∫ x, heatedCut ε G k x * Real.exp (-(1 / 2) * x)) / 2 := fun k =>
    sinhHalfMoment_eq_laplace (integrable_heatedCut_mul_exp ε hG k _)
      (integrable_heatedCut_mul_exp ε hG k _)
  simp only [e]
  convert (hp.sub hm).div_const 2 using 2
  norm_num
  ring

/-! ### The heated pairing is the heated form -/

/-- The heated form: Gamma part damped by `e^{−εr²}`, prime terms heat-averaged, charges times
`e^{ε/4}`. -/
def heatedForm (ε : ℝ) (F G : ℝ → ℝ) : ℝ :=
  heatedGamma ε F G - heatedPrime ε F G + Real.exp (ε / 4) *
    (2 * coshHalfMoment F * coshHalfMoment G - 2 * sinhHalfMoment F * sinhHalfMoment G)

theorem tendsto_bareMixedEnergy_heatedCut {ε : ℝ} (hε : 0 < ε) {F G : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hG : CriticalHalfLineEnergyDomain G) :
    Tendsto (fun k : ℕ => bareMixedEnergy F (heatedCut ε G k)) atTop (𝓝 (heatedForm ε F G)) := by
  have e : ∀ k : ℕ, bareMixedEnergy F (heatedCut ε G k) = gammaMixedForm F (heatedCut ε G k) -
      primeMixedForm F (heatedCut ε G k) + (2 * coshHalfMoment F * coshHalfMoment (heatedCut ε G k) -
        2 * sinhHalfMoment F * sinhHalfMoment (heatedCut ε G k)) := fun k => by
    unfold bareMixedEnergy
    rw [primeMixedForm_comm]
    ring
  simp only [e]
  have h := ((tendsto_gammaMixedForm_heatedCut hε hF hG).sub
    (tendsto_primeMixedForm_heatedCut hε hF hG)).add
    (((tendsto_coshHalfMoment_heatedCut hε hG).const_mul (2 * coshHalfMoment F)).sub
      ((tendsto_sinhHalfMoment_heatedCut hε hG).const_mul (2 * sinhHalfMoment F)))
  have hv : heatedForm ε F G = heatedGamma ε F G - heatedPrime ε F G +
      (2 * coshHalfMoment F * (Real.exp (ε / 4) * coshHalfMoment G) -
        2 * sinhHalfMoment F * (Real.exp (ε / 4) * sinhHalfMoment G)) := by
    unfold heatedForm; ring
  rw [hv]
  exact h

/-- **At every positive heat the zero pairing is the heated form.** -/
theorem heatedZeroPairing_eq_heatedForm {ε : ℝ} (hε : 0 < ε) {F G : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hG : CriticalHalfLineEnergyDomain G) :
    ∑' q : XiZeroCopy, negativeHalfLineLaplace (cx F) (centredZero q) *
        negativeHalfLineLaplace (cx G) (-centredZero q) * Complex.exp ((ε : ℂ) * centredZero q ^ 2) =
      ((heatedForm ε F G : ℝ) : ℂ) := by
  have h1 := tendsto_zeroPairing_heatedCut hε hF hG
  have h2 := (Complex.continuous_ofReal.tendsto _).comp (tendsto_bareMixedEnergy_heatedCut hε hF hG)
  have e : ∀ k : ℕ, ∑' q : XiZeroCopy, negativeHalfLineLaplace (cx F) (centredZero q) *
      negativeHalfLineLaplace (cx (heatedCut ε G k)) (-centredZero q) =
      ((bareMixedEnergy F (heatedCut ε G k) : ℝ) : ℂ) := fun k =>
    (hasSum_bareMixedEnergy_of_compactSupport hF (contDiff_heatedCut ε hG k)
      (hasCompactSupport_heatedCut ε hG k)).tsum_eq
  exact tendsto_nhds_unique (h1.congr e) h2

/-! ### Removing the heat -/

theorem tendsto_heatAverage {F G : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (hG : CriticalHalfLineEnergyDomain G) (s : ℝ) :
    Tendsto (fun ε : ℝ => heatAverage ε F G s) (𝓝[>] 0) (𝓝 (profileCorr F G s)) := by
  have hc := continuous_profileCorr hF.meas hG.meas hF.sq hG.sq
  have hC : Continuous fun y : ℝ => ((profileCorr F G (s + y) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (hc.comp (continuous_const.add continuous_id))
  have hM : ∀ y : ℝ, ‖((profileCorr F G (s + y) : ℝ) : ℂ)‖ ≤ corrConst F G := fun y => by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact (abs_profileCorr_le' hF hG _).trans
      (mul_le_of_le_one_left (corrConst_nonneg F G) (Real.exp_le_one_iff.mpr (by positivity)))
  have h := tendsto_integral_tiltedHeatKernel_mul hC hM 0
  have e : ∀ ε : ℝ, (∫ y, ((tiltedHeatKernel ε 0 y : ℝ) : ℂ) * ((profileCorr F G (s + y) : ℝ) : ℂ)) =
      ((heatAverage ε F G s : ℝ) : ℂ) := fun ε => by
    unfold heatAverage tiltedHeatKernel
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp
  simp only [e, add_zero] at h
  simpa using (Complex.continuous_re.tendsto _).comp h

theorem tendsto_heatedPrime {F G : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (hG : CriticalHalfLineEnergyDomain G) :
    Tendsto (fun ε : ℝ => heatedPrime ε F G) (𝓝[>] 0) (𝓝 (primeMixedForm F G)) := by
  have hP : primeMixedForm F G = ∑' n : ℕ, vonMangoldtAtom n *
      (profileCorr F G (Real.log n) + profileCorr F G (-Real.log n)) := by
    unfold primeMixedForm
    refine tsum_congr fun n => ?_
    unfold primePairTerm profileCorr
    simp_rw [sub_neg_eq_add]
  rw [hP]
  unfold heatedPrime
  refine tendsto_tsum_of_dominated_convergence
    (bound := fun n => vonMangoldtAtom n * Real.exp (-4 * Real.log n) *
      (2 * corrConst F G * (2 * Real.exp 16)))
    ((summable_primeHead_damping (c := 4) (by norm_num)).mul_right _)
    (fun n => ((tendsto_heatAverage hF hG _).add (tendsto_heatAverage hF hG _)).const_mul _) ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε n
  have hε0 : 0 < ε := hε.1
  have hT : ∫ y, stateHeatKernel ε y * Real.exp (4 * |y|) ≤ 2 * Real.exp 16 :=
    (integral_stateHeatKernel_mul_exp_four_le hε0).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [hε.2])) (by norm_num))
  have hL : |Real.log n| = Real.log n := abs_of_nonneg (Real.log_natCast_nonneg n)
  have b1 := abs_heatAverage_le hε0 hF hG (Real.log n)
  have b2 := abs_heatAverage_le hε0 hF hG (-Real.log n)
  rw [abs_neg, hL] at b2
  rw [hL] at b1
  have hK : 0 ≤ Real.exp (-(4 * Real.log n)) * corrConst F G :=
    mul_nonneg (Real.exp_pos _).le (corrConst_nonneg F G)
  have b1' := b1.trans (mul_le_mul_of_nonneg_left hT hK)
  have b2' := b2.trans (mul_le_mul_of_nonneg_left hT hK)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (atomNonneg n)]
  have h3 := abs_add_le (heatAverage ε F G (Real.log n)) (heatAverage ε F G (-Real.log n))
  calc vonMangoldtAtom n * |heatAverage ε F G (Real.log n) + heatAverage ε F G (-Real.log n)|
      ≤ vonMangoldtAtom n * (2 * (Real.exp (-(4 * Real.log n)) * corrConst F G * (2 * Real.exp 16))) :=
        mul_le_mul_of_nonneg_left (by linarith) (atomNonneg n)
    _ = vonMangoldtAtom n * Real.exp (-4 * Real.log n) * (2 * corrConst F G * (2 * Real.exp 16)) := by
        rw [show -(4 * Real.log n) = -4 * Real.log n by ring]; ring

theorem tendsto_heatedGamma {F G : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (hG : CriticalHalfLineEnergyDomain G) :
    Tendsto (fun ε : ℝ => heatedGamma ε F G) (𝓝[>] 0) (𝓝 (gammaMixedForm F G)) := by
  have hi := integrable_gammaFourierPair hF.integrable hG.integrable hF.gamma hG.gamma
  have hc := continuous_gammaFourierPair hF.integrable hG.integrable
  unfold heatedGamma gammaMixedForm
  refine Tendsto.const_mul _ (tendsto_integral_filter_of_dominated_convergence
    (fun r => |gammaFourierPair F G r * EF.gammaBracket r|)
    (Eventually.of_forall fun ε => (((by fun_prop : Continuous fun r : ℝ =>
      Real.exp (-(ε * r ^ 2))).mul hc).mul WeilHerglotz.continuous_gammaBracket).aestronglyMeasurable)
    (self_mem_nhdsWithin.mono fun ε (hε : 0 < ε) => Eventually.of_forall fun r => ?_)
    hi.abs (Eventually.of_forall fun r => ?_))
  · rw [Real.norm_eq_abs, mul_assoc, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_left (abs_nonneg _) (Real.exp_le_one_iff.mpr (by
      have := sq_nonneg r; nlinarith))
  · have h0 : Tendsto (fun ε : ℝ => Real.exp (-(ε * r ^ 2))) (𝓝[>] 0) (𝓝 1) := by
      have := ((by fun_prop : Continuous fun ε : ℝ => Real.exp (-(ε * r ^ 2))).tendsto 0).mono_left
        nhdsWithin_le_nhds
      simpa using this
    simpa [mul_assoc] using (h0.mul_const (gammaFourierPair F G r * EF.gammaBracket r))

theorem tendsto_heatedForm {F G : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (hG : CriticalHalfLineEnergyDomain G) :
    Tendsto (fun ε : ℝ => heatedForm ε F G) (𝓝[>] 0) (𝓝 (bareMixedEnergy F G)) := by
  have he : Tendsto (fun ε : ℝ => Real.exp (ε / 4)) (𝓝[>] 0) (𝓝 1) := by
    have := ((by fun_prop : Continuous fun ε : ℝ => Real.exp (ε / 4)).tendsto 0).mono_left
      nhdsWithin_le_nhds
    simpa using this
  have h := ((tendsto_heatedGamma hF hG).sub (tendsto_heatedPrime hF hG)).add
    (he.mul_const (2 * coshHalfMoment F * coshHalfMoment G - 2 * sinhHalfMoment F * sinhHalfMoment G))
  have hv : bareMixedEnergy F G = gammaMixedForm F G - primeMixedForm F G + 1 *
      (2 * coshHalfMoment F * coshHalfMoment G - 2 * sinhHalfMoment F * sinhHalfMoment G) := by
    unfold bareMixedEnergy
    rw [primeMixedForm_comm]
    ring
  rw [hv]
  exact h

/-- **The heated zero pairing of two profiles is Weil's form.** For `F, G` in the energy domain,
`lim_{ε→0⁺} Σ_z L F(z) L G(−z) e^{εz²} = W(F, G)`, the sum over the centred zeros with
multiplicity. -/
theorem tendsto_heatedZeroPairing {F G : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (hG : CriticalHalfLineEnergyDomain G) :
    Tendsto (fun ε : ℝ => ∑' q : XiZeroCopy, negativeHalfLineLaplace (cx F) (centredZero q) *
        negativeHalfLineLaplace (cx G) (-centredZero q) * Complex.exp ((ε : ℂ) * centredZero q ^ 2))
      (𝓝[>] 0) (𝓝 ((bareMixedEnergy F G : ℝ) : ℂ)) := by
  refine ((Complex.continuous_ofReal.tendsto _).comp (tendsto_heatedForm hF hG)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  exact (heatedZeroPairing_eq_heatedForm hε hF hG).symm

#print axioms tendsto_heatedZeroPairing

end GaloisForLFunctions.ExclusionOfTheCriticalState
