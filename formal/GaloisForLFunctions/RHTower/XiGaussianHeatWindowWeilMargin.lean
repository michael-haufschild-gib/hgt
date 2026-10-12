import GaloisForLFunctions.RHTower.XiGaussianHeatWeilMarginInterface
import GaloisForLFunctions.RHTower.XiGaussianHeatHankelExponentialTypeTransfer

/-!
# A Weil margin forces positivity of the heat Hankel form on the pole hyperplane

Fix an aperture `A`, radii `0 < B₀ < B₁ < A`, a heat time `0 < a < 1` and a real polynomial `P`
with `P(−1/4) = 0`.  Let `g = Q e^{-x²/(2a)}` be the physical heat test of `P`, `χ` the smooth even
cutoff (`1` on `|x| ≤ B₀`, `0` on `|x| ≥ B₁`), and correct the truncation `gχ` by a multiple of `χ`
so that its exponential moment vanishes:

`u = (g − κ) χ`,   `κ = ∫ g χ e^{x/2} / ∫ χ e^{x/2}`.

Then `u` is a pole-vanishing real even source at aperture `A`, so the pole-vanishing ground energy
`μ₀(A)` bounds its Weil energy `Re Σ_q F_u(z_q)²` from below.  Since `H_a(P, P) = Σ_q G(z_q)²` with
`G = F_g`, and `G − F_u = F_h` for `h = g(1 − χ) + κχ`, which lives beyond `|x| = B₀` up to the small
multiple `κ` of the cutoff, integration by parts on the strip gives
(`le_re_heatHankel_of_polarGroundEnergy`)

`μ₀(A) ((V − T)/2 − 2B₀κ²) ≤ Re H_a(P, P) + (2Mρ + ρ²) Σ_q |z_q|^{-2}`,

with `V = ∫ g²`, `T = ∫_{|x| ≥ B₀} g²`, `M = ∫ |g'| e^{|x|/2}`,
`ρ = ∫_{|x|≥B₀} |g'| e^{|x|/2} + C ∫_{|x|≥B₀} |g| e^{|x|/2} + |κ| ∫ |χ'| e^{|x|/2}` and `C ≥ |χ'|`.
The pole moment `∫ g e^{x/2} = G(−i/2) = e^{a/8} P(−1/4)` vanishes, so `κ` is controlled by the tail:
`|κ| ∫ χ e^{x/2} ≤ ∫_{|x| ≥ B₀} |g| e^{|x|/2}` (`abs_heatPoleCorrection_mul_le`).
-/

open scoped Real
open Complex MeasureTheory Set Polynomial
open GaloisForLFunctions (gaussPolyFun gaussPolyDerivPoly continuous_gaussPolyFun
  hasDerivAt_gaussPolyFun gaussPolyFun_neg_of_even sq_integral_abs_gaussPolyFun_mul_exp_half_le
  integrable_gaussPolyFun_sq)

namespace RHTower

noncomputable section

theorem contDiff_gaussPolyFun (Q : ℝ[X]) (β : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (gaussPolyFun Q β) := by
  have hQ : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => Q.eval x) := by
    have := Polynomial.contDiff_aeval (𝕜 := ℝ) (R := ℝ) Q ((⊤ : ℕ∞) : WithTop ℕ∞)
    simpa [Polynomial.coe_aeval_eq_eval] using this
  have he : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => Real.exp (-(β * x ^ 2))) :=
    Real.contDiff_exp.comp ((contDiff_const.mul (contDiff_id.pow 2)).neg)
  exact hQ.mul he

/-- The physical heat test `g = Q e^{-x²/(2a)}` of a real polynomial. -/
def heatTest (a : ℝ) (P : ℝ[X]) : ℝ → ℝ := gaussPolyFun (heatPolyR a P) (1 / (2 * a))

/-- Its derivative. -/
def heatTestDeriv (a : ℝ) (P : ℝ[X]) : ℝ → ℝ :=
  gaussPolyFun (gaussPolyDerivPoly (heatPolyR a P) (1 / (2 * a))) (1 / (2 * a))

/-- The exponential moment `∫ χ e^{x/2}` of the cutoff. -/
def cutoffMoment (B₀ B₁ : ℝ) : ℝ := ∫ x, heatCutoff B₀ B₁ x * Real.exp (x / 2)

/-- The pole correction `κ = ∫ g χ e^{x/2} / ∫ χ e^{x/2}`. -/
def heatPoleCorrection (a : ℝ) (P : ℝ[X]) (B₀ B₁ : ℝ) : ℝ :=
  (∫ x, heatTest a P x * heatCutoff B₀ B₁ x * Real.exp (x / 2)) / cutoffMoment B₀ B₁

/-- The corrected truncation `u = (g − κ) χ`. -/
def heatSource (a : ℝ) (P : ℝ[X]) (B₀ B₁ : ℝ) (x : ℝ) : ℝ :=
  (heatTest a P x - heatPoleCorrection a P B₀ B₁) * heatCutoff B₀ B₁ x

/-- The strip mass `∫_S |f| e^{|x|/2}` on a set. -/
def stripMassOn (f : ℝ → ℝ) (S : Set ℝ) : ℝ := ∫ x in S, |f x| * Real.exp (|x| / 2)

/-- The tail set `|x| ≥ L`. -/
def heatTailSet (L : ℝ) : Set ℝ := {x : ℝ | L ≤ |x|}

theorem measurableSet_heatTailSet (L : ℝ) : MeasurableSet (heatTailSet L) :=
  measurableSet_le measurable_const continuous_abs.measurable

variable {B₀ B₁ : ℝ}

/-! ## Basic properties -/

theorem hasDerivAt_heatTest (a : ℝ) (P : ℝ[X]) (x : ℝ) :
    HasDerivAt (heatTest a P) (heatTestDeriv a P x) x :=
  hasDerivAt_gaussPolyFun _ _ x

theorem continuous_heatTest (a : ℝ) (P : ℝ[X]) : Continuous (heatTest a P) :=
  continuous_gaussPolyFun _ _

theorem continuous_heatTestDeriv (a : ℝ) (P : ℝ[X]) : Continuous (heatTestDeriv a P) :=
  continuous_gaussPolyFun _ _

theorem heatTest_neg (a : ℝ) (P : ℝ[X]) (x : ℝ) : heatTest a P (-x) = heatTest a P x :=
  gaussPolyFun_neg_of_even _ (heatPolyR_comp_neg a P) _ _

theorem integrable_abs_heatTest_mul_exp {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (P : ℝ[X]) :
    Integrable (fun x => |heatTest a P x| * Real.exp (|x| / 2)) := by
  have hβ : 1 / 2 < 1 / (2 * a) := by
    rw [lt_div_iff₀ (by positivity)]; nlinarith
  exact (sq_integral_abs_gaussPolyFun_mul_exp_half_le (heatPolyR a P) hβ one_pos 0).1

theorem integrable_abs_heatTestDeriv_mul_exp {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (P : ℝ[X]) :
    Integrable (fun x => |heatTestDeriv a P x| * Real.exp (|x| / 2)) := by
  have hβ : 1 / 2 < 1 / (2 * a) := by
    rw [lt_div_iff₀ (by positivity)]; nlinarith
  exact (sq_integral_abs_gaussPolyFun_mul_exp_half_le _ hβ one_pos 0).1

theorem integrable_of_abs_mul_exp {f : ℝ → ℝ} (hf : Continuous f)
    (hint : Integrable (fun x => |f x| * Real.exp (|x| / 2))) : Integrable f := by
  refine hint.mono' hf.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  have : 1 ≤ Real.exp (|x| / 2) := Real.one_le_exp (by positivity)
  nlinarith [abs_nonneg (f x)]

theorem integrable_mul_exp_half_of_abs {f : ℝ → ℝ} (hf : Continuous f)
    (hint : Integrable (fun x => |f x| * Real.exp (|x| / 2))) :
    Integrable (fun x => f x * Real.exp (x / 2)) := by
  refine hint.mono' (hf.mul (Real.continuous_exp.comp (continuous_id.div_const 2))).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  have : Real.exp (x / 2) ≤ Real.exp (|x| / 2) :=
    Real.exp_le_exp.2 (by linarith [le_abs_self x])
  exact mul_le_mul_of_nonneg_left this (abs_nonneg _)

theorem integrable_of_continuous_compact {f : ℝ → ℝ} (hf : Continuous f) (hc : HasCompactSupport f)
    {w : ℝ → ℝ} (hw : Continuous w) : Integrable (fun x => f x * w x) :=
  (hf.mul hw).integrable_of_hasCompactSupport (hc.mul_right)

theorem continuous_heatCutoff : Continuous (heatCutoff B₀ B₁) :=
  (contDiff_heatCutoff B₀ B₁).continuous

theorem cutoffMoment_pos (h0 : 0 < B₀) (h01 : B₀ < B₁) : 0 < cutoffMoment B₀ B₁ := by
  unfold cutoffMoment
  refine (continuous_heatCutoff.mul (Real.continuous_exp.comp
    (continuous_id.div_const 2))).integral_pos_of_hasCompactSupport_nonneg_nonzero
    ((hasCompactSupport_heatCutoff h0.le h01).mul_right) (fun x => ?_) (x := 0) ?_
  · exact mul_nonneg (heatCutoff_nonneg x) (Real.exp_pos _).le
  · rw [heatCutoff_eq_one h0.le h01 (by simp [h0.le]), one_mul]
    exact (Real.exp_pos _).ne'

theorem contDiff_heatSource (a : ℝ) (P : ℝ[X]) :
    ContDiff ℝ (⊤ : ℕ∞) (heatSource a P B₀ B₁) :=
  ((contDiff_gaussPolyFun _ _).sub contDiff_const).mul (contDiff_heatCutoff B₀ B₁)

theorem hasCompactSupport_heatSource (h0 : 0 ≤ B₀) (h01 : B₀ < B₁) (a : ℝ) (P : ℝ[X]) :
    HasCompactSupport (heatSource a P B₀ B₁) :=
  (hasCompactSupport_heatCutoff h0 h01).mul_left

theorem tsupport_heatSource_subset (h0 : 0 ≤ B₀) (h01 : B₀ < B₁) (a : ℝ) (P : ℝ[X]) :
    tsupport (heatSource a P B₀ B₁) ⊆ Icc (-B₁) B₁ :=
  (tsupport_mul_subset_right (f := fun x => heatTest a P x - heatPoleCorrection a P B₀ B₁)
    (g := heatCutoff B₀ B₁)).trans (tsupport_heatCutoff_subset h0 h01)

theorem heatSource_neg (a : ℝ) (P : ℝ[X]) (x : ℝ) :
    heatSource a P B₀ B₁ (-x) = heatSource a P B₀ B₁ x := by
  simp only [heatSource, heatTest_neg, heatCutoff_neg]

/-! ## The pole moments -/

theorem cexp_I_mul_neg_half_I (x : ℝ) :
    Complex.exp (I * (-I / 2) * x) = ((Real.exp (x / 2) : ℝ) : ℂ) := by
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring_nf
  rw [I_sq]
  ring

/-- **The pole moment of the heat test.**  `∫ g e^{x/2} = e^{a/8} P(−1/4)`, which vanishes on the
pole hyperplane. -/
theorem integral_heatTest_mul_exp_half {a : ℝ} (ha : 0 < a) (P : ℝ[X])
    (hP : P.eval (-1 / 4) = 0) : ∫ x, heatTest a P x * Real.exp (x / 2) = 0 := by
  have h := heatStripTransform_heatPhysical ha P (-I / 2)
  have hsq : (-I / 2) ^ 2 = (((-1 / 4 : ℝ)) : ℂ) := by
    push_cast; ring_nf; rw [I_sq]; ring
  rw [hsq, eval_map_ofReal, hP, Complex.ofReal_zero, mul_zero] at h
  unfold heatStripTransform at h
  simp_rw [cexp_I_mul_neg_half_I, ← Complex.ofReal_mul] at h
  rw [integral_complex_ofReal] at h
  exact_mod_cast h

theorem heatPoleCorrection_mul_cutoffMoment (h0 : 0 < B₀) (h01 : B₀ < B₁) (a : ℝ) (P : ℝ[X]) :
    heatPoleCorrection a P B₀ B₁ * cutoffMoment B₀ B₁ =
      ∫ x, heatTest a P x * heatCutoff B₀ B₁ x * Real.exp (x / 2) := by
  rw [heatPoleCorrection, div_mul_cancel₀ _ (cutoffMoment_pos h0 h01).ne']

theorem integrable_heatTest_mul_cutoff_mul_exp (h0 : 0 < B₀) (h01 : B₀ < B₁) (a : ℝ)
    (P : ℝ[X]) :
    Integrable (fun x => heatTest a P x * heatCutoff B₀ B₁ x * Real.exp (x / 2)) := by
  refine ((continuous_heatTest a P).mul continuous_heatCutoff |>.mul
    (Real.continuous_exp.comp (continuous_id.div_const 2))).integrable_of_hasCompactSupport ?_
  exact ((hasCompactSupport_heatCutoff h0.le h01).mul_left).mul_right

theorem integrable_cutoff_mul_exp (h0 : 0 < B₀) (h01 : B₀ < B₁) :
    Integrable (fun x => heatCutoff B₀ B₁ x * Real.exp (x / 2)) :=
  (continuous_heatCutoff.mul (Real.continuous_exp.comp
    (continuous_id.div_const 2))).integrable_of_hasCompactSupport
    ((hasCompactSupport_heatCutoff h0.le h01).mul_right)

/-- **The corrected truncation is pole-vanishing.**  `∫ e^{x/2} u = 0`. -/
theorem integral_exp_half_mul_heatSource (h0 : 0 < B₀) (h01 : B₀ < B₁) (a : ℝ) (P : ℝ[X]) :
    ∫ x, Real.exp (x / 2) * heatSource a P B₀ B₁ x = 0 := by
  have e : (fun x => Real.exp (x / 2) * heatSource a P B₀ B₁ x) = fun x =>
      heatTest a P x * heatCutoff B₀ B₁ x * Real.exp (x / 2) -
        heatPoleCorrection a P B₀ B₁ * (heatCutoff B₀ B₁ x * Real.exp (x / 2)) := by
    funext x; simp only [heatSource]; ring
  rw [e, integral_sub (integrable_heatTest_mul_cutoff_mul_exp h0 h01 a P)
    ((integrable_cutoff_mul_exp h0 h01).const_mul _), integral_const_mul,
    ← heatPoleCorrection_mul_cutoffMoment h0 h01, cutoffMoment, sub_self]

/-- **The pole correction is controlled by the tail.**
`|κ| ∫ χ e^{x/2} ≤ ∫_{|x| ≥ B₀} |g| e^{|x|/2}`. -/
theorem abs_heatPoleCorrection_mul_le (h0 : 0 < B₀) (h01 : B₀ < B₁) {a : ℝ} (ha : 0 < a)
    (ha1 : a < 1) (P : ℝ[X]) (hP : P.eval (-1 / 4) = 0) :
    |heatPoleCorrection a P B₀ B₁| * cutoffMoment B₀ B₁ ≤
      stripMassOn (heatTest a P) (heatTailSet B₀) := by
  have hc := cutoffMoment_pos h0 h01
  rw [← abs_of_pos hc, ← abs_mul, heatPoleCorrection_mul_cutoffMoment h0 h01]
  have hg := integrable_mul_exp_half_of_abs (continuous_heatTest a P)
    (integrable_abs_heatTest_mul_exp ha ha1 P)
  have hgχ := integrable_heatTest_mul_cutoff_mul_exp h0 h01 a P
  have hsplit : ∫ x, heatTest a P x * heatCutoff B₀ B₁ x * Real.exp (x / 2) =
      -∫ x, heatTest a P x * (1 - heatCutoff B₀ B₁ x) * Real.exp (x / 2) := by
    have e : (fun x => heatTest a P x * (1 - heatCutoff B₀ B₁ x) * Real.exp (x / 2)) =
        fun x => heatTest a P x * Real.exp (x / 2) -
          heatTest a P x * heatCutoff B₀ B₁ x * Real.exp (x / 2) := by
      funext x; ring
    rw [e, integral_sub hg hgχ, integral_heatTest_mul_exp_half ha P hP]
    ring
  rw [hsplit, abs_neg, stripMassOn, ← integral_indicator (measurableSet_heatTailSet B₀)]
  have hind : Integrable ((heatTailSet B₀).indicator
      fun x => |heatTest a P x| * Real.exp (|x| / 2)) :=
    (integrable_abs_heatTest_mul_exp ha ha1 P).indicator (measurableSet_heatTailSet B₀)
  refine (abs_integral_le_integral_abs).trans (integral_mono (hg.sub hgχ |>.congr
    (Filter.Eventually.of_forall fun x => by simp only [Pi.sub_apply]; ring)).abs hind
    fun x => ?_)
  simp only
  by_cases hx : x ∈ heatTailSet B₀
  · rw [indicator_of_mem hx, abs_mul, abs_mul, abs_of_pos (Real.exp_pos (x / 2))]
    have h1 : |1 - heatCutoff B₀ B₁ x| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith [heatCutoff_nonneg (B₀ := B₀) (B₁ := B₁) x,
        heatCutoff_le_one (B₀ := B₀) (B₁ := B₁) x]
    have h2 : Real.exp (x / 2) ≤ Real.exp (|x| / 2) :=
      Real.exp_le_exp.2 (by linarith [le_abs_self x])
    calc |heatTest a P x| * |1 - heatCutoff B₀ B₁ x| * Real.exp (x / 2)
        ≤ |heatTest a P x| * 1 * Real.exp (|x| / 2) := by gcongr
      _ = _ := by ring
  · rw [indicator_of_notMem hx]
    have hx' : |x| ≤ B₀ := le_of_lt (lt_of_not_ge hx)
    rw [heatCutoff_eq_one h0.le h01 hx']
    simp

/-! ## The aperture norm of the corrected truncation -/

theorem heatTailSet_compl (L : ℝ) : (heatTailSet L)ᶜ = Ioo (-L) L := by
  ext x
  simp [heatTailSet, abs_lt]

theorem integrable_heatTest_sq {a : ℝ} (ha : 0 < a) (P : ℝ[X]) :
    Integrable (fun x => heatTest a P x ^ 2) :=
  integrable_gaussPolyFun_sq _ (by positivity)

/-- **The corrected truncation keeps the mass of `g` inside `|x| < B₀`.**
`∫ u² ≥ (∫ g² − ∫_{|x| ≥ B₀} g²)/2 − 2B₀κ²`. -/
theorem integral_heatSource_sq_ge (h0 : 0 < B₀) (h01 : B₀ < B₁) {a : ℝ} (ha : 0 < a)
    (P : ℝ[X]) :
    ((∫ x, heatTest a P x ^ 2) - ∫ x in heatTailSet B₀, heatTest a P x ^ 2) / 2 -
        2 * B₀ * heatPoleCorrection a P B₀ B₁ ^ 2 ≤
      ∫ x, heatSource a P B₀ B₁ x ^ 2 := by
  set κ := heatPoleCorrection a P B₀ B₁
  have hS := measurableSet_heatTailSet B₀
  have hV := integrable_heatTest_sq ha P
  have hsplit := integral_add_compl hS hV
  have hu : Integrable (fun x => heatSource a P B₀ B₁ x ^ 2) := by
    have hc : Continuous fun x => heatSource a P B₀ B₁ x ^ 2 :=
      (contDiff_heatSource (B₀ := B₀) (B₁ := B₁) a P).continuous.pow 2
    exact hc.integrable_of_hasCompactSupport
      ((hasCompactSupport_heatSource h0.le h01 a P).comp_left (g := fun y : ℝ => y ^ 2)
        (by norm_num))
  have h1 : ∫ x in (heatTailSet B₀)ᶜ, heatSource a P B₀ B₁ x ^ 2 ≤ ∫ x, heatSource a P B₀ B₁ x ^ 2 :=
    setIntegral_le_integral hu (Filter.Eventually.of_forall fun x => sq_nonneg _)
  have hconst : IntegrableOn (fun _ => κ ^ 2) (heatTailSet B₀)ᶜ := by
    rw [heatTailSet_compl]
    exact integrableOn_const measure_Ioo_lt_top.ne
  have hfin : IntegrableOn (fun x => heatTest a P x ^ 2 / 2 - κ ^ 2) (heatTailSet B₀)ᶜ :=
    (hV.integrableOn.div_const 2).sub hconst
  have h2 : ∫ x in (heatTailSet B₀)ᶜ, (heatTest a P x ^ 2 / 2 - κ ^ 2) ≤
      ∫ x in (heatTailSet B₀)ᶜ, heatSource a P B₀ B₁ x ^ 2 := by
    refine setIntegral_mono_on hfin hu.integrableOn hS.compl fun x hx => ?_
    have hx' : |x| ≤ B₀ := le_of_lt (lt_of_not_ge hx)
    simp only [heatSource, heatCutoff_eq_one h0.le h01 hx', mul_one]
    nlinarith [sq_nonneg (heatTest a P x - 2 * κ)]
  have h3 : ∫ x in (heatTailSet B₀)ᶜ, (heatTest a P x ^ 2 / 2 - κ ^ 2) =
      (∫ x in (heatTailSet B₀)ᶜ, heatTest a P x ^ 2) / 2 - 2 * B₀ * κ ^ 2 := by
    rw [integral_sub (hV.integrableOn.div_const 2) hconst, integral_div, setIntegral_const,
      heatTailSet_compl, Real.volume_real_Ioo, smul_eq_mul]
    have : B₀ - -B₀ = 2 * B₀ := by ring
    rw [this, max_eq_left (by linarith)]
  linarith

/-! ## The comparison -/

theorem norm_ofReal_mul_exp (f : ℝ → ℝ) (x : ℝ) :
    ‖((f x : ℝ) : ℂ)‖ * Real.exp (|x| / 2) = |f x| * Real.exp (|x| / 2) := by
  rw [Complex.norm_real, Real.norm_eq_abs]

theorem integrable_abs_of_compact {f : ℝ → ℝ} (hf : Continuous f) (hc : HasCompactSupport f) :
    Integrable (fun x => |f x| * Real.exp (|x| / 2)) :=
  ((continuous_abs.comp hf).mul (Real.continuous_exp.comp
    (continuous_abs.div_const 2))).integrable_of_hasCompactSupport (hc.abs.mul_right)

/-- **Positivity transfer from the pole-vanishing ground energy.** -/
theorem le_re_heatHankel_of_polarGroundEnergy (A : SuzukiPositiveAperture) (h0 : 0 < B₀)
    (h01 : B₀ < B₁) (h1A : B₁ < A.1) {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (P : ℝ[X])
    (hμ : 0 ≤ ccmRestrictedWeilPolarGroundEnergy A) {C : ℝ}
    (hC : ∀ x, |deriv (heatCutoff B₀ B₁) x| ≤ C) :
    ccmRestrictedWeilPolarGroundEnergy A *
        (((∫ x, heatTest a P x ^ 2) - ∫ x in heatTailSet B₀, heatTest a P x ^ 2) / 2 -
          2 * B₀ * heatPoleCorrection a P B₀ B₁ ^ 2) ≤
      (heatHankel a (P.map (algebraMap ℝ ℂ)) (P.map (algebraMap ℝ ℂ))).re +
        (2 * (∫ x, |heatTestDeriv a P x| * Real.exp (|x| / 2)) *
            (stripMassOn (heatTestDeriv a P) (heatTailSet B₀) +
              C * stripMassOn (heatTest a P) (heatTailSet B₀) +
              |heatPoleCorrection a P B₀ B₁| *
                ∫ x, |deriv (heatCutoff B₀ B₁) x| * Real.exp (|x| / 2)) +
          (stripMassOn (heatTestDeriv a P) (heatTailSet B₀) +
              C * stripMassOn (heatTest a P) (heatTailSet B₀) +
              |heatPoleCorrection a P B₀ B₁| *
                ∫ x, |deriv (heatCutoff B₀ B₁) x| * Real.exp (|x| / 2)) ^ 2) *
          ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2 := by
  set κ := heatPoleCorrection a P B₀ B₁ with hκ
  set g := heatTest a P with hg_def
  set g' := heatTestDeriv a P with hg'_def
  set χ := heatCutoff B₀ B₁ with hχ_def
  set χ' := deriv (heatCutoff B₀ B₁) with hχ'_def
  set u := heatSource a P B₀ B₁ with hu_def
  set M := ∫ x, |g' x| * Real.exp (|x| / 2) with hM_def
  set ρ := stripMassOn g' (heatTailSet B₀) + C * stripMassOn g (heatTailSet B₀) +
    |κ| * ∫ x, |χ' x| * Real.exp (|x| / 2) with hρ_def
  have hsupp : tsupport u ⊆ Ioo (-A.1) A.1 :=
    (tsupport_heatSource_subset h0.le h01 a P).trans (Icc_subset_Ioo (by linarith) h1A)
  set src := realEvenSource A u (contDiff_heatSource a P) (hasCompactSupport_heatSource h0.le h01 a P)
    hsupp
  -- the Weil floor
  have hpolar : IsPolarConstrained A src.toCCMFormVector :=
    isPolarConstrained_realEven (heatSource_neg a P) (integral_exp_half_mul_heatSource h0 h01 a P)
  have hfloor := ccmRestrictedWeilPolarGroundEnergy_mul_le A src.toCCMFormVector hpolar
  rw [sq_norm_ccmArchimedeanFormToAperture_realSource,
    ccmRestrictedWeilSourceQuadratic_realEven (heatSource_neg a P)] at hfloor
  -- derivatives and integrability
  have hgd : ∀ x, HasDerivAt g (g' x) x := hasDerivAt_heatTest a P
  have hχd : ∀ x, HasDerivAt χ (χ' x) x := fun x => hasDerivAt_heatCutoff x
  have hud : ∀ x, HasDerivAt u (g' x * χ x + (g x - κ) * χ' x) x := fun x =>
    ((hgd x).sub_const κ).mul (hχd x)
  have hgc : Continuous g := continuous_heatTest a P
  have hg'c : Continuous g' := continuous_heatTestDeriv a P
  have hχc : Continuous χ := continuous_heatCutoff
  have hχ'c : Continuous χ' := continuous_deriv_heatCutoff
  have hχcpt : HasCompactSupport χ := hasCompactSupport_heatCutoff h0.le h01
  have hχ'cpt : HasCompactSupport χ' := hasCompactSupport_deriv_heatCutoff h0.le h01
  have huc : Continuous u := (contDiff_heatSource a P).continuous
  have hucpt : HasCompactSupport u := hasCompactSupport_heatSource h0.le h01 a P
  have hu'c : Continuous fun x => g' x * χ x + (g x - κ) * χ' x :=
    (hg'c.mul hχc).add ((hgc.sub continuous_const).mul hχ'c)
  have hu'cpt : HasCompactSupport fun x => g' x * χ x + (g x - κ) * χ' x :=
    (hχcpt.mul_left).add (hχ'cpt.mul_left)
  have hgi := integrable_abs_heatTest_mul_exp ha ha1 P
  have hg'i := integrable_abs_heatTestDeriv_mul_exp ha ha1 P
  have hui := integrable_abs_of_compact huc hucpt
  have hu'i := integrable_abs_of_compact hu'c hu'cpt
  have hχ'i := integrable_abs_of_compact hχ'c hχ'cpt
  have hcast : ∀ {f : ℝ → ℝ}, Integrable (fun x => |f x| * Real.exp (|x| / 2)) →
      Integrable (fun x => ‖((f x : ℝ) : ℂ)‖ * Real.exp (|x| / 2)) := fun h => by
    simpa only [norm_ofReal_mul_exp] using h
  -- the function h = g − u and its derivative
  set h : ℝ → ℝ := fun x => g x - u x with hh_def
  set h' : ℝ → ℝ := fun x => g' x - (g' x * χ x + (g x - κ) * χ' x) with hh'_def
  have hhd : ∀ x, HasDerivAt h (h' x) x := fun x => (hgd x).sub (hud x)
  have hhi : Integrable (fun x => |h x| * Real.exp (|x| / 2)) := by
    refine (hgi.add hui).mono' ((continuous_abs.comp (hgc.sub huc)).mul (Real.continuous_exp.comp
      (continuous_abs.div_const 2))).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    have := abs_sub (g x) (u x)
    have he := Real.exp_pos (|x| / 2)
    simp only [Pi.add_apply]
    nlinarith
  have hh'i : Integrable (fun x => |h' x| * Real.exp (|x| / 2)) := by
    refine (hg'i.add hu'i).mono' ((continuous_abs.comp (hg'c.sub hu'c)).mul
      (Real.continuous_exp.comp (continuous_abs.div_const 2))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    have := abs_sub (g' x) (g' x * χ x + (g x - κ) * χ' x)
    have he := Real.exp_pos (|x| / 2)
    simp only [Pi.add_apply]
    nlinarith
  -- strip bounds
  have hstrip : ∀ q : XiZeroCopy, |(xiSpectralPoint q).im| ≤ 1 / 2 :=
    abs_im_xiSpectralPoint_le_half
  have hG : ∀ q : XiZeroCopy, ‖xiSpectralPoint q‖ *
      ‖heatStripTransform (fun x => ((g x : ℝ) : ℂ)) (xiSpectralPoint q)‖ ≤ M := fun q => by
    have := norm_mul_norm_heatStripTransform_le (f := fun x => ((g x : ℝ) : ℂ))
      (f' := fun x => ((g' x : ℝ) : ℂ)) (Complex.continuous_ofReal.comp hgc)
      (Complex.continuous_ofReal.comp hg'c) (fun x => (hgd x).ofReal_comp) (hcast hgi)
      (hcast hg'i) (hstrip q)
    simpa only [norm_ofReal_mul_exp] using this
  have hdiff : ∀ z : ℂ, |z.im| ≤ 1 / 2 →
      heatStripTransform (fun x => ((g x : ℝ) : ℂ)) z -
        heatStripTransform (fun x => ((u x : ℝ) : ℂ)) z =
      heatStripTransform (fun x => ((h x : ℝ) : ℂ)) z := fun z hz => by
    have i1 := integrable_mul_cexp_of_strip (f := fun x => ((g x : ℝ) : ℂ))
      (Complex.continuous_ofReal.comp hgc) (hcast hgi) hz
    have i2 := integrable_mul_cexp_of_strip (f := fun x => ((u x : ℝ) : ℂ))
      (Complex.continuous_ofReal.comp huc) (hcast hui) hz
    unfold heatStripTransform
    rw [← integral_sub i1 i2]
    congr 1
    funext x
    simp only [hh_def]
    push_cast
    ring
  have hpt : ∀ x, |h' x| * Real.exp (|x| / 2) ≤
      (heatTailSet B₀).indicator (fun x => |g' x| * Real.exp (|x| / 2) +
        C * (|g x| * Real.exp (|x| / 2))) x + |κ| * (|χ' x| * Real.exp (|x| / 2)) := fun x => by
    have he := Real.exp_pos (|x| / 2)
    by_cases hx : x ∈ heatTailSet B₀
    · rw [indicator_of_mem hx]
      have hχ0 := heatCutoff_nonneg (B₀ := B₀) (B₁ := B₁) x
      have hχ1 := heatCutoff_le_one (B₀ := B₀) (B₁ := B₁) x
      have hb : |h' x| ≤ |g' x| + C * |g x| + |κ| * |χ' x| := by
        have e : h' x = g' x * (1 - χ x) - g x * χ' x + κ * χ' x := by
          simp only [hh'_def]; ring
        rw [e]
        have h1 : |g' x * (1 - χ x)| ≤ |g' x| := by
          rw [abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - χ x)]
          nlinarith [abs_nonneg (g' x)]
        have h2 : |g x * χ' x| ≤ C * |g x| := by
          rw [abs_mul, mul_comm]; exact mul_le_mul_of_nonneg_right (hC x) (abs_nonneg _)
        have h3 : |κ * χ' x| = |κ| * |χ' x| := abs_mul _ _
        have t1 := abs_sub (g' x * (1 - χ x)) (g x * χ' x)
        have t2 := abs_add_le (g' x * (1 - χ x) - g x * χ' x) (κ * χ' x)
        linarith
      nlinarith [abs_nonneg (κ), abs_nonneg (χ' x)]
    · rw [indicator_of_notMem hx]
      have hx' : |x| < B₀ := lt_of_not_ge hx
      have e : h' x = 0 := by
        simp only [hh'_def, hχ_def, hχ'_def, heatCutoff_eq_one h0.le h01 hx'.le,
          deriv_heatCutoff_eq_zero h0.le h01 hx']
        ring
      rw [e, abs_zero, zero_mul]
      positivity
  have hρbound : ∫ x, |h' x| * Real.exp (|x| / 2) ≤ ρ := by
    have hind : Integrable ((heatTailSet B₀).indicator (fun x => |g' x| * Real.exp (|x| / 2) +
        C * (|g x| * Real.exp (|x| / 2)))) :=
      (hg'i.add (hgi.const_mul C)).indicator (measurableSet_heatTailSet B₀)
    calc ∫ x, |h' x| * Real.exp (|x| / 2)
        ≤ ∫ x, ((heatTailSet B₀).indicator (fun x => |g' x| * Real.exp (|x| / 2) +
            C * (|g x| * Real.exp (|x| / 2))) x + |κ| * (|χ' x| * Real.exp (|x| / 2))) :=
          integral_mono hh'i (hind.add (hχ'i.const_mul _)) hpt
      _ = ρ := by
          rw [integral_add hind (hχ'i.const_mul _), integral_indicator (measurableSet_heatTailSet B₀),
            integral_add hg'i.integrableOn (hgi.const_mul C).integrableOn, integral_const_mul,
            integral_const_mul, hρ_def, stripMassOn, stripMassOn]
  have hR : ∀ q : XiZeroCopy, ‖xiSpectralPoint q‖ *
      ‖heatStripTransform (fun x => ((g x : ℝ) : ℂ)) (xiSpectralPoint q) -
        heatStripTransform (fun x => ((u x : ℝ) : ℂ)) (xiSpectralPoint q)‖ ≤ ρ := fun q => by
    rw [hdiff _ (hstrip q)]
    have := norm_mul_norm_heatStripTransform_le (f := fun x => ((h x : ℝ) : ℂ))
      (f' := fun x => ((h' x : ℝ) : ℂ)) (Complex.continuous_ofReal.comp (hgc.sub huc))
      (Complex.continuous_ofReal.comp (hg'c.sub hu'c)) (fun x => (hhd x).ofReal_comp) (hcast hhi)
      (hcast hh'i) (hstrip q)
    simp only [norm_ofReal_mul_exp] at this
    exact this.trans hρbound
  have hcmp := re_tsum_sq_le_of_strip hG hR
  have hH : heatHankel a (P.map (algebraMap ℝ ℂ)) (P.map (algebraMap ℝ ℂ)) =
      ∑' q : XiZeroCopy, heatStripTransform (fun x => ((g x : ℝ) : ℂ)) (xiSpectralPoint q) ^ 2 :=
    heatHankel_map_eq_tsum_sq ha P
  rw [← hH] at hcmp
  have hnorm := integral_heatSource_sq_ge h0 h01 ha P
  calc ccmRestrictedWeilPolarGroundEnergy A *
        (((∫ x, g x ^ 2) - ∫ x in heatTailSet B₀, g x ^ 2) / 2 - 2 * B₀ * κ ^ 2)
      ≤ ccmRestrictedWeilPolarGroundEnergy A * ∫ x, u x ^ 2 :=
        mul_le_mul_of_nonneg_left hnorm hμ
    _ ≤ _ := hfloor
    _ ≤ _ := hcmp

end

end RHTower
