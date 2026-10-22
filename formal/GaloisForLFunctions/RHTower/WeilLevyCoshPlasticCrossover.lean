import GaloisForLFunctions.RHTower.Suzuki.SuzukiExplicitScrewRegularKernel
import GaloisForLFunctions.RHTower.WeilLevyPoleGaussModeCancellation

/-!
# Lévy–cosh plastic-number crossover identity and signed short-support positivity

This module unifies the regular screw kernel of `SuzukiExplicitScrewRegularKernel`
(`screwRegularKernel t = e^{t/2} - e^{-5t/2}/(1 - e^{-2t})`, with sign threshold at the plastic
number `screwSignThreshold = log plasticRoot ≈ 0.2812`, `plasticRoot^3 = plasticRoot + 1`) and the
Lévy–pole decomposition of `WeilArchReLevyPoleForm` / `WeilLevyPoleGaussModeCancellation`
(`archLevyDensity`, `archLevyAntideriv`):

1. **Exact kernel unification (`screwRegularKernel_eq_two_mul_cosh_sub_archLevyDensity`)**:
   For all `t > 0`,
   `screwRegularKernel t = 2 cosh(t/2) - archLevyDensity t`.
   Consequently, `2 cosh(t/2) ≤ archLevyDensity t` on `(0, screwSignThreshold]` and
   `archLevyDensity t ≤ 2 cosh(t/2)` on `[screwSignThreshold, ∞)`, with equality at
   `t = screwSignThreshold`.

2. **The Lévy–cosh potential (`levyCoshPotential`) and its global minimum at `screwSignThreshold`**:
   `levyCoshPotential c = 8 sinh(c/2) + 2 archLevyAntideriv c` has exact derivative
   `2 * screwRegularKernel c` on `(0, ∞)` (`hasDerivAt_levyCoshPotential`), is antitone on
   `(0, screwSignThreshold]` and monotone on `[screwSignThreshold, ∞)`, and attains its global
   minimum on `(0, ∞)` at `screwSignThreshold = log plasticRoot`
   (`levyCoshPotential_screwSignThreshold_le`).

3. **Algebraic-rational bounds at the plastic threshold (`twenty_six_fifths_lt_levyCoshPotential_screwSignThreshold`)**:
   Using `u = exp(screwSignThreshold / 2) = √plasticRoot` (`u^6 = u^2 + 1`), we prove
   `11509 / 10000 < exp(screwSignThreshold / 2) < 1151 / 1000` and
   `26 / 5 < levyCoshPotential screwSignThreshold` (`5.2 < Φ(t_*)`), so
   `-(2 / 5) < EF.gammaBracket 0 + levyCoshPotential screwSignThreshold`.

4. **Piecewise Lévy–cosh crossover kernel (`levyCoshKernel`) and master crossover bounds
   (`levyCosh_crossover_add_jump_le_weilArchRe`, `plastic_floor_add_jump_le_weilArchRe`,
   `weilArchRe_nonneg_of_signed_support_Icc_le`)**:
   Replacing the singular density `archLevyDensity x` on `(0, c]` by the smooth pole kernel
   `2 cosh(x/2)` cancels the `2 cosh((u - v)/2)` pole term identically for `|u - v| ≤ c`, while
   leaving the nonnegative jump excess `(-screwRegularKernel x) ‖f - f(· + x)‖₂²` on `(0, c)` and
   the `screwRegularKernel |u - v|` pair kernel on `|u - v| > c`.
   * At `c = screwSignThreshold`, both kernels are simultaneously nonnegative, yielding the
     universal nonnegative-cone lower bound
     `(EF.gammaBracket 0 + levyCoshPotential screwSignThreshold) ∫ f² + ∫_{x ∈ (δ, t_*)} (-screwRegularKernel x) ‖f - f(· + x)‖₂² ≤ W_∞(f ⋆ f̃)`.
   * For any **signed** `f ∈ C²_c(ℝ)` supported in an interval `[a, a + L]` of length
     `0 < L ≤ screwSignThreshold`, the `|u - v| > L` pair term vanishes identically, yielding
     `(EF.gammaBracket 0 + levyCoshPotential L) ∫ f² ≤ W_∞(f ⋆ f̃)` and unconditional signed
     positivity whenever `-EF.gammaBracket 0 ≤ levyCoshPotential L` (in particular for all
     `0 < L ≤ 1 / 130`).
-/

open Complex MeasureTheory Set Filter Topology
open scoped FourierTransform ComplexConjugate
open Zeta23
open GaloisForLFunctions.RHTower
open GaloisForLFunctions.HTGeometry.QuantileTransport

namespace RHTower.WeilLevyCoshCrossover

noncomputable section

open WeilLevyPole RHTower.NonnegativeCone RHTower.WeilLevyPoleGauss

/-! ## Section 1: Exact Unification of `screwRegularKernel` and `archLevyDensity` -/

/-- On `(0, ∞)`, Suzuki's regular screw kernel `screwRegularKernel t` is identically
`2 * Real.cosh (t / 2) - archLevyDensity t`. -/
theorem screwRegularKernel_eq_two_mul_cosh_sub_archLevyDensity {t : ℝ} (ht : 0 < t) :
    screwRegularKernel t = 2 * Real.cosh (t / 2) - archLevyDensity t := by
  rw [screwRegularKernel_eq_tailForm ht, Real.cosh_eq]
  unfold archLevyDensity
  rw [show -t / 2 = -(t / 2) by ring, show -2 * t = -(2 * t) by ring]
  ring

/-- Dual form: `archLevyDensity t - 2 * Real.cosh (t / 2) = -screwRegularKernel t` for `t > 0`. -/
theorem archLevyDensity_sub_two_mul_cosh_eq_neg_screwRegularKernel {t : ℝ} (ht : 0 < t) :
    archLevyDensity t - 2 * Real.cosh (t / 2) = -screwRegularKernel t := by
  rw [screwRegularKernel_eq_two_mul_cosh_sub_archLevyDensity ht]; ring

/-- `exp screwSignThreshold = plasticRoot`. -/
theorem exp_screwSignThreshold : Real.exp screwSignThreshold = plasticRoot :=
  Real.exp_log plasticRoot_pos

/-- At the plastic-number sign threshold `screwSignThreshold = log plasticRoot`,
`screwRegularKernel` vanishes identically. -/
theorem screwRegularKernel_screwSignThreshold : screwRegularKernel screwSignThreshold = 0 := by
  have ht := screwSignThreshold_pos
  have hfac := screwKernelSignFactor_pos ht
  have hmul := screwRegularKernel_mul_eq_cubic ht
  rw [exp_screwSignThreshold, plasticRoot_cubic] at hmul
  exact (mul_eq_zero.mp hmul).resolve_right hfac.ne'

/-- At `screwSignThreshold`, `archLevyDensity` and `2 cosh(·/2)` cross:
`archLevyDensity screwSignThreshold = 2 * Real.cosh (screwSignThreshold / 2)`. -/
theorem archLevyDensity_screwSignThreshold :
    archLevyDensity screwSignThreshold = 2 * Real.cosh (screwSignThreshold / 2) := by
  have h := screwRegularKernel_eq_two_mul_cosh_sub_archLevyDensity screwSignThreshold_pos
  rw [screwRegularKernel_screwSignThreshold] at h
  linarith

/-- On `(0, screwSignThreshold]`, `screwRegularKernel t ≤ 0`. -/
theorem screwRegularKernel_nonpos_of_le_threshold {t : ℝ} (ht : 0 < t)
    (hle : t ≤ screwSignThreshold) :
    screwRegularKernel t ≤ 0 := by
  rcases eq_or_lt_of_le hle with rfl | hlt
  · exact screwRegularKernel_screwSignThreshold.le
  · exact (screwRegularKernel_neg_of_lt_threshold ht hlt).le

/-- On `[screwSignThreshold, ∞)`, `0 ≤ screwRegularKernel t`. -/
theorem screwRegularKernel_nonneg_of_threshold_le {t : ℝ} (hle : screwSignThreshold ≤ t) :
    0 ≤ screwRegularKernel t := by
  have ht : 0 < t := lt_of_lt_of_le screwSignThreshold_pos hle
  rcases eq_or_lt_of_le hle with hEq | hlt
  · rw [← hEq, screwRegularKernel_screwSignThreshold]
  · exact ((screwRegularKernel_pos_iff ht).mpr hlt).le

/-- On `(0, screwSignThreshold]`, `2 * Real.cosh (t / 2) ≤ archLevyDensity t`. -/
theorem two_mul_cosh_le_archLevyDensity_of_le_threshold {t : ℝ} (ht : 0 < t)
    (hle : t ≤ screwSignThreshold) :
    2 * Real.cosh (t / 2) ≤ archLevyDensity t := by
  have h := screwRegularKernel_nonpos_of_le_threshold ht hle
  rw [screwRegularKernel_eq_two_mul_cosh_sub_archLevyDensity ht] at h
  linarith

/-- On `[screwSignThreshold, ∞)`, `archLevyDensity t ≤ 2 * Real.cosh (t / 2)`. -/
theorem archLevyDensity_le_two_mul_cosh_of_threshold_le {t : ℝ}
    (hle : screwSignThreshold ≤ t) :
    archLevyDensity t ≤ 2 * Real.cosh (t / 2) := by
  have ht : 0 < t := lt_of_lt_of_le screwSignThreshold_pos hle
  have h := screwRegularKernel_nonneg_of_threshold_le hle
  rw [screwRegularKernel_eq_two_mul_cosh_sub_archLevyDensity ht] at h
  linarith

/-- `screwRegularKernel` is continuous on `(0, ∞)`. -/
theorem continuousOn_screwRegularKernel : ContinuousOn screwRegularKernel (Ioi 0) := by
  refine ContinuousOn.congr (f := fun t => 2 * Real.cosh (t / 2) - archLevyDensity t) ?_
    fun t ht => screwRegularKernel_eq_two_mul_cosh_sub_archLevyDensity ht
  exact (by fun_prop : ContinuousOn (fun t : ℝ => 2 * Real.cosh (t / 2)) (Ioi 0)).sub
    continuousOn_archLevyDensity

/-! ## Section 2: The Lévy–Cosh Potential and Its Unique Minimum at `screwSignThreshold` -/

/-- The **Lévy–cosh potential** on `(0, ∞)`:
`levyCoshPotential c = 8 sinh(c/2) + 2 archLevyAntideriv c`.
It measures the total `L²` mass extracted when `archLevyDensity` is replaced by `2 cosh(x/2)` on
`(0, c]` and integrated directly on `(c, ∞)`. -/
def levyCoshPotential (c : ℝ) : ℝ :=
  8 * Real.sinh (c / 2) + 2 * archLevyAntideriv c

/-- On `(0, ∞)`, `levyCoshPotential c` strictly exceeds `2 * archLevyAntideriv c`. -/
theorem two_mul_archLevyAntideriv_lt_levyCoshPotential {c : ℝ} (hc : 0 < c) :
    2 * archLevyAntideriv c < levyCoshPotential c := by
  unfold levyCoshPotential
  have hsinh : 0 < Real.sinh (c / 2) := Real.sinh_pos_iff.mpr (by linarith)
  linarith

/-- `levyCoshPotential c > 0` for all `c > 0`. -/
theorem levyCoshPotential_pos {c : ℝ} (hc : 0 < c) : 0 < levyCoshPotential c :=
  lt_trans (mul_pos zero_lt_two (archLevyAntideriv_pos hc))
    (two_mul_archLevyAntideriv_lt_levyCoshPotential hc)

/-- Derivative of `8 * Real.sinh (x / 2)`. -/
theorem hasDerivAt_eight_mul_sinh_half (c : ℝ) :
    HasDerivAt (fun x : ℝ => 8 * Real.sinh (x / 2)) (4 * Real.cosh (c / 2)) c := by
  have h := ((hasDerivAt_id c).div_const (2 : ℝ)).sinh.const_mul (8 : ℝ)
  exact h.congr_deriv (by dsimp only [id_eq]; ring)

/-- **Exact derivative of `levyCoshPotential`**:
for every `c > 0`, `levyCoshPotential'(c) = 2 * screwRegularKernel c`. -/
theorem hasDerivAt_levyCoshPotential {c : ℝ} (hc : 0 < c) :
    HasDerivAt levyCoshPotential (2 * screwRegularKernel c) c := by
  have h1 := hasDerivAt_eight_mul_sinh_half c
  have h2 := (hasDerivAt_archLevyAntideriv hc).const_mul (2 : ℝ)
  have hsum := h1.add h2
  refine hsum.congr_deriv ?_
  rw [screwRegularKernel_eq_two_mul_cosh_sub_archLevyDensity hc]
  ring

/-- Fundamental Theorem of Calculus for `levyCoshPotential`:
for `a > 0` and `b > 0`, `∫ x in a..b, 2 * screwRegularKernel x = levyCoshPotential b - levyCoshPotential a`. -/
theorem integral_two_mul_screwRegularKernel {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ x in a..b, 2 * screwRegularKernel x = levyCoshPotential b - levyCoshPotential a := by
  have hsub : uIcc a b ⊆ Ioi 0 := fun x hx =>
    lt_of_lt_of_le (lt_min ha hb) hx.1
  have hcont : ContinuousOn (fun x => 2 * screwRegularKernel x) (uIcc a b) :=
    (continuousOn_const.mul continuousOn_screwRegularKernel).mono hsub
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => hasDerivAt_levyCoshPotential (hsub hx))
    hcont.intervalIntegrable

/-- `levyCoshPotential` is antitone on `(0, screwSignThreshold]`. -/
theorem antitoneOn_levyCoshPotential_Ioc :
    AntitoneOn levyCoshPotential (Ioc 0 screwSignThreshold) := by
  intro a ha b hb hab
  have hFTC := integral_two_mul_screwRegularKernel ha.1 hb.1
  have hnonpos : ∫ x in a..b, 2 * screwRegularKernel x ≤ 0 := by
    rw [intervalIntegral.integral_of_le hab]
    exact setIntegral_nonpos measurableSet_Ioc fun x hx =>
      mul_nonpos_of_nonneg_of_nonpos zero_le_two
        (screwRegularKernel_nonpos_of_le_threshold (lt_trans ha.1 hx.1) (hx.2.trans hb.2))
  linarith

/-- `levyCoshPotential` is monotone on `[screwSignThreshold, ∞)`. -/
theorem monotoneOn_levyCoshPotential_Ici :
    MonotoneOn levyCoshPotential (Ici screwSignThreshold) := by
  intro a ha b hb hab
  have ha0 : 0 < a := lt_of_lt_of_le screwSignThreshold_pos ha
  have hb0 : 0 < b := lt_of_lt_of_le screwSignThreshold_pos hb
  have hFTC := integral_two_mul_screwRegularKernel ha0 hb0
  have hnonneg : 0 ≤ ∫ x in a..b, 2 * screwRegularKernel x := by
    rw [intervalIntegral.integral_of_le hab]
    exact setIntegral_nonneg measurableSet_Ioc fun x hx =>
      mul_nonneg zero_le_two
        (screwRegularKernel_nonneg_of_threshold_le (ha.trans hx.1.le))
  linarith

/-- **Global minimum of `levyCoshPotential` on `(0, ∞)`**:
for every `c > 0`, `levyCoshPotential screwSignThreshold ≤ levyCoshPotential c`. -/
theorem levyCoshPotential_screwSignThreshold_le {c : ℝ} (hc : 0 < c) :
    levyCoshPotential screwSignThreshold ≤ levyCoshPotential c := by
  rcases le_total c screwSignThreshold with hle | hge
  · exact antitoneOn_levyCoshPotential_Ioc ⟨hc, hle⟩ ⟨screwSignThreshold_pos, le_rfl⟩ hle
  · exact monotoneOn_levyCoshPotential_Ici (mem_Ici.mpr le_rfl) (mem_Ici.mpr hge) hge

/-- `archLevyAntideriv y → 0` as `y → ∞`. -/
theorem tendsto_archLevyAntideriv_atTop : Tendsto archLevyAntideriv atTop (𝓝 0) := by
  refine squeeze_zero'
    ((eventually_gt_atTop (0 : ℝ)).mp (Eventually.of_forall fun y hy => (archLevyAntideriv_pos hy).le))
    ((eventually_gt_atTop (0 : ℝ)).mp (Eventually.of_forall fun y hy => archLevyAntideriv_le hy)) ?_
  have hexp0 : Tendsto (fun y : ℝ => Real.exp (-y / 2)) atTop (𝓝 0) := by
    rw [show (fun y : ℝ => Real.exp (-y / 2)) = fun y : ℝ => Real.exp (-(y / 2)) by
      funext y; ring_nf]
    exact Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.atTop_div_const two_pos)
  have h0 : (2 * (0 : ℝ)) / (1 - 0) = 0 := by ring
  rw [← h0]
  exact (hexp0.const_mul 2).div (tendsto_const_nhds.sub hexp0) (by norm_num)

/-- **Exact improper integral of `archLevyDensity` on `(c, ∞)`**:
for every `c > 0`, `∫ x in Ioi c, archLevyDensity x = archLevyAntideriv c`. -/
theorem integral_archLevyDensity_Ioi {c : ℝ} (hc : 0 < c) :
    ∫ x in Ioi c, archLevyDensity x = archLevyAntideriv c := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg
    (g := fun x => -archLevyAntideriv x) (g' := archLevyDensity) (a := c) (l := 0)
    ((hasDerivAt_archLevyAntideriv hc).fun_neg.continuousAt.continuousWithinAt)
    (fun x hx => ((hasDerivAt_archLevyAntideriv (lt_trans hc hx)).fun_neg).congr_deriv (neg_neg _))
    (fun x hx => (archLevyDensity_pos (lt_trans hc hx)).le)
    (by simpa using tendsto_archLevyAntideriv_atTop.neg)
  linarith

/-- Upper bound `archLevyDensity x ≤ (1 - exp(-2c))⁻¹ * exp(-(1/2) * x)` on `[c, ∞)`. -/
theorem archLevyDensity_le_of_le {c x : ℝ} (hc : 0 < c) (hcx : c ≤ x) :
    archLevyDensity x ≤ (1 - Real.exp (-2 * c))⁻¹ * Real.exp (-(1 / 2) * x) := by
  unfold archLevyDensity
  have h1 : Real.exp (-2 * x) ≤ Real.exp (-2 * c) :=
    Real.exp_le_exp.mpr (by linarith)
  have h2 : 0 < 1 - Real.exp (-2 * c) := by
    have : Real.exp (-2 * c) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  rw [div_eq_inv_mul, show -x / 2 = -(1 / 2) * x by ring]
  exact mul_le_mul_of_nonneg_right (inv_anti₀ h2 (by linarith)) (Real.exp_pos _).le

/-- `archLevyDensity` is integrable on `Ioi c` for every `c > 0`. -/
theorem integrableOn_archLevyDensity_Ioi {c : ℝ} (hc : 0 < c) :
    IntegrableOn archLevyDensity (Ioi c) := by
  refine ((integrableOn_exp_mul_Ioi (by norm_num : -(1 / 2 : ℝ) < 0) c).const_mul
    (1 - Real.exp (-2 * c))⁻¹).mono'
    ((continuousOn_archLevyDensity.mono fun x hx => lt_trans hc hx).aestronglyMeasurable
      measurableSet_Ioi)
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_))
  rw [Real.norm_eq_abs, abs_of_pos (archLevyDensity_pos (lt_trans hc hx))]
  exact archLevyDensity_le_of_le hc (mem_Ioi.mp hx).le

/-! ## Section 3: Algebraic-Rational Sandwich for `plasticRoot` and `levyCoshPotential screwSignThreshold > 26 / 5` -/

/-- Rational lower bound `331 / 250 < plasticRoot` (`1.324 < ρ`). -/
theorem plasticRoot_gt : (331 : ℝ) / 250 < plasticRoot := by
  by_contra hle
  rw [not_lt] at hle
  have hpos : 0 < ((331 : ℝ) / 250) ^ 3 - (331 / 250) - 1 ↔ plasticRoot < 331 / 250 :=
    cubic_pos_iff_plasticRoot_lt (by norm_num)
  rcases eq_or_lt_of_le hle with hEq | hlt
  · have hc := plasticRoot_cubic
    rw [hEq] at hc
    norm_num at hc
  · have hc := hpos.mpr hlt
    norm_num at hc

/-- Rational upper bound `plasticRoot < 53 / 40` (`ρ < 1.325`). -/
theorem plasticRoot_lt : plasticRoot < (53 : ℝ) / 40 :=
  (cubic_pos_iff_plasticRoot_lt (by norm_num)).mp (by norm_num)

/-- `(exp(screwSignThreshold / 2))^2 = plasticRoot`. -/
theorem exp_half_screwSignThreshold_sq :
    Real.exp (screwSignThreshold / 2) ^ 2 = plasticRoot := by
  rw [sq, ← Real.exp_add, add_halves, exp_screwSignThreshold]

/-- Rational lower bound `11509 / 10000 < exp(screwSignThreshold / 2)`. -/
theorem exp_half_screwSignThreshold_gt :
    (11509 : ℝ) / 10000 < Real.exp (screwSignThreshold / 2) := by
  have hsq : ((11509 : ℝ) / 10000) ^ 2 < Real.exp (screwSignThreshold / 2) ^ 2 := by
    rw [exp_half_screwSignThreshold_sq]
    have hρ : ((11509 : ℝ) / 10000) ^ 2 < plasticRoot := by
      by_contra hle
      rw [not_lt] at hle
      have hpos : 0 < (((11509 : ℝ) / 10000) ^ 2) ^ 3 - ((11509 : ℝ) / 10000) ^ 2 - 1 ↔
          plasticRoot < ((11509 : ℝ) / 10000) ^ 2 :=
        cubic_pos_iff_plasticRoot_lt (by norm_num)
      rcases eq_or_lt_of_le hle with hEq | hlt
      · have hc := plasticRoot_cubic
        rw [hEq] at hc
        norm_num at hc
      · have hc := hpos.mpr hlt
        norm_num at hc
    exact hρ
  nlinarith [Real.exp_pos (screwSignThreshold / 2)]

/-- Rational upper bound `exp(screwSignThreshold / 2) < 1151 / 1000`. -/
theorem exp_half_screwSignThreshold_lt :
    Real.exp (screwSignThreshold / 2) < (1151 : ℝ) / 1000 := by
  have hsq : Real.exp (screwSignThreshold / 2) ^ 2 < ((1151 : ℝ) / 1000) ^ 2 := by
    rw [exp_half_screwSignThreshold_sq]
    exact (cubic_pos_iff_plasticRoot_lt (by norm_num)).mp (by norm_num)
  nlinarith [Real.exp_pos (screwSignThreshold / 2)]

/-- Closed form for `levyCoshPotential c` in terms of `u = exp(c / 2) > 1`:
`levyCoshPotential c = 4 (u - 1 / u) + log((u + 1) / (u - 1)) + 2 arctan(1 / u)`. -/
theorem levyCoshPotential_eq_of_exp_half {c : ℝ} (hc : 0 < c) :
    let u := Real.exp (c / 2)
    levyCoshPotential c =
      4 * (u - 1 / u) + Real.log ((u + 1) / (u - 1)) + 2 * Real.arctan (1 / u) := by
  intro u
  have hu : 1 < u := Real.one_lt_exp_iff.mpr (by linarith)
  have hu0 : 0 < u := by linarith
  have hinv : Real.exp (-c / 2) = 1 / u := by
    rw [show -c / 2 = -(c / 2) by ring, Real.exp_neg, one_div]
  unfold levyCoshPotential
  rw [archLevyAntideriv_eq_log_div hc, Real.sinh_eq, ← show u = Real.exp (c / 2) from rfl,
    Real.exp_neg, ← one_div, hinv]
  have hfrac : (1 + 1 / u) / (1 - 1 / u) = (u + 1) / (u - 1) := by
    have : u - 1 ≠ 0 := by linarith
    have : 1 - 1 / u ≠ 0 := by
      intro h; apply ‹u - 1 ≠ 0›
      have := congr_arg (u * ·) h; field_simp at this; linarith
    field_simp
  rw [hfrac]
  ring

/-- Elementary lower bound on `arctan t` near `t = 1`:
for `0 ≤ t ≤ 1`, `π / 4 - (1 - t) / (1 + t^2) ≤ arctan t`. -/
theorem pi_div_four_sub_le_arctan {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Real.pi / 4 - (1 - t) / (1 + t ^ 2) ≤ Real.arctan t := by
  have hcont : Continuous fun s : ℝ => 1 / (1 + s ^ 2) :=
    continuous_const.div (by fun_prop) (fun s => by positivity)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := Real.arctan) (f' := fun s => 1 / (1 + s ^ 2)) (a := t) (b := 1)
    (fun s _ => Real.hasDerivAt_arctan s) (hcont.intervalIntegrable t 1)
  rw [Real.arctan_one] at hFTC
  have hle : ∫ s in t..1, 1 / (1 + s ^ 2) ≤ (1 - t) / (1 + t ^ 2) := by
    calc ∫ s in t..1, 1 / (1 + s ^ 2)
        ≤ ∫ _s in t..1, 1 / (1 + t ^ 2) := by
          refine intervalIntegral.integral_mono_on ht1 (hcont.intervalIntegrable t 1)
            intervalIntegrable_const fun s hs => ?_
          exact one_div_le_one_div_of_le (by positivity) (by nlinarith [hs.1])
      _ = (1 - t) / (1 + t ^ 2) := by simp [div_eq_mul_inv]
  linarith

/-- **Unconditional rational lower bound at the plastic-number threshold**:
`26 / 5 < levyCoshPotential screwSignThreshold` (`5.2 < Φ(t_*)`). -/
theorem twenty_six_fifths_lt_levyCoshPotential_screwSignThreshold :
    (26 : ℝ) / 5 < levyCoshPotential screwSignThreshold := by
  have hform := levyCoshPotential_eq_of_exp_half screwSignThreshold_pos
  dsimp only at hform
  set u := Real.exp (screwSignThreshold / 2)
  have hu_gt : (11509 : ℝ) / 10000 < u := exp_half_screwSignThreshold_gt
  have hu_lt : u < (1151 : ℝ) / 1000 := exp_half_screwSignThreshold_lt
  have hu0 : 0 < u := by linarith
  have hu1 : 0 < u - 1 := by linarith
  -- Term 1: 4 (u - 1 / u) > 4 (11509/10000 - 10000/11509) > 1128 / 1000
  have hterm1 : (1128 : ℝ) / 1000 < 4 * (u - 1 / u) := by
    have hinv : 1 / u < (10000 : ℝ) / 11509 := by
      rw [div_lt_div_iff₀ hu0 (by norm_num)]
      linarith
    linarith
  -- Term 2: log((u + 1) / (u - 1)) > 2655 / 1000 using (u + 1)/(u - 1) > 2151 / 151 and 2 e^2
  have hquot : (2151 : ℝ) / 151 < (u + 1) / (u - 1) := by
    rw [div_lt_div_iff₀ (by norm_num) hu1]
    linarith
  have hlog : (2655 : ℝ) / 1000 < Real.log ((u + 1) / (u - 1)) := by
    have h2151 : Real.log ((2151 : ℝ) / 151) < Real.log ((u + 1) / (u - 1)) :=
      Real.log_lt_log (by positivity) hquot
    have hdecomp : Real.log ((2151 : ℝ) / 151) =
        Real.log 2 + 2 - Real.log (2 * Real.exp 1 ^ 2 * 151 / 2151) := by
      have hepos : 0 < Real.exp 1 := Real.exp_pos 1
      have hprod : (2151 : ℝ) / 151 * (2 * Real.exp 1 ^ 2 * 151 / 2151) =
          2 * Real.exp 1 ^ 2 := by ring
      have h1 := Real.log_mul (by norm_num : (2151 : ℝ) / 151 ≠ 0)
        (by positivity : 2 * Real.exp 1 ^ 2 * 151 / 2151 ≠ 0)
      rw [hprod, Real.log_mul two_ne_zero (by positivity), Real.log_pow, Real.log_exp] at h1
      linarith
    have hrem : Real.log (2 * Real.exp 1 ^ 2 * 151 / 2151) ≤
        2 * Real.exp 1 ^ 2 * 151 / 2151 - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have he_lt := Real.exp_one_lt_d9
    have he_gt := Real.exp_one_gt_d9
    have hl2 := Real.log_two_gt_d9
    nlinarith
  -- Term 3: 2 arctan(1 / u) > 1421 / 1000
  have harc : (1421 : ℝ) / 1000 < 2 * Real.arctan (1 / u) := by
    have ht0 : 0 ≤ 1 / u := by positivity
    have ht1 : 1 / u ≤ 1 := div_le_one_of_le₀ (by linarith) hu0.le
    have hlow := pi_div_four_sub_le_arctan ht0 ht1
    have ht_gt : (1000 : ℝ) / 1151 < 1 / u := by
      rw [div_lt_div_iff₀ (by norm_num) hu0]
      linarith
    have hfrac_lt : (1 - 1 / u) / (1 + (1 / u) ^ 2) <
        (1 - (1000 : ℝ) / 1151) / (1 + ((1000 : ℝ) / 1151) ^ 2) := by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have hpi := Real.pi_gt_d4
    linarith
  rw [hform]
  linarith

/-- For every `c > 0`, `26 / 5 < levyCoshPotential c`. -/
theorem twenty_six_fifths_lt_levyCoshPotential {c : ℝ} (hc : 0 < c) :
    (26 : ℝ) / 5 < levyCoshPotential c :=
  lt_of_lt_of_le twenty_six_fifths_lt_levyCoshPotential_screwSignThreshold
    (levyCoshPotential_screwSignThreshold_le hc)

/-- At `screwSignThreshold`, `-(2 / 5) < EF.gammaBracket 0 + levyCoshPotential screwSignThreshold`. -/
theorem neg_two_fifths_lt_gammaBracket_add_levyCoshPotential_screwSignThreshold :
    -(2 / 5 : ℝ) < EF.gammaBracket 0 + levyCoshPotential screwSignThreshold := by
  have h1 := neg_gammaBracket_zero_lt
  have h2 := twenty_six_fifths_lt_levyCoshPotential_screwSignThreshold
  linarith

/-! ## Section 4: Piecewise Lévy–Cosh Kernel `levyCoshKernel` and Crossover Jump Identity -/

/-- The **piecewise Lévy–cosh crossover kernel** at threshold `c > 0`:
equals `2 cosh(x / 2)` on `x ≤ c` and `archLevyDensity x` on `x > c`. -/
def levyCoshKernel (c x : ℝ) : ℝ :=
  if x ≤ c then 2 * Real.cosh (x / 2) else archLevyDensity x

/-- `levyCoshKernel c x` is strictly positive for all `x > 0`. -/
theorem levyCoshKernel_pos {c x : ℝ} (hx : 0 < x) : 0 < levyCoshKernel c x := by
  unfold levyCoshKernel
  split_ifs
  · exact mul_pos zero_lt_two (Real.cosh_pos _)
  · exact archLevyDensity_pos hx

/-- `levyCoshKernel c` is measurable for every `c`. -/
theorem measurable_levyCoshKernel (c : ℝ) : Measurable (levyCoshKernel c) := by
  unfold levyCoshKernel archLevyDensity
  exact Measurable.ite measurableSet_Iic (by fun_prop) (by fun_prop)

/-- Global upper bound on `|levyCoshKernel c (|r|)|` across `r ∈ ℝ` for `c > 0`. -/
theorem abs_levyCoshKernel_abs_le {c : ℝ} (hc : 0 < c) (r : ℝ) :
    |levyCoshKernel c (|r|)| ≤ 2 * Real.cosh (c / 2) + (1 - Real.exp (-2 * c))⁻¹ := by
  have h1 : 0 < 2 * Real.cosh (c / 2) := mul_pos zero_lt_two (Real.cosh_pos _)
  have h2 : 0 < (1 - Real.exp (-2 * c))⁻¹ := by
    rw [inv_pos, sub_pos, Real.exp_lt_one_iff]; linarith
  unfold levyCoshKernel
  split_ifs with hle
  · rw [abs_of_pos (mul_pos zero_lt_two (Real.cosh_pos _))]
    have hcosh : Real.cosh (|r| / 2) ≤ Real.cosh (c / 2) :=
      Real.cosh_le_cosh.mpr (by
        rw [abs_div, abs_abs, abs_div, abs_two, abs_of_pos hc]
        linarith)
    linarith
  · have hle := not_le.mp hle
    have hr0 : 0 < |r| := lt_trans hc hle
    rw [abs_of_pos (archLevyDensity_pos hr0)]
    have hle' := archLevyDensity_le_of_le hc hle.le
    have hexp1 : Real.exp (-(1 / 2) * |r|) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by linarith)
    have h3 : (1 - Real.exp (-2 * c))⁻¹ * Real.exp (-(1 / 2) * |r|) ≤
        (1 - Real.exp (-2 * c))⁻¹ :=
      mul_le_of_le_one_right h2.le hexp1
    linarith

/-- For `c ≤ screwSignThreshold` and `x > 0`, `levyCoshKernel c x ≤ archLevyDensity x`. -/
theorem levyCoshKernel_le_archLevyDensity {c x : ℝ}
    (hct : c ≤ screwSignThreshold) (hx : 0 < x) :
    levyCoshKernel c x ≤ archLevyDensity x := by
  unfold levyCoshKernel
  split_ifs with hle
  · exact two_mul_cosh_le_archLevyDensity_of_le_threshold hx (hle.trans hct)
  · exact le_rfl

/-- More generally, for `0 < δ ≤ c ≤ screwSignThreshold` and `x > 0`, adding the `Ioo δ c` jump
excess `Set.indicator (Ioo δ c) (fun x => -screwRegularKernel x) x` to `levyCoshKernel c x`
remains bounded above by `archLevyDensity x`. -/
theorem levyCoshKernel_add_indicator_le_archLevyDensity {δ c x : ℝ}
    (hct : c ≤ screwSignThreshold) (hx : 0 < x) :
    levyCoshKernel c x +
        Set.indicator (Ioo δ c) (fun y => -screwRegularKernel y) x ≤
      archLevyDensity x := by
  by_cases hxI : x ∈ Ioo δ c
  · rw [Set.indicator_of_mem hxI]
    unfold levyCoshKernel
    rw [if_pos hxI.2.le, screwRegularKernel_eq_two_mul_cosh_sub_archLevyDensity hx]
    linarith
  · rw [Set.indicator_of_notMem hxI, add_zero]
    unfold levyCoshKernel
    split_ifs with hle
    · exact two_mul_cosh_le_archLevyDensity_of_le_threshold hx (hle.trans hct)
    · exact le_rfl

/-- At `c = screwSignThreshold`, `levyCoshKernel screwSignThreshold x = min (2 cosh(x/2)) (archLevyDensity x)`
for all `x > 0`. -/
theorem levyCoshKernel_screwSignThreshold_eq_min {x : ℝ} (hx : 0 < x) :
    levyCoshKernel screwSignThreshold x = min (2 * Real.cosh (x / 2)) (archLevyDensity x) := by
  unfold levyCoshKernel
  split_ifs with hle
  · exact (min_eq_left (two_mul_cosh_le_archLevyDensity_of_le_threshold hx hle)).symm
  · have hle := not_le.mp hle
    exact (min_eq_right (archLevyDensity_le_two_mul_cosh_of_threshold_le hle.le)).symm

/-- Exact formula for the residual 2D pair kernel `2 cosh((u - v)/2) - levyCoshKernel c |u - v|`:
it vanishes identically for `|r| ≤ c` and equals `screwRegularKernel |r|` for `|r| > c` (`c > 0`). -/
theorem two_mul_cosh_sub_levyCoshKernel_eq {c : ℝ} (hc : 0 < c) (r : ℝ) :
    2 * Real.cosh (r / 2) - levyCoshKernel c |r| =
      if |r| ≤ c then 0 else screwRegularKernel |r| := by
  have hca : Real.cosh (r / 2) = Real.cosh (|r| / 2) := by
    rw [← Real.cosh_abs, abs_div, abs_two]
  unfold levyCoshKernel
  split_ifs with hle
  · rw [hca, sub_self]
  · have hle := not_le.mp hle
    rw [hca, ← screwRegularKernel_eq_two_mul_cosh_sub_archLevyDensity (lt_trans hc hle)]

/-- When `screwSignThreshold ≤ c`, the residual pair kernel
`2 cosh(r / 2) - levyCoshKernel c |r|` is nonnegative for all `r ∈ ℝ`. -/
theorem two_mul_cosh_sub_levyCoshKernel_nonneg {c : ℝ} (hct : screwSignThreshold ≤ c) (r : ℝ) :
    0 ≤ 2 * Real.cosh (r / 2) - levyCoshKernel c |r| := by
  have hc : 0 < c := lt_of_lt_of_le screwSignThreshold_pos hct
  rw [two_mul_cosh_sub_levyCoshKernel_eq hc]
  split_ifs with hle
  · exact le_rfl
  · have hle := not_le.mp hle
    exact screwRegularKernel_nonneg_of_threshold_le (hct.trans hle.le)

/-- `levyCoshKernel c` is integrable on `Ioc 0 c`. -/
theorem integrableOn_levyCoshKernel_Ioc (c : ℝ) :
    IntegrableOn (levyCoshKernel c) (Ioc 0 c) := by
  refine ((by fun_prop : Continuous fun x : ℝ => 2 * Real.cosh (x / 2)).integrableOn_Ioc).congr_fun
    (fun x hx => ?_) measurableSet_Ioc
  unfold levyCoshKernel
  exact (if_pos hx.2).symm

/-- `levyCoshKernel c` is integrable on `Ioi c` for `c > 0`. -/
theorem integrableOn_levyCoshKernel_Ioi_of_pos {c : ℝ} (hc : 0 < c) :
    IntegrableOn (levyCoshKernel c) (Ioi c) := by
  refine (integrableOn_archLevyDensity_Ioi hc).congr_fun (fun x hx => ?_) measurableSet_Ioi
  unfold levyCoshKernel
  exact (if_neg (not_le.mpr hx)).symm

/-- `levyCoshKernel c` is integrable on `Ioi 0` for `c > 0`. -/
theorem integrableOn_levyCoshKernel_Ioi {c : ℝ} (hc : 0 < c) :
    IntegrableOn (levyCoshKernel c) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi hc.le]
  exact (integrableOn_levyCoshKernel_Ioc c).union (integrableOn_levyCoshKernel_Ioi_of_pos hc)

/-- **Exact integral of `levyCoshKernel c` on `(0, ∞)`**:
for every `c > 0`, `∫ x in Ioi 0, levyCoshKernel c x = (1 / 2) * levyCoshPotential c`. -/
theorem integral_levyCoshKernel_Ioi {c : ℝ} (hc : 0 < c) :
    ∫ x in Ioi 0, levyCoshKernel c x = (1 / 2) * levyCoshPotential c := by
  rw [← Ioc_union_Ioi_eq_Ioi hc.le,
    setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (integrableOn_levyCoshKernel_Ioc c) (integrableOn_levyCoshKernel_Ioi_of_pos hc)]
  have h1 : ∫ x in Ioc 0 c, levyCoshKernel c x = 4 * Real.sinh (c / 2) := by
    have hcongr : ∫ x in Ioc 0 c, levyCoshKernel c x =
        ∫ x in (0 : ℝ)..c, 2 * Real.cosh (x / 2) := by
      rw [intervalIntegral.integral_of_le hc.le]
      exact setIntegral_congr_fun measurableSet_Ioc fun x hx => by
        unfold levyCoshKernel; exact if_pos hx.2
    rw [hcongr]
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun x : ℝ => 4 * Real.sinh (x / 2))
      (f' := fun x : ℝ => 2 * Real.cosh (x / 2)) (a := 0) (b := c)
      (fun x _ => by
        have h := ((hasDerivAt_id x).div_const (2 : ℝ)).sinh.const_mul (4 : ℝ)
        exact h.congr_deriv (by dsimp only [id_eq]; ring))
      ((by fun_prop : Continuous fun x : ℝ => 2 * Real.cosh (x / 2)).intervalIntegrable 0 c)
    rw [hFTC, zero_div, Real.sinh_zero, mul_zero, sub_zero]
  have h2 : ∫ x in Ioi c, levyCoshKernel c x = archLevyAntideriv c := by
    rw [setIntegral_congr_fun measurableSet_Ioi fun x hx => by
      unfold levyCoshKernel; exact if_neg (not_le.mpr hx)]
    exact integral_archLevyDensity_Ioi hc
  rw [h1, h2]
  unfold levyCoshPotential
  ring

/-- **Exact jump integral identity for `levyCoshKernel c`**:
for any `BddSupp A h C` and `c > 0`,
`∫_{x > 0} levyCoshKernel c x * ∫ (h(u) - h(u + x))² du = levyCoshPotential c * ∫ h² - ∫∫ h(u) h(v) levyCoshKernel c |u - v| du dv`. -/
theorem integral_levyCoshKernel_mul_jump_sq {A : Set ℝ} {h : ℝ → ℝ} {C c : ℝ}
    (hh : BddSupp A h C) (hc : 0 < c) :
    ∫ x in Ioi (0 : ℝ), levyCoshKernel c x * (∫ u, (h u - h (u + x)) ^ 2) =
      levyCoshPotential c * (∫ u, h u ^ 2) -
        ∫ p : ℝ × ℝ, h p.1 * h p.2 * levyCoshKernel c |p.1 - p.2| := by
  set k : ℝ → ℝ := fun r => levyCoshKernel c |r| with hkdef
  have hk_meas : Measurable k := (measurable_levyCoshKernel c).comp measurable_abs
  have hk_bound : ∀ r, |k r| ≤ 2 * Real.cosh (c / 2) + (1 - Real.exp (-2 * c))⁻¹ :=
    abs_levyCoshKernel_abs_le hc
  have hpair := integral_pair_eq_two_mul_Ioi hh hk_meas hk_bound
  have hpair_eq : (∫ p : ℝ × ℝ, h p.1 * h p.2 * k |p.1 - p.2|) =
      ∫ p : ℝ × ℝ, h p.1 * h p.2 * levyCoshKernel c |p.1 - p.2| := by
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    simp [hkdef, abs_abs]
  rw [hpair_eq] at hpair
  have hI_ker : IntegrableOn (levyCoshKernel c) (Ioi 0) := integrableOn_levyCoshKernel_Ioi hc
  have hI_auto : IntegrableOn (fun x : ℝ => levyCoshKernel c x * autocorr h x) (Ioi 0) := by
    refine (integrable_kernel_mul_autocorr hh hk_meas hk_bound).integrableOn.congr_fun
      (fun x hx => ?_) measurableSet_Ioi
    simp [hkdef, abs_of_pos (mem_Ioi.mp hx)]
  have hcongr : EqOn (fun x : ℝ => levyCoshKernel c x * ∫ u, (h u - h (u + x)) ^ 2)
      (fun x : ℝ => 2 * (∫ u, h u ^ 2) * levyCoshKernel c x -
        2 * (levyCoshKernel c x * autocorr h x)) (Ioi 0) := fun x _ => by
    simp only
    rw [integral_jump_sq hh x]
    ring
  have hcongr_k : (∫ x in Ioi (0 : ℝ), k x * autocorr h x) =
      ∫ x in Ioi (0 : ℝ), levyCoshKernel c x * autocorr h x :=
    setIntegral_congr_fun measurableSet_Ioi fun x hx => by
      simp [hkdef, abs_of_pos (mem_Ioi.mp hx)]
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr,
    integral_sub (hI_ker.const_mul _) (hI_auto.const_mul 2),
    integral_const_mul, integral_const_mul,
    integral_levyCoshKernel_Ioi hc, hpair, hcongr_k]
  ring

/-- The 2D pair integral against `levyCoshKernel c |p.1 - p.2|` is integrable for `BddSupp A h C`. -/
theorem integrable_pair_levyCoshKernel {A : Set ℝ} {h : ℝ → ℝ} {C c : ℝ}
    (hh : BddSupp A h C) (hc : 0 < c) :
    Integrable (fun p : ℝ × ℝ => h p.1 * h p.2 * levyCoshKernel c |p.1 - p.2|) := by
  set M := 2 * Real.cosh (c / 2) + (1 - Real.exp (-2 * c))⁻¹
  rw [Measure.volume_eq_prod]
  refine ((hh.integrable.abs.mul_prod hh.integrable.abs).mul_const M).mono'
    (((hh.meas.comp measurable_fst).mul (hh.meas.comp measurable_snd)).mul
      ((measurable_levyCoshKernel c).comp (measurable_fst.sub measurable_snd).abs)).aestronglyMeasurable
    (ae_of_all _ fun p => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left (abs_levyCoshKernel_abs_le hc (p.1 - p.2))
    (mul_nonneg (abs_nonneg _) (abs_nonneg _))

/-! ## Section 5: Master Lévy–Cosh Crossover Lower Bound, Plastic Floor, and Signed Short-Support Positivity -/

/-- `ENNReal` lower bound on `jumpEnergy h` combining `levyCoshPotential c` and the `Ioo δ c`
jump integral for any `0 < δ ≤ c ≤ screwSignThreshold`. -/
theorem ofReal_levyCosh_add_jump_le_jumpEnergy {A : Set ℝ} {h : ℝ → ℝ} {C δ c : ℝ}
    (hh : BddSupp A h C) (hδ : 0 < δ) (hδc : δ ≤ c) (hct : c ≤ screwSignThreshold) :
    ENNReal.ofReal (levyCoshPotential c * (∫ u, h u ^ 2) -
        (∫ p : ℝ × ℝ, h p.1 * h p.2 * levyCoshKernel c |p.1 - p.2|) +
        ∫ x in Ioo δ c, (-screwRegularKernel x) * (∫ u, (h u - h (u + x)) ^ 2)) ≤
      jumpEnergy h := by
  have hc : 0 < c := lt_of_lt_of_le hδ hδc
  have h1 := integral_levyCoshKernel_mul_jump_sq hh hc
  have hD0 : ∀ x, 0 ≤ ∫ u, (h u - h (u + x)) ^ 2 := fun x => integral_nonneg fun _ => sq_nonneg _
  have hDm := measurable_jump hh
  have hI1 : IntegrableOn (fun x : ℝ => levyCoshKernel c x * ∫ u, (h u - h (u + x)) ^ 2)
      (Ioi 0) := by
    refine ((integrableOn_levyCoshKernel_Ioi hc).mul_const (4 * ∫ u, h u ^ 2)).mono'
      ((measurable_levyCoshKernel c).mul hDm).aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (levyCoshKernel_pos hx).le (hD0 x))]
    exact mul_le_mul_of_nonneg_left (jump_le hh x) (levyCoshKernel_pos hx).le
  have hcont_K : ContinuousOn (fun x => -screwRegularKernel x) (Icc δ c) :=
    (continuousOn_screwRegularKernel.mono fun x hx => lt_of_lt_of_le hδ hx.1).neg
  have hI_K_Ioo : IntegrableOn (fun x => -screwRegularKernel x) (Ioo δ c) :=
    hcont_K.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hKm : Measurable fun x : ℝ => -screwRegularKernel x := by
    unfold screwRegularKernel; fun_prop
  have hI2_Ioo : IntegrableOn (fun x : ℝ => (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2)
      (Ioo δ c) := by
    refine (hI_K_Ioo.mul_const (4 * ∫ u, h u ^ 2)).mono'
      (hKm.mul hDm).aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun x hx => ?_))
    have hK0 : 0 ≤ -screwRegularKernel x :=
      neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold (lt_trans hδ hx.1)
        (hx.2.le.trans hct))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK0 (hD0 x))]
    exact mul_le_mul_of_nonneg_left (jump_le hh x) hK0
  have hsub : Ioo δ c ⊆ Ioi 0 := fun x hx => lt_trans hδ hx.1
  have hI2 : IntegrableOn
      (fun x : ℝ => Set.indicator (Ioo δ c)
        (fun y => (-screwRegularKernel y) * ∫ u, (h u - h (u + y)) ^ 2) x) (Ioi 0) :=
    (integrable_indicator_iff measurableSet_Ioo).mpr hI2_Ioo |>.integrableOn
  have hind_eq : ∫ x in Ioi (0 : ℝ),
      Set.indicator (Ioo δ c)
        (fun y => (-screwRegularKernel y) * ∫ u, (h u - h (u + y)) ^ 2) x =
      ∫ x in Ioo δ c, (-screwRegularKernel x) * ∫ u, (h u - h (u + x)) ^ 2 := by
    rw [setIntegral_indicator measurableSet_Ioo, inter_eq_self_of_subset_right hsub]
  rw [← h1, ← hind_eq, ← integral_add hI1 hI2]
  have hnn : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ levyCoshKernel c x * (∫ u, (h u - h (u + x)) ^ 2) +
      Set.indicator (Ioo δ c)
        (fun y => (-screwRegularKernel y) * ∫ u, (h u - h (u + y)) ^ 2) x := by
    intro x hx
    refine add_nonneg (mul_nonneg (levyCoshKernel_pos hx).le (hD0 x)) ?_
    by_cases hxI : x ∈ Ioo δ c
    · rw [Set.indicator_of_mem hxI]
      exact mul_nonneg (neg_nonneg.mpr (screwRegularKernel_nonpos_of_le_threshold
        (lt_trans hδ hxI.1) (hxI.2.le.trans hct))) (hD0 x)
    · rw [Set.indicator_of_notMem hxI]
  have hI12 : IntegrableOn
      (fun x : ℝ => levyCoshKernel c x * (∫ u, (h u - h (u + x)) ^ 2) +
        Set.indicator (Ioo δ c)
          (fun y => (-screwRegularKernel y) * ∫ u, (h u - h (u + y)) ^ 2) x) (Ioi 0) :=
    hI1.add hI2
  rw [ofReal_integral_eq_lintegral_ofReal hI12
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall hnn))]
  unfold jumpEnergy
  refine setLIntegral_mono' measurableSet_Ioi fun x hx => ENNReal.ofReal_le_ofReal ?_
  have hind_mul : Set.indicator (Ioo δ c)
      (fun y => (-screwRegularKernel y) * ∫ u, (h u - h (u + y)) ^ 2) x =
      Set.indicator (Ioo δ c) (fun y => -screwRegularKernel y) x *
        ∫ u, (h u - h (u + x)) ^ 2 := by
    by_cases hxI : x ∈ Ioo δ c
    · simp [Set.indicator_of_mem hxI]
    · simp [Set.indicator_of_notMem hxI]
  rw [hind_mul, ← add_mul]
  exact mul_le_mul_of_nonneg_right (levyCoshKernel_add_indicator_le_archLevyDensity hct hx) (hD0 x)

private theorem le_toReal_of_ofReal_le {a : ℝ} {b : ENNReal} (hb : b ≠ ⊤)
    (h : ENNReal.ofReal a ≤ b) : a ≤ b.toReal := by
  have h1 := ENNReal.toReal_mono hb h
  rcases le_or_gt 0 a with ha | ha
  · rwa [ENNReal.toReal_ofReal ha] at h1
  · exact ha.le.trans ENNReal.toReal_nonneg

/-- **Master Lévy–Cosh Crossover Lower Bound for `weilArchRe` (all signed `f ∈ C²_c(ℝ)`)**:
for every `f ∈ C²_c(ℝ)` and `0 < δ ≤ c ≤ screwSignThreshold`,
`(A(0) + levyCoshPotential c) ∫ f² + ∫_{x ∈ (δ, c)} (-screwRegularKernel x) ‖f - f(· + x)‖₂² + ∫∫ f(u) f(v) (2 cosh((u - v)/2) - levyCoshKernel c |u - v|) du dv ≤ W_∞(f ⋆ f̃)`. -/
theorem levyCosh_crossover_add_jump_le_weilArchRe {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {δ c : ℝ} (hδ : 0 < δ) (hδc : δ ≤ c)
    (hct : c ≤ screwSignThreshold) :
    (EF.gammaBracket 0 + levyCoshPotential c) * (∫ u, f u ^ 2) +
        (∫ x in Ioo δ c, (-screwRegularKernel x) * (∫ u, (f u - f (u + x)) ^ 2)) +
        (∫ p : ℝ × ℝ, f p.1 * f p.2 *
          (2 * Real.cosh ((p.1 - p.2) / 2) - levyCoshKernel c |p.1 - p.2|)) ≤
      WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  have hc : 0 < c := lt_of_lt_of_le hδ hδc
  obtain ⟨R, C, hB⟩ := exists_bddSupp_of_hasCompactSupport hf.continuous hfc
  have hJ := jumpEnergy_ne_top_of_smooth hf hfc
  have h1 := le_toReal_of_ofReal_le hJ (ofReal_levyCosh_add_jump_le_jumpEnergy hB hδ hδc hct)
  have hcs_cosh : HasCompactSupport fun p : ℝ × ℝ =>
      f p.1 * f p.2 * Real.cosh ((p.1 - p.2) / 2) := by
    refine HasCompactSupport.intro (hfc.isCompact.prod hfc.isCompact) fun p hp => ?_
    rcases not_and_or.mp (show ¬(p.1 ∈ tsupport f ∧ p.2 ∈ tsupport f) from hp) with h1' | h2'
    · rw [image_eq_zero_of_notMem_tsupport h1']; ring
    · rw [image_eq_zero_of_notMem_tsupport h2']; ring
  have hI_cosh : Integrable fun p : ℝ × ℝ => f p.1 * f p.2 * Real.cosh ((p.1 - p.2) / 2) :=
    (by fun_prop : Continuous fun p : ℝ × ℝ =>
      f p.1 * f p.2 * Real.cosh ((p.1 - p.2) / 2)).integrable_of_hasCompactSupport hcs_cosh
  have hI_ker : Integrable fun p : ℝ × ℝ =>
      f p.1 * f p.2 * levyCoshKernel c |p.1 - p.2| :=
    integrable_pair_levyCoshKernel hB hc
  have hcomb : 2 * (∫ p : ℝ × ℝ, f p.1 * f p.2 * Real.cosh ((p.1 - p.2) / 2)) -
      (∫ p : ℝ × ℝ, f p.1 * f p.2 * levyCoshKernel c |p.1 - p.2|) =
      ∫ p : ℝ × ℝ, f p.1 * f p.2 *
        (2 * Real.cosh ((p.1 - p.2) / 2) - levyCoshKernel c |p.1 - p.2|) := by
    rw [← integral_const_mul, ← integral_sub (hI_cosh.const_mul 2) hI_ker]
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    simp only
    ring
  rw [weilArchRe_eq_levy_pole hf hfc]
  change _ ≤ EF.gammaBracket 0 * (∫ u, f u ^ 2) + (jumpEnergy f).toReal +
    2 * ∫ p : ℝ × ℝ, f p.1 * f p.2 * Real.cosh ((p.1 - p.2) / 2)
  linarith

/-- Dropping the nonnegative `Ioo δ c` jump integral gives the pure crossover lower bound for
all signed `f ∈ C²_c(ℝ)` and `0 < c ≤ screwSignThreshold`. -/
theorem levyCosh_crossover_le_weilArchRe {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {c : ℝ} (hc : 0 < c) (hct : c ≤ screwSignThreshold) :
    (EF.gammaBracket 0 + levyCoshPotential c) * (∫ u, f u ^ 2) +
        (∫ p : ℝ × ℝ, f p.1 * f p.2 *
          (2 * Real.cosh ((p.1 - p.2) / 2) - levyCoshKernel c |p.1 - p.2|)) ≤
      WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  have h := levyCosh_crossover_add_jump_le_weilArchRe hf hfc hc le_rfl hct
  rw [Ioo_self, setIntegral_empty] at h
  linarith

/-- **Plastic-number crossover bound on the nonnegative cone with `(δ, screwSignThreshold)`
jump energy retained**:
for every nonnegative `f ∈ C²_c(ℝ)` and every `0 < δ ≤ screwSignThreshold`,
`(A(0) + levyCoshPotential screwSignThreshold) ∫ f² + ∫_{x ∈ (δ, screwSignThreshold)} (-screwRegularKernel x) ‖f - f(· + x)‖₂² ≤ W_∞(f ⋆ f̃)`. -/
theorem plastic_floor_add_jump_le_weilArchRe {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hf0 : ∀ u, 0 ≤ f u) {δ : ℝ} (hδ : 0 < δ)
    (hδt : δ ≤ screwSignThreshold) :
    (EF.gammaBracket 0 + levyCoshPotential screwSignThreshold) * (∫ u, f u ^ 2) +
        (∫ x in Ioo δ screwSignThreshold,
          (-screwRegularKernel x) * (∫ u, (f u - f (u + x)) ^ 2)) ≤
      WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  have hmain := levyCosh_crossover_add_jump_le_weilArchRe hf hfc hδ hδt le_rfl
  have hpair_nn : 0 ≤ ∫ p : ℝ × ℝ, f p.1 * f p.2 *
      (2 * Real.cosh ((p.1 - p.2) / 2) - levyCoshKernel screwSignThreshold |p.1 - p.2|) :=
    integral_nonneg fun p => mul_nonneg (mul_nonneg (hf0 _) (hf0 _))
      (two_mul_cosh_sub_levyCoshKernel_nonneg le_rfl _)
  linarith

/-- **Universal plastic-number anomaly floor on the nonnegative cone**:
every nonnegative `f ∈ C²_c(ℝ)` satisfies
`(EF.gammaBracket 0 + levyCoshPotential screwSignThreshold) * ∫ f² ≤ W_∞(f ⋆ f̃)`. -/
theorem plastic_floor_le_weilArchRe {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hf0 : ∀ u, 0 ≤ f u) :
    (EF.gammaBracket 0 + levyCoshPotential screwSignThreshold) * (∫ u, f u ^ 2) ≤
      WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  have h := plastic_floor_add_jump_le_weilArchRe hf hfc hf0 screwSignThreshold_pos le_rfl
  rw [Ioo_self, setIntegral_empty] at h
  linarith

/-- **Rational plastic-number floor on the nonnegative cone**:
every nonnegative `f ∈ C²_c(ℝ)` satisfies `-(2 / 5) * ∫ f² ≤ W_∞(f ⋆ f̃)`. -/
theorem rational_plastic_floor_le_weilArchRe {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hf0 : ∀ u, 0 ≤ f u) :
    -(2 / 5 : ℝ) * (∫ u, f u ^ 2) ≤
      WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  have h1 := plastic_floor_le_weilArchRe hf hfc hf0
  have h2 := neg_two_fifths_lt_gammaBracket_add_levyCoshPotential_screwSignThreshold
  have hsq : 0 ≤ ∫ u, f u ^ 2 := integral_nonneg fun _ => sq_nonneg _
  nlinarith

/-- **Signed short-support Lévy–cosh lower bound**:
for **every signed** (not necessarily nonnegative!) `f ∈ C²_c(ℝ)` vanishing outside `[a, a + L]`
with `0 < L ≤ screwSignThreshold`, the residual pair integral vanishes identically and
`(EF.gammaBracket 0 + levyCoshPotential L) * ∫ f² ≤ W_∞(f ⋆ f̃)`. -/
theorem levyCosh_signed_short_support_le_weilArchRe {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {a L : ℝ} (hL0 : 0 < L) (hLt : L ≤ screwSignThreshold)
    (hsupp : ∀ u ∉ Icc a (a + L), f u = 0) :
    (EF.gammaBracket 0 + levyCoshPotential L) * (∫ u, f u ^ 2) ≤
      WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  have hmain := levyCosh_crossover_le_weilArchRe hf hfc hL0 hLt
  have hpair0 : (∫ p : ℝ × ℝ, f p.1 * f p.2 *
      (2 * Real.cosh ((p.1 - p.2) / 2) - levyCoshKernel L |p.1 - p.2|)) = 0 := by
    have hzero : ∀ p : ℝ × ℝ,
        f p.1 * f p.2 * (2 * Real.cosh ((p.1 - p.2) / 2) - levyCoshKernel L |p.1 - p.2|) = 0 := by
      intro p
      by_cases hp1 : p.1 ∈ Icc a (a + L)
      · by_cases hp2 : p.2 ∈ Icc a (a + L)
        · have habs : |p.1 - p.2| ≤ L := abs_le.mpr ⟨by linarith [hp1.1, hp2.2],
            by linarith [hp1.2, hp2.1]⟩
          rw [two_mul_cosh_sub_levyCoshKernel_eq hL0, if_pos habs, mul_zero]
        · rw [hsupp p.2 hp2, mul_zero, zero_mul]
      · rw [hsupp p.1 hp1, zero_mul, zero_mul]
    simp_rw [hzero, integral_zero]
  linarith

/-- **Unconditional signed short-support positivity of `weilArchRe`**:
for **every signed** `f ∈ C²_c(ℝ)` vanishing outside `[a, a + L]` with `0 < L ≤ screwSignThreshold`
and `-EF.gammaBracket 0 ≤ levyCoshPotential L`, `0 ≤ W_∞(f ⋆ f̃)` holds unconditionally
(requiring neither `f ≥ 0` nor `WindowPositive`). -/
theorem weilArchRe_nonneg_of_signed_support_Icc_le {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {a L : ℝ} (hL0 : 0 < L) (hLt : L ≤ screwSignThreshold)
    (hsupp : ∀ u ∉ Icc a (a + L), f u = 0)
    (hΦ : -EF.gammaBracket 0 ≤ levyCoshPotential L) :
    0 ≤ WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  have hmain := levyCosh_signed_short_support_le_weilArchRe hf hfc hL0 hLt hsupp
  have hsq : 0 ≤ ∫ u, f u ^ 2 := integral_nonneg fun _ => sq_nonneg _
  nlinarith

/-- Rational lower bound `13 / 50 < screwSignThreshold` (`0.26 < t_*`). -/
theorem screwSignThreshold_gt : (13 : ℝ) / 50 < screwSignThreshold := by
  have hu := exp_half_screwSignThreshold_gt
  have hu0 : 0 < Real.exp (screwSignThreshold / 2) := Real.exp_pos _
  have hinv : Real.exp (-(screwSignThreshold / 2)) < (10000 : ℝ) / 11509 := by
    rw [Real.exp_neg, ← one_div, div_lt_div_iff₀ hu0 (by norm_num)]
    linarith
  have hexp := Real.add_one_le_exp (-(screwSignThreshold / 2))
  linarith

/-- Rational upper bound `screwSignThreshold < 151 / 500` (`t_* < 0.302`). -/
theorem screwSignThreshold_lt : screwSignThreshold < (151 : ℝ) / 500 := by
  have hu := exp_half_screwSignThreshold_lt
  have hexp := Real.add_one_le_exp (screwSignThreshold / 2)
  linarith

/-- Concrete unconditional signed short-support positivity on `[a, a + L]` for all
`0 < L ≤ 1 / 130` (requiring neither `f ≥ 0` nor `WindowPositive`). -/
theorem weilArchRe_nonneg_of_signed_support_Icc_le_inv_130 {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {a L : ℝ} (hL0 : 0 < L) (hL : L ≤ 1 / 130)
    (hsupp : ∀ u ∉ Icc a (a + L), f u = 0) :
    0 ≤ WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  have hLt : L ≤ screwSignThreshold := by linarith [screwSignThreshold_gt]
  have hΦ : -EF.gammaBracket 0 ≤ levyCoshPotential L :=
    (neg_gammaBracket_zero_le_two_mul_archLevyAntideriv hL0 hL).trans
      (two_mul_archLevyAntideriv_lt_levyCoshPotential hL0).le
  exact weilArchRe_nonneg_of_signed_support_Icc_le hf hfc hL0 hLt hsupp hΦ

end

end RHTower.WeilLevyCoshCrossover
