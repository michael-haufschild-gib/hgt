import GaloisForLFunctions.HTGeometry.ExponentialWallBurnolPartner
import GaloisForLFunctions.RHTower.RestrictedUnitaryCubicRelativeIndex
import GaloisForLFunctions.RHTower.SourceHorizontalWoldBVCompleteSplitPrimitiveBudgetFirewall
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# Cubic aperture-gauged Euler–continuum synthesis

On the Burnol carrier `H_B = L²((0, ∞), dr)` the radial features `f_s(r) = r e^{-sr}` have the
Cauchy-cubic Gram `⟨f_s, f_u⟩ = 2/(s + u)³`, so `‖f_s‖² = 1/(4s³)` blows up at the continuum
zero mode `s = 0`.  The cubic aperture gauge

`g_{x,c,s} = √(h_x(s)) d_c(s)^{3/2} f_s`,  `h_x(s) = exp(-πx e^{2s})`,  `d_c(s) = 1 - e^{-2cs}`,

makes the continuum synthesis `A₀ a = ∫ a(s) g_s ds : L²(ds) → H_B` Hilbert–Schmidt with
`‖A₀‖²_HS = ¼ ∫ h_x d_c³ / s³ ds < ∞`, because `d_c(s) ≤ 2cs`.  The defect order three is sharp:
the order-`q` energy `¼ ∫ h_x d_c^q / s³ ds` is finite exactly for `q ≥ 3`, since `d_c(s) ≥ cs` and
`h_x ≥ e^{-πxe}` near zero.  The atomic synthesis `A_E` with vectors
`a_n f_{log n}`, `a_n = √(Λ(n)/n) e^{-πxn²/2} (1 - n^{-2c})^{3/2}`, is Hilbert–Schmidt with
`‖A_E‖²_HS = ¼ ∑ Λ(n)/n · e^{-πxn²} (1 - n^{-2c})³ / log³ n ≤ B_base < 1`.
-/

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-! ## The Cauchy-cubic Gram -/

/-- The Burnol radial feature `f_s(r) = r e^{-sr}`. -/
def burnolRadial (s r : ℝ) : ℝ := r * Real.exp (-(s * r))

theorem burnolRadial_mul (s u r : ℝ) :
    burnolRadial s r * burnolRadial u r = r ^ 2 * Real.exp (-((s + u) * r)) := by
  unfold burnolRadial
  rw [show r * Real.exp (-(s * r)) * (r * Real.exp (-(u * r)))
      = r ^ 2 * (Real.exp (-(s * r)) * Real.exp (-(u * r))) by ring, ← Real.exp_add]
  ring_nf

/-- **(CAGC.1).**  `⟨f_s, f_u⟩ = 2/(s + u)³`. -/
theorem integral_burnolRadial_mul {s u : ℝ} (h : 0 < s + u) :
    ∫ r, burnolRadial s r * burnolRadial u r ∂halfLineMeasure = 2 / (s + u) ^ 3 := by
  simp_rw [burnolRadial_mul]
  rw [halfLineMeasure, integral_Ici_eq_integral_Ioi, integral_pow_mul_exp_neg_mul_Ioi 2 h]
  norm_num

/-- **(CAGC.1).**  `‖f_s‖² = 1/(4s³)`. -/
theorem integral_burnolRadial_sq {s : ℝ} (hs : 0 < s) :
    ∫ r, burnolRadial s r ^ 2 ∂halfLineMeasure = 1 / (4 * s ^ 3) := by
  simp_rw [sq]
  rw [integral_burnolRadial_mul (by linarith)]
  field_simp
  ring

theorem integrableOn_burnolRadial_sq {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun r => burnolRadial s r ^ 2) (Ioi 0) := by
  have h := integrableOn_pow_mul_exp_neg_mul_Ioi 2 (show 0 < s + s by linarith)
  refine IntegrableOn.congr_fun h (fun r _ => ?_) measurableSet_Ioi
  show _ = burnolRadial s r ^ 2
  rw [sq (burnolRadial s r), burnolRadial_mul]

theorem lintegral_burnolRadial_sq {s : ℝ} (hs : 0 < s) :
    ∫⁻ r, ENNReal.ofReal (burnolRadial s r ^ 2) ∂halfLineMeasure
      = ENNReal.ofReal (1 / (4 * s ^ 3)) := by
  rw [← integral_burnolRadial_sq hs, halfLineMeasure, setLIntegral_congr Ioi_ae_eq_Ici.symm,
    integral_Ici_eq_integral_Ioi]
  exact (ofReal_integral_eq_lintegral_ofReal (integrableOn_burnolRadial_sq hs)
    (Eventually.of_forall fun r => sq_nonneg _)).symm

/-! ## The cubic aperture gauge -/

/-- The theta damping `h_x(s) = exp(-πx e^{2s})`. -/
def thetaDamping (x s : ℝ) : ℝ := Real.exp (-(Real.pi * x * Real.exp (2 * s)))

/-- The aperture defect `d_c(s) = 1 - e^{-2cs}`. -/
def apertureDefect (c s : ℝ) : ℝ := 1 - Real.exp (-(2 * c * s))

/-- The cubic gauge weight `√(h_x(s)) d_c(s)^{3/2}`. -/
def cubicGaugeWeight (x c s : ℝ) : ℝ :=
  Real.sqrt (thetaDamping x s) * apertureDefect c s ^ ((3 : ℝ) / 2)

theorem thetaDamping_pos (x s : ℝ) : 0 < thetaDamping x s := Real.exp_pos _

theorem thetaDamping_le_one {x : ℝ} (hx : 0 ≤ x) (s : ℝ) : thetaDamping x s ≤ 1 := by
  rw [thetaDamping, Real.exp_le_one_iff]
  have := Real.exp_pos (2 * s)
  have : 0 ≤ Real.pi * x * Real.exp (2 * s) := by positivity
  linarith

theorem apertureDefect_nonneg {c s : ℝ} (hc : 0 ≤ c) (hs : 0 ≤ s) : 0 ≤ apertureDefect c s := by
  rw [apertureDefect, sub_nonneg, Real.exp_le_one_iff]
  have : 0 ≤ 2 * c * s := by positivity
  linarith

theorem apertureDefect_le_one (c s : ℝ) : apertureDefect c s ≤ 1 := by
  rw [apertureDefect]
  linarith [Real.exp_pos (-(2 * c * s))]

theorem apertureDefect_le (c s : ℝ) : apertureDefect c s ≤ 2 * c * s := by
  rw [apertureDefect]
  linarith [Real.add_one_le_exp (-(2 * c * s))]

theorem apertureDefect_ge {c s : ℝ} (hc : 0 ≤ c) (hs : 0 ≤ s) (h1 : 2 * c * s ≤ 1) :
    c * s ≤ apertureDefect c s := by
  set u := 2 * c * s
  have hu : 0 ≤ u := by positivity
  have hexp : Real.exp (-u) ≤ 1 - u / 2 := by
    have h1' := Real.add_one_le_exp u
    have hpos := Real.exp_pos u
    rw [Real.exp_neg, inv_le_iff_one_le_mul₀ hpos]
    nlinarith
  rw [apertureDefect]
  change c * s ≤ 1 - Real.exp (-u)
  have : c * s = u / 2 := by simp only [u]; ring
  linarith

theorem cubicGaugeWeight_sq {x c s : ℝ} (hc : 0 ≤ c) (hs : 0 ≤ s) :
    cubicGaugeWeight x c s ^ 2 = thetaDamping x s * apertureDefect c s ^ 3 := by
  have hd := apertureDefect_nonneg hc hs
  rw [cubicGaugeWeight, mul_pow, Real.sq_sqrt (thetaDamping_pos x s).le, ← Real.rpow_natCast,
    ← Real.rpow_mul hd]
  norm_num

theorem continuous_cubicGaugeWeight (x c : ℝ) : Continuous (cubicGaugeWeight x c) := by
  unfold cubicGaugeWeight thetaDamping apertureDefect
  exact (Real.continuous_sqrt.comp (by fun_prop)).mul
    ((Real.continuous_rpow_const (by norm_num)).comp (by fun_prop))

/-! ## Energies and the order-three threshold -/

/-- The order-`q` continuum energy density `h_x(s) d_c(s)^q / (4s³)`. -/
def continuumEnergyDensity (q : ℕ) (x c s : ℝ) : ℝ :=
  thetaDamping x s * apertureDefect c s ^ q / (4 * s ^ 3)

theorem continuumEnergyDensity_nonneg (q : ℕ) {x c s : ℝ} (hc : 0 ≤ c) (hs : 0 < s) :
    0 ≤ continuumEnergyDensity q x c s := by
  have := apertureDefect_nonneg hc hs.le
  have := thetaDamping_pos x s
  unfold continuumEnergyDensity
  positivity

theorem integrableOn_continuumEnergyDensity {x c : ℝ} (hx : 0 ≤ x) (hc : 0 < c) :
    IntegrableOn (continuumEnergyDensity 3 x c) (Ioi 0) := by
  have hmeas : Measurable (continuumEnergyDensity 3 x c) := by
    unfold continuumEnergyDensity thetaDamping apertureDefect
    fun_prop
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  refine IntegrableOn.union ?_ ?_
  · refine Measure.integrableOn_of_bounded (M := 2 * c ^ 3) measure_Ioc_lt_top.ne
      hmeas.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun s hs => ?_)
    have hs0 : 0 < s := hs.1
    rw [Real.norm_eq_abs, abs_of_nonneg (continuumEnergyDensity_nonneg 3 hc.le hs0),
      continuumEnergyDensity, div_le_iff₀ (by positivity)]
    have hd0 := apertureDefect_nonneg hc.le hs0.le
    have hd := apertureDefect_le c s
    have hh := thetaDamping_le_one hx s
    have hh0 := (thetaDamping_pos x s).le
    have h3 : apertureDefect c s ^ 3 ≤ (2 * c * s) ^ 3 := pow_le_pow_left₀ hd0 hd 3
    calc thetaDamping x s * apertureDefect c s ^ 3 ≤ 1 * (2 * c * s) ^ 3 :=
          mul_le_mul hh h3 (by positivity) zero_le_one
      _ = 2 * c ^ 3 * (4 * s ^ 3) := by ring
  · have hg := (integrableOn_Ioi_rpow_of_lt (show (-3 : ℝ) < -1 by norm_num) one_pos).const_mul
      (1 / 4 : ℝ)
    refine hg.mono' hmeas.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun s hs => ?_))
    have hs0 : 0 < s := lt_trans one_pos hs
    rw [Real.norm_eq_abs, abs_of_nonneg (continuumEnergyDensity_nonneg 3 hc.le hs0),
      continuumEnergyDensity, Real.rpow_neg hs0.le]
    norm_num
    have hd0 := apertureDefect_nonneg hc.le hs0.le
    have hd1 := apertureDefect_le_one c s
    have hh := thetaDamping_le_one hx s
    have hh0 := (thetaDamping_pos x s).le
    have h3 : apertureDefect c s ^ 3 ≤ 1 := pow_le_one₀ hd0 hd1
    have hnum : thetaDamping x s * apertureDefect c s ^ 3 ≤ 1 :=
      mul_le_one₀ hh (pow_nonneg hd0 3) h3
    rw [div_le_iff₀ (by positivity)]
    field_simp
    nlinarith [pow_pos hs0 3]

/-- **Theorem CAGC-A (minimality).**  The order-`q` continuum energy is finite exactly for
`q ≥ 3`. -/
theorem lintegral_continuumEnergyDensity_lt_top_iff {x c : ℝ} (hx : 0 < x) (hc : 0 < c) (q : ℕ) :
    ∫⁻ s in Ioi 0, ENNReal.ofReal (continuumEnergyDensity q x c s) < ∞ ↔ 3 ≤ q := by
  constructor
  · intro hfin
    by_contra hq
    push Not at hq
    set ε : ℝ := min (1 / 2) (1 / (2 * c))
    have hε : 0 < ε := lt_min (by norm_num) (by positivity)
    set C : ℝ := Real.exp (-(Real.pi * x * Real.exp 1)) * c ^ q / 4
    have hC : 0 < C := by positivity
    have hlow : ∀ s ∈ Ioo 0 ε, C * s ^ (-1 : ℝ) ≤ continuumEnergyDensity q x c s := by
      intro s hs
      have hs0 : 0 < s := hs.1
      have hs1 : s ≤ 1 / 2 := hs.2.le.trans (min_le_left _ _)
      have hsc : 2 * c * s ≤ 1 := by
        have := hs.2.le.trans (min_le_right _ _)
        rw [le_div_iff₀ (by positivity)] at this
        linarith
      have hd := apertureDefect_ge hc.le hs0.le hsc
      have hh : Real.exp (-(Real.pi * x * Real.exp 1)) ≤ thetaDamping x s := by
        rw [thetaDamping, Real.exp_le_exp, neg_le_neg_iff]
        have : Real.exp (2 * s) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by linarith)
        exact mul_le_mul_of_nonneg_left this (by positivity)
      rw [Real.rpow_neg_one, continuumEnergyDensity, le_div_iff₀ (by positivity)]
      have hpow : (c * s) ^ q ≤ apertureDefect c s ^ q := pow_le_pow_left₀ (by positivity) hd q
      have hsq : s ^ 3 ≤ s ^ (q + 1) := pow_le_pow_of_le_one hs0.le (by linarith) (by omega)
      calc C * s⁻¹ * (4 * s ^ 3)
          = Real.exp (-(Real.pi * x * Real.exp 1)) * c ^ q * s ^ 3 / s := by
            simp only [C]; field_simp
        _ ≤ Real.exp (-(Real.pi * x * Real.exp 1)) * c ^ q * s ^ (q + 1) / s := by
            gcongr
        _ = Real.exp (-(Real.pi * x * Real.exp 1)) * (c * s) ^ q := by
            rw [mul_pow, pow_succ]
            field_simp
        _ ≤ thetaDamping x s * apertureDefect c s ^ q :=
            mul_le_mul hh hpow (by positivity) (thetaDamping_pos x s).le
    have hnot : ¬ IntegrableOn (fun s : ℝ => C * s ^ (-1 : ℝ)) (Ioo 0 ε) := by
      intro h
      have h' : IntegrableOn (fun s : ℝ => C⁻¹ * (C * s ^ (-1 : ℝ))) (Ioo 0 ε) :=
        h.const_mul C⁻¹
      have := (intervalIntegral.integrableOn_Ioo_rpow_iff hε).mp
        (IntegrableOn.congr_fun h' (fun s _ => by field_simp) measurableSet_Ioo)
      norm_num at this
    apply hnot
    refine ⟨(by fun_prop : Measurable fun s : ℝ => C * s ^ (-1 : ℝ)).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal ((ae_restrict_iff' measurableSet_Ioo).mpr
      (Eventually.of_forall fun s hs => by have : 0 < s := hs.1; positivity))]
    refine lt_of_le_of_lt ?_ hfin
    refine (setLIntegral_mono' measurableSet_Ioo fun s hs => ENNReal.ofReal_le_ofReal
      (hlow s hs)).trans (lintegral_mono_set Ioo_subset_Ioi_self)
  · intro hq
    have hint := integrableOn_continuumEnergyDensity hx.le hc
    have hfin : ∫⁻ s in Ioi 0, ENNReal.ofReal (continuumEnergyDensity 3 x c s) < ∞ := by
      rw [← ofReal_integral_eq_lintegral_ofReal hint
        ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun s hs =>
          continuumEnergyDensity_nonneg 3 hc.le hs))]
      exact ENNReal.ofReal_lt_top
    refine lt_of_le_of_lt (setLIntegral_mono' measurableSet_Ioi fun s hs => ?_) hfin
    refine ENNReal.ofReal_le_ofReal ?_
    have hs0 : 0 < s := hs
    unfold continuumEnergyDensity
    have hd0 := apertureDefect_nonneg hc.le hs0.le
    have hd1 := apertureDefect_le_one c s
    have : apertureDefect c s ^ q ≤ apertureDefect c s ^ 3 := pow_le_pow_of_le_one hd0 hd1 hq
    have := (thetaDamping_pos x s).le
    gcongr

/-! ## The continuum synthesis -/

local instance factTwoNeTopCubicAperture : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩

theorem continuous_continuumFeature (x c : ℝ) :
    Continuous fun p : ℝ × ℝ => cubicGaugeWeight x c p.2 * burnolRadial p.2 p.1 := by
  have h1 : Continuous fun p : ℝ × ℝ => cubicGaugeWeight x c p.2 :=
    (continuous_cubicGaugeWeight x c).comp continuous_snd
  have h2 : Continuous fun p : ℝ × ℝ => burnolRadial p.2 p.1 := by
    unfold burnolRadial
    fun_prop
  exact h1.mul h2

theorem lintegral_continuumFeature_sq {x c s : ℝ} (hc : 0 < c) (hs : 0 < s) :
    ∫⁻ r, ‖((cubicGaugeWeight x c s * burnolRadial s r : ℝ) : ℂ)‖ₑ ^ 2 ∂halfLineMeasure
      = ENNReal.ofReal (continuumEnergyDensity 3 x c s) := by
  simp_rw [enorm_ofReal_sq, mul_pow]
  simp_rw [ENNReal.ofReal_mul (sq_nonneg (cubicGaugeWeight x c s))]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_burnolRadial_sq hs,
    ← ENNReal.ofReal_mul (sq_nonneg _), cubicGaugeWeight_sq hc.le hs.le, continuumEnergyDensity]
  congr 1
  field_simp

theorem lintegral_lintegral_continuumFeature {x c : ℝ} (hx : 0 < x) (hc : 0 < c) :
    ∫⁻ r, ∫⁻ s, ‖((cubicGaugeWeight x c s * burnolRadial s r : ℝ) : ℂ)‖ₑ ^ 2
        ∂halfLineMeasure ∂halfLineMeasure
      = ENNReal.ofReal (∫ s in Ioi 0, continuumEnergyDensity 3 x c s) := by
  have hc0 : Measurable fun p : ℝ × ℝ => ((cubicGaugeWeight x c p.2 * burnolRadial p.2 p.1 : ℝ) :
      ℂ) := (Complex.continuous_ofReal.comp (continuous_continuumFeature x c)).measurable
  have hm : Measurable (Function.uncurry fun r s =>
      ‖((cubicGaugeWeight x c s * burnolRadial s r : ℝ) : ℂ)‖ₑ ^ 2) := hc0.enorm.pow_const 2
  rw [lintegral_lintegral_swap hm.aemeasurable, halfLineMeasure,
    setLIntegral_congr Ioi_ae_eq_Ici.symm]
  rw [setLIntegral_congr_fun measurableSet_Ioi fun s hs => lintegral_continuumFeature_sq hc hs]
  exact (ofReal_integral_eq_lintegral_ofReal (integrableOn_continuumEnergyDensity hx.le hc)
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun s hs =>
      continuumEnergyDensity_nonneg 3 hc.le hs))).symm

/-- The continuum kernel `(r, s) ↦ g_{x,c,s}(r)`. -/
def continuumKernel {x c : ℝ} (hx : 0 < x) (hc : 0 < c) :
    SqIntKernel halfLineMeasure halfLineMeasure where
  toFun r s := ((cubicGaugeWeight x c s * burnolRadial s r : ℝ) : ℂ)
  measurable := (Complex.continuous_ofReal.comp (continuous_continuumFeature x c)).measurable
  energy_lt_top := by
    rw [lintegral_lintegral_continuumFeature hx hc]
    exact ENNReal.ofReal_lt_top

/-- **(CAGC.3).**  The continuum synthesis `A₀ a = ∫ a(s) g_{x,c,s} ds`. -/
def continuumSynthesis {x c : ℝ} (hx : 0 < x) (hc : 0 < c) :
    Lp ℂ 2 halfLineMeasure →L[ℂ] Lp ℂ 2 halfLineMeasure :=
  (continuumKernel hx hc).op

/-- **Theorem CAGC-A.**  `A₀` is Hilbert–Schmidt. -/
theorem isHilbertSchmidt_continuumSynthesis {x c : ℝ} (hx : 0 < x) (hc : 0 < c) :
    ContinuousLinearMap.IsHilbertSchmidt (continuumSynthesis hx hc) :=
  (continuumKernel hx hc).isHilbertSchmidt_op

/-- **(CAGC.5).**  `‖A₀‖²_HS = ¼ ∫ h_x d_c³ / s³ ds < ∞`. -/
theorem hsNormSq_continuumSynthesis {x c : ℝ} (hx : 0 < x) (hc : 0 < c) :
    ContinuousLinearMap.hsNormSq (continuumSynthesis hx hc)
      = 1 / 4 * ∫ s in Ioi 0, thetaDamping x s * apertureDefect c s ^ 3 / s ^ 3 := by
  rw [continuumSynthesis, SqIntKernel.hsNormSq_op, SqIntKernel.energy]
  change (∫⁻ r, ∫⁻ s, ‖((cubicGaugeWeight x c s * burnolRadial s r : ℝ) : ℂ)‖ₑ ^ 2
    ∂halfLineMeasure ∂halfLineMeasure).toReal = _
  rw [lintegral_lintegral_continuumFeature hx hc, ENNReal.toReal_ofReal
    (setIntegral_nonneg measurableSet_Ioi fun s hs => continuumEnergyDensity_nonneg 3 hc.le hs),
    ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  rw [continuumEnergyDensity]
  ring

/-! ## The atomic synthesis -/

/-- Literal integer labels `n ≥ 2`. -/
abbrev AtomLabel := {n : ℕ // 2 ≤ n}

/-- The atomic coefficient `a_n = √(Λ(n)/n) e^{-πxn²/2} (1 - n^{-2c})^{3/2}`. -/
def atomicCoefficient (x c : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (ArithmeticFunction.vonMangoldt n / n) * Real.exp (-(Real.pi * x * n ^ 2 / 2))
    * (1 - (n : ℝ) ^ (-(2 * c))) ^ ((3 : ℝ) / 2)

theorem one_sub_rpow_nonneg {n : ℕ} (hn : 1 ≤ n) {c : ℝ} (hc : 0 ≤ c) :
    0 ≤ 1 - (n : ℝ) ^ (-(2 * c)) := by
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have : (n : ℝ) ^ (-(2 * c)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith)
  linarith

theorem atomicCoefficient_sq {x c : ℝ} (hc : 0 ≤ c) {n : ℕ} (hn : 1 ≤ n) :
    atomicCoefficient x c n ^ 2 = ArithmeticFunction.vonMangoldt n / n
      * Real.exp (-(Real.pi * x * n ^ 2)) * (1 - (n : ℝ) ^ (-(2 * c))) ^ 3 := by
  have hd := one_sub_rpow_nonneg hn hc
  have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt n / (n : ℝ) :=
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _)
  have he : Real.exp (-(Real.pi * x * n ^ 2 / 2)) ^ 2 = Real.exp (-(Real.pi * x * n ^ 2)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hr : ((1 - (n : ℝ) ^ (-(2 * c))) ^ ((3 : ℝ) / 2)) ^ 2 = (1 - (n : ℝ) ^ (-(2 * c))) ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hd]
    norm_num
  rw [atomicCoefficient, mul_pow, mul_pow, Real.sq_sqrt hΛ, he, hr]

theorem log_pos_of_atomLabel (n : AtomLabel) : 0 < Real.log (n : ℕ) :=
  Real.log_pos (by exact_mod_cast (show 1 < (n : ℕ) by have := n.2; omega))

/-- The atomic energy term `a_n² ‖f_{log n}‖² = a_n²/(4 log³ n)`. -/
def atomicEnergyTerm (x c : ℝ) (n : AtomLabel) : ℝ :=
  atomicCoefficient x c n ^ 2 / (4 * Real.log (n : ℕ) ^ 3)

theorem atomicEnergyTerm_nonneg (x c : ℝ) (n : AtomLabel) : 0 ≤ atomicEnergyTerm x c n := by
  have := log_pos_of_atomLabel n
  unfold atomicEnergyTerm
  positivity

theorem atomicEnergyTerm_le_base {x c : ℝ} (hx : 0 ≤ x) (hc : 0 ≤ c) (n : AtomLabel) :
    atomicEnergyTerm x c n ≤ RHTower.routePPrimeGammaBaseCubicWeight n := by
  have hn1 : 1 ≤ (n : ℕ) := le_trans (by norm_num) n.2
  have hlog := log_pos_of_atomLabel n
  rw [atomicEnergyTerm, atomicCoefficient_sq hc hn1,
    RHTower.routePPrimeGammaBaseCubicWeight_eq_vonMangoldt, RHTower.finiteVonMangoldtRealWeight]
  have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt (n : ℕ) / ((n : ℕ) : ℝ) :=
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _)
  have hexp : Real.exp (-(Real.pi * x * ((n : ℕ) : ℝ) ^ 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ Real.pi * x * ((n : ℕ) : ℝ) ^ 2 := by positivity
    linarith
  have hd0 := one_sub_rpow_nonneg hn1 hc
  have hd1 : 1 - ((n : ℕ) : ℝ) ^ (-(2 * c)) ≤ 1 := by
    linarith [Real.rpow_nonneg (Nat.cast_nonneg ((n : ℕ))) (-(2 * c))]
  have hd3 : (1 - ((n : ℕ) : ℝ) ^ (-(2 * c))) ^ 3 ≤ 1 := pow_le_one₀ hd0 hd1
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  calc ArithmeticFunction.vonMangoldt (n : ℕ) / ((n : ℕ) : ℝ)
        * Real.exp (-(Real.pi * x * ((n : ℕ) : ℝ) ^ 2)) * (1 - ((n : ℕ) : ℝ) ^ (-(2 * c))) ^ 3
      ≤ ArithmeticFunction.vonMangoldt (n : ℕ) / ((n : ℕ) : ℝ) * 1 * 1 := by
        gcongr
    _ = _ := by ring

theorem summable_atomicEnergyTerm {x c : ℝ} (hx : 0 ≤ x) (hc : 0 ≤ c) :
    Summable (atomicEnergyTerm x c) :=
  (RHTower.summable_routePPrimeGammaBaseCubicWeight.subtype _).of_nonneg_of_le
    (atomicEnergyTerm_nonneg x c) (atomicEnergyTerm_le_base hx hc)

/-- **(CAGC.6).**  The atomic energy is at most the Route-P base budget, which is below one. -/
theorem tsum_atomicEnergyTerm_le {x c : ℝ} (hx : 0 ≤ x) (hc : 0 ≤ c) :
    ∑' n, atomicEnergyTerm x c n ≤ RHTower.routePPrimitiveBaseCauchyCubicTraceBudget ∧
      RHTower.routePPrimitiveBaseCauchyCubicTraceBudget < 1 := by
  refine ⟨?_, RHTower.routePPrimitiveBaseCauchyCubicTraceBudget_lt_one⟩
  rw [← RHTower.tsum_routePPrimeGammaBaseCubicWeight_eq_budget]
  have hbase_nonneg : ∀ m, 0 ≤ RHTower.routePPrimeGammaBaseCubicWeight m := fun m => by
    rw [RHTower.routePPrimeGammaBaseCubicWeight_eq_vonMangoldt, RHTower.finiteVonMangoldtRealWeight]
    rcases Nat.lt_or_ge m 2 with hm | hm
    · interval_cases m <;> simp
    · have : 0 < Real.log m := Real.log_pos (by exact_mod_cast (show 1 < m by omega))
      have : 0 ≤ ArithmeticFunction.vonMangoldt m / (m : ℝ) :=
        div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _)
      positivity
  calc ∑' n, atomicEnergyTerm x c n ≤ ∑' n : AtomLabel, RHTower.routePPrimeGammaBaseCubicWeight n :=
        (summable_atomicEnergyTerm hx hc).tsum_le_tsum (atomicEnergyTerm_le_base hx hc)
          (RHTower.summable_routePPrimeGammaBaseCubicWeight.subtype _)
    _ ≤ ∑' m, RHTower.routePPrimeGammaBaseCubicWeight m :=
        RHTower.summable_routePPrimeGammaBaseCubicWeight.tsum_subtype_le _ _ hbase_nonneg

theorem continuous_atomicFeature (x c : ℝ) (n : AtomLabel) :
    Continuous fun r : ℝ => atomicCoefficient x c n * burnolRadial (Real.log (n : ℕ)) r := by
  unfold burnolRadial
  fun_prop

theorem lintegral_atomicFeature_sq {x c : ℝ} (n : AtomLabel) :
    ∫⁻ r, ‖((atomicCoefficient x c n * burnolRadial (Real.log (n : ℕ)) r : ℝ) : ℂ)‖ₑ ^ 2
        ∂halfLineMeasure = ENNReal.ofReal (atomicEnergyTerm x c n) := by
  simp_rw [enorm_ofReal_sq, mul_pow]
  simp_rw [ENNReal.ofReal_mul (sq_nonneg (atomicCoefficient x c n))]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_burnolRadial_sq (log_pos_of_atomLabel n), ← ENNReal.ofReal_mul (sq_nonneg _),
    atomicEnergyTerm]
  congr 1
  field_simp

theorem lintegral_lintegral_atomicFeature {x c : ℝ} (hx : 0 ≤ x) (hc : 0 ≤ c) :
    ∫⁻ r, ∫⁻ n : AtomLabel, ‖((atomicCoefficient x c n * burnolRadial (Real.log (n : ℕ)) r : ℝ) :
        ℂ)‖ₑ ^ 2 ∂Measure.count ∂halfLineMeasure
      = ENNReal.ofReal (∑' n, atomicEnergyTerm x c n) := by
  have hm : Measurable (Function.uncurry fun (r : ℝ) (n : AtomLabel) =>
      ‖((atomicCoefficient x c n * burnolRadial (Real.log (n : ℕ)) r : ℝ) : ℂ)‖ₑ ^ 2) :=
    measurable_from_prod_countable_left fun n =>
      ((Complex.continuous_ofReal.comp (continuous_atomicFeature x c n)).measurable.enorm).pow_const
        2
  rw [lintegral_lintegral_swap hm.aemeasurable, lintegral_count]
  simp_rw [lintegral_atomicFeature_sq]
  exact (ENNReal.ofReal_tsum_of_nonneg (atomicEnergyTerm_nonneg x c)
    (summable_atomicEnergyTerm hx hc)).symm

/-- The atomic kernel `(r, n) ↦ a_n f_{log n}(r)`. -/
def atomicKernel {x c : ℝ} (hx : 0 ≤ x) (hc : 0 ≤ c) :
    SqIntKernel halfLineMeasure (Measure.count : Measure AtomLabel) where
  toFun r n := ((atomicCoefficient x c n * burnolRadial (Real.log (n : ℕ)) r : ℝ) : ℂ)
  measurable := measurable_from_prod_countable_left fun n =>
    (Complex.continuous_ofReal.comp (continuous_atomicFeature x c n)).measurable
  energy_lt_top := by
    rw [lintegral_lintegral_atomicFeature hx hc]
    exact ENNReal.ofReal_lt_top

/-- **(CAGC.4).**  The atomic synthesis `A_E e_n = a_n f_{log n}`. -/
def atomicSynthesis {x c : ℝ} (hx : 0 ≤ x) (hc : 0 ≤ c) :
    Lp ℂ 2 (Measure.count : Measure AtomLabel) →L[ℂ] Lp ℂ 2 halfLineMeasure :=
  (atomicKernel hx hc).op

/-- **Theorem CAGC-B.**  `A_E` is Hilbert–Schmidt. -/
theorem isHilbertSchmidt_atomicSynthesis {x c : ℝ} (hx : 0 ≤ x) (hc : 0 ≤ c) :
    ContinuousLinearMap.IsHilbertSchmidt (atomicSynthesis hx hc) :=
  (atomicKernel hx hc).isHilbertSchmidt_op

/-- **(CAGC.6).**  `‖A_E‖²_HS = ¼ ∑ Λ(n)/n · e^{-πxn²}(1 - n^{-2c})³/log³ n ≤ B_base < 1`. -/
theorem hsNormSq_atomicSynthesis {x c : ℝ} (hx : 0 ≤ x) (hc : 0 ≤ c) :
    ContinuousLinearMap.hsNormSq (atomicSynthesis hx hc) = ∑' n, atomicEnergyTerm x c n ∧
      ContinuousLinearMap.hsNormSq (atomicSynthesis hx hc)
        ≤ RHTower.routePPrimitiveBaseCauchyCubicTraceBudget ∧
      RHTower.routePPrimitiveBaseCauchyCubicTraceBudget < 1 := by
  have h : ContinuousLinearMap.hsNormSq (atomicSynthesis hx hc) = ∑' n, atomicEnergyTerm x c n := by
    rw [atomicSynthesis, SqIntKernel.hsNormSq_op, SqIntKernel.energy]
    change (∫⁻ r, ∫⁻ n : AtomLabel, ‖((atomicCoefficient x c n * burnolRadial (Real.log (n : ℕ)) r :
      ℝ) : ℂ)‖ₑ ^ 2 ∂Measure.count ∂halfLineMeasure).toReal = _
    rw [lintegral_lintegral_atomicFeature hx hc,
      ENNReal.toReal_ofReal (tsum_nonneg (atomicEnergyTerm_nonneg x c))]
  refine ⟨h, ?_⟩
  rw [h]
  exact tsum_atomicEnergyTerm_le hx hc

theorem atomicEnergyTerm_eq {x c : ℝ} (hc : 0 ≤ c) (n : AtomLabel) :
    atomicEnergyTerm x c n = 1 / 4 * (ArithmeticFunction.vonMangoldt (n : ℕ) / (n : ℕ)
      * Real.exp (-(Real.pi * x * ((n : ℕ) : ℝ) ^ 2))
      * (1 - ((n : ℕ) : ℝ) ^ (-(2 * c))) ^ 3 / Real.log (n : ℕ) ^ 3) := by
  rw [atomicEnergyTerm, atomicCoefficient_sq hc (le_trans (by norm_num) n.2)]
  ring

end GaloisForLFunctions.HTGeometry
