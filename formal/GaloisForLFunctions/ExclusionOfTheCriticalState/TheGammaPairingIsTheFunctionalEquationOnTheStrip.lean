import GaloisForLFunctions.ExclusionOfTheCriticalState.TheStateContinuesAcrossTheCriticalLine
import GaloisForLFunctions.RHTower.WeilLevyCoshPlasticCrossover
import GaloisForLFunctions.RHTower.XiCentralDiscBound
import GaloisForLFunctions.RHTower.WeilConeBoundaryDilationInequality
import GaloisForLFunctions.PNTPlus.ZetaConj

/-!
# On the strip the Gamma pairing is the functional equation

Writing the probe tail as transform minus head, `∫_{u<-x} F e^{pu} = L F(p) - H_x(p)`, splits the
Lévy pairing on the strip `|Re p| < ½`:

  `Γ F(p) = L F(p) · (2θ'(0) + g(p)) + J F(p)`,

with the Lévy symbol `g(p) = ∫_{x>0} ω(x)(2 - e^{-px} - e^{px}) dx` and the head term
`J F(p) = ∫_{x>0} ω(x) e^{px} H_x(p) dx`, holomorphic on all of `Re p < ½`. On the imaginary axis
`2θ'(0) + g(ir) = 2θ'(r)` (Lévy–Khintchine) and `ζ'/ζ(½+ir) + ζ'/ζ(½-ir) = -2θ'(r)`; by the identity
theorem the symbol is the functional equation of `ζ` on the whole strip,

  `2θ'(0) + g(p) = -(ζ'/ζ(½+p) + ζ'/ζ(½-p))`.

Hence `Γ F(p) = -L F(p)(ζ'/ζ(½+p) + ζ'/ζ(½-p)) + J F(p)`: the archimedean pairing of a profile with a
probe is the reflected Euler term plus a head term that sees `F` only on `(-x, 0)`.
-/

noncomputable section
open MeasureTheory Set Filter Zeta23 Complex Metric Topology
open scoped ComplexConjugate

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-- Holomorphy of a set integral whose integrand is locally bounded on the set. -/
theorem differentiableOn_setIntegral_of_locally_bounded {s : Set ℝ} (hs : MeasurableSet s)
    {U : Set ℂ} (hU : IsOpen U) {f : ℝ → ℂ → ℂ} (hf : ∀ u, DifferentiableOn ℂ (f u) U)
    (hmeas : ∀ z ∈ U, AEStronglyMeasurable (fun u => f u z) (volume.restrict s))
    (hbound : ∀ z₀ ∈ U, ∃ r > 0, closedBall z₀ r ⊆ U ∧ ∃ g : ℝ → ℝ, IntegrableOn g s ∧
      ∀ u ∈ s, ∀ z ∈ closedBall z₀ r, ‖f u z‖ ≤ g u) :
    DifferentiableOn ℂ (fun z => ∫ u in s, f u z) U := by
  have h := differentiableOn_integral_of_locally_bounded (ν := volume)
    (F := fun u z => s.indicator (fun u => f u z) u) hU ?_ ?_ ?_
  · exact h.congr fun z _ => (integral_indicator hs).symm
  · intro u
    by_cases hu : u ∈ s
    · exact (hf u).congr fun z _ => Set.indicator_of_mem hu _
    · exact (differentiableOn_const (0 : ℂ)).congr fun z _ => Set.indicator_of_notMem hu _
  · intro z hz
    exact (aestronglyMeasurable_indicator_iff hs).mpr (hmeas z hz)
  · intro z₀ hz₀
    obtain ⟨r, hr, hsub, g, hg, hgb⟩ := hbound z₀ hz₀
    refine ⟨r, hr, hsub, s.indicator g, (integrable_indicator_iff hs).mpr hg, fun u z hz => ?_⟩
    by_cases hu : u ∈ s
    · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu]; exact hgb u hu z hz
    · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu, norm_zero]

theorem re_mem_of_mem_closedBall {z z₀ : ℂ} {r : ℝ} (hz : z ∈ closedBall z₀ r) :
    z.re ≤ z₀.re + r ∧ z₀.re - r ≤ z.re := by
  rw [mem_closedBall, dist_eq_norm] at hz
  have h := abs_le.mp ((Complex.abs_re_le_norm (z - z₀)).trans hz)
  simp only [Complex.sub_re] at h
  constructor <;> linarith [h.1, h.2]

/-! ### The head transform -/

/-- The head transform `H_x(p) = ∫_{u ≥ -x} e^{pu} F(u) du`; for `F` supported on `u < 0` it sees
only `(-x, 0)` and is entire in `p`. -/
def levyHead (F : ℝ → ℝ) (p : ℂ) (x : ℝ) : ℂ := ∫ u : ℝ in Ici (-x), cexp (p * u) * (F u : ℂ)

theorem stronglyMeasurable_levyHead {F : ℝ → ℝ} (hFm : Measurable F) (p : ℂ) :
    StronglyMeasurable fun x => levyHead F p x := by
  set f : ℝ × ℝ → ℂ := fun q => if -q.1 ≤ q.2 then cexp (p * q.2) * (F q.2 : ℂ) else 0 with hf
  have hfm : Measurable f :=
    Measurable.ite (measurableSet_le measurable_fst.neg measurable_snd)
      ((by fun_prop : Measurable fun q : ℝ × ℝ => cexp (p * q.2)).mul
        (Complex.measurable_ofReal.comp (hFm.comp measurable_snd))) measurable_const
  have h := hfm.stronglyMeasurable.integral_prod_right' (ν := volume)
  convert h using 1
  funext x
  unfold levyHead
  rw [← integral_indicator measurableSet_Ici]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [Set.indicator, Set.mem_Ici, hf]

theorem differentiable_levyHead {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) (x : ℝ) :
    Differentiable ℂ fun p => levyHead F p x := by
  have h := differentiableOn_setIntegral_of_locally_bounded (s := Ici (-x)) measurableSet_Ici
    isOpen_univ (f := fun (u : ℝ) (p : ℂ) => cexp (p * u) * (F u : ℂ))
    (fun u => (by fun_prop : Differentiable ℂ fun p : ℂ =>
      cexp (p * u) * (F u : ℂ)).differentiableOn)
    (fun p _ => ((by fun_prop : Continuous fun u : ℝ => cexp (p * u)).measurable.mul
      (Complex.measurable_ofReal.comp hF.meas)).aestronglyMeasurable) ?_
  · exact differentiableOn_univ.mp h
  · intro z₀ _
    refine ⟨1, one_pos, subset_univ _, fun u => |F u| * Real.exp ((‖z₀‖ + 1) * |x|),
      (hF.integrable.abs.mul_const _).integrableOn, fun u hu z hz => ?_⟩
    have hu' : -x ≤ u := hu
    have hz' : |z.re| ≤ ‖z₀‖ + 1 :=
      (Complex.abs_re_le_norm z).trans (_root_.norm_le_of_mem_closedBall hz)
    rw [norm_mul, norm_cexp_mul_ofReal, Complex.norm_real, Real.norm_eq_abs, mul_comm]
    rcases lt_or_ge u 0 with h0 | h0
    · refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (abs_nonneg _)
      have h1 : z.re * u ≤ |z.re| * |u| := by rw [← abs_mul]; exact le_abs_self _
      have h2 : |u| ≤ |x| := by rw [abs_of_neg h0]; linarith [le_abs_self x]
      exact h1.trans (mul_le_mul hz' h2 (abs_nonneg _) (by positivity))
    · simp [hF.support u h0]

/-- `|e^{px} H_x(p)| ≤ e^{σx} ∫_{-x}^0 |F|` for `Re p ≤ σ`, `σ ≥ 0`. -/
theorem norm_cexp_mul_levyHead_le {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {p : ℂ}
    {σ : ℝ} (hσ : 0 ≤ σ) (hp : p.re ≤ σ) (x : ℝ) :
    ‖cexp (p * x) * levyHead F p x‖ ≤ Real.exp (σ * x) * ∫ u in Ici (-x), |F u| := by
  unfold levyHead
  rw [← integral_const_mul, ← integral_const_mul]
  refine norm_integral_le_of_norm_le (hF.integrable.abs.integrableOn.const_mul _)
    ((ae_restrict_iff' measurableSet_Ici).mpr (Eventually.of_forall fun u hu => ?_))
  have hu' : -x ≤ u := hu
  rw [norm_mul, norm_mul, norm_cexp_mul_ofReal, norm_cexp_mul_ofReal, Complex.norm_real,
    Real.norm_eq_abs, ← mul_assoc, ← Real.exp_add]
  rcases lt_or_ge u 0 with h0 | h0
  · refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (abs_nonneg _)
    nlinarith [mul_nonneg (sub_nonneg.mpr hp) (by linarith : (0 : ℝ) ≤ x + u),
      mul_nonneg hσ (by linarith : (0 : ℝ) ≤ -u)]
  · simp [hF.support u h0]

/-! ### The Lévy symbol -/

/-- The archimedean Lévy symbol `g(p) = ∫_{x>0} ω(x)(2 - e^{-px} - e^{px}) dx`. -/
def levySymbol (p : ℂ) : ℂ :=
  ∫ x in Ioi (0 : ℝ), (archLevyDensity x : ℂ) * (2 - cexp (-(p * x)) - cexp (p * x))

theorem norm_two_sub_cexp_le_near {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖(2 : ℂ) - cexp (-z) - cexp z‖ ≤ 4 * ‖z‖ := by
  have h1 := Complex.norm_exp_sub_one_le hz
  have h2 := Complex.norm_exp_sub_one_le (x := -z) (by rwa [norm_neg])
  rw [norm_neg] at h2
  calc ‖(2 : ℂ) - cexp (-z) - cexp z‖ = ‖-(cexp (-z) - 1) - (cexp z - 1)‖ := by congr 1; ring
    _ ≤ ‖cexp (-z) - 1‖ + ‖cexp z - 1‖ := by
        refine (norm_sub_le _ _).trans ?_; rw [norm_neg]
    _ ≤ 4 * ‖z‖ := by linarith

theorem norm_two_sub_cexp_le_far (z : ℂ) {x : ℝ} (hx : 0 ≤ x) {σ : ℝ} (hz : |z.re| ≤ σ) :
    ‖(2 : ℂ) - cexp (-(z * x)) - cexp (z * x)‖ ≤ 2 + 2 * Real.exp (σ * x) := by
  have e1 : ‖cexp (-(z * x))‖ ≤ Real.exp (σ * x) := by
    rw [show -(z * (x : ℂ)) = (-z) * x by ring, norm_cexp_mul_ofReal, Complex.neg_re]
    exact Real.exp_le_exp.mpr
      (by nlinarith [mul_nonneg (by linarith [neg_abs_le z.re] : 0 ≤ σ + z.re) hx])
  have e2 : ‖cexp (z * x)‖ ≤ Real.exp (σ * x) := by
    rw [norm_cexp_mul_ofReal]
    exact Real.exp_le_exp.mpr
      (by nlinarith [mul_nonneg (by linarith [le_abs_self z.re] : 0 ≤ σ - z.re) hx])
  calc ‖(2 : ℂ) - cexp (-(z * x)) - cexp (z * x)‖
      ≤ ‖(2 : ℂ)‖ + ‖cexp (-(z * x))‖ + ‖cexp (z * x)‖ :=
        (norm_sub_le _ _).trans (by linarith [norm_sub_le (2 : ℂ) (cexp (-(z * x)))])
    _ ≤ 2 + 2 * Real.exp (σ * x) := by
        rw [show ‖(2 : ℂ)‖ = 2 by simp]; linarith

/-- A dominating function for the symbol integrand on `|Re z| ≤ σ < ½`, `‖z‖ ≤ P`. -/
theorem exists_levySymbol_dominator {σ P : ℝ} (hσ : σ < 1 / 2) (hP : 1 ≤ P) :
    ∃ g : ℝ → ℝ, IntegrableOn g (Ioi 0) ∧ ∀ x ∈ Ioi (0 : ℝ), ∀ z : ℂ, |z.re| ≤ σ → ‖z‖ ≤ P →
      ‖(archLevyDensity x : ℂ) * (2 - cexp (-(z * x)) - cexp (z * x))‖ ≤ g x := by
  set x₁ := 1 / P with hx₁
  have hx₁pos : 0 < x₁ := by rw [hx₁]; positivity
  have hx₁1 : x₁ ≤ 1 := by rw [hx₁, div_le_one (by linarith)]; exact hP
  set M₀ := (1 - Real.exp (-2 * x₁))⁻¹ with hM₀
  have hM₀pos : 0 < M₀ := by
    rw [hM₀]; apply inv_pos.mpr
    have h := Real.exp_lt_exp.mpr (show -2 * x₁ < 0 by linarith)
    rw [Real.exp_zero] at h
    linarith
  refine ⟨fun x => (Ioc 0 x₁).indicator (fun _ => 6 * P) x + (Ioi x₁).indicator
      (fun x => M₀ * (2 * Real.exp (-(1 / 2) * x) + 2 * Real.exp (-(1 / 2 - σ) * x))) x, ?_, ?_⟩
  · have h1 : IntegrableOn (fun _ : ℝ => 6 * P) (Ioc 0 x₁) :=
      integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    have h2 : IntegrableOn (fun x : ℝ => M₀ * (2 * Real.exp (-(1 / 2) * x) +
        2 * Real.exp (-(1 / 2 - σ) * x))) (Ioi x₁) :=
      (((exp_neg_integrableOn_Ioi x₁ (by norm_num : (0 : ℝ) < 1 / 2)).const_mul 2).add
        ((exp_neg_integrableOn_Ioi x₁ (by linarith : (0 : ℝ) < 1 / 2 - σ)).const_mul 2)).const_mul M₀
    exact ((h1.integrable_indicator measurableSet_Ioc).add
      (h2.integrable_indicator measurableSet_Ioi)).integrableOn
  · intro x hx z hzr hzP
    have hx0 : 0 < x := hx
    beta_reduce
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (archLevyDensity_pos hx0).le]
    by_cases hxx : x ≤ x₁
    · rw [Set.indicator_of_mem (show x ∈ Ioc 0 x₁ from ⟨hx0, hxx⟩),
        Set.indicator_of_notMem (show x ∉ Ioi x₁ from not_lt.mpr hxx), add_zero]
      have hω := archLevyDensity_le_near hx0 (hxx.trans hx₁1)
      have hzx : ‖z * (x : ℂ)‖ ≤ P * x := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hx0.le]
        exact mul_le_mul_of_nonneg_right hzP hx0.le
      have hPx : P * x ≤ 1 := by
        have := mul_le_mul_of_nonneg_left hxx (by linarith : (0 : ℝ) ≤ P)
        rwa [hx₁, mul_one_div_cancel (by linarith)] at this
      have hK := norm_two_sub_cexp_le_near (hzx.trans hPx)
      calc archLevyDensity x * ‖(2 : ℂ) - cexp (-(z * x)) - cexp (z * x)‖
          ≤ 3 / (2 * x) * (4 * (P * x)) :=
            mul_le_mul hω (hK.trans (by linarith)) (norm_nonneg _) (by positivity)
        _ = 6 * P := by field_simp; ring
    · have hx1' : x₁ < x := lt_of_not_ge hxx
      rw [Set.indicator_of_notMem (show x ∉ Ioc 0 x₁ from fun h => hxx h.2),
        Set.indicator_of_mem (show x ∈ Ioi x₁ from hx1'), zero_add]
      have hω : archLevyDensity x ≤ M₀ * Real.exp (-(1 / 2) * x) :=
        WeilLevyCoshCrossover.archLevyDensity_le_of_le hx₁pos hx1'.le
      have hK := norm_two_sub_cexp_le_far z hx0.le hzr
      calc archLevyDensity x * ‖(2 : ℂ) - cexp (-(z * x)) - cexp (z * x)‖
          ≤ M₀ * Real.exp (-(1 / 2) * x) * (2 + 2 * Real.exp (σ * x)) :=
            mul_le_mul hω hK (norm_nonneg _) (by positivity)
        _ = M₀ * (2 * Real.exp (-(1 / 2) * x) + 2 * Real.exp (-(1 / 2 - σ) * x)) := by
            rw [show -(1 / 2 - σ) * x = -(1 / 2) * x + σ * x by ring, Real.exp_add]; ring

/-- The Lévy symbol is holomorphic on the strip `|Re p| < ½`. -/
theorem differentiableOn_levySymbol : DifferentiableOn ℂ levySymbol {p : ℂ | |p.re| < 1 / 2} := by
  have hU : IsOpen {p : ℂ | |p.re| < 1 / 2} :=
    isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const
  refine differentiableOn_setIntegral_of_locally_bounded measurableSet_Ioi hU
    (f := fun (x : ℝ) (p : ℂ) => (archLevyDensity x : ℂ) * (2 - cexp (-(p * x)) - cexp (p * x)))
    (fun x => (by fun_prop : Differentiable ℂ fun p : ℂ =>
      (archLevyDensity x : ℂ) * (2 - cexp (-(p * x)) - cexp (p * x))).differentiableOn)
    (fun p _ => ((Complex.measurable_ofReal.comp measurable_archLevyDensity').aestronglyMeasurable).mul
      ((by fun_prop : Continuous fun x : ℝ =>
        (2 : ℂ) - cexp (-(p * x)) - cexp (p * x)).aestronglyMeasurable)) ?_
  intro z₀ hz₀
  have hz₀' : |z₀.re| < 1 / 2 := hz₀
  set r := (1 / 2 - |z₀.re|) / 2 with hr
  have hrpos : 0 < r := by rw [hr]; linarith
  set P := max 1 (‖z₀‖ + r) with hP
  obtain ⟨g, hg, hgb⟩ := exists_levySymbol_dominator (σ := |z₀.re| + r) (P := P)
    (by rw [hr]; linarith) (le_max_left _ _)
  have hball : ∀ z ∈ closedBall z₀ r, |z.re| ≤ |z₀.re| + r ∧ ‖z‖ ≤ P := by
    intro z hz
    obtain ⟨h1, h2⟩ := re_mem_of_mem_closedBall hz
    refine ⟨abs_le.mpr ⟨by linarith [neg_abs_le z₀.re], by linarith [le_abs_self z₀.re]⟩,
      (_root_.norm_le_of_mem_closedBall hz).trans (le_max_right _ _)⟩
  refine ⟨r, hrpos, fun z hz => ?_, g, hg, fun x hx z hz => hgb x hx z (hball z hz).1 (hball z hz).2⟩
  show |z.re| < 1 / 2
  have := (hball z hz).1
  rw [hr] at this; linarith

/-! ### The head term -/

/-- The head term `J F(p) = ∫_{x>0} ω(x) e^{px} H_x(p) dx`. -/
def levyHeadTerm (F : ℝ → ℝ) (p : ℂ) : ℂ :=
  ∫ x in Ioi (0 : ℝ), (archLevyDensity x : ℂ) * (cexp (p * x) * levyHead F p x)

/-- A dominating function for the head-term integrand on `Re z ≤ σ`, `0 ≤ σ < ½`. -/
theorem exists_levyHeadTerm_dominator {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {σ : ℝ}
    (hσ0 : 0 ≤ σ) (hσ : σ < 1 / 2) :
    ∃ g : ℝ → ℝ, IntegrableOn g (Ioi 0) ∧ ∀ x ∈ Ioi (0 : ℝ), ∀ z : ℂ, z.re ≤ σ →
      ‖(archLevyDensity x : ℂ) * (cexp (z * x) * levyHead F z x)‖ ≤ g x := by
  set M₂ := ∫ u, F u ^ 2 with hM₂
  set N₁ := ∫ u, |F u| with hN₁
  have hM₂0 : 0 ≤ M₂ := integral_nonneg fun u => sq_nonneg _
  have hN₁0 : 0 ≤ N₁ := integral_nonneg fun u => abs_nonneg _
  refine ⟨fun x => (Ioc 0 1).indicator
      (fun x => 3 * Real.exp σ * (M₂ + 1) / 4 * x ^ (-(1 / 2) : ℝ)) x +
      (Ioi 1).indicator (fun x => 2 * N₁ * Real.exp (-(1 / 2 - σ) * x)) x, ?_, ?_⟩
  · have h1 : IntegrableOn (fun x : ℝ => 3 * Real.exp σ * (M₂ + 1) / 4 * x ^ (-(1 / 2) : ℝ))
        (Ioc 0 1) := by
      have hrpow : IntegrableOn (fun x : ℝ => x ^ (-(1 / 2) : ℝ)) (Ioc 0 1) := by
        rw [integrableOn_Ioc_iff_integrableOn_Ioo,
          intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0 : ℝ) < 1)]
        norm_num
      exact hrpow.const_mul _
    have h2 : IntegrableOn (fun x : ℝ => 2 * N₁ * Real.exp (-(1 / 2 - σ) * x)) (Ioi 1) :=
      (exp_neg_integrableOn_Ioi 1 (by linarith : (0 : ℝ) < 1 / 2 - σ)).const_mul _
    exact ((h1.integrable_indicator measurableSet_Ioc).add
      (h2.integrable_indicator measurableSet_Ioi)).integrableOn
  · intro x hx z hz
    have hx0 : 0 < x := hx
    beta_reduce
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (archLevyDensity_pos hx0).le]
    have hH := norm_cexp_mul_levyHead_le hF hσ0 hz x
    have hI0 : 0 ≤ ∫ u in Ici (-x), |F u| := integral_nonneg fun u => abs_nonneg _
    by_cases hx1 : x ≤ 1
    · rw [Set.indicator_of_mem (show x ∈ Ioc 0 1 from ⟨hx0, hx1⟩),
        Set.indicator_of_notMem (show x ∉ Ioi 1 from not_lt.mpr hx1), add_zero]
      have hω := archLevyDensity_le_near hx0 hx1
      have hhead := setIntegral_Ici_abs_le hF hx0
      have hb : ‖cexp (z * x) * levyHead F z x‖ ≤
          Real.exp σ * (Real.sqrt x * (M₂ + 1) / 2) :=
        hH.trans (mul_le_mul (Real.exp_le_exp.mpr (by nlinarith)) hhead hI0 (Real.exp_pos _).le)
      calc archLevyDensity x * ‖cexp (z * x) * levyHead F z x‖
          ≤ 3 / (2 * x) * (Real.exp σ * (Real.sqrt x * (M₂ + 1) / 2)) :=
            mul_le_mul hω hb (norm_nonneg _) (by positivity)
        _ = 3 * Real.exp σ * (M₂ + 1) / 4 * x ^ (-(1 / 2) : ℝ) := by
            rw [Real.rpow_neg hx0.le, ← Real.sqrt_eq_rpow]
            set s := Real.sqrt x with hsdef
            have hs2 : x = s ^ 2 := (Real.sq_sqrt hx0.le).symm
            have hsp : 0 < s := Real.sqrt_pos.mpr hx0
            clear_value s
            subst hs2
            field_simp
            ring
    · have hx1' : 1 < x := lt_of_not_ge hx1
      rw [Set.indicator_of_notMem (show x ∉ Ioc 0 1 from fun h => hx1 h.2),
        Set.indicator_of_mem (show x ∈ Ioi 1 from hx1'), zero_add]
      have hω := archLevyDensity_le_far hx1'.le
      have hN : (∫ u in Ici (-x), |F u|) ≤ N₁ :=
        setIntegral_le_integral hF.integrable.abs (Eventually.of_forall fun u => abs_nonneg _)
      calc archLevyDensity x * ‖cexp (z * x) * levyHead F z x‖
          ≤ 2 * Real.exp (-(x / 2)) * (Real.exp (σ * x) * N₁) :=
            mul_le_mul hω (hH.trans (mul_le_mul_of_nonneg_left hN (Real.exp_pos _).le))
              (norm_nonneg _) (by positivity)
        _ = 2 * N₁ * Real.exp (-(1 / 2 - σ) * x) := by
            rw [show -(1 / 2 - σ) * x = -(x / 2) + σ * x by ring, Real.exp_add]; ring

/-- The head term is holomorphic on `Re p < ½`. -/
theorem differentiableOn_levyHeadTerm {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) :
    DifferentiableOn ℂ (levyHeadTerm F) {p : ℂ | p.re < 1 / 2} := by
  intro p₀ hp₀
  have hp₀' : p₀.re < 1 / 2 := hp₀
  set σ := (max p₀.re 0 + 1 / 2) / 2 with hσdef
  have hσ0 : 0 ≤ σ := by rw [hσdef]; have := le_max_right p₀.re 0; linarith
  have hσ : σ < 1 / 2 := by
    rw [hσdef]; have := max_lt hp₀' (by norm_num : (0 : ℝ) < 1 / 2); linarith
  have hσp : p₀.re < σ := by rw [hσdef]; have := le_max_left p₀.re 0; linarith
  have hU : IsOpen {p : ℂ | p.re < σ} := isOpen_lt Complex.continuous_re continuous_const
  obtain ⟨g, hg, hgb⟩ := exists_levyHeadTerm_dominator hF hσ0 hσ
  have hd : DifferentiableOn ℂ (levyHeadTerm F) {p : ℂ | p.re < σ} := by
    refine differentiableOn_setIntegral_of_locally_bounded measurableSet_Ioi hU
      (f := fun (x : ℝ) (p : ℂ) => (archLevyDensity x : ℂ) * (cexp (p * x) * levyHead F p x))
      (fun x => (((by fun_prop : Differentiable ℂ fun p : ℂ => cexp (p * x)).mul
        (differentiable_levyHead hF x)).const_mul _).differentiableOn) ?_ ?_
    · intro p _
      exact ((Complex.measurable_ofReal.comp measurable_archLevyDensity').aestronglyMeasurable).mul
        (((by fun_prop : Continuous fun x : ℝ => cexp (p * x)).aestronglyMeasurable).mul
          (stronglyMeasurable_levyHead hF.meas p).aestronglyMeasurable)
    · intro z₀ hz₀
      have hz₀' : z₀.re < σ := hz₀
      refine ⟨(σ - z₀.re) / 2, by linarith, fun z hz => ?_, g, hg,
        fun x hx z hz => hgb x hx z ?_⟩
      · show z.re < σ; have := (re_mem_of_mem_closedBall hz).1; linarith
      · have := (re_mem_of_mem_closedBall hz).1; linarith
  exact (hd.differentiableAt (hU.mem_nhds hσp)).differentiableWithinAt

/-! ### The strip decomposition -/

/-- **Strip decomposition.** On `|Re p| < ½`: `Γ F(p) = L F(p)(2θ'(0) + g(p)) + J F(p)`. -/
theorem levyGamma_eq_symbol_add_head {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {p : ℂ}
    (hp : |p.re| < 1 / 2) :
    levyGamma F p = negativeHalfLineLaplace (cx F) p *
      (2 * (gammaHardyPhaseRate 0 : ℂ) + levySymbol p) + levyHeadTerm F p := by
  have hp4 : -4 < p.re := by have := neg_abs_le p.re; linarith
  obtain ⟨g₁, hg₁, hb₁⟩ := exists_levySymbol_dominator (σ := |p.re|) (P := max 1 ‖p‖) hp
    (le_max_left _ _)
  have hI₁ : IntegrableOn (fun x : ℝ => (archLevyDensity x : ℂ) *
      (2 - cexp (-(p * x)) - cexp (p * x))) (Ioi 0) :=
    hg₁.mono' (((Complex.measurable_ofReal.comp measurable_archLevyDensity').aestronglyMeasurable).mul
      ((by fun_prop : Continuous fun x : ℝ =>
        (2 : ℂ) - cexp (-(p * x)) - cexp (p * x)).aestronglyMeasurable))
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx =>
        hb₁ x hx p le_rfl (le_max_right _ _)))
  obtain ⟨g₂, hg₂, hb₂⟩ := exists_levyHeadTerm_dominator hF (σ := |p.re|) (abs_nonneg _) hp
  have hI₂ : IntegrableOn (fun x : ℝ => (archLevyDensity x : ℂ) *
      (cexp (p * x) * levyHead F p x)) (Ioi 0) :=
    hg₂.mono' (((Complex.measurable_ofReal.comp measurable_archLevyDensity').aestronglyMeasurable).mul
      (((by fun_prop : Continuous fun x : ℝ => cexp (p * x)).aestronglyMeasurable).mul
        (stronglyMeasurable_levyHead hF.meas p).aestronglyMeasurable))
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx =>
        hb₂ x hx p (le_abs_self _)))
  have hpt : ∀ x, (archLevyDensity x : ℂ) * levyKernel F p x =
      negativeHalfLineLaplace (cx F) p *
        ((archLevyDensity x : ℂ) * (2 - cexp (-(p * x)) - cexp (p * x))) +
      (archLevyDensity x : ℂ) * (cexp (p * x) * levyHead F p x) := by
    intro x
    have hs := laplace_eq_levyTail_add hF hp4 x
    have ht : levyTail F p x = negativeHalfLineLaplace (cx F) p - levyHead F p x := by
      unfold levyHead; rw [hs]; ring
    unfold levyKernel
    rw [ht]
    ring
  unfold levyGamma levyIntegrand levySymbol levyHeadTerm
  rw [integral_indicator measurableSet_Ioi]
  simp_rw [hpt]
  rw [integral_add (hI₁.const_mul _) hI₂, integral_const_mul]
  ring

/-! ### The symbol is the functional equation -/

/-- On the imaginary axis the symbol is the Lévy–Khintchine integral of the phase rate:
`2θ'(0) + g(ir) = 2θ'(r)`. -/
theorem levySymbol_mul_I (r : ℝ) :
    2 * (gammaHardyPhaseRate 0 : ℂ) + levySymbol ((r : ℂ) * I) = 2 * (gammaHardyPhaseRate r : ℂ) := by
  have hLK := gammaHardyPhaseRate_sub_zero_eq_integral r
  have hsym : levySymbol ((r : ℂ) * I) =
      ((∫ x in Ioi (0 : ℝ), 2 * (archLevyDensity x * (1 - Real.cos (r * x))) : ℝ) : ℂ) := by
    unfold levySymbol
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    have h1 : cexp ((r : ℂ) * I * x) = cexp (((r * x : ℝ) : ℂ) * I) := by congr 1; push_cast; ring
    have h2 : cexp (-((r : ℂ) * I * x)) = cexp (((-(r * x) : ℝ) : ℂ) * I) := by
      congr 1; push_cast; ring
    simp only
    rw [h1, h2, Complex.exp_mul_I, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  rw [hsym, integral_const_mul, ← hLK]
  push_cast
  ring

/-- On the critical line `ζ'/ζ(½+ir) + ζ'/ζ(½-ir) = -2θ'(r)`. -/
theorem logDeriv_zeta_add_conj_line {r : ℝ} (hζ : riemannZeta (1 / 2 + (r : ℂ) * I) ≠ 0) :
    deriv riemannZeta (1 / 2 + (r : ℂ) * I) / riemannZeta (1 / 2 + (r : ℂ) * I) +
      deriv riemannZeta (1 / 2 - (r : ℂ) * I) / riemannZeta (1 / 2 - (r : ℂ) * I) =
        -2 * (gammaHardyPhaseRate r : ℂ) := by
  have hl : linePt r = 1 / 2 + (r : ℂ) * I := by unfold linePt; push_cast; ring
  have h1 := WeilBoundaryDilation.logDeriv_zeta_line (t := r) (by rwa [hl])
  rw [hl] at h1
  have hc : (1 / 2 - (r : ℂ) * I) = conj (1 / 2 + (r : ℂ) * I) := by
    apply Complex.ext <;> simp
  have h2 := logDerivZeta_conj (1 / 2 + (r : ℂ) * I)
  simp only [Pi.div_apply] at h2
  rw [hc, h2, h1]
  simp [map_sub, map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

/-- **The Lévy symbol is the functional equation.** On `|Re p| < ½`, off the zeros,
`2θ'(0) + g(p) = -(ζ'/ζ(½+p) + ζ'/ζ(½-p))`. -/
theorem levySymbol_eq_neg_logDeriv {p : ℂ} (hp : |p.re| < 1 / 2)
    (hζ₁ : riemannZeta (1 / 2 + p) ≠ 0) (hζ₂ : riemannZeta (1 / 2 - p) ≠ 0) :
    2 * (gammaHardyPhaseRate 0 : ℂ) + levySymbol p =
      -(deriv riemannZeta (1 / 2 + p) / riemannZeta (1 / 2 + p) +
        deriv riemannZeta (1 / 2 - p) / riemannZeta (1 / 2 - p)) := by
  set S := {p : ℂ | |p.re| < 1 / 2} with hS
  have hSo : IsOpen S := isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const
  have hSeq : S = {p : ℂ | -(1 / 2) < p.re} ∩ {p : ℂ | p.re < 1 / 2} := by
    ext q; simp only [hS, Set.mem_setOf_eq, Set.mem_inter_iff, abs_lt]
  have hSc : IsPreconnected S := by
    rw [hSeq]
    exact ((convex_halfSpace_re_gt (-(1 / 2))).inter (convex_halfSpace_re_lt (1 / 2))).isPreconnected
  have hne1 : ∀ q ∈ S, (1 : ℂ) / 2 + q ≠ 1 ∧ (1 : ℂ) / 2 - q ≠ 1 := by
    intro q hq
    have hq' : |q.re| < 1 / 2 := hq
    have h := abs_lt.mp hq'
    refine ⟨fun h1 => ?_, fun h1 => ?_⟩ <;>
    · have := congrArg Complex.re h1; simp at this; linarith
  -- the cleared identity, holomorphic on the strip
  set Y : ℂ → ℂ := fun q => riemannZeta (1 / 2 + q) * riemannZeta (1 / 2 - q) *
      (2 * (gammaHardyPhaseRate 0 : ℂ) + levySymbol q) +
      deriv riemannZeta (1 / 2 + q) * riemannZeta (1 / 2 - q) +
      riemannZeta (1 / 2 + q) * deriv riemannZeta (1 / 2 - q) with hY
  have hYd : DifferentiableOn ℂ Y S := by
    intro q hq
    obtain ⟨h1, h2⟩ := hne1 q hq
    have hz1 : DifferentiableAt ℂ (fun q : ℂ => riemannZeta (1 / 2 + q)) q :=
      differentiableAt_zeta_shift h1
    have hd1 : DifferentiableAt ℂ (fun q : ℂ => deriv riemannZeta (1 / 2 + q)) q :=
      differentiableAt_deriv_zeta_shift h1
    have hz2 : DifferentiableAt ℂ (fun q : ℂ => riemannZeta (1 / 2 - q)) q :=
      (HTGeometry.analyticAt_riemannZeta h2).differentiableAt.comp q
        ((differentiableAt_const _).sub differentiableAt_id)
    have hd2 : DifferentiableAt ℂ (fun q : ℂ => deriv riemannZeta (1 / 2 - q)) q :=
      (HTGeometry.analyticAt_riemannZeta h2).deriv.differentiableAt.comp q
        ((differentiableAt_const _).sub differentiableAt_id)
    have hs : DifferentiableAt ℂ levySymbol q :=
      differentiableOn_levySymbol.differentiableAt (hSo.mem_nhds hq)
    exact ((((hz1.mul hz2).mul ((differentiableAt_const _).add hs)).add
      (hd1.mul hz2)).add (hz1.mul hd2)).differentiableWithinAt
  -- it vanishes on the imaginary axis near `0`
  have hline : ∀ r : ℝ, |r| < 1 → Y ((r : ℂ) * I) = 0 := by
    intro r hr
    have hnear : ∀ s : ℂ, s.re = 1 / 2 → ‖s - 1 / 2‖ ≤ 1 → riemannZeta s ≠ 0 := by
      intro s hs hd
      refine riemannZeta_ne_zero_of_dist_le_one (fun h => ?_) (by rw [hs]; norm_num) hd
      rw [h] at hs; norm_num at hs
    have hz1 : riemannZeta (1 / 2 + (r : ℂ) * I) ≠ 0 :=
      hnear _ (by simp) (by simp [Complex.norm_real, Real.norm_eq_abs]; linarith)
    have hz2 : riemannZeta (1 / 2 - (r : ℂ) * I) ≠ 0 :=
      hnear _ (by simp) (by
        rw [show (1 : ℂ) / 2 - (r : ℂ) * I - 1 / 2 = -((r : ℂ) * I) by ring, norm_neg]
        simp [Complex.norm_real, Real.norm_eq_abs]; linarith)
    have hA := levySymbol_mul_I r
    have hB := logDeriv_zeta_add_conj_line hz1
    rw [div_add_div _ _ hz1 hz2, div_eq_iff (mul_ne_zero hz1 hz2)] at hB
    simp only [hY]
    rw [hA]
    linear_combination hB
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), Y z = 0 := by
    have ht : Tendsto (fun r : ℝ => (r : ℂ) * I) (𝓝[≠] 0) (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have h : Tendsto (fun r : ℝ => (r : ℂ) * I) (𝓝 0) (𝓝 (((0 : ℝ) : ℂ) * I)) :=
          (Complex.continuous_ofReal.tendsto 0).mul_const I
        simp only [Complex.ofReal_zero, zero_mul] at h
        exact h.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with r hr
        exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hr) I_ne_zero
    have hev : ∀ᶠ r : ℝ in 𝓝[≠] (0 : ℝ), Y ((r : ℂ) * I) = 0 := by
      have h : ∀ᶠ r : ℝ in 𝓝 (0 : ℝ), Y ((r : ℂ) * I) = 0 := by
        filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with r hr
        rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hr
        exact hline r hr
      exact h.filter_mono nhdsWithin_le_nhds
    exact ht.frequently hev.frequently
  have h0S : (0 : ℂ) ∈ S := by show |(0 : ℂ).re| < 1 / 2; norm_num
  have hYp := (hYd.analyticOnNhd hSo).eqOn_zero_of_preconnected_of_frequently_eq_zero hSc h0S
    hfreq (show p ∈ S from hp)
  simp only [hY, Pi.zero_apply] at hYp
  rw [div_add_div _ _ hζ₁ hζ₂, ← neg_div, eq_div_iff (mul_ne_zero hζ₁ hζ₂)]
  linear_combination hYp

/-- **The Gamma pairing on the strip.** For `|Re p| < ½` off the zeros,
`Γ F(p) = -L F(p)(ζ'/ζ(½+p) + ζ'/ζ(½-p)) + J F(p)`. -/
theorem levyGamma_eq_reflected_euler {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) {p : ℂ}
    (hp : |p.re| < 1 / 2) (hζ₁ : riemannZeta (1 / 2 + p) ≠ 0) (hζ₂ : riemannZeta (1 / 2 - p) ≠ 0) :
    levyGamma F p = -(negativeHalfLineLaplace (cx F) p *
      (deriv riemannZeta (1 / 2 + p) / riemannZeta (1 / 2 + p) +
        deriv riemannZeta (1 / 2 - p) / riemannZeta (1 / 2 - p))) + levyHeadTerm F p := by
  rw [levyGamma_eq_symbol_add_head hF hp, levySymbol_eq_neg_logDeriv hp hζ₁ hζ₂]
  ring

end GaloisForLFunctions.ExclusionOfTheCriticalState
