import GaloisForLFunctions.ArithmeticInnerFunctionTheory.ThePoissonJensenIdentity
import GaloisForLFunctions.RHTower.Deninger.DeningerZetaLowerBound
import GaloisForLFunctions.RHTower.FermiNymanCorrelationJets

/-!
# The inner field of `ζ`

On `Re s > ½` write `E(s) = (s − 1)ζ(s)/s`, so that `|E| = |ζ|` on the critical line. The **inner field**

`I(w) = ∫ log |ζ(½ + iτ)| P_w(τ) dτ − log |E(w)|`

is the logarithm of the reciprocal modulus of the inner factor of `E` at `w`. By the Poisson–Jensen
identity it is exactly the Green potential of the right zeros, at every point `w` that is not a zero
(`hasSum_innerField`):

`I(w) = Σ_ρ m_ρ log (|ρ + w̄ − 1| / |ρ − w|)`.

So `E` has no singular inner factor, `I ≥ 0`, and one value decides the line:
`RH ⇔ I(w) = 0` at any single nonzero point `w` (`riemannHypothesis_iff_innerField_eq_zero`).
The Balazard–Saias–Yor identity is the value at `w = 1` (`innerField_one`).

The module records the two elementary inputs on the boundary: the Poisson mean of `log |s|` on the
line (`integral_log_norm_line_poisson`) and the boundary Harnack inequality comparing `P_w` with `P₁`
(`exists_poissonKernel_le_one`).
-/

open Complex Metric Filter Topology MeasureTheory Set
open scoped Real ComplexConjugate

namespace GaloisForLFunctions.ArithmeticInnerFunctionTheory

open _root_.RHTower

noncomputable section

/-! ### The boundary kernel -/

theorem halfPlanePoissonKernel_pos {w : ℂ} (hw : 1 / 2 < w.re) (τ : ℝ) :
    0 < halfPlanePoissonKernel w τ := by
  have hb : 0 < w.re - 1 / 2 := by linarith
  unfold halfPlanePoissonKernel
  positivity

theorem halfPlanePoissonKernel_one (τ : ℝ) :
    halfPlanePoissonKernel 1 τ = (2 * π)⁻¹ * (1 / (1 / 4 + τ ^ 2)) := by
  unfold halfPlanePoissonKernel
  have h : (0 : ℝ) < 1 / 4 + τ ^ 2 := by positivity
  simp only [Complex.one_re, Complex.one_im, sub_zero]
  have hπ := Real.pi_pos
  field_simp
  ring

/-- **Boundary Harnack.** `P_w` is dominated by a multiple of `P₁`. -/
theorem exists_poissonKernel_le_one {w : ℂ} (hw : 1 / 2 < w.re) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, halfPlanePoissonKernel w τ ≤ C * halfPlanePoissonKernel 1 τ := by
  have hb : 0 < w.re - 1 / 2 := by linarith
  set b : ℝ := w.re - 1 / 2 with hbdef
  set t : ℝ := w.im with ht
  set c₀ : ℝ := 2 + (1 / 4 + 2 * t ^ 2) / b ^ 2 with hc₀
  have hc₀0 : 0 ≤ c₀ := by rw [hc₀]; positivity
  refine ⟨2 * b * c₀, by positivity, fun τ => ?_⟩
  have hA : 0 < b ^ 2 + (τ - t) ^ 2 := by positivity
  have hB : (0 : ℝ) < 1 / 4 + τ ^ 2 := by positivity
  have key : 1 / 4 + τ ^ 2 ≤ c₀ * (b ^ 2 + (τ - t) ^ 2) := by
    have h1 : (1 / 4 + 2 * t ^ 2) / b ^ 2 * b ^ 2 = 1 / 4 + 2 * t ^ 2 := by field_simp
    have h2 : 0 ≤ (1 / 4 + 2 * t ^ 2) / b ^ 2 * (τ - t) ^ 2 := by positivity
    rw [hc₀]
    nlinarith [sq_nonneg (τ - 2 * t), sq_nonneg b]
  rw [halfPlanePoissonKernel_one]
  unfold halfPlanePoissonKernel
  rw [← hbdef, ← ht]
  have hπ := Real.pi_pos
  rw [div_le_iff₀ (by positivity)]
  have hrhs : 2 * b * c₀ * ((2 * π)⁻¹ * (1 / (1 / 4 + τ ^ 2))) * (π * (b ^ 2 + (τ - t) ^ 2)) =
      b * (c₀ * (b ^ 2 + (τ - t) ^ 2)) / (1 / 4 + τ ^ 2) := by
    field_simp
  rw [hrhs, le_div_iff₀ hB]
  exact mul_le_mul_of_nonneg_left key hb.le

/-! ### The Poisson mean of `log |s|` -/

theorem isHalfPlaneDatum_id : IsHalfPlaneDatum (fun z : ℂ => z) :=
  ⟨differentiable_id, 1, le_rfl, fun s _ => by nlinarith [norm_nonneg s]⟩

/-- A zero-free datum: the Poisson mean of `log |E|` is `log |E(w)|`. -/
theorem integrable_and_integral_log_of_no_right_zeros {E : ℂ → ℂ} (hE : IsHalfPlaneDatum E)
    {w : ℂ} (hw : IsCentre E w) (hz : ∀ ρ : ℂ, 1 / 2 < ρ.re → E ρ ≠ 0) :
    Integrable (fun τ : ℝ => Real.log ‖E (1 / 2 + τ * I)‖ * halfPlanePoissonKernel w τ) ∧
      ∫ τ : ℝ, Real.log ‖E (1 / 2 + τ * I)‖ * halfPlanePoissonKernel w τ = Real.log ‖E w‖ := by
  obtain ⟨hint, hsum⟩ := hasSum_poissonJensen hE hw
  have hemp : IsEmpty (RightZeros E) := ⟨fun ρ => hz ρ ρ.2.2 ρ.2.1⟩
  have h0 := hsum.unique hasSum_empty
  exact ⟨hint, by linarith⟩

/-- The Poisson mean of `log |s|` on the critical line is `log |w|`. -/
theorem integral_log_norm_line_poisson {w : ℂ} (hw : 1 / 2 < w.re) :
    Integrable (fun τ : ℝ => Real.log ‖(1 / 2 + τ * I : ℂ)‖ * halfPlanePoissonKernel w τ) ∧
      ∫ τ : ℝ, Real.log ‖(1 / 2 + τ * I : ℂ)‖ * halfPlanePoissonKernel w τ = Real.log ‖w‖ := by
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw; linarith
  refine integrable_and_integral_log_of_no_right_zeros isHalfPlaneDatum_id
    ⟨hw, hw0, 1, 1, one_pos, fun σ hσ => ?_⟩ fun ρ hρ h0 => ?_
  · have h := Complex.abs_re_le_norm ((σ : ℂ) + (w.im : ℂ) * I)
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero] at h
    rw [abs_of_pos (by linarith)] at h
    linarith
  · rw [h0] at hρ
    simp at hρ
    linarith

/-! ### `(s − 1)ζ(s)` as a datum -/

theorem isHalfPlaneDatum_zetaEntire : IsHalfPlaneDatum zetaEntire :=
  ⟨differentiable_zetaEntire, exists_norm_zetaEntire_le⟩

/-- Every nonzero point of the half-plane is a centre of `(s − 1)ζ(s)`. -/
theorem isCentre_zetaEntire {w : ℂ} (hw : 1 / 2 < w.re) (h0 : zetaEntire w ≠ 0) :
    IsCentre zetaEntire w := by
  refine ⟨hw, h0, 1 / 4, 2, by norm_num, fun σ hσ => ?_⟩
  set s : ℂ := (σ : ℂ) + (w.im : ℂ) * I with hs
  have hre : s.re = σ := by simp [hs]
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hre
    simp at hre
    linarith
  rw [zetaEntire_eq hs1, norm_mul]
  have h1 : 1 ≤ ‖s - 1‖ := by
    have h := Complex.abs_re_le_norm (s - 1)
    rw [Complex.sub_re, Complex.one_re, hre, abs_of_nonneg (by linarith)] at h
    linarith
  have h2 := norm_riemannZeta_ge_of_two_le_re (s := s) (by rw [hre]; exact hσ)
  nlinarith [norm_nonneg (riemannZeta s)]

theorem line_ne_one (τ : ℝ) : (1 / 2 + τ * I : ℂ) ≠ 1 := by
  intro h
  have := congrArg Complex.re h
  norm_num at this

/-- On the line `|s − 1| = |s|`. -/
theorem norm_line_sub_one (τ : ℝ) : ‖(1 / 2 + τ * I : ℂ) - 1‖ = ‖(1 / 2 + τ * I : ℂ)‖ := by
  have e : (1 / 2 + τ * I : ℂ) - 1 = -conj (1 / 2 + τ * I : ℂ) := by
    apply Complex.ext
    · simp; norm_num
    · simp
  rw [e, norm_neg, Complex.norm_conj]

theorem measurable_log_norm_zeta_line :
    Measurable (fun τ : ℝ => Real.log ‖riemannZeta (1 / 2 + τ * I)‖) := by
  have hc : Continuous (fun τ : ℝ => riemannZeta (1 / 2 + τ * I)) := by
    rw [continuous_iff_continuousAt]
    intro τ
    have h1 : ContinuousAt riemannZeta (1 / 2 + τ * I) :=
      (differentiableAt_riemannZeta (line_ne_one τ)).continuousAt
    exact ContinuousAt.comp (f := fun τ : ℝ => (1 / 2 + τ * I : ℂ)) h1 (by fun_prop)
  exact Real.measurable_log.comp hc.norm.measurable

/-- The boundary logarithm of `ζ` is integrable against every Poisson kernel. -/
theorem integrable_log_zeta_poisson {w : ℂ} (hw : 1 / 2 < w.re) :
    Integrable (fun τ : ℝ => Real.log ‖riemannZeta (1 / 2 + τ * I)‖ * halfPlanePoissonKernel w τ) := by
  obtain ⟨C, hC0, hC⟩ := exists_poissonKernel_le_one hw
  have h1 := (integrable_and_sum_log_le_integral_log_norm_zeta (Z := ∅) (by simp)).1
  have h2 : Integrable (fun τ : ℝ => |Real.log ‖riemannZeta (1 / 2 + τ * I)‖ / (1 / 4 + τ ^ 2)| *
      (C * (2 * π)⁻¹)) := h1.abs.mul_const _
  refine h2.mono' ?_ (Eventually.of_forall fun τ => ?_)
  · have hk : Measurable (fun τ : ℝ => halfPlanePoissonKernel w τ) := by
      unfold halfPlanePoissonKernel
      fun_prop
    exact (measurable_log_norm_zeta_line.mul hk).aestronglyMeasurable
  · have hP := hC τ
    have hP0 := (halfPlanePoissonKernel_pos hw τ).le
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hP0]
    rw [halfPlanePoissonKernel_one] at hP
    have hB : (0 : ℝ) < 1 / 4 + τ ^ 2 := by positivity
    have e : |Real.log ‖riemannZeta (1 / 2 + τ * I)‖ / (1 / 4 + τ ^ 2)| * (C * (2 * π)⁻¹) =
        |Real.log ‖riemannZeta (1 / 2 + τ * I)‖| * (C * ((2 * π)⁻¹ * (1 / (1 / 4 + τ ^ 2)))) := by
      rw [abs_div, abs_of_pos hB]
      ring
    rw [e]
    exact mul_le_mul_of_nonneg_left hP (abs_nonneg _)

theorem ae_log_zetaEntire_line :
    ∀ᵐ τ : ℝ, Real.log ‖zetaEntire (1 / 2 + τ * I)‖ =
      Real.log ‖(1 / 2 + τ * I : ℂ)‖ + Real.log ‖riemannZeta (1 / 2 + τ * I)‖ := by
  have hcount : {τ : ℝ | riemannZeta (1 / 2 + τ * I) = 0}.Countable := by
    have hinj : Function.Injective (fun τ : ℝ => (1 / 2 : ℂ) + τ * I) := by
      intro a b hab
      have := congrArg Complex.im hab
      simpa using this
    refine (countable_setOf_zetaEntire_eq_zero.preimage hinj).mono fun τ hτ => ?_
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at hτ ⊢
    rw [zetaEntire_eq (line_ne_one τ), hτ, mul_zero]
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp (hcount.measure_zero _)] with τ hτ
  have hsub : (1 / 2 : ℂ) + τ * I - 1 ≠ 0 := sub_ne_zero.mpr (line_ne_one τ)
  rw [zetaEntire_eq (line_ne_one τ), norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hsub)
    (norm_ne_zero_iff.mpr hτ), norm_line_sub_one]

/-- The Poisson mean of `log |(s − 1)ζ(s)|` splits off `log |w|`. -/
theorem integral_log_zetaEntire_poisson {w : ℂ} (hw : 1 / 2 < w.re) :
    Integrable (fun τ : ℝ => Real.log ‖zetaEntire (1 / 2 + τ * I)‖ * halfPlanePoissonKernel w τ) ∧
      ∫ τ : ℝ, Real.log ‖zetaEntire (1 / 2 + τ * I)‖ * halfPlanePoissonKernel w τ =
        (∫ τ : ℝ, Real.log ‖riemannZeta (1 / 2 + τ * I)‖ * halfPlanePoissonKernel w τ) +
          Real.log ‖w‖ := by
  obtain ⟨hL, hL0⟩ := integral_log_norm_line_poisson hw
  have hZ := integrable_log_zeta_poisson hw
  have hae : (fun τ : ℝ => Real.log ‖zetaEntire (1 / 2 + τ * I)‖ * halfPlanePoissonKernel w τ) =ᵐ[volume]
      fun τ => Real.log ‖riemannZeta (1 / 2 + τ * I)‖ * halfPlanePoissonKernel w τ +
        Real.log ‖(1 / 2 + τ * I : ℂ)‖ * halfPlanePoissonKernel w τ := by
    filter_upwards [ae_log_zetaEntire_line] with τ hτ
    rw [hτ]
    ring
  refine ⟨(hZ.add hL).congr hae.symm, ?_⟩
  rw [integral_congr_ae hae, integral_add hZ hL, hL0]

/-! ### The inner field -/

/-- The zeros of `ζ` right of the critical line. -/
abbrev ZetaRightZero := {ρ : ℂ // riemannZeta ρ = 0 ∧ 1 / 2 < ρ.re}

/-- The multiplicity of a zero of `ζ`, as a real number. -/
def zeroMult (ρ : ℂ) : ℝ := (analyticOrderNatAt riemannZeta ρ : ℝ)

/-- The inner field `I(w) = ∫ log |ζ| P_w − log |E(w)|`, `E(s) = (s − 1)ζ(s)/s`. -/
def innerField (w : ℂ) : ℝ :=
  (∫ τ : ℝ, Real.log ‖riemannZeta (1 / 2 + τ * I)‖ * halfPlanePoissonKernel w τ) + Real.log ‖w‖ -
    Real.log ‖zetaEntire w‖

theorem zetaEntire_eq_zero_iff {ρ : ℂ} : zetaEntire ρ = 0 ↔ riemannZeta ρ = 0 := by
  rcases eq_or_ne ρ 1 with rfl | hρ
  · rw [zetaEntire_eval_one]
    simp only [one_ne_zero, false_iff]
    exact riemannZeta_ne_zero_of_one_le_re (by simp)
  · rw [zetaEntire_eq hρ, mul_eq_zero]
    exact ⟨fun h => h.resolve_left (sub_ne_zero.mpr hρ), Or.inr⟩

/-- The two parametrizations of the right zeros agree. -/
def rightZerosEquiv : RightZeros zetaEntire ≃ ZetaRightZero :=
  Equiv.subtypeEquivRight fun ρ => by rw [zetaEntire_eq_zero_iff]

theorem analyticOrderNatAt_zetaEntire {ρ : ℂ} (hρ : ρ ≠ 1) :
    analyticOrderNatAt zetaEntire ρ = analyticOrderNatAt riemannZeta ρ := by
  simp only [analyticOrderNatAt, analyticOrderAt_zetaEntire_of_ne_one hρ]

theorem ZetaRightZero.ne_one (ρ : ZetaRightZero) : (ρ : ℂ) ≠ 1 := by
  intro h
  have h0 := ρ.2.1
  rw [h] at h0
  exact riemannZeta_ne_zero_of_one_le_re (by simp) h0

/-- **The inner field is the Green potential of the right zeros**, at every nonzero point. -/
theorem hasSum_innerField {w : ℂ} (hw : 1 / 2 < w.re) (h0 : zetaEntire w ≠ 0) :
    HasSum (fun ρ : ZetaRightZero => zeroMult ρ * greenKernel w ρ) (innerField w) := by
  obtain ⟨-, hsum⟩ := hasSum_poissonJensen isHalfPlaneDatum_zetaEntire (isCentre_zetaEntire hw h0)
  rw [(integral_log_zetaEntire_poisson hw).2] at hsum
  have ht := rightZerosEquiv.symm.hasSum_iff.mpr hsum
  have e : ((fun ρ : RightZeros zetaEntire =>
      (analyticOrderNatAt zetaEntire ρ : ℝ) * greenKernel w ρ) ∘ rightZerosEquiv.symm) =
      fun ρ : ZetaRightZero => zeroMult ρ * greenKernel w ρ := by
    funext ρ
    change (analyticOrderNatAt zetaEntire ρ : ℝ) * greenKernel w ρ = _
    rw [analyticOrderNatAt_zetaEntire ρ.ne_one, zeroMult]
  rw [e] at ht
  exact ht

theorem zeroMult_pos (ρ : ZetaRightZero) : 0 < zeroMult ρ := by
  have hE : analyticOrderAt riemannZeta ρ ≠ 0 := by
    rw [← analyticOrderAt_zetaEntire_of_ne_one ρ.ne_one,
      (differentiable_zetaEntire.analyticAt _).analyticOrderAt_ne_zero, zetaEntire_eq_zero_iff]
    exact ρ.2.1
  have hne : analyticOrderAt riemannZeta ρ ≠ ⊤ := by
    have hE' : analyticOrderAt zetaEntire ρ ≠ ⊤ := by
      refine AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected
        (fun z _ => differentiable_zetaEntire.analyticAt z) isPreconnected_univ (mem_univ (1 : ℂ))
        (mem_univ _) ?_
      rw [(differentiable_zetaEntire.analyticAt 1).analyticOrderAt_eq_zero.mpr
        (by rw [zetaEntire_eval_one]; exact one_ne_zero)]
      exact ENat.zero_ne_top
    rwa [analyticOrderAt_zetaEntire_of_ne_one ρ.ne_one] at hE'
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hne
  have hm0 : m ≠ 0 := by
    rintro rfl
    apply hE
    rw [← hm]
    rfl
  rw [zeroMult, analyticOrderNatAt, ← hm]
  simp only [ENat.toNat_coe, Nat.cast_pos]
  exact Nat.pos_of_ne_zero hm0

/-- **The inner field is nonnegative.** -/
theorem innerField_nonneg {w : ℂ} (hw : 1 / 2 < w.re) (h0 : zetaEntire w ≠ 0) :
    0 ≤ innerField w := by
  refine (hasSum_innerField hw h0).nonneg fun ρ => mul_nonneg (zeroMult_pos ρ).le ?_
  have hne : (ρ : ℂ) ≠ w := by
    intro h
    apply h0
    rw [← h, zetaEntire_eq_zero_iff]
    exact ρ.2.1
  exact (greenKernel_pos hw ρ.2.2 hne).le

/-- **One value decides the line.** At any nonzero point `w`, RH is `I(w) = 0`. -/
theorem riemannHypothesis_iff_innerField_eq_zero {w : ℂ} (hw : 1 / 2 < w.re)
    (h0 : zetaEntire w ≠ 0) : RiemannHypothesis ↔ innerField w = 0 := by
  have hsum := hasSum_innerField hw h0
  constructor
  · intro hRH
    have hemp : IsEmpty ZetaRightZero := ⟨fun ρ =>
      (riemannHypothesis_iff_riemannZeta_ne_zero_of_half_lt_re.mp hRH) ρ ρ.2.2 ρ.2.1⟩
    exact hsum.unique hasSum_empty
  · intro hI
    rw [riemannHypothesis_iff_riemannZeta_ne_zero_of_half_lt_re]
    intro ρ hρ hz
    have hne : ρ ≠ w := by
      intro h
      apply h0
      rw [← h, zetaEntire_eq_zero_iff]
      exact hz
    have hpos : 0 < zeroMult ρ * greenKernel w ρ :=
      mul_pos (zeroMult_pos ⟨ρ, hz, hρ⟩) (greenKernel_pos hw hρ hne)
    have hnn : ∀ a : ZetaRightZero, 0 ≤ zeroMult a * greenKernel w a := fun a => by
      refine mul_nonneg (zeroMult_pos a).le ?_
      have hne' : (a : ℂ) ≠ w := by
        intro h
        apply h0
        rw [← h, zetaEntire_eq_zero_iff]
        exact a.2.1
      exact (greenKernel_pos hw a.2.2 hne').le
    have hle := sum_le_hasSum ({⟨ρ, hz, hρ⟩} : Finset ZetaRightZero)
      (fun a _ => hnn a) hsum
    rw [Finset.sum_singleton, hI] at hle
    exact absurd hle (not_le.mpr hpos)

/-- A nonzero value of `ζ` at a point of the half-plane makes it a nonzero point of `E`. -/
theorem zetaEntire_ne_zero_of_zeta_ne_zero {w : ℂ} (h : riemannZeta w ≠ 0) : zetaEntire w ≠ 0 :=
  fun h0 => h (zetaEntire_eq_zero_iff.mp h0)

/-- **The inner mass.** The value of the field at `1` is the Balazard–Saias–Yor integral. -/
theorem innerField_one :
    innerField 1 = (2 * π)⁻¹ * ∫ τ : ℝ, Real.log ‖riemannZeta (1 / 2 + τ * I)‖ / (1 / 4 + τ ^ 2) := by
  rw [innerField, norm_one, Real.log_one, zetaEntire_eval_one, norm_one, Real.log_one, add_zero,
    sub_zero, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
  simp only [halfPlanePoissonKernel_one]
  ring

/-- `1` is a nonzero point of `E`. -/
theorem zetaEntire_one_ne_zero : zetaEntire 1 ≠ 0 := by
  rw [zetaEntire_eval_one]
  exact one_ne_zero

/-- The inner mass lies between `0` and `½ log (log 2π − γ)`. -/
theorem innerField_one_mem_Icc :
    0 ≤ innerField 1 ∧
      innerField 1 ≤ 1 / 2 * Real.log (Real.log (2 * π) - Real.eulerMascheroniConstant) := by
  rw [innerField_one]
  exact integral_log_norm_zeta_criticalLine_mem_Icc

end

end GaloisForLFunctions.ArithmeticInnerFunctionTheory
