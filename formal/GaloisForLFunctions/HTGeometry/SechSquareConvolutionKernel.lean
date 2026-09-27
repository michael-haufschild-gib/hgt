import GaloisForLFunctions.HTGeometry.SchurKernelOperator
import GaloisForLFunctions.HTGeometry.HyperbolicLevyKhintchine
import GaloisForLFunctions.HTGeometry.TwoSidedExponentialMoments
import GaloisForLFunctions.HTGeometry.ExponentialFeatureTangentSpace

/-!
# The Poisson history profile `sech²(s/2)`

The profile `h(s) = sech²(s/2) = 4e^s/(1+e^s)²` is the Gram kernel of the full Poisson history:

`h(a - b) = ∫_0^∞ u · (2e^a e^{-u e^a}) (2e^b e^{-u e^b}) du`.

This module collects its analytic properties: positivity, evenness, `h ≤ 1`, `h(s) ≤ 4e^{-|s|}`,
`|h'| ≤ h`, monotonicity on `[0, ∞)`, the Fourier transform

`∫ h(s) e^{-iξs} ds = 4π|ξ| / |sinh(πξ)|`   (`= 4` at `ξ = 0`),

and the fact that every value in `(0, 4]` is attained by the transform.  The Gram representation
makes every Schur-bounded kernel `h(ψ(y) - ψ(z))` a positive operator: its quadratic form is
`∫_0^∞ u |∫ 2e^{ψ(y)} e^{-u e^{ψ(y)}} f(y) dμ(y)|² du`.

Finally, an exponentially decaying profile `g` composed with a clock `φ` with `|φ(y) - y| ≤ De^{-y}`
differs from its translation-invariant version by a square-integrable kernel on `[0, ∞)²`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ### The profile -/

/-- The Poisson history profile `h(s) = sech²(s/2) = 4e^s/(1+e^s)²`. -/
def sechSqHalf (s : ℝ) : ℝ := 4 * Real.exp s / (1 + Real.exp s) ^ 2

theorem sechSqHalf_pos (s : ℝ) : 0 < sechSqHalf s := by
  unfold sechSqHalf; positivity

theorem sechSqHalf_neg (s : ℝ) : sechSqHalf (-s) = sechSqHalf s := by
  unfold sechSqHalf
  rw [Real.exp_neg]
  have := Real.exp_pos s
  field_simp
  ring

theorem sechSqHalf_le_one (s : ℝ) : sechSqHalf s ≤ 1 := by
  unfold sechSqHalf
  rw [div_le_one (by positivity)]
  nlinarith [sq_nonneg (1 - Real.exp s)]

theorem sechSqHalf_le_four_mul_exp_neg (s : ℝ) : sechSqHalf s ≤ 4 * Real.exp (-s) := by
  unfold sechSqHalf
  have hx := Real.exp_pos s
  rw [Real.exp_neg, div_le_iff₀ (by positivity)]
  field_simp
  nlinarith [sq_nonneg (Real.exp s)]

/-- `h(s) ≤ 4 e^{-|s|}`. -/
theorem sechSqHalf_le_exp_neg_abs (s : ℝ) : sechSqHalf s ≤ 4 * Real.exp (-|s|) := by
  rcases le_total 0 s with hs | hs
  · rw [abs_of_nonneg hs]; exact sechSqHalf_le_four_mul_exp_neg s
  · rw [abs_of_nonpos hs, ← sechSqHalf_neg]
    exact sechSqHalf_le_four_mul_exp_neg (-s)

theorem sechSqHalf_eq_cosh (s : ℝ) : sechSqHalf s = Real.cosh (s / 2) ^ (-2 : ℝ) := by
  have hc := Real.cosh_pos (s / 2)
  rw [Real.rpow_neg hc.le, Real.rpow_two, Real.cosh_eq, sechSqHalf]
  have he : Real.exp s = Real.exp (s / 2) ^ 2 := by
    rw [← Real.exp_nat_mul]; ring_nf
  have hn : Real.exp (-(s / 2)) = (Real.exp (s / 2))⁻¹ := Real.exp_neg _
  rw [he, hn]
  have := Real.exp_pos (s / 2)
  field_simp
  ring

theorem continuous_sechSqHalf : Continuous sechSqHalf :=
  (continuous_const.mul Real.continuous_exp).div (by fun_prop) fun s => by positivity

theorem measurable_sechSqHalf : Measurable sechSqHalf := continuous_sechSqHalf.measurable

theorem integrable_sechSqHalf : Integrable sechSqHalf := by
  have h := (_root_.HTGeometry.integrable_abs_pow_mul_exp_neg_abs 0 (r := 1) one_pos).const_mul 4
  refine h.mono' continuous_sechSqHalf.aestronglyMeasurable (Eventually.of_forall fun s => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (sechSqHalf_pos s)]
  simpa using sechSqHalf_le_exp_neg_abs s

/-- The first absolute moment `∫ |s| h(s) ds` is finite. -/
theorem integrable_abs_mul_sechSqHalf : Integrable fun s => |s| * sechSqHalf s := by
  have h := (_root_.HTGeometry.integrable_abs_pow_mul_exp_neg_abs 1 (r := 1) one_pos).const_mul 4
  refine h.mono' ((continuous_abs.mul continuous_sechSqHalf).aestronglyMeasurable)
    (Eventually.of_forall fun s => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_pos (sechSqHalf_pos s)]
  have := mul_le_mul_of_nonneg_left (sechSqHalf_le_exp_neg_abs s) (abs_nonneg s)
  simp only [pow_one, neg_one_mul]
  linarith

/-! ### Derivative and monotonicity -/

/-- `h'(s) = 4e^s(1 - e^s)/(1+e^s)³`. -/
def sechSqHalfDeriv (s : ℝ) : ℝ := 4 * Real.exp s * (1 - Real.exp s) / (1 + Real.exp s) ^ 3

theorem hasDerivAt_sechSqHalf (s : ℝ) : HasDerivAt sechSqHalf (sechSqHalfDeriv s) s := by
  have h1 : HasDerivAt (fun s => 4 * Real.exp s) (4 * Real.exp s) s :=
    (Real.hasDerivAt_exp s).const_mul 4
  have h2 : HasDerivAt (fun s => (1 + Real.exp s) ^ 2)
      ((2 : ℕ) * (1 + Real.exp s) ^ (2 - 1) * Real.exp s) s :=
    ((Real.hasDerivAt_exp s).const_add 1).fun_pow 2
  have h := h1.div h2 (by positivity)
  show HasDerivAt (fun y => 4 * Real.exp y / (1 + Real.exp y) ^ 2) _ s
  refine h.congr_deriv ?_
  unfold sechSqHalfDeriv
  have := Real.exp_pos s
  field_simp
  ring

/-- `|h'| ≤ h`. -/
theorem abs_sechSqHalfDeriv_le (s : ℝ) : |sechSqHalfDeriv s| ≤ sechSqHalf s := by
  have hx := Real.exp_pos s
  have hq : sechSqHalfDeriv s = sechSqHalf s * ((1 - Real.exp s) / (1 + Real.exp s)) := by
    unfold sechSqHalfDeriv sechSqHalf
    field_simp
  rw [hq, abs_mul, abs_of_pos (sechSqHalf_pos s)]
  refine mul_le_of_le_one_right (sechSqHalf_pos s).le ?_
  rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < 1 + Real.exp s), div_le_one (by linarith)]
  rw [abs_le]; constructor <;> linarith

/-- `h` is antitone on `[0, ∞)`. -/
theorem sechSqHalf_le_of_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : sechSqHalf b ≤ sechSqHalf a := by
  unfold sechSqHalf
  have hx : 1 ≤ Real.exp a := Real.one_le_exp ha
  have hxy : Real.exp a ≤ Real.exp b := Real.exp_le_exp.mpr hab
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (by nlinarith : (0 : ℝ) ≤ Real.exp a * Real.exp b - 1)]

/-! ### The Fourier transform -/

theorem norm_exp_neg_mul_I (ξ s : ℝ) :
    ‖Complex.exp (-((ξ : ℂ) * (s : ℂ)) * Complex.I)‖ = 1 := by
  rw [show -((ξ : ℂ) * (s : ℂ)) * Complex.I = ((-(ξ * s) : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- The Fourier symbol `ĥ(ξ) = ∫ h(s) e^{-iξs} ds`. -/
def sechSqHalfSymbol (ξ : ℝ) : ℂ :=
  ∫ s : ℝ, (sechSqHalf s : ℂ) * Complex.exp (-((ξ : ℂ) * (s : ℂ)) * Complex.I)

/-- **Fourier transform of `sech²(s/2)`.** -/
theorem sechSqHalfSymbol_eq (ξ : ℝ) :
    sechSqHalfSymbol ξ =
      if ξ = 0 then 4 else ((4 * Real.pi * |ξ| / |Real.sinh (Real.pi * ξ)| : ℝ) : ℂ) := by
  have hG : (fun s : ℝ => (sechSqHalf s : ℂ) * Complex.exp (-((ξ : ℂ) * (s : ℂ)) * Complex.I)) =
      fun s => (fun t : ℝ => (((Real.cosh t) ^ (-2 : ℝ) : ℝ) : ℂ) *
        Complex.exp (-(((2 * ξ : ℝ) : ℂ) * (t : ℂ)) * Complex.I)) (s / 2) := by
    funext s
    rw [sechSqHalf_eq_cosh]
    congr 2
    push_cast
    ring
  rw [sechSqHalfSymbol, hG, Measure.integral_comp_div (fun t : ℝ => (((Real.cosh t) ^ (-2 : ℝ) : ℝ) : ℂ) *
    Complex.exp (-(((2 * ξ : ℝ) : ℂ) * (t : ℂ)) * Complex.I)) 2,
    _root_.HTGeometry.transform_sech_sq]
  by_cases hξ : ξ = 0
  · subst hξ
    simp only [mul_zero, if_true]
    norm_num
  · have h2ξ : 2 * ξ ≠ 0 := mul_ne_zero two_ne_zero hξ
    rw [if_neg h2ξ, if_neg hξ, abs_two, abs_mul, abs_two]
    rw [show Real.pi * (2 * ξ) / 2 = Real.pi * ξ by ring, Complex.real_smul]
    push_cast
    ring

theorem integral_sechSqHalf : ∫ s : ℝ, sechSqHalf s = 4 := by
  have h := sechSqHalfSymbol_eq 0
  rw [if_pos rfl, sechSqHalfSymbol] at h
  simp only [Complex.ofReal_zero, zero_mul, neg_zero, Complex.exp_zero, mul_one] at h
  rw [integral_complex_ofReal] at h
  exact_mod_cast h

theorem continuous_sechSqHalfSymbol : Continuous sechSqHalfSymbol := by
  refine continuous_of_dominated (bound := sechSqHalf) (fun ξ => ?_) (fun ξ => ?_)
    integrable_sechSqHalf (Eventually.of_forall fun s => by fun_prop)
  · exact ((Complex.continuous_ofReal.comp continuous_sechSqHalf).mul
      (by fun_prop)).aestronglyMeasurable
  · refine Eventually.of_forall fun s => ?_
    rw [norm_mul, norm_exp_neg_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (sechSqHalf_pos s)]

theorem sechSqHalfSymbol_of_pos {ξ : ℝ} (hξ : 0 < ξ) :
    sechSqHalfSymbol ξ = ((4 * Real.pi * ξ / Real.sinh (Real.pi * ξ) : ℝ) : ℂ) := by
  rw [sechSqHalfSymbol_eq, if_neg hξ.ne', abs_of_pos hξ,
    abs_of_pos (Real.sinh_pos_iff.mpr (by positivity))]

theorem sq_div_four_le_sinh {x : ℝ} (hx : 0 ≤ x) : x ^ 2 / 4 ≤ Real.sinh x := by
  rw [Real.sinh_eq]
  have h1 := Real.quadratic_le_exp_of_nonneg hx
  have h2 : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  nlinarith

/-- **Every value in `(0, 4]` is a Fourier value of `h`.** -/
theorem exists_sechSqHalfSymbol_eq {c : ℝ} (hc0 : 0 < c) (hc4 : c ≤ 4) :
    ∃ ξ : ℝ, sechSqHalfSymbol ξ = c := by
  set R : ℝ := 16 / c with hR
  have hRpos : 0 < R := by positivity
  have hcont : ContinuousOn (fun ξ => (sechSqHalfSymbol ξ).re) (Icc 0 R) :=
    (Complex.continuous_re.comp continuous_sechSqHalfSymbol).continuousOn
  have h0 : (sechSqHalfSymbol 0).re = 4 := by rw [sechSqHalfSymbol_eq, if_pos rfl]; simp
  have hRval : (sechSqHalfSymbol R).re ≤ c := by
    rw [sechSqHalfSymbol_of_pos hRpos, Complex.ofReal_re]
    have hπ : 3 < Real.pi := Real.pi_gt_three
    have hx : 0 < Real.pi * R := by positivity
    have hs := sq_div_four_le_sinh hx.le
    rw [div_le_iff₀ (lt_of_lt_of_le (by positivity) hs)]
    calc 4 * Real.pi * R = 16 / (Real.pi * R) * ((Real.pi * R) ^ 2 / 4) := by
          field_simp; norm_num
      _ ≤ c * ((Real.pi * R) ^ 2 / 4) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [div_le_iff₀ hx, hR]
          field_simp
          nlinarith
      _ ≤ c * Real.sinh (Real.pi * R) := mul_le_mul_of_nonneg_left hs hc0.le
  obtain ⟨ξ, hξ, hξc⟩ := intermediate_value_Icc' hRpos.le hcont ⟨hRval, h0 ▸ hc4⟩
  refine ⟨ξ, ?_⟩
  have him : (sechSqHalfSymbol ξ).im = 0 := by
    rw [sechSqHalfSymbol_eq]
    split_ifs <;> simp
  apply Complex.ext
  · simpa using hξc
  · simpa using him

/-! ### The Gram (Laplace) representation -/

/-- The Laplace feature `2e^a e^{-u e^a}` of the Poisson history. -/
def sechLaplaceFeature (a u : ℝ) : ℝ := 2 * Real.exp a * Real.exp (-(u * Real.exp a))

theorem continuous_sechLaplaceFeature :
    Continuous fun p : ℝ × ℝ => sechLaplaceFeature p.1 p.2 := by
  unfold sechLaplaceFeature; fun_prop

theorem sechLaplace_integrand_eq (a b u : ℝ) :
    u * (sechLaplaceFeature a u * sechLaplaceFeature b u) =
      4 * Real.exp (a + b) * (u * Real.exp (-((Real.exp a + Real.exp b) * u))) := by
  unfold sechLaplaceFeature
  rw [Real.exp_add, show -((Real.exp a + Real.exp b) * u) = -(u * Real.exp a) + -(u * Real.exp b)
    by ring, Real.exp_add]
  ring

theorem integrableOn_sechLaplace (a b : ℝ) :
    IntegrableOn (fun u => u * (sechLaplaceFeature a u * sechLaplaceFeature b u)) (Ioi 0) := by
  simp_rw [sechLaplace_integrand_eq]
  exact (integrableOn_Ioi_mul_exp_neg (by positivity)).const_mul _

/-- **Gram representation.** `h(a - b) = ∫_0^∞ u (2e^a e^{-ue^a})(2e^b e^{-ue^b}) du`. -/
theorem integral_sechLaplace (a b : ℝ) :
    ∫ u in Ioi (0 : ℝ), u * (sechLaplaceFeature a u * sechLaplaceFeature b u) =
      sechSqHalf (a - b) := by
  simp_rw [sechLaplace_integrand_eq]
  rw [integral_const_mul, integral_Ioi_mul_exp_neg (by positivity), sechSqHalf, Real.exp_sub,
    Real.exp_add]
  have := Real.exp_pos a
  have := Real.exp_pos b
  field_simp
  ring

/-! ### Positivity of `h(ψ(y) - ψ(z))` kernels -/

section Positivity

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]

/-- **Quadratic form of a Gram kernel.**  For a Schur kernel `h(ψ(y) - ψ(z))`,
`⟪f, T f⟫ = ∫_0^∞ u |∫ 2e^{ψ(y)} e^{-u e^{ψ(y)}} f(y) dμ(y)|² du`. -/
theorem SchurKernel.inner_op_eq_of_sechSqHalf (k : SchurKernel μ) {ψ : α → ℝ} (hψ : Measurable ψ)
    (hk : ∀ y z, k.toFun y z = (sechSqHalf (ψ y - ψ z) : ℂ)) (f : Lp ℂ 2 μ) :
    inner ℂ f (k.op f) = ((∫ u in Ioi (0 : ℝ),
      u * ‖∫ y, (sechLaplaceFeature (ψ y) u : ℂ) * (f : α → ℂ) y ∂μ‖ ^ 2 : ℝ) : ℂ) := by
  set ν : Measure ℝ := volume.restrict (Ioi 0)
  have hf : Measurable (f : α → ℂ) := (Lp.stronglyMeasurable f).measurable
  set G : α → ℝ → ℝ := fun y u => sechLaplaceFeature (ψ y) u with hGdef
  have hGm : Measurable fun p : α × ℝ => G p.1 p.2 :=
    continuous_sechLaplaceFeature.measurable.comp ((hψ.comp measurable_fst).prodMk measurable_snd)
  set F : (α × α) × ℝ → ℂ := fun q => (starRingEnd ℂ) ((f : α → ℂ) q.1.1) * (f : α → ℂ) q.1.2 *
    ((q.2 * (G q.1.1 q.2 * G q.1.2 q.2) : ℝ) : ℂ) with hFdef
  have hFm : Measurable F := by
    refine ((Complex.continuous_conj.measurable.comp (hf.comp (measurable_fst.comp
      measurable_fst))).mul (hf.comp (measurable_snd.comp measurable_fst))).mul ?_
    refine Complex.measurable_ofReal.comp (measurable_snd.mul ?_)
    exact (hGm.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).mul
      (hGm.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  have hinner : ∀ p : α × α, ∫ u, F (p, u) ∂ν =
      (starRingEnd ℂ) ((f : α → ℂ) p.1) * k.toFun p.1 p.2 * (f : α → ℂ) p.2 := by
    intro p
    simp only [hFdef]
    rw [integral_const_mul, integral_complex_ofReal, hGdef, integral_sechLaplace, hk]
    ring
  have hnorm : ∀ p : α × α, ∫ u, ‖F (p, u)‖ ∂ν =
      ‖(starRingEnd ℂ) ((f : α → ℂ) p.1) * k.toFun p.1 p.2 * (f : α → ℂ) p.2‖ := by
    intro p
    have h1 : ∀ u ∈ Ioi (0 : ℝ), ‖F (p, u)‖ = ‖(f : α → ℂ) p.1‖ * ‖(f : α → ℂ) p.2‖ *
        (u * (G p.1 u * G p.2 u)) := by
      intro u hu
      have hG0 : 0 ≤ u * (G p.1 u * G p.2 u) := by
        have hu' : (0 : ℝ) < u := hu
        simp only [hGdef, sechLaplaceFeature]; positivity
      simp only [hFdef, norm_mul, RCLike.norm_conj, Complex.norm_real, Real.norm_eq_abs]
      rw [← abs_mul, ← abs_mul, abs_of_nonneg hG0]
    rw [setIntegral_congr_fun measurableSet_Ioi h1, integral_const_mul, hGdef,
      integral_sechLaplace, hk, norm_mul, norm_mul, RCLike.norm_conj, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (sechSqHalf_pos _)]
    ring
  have hFint : Integrable F ((μ.prod μ).prod ν) := by
    rw [integrable_prod_iff hFm.aestronglyMeasurable]
    refine ⟨Eventually.of_forall fun p => ?_, ?_⟩
    · simp only [hFdef]
      refine Integrable.const_mul ?_ _
      exact (integrableOn_sechLaplace (ψ p.1) (ψ p.2)).ofReal
    · simp_rw [hnorm]
      exact (k.integrable_triple f f).norm
  -- first order of integration: the operator form
  have hleft : ∫ q, F q ∂((μ.prod μ).prod ν) = inner ℂ f (k.op f) := by
    rw [integral_prod F hFint]
    simp_rw [hinner]
    rw [k.inner_op, integral_prod _ (k.integrable_triple f f)]
  -- second order of integration: the Gram form
  have hright : ∫ q, F q ∂((μ.prod μ).prod ν) =
      ∫ u, ((u * ‖∫ y, (G y u : ℂ) * (f : α → ℂ) y ∂μ‖ ^ 2 : ℝ) : ℂ) ∂ν := by
    rw [integral_prod F hFint]
    have hswap := integral_integral_swap (μ := μ.prod μ) (ν := ν)
      (f := fun p u => F (p, u)) hFint
    rw [hswap]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [hFdef]
    have hsplit : (fun p : α × α => (starRingEnd ℂ) ((f : α → ℂ) p.1) * (f : α → ℂ) p.2 *
        ((u * (G p.1 u * G p.2 u) : ℝ) : ℂ)) = fun p => (u : ℂ) *
          ((starRingEnd ℂ) ((G p.1 u : ℂ) * (f : α → ℂ) p.1) * ((G p.2 u : ℂ) * (f : α → ℂ) p.2)) := by
      funext p
      simp only [map_mul, Complex.conj_ofReal]
      push_cast
      ring
    rw [hsplit, integral_const_mul]
    rw [integral_prod_mul (fun y => (starRingEnd ℂ) ((G y u : ℂ) * (f : α → ℂ) y))
      (fun z => (G z u : ℂ) * (f : α → ℂ) z), integral_conj, RCLike.conj_mul]
    push_cast
    rfl
  rw [← hleft, hright, integral_complex_ofReal]

theorem SchurKernel.re_inner_op_nonneg_of_sechSqHalf (k : SchurKernel μ) {ψ : α → ℝ}
    (hψ : Measurable ψ) (hk : ∀ y z, k.toFun y z = (sechSqHalf (ψ y - ψ z) : ℂ))
    (f : Lp ℂ 2 μ) : 0 ≤ (inner ℂ f (k.op f)).re := by
  rw [k.inner_op_eq_of_sechSqHalf hψ hk f, Complex.ofReal_re]
  refine setIntegral_nonneg measurableSet_Ioi fun u hu => ?_
  have : (0 : ℝ) < u := hu
  positivity

end Positivity

/-! ### Clock perturbations are square integrable -/

theorem abs_sub_le_of_deriv_exp {g g' : ℝ → ℝ} (hg : ∀ s, HasDerivAt g (g' s) s) {M α : ℝ}
    (hM : 0 ≤ M) (hα : 0 ≤ α) (hg' : ∀ s, |g' s| ≤ M * Real.exp (-(α * |s|))) (a b : ℝ) :
    |g a - g b| ≤ M * Real.exp (α * |a - b|) * Real.exp (-(α * |b|)) * |a - b| := by
  have hbound : ∀ c ∈ uIcc b a, ‖g' c‖ ≤ M * Real.exp (α * |a - b|) * Real.exp (-(α * |b|)) := by
    intro c hc
    rw [Real.norm_eq_abs]
    refine (hg' c).trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hM
    rw [← Real.exp_add, Real.exp_le_exp]
    have hcb : |c - b| ≤ |a - b| := by
      have := Set.abs_sub_left_of_mem_uIcc hc
      exact this
    have : |b| ≤ |c| + |c - b| := by
      have := abs_sub_abs_le_abs_sub b c
      rw [abs_sub_comm] at this
      linarith
    nlinarith
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun c _ => (hg c).hasDerivWithinAt) hbound (convex_uIcc b a) left_mem_uIcc right_mem_uIcc
  simpa [Real.norm_eq_abs] using h

/-! ### Two-sided exponential integrals -/

theorem integrable_exp_neg_mul_abs_sub {β : ℝ} (hβ : 0 < β) (y : ℝ) :
    Integrable fun z : ℝ => Real.exp (-(β * |y - z|)) := by
  have h := (_root_.HTGeometry.integrable_abs_pow_mul_exp_neg_abs 0 hβ).comp_sub_left y
  refine h.congr (Eventually.of_forall fun z => ?_)
  simp [neg_mul]

theorem integral_exp_neg_mul_abs_sub {β : ℝ} (hβ : 0 < β) (y : ℝ) :
    ∫ z : ℝ, Real.exp (-(β * |y - z|)) = 2 / β := by
  have h1 := integral_sub_left_eq_self (fun s : ℝ => Real.exp (-(β * |s|))) volume y
  rw [h1]
  have h := _root_.HTGeometry.integral_abs_evenPow_mul_exp_neg_abs 0 hβ
  simp only [mul_zero, pow_zero, one_mul, Nat.factorial_zero, Nat.cast_one, zero_add, pow_one,
    neg_mul] at h
  rw [h]
  ring

/-- `∬ c e^{-β|y|} e^{-γ|y-z|} dy dz < ∞`. -/
theorem lintegral_exp_abs_mul_exp_abs_sub_lt_top {β γ c : ℝ} (hβ : 0 < β) (hγ : 0 < γ)
    (hc : 0 ≤ c) :
    ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (c * Real.exp (-(β * |p.1|)) * Real.exp (-(γ * |p.1 - p.2|)))
      ∂(volume.prod volume) < ∞ := by
  rw [lintegral_prod _ (by fun_prop : Measurable fun p : ℝ × ℝ => ENNReal.ofReal
    (c * Real.exp (-(β * |p.1|)) * Real.exp (-(γ * |p.1 - p.2|)))).aemeasurable]
  have hin : ∀ y : ℝ, ∫⁻ z, ENNReal.ofReal (c * Real.exp (-(β * |y|)) * Real.exp (-(γ * |y - z|))) =
      ENNReal.ofReal (c * Real.exp (-(β * |y|)) * (2 / γ)) := by
    intro y
    rw [← ofReal_integral_eq_lintegral_ofReal ((integrable_exp_neg_mul_abs_sub hγ y).const_mul _)
      (Eventually.of_forall fun z => by positivity), integral_const_mul,
      integral_exp_neg_mul_abs_sub hγ]
  simp_rw [hin]
  have hint : Integrable fun y : ℝ => c * Real.exp (-(β * |y|)) * (2 / γ) := by
    have h := (_root_.HTGeometry.integrable_abs_pow_mul_exp_neg_abs 0 hβ).const_mul c
    refine (h.mul_const (2 / γ)).congr (Eventually.of_forall fun y => ?_)
    simp [neg_mul]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun y => by positivity)]
  exact ENNReal.ofReal_lt_top

/-! ### Clock kernels -/

/-- **Schur bound for a clock kernel.**  If `|g(s)| ≤ M e^{-α|s|}` and `|φ(y) - y| ≤ D`, then
`∫ |g(φ(y) - φ(z))| dz ≤ M e^{2αD} · 2/α`. -/
theorem lintegral_enorm_clock_kernel_le {g : ℝ → ℝ} {M α : ℝ} (hM : 0 ≤ M) (hα : 0 < α)
    (hg : ∀ s, |g s| ≤ M * Real.exp (-(α * |s|))) {φ : ℝ → ℝ} {D : ℝ}
    (hφD : ∀ y, |φ y - y| ≤ D) (y : ℝ) :
    ∫⁻ z, ‖((g (φ y - φ z) : ℝ) : ℂ)‖ₑ ≤ ENNReal.ofReal (M * Real.exp (α * (2 * D)) * (2 / α)) := by
  have hpt : ∀ z, ‖((g (φ y - φ z) : ℝ) : ℂ)‖ₑ ≤
      ENNReal.ofReal (M * Real.exp (α * (2 * D)) * Real.exp (-(α * |y - z|))) := by
    intro z
    rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs]
    refine ENNReal.ofReal_le_ofReal ((hg _).trans ?_)
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hM
    rw [← Real.exp_add, Real.exp_le_exp]
    have h1 := hφD y
    have h2 := hφD z
    have : |y - z| ≤ |φ y - φ z| + 2 * D := by
      have := abs_sub_abs_le_abs_sub (y - z) (φ y - φ z)
      have h3 : |(y - z) - (φ y - φ z)| ≤ 2 * D := by
        calc |(y - z) - (φ y - φ z)| = |(φ z - z) - (φ y - y)| := by congr 1; ring
          _ ≤ |φ z - z| + |φ y - y| := abs_sub _ _
          _ ≤ 2 * D := by linarith
      linarith
    nlinarith
  refine (lintegral_mono hpt).trans (le_of_eq ?_)
  rw [← ofReal_integral_eq_lintegral_ofReal ((integrable_exp_neg_mul_abs_sub hα y).const_mul _)
    (Eventually.of_forall fun z => by positivity), integral_const_mul,
    integral_exp_neg_mul_abs_sub hα]

theorem lintegral_enorm_clock_kernel_le' {g : ℝ → ℝ} {M α : ℝ} (hM : 0 ≤ M) (hα : 0 < α)
    (hg : ∀ s, |g s| ≤ M * Real.exp (-(α * |s|))) {φ : ℝ → ℝ} {D : ℝ}
    (hφD : ∀ y, |φ y - y| ≤ D) (z : ℝ) :
    ∫⁻ y, ‖((g (φ y - φ z) : ℝ) : ℂ)‖ₑ ≤ ENNReal.ofReal (M * Real.exp (α * (2 * D)) * (2 / α)) := by
  have hg' : ∀ s, |g (-s)| ≤ M * Real.exp (-(α * |s|)) := fun s => by
    simpa [abs_neg] using hg (-s)
  have h := lintegral_enorm_clock_kernel_le (g := fun s => g (-s)) hM hα hg' hφD z
  simpa [neg_sub] using h

/-- **Clock perturbation is square integrable.**  Let `g` have derivative bounded by
`M e^{-α|s|}` and let `φ` satisfy `|φ(y) - y| ≤ D e^{-y}` on `[0, ∞)`.  Then
`g(φ(y) - φ(z)) - g(y - z)` is square integrable on `[0, ∞)²`: the mean value theorem bounds it by
`M e^{2αD} D (e^{-y} + e^{-z}) e^{-α|y-z|}`. -/
theorem lintegral_clock_sub_sq_lt_top {g g' : ℝ → ℝ} (hg : ∀ s, HasDerivAt g (g' s) s)
    {M α : ℝ} (hM : 0 ≤ M) (hα : 0 < α) (hg' : ∀ s, |g' s| ≤ M * Real.exp (-(α * |s|)))
    {φ : ℝ → ℝ} {D : ℝ} (hD : 0 ≤ D) (hφD : ∀ y, 0 ≤ y → |φ y - y| ≤ D * Real.exp (-y)) :
    ∫⁻ p, ‖((g (φ p.1 - φ p.2) - g (p.1 - p.2) : ℝ) : ℂ)‖ₑ ^ 2
      ∂((volume.restrict (Ici (0 : ℝ))).prod (volume.restrict (Ici (0 : ℝ)))) < ∞ := by
  set P : ℝ := M * Real.exp (α * (2 * D)) * D with hPdef
  set K : ℝ := 2 * P ^ 2 with hKdef
  have hK : 0 ≤ K := by positivity
  set B1 : ℝ × ℝ → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (K * Real.exp (-(2 * |p.1|)) * Real.exp (-((2 * α) * |p.1 - p.2|))) with hB1
  have hpt : ∀ y z, 0 ≤ y → 0 ≤ z →
      ‖((g (φ y - φ z) - g (y - z) : ℝ) : ℂ)‖ₑ ^ 2 ≤ B1 (y, z) + B1 (z, y) := by
    intro y z hy hz
    set a := φ y - φ z
    set b := y - z
    have h1 := hφD y hy
    have h2 := hφD z hz
    have hey : Real.exp (-y) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hez : Real.exp (-z) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hab : |a - b| ≤ D * (Real.exp (-y) + Real.exp (-z)) := by
      calc |a - b| = |(φ y - y) - (φ z - z)| := by congr 1; simp only [a, b]; ring
        _ ≤ |φ y - y| + |φ z - z| := abs_sub _ _
        _ ≤ _ := by linarith
    have hab2 : |a - b| ≤ 2 * D := by nlinarith
    have hmv := abs_sub_le_of_deriv_exp hg hM hα.le hg' a b
    have hbound : |g a - g b| ≤ P * Real.exp (-(α * |b|)) * (Real.exp (-y) + Real.exp (-z)) := by
      refine hmv.trans ?_
      have he : Real.exp (α * |a - b|) ≤ Real.exp (α * (2 * D)) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hab2 hα.le)
      calc M * Real.exp (α * |a - b|) * Real.exp (-(α * |b|)) * |a - b|
          ≤ M * Real.exp (α * (2 * D)) * Real.exp (-(α * |b|)) *
              (D * (Real.exp (-y) + Real.exp (-z))) := by gcongr
        _ = _ := by rw [hPdef]; ring
    have hsq : (g a - g b) ^ 2 ≤ K * Real.exp (-(2 * |y|)) * Real.exp (-((2 * α) * |y - z|)) +
        K * Real.exp (-(2 * |z|)) * Real.exp (-((2 * α) * |z - y|)) := by
      have h2' := pow_le_pow_left₀ (abs_nonneg _) hbound 2
      rw [sq_abs] at h2'
      refine h2'.trans (le_of_sub_nonneg ?_)
      have e1 : Real.exp (-(2 * |y|)) = Real.exp (-y) ^ 2 := by
        rw [abs_of_nonneg hy, ← Real.exp_nat_mul]; ring_nf
      have e2 : Real.exp (-(2 * |z|)) = Real.exp (-z) ^ 2 := by
        rw [abs_of_nonneg hz, ← Real.exp_nat_mul]; ring_nf
      have e3 : Real.exp (-((2 * α) * |y - z|)) = Real.exp (-(α * |b|)) ^ 2 := by
        rw [← Real.exp_nat_mul]; simp only [b]; ring_nf
      have e4 : Real.exp (-((2 * α) * |z - y|)) = Real.exp (-(α * |b|)) ^ 2 := by
        rw [abs_sub_comm, e3]
      rw [e1, e2, e3, e4, hKdef]
      have : 2 * P ^ 2 * Real.exp (-y) ^ 2 * Real.exp (-(α * |b|)) ^ 2 +
          2 * P ^ 2 * Real.exp (-z) ^ 2 * Real.exp (-(α * |b|)) ^ 2 -
          (P * Real.exp (-(α * |b|)) * (Real.exp (-y) + Real.exp (-z))) ^ 2 =
          (P * Real.exp (-(α * |b|)) * (Real.exp (-y) - Real.exp (-z))) ^ 2 := by ring
      rw [this]
      positivity
    rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, ← ENNReal.ofReal_pow (abs_nonneg _),
      sq_abs, hB1]
    simp only
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal hsq
  have hB1m : Measurable B1 := by rw [hB1]; fun_prop
  have hB1fin : ∫⁻ p, B1 p ∂(volume.prod volume) < ∞ :=
    lintegral_exp_abs_mul_exp_abs_sub_lt_top (by norm_num) (by positivity) hK
  have hB2fin : ∫⁻ p, B1 p.swap ∂(volume.prod volume) < ∞ := by
    rw [lintegral_prod_swap B1]; exact hB1fin
  rw [Measure.prod_restrict]
  calc ∫⁻ p in Ici 0 ×ˢ Ici 0, ‖((g (φ p.1 - φ p.2) - g (p.1 - p.2) : ℝ) : ℂ)‖ₑ ^ 2
        ∂(volume.prod volume)
      ≤ ∫⁻ p in Ici 0 ×ˢ Ici 0, (B1 p + B1 p.swap) ∂(volume.prod volume) :=
        setLIntegral_mono (hB1m.add (hB1m.comp measurable_swap)) fun p hp =>
          hpt p.1 p.2 hp.1 hp.2
    _ ≤ ∫⁻ p, (B1 p + B1 p.swap) ∂(volume.prod volume) := setLIntegral_le_lintegral _ _
    _ = ∫⁻ p, B1 p ∂(volume.prod volume) + ∫⁻ p, B1 p.swap ∂(volume.prod volume) :=
        lintegral_add_left hB1m _
    _ < ∞ := ENNReal.add_lt_top.mpr ⟨hB1fin, hB2fin⟩

/-! ### The tilted profile `j(s) = s h(s)` -/

/-- The tilted profile `j(s) = s · sech²(s/2)`, the kernel of the clock commutator. -/
def sechSqHalfTilt (s : ℝ) : ℝ := s * sechSqHalf s

theorem one_add_mul_exp_neg_le (x : ℝ) : (1 + x) * Real.exp (-x) ≤ 2 * Real.exp (-(x / 2)) := by
  have h := Real.add_one_le_exp (x / 2)
  have e : Real.exp (-x) = Real.exp (-(x / 2)) * Real.exp (-(x / 2)) := by
    rw [← Real.exp_add]; ring_nf
  rw [e]
  have hpos := Real.exp_pos (-(x / 2))
  have hinv : Real.exp (x / 2) * Real.exp (-(x / 2)) = 1 := by
    rw [← Real.exp_add]; simp
  nlinarith

theorem abs_sechSqHalfTilt_le (s : ℝ) : |sechSqHalfTilt s| ≤ 8 * Real.exp (-((1 / 2) * |s|)) := by
  rw [sechSqHalfTilt, abs_mul, abs_of_pos (sechSqHalf_pos s)]
  have h1 := mul_le_mul_of_nonneg_left (sechSqHalf_le_exp_neg_abs s) (abs_nonneg s)
  have h2 := one_add_mul_exp_neg_le |s|
  have h3 : |s| * Real.exp (-|s|) ≤ (1 + |s|) * Real.exp (-|s|) := by
    nlinarith [Real.exp_pos (-|s|)]
  calc |s| * sechSqHalf s ≤ |s| * (4 * Real.exp (-|s|)) := h1
    _ ≤ 4 * ((1 + |s|) * Real.exp (-|s|)) := by nlinarith
    _ ≤ 4 * (2 * Real.exp (-(|s| / 2))) := by gcongr
    _ = 8 * Real.exp (-((1 / 2) * |s|)) := by ring_nf

/-- The derivative `j'(s) = h(s) + s h'(s)`. -/
def sechSqHalfTiltDeriv (s : ℝ) : ℝ := sechSqHalf s + s * sechSqHalfDeriv s

theorem hasDerivAt_sechSqHalfTilt (s : ℝ) :
    HasDerivAt sechSqHalfTilt (sechSqHalfTiltDeriv s) s := by
  have h := (hasDerivAt_id' s).mul (hasDerivAt_sechSqHalf s)
  show HasDerivAt (fun y => y * sechSqHalf y) _ s
  exact h.congr_deriv (by rw [sechSqHalfTiltDeriv]; ring)

theorem abs_sechSqHalfTiltDeriv_le (s : ℝ) :
    |sechSqHalfTiltDeriv s| ≤ 8 * Real.exp (-((1 / 2) * |s|)) := by
  unfold sechSqHalfTiltDeriv
  have hd := abs_sechSqHalfDeriv_le s
  have hh := sechSqHalf_le_exp_neg_abs s
  have hpos := sechSqHalf_pos s
  have h2 := one_add_mul_exp_neg_le |s|
  calc |sechSqHalf s + s * sechSqHalfDeriv s| ≤ sechSqHalf s + |s| * sechSqHalf s := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_of_pos hpos, abs_mul]
        gcongr
    _ = (1 + |s|) * sechSqHalf s := by ring
    _ ≤ (1 + |s|) * (4 * Real.exp (-|s|)) := by gcongr
    _ = 4 * ((1 + |s|) * Real.exp (-|s|)) := by ring
    _ ≤ 4 * (2 * Real.exp (-(|s| / 2))) := by gcongr
    _ = 8 * Real.exp (-((1 / 2) * |s|)) := by ring_nf

theorem abs_sechSqHalf_le (s : ℝ) : |sechSqHalf s| ≤ 4 * Real.exp (-(1 * |s|)) := by
  rw [abs_of_pos (sechSqHalf_pos s), one_mul]; exact sechSqHalf_le_exp_neg_abs s

theorem abs_sechSqHalfDeriv_le_exp (s : ℝ) : |sechSqHalfDeriv s| ≤ 4 * Real.exp (-(1 * |s|)) :=
  (abs_sechSqHalfDeriv_le s).trans (by rw [one_mul]; exact sechSqHalf_le_exp_neg_abs s)

theorem continuous_sechSqHalfTilt : Continuous sechSqHalfTilt :=
  continuous_id.mul continuous_sechSqHalf

theorem sechSqHalfTilt_neg (s : ℝ) : sechSqHalfTilt (-s) = -sechSqHalfTilt s := by
  rw [sechSqHalfTilt, sechSqHalfTilt, sechSqHalf_neg]; ring

end

end GaloisForLFunctions.HTGeometry
