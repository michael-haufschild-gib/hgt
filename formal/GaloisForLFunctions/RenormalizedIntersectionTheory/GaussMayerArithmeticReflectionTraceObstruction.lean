import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerFixedPointTrace
import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerSourceParameterHolomorphy
import GaloisForLFunctions.HTGeometry.RegularizedDeterminantTraceRecovery
import GaloisForLFunctions.RHTower.ZetaPoleSplit
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# The arithmetic reflection defect of the Mayer trace

The actual first trace is `T(w) = ζ(w) + R(w)`, with `R` holomorphic for
`Re w > -1`. Its reflected difference `T(1 - w) - T(w)` has residue `-1`
at both endpoints of the critical strip. Clearing these poles gives a
holomorphic, reflection-odd function whose endpoint values are `1` and `-1`.

Holomorphic uniqueness excludes reflection invariance on every nonempty open
subset of the strip. Differentiation at spectral parameter zero transfers
this obstruction to the full Fredholm determinant, even with a scalar
factor independent of the spectral parameter.
-/

open Complex Set Filter Topology
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RenormalizedIntersectionTheory
open MayerTrace MayerFredholm MayerParameter
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerArithmeticReflection

private def traceRegularPart (w : ℂ) : ℂ := RHTower.zetaRegularized w + traceCorrection w

/-- The holomorphic remainder after subtracting both reflected trace poles. -/
def traceReflectionRemainder (w : ℂ) : ℂ := traceRegularPart (1 - w) - traceRegularPart w

/-- The trace reflection defect multiplied by `w(w - 1)`, extended through both poles. -/
def clearedTraceReflectionDefect (w : ℂ) : ℂ :=
  w * (w - 1)* traceReflectionRemainder w + 1 - 2 * w

private theorem traceRegularPart_eq {w : ℂ} (hw : w ≠ 1) :
    traceRegularPart w = continuedTrace w - 1/(w - 1) := by
  rw [traceRegularPart, RHTower.zetaRegularized_of_ne hw, continuedTrace]
  ring

/-- The exact pole decomposition of the reflected trace difference. -/
theorem traceReflectionRemainder_eq {w : ℂ} (h0 : w ≠ 0) (h1 : w ≠ 1) :
    traceReflectionRemainder w = continuedTrace (1 - w) - continuedTrace w + 1 / w + 1 /(w - 1) := by
  have hr : 1 - w ≠ 1 := by intro he; apply h0; linear_combination -he
  rw [traceReflectionRemainder, traceRegularPart_eq hr, traceRegularPart_eq h1]
  rw [show 1 - w - 1 = -w by ring, div_neg]
  ring

theorem clearedTraceReflectionDefect_eq {w : ℂ} (h0 : w ≠ 0) (h1 : w ≠ 1) :
    clearedTraceReflectionDefect w = w * (w - 1)* (continuedTrace (1 - w) - continuedTrace w) := by
  rw [clearedTraceReflectionDefect, traceReflectionRemainder_eq h0 h1]
  field_simp
  ring

private theorem differentiableOn_traceRegularPart :
    DifferentiableOn ℂ traceRegularPart {w : ℂ | -1 < w.re} :=
  RHTower.differentiable_zetaRegularized.differentiableOn.add differentiableOn_traceCorrection

/-- The remainder is holomorphic on a strip containing both reflected poles. -/
theorem differentiableOn_traceReflectionRemainder :
    DifferentiableOn ℂ traceReflectionRemainder {w : ℂ | -1 < w.re ∧ w.re < 2} := by
  intro w hw
  have hU : IsOpen {w : ℂ | -1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hwR : -1 < (1 - w).re := by simp only [sub_re, one_re]; linarith only [hw.2]
  have hleft := (differentiableOn_traceRegularPart.differentiableAt (hU.mem_nhds hwR)).comp w
    ((differentiableAt_const (1 : ℂ)).sub differentiableAt_id)
  exact (hleft.sub (differentiableOn_traceRegularPart.differentiableAt
    (hU.mem_nhds hw.1))).differentiableWithinAt

/-- Clearing both poles extends the defect holomorphically across the closed critical strip. -/
theorem differentiableOn_clearedTraceReflectionDefect :
    DifferentiableOn ℂ clearedTraceReflectionDefect {w : ℂ | -1 < w.re ∧ w.re < 2} := by
  exact ((differentiableOn_id.mul (differentiableOn_id.sub_const 1)).mul
    differentiableOn_traceReflectionRemainder |>.add_const 1).sub
      (show DifferentiableOn ℂ (fun w : ℂ => 2 * w) _ by fun_prop)

theorem clearedTraceReflectionDefect_zero : clearedTraceReflectionDefect 0 = 1 := by
  simp only [clearedTraceReflectionDefect, zero_mul, mul_zero, zero_add, sub_zero]

theorem clearedTraceReflectionDefect_one : clearedTraceReflectionDefect 1 = -1 := by
  simp only [clearedTraceReflectionDefect, sub_self, mul_zero, zero_mul, zero_add, mul_one]
  norm_num

theorem clearedTraceReflectionDefect_reflect (w : ℂ) :
    clearedTraceReflectionDefect (1 - w) = -clearedTraceReflectionDefect w := by
  simp only [clearedTraceReflectionDefect, traceReflectionRemainder,
    show 1-(1 - w) = w by ring]
  ring

private theorem expandedStrip_open : IsOpen {w : ℂ | -1 < w.re ∧ w.re < 2} :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)

private theorem expandedStrip_preconnected :
    IsPreconnected {w : ℂ | -1 < w.re ∧ w.re < 2} := by
  have hc : Convex ℝ {w : ℂ | -1 < w.re ∧ w.re < 2} :=
    (convex_Ioo (-1 : ℝ) 2).linear_preimage Complex.reLm
  exact hc.isPreconnected

/-- Reflection carries the trace pole at one to a pole of residue `-1` at zero. -/
theorem traceReflectionDefect_residue_zero :
    Tendsto (fun w : ℂ => w * (continuedTrace (1 - w) - continuedTrace w))
      (𝓝[≠] 0) (𝓝 (-1)) := by
  have hG : ContinuousAt clearedTraceReflectionDefect 0 :=
    (differentiableOn_clearedTraceReflectionDefect.differentiableAt
      (expandedStrip_open.mem_nhds (by norm_num))).continuousAt
  have hden : Tendsto (fun w : ℂ => w - 1) (𝓝[≠] 0) (𝓝 (-1)) := by
    have hc : Continuous (fun w : ℂ => w - 1) := continuous_id.sub continuous_const
    simpa only [zero_sub] using (hc.tendsto (0 : ℂ)).mono_left nhdsWithin_le_nhds
  have hlim := (hG.tendsto.mono_left nhdsWithin_le_nhds).div hden (by norm_num)
  rw [clearedTraceReflectionDefect_zero] at hlim
  simp only [div_neg, div_one] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds (by norm_num : (0 : ℂ) ≠ 1))] with w h0 h1
  change clearedTraceReflectionDefect w/(w - 1) = _
  rw [clearedTraceReflectionDefect_eq h0 h1]
  field_simp [h0, sub_ne_zero.mpr h1]

/-- Subtracting the original trace gives residue `-1` at one as well. -/
theorem traceReflectionDefect_residue_one :
    Tendsto (fun w : ℂ => (w - 1)* (continuedTrace (1 - w) - continuedTrace w))
      (𝓝[≠] 1) (𝓝 (-1)) := by
  have hG : ContinuousAt clearedTraceReflectionDefect 1 :=
    (differentiableOn_clearedTraceReflectionDefect.differentiableAt
      (expandedStrip_open.mem_nhds (by norm_num))).continuousAt
  have hden : Tendsto (fun w : ℂ => w) (𝓝[≠] 1) (𝓝 1) := nhdsWithin_le_nhds
  have hlim := (hG.tendsto.mono_left nhdsWithin_le_nhds).div hden one_ne_zero
  rw [clearedTraceReflectionDefect_one] at hlim
  simp only [div_one] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds (by norm_num : (1 : ℂ) ≠ 0))] with w h1 h0
  change clearedTraceReflectionDefect w/w = _
  rw [clearedTraceReflectionDefect_eq h0 h1]
  have hw0 : w ≠ 0 := h0
  apply (div_eq_iff hw0).mpr
  ring

/-- No nonempty open subset of the critical strip has arithmetic trace reflection symmetry. -/
theorem exists_trace_ne_reflect_in_open {V : Set ℂ} (hVo : IsOpen V) (hV : V.Nonempty)
    (hstrip : V ⊆ {w : ℂ | 0 < w.re ∧ w.re < 1}) :
    ∃ w ∈ V, continuedTrace (1 - w) ≠ continuedTrace w := by
  by_contra! heq
  obtain ⟨w₀, hw₀⟩ := hV
  have han : AnalyticOnNhd ℂ clearedTraceReflectionDefect {w : ℂ | -1 < w.re ∧ w.re < 2} :=
    differentiableOn_clearedTraceReflectionDefect.analyticOnNhd expandedStrip_open
  have hsub : V ⊆ {w : ℂ | -1 < w.re ∧ w.re < 2} := by
    intro w hw
    have h := hstrip hw
    constructor <;> linarith only [h.1,h.2]
  have hnear : clearedTraceReflectionDefect =ᶠ[𝓝 w₀] 0 := by
    filter_upwards [hVo.mem_nhds hw₀] with w hw
    have h := hstrip hw
    have h0 : w ≠ 0 := by intro he; simpa only [he, zero_re, lt_self_iff_false] using h.1
    have h1 : w ≠ 1 := by intro he; simpa only [he, one_re, lt_self_iff_false] using h.2
    rw [clearedTraceReflectionDefect_eq h0 h1, heq w hw, sub_self, mul_zero]
    rfl
  -- Local trace symmetry would force the cleared defect to vanish at its nonzero endpoint.
  have hall := han.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
    expandedStrip_preconnected (hsub hw₀) hnear
  have hz := hall (by norm_num : (0 : ℂ) ∈ {w : ℂ | -1 < w.re ∧ w.re < 2})
  rw [clearedTraceReflectionDefect_zero] at hz
  exact one_ne_zero hz

/-- The first spectral derivative of the actual Fredholm determinant recovers its trace. -/
theorem sourceDeterminant_deriv_zero {w : ℂ} (hw : 0 < w.re) :
    deriv (sourceDeterminant w) 0 = -continuedTrace w := by
  have he : sourceDeterminant w = completedDet2 (kernel w hw) (continuedTrace w) := by
    funext lam
    rw [sourceDeterminant_eq hw, determinant_eq_entireDet2 hw, continuedTrace_eq_diagonalTrace hw]
    rfl
  rw [he, deriv_completedDet2_zero (kernel_isHS hw)]

/-- Arithmetic reflection fails for the full spectral family on every nonempty open set. -/
theorem exists_spectralDeterminant_ne_reflect_in_open {V : Set ℂ} (hVo : IsOpen V)
    (hV : V.Nonempty) (hstrip : V ⊆ {w : ℂ | 0 < w.re ∧ w.re < 1}) :
    ∃ w ∈ V, ∃ lam : ℂ, sourceDeterminant (1 - w) lam ≠ sourceDeterminant w lam := by
  obtain ⟨w,hw,hne⟩ := exists_trace_ne_reflect_in_open hVo hV hstrip
  refine ⟨w,hw,?_⟩
  by_contra! he
  have hd := congrArg (fun f : ℂ → ℂ => deriv f 0) (funext he)
  have hr : 0 < (1 - w).re := by simp only [sub_re, one_re]; linarith only [(hstrip hw).2]
  rw [sourceDeterminant_deriv_zero hr, sourceDeterminant_deriv_zero (hstrip hw).1] at hd
  exact hne (neg_injective hd)

/-- A scalar factor independent of the spectral parameter cannot restore arithmetic reflection. -/
theorem exists_spectralDeterminant_no_scalar_reflection_in_open {V : Set ℂ} (hVo : IsOpen V)
    (hV : V.Nonempty) (hstrip : V ⊆ {w : ℂ | 0 < w.re ∧ w.re < 1}) :
    ∃ w ∈ V, ∀ c : ℂ, ∃ lam : ℂ,
      sourceDeterminant (1 - w) lam ≠ c * sourceDeterminant w lam := by
  obtain ⟨w,hw,lam,hne⟩ := exists_spectralDeterminant_ne_reflect_in_open hVo hV hstrip
  refine ⟨w,hw,fun c => ?_⟩
  by_contra! he
  have hr : 0 < (1 - w).re := by simp only [sub_re, one_re]; linarith only [(hstrip hw).2]
  -- Normalization at spectral parameter zero forces every such scalar factor to be one.
  have hz := he 0
  rw [sourceDeterminant_eq hr, sourceDeterminant_eq (hstrip hw).1,
    determinant_zero hr, determinant_zero (hstrip hw).1, mul_one] at hz
  have hAtLam := he lam
  rw [← hz, one_mul] at hAtLam
  exact hne hAtLam


/-- The fixed-point trace respects complex conjugation. -/
theorem continuedTrace_conj (w : ℂ) : continuedTrace (conj w) = conj (continuedTrace w) := by
  have hpow (x : ℝ) (hx : 0 < x) :
      (x : ℂ)^(-conj w) = conj ((x : ℂ)^(-w)) := by
    have ha : (x : ℂ).arg ≠ Real.pi := by
      rw [Complex.arg_ofReal_of_nonneg hx.le]
      exact Real.pi_ne_zero.symm
    simpa only [map_neg, Complex.conj_ofReal] using Complex.cpow_conj (x : ℂ) (-w) ha
  rw [continuedTrace, continuedTrace, riemannZeta_conj, map_add]
  congr 1
  rw [traceCorrection, traceCorrection, Complex.conj_tsum]
  apply tsum_congr
  intro j
  rw [map_sub, branchTrace, branchTrace, map_div₀, map_add, map_one, map_pow,
    map_inv₀, Complex.conj_ofReal, hpow _ (multiplier_pos _)]
  have hn : (0 : ℝ) < (j + 1 : ℕ) := by positivity
  simpa only [Complex.ofReal_natCast] using congrArg
    (fun z : ℂ => conj ((multiplier (j+1) : ℂ)^(-w)) /
      (1 + ((multiplier (j+1) : ℂ)⁻¹)^2) - z) (hpow (j+1 : ℕ) hn)

/-- Arithmetic reflection with conjugation also fails locally for the actual first trace. -/
theorem exists_trace_ne_arithmetic_reflect_in_open {V : Set ℂ} (hVo : IsOpen V)
    (hV : V.Nonempty) (hstrip : V ⊆ {w : ℂ | 0 < w.re ∧ w.re < 1}) :
    ∃ w ∈ V, continuedTrace (1 - conj w) ≠ conj (continuedTrace w) := by
  obtain ⟨w, hw, hne⟩ := exists_trace_ne_reflect_in_open hVo hV hstrip
  refine ⟨w, hw, ?_⟩
  rw [show 1 - conj w = conj (1 - w) by rw [map_sub, map_one], continuedTrace_conj]
  exact fun he => hne ((starRingEnd ℂ).injective he)

#print axioms continuedTrace_conj
#print axioms exists_trace_ne_arithmetic_reflect_in_open

/-- Even conjugated arithmetic reflection admits no spectral-parameter-independent scalar. -/
theorem exists_spectralDeterminant_no_scalar_arithmetic_reflection_in_open
    {V : Set ℂ} (hVo : IsOpen V) (hV : V.Nonempty)
    (hstrip : V ⊆ {w : ℂ | 0 < w.re ∧ w.re < 1}) :
    ∃ w ∈ V, ∀ c : ℂ, ∃ lam : ℂ,
      sourceDeterminant (1 - conj w) (conj lam) ≠ c * conj (sourceDeterminant w lam) := by
  obtain ⟨w, hw, hne⟩ := exists_trace_ne_arithmetic_reflect_in_open hVo hV hstrip
  refine ⟨w, hw, fun c => ?_⟩
  by_contra! he
  have hr : 0 < (1 - conj w).re := by
    simp only [sub_re, one_re, conj_re]
    linarith only [(hstrip hw).2]
  have hz := he 0
  rw [map_zero, sourceDeterminant_eq hr, sourceDeterminant_eq (hstrip hw).1,
    determinant_zero hr, determinant_zero (hstrip hw).1, map_one, mul_one] at hz
  have hf : sourceDeterminant (1 - conj w) = fun z => conj (sourceDeterminant w (conj z)) := by
    funext z
    have hAt := he (conj z)
    simpa only [conj_conj, ← hz, one_mul] using hAt
  have hd := congrArg (fun f : ℂ → ℂ => deriv f 0) hf
  have hconj : deriv (fun z => conj (sourceDeterminant w (conj z))) 0 =
      conj (deriv (sourceDeterminant w) 0) := by
    change deriv (conj ∘ sourceDeterminant w ∘ conj) 0 = _
    rw [deriv_conj_conj]
    simp only [Function.comp_apply, map_zero]
  rw [hconj, sourceDeterminant_deriv_zero hr, sourceDeterminant_deriv_zero (hstrip hw).1,
    map_neg] at hd
  exact hne (neg_injective hd)

#print axioms exists_spectralDeterminant_no_scalar_arithmetic_reflection_in_open

#print axioms traceReflectionRemainder_eq
#print axioms differentiableOn_traceReflectionRemainder
#print axioms differentiableOn_clearedTraceReflectionDefect
#print axioms clearedTraceReflectionDefect_reflect
#print axioms traceReflectionDefect_residue_zero
#print axioms traceReflectionDefect_residue_one
#print axioms exists_trace_ne_reflect_in_open
#print axioms sourceDeterminant_deriv_zero
#print axioms exists_spectralDeterminant_no_scalar_reflection_in_open

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerArithmeticReflection
