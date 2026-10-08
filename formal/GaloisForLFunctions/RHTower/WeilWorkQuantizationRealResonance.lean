import GaloisForLFunctions.RHTower.WeilWorkQuantizationPhaseCoupling

/-!
# Resonance at every positive real height

Exact kernel dilation shifts frequencies and reuses the actual source
height-one infinite-sum comparison. No noninteger residue is assumed zero.
-/
open Complex Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace RHTower.WeilSpectral
open TruncatedRadial AbelianTwist RightEdgeKernel IntegerMassRigidity HamburgerStability
  HamburgerTwisted PhaseLockRigidity GaloisForLFunctions.HTGeometry


/-- Positive dilation of the exact Hamburger kernel. -/
theorem quantization_offKernel_real_scale {x : ℝ} (hx : 0 < x)
    {τ : ℂ} (hτ : τ ≠ 0) (s : ℂ) :
    offKernel ((x : ℂ) * τ) s =
      cexp ((Real.log x : ℂ) * (s - 1)) * offKernel τ s := by
  have hz : (Real.pi : ℂ) * τ ^ 2 ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) (pow_ne_zero _ hτ)
  have hx2 : (0 : ℝ) < x ^ 2 := sq_pos_of_pos hx
  have hx2c : ((x ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx2.ne'
  have he : (Real.pi : ℂ) * ((x : ℂ) * τ) ^ 2 =
      ((x ^ 2 : ℝ) : ℂ) * ((Real.pi : ℂ) * τ ^ 2) := by push_cast; ring
  have hc : (((x ^ 2 : ℝ) : ℂ) * ((Real.pi : ℂ) * τ ^ 2)) ^ (s / 2 - 1) =
      cexp ((2 * (Real.log x : ℂ)) * (s / 2 - 1)) *
        ((Real.pi : ℂ) * τ ^ 2) ^ (s / 2 - 1) := by
    rw [Complex.cpow_def_of_ne_zero (mul_ne_zero hx2c hz),
      Complex.log_ofReal_mul hx2 hz,
      Real.log_pow, Complex.ofReal_mul, Complex.ofReal_natCast,
      add_mul, Complex.exp_add, ← Complex.cpow_def_of_ne_zero hz]
    norm_num
  have hxexp : (x : ℂ) = cexp (Real.log x : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log hx]
  have hexp : (x : ℂ) * cexp ((2 * (Real.log x : ℂ)) * (s / 2 - 1)) =
      cexp ((Real.log x : ℂ) * (s - 1)) := by
    rw [hxexp, ← Complex.exp_add]
    congr 1
    ring
  unfold offKernel
  rw [he, hc]
  calc _ = ((x : ℂ) * cexp ((2 * (Real.log x : ℂ)) * (s / 2 - 1))) *
      ((Real.pi : ℂ) ^ (1 - s / 2) * τ *
        ((Real.pi : ℂ) * τ ^ 2) ^ (s / 2 - 1) / Complex.sin (Real.pi * s / 2)) := by ring
    _ = _ := by rw [hexp]

/-- On the critical line, dilation is a unitary frequency shift and a scalar. -/
theorem quantization_pairKernel_real_scale {x : ℝ} (hx : 0 < x)
    {τ : ℂ} (hτ : τ ≠ 0) (y : ℝ) :
    pairKernel y ((x : ℂ) * τ) =
      (Real.exp (-(Real.log x / 2)) : ℂ) *
        linTwist (-2 * Real.log x) (((1 / 2 : ℝ) : ℂ) + y * I) * pairKernel y τ := by
  rw [pairKernel_eq_offKernel, quantization_offKernel_real_scale hx hτ,
    pairKernel_eq_offKernel]
  congr 1
  unfold linTwist HamburgerStability.linePt
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The weighted frequency moment is stable under a fixed translation. -/
theorem summable_quantization_shifted_frequencies {ι : Type} {p : ι → ℂ} {ω : ι → ℝ}
    (hp : Summable fun j => ‖p j‖ * Real.exp (|ω j| / 2)) (a : ℝ) :
    Summable fun j => ‖p j‖ * Real.exp (|ω j - 2 * a| / 2) := by
  refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_)
    (hp.mul_left (Real.exp |a|))
  calc ‖p j‖ * Real.exp (|ω j - 2 * a| / 2) ≤
      ‖p j‖ * Real.exp (|ω j| / 2 + |a|) := by
        gcongr
        have h := abs_sub (ω j) (2 * a)
        rw [abs_mul, abs_two] at h
        linarith
    _ = Real.exp |a| * (‖p j‖ * Real.exp (|ω j| / 2)) := by
      rw [Real.exp_add]
      ring

/-- Positive dilation preserves the right radial filter. -/
theorem quantization_tendsto_div_nhdsGT {x : ℝ} (hx : 0 < x) :
    Tendsto (fun ε : ℝ => ε / x) (𝓝[>] 0) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · simpa using ((continuous_id.div_const x).tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  · exact eventually_nhdsWithin_of_forall fun ε hε => div_pos hε hx



/-- Fixed translation of the frequency parameter is multiplicative. -/
theorem quantization_linTwist_add (ω η : ℝ) (s : ℂ) :
    linTwist ω s * linTwist η s = linTwist (ω + η) s := by
  unfold linTwist
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Real-height coefficient sum, normalized to the height-one kernel. -/
def quantizationRealFrequencySum {ι : Type} (lam : ℕ → ℝ) (p : ι → ℂ)
    (ω : ι → ℝ) (x : ℝ) : ℂ :=
  (Real.exp (Real.log x / 2) : ℂ) *
    ∑' j, p j * quantizationFrequencyResidue lam (ω j - 2 * Real.log x) 1

/-- Dilation of the complete lower-tail integral is an exact frequency shift. -/
theorem quantization_frequency_integral_real_scale {ι : Type} (p : ι → ℂ) (ω : ι → ℝ)
    (F : ℝ → ℂ) {x : ℝ} (hx : 0 < x) {τ : ℂ} (hτ : τ ≠ 0) :
    (∫ y in Iic (-2 : ℝ), (∑' j, p j * linTwist (ω j) (((1 / 2 : ℝ) : ℂ) + y * I)) *
      (F y * pairKernel y ((x : ℂ) * τ))) =
    (Real.exp (-(Real.log x / 2)) : ℂ) *
      ∫ y in Iic (-2 : ℝ), (∑' j, p j * linTwist (ω j - 2 * Real.log x)
        (((1 / 2 : ℝ) : ℂ) + y * I)) * (F y * pairKernel y τ) := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    dsimp only
    rw [quantization_pairKernel_real_scale hx hτ]
    have hs : (∑' j, p j * linTwist (ω j) (((1 / 2 : ℝ) : ℂ) + y * I)) *
        linTwist (-2 * Real.log x) (((1 / 2 : ℝ) : ℂ) + y * I) =
        ∑' j, p j * linTwist (ω j - 2 * Real.log x) (((1 / 2 : ℝ) : ℂ) + y * I) := by
      rw [← tsum_mul_right]
      apply tsum_congr
      intro j
      rw [mul_assoc, quantization_linTwist_add]
      congr 2
      ring
    linear_combination (Real.exp (-(Real.log x / 2)) : ℂ) * F y * pairKernel y τ * hs

/-- Complete source resonance at every positive real height. -/
theorem tendsto_quantization_frequency_sum_real {ι : Type} [Countable ι]
    {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {p : ι → ℂ} {ω : ι → ℝ}
    (hp : Summable fun j => ‖p j‖ * Real.exp (|ω j| / 2)) {x : ℝ} (hx : 0 < x) :
    Tendsto (fun ε : ℝ =>
      (ε : ℂ) * (∫ y in Iic (-2 : ℝ), (∑' j, p j *
        linTwist (ω j) (((1 / 2 : ℝ) : ℂ) + y * I)) *
          (quantizationTraceF hW y * pairKernel y ((ε : ℂ) + (x : ℂ) * I))) -
      quantizationRealFrequencySum lam p ω x * quantizationMainRadial 1 (ε / x))
      (𝓝[>] 0) (𝓝 0) := by
  have ht := ((tendsto_quantization_frequency_sum_resonance hW
    (summable_quantization_shifted_frequencies hp (Real.log x)) (m := 1) le_rfl).comp
      (quantization_tendsto_div_nhdsGT hx)).const_mul (Real.exp (Real.log x / 2) : ℂ)
  rw [mul_zero] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have he : (ε : ℂ) + (x : ℂ) * I = (x : ℂ) * (((ε / x : ℝ) : ℂ) + I) := by
    push_cast
    field_simp
  have hτ : (((ε / x : ℝ) : ℂ) + I) ≠ 0 := by
    intro hz
    have hi := congrArg Complex.im hz
    norm_num at hi
  have hscalar : (ε : ℂ) * (Real.exp (-(Real.log x / 2)) : ℂ) =
      (Real.exp (Real.log x / 2) : ℂ) * ((ε / x : ℝ) : ℂ) := by
    have hs : x * Real.exp (-(Real.log x / 2)) = Real.exp (Real.log x / 2) := by
      conv_lhs => lhs; rw [← Real.exp_log hx]
      rw [← Real.exp_add]
      congr 1
      ring
    have hr : ε * Real.exp (-(Real.log x / 2)) =
        Real.exp (Real.log x / 2) * (ε / x) := by
      field_simp
      nlinarith [hs]
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
    exact congrArg Complex.ofReal hr
  dsimp only [Function.comp_def]

  rw [he, quantization_frequency_integral_real_scale p ω _ hx hτ,
    ← mul_assoc, hscalar]
  simp only [Nat.cast_one, one_mul, quantizationRealFrequencySum]
  ring



end RHTower.WeilSpectral
