import GaloisForLFunctions.RHTower.WeilWorkQuantizationRealResonance

/-!
# Period-one law for the actual reflected residues

The source reflected Laplace series is i-periodic up to its explicit polar
term. Its real-height residues therefore form a period-one function. This
is a representation constraint, not a producer of a phase representation.
-/
open Complex Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace RHTower.WeilSpectral
open TruncatedRadial AbelianTwist RightEdgeKernel IntegerMassRigidity HamburgerStability
  HamburgerTwisted PhaseLockRigidity GaloisForLFunctions.HTGeometry


/-- Only the lower tail can carry a positive-height reflected residue. -/
theorem tendsto_quantization_laplace_sub_far_unit {h : ℝ → ℂ} {C : ℝ} {N : ℕ}
    (hh : AEStronglyMeasurable h volume) (hB : ∀ t, ‖h t‖ ≤ C * (1 + |t|) ^ N) :
    Tendsto (fun ε : ℝ => (ε : ℂ) *
      ((2 * Real.pi : ℂ) * defectLaplace h ((ε : ℂ) + I) -
        ∫ t in Iic (-1 : ℝ), h t * pairKernel (2 * t) ((ε : ℂ) + I)))
      (𝓝[>] 0) (𝓝 0) := by
  have hup := tendsto_mul_defectLaplace_upper_radial hh hB (Y := 1) zero_le_one 1
  have hmid := tendsto_mul_defectLaplace_radial (hh.indicator measurableSet_Icc)
    (fun t => (norm_indicator_le_norm_self h t).trans (hB t))
    (tendsto_mul_abelMass_indicator_Icc hh hB 1) 1
  have ht := (hup.add hmid).const_mul (2 * Real.pi : ℂ)
  simp only [Nat.cast_one, one_mul, add_zero, mul_zero] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  rw [defectLaplace_split hh hB zero_le_one (τ := (ε : ℂ) + I) (by simpa using hε)]
  have hlow : (2 * Real.pi : ℂ) * defectLaplace ((Iio (-1 : ℝ)).indicator h)
      ((ε : ℂ) + I) = ∫ t in Iic (-1 : ℝ), h t * pairKernel (2 * t) ((ε : ℂ) + I) := by
    unfold defectLaplace
    have he : (fun t => (Iio (-1 : ℝ)).indicator h t * pairKernel (2 * t) ((ε : ℂ) + I)) =
        (Iio (-1 : ℝ)).indicator (fun t => h t * pairKernel (2 * t) ((ε : ℂ) + I)) := by
      funext t
      by_cases ht : t ∈ Iio (-1 : ℝ) <;> simp [ht]
    rw [he, integral_indicator measurableSet_Iio, integral_Iic_eq_integral_Iio]
    push_cast
    field_simp
  rw [← hlow]
  ring

/-- Real dilation of a restricted Laplace integral. -/
theorem quantization_setIntegral_real_scale (h : ℝ → ℂ) (s : Set ℝ)
    {x : ℝ} (hx : 0 < x) {τ : ℂ} (hτ : τ ≠ 0) :
    (∫ t in s, h t * pairKernel (2 * t) ((x : ℂ) * τ)) =
      (Real.exp (-(Real.log x / 2)) : ℂ) * ∫ t in s,
        (linTwist (-2 * Real.log x) (((1 / 2 : ℝ) : ℂ) + (2 * t : ℝ) * I) * h t) *
          pairKernel (2 * t) τ := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun t => by
    dsimp only
    rw [quantization_pairKernel_real_scale hx hτ]
    ring

theorem quantization_defectLaplace_real_scale (h : ℝ → ℂ)
    {x : ℝ} (hx : 0 < x) {τ : ℂ} (hτ : τ ≠ 0) :
    defectLaplace h ((x : ℂ) * τ) = (Real.exp (-(Real.log x / 2)) : ℂ) *
      defectLaplace (fun t => linTwist (-2 * Real.log x)
        (((1 / 2 : ℝ) : ℂ) + (2 * t : ℝ) * I) * h t) τ := by
  have he := quantization_setIntegral_real_scale h Set.univ hx hτ
  simp only [setIntegral_univ] at he
  unfold defectLaplace
  rw [he]
  ring

/-- Upper and compact pieces vanish also below height one. -/
theorem tendsto_quantization_laplace_sub_far_real {h : ℝ → ℂ} {C : ℝ} {N : ℕ}
    (hh : AEStronglyMeasurable h volume) (hB : ∀ t, ‖h t‖ ≤ C * (1 + |t|) ^ N)
    {x : ℝ} (hx : 0 < x) :
    Tendsto (fun ε : ℝ => (ε : ℂ) *
      ((2 * Real.pi : ℂ) * defectLaplace h ((ε : ℂ) + (x : ℂ) * I) -
        ∫ t in Iic (-1 : ℝ), h t * pairKernel (2 * t) ((ε : ℂ) + (x : ℂ) * I)))
      (𝓝[>] 0) (𝓝 0) := by
  let g : ℝ → ℂ := fun t => linTwist (-2 * Real.log x)
    (((1 / 2 : ℝ) : ℂ) + (2 * t : ℝ) * I) * h t
  have hgc : Continuous (fun t : ℝ => linTwist (-2 * Real.log x)
      (((1 / 2 : ℝ) : ℂ) + (2 * t : ℝ) * I)) :=
    (continuous_linTwist _).comp (by fun_prop)
  have hgm : AEStronglyMeasurable g volume := hgc.aestronglyMeasurable.mul hh
  have hgb : ∀ t, ‖g t‖ ≤ C * (1 + |t|) ^ N := by
    intro t
    simpa [g, norm_mul, norm_linTwist] using hB t
  have ht := ((tendsto_quantization_laplace_sub_far_unit hgm hgb).comp
    (quantization_tendsto_div_nhdsGT hx)).const_mul
      ((x : ℂ) * (Real.exp (-(Real.log x / 2)) : ℂ))
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
  dsimp only [Function.comp_def]
  rw [he, quantization_defectLaplace_real_scale h hx hτ,
    quantization_setIntegral_real_scale h _ hx hτ]
  dsimp only [g]
  push_cast
  field_simp
  ring_nf
  simp only [mul_comm]

/-- The actual reflected transform has equal radial residues a unit apart. -/
theorem tendsto_quantization_reflected_radial_translation {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {x : ℝ} (hx : 0 < x) :
    Tendsto (fun ε : ℝ => (ε : ℂ) *
      (defectLaplace (fun t => quantizationReflectedTraceF hW (2 * t))
        ((ε : ℂ) + ((x + 1 : ℝ) : ℂ) * I) -
       defectLaplace (fun t => quantizationReflectedTraceF hW (2 * t))
        ((ε : ℂ) + (x : ℂ) * I))) (𝓝[>] 0) (𝓝 0) := by
  let β := betaG (quantizationCompletion hW)
  have hcorr (y : ℝ) (hy : 0 < y) : Tendsto (fun ε : ℝ => (ε : ℂ) *
      (β / (Real.pi * ((ε : ℂ) + (y : ℂ) * I)))) (𝓝[>] 0) (𝓝 0) := by
    have hden : (Real.pi : ℂ) * ((0 : ℂ) + (y : ℂ) * I) ≠ 0 := by
      simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero, Complex.ofReal_ne_zero.mpr hy.ne']
    have ht := (Complex.continuous_ofReal.tendsto (0 : ℝ)).mul
      ((tendsto_const_nhds (x := β)).div ((tendsto_const_nhds (x := (Real.pi : ℂ))).mul
        ((Complex.continuous_ofReal.tendsto (0 : ℝ)).add_const ((y : ℂ) * I))) hden)
    simpa using ht.mono_left nhdsWithin_le_nhds
  have ht := (hcorr x hx).sub (hcorr (x + 1) (by linarith))
  rw [sub_self] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  rw [quantization_reflected_defectLaplace_eq hW (by simpa using hε),
    quantization_reflected_defectLaplace_eq hW (by simpa using hε)]
  have hp := thetaLaplace_add_nat_mul_I (dirichletExp (lamLog lam))
    ((ε : ℂ) + (x : ℂ) * I) 1
  simp only [Nat.cast_one, one_mul] at hp
  have he : (ε : ℂ) + ((x + 1 : ℝ) : ℂ) * I = ((ε : ℂ) + (x : ℂ) * I) + I := by
    push_cast
    ring
  rw [he]
  change _ = (ε : ℂ) * ((thetaLaplace _ (((ε : ℂ) + (x : ℂ) * I) + I) - _) -
    (thetaLaplace _ ((ε : ℂ) + (x : ℂ) * I) - _))
  rw [hp]
  dsimp only [β]
  ring



/-- The actual reflected far integral equals the represented source integral. -/
theorem quantization_reflected_far_phase_eq {ι : Type} [Countable ι]
    {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {p : ι → ℂ} {ω : ι → ℝ}
    (hphase : ∀ x : ℝ, 0 < x →
      cexp (((2 * Real.pi * quantizationResidualCumulative hW x : ℝ) : ℂ) * I) =
        ∑' j, p j * cexp (((ω j * x : ℝ) : ℂ) * I)) (τ : ℂ) :
    (∫ t in Iic (-1 : ℝ), quantizationReflectedTraceF hW (2 * t) * pairKernel (2 * t) τ) =
      (quantizationOriginPhase hW / 2) * ∫ y in Iic (-2 : ℝ),
        (∑' j, p j * linTwist (ω j) (((1 / 2 : ℝ) : ℂ) + y * I)) *
          (quantizationTraceF hW y * pairKernel y τ) := by
  let P : ℝ → ℂ := fun y => ∑' j, p j * linTwist (ω j) (((1 / 2 : ℝ) : ℂ) + y * I)
  have heq : (∫ t in Iic (-1 : ℝ), quantizationReflectedTraceF hW (2 * t) *
      pairKernel (2 * t) τ) = quantizationOriginPhase hW *
      ∫ t in Iic (-1 : ℝ), P (2 * t) *
        (quantizationTraceF hW (2 * t) * pairKernel (2 * t) τ) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (ae_quantizationReflectedTraceF_cumulative_phase hW),
      ae_restrict_mem measurableSet_Iic] with t ht ht1
    have ht0 : t < 0 := lt_of_le_of_lt ht1 (by norm_num)
    rw [ht ht0, hphase (-t) (by linarith)]
    have hP : P (2 * t) = ∑' j, p j * cexp (((ω j * (-t) : ℝ) : ℂ) * I) := by
      apply tsum_congr
      intro j
      congr 1
      unfold linTwist
      congr 1
      push_cast
      ring
    rw [hP]
    ring
  have hchange := setIntegral_Iic_comp_two_mul
    (fun y => P y * (quantizationTraceF hW y * pairKernel y τ)) (-1)
  norm_num only [mul_neg, mul_one] at hchange
  rw [heq, hchange]
  dsimp only [P]
  ring

/-- A represented actual source fixes a nonzero limit of the height-one kernel. -/
theorem exists_quantization_mainRadial_limit {ι : Type} [Countable ι]
    {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {p : ι → ℂ} {ω : ι → ℝ}
    (hp : Summable fun j => ‖p j‖ * Real.exp (|ω j| / 2))
    (hphase : ∀ x : ℝ, 0 < x →
      cexp (((2 * Real.pi * quantizationResidualCumulative hW x : ℝ) : ℂ) * I) =
        ∑' j, p j * cexp (((ω j * x : ℝ) : ℂ) * I)) :
    ∃ L : ℂ, L ≠ 0 ∧ Tendsto (quantizationMainRadial 1) (𝓝[>] 0) (𝓝 L) := by
  let B := ∑' j, p j * quantizationFrequencyResidue lam (ω j) 1
  let κ := quantizationOriginPhase hW
  have hB : B ≠ 0 := (quantization_phase_resonance_constant hW hp hphase).1
  have hκ : κ ≠ 0 := by
    intro he
    have hn := norm_quantizationOriginPhase hW
    change ‖κ‖ = 1 at hn
    rw [he, norm_zero] at hn
    norm_num at hn
  have hβ : betaG (quantizationCompletion hW) ≠ 0 := by
    unfold betaG
    exact div_ne_zero (G_ne_zero (differentiableOn_weilContinuation hW)
      (fun _ hs => hasDerivAt_quantizationCompletion hW hs) (quantizationCompletion_two hW)
      (by norm_num : (1 / 2 : ℝ) < (1 : ℂ).re)) two_ne_zero
  have hd : κ * B ≠ 0 := mul_ne_zero hκ hB
  refine ⟨4 * betaG (quantizationCompletion hW) / (κ * B),
    div_ne_zero (mul_ne_zero (by norm_num) hβ) hd, ?_⟩
  have ht := (tendsto_quantization_phase_resonance hW hp hphase (m := 1) le_rfl).div_const (κ * B)
  apply ht.congr
  intro ε
  change (κ * B * quantizationMainRadial 1 ε) / (κ * B) = quantizationMainRadial 1 ε
  field_simp

/-- Every real-height coefficient sum is the corresponding actual reflected residue. -/
theorem tendsto_quantization_phase_laplace_real {ι : Type} [Countable ι]
    {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {p : ι → ℂ} {ω : ι → ℝ}
    (hp : Summable fun j => ‖p j‖ * Real.exp (|ω j| / 2))
    (hphase : ∀ x : ℝ, 0 < x →
      cexp (((2 * Real.pi * quantizationResidualCumulative hW x : ℝ) : ℂ) * I) =
        ∑' j, p j * cexp (((ω j * x : ℝ) : ℂ) * I))
    {L : ℂ} (hL : Tendsto (quantizationMainRadial 1) (𝓝[>] 0) (𝓝 L))
    {x : ℝ} (hx : 0 < x) :
    Tendsto (fun ε : ℝ => (ε : ℂ) * ((2 * Real.pi : ℂ) *
      defectLaplace (fun t => quantizationReflectedTraceF hW (2 * t))
        ((ε : ℂ) + (x : ℂ) * I))) (𝓝[>] 0)
      (𝓝 ((quantizationOriginPhase hW / 2) * quantizationRealFrequencySum lam p ω x * L)) := by
  have hmain := (hL.comp (quantization_tendsto_div_nhdsGT hx)).const_mul
    (quantizationRealFrequencySum lam p ω x)
  have ht := (tendsto_quantization_frequency_sum_real hW hp hx).add hmain
  simp only [Function.comp_def, zero_add, sub_add_cancel] at ht
  have hfar := ht.const_mul (quantizationOriginPhase hW / 2)
  obtain ⟨C, _, hB⟩ := exists_quantization_trace_pair_bound hW
  have herr := tendsto_quantization_laplace_sub_far_real
    ((measurable_quantizationReflectedTraceF hW).comp
      (measurable_const.mul measurable_id)).aestronglyMeasurable
    (fun t => (hB t).2) hx
  simp only [Function.comp_def, Pi.mul_apply, id_eq] at herr
  have hall := herr.add hfar
  simp only [zero_add] at hall
  rw [← mul_assoc (quantizationOriginPhase hW / 2) (quantizationRealFrequencySum lam p ω x) L] at hall
  apply hall.congr
  intro ε
  rw [quantization_reflected_far_phase_eq hW hphase]
  ring

/-- Translation of the actual reflected source makes every real resonance sum period one. -/
theorem quantization_phase_resonance_periodic {ι : Type} [Countable ι]
    {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {p : ι → ℂ} {ω : ι → ℝ}
    (hp : Summable fun j => ‖p j‖ * Real.exp (|ω j| / 2))
    (hphase : ∀ x : ℝ, 0 < x →
      cexp (((2 * Real.pi * quantizationResidualCumulative hW x : ℝ) : ℂ) * I) =
        ∑' j, p j * cexp (((ω j * x : ℝ) : ℂ) * I)) {x : ℝ} (hx : 0 < x) :
    quantizationRealFrequencySum lam p ω (x + 1) = quantizationRealFrequencySum lam p ω x := by
  obtain ⟨L, hL0, hL⟩ := exists_quantization_mainRadial_limit hW hp hphase
  have hκ : quantizationOriginPhase hW / 2 ≠ 0 := by
    apply div_ne_zero _ two_ne_zero
    intro he
    have hn := norm_quantizationOriginPhase hW
    rw [he, norm_zero] at hn
    norm_num at hn
  have ht := (tendsto_quantization_phase_laplace_real hW hp hphase hL (by linarith : 0 < x + 1)).sub
    (tendsto_quantization_phase_laplace_real hW hp hphase hL hx)
  have hz := (tendsto_quantization_reflected_radial_translation hW hx).const_mul (2 * Real.pi : ℂ)
  rw [mul_zero] at hz
  have he := tendsto_nhds_unique ht (hz.congr (fun ε => by ring))
  have heq := sub_eq_zero.mp he
  exact mul_left_cancel₀ hκ (mul_right_cancel₀ hL0 heq)

end RHTower.WeilSpectral
