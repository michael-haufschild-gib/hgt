import GaloisForLFunctions.RHTower.L2FourierEndpointOrthogonality
import GaloisForLFunctions.HTGeometry.L2MultiplierContinuity
import GaloisForLFunctions.HTGeometry.MassGaugeRadiationLimit
import GaloisForLFunctions.HTGeometry.MassGaugeHalfWaveL2

/-!
# Superluminal causal compression retains the full radiation norm

Write `U_u` for the gauged massive half-wave propagator, the Fourier multiplier with symbol
`exp (-i u ω_{a,λ})`, and `P_H` for multiplication by the indicator of `(0, H)`.  The full-space
operator norm of `U_u` is `e^{λ|u|}`: the amplified outgoing end of the symbol is not integrable
away.

Compressing to a causal window cannot remove that end as long as the window outruns the
propagation distance.  A unit datum supported in `(u, H)` and modulated by `e^{-iRh}` has Fourier
transform concentrated near frequency `-R`, where the symbol is asymptotically the amplified plane
wave `e^{λu} e^{iuξ}`; dominated convergence turns this into

`‖U_u φ_R − e^{λu} φ_R(· + u)‖₂ → 0`,

and the limit is supported in `(0, H - u)`.  Both the input and the limit are therefore fixed by
`P_H`, so

`H > u ≥ 0  ⟹  ‖P_H U_u P_H‖ = e^{λu}`.

No Hardy factorisation, spectral support assumption or asymptotic norm heuristic is used.
-/

open MeasureTheory Filter Complex Set

open scoped ENNReal FourierTransform

namespace RHTower

open GaloisForLFunctions.HTGeometry RHTower.MellinL2

noncomputable section

/-! ## The symbol in the analyst frequency variable -/

/-- The gauged half-wave symbol read in the `2π`-normalised frequency variable. -/
def superluminalSymbol (a lambda u w : ℝ) : ℂ :=
  massGaugeHalfWaveSymbol a lambda u (2 * Real.pi * w)

/-- The amplified outgoing model symbol read in the `2π`-normalised frequency variable. -/
def superluminalModel (lambda u w : ℝ) : ℂ :=
  ((Real.exp (u * lambda) : ℝ) : ℂ) * fourierPhase u w

/-- The difference of the two symbols. -/
def superluminalDiff (a lambda u w : ℝ) : ℂ :=
  superluminalSymbol a lambda u w - superluminalModel lambda u w

theorem superluminalModel_eq (lambda u w : ℝ) :
    superluminalModel lambda u w = massGaugeRadiationModel lambda u (2 * Real.pi * w) := by
  have hexp : ((2 * Real.pi * (u * w) : ℝ) : ℂ) * I
      = I * (u : ℂ) * ((2 * Real.pi * w : ℝ) : ℂ) := by
    push_cast
    ring
  rw [superluminalModel, massGaugeRadiationModel, fourierPhase, Real.fourierChar_apply, hexp]

theorem continuous_superluminalSymbol {a lambda : ℝ} (ha : lambda < a) (hlambda : 0 ≤ lambda)
    (u : ℝ) : Continuous (superluminalSymbol a lambda u) :=
  (continuous_massGaugeHalfWaveSymbol ha hlambda u).comp (by fun_prop)

theorem measurable_superluminalSymbol {a lambda : ℝ} (ha : lambda < a) (hlambda : 0 ≤ lambda)
    (u : ℝ) : Measurable (superluminalSymbol a lambda u) :=
  (continuous_superluminalSymbol ha hlambda u).measurable

theorem continuous_superluminalModel (lambda u : ℝ) :
    Continuous (superluminalModel lambda u) := by
  refine continuous_const.mul ?_
  exact fourierPhase_continuous u

theorem measurable_superluminalModel (lambda u : ℝ) :
    Measurable (superluminalModel lambda u) :=
  (continuous_superluminalModel lambda u).measurable

theorem measurable_superluminalDiff {a lambda : ℝ} (ha : lambda < a) (hlambda : 0 ≤ lambda)
    (u : ℝ) : Measurable (superluminalDiff a lambda u) :=
  (measurable_superluminalSymbol ha hlambda u).sub (measurable_superluminalModel lambda u)

theorem norm_superluminalSymbol_le {a lambda : ℝ} (ha : lambda < a) (hlambda : 0 < lambda)
    (u w : ℝ) : ‖superluminalSymbol a lambda u w‖ ≤ Real.exp (|u| * lambda) :=
  norm_massGaugeHalfWaveSymbol_le ha hlambda u _

@[simp]
theorem norm_superluminalModel (lambda u w : ℝ) :
    ‖superluminalModel lambda u w‖ = Real.exp (u * lambda) := by
  rw [superluminalModel, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.exp_nonneg _), norm_fourierPhase, mul_one]

/-- The uniform bound shared by the symbol, the model and their difference. -/
def superluminalBound (lambda u : ℝ) : ℝ := Real.exp (|u| * lambda) + Real.exp (u * lambda)

theorem superluminalBound_nonneg (lambda u : ℝ) : 0 ≤ superluminalBound lambda u := by
  unfold superluminalBound
  positivity

theorem norm_superluminalDiff_le {a lambda : ℝ} (ha : lambda < a) (hlambda : 0 < lambda)
    (u w : ℝ) : ‖superluminalDiff a lambda u w‖ ≤ superluminalBound lambda u := by
  refine le_trans (norm_sub_le _ _) ?_
  rw [norm_superluminalModel, superluminalBound]
  linarith [norm_superluminalSymbol_le ha hlambda u w]

/-- **(24.44) At the outgoing end the symbol is asymptotically the amplified plane wave.** -/
theorem tendsto_superluminalDiff_atBot {a lambda : ℝ} (ha : lambda ≤ a) (hlambda : 0 ≤ lambda)
    (u : ℝ) : Tendsto (superluminalDiff a lambda u) atBot (nhds 0) := by
  have hscale : Tendsto (fun w : ℝ => 2 * Real.pi * w) atBot atBot :=
    Filter.Tendsto.const_mul_atBot (by positivity) Filter.tendsto_id
  have hbase := tendsto_massGaugeHalfWaveSymbol_sub_radiation_atBot ha hlambda u
  have hcomp := hbase.comp hscale
  refine hcomp.congr fun w => ?_
  rw [Function.comp_apply, superluminalDiff, superluminalSymbol, superluminalModel_eq]

/-! ## The half-wave propagator and the causal windows -/

/-- The gauged massive half-wave propagator on `L²(ℝ)`. -/
def superluminalHalfWave {a lambda : ℝ} (ha : lambda < a) (hlambda : 0 < lambda) (u : ℝ) :
    Lp (α := ℝ) ℂ 2 →L[ℂ] Lp (α := ℝ) ℂ 2 :=
  fourierMulCLM (measurable_superluminalSymbol ha hlambda.le u) (Real.exp_nonneg _)
    (norm_superluminalSymbol_le ha hlambda u)

/-- The indicator symbol of a window. -/
def windowSymbol (S : Set ℝ) (h : ℝ) : ℂ := Set.indicator S (fun _ => (1 : ℂ)) h

theorem measurable_windowSymbol {S : Set ℝ} (hS : MeasurableSet S) :
    Measurable (windowSymbol S) :=
  measurable_const.indicator hS

theorem norm_windowSymbol_le (S : Set ℝ) (h : ℝ) : ‖windowSymbol S h‖ ≤ 1 := by
  rw [windowSymbol]
  by_cases hh : h ∈ S
  · rw [Set.indicator_of_mem hh]
    simp
  · rw [Set.indicator_of_notMem hh]
    simp

theorem windowSymbol_eq_one {S : Set ℝ} {h : ℝ} (hh : h ∈ S) : windowSymbol S h = 1 :=
  Set.indicator_of_mem hh _

/-- Multiplication by the indicator of a window. -/
def windowCutoff {S : Set ℝ} (hS : MeasurableSet S) :
    Lp (α := ℝ) ℂ 2 →L[ℂ] Lp (α := ℝ) ℂ 2 :=
  lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ)) (measurable_windowSymbol hS)
    zero_le_one (norm_windowSymbol_le S)

theorem norm_windowCutoff_le {S : Set ℝ} (hS : MeasurableSet S) : ‖windowCutoff hS‖ ≤ 1 :=
  norm_lpBoundedMulCLM_le (p := 2) (μ := (volume : Measure ℝ)) (measurable_windowSymbol hS)
    zero_le_one (norm_windowSymbol_le S)

theorem windowCutoff_coeFn {S : Set ℝ} (hS : MeasurableSet S) (f : Lp (α := ℝ) ℂ 2) :
    (windowCutoff hS f : ℝ → ℂ) =ᵐ[volume] fun h => windowSymbol S h * (f : ℝ → ℂ) h :=
  lpBoundedMulCLM_coeFn (p := 2) (μ := (volume : Measure ℝ)) (measurable_windowSymbol hS)
    zero_le_one (norm_windowSymbol_le S) f

/-- A datum vanishing outside the window is fixed by the cutoff. -/
theorem windowCutoff_eq_self {S : Set ℝ} (hS : MeasurableSet S) {f : Lp (α := ℝ) ℂ 2}
    (hf : ∀ᵐ h : ℝ, h ∉ S → (f : ℝ → ℂ) h = 0) : windowCutoff hS f = f := by
  refine Lp.ext ?_
  filter_upwards [windowCutoff_coeFn hS f, hf] with h h1 h2
  rw [h1]
  by_cases hmem : h ∈ S
  · rw [windowSymbol_eq_one hmem, one_mul]
  · rw [h2 hmem, mul_zero]

/-! ## The translation dictionary -/

theorem translation_coeFn_massGaugeSuperluminalCompression (b : ℝ) (f : Lp (α := ℝ) ℂ 2) :
    (additiveTranslationUnitary b f : ℝ → ℂ) =ᵐ[volume] fun x => (f : ℝ → ℂ) (x + b) := by
  filter_upwards [Lp.coeFn_compMeasurePreserving f (realTranslation_measurePreserving b)]
    with x hx
  simpa [additiveTranslationUnitary, lpCompMeasurePreservingEquiv, Function.comp_def,
    realTranslationEquiv] using hx

theorem phaseMul_coeFn (c : ℝ) (f : Lp (α := ℝ) ℂ 2) :
    (fourierPhaseMulUnitary c f : ℝ → ℂ) =ᵐ[volume] fun x => fourierPhase c x * (f : ℝ → ℂ) x :=
  fourierPhaseMulAux_ae c f

/-- A translated multiplication operator is the multiplication operator of the translated
symbol. -/
theorem lpBoundedMulCLM_additiveTranslation {chi chi' : ℝ → ℂ} (hchi : Measurable chi)
    (hchi' : Measurable chi') {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ x, ‖chi x‖ ≤ C)
    (hC' : ∀ x, ‖chi' x‖ ≤ C) (b : ℝ) (hshift : ∀ x, chi' x = chi (x - b))
    (G : Lp (α := ℝ) ℂ 2) :
    lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ)) hchi hC0 hC
        (additiveTranslationUnitary b G)
      = additiveTranslationUnitary b
          (lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ)) hchi' hC0 hC' G) := by
  refine Lp.ext ?_
  have hinner := (lpBoundedMulCLM_coeFn (p := 2) (μ := (volume : Measure ℝ)) hchi' hC0 hC'
    G).comp_tendsto (realTranslation_measurePreserving b).quasiMeasurePreserving.tendsto_ae
  filter_upwards [
    lpBoundedMulCLM_coeFn (p := 2) (μ := (volume : Measure ℝ)) hchi hC0 hC
      (additiveTranslationUnitary b G),
    translation_coeFn_massGaugeSuperluminalCompression b G,
    translation_coeFn_massGaugeSuperluminalCompression b (lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ)) hchi' hC0 hC' G),
    hinner] with x h1 h2 h3 h4
  rw [h1, h2, h3]
  have h4' : (lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ)) hchi' hC0 hC' G : ℝ → ℂ)
      (x + b) = chi' (x + b) * (G : ℝ → ℂ) (x + b) := by
    simpa [Function.comp_apply, realTranslationEquiv] using h4
  rw [h4', hshift (x + b)]
  congr 2
  ring

/-! ## The exact inverse Fourier dictionary -/

theorem fourierL2_eq (f : Lp (α := ℝ) ℂ 2) : fourierL2 ℝ f = 𝓕 f := rfl

theorem fourierL2inv_eq (f : Lp (α := ℝ) ℂ 2) : fourierL2inv ℝ f = 𝓕⁻ f := rfl

/-- The model multiplier is the amplified translation. -/
theorem superluminalModelMul_apply (lambda u : ℝ) (f : Lp (α := ℝ) ℂ 2) :
    fourierL2inv ℝ (lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ))
        (measurable_superluminalModel lambda u) (Real.exp_nonneg _)
        (fun w => le_of_eq (norm_superluminalModel lambda u w)) (fourierL2 ℝ f))
      = ((Real.exp (u * lambda) : ℝ) : ℂ) • additiveTranslationUnitary u f := by
  have hphase : lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ))
      (measurable_superluminalModel lambda u) (Real.exp_nonneg _)
      (fun w => le_of_eq (norm_superluminalModel lambda u w)) (fourierL2 ℝ f)
      = ((Real.exp (u * lambda) : ℝ) : ℂ) • fourierPhaseMulUnitary u (𝓕 f) := by
    refine Lp.ext ?_
    filter_upwards [
      lpBoundedMulCLM_coeFn (p := 2) (μ := (volume : Measure ℝ))
        (measurable_superluminalModel lambda u) (Real.exp_nonneg _)
        (fun w => le_of_eq (norm_superluminalModel lambda u w)) (fourierL2 ℝ f),
      Lp.coeFn_smul (((Real.exp (u * lambda) : ℝ) : ℂ)) (fourierPhaseMulUnitary u (𝓕 f)),
      phaseMul_coeFn u (𝓕 f)] with w h1 h2 h3
    rw [h1, h2, Pi.smul_apply, h3, smul_eq_mul, superluminalModel, fourierL2_eq]
    ring
  rw [hphase, map_smul, ← fourier_additiveTranslation, fourierL2inv_eq]
  congr 1
  exact (Lp.fourierTransformₗᵢ ℝ ℂ).symm_apply_apply _

/-! ## The normalized causal packet -/

theorem volume_Ioo_ne_top (u H : ℝ) : (volume (Set.Ioo u H)) ≠ ∞ := by
  rw [Real.volume_Ioo]
  exact ENNReal.ofReal_ne_top

/-- The `L²`-normalized indicator of the causal interval `(u, H)`. -/
def causalPacket (u H : ℝ) : Lp (α := ℝ) ℂ 2 :=
  indicatorConstLp 2 (measurableSet_Ioo (a := u) (b := H)) (volume_Ioo_ne_top u H)
    ((((Real.sqrt (H - u))⁻¹ : ℝ) : ℂ))

theorem causalPacket_vanishing (u H : ℝ) :
    ∀ᵐ h : ℝ, h ∉ Set.Ioo u H → (causalPacket u H : ℝ → ℂ) h = 0 := by
  filter_upwards [indicatorConstLp_coeFn (p := 2)
    (hs := measurableSet_Ioo (a := u) (b := H)) (hμs := volume_Ioo_ne_top u H)
    (c := (((Real.sqrt (H - u))⁻¹ : ℝ) : ℂ))] with h hh hnot
  rw [causalPacket, hh, Set.indicator_of_notMem hnot]

theorem norm_causalPacket {u H : ℝ} (h : u < H) : ‖causalPacket u H‖ = 1 := by
  have hpos : (0 : ℝ) < H - u := by linarith
  have hsq : 0 < Real.sqrt (H - u) := Real.sqrt_pos.2 hpos
  rw [causalPacket, norm_indicatorConstLp (by norm_num) (by norm_num)]
  have hvol : (volume : Measure ℝ).real (Set.Ioo u H) = H - u := by
    rw [measureReal_def, Real.volume_Ioo, ENNReal.toReal_ofReal hpos.le]
  have hcoe : ‖(((Real.sqrt (H - u))⁻¹ : ℝ) : ℂ)‖ = (Real.sqrt (H - u))⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have htoReal : ((2 : ℝ≥0∞)).toReal = 2 := by simp
  rw [hvol, hcoe, htoReal, ← Real.sqrt_eq_rpow, inv_mul_cancel₀ hsq.ne']

/-- The modulated causal packet. -/
def causalPacketMod (u H t : ℝ) : Lp (α := ℝ) ℂ 2 :=
  fourierPhaseMulUnitary t (causalPacket u H)

theorem norm_causalPacketMod {u H : ℝ} (h : u < H) (t : ℝ) : ‖causalPacketMod u H t‖ = 1 := by
  rw [causalPacketMod, (fourierPhaseMulUnitary t).norm_map, norm_causalPacket h]

theorem causalPacketMod_vanishing (u H t : ℝ) :
    ∀ᵐ h : ℝ, h ∉ Set.Ioo u H → (causalPacketMod u H t : ℝ → ℂ) h = 0 := by
  filter_upwards [phaseMul_coeFn t (causalPacket u H), causalPacket_vanishing u H]
    with h h1 h2 hnot
  rw [causalPacketMod, h1, h2 hnot, mul_zero]

theorem windowCutoff_causalPacketMod {u H : ℝ} {S : Set ℝ} (hS : MeasurableSet S)
    (hin : Set.Ioo u H ⊆ S) (t : ℝ) :
    windowCutoff hS (causalPacketMod u H t) = causalPacketMod u H t := by
  refine windowCutoff_eq_self hS ?_
  filter_upwards [causalPacketMod_vanishing u H t] with h hh hnot
  exact hh fun hmem => hnot (hin hmem)

theorem windowCutoff_translated {u H : ℝ} {S : Set ℝ} (hS : MeasurableSet S)
    (hout : Set.Ioo 0 (H - u) ⊆ S) (t : ℝ) :
    windowCutoff hS (additiveTranslationUnitary u (causalPacketMod u H t))
      = additiveTranslationUnitary u (causalPacketMod u H t) := by
  refine windowCutoff_eq_self hS ?_
  have hshift : ∀ᵐ h : ℝ, h + u ∉ Set.Ioo u H →
      (causalPacketMod u H t : ℝ → ℂ) (h + u) = 0 := by
    simpa [Function.comp_def, realTranslationEquiv] using
      (realTranslation_measurePreserving u).quasiMeasurePreserving.ae
        (causalPacketMod_vanishing u H t)
  filter_upwards [translation_coeFn_massGaugeSuperluminalCompression u (causalPacketMod u H t), hshift] with h h1 h2 hnot
  rw [h1]
  refine h2 fun hmem => hnot (hout ?_)
  rw [Set.mem_Ioo] at hmem ⊢
  exact ⟨by linarith [hmem.1], by linarith [hmem.2]⟩

/-! ## The shifted difference symbol -/

/-- The difference symbol translated to the outgoing end. -/
def superluminalShiftedDiff (a lambda u t w : ℝ) : ℂ := superluminalDiff a lambda u (w + t)

theorem measurable_superluminalShiftedDiff {a lambda : ℝ} (ha : lambda < a) (hlambda : 0 ≤ lambda)
    (u t : ℝ) : Measurable (superluminalShiftedDiff a lambda u t) :=
  (measurable_superluminalDiff ha hlambda u).comp (measurable_id.add_const t)

theorem norm_superluminalShiftedDiff_le {a lambda : ℝ} (ha : lambda < a) (hlambda : 0 < lambda)
    (u t w : ℝ) : ‖superluminalShiftedDiff a lambda u t w‖ ≤ superluminalBound lambda u :=
  norm_superluminalDiff_le ha hlambda u _

theorem tendsto_superluminalShiftedDiff {a lambda : ℝ} (ha : lambda ≤ a) (hlambda : 0 ≤ lambda)
    (u w : ℝ) :
    Tendsto (fun t : ℝ => superluminalShiftedDiff a lambda u t w) atBot (nhds 0) := by
  have hshift : Tendsto (fun t : ℝ => w + t) atBot atBot :=
    Filter.tendsto_atBot_add_const_left _ w Filter.tendsto_id
  exact (tendsto_superluminalDiff_atBot ha hlambda u).comp hshift

/-! ## The packet defect vanishes at the outgoing end -/

/-- The defect between the propagated packet and its amplified translate. -/
def superluminalDefect {a lambda : ℝ} (ha : lambda < a) (hlambda : 0 < lambda) (u H t : ℝ) :
    Lp (α := ℝ) ℂ 2 :=
  superluminalHalfWave ha hlambda u (causalPacketMod u H t)
    - ((Real.exp (u * lambda) : ℝ) : ℂ) • additiveTranslationUnitary u (causalPacketMod u H t)

theorem superluminalDefect_eq {a lambda : ℝ} (ha : lambda < a) (hlambda : 0 < lambda)
    (u H t : ℝ) :
    superluminalDefect ha hlambda u H t
      = fourierL2inv ℝ (additiveTranslationUnitary (-t)
          (lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ))
            (measurable_superluminalShiftedDiff ha hlambda.le u t)
            (superluminalBound_nonneg lambda u)
            (norm_superluminalShiftedDiff_le ha hlambda u t)
            (𝓕 (causalPacket u H)))) := by
  classical
  set G := 𝓕 (causalPacket u H) with hG
  have hfour : fourierL2 ℝ (causalPacketMod u H t) = additiveTranslationUnitary (-t) G := by
    rw [fourierL2_eq, causalPacketMod, fourier_fourierPhaseMulUnitary]
  have hmodel := superluminalModelMul_apply lambda u (causalPacketMod u H t)
  have hsub : lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ))
      (measurable_superluminalDiff ha hlambda.le u) (superluminalBound_nonneg lambda u)
      (norm_superluminalDiff_le ha hlambda u)
      = lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ))
          (measurable_superluminalSymbol ha hlambda.le u) (Real.exp_nonneg _)
          (norm_superluminalSymbol_le ha hlambda u)
        - lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ))
          (measurable_superluminalModel lambda u) (Real.exp_nonneg _)
          (fun w => le_of_eq (norm_superluminalModel lambda u w)) :=
    lpBoundedMulCLM_sub _ _ _ _ _ _ _ _ _ (Filter.Eventually.of_forall fun _ => rfl)
  have hshifted : lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ))
      (measurable_superluminalDiff ha hlambda.le u) (superluminalBound_nonneg lambda u)
      (norm_superluminalDiff_le ha hlambda u) (additiveTranslationUnitary (-t) G)
      = additiveTranslationUnitary (-t)
        (lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ))
          (measurable_superluminalShiftedDiff ha hlambda.le u t)
          (superluminalBound_nonneg lambda u)
          (norm_superluminalShiftedDiff_le ha hlambda u t) G) := by
    refine lpBoundedMulCLM_additiveTranslation _ _ _ _ _ (-t) (fun x => ?_) G
    rw [superluminalShiftedDiff, sub_neg_eq_add]
  rw [superluminalDefect, superluminalHalfWave, fourierMulCLM_apply, ← hmodel, ← map_sub,
    ← sub_apply, ← hsub, hfour, hshifted]

theorem norm_superluminalDefect {a lambda : ℝ} (ha : lambda < a) (hlambda : 0 < lambda)
    (u H t : ℝ) :
    ‖superluminalDefect ha hlambda u H t‖
      = ‖lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ))
          (measurable_superluminalShiftedDiff ha hlambda.le u t)
          (superluminalBound_nonneg lambda u)
          (norm_superluminalShiftedDiff_le ha hlambda u t)
          (𝓕 (causalPacket u H))‖ := by
  rw [superluminalDefect_eq ha hlambda u H t, norm_fourierL2inv_apply,
    (additiveTranslationUnitary (-t)).norm_map]

/-- **(24.46) The propagated packet converges to its amplified translate.** -/
theorem tendsto_norm_superluminalDefect {a lambda : ℝ} (ha : lambda < a) (hlambda : 0 < lambda)
    (u H : ℝ) :
    Tendsto (fun t : ℝ => ‖superluminalDefect ha hlambda u H t‖) atBot (nhds 0) := by
  have hbnd : ∀ _w : ℝ, ‖(0 : ℂ)‖ ≤ superluminalBound lambda u := fun _ => by
    rw [norm_zero]
    exact superluminalBound_nonneg lambda u
  have hbase := tendsto_lpBoundedMulCLM_apply (μ := (volume : Measure ℝ))
    (φ := fun t : ℝ => superluminalShiftedDiff a lambda u t) (ψ := fun _ : ℝ => (0 : ℂ))
    (fun t => measurable_superluminalShiftedDiff ha hlambda.le u t)
    (measurable_const (a := (0 : ℂ)))
    (superluminalBound_nonneg lambda u)
    (fun t => norm_superluminalShiftedDiff_le ha hlambda u t)
    hbnd
    (fun w => tendsto_superluminalShiftedDiff ha.le hlambda.le u w)
    (𝓕 (causalPacket u H))
  have hzero := lpBoundedMulCLM_eq_zero (p := 2) (μ := (volume : Measure ℝ))
    (measurable_const (a := (0 : ℂ))) (superluminalBound_nonneg lambda u) hbnd
    (Filter.Eventually.of_forall fun _ => rfl)
  rw [hzero, zero_apply] at hbase
  have hnorm := tendsto_zero_iff_norm_tendsto_zero.1 hbase
  exact hnorm.congr fun t => (norm_superluminalDefect ha hlambda u H t).symm

/-! ## The exact compression law -/

/-- The compression of the gauged massive half-wave to a window. -/
def windowCompression {a lambda : ℝ} (ha : lambda < a) (hlambda : 0 < lambda) (u : ℝ)
    {S : Set ℝ} (hS : MeasurableSet S) : Lp (α := ℝ) ℂ 2 →L[ℂ] Lp (α := ℝ) ℂ 2 :=
  (windowCutoff hS).comp ((superluminalHalfWave ha hlambda u).comp (windowCutoff hS))

theorem norm_windowCompression_le {a lambda : ℝ} (ha : lambda < a) (hlambda : 0 < lambda)
    (u : ℝ) {S : Set ℝ} (hS : MeasurableSet S) :
    ‖windowCompression ha hlambda u hS‖ ≤ Real.exp (|u| * lambda) := by
  have hU : ‖superluminalHalfWave ha hlambda u‖ ≤ Real.exp (|u| * lambda) :=
    norm_fourierMulCLM_le _ _ _
  have hP := norm_windowCutoff_le hS
  have hstep1 : ‖(superluminalHalfWave ha hlambda u).comp (windowCutoff hS)‖
      ≤ Real.exp (|u| * lambda) * 1 := by
    refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
    exact mul_le_mul hU hP (norm_nonneg _) (Real.exp_nonneg _)
  refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
  calc ‖windowCutoff hS‖ * ‖(superluminalHalfWave ha hlambda u).comp (windowCutoff hS)‖
      ≤ 1 * (Real.exp (|u| * lambda) * 1) :=
        mul_le_mul hP hstep1 (norm_nonneg _) zero_le_one
    _ = Real.exp (|u| * lambda) := by ring

/-- **(24.45) The compressed half-wave retains the full radiation norm** as soon as the window
contains both the input interval `(u, H)` and the propagated interval `(0, H - u)`. -/
theorem le_norm_windowCompression {a lambda : ℝ} (ha : lambda < a) (hlambda : 0 < lambda)
    {u H : ℝ} (huH : u < H) {S : Set ℝ} (hS : MeasurableSet S)
    (hin : Set.Ioo u H ⊆ S) (hout : Set.Ioo 0 (H - u) ⊆ S) :
    Real.exp (u * lambda) ≤ ‖windowCompression ha hlambda u hS‖ := by
  have hlim : Tendsto
      (fun t : ℝ => Real.exp (u * lambda) - ‖superluminalDefect ha hlambda u H t‖) atBot
      (nhds (Real.exp (u * lambda))) := by
    have hstep := (tendsto_const_nhds (x := Real.exp (u * lambda))
      (f := (atBot : Filter ℝ))).sub (tendsto_norm_superluminalDefect ha hlambda u H)
    rwa [sub_zero] at hstep
  refine le_of_tendsto hlim (Filter.Eventually.of_forall fun t => ?_)
  have hnorm1 : ‖causalPacketMod u H t‖ = 1 := norm_causalPacketMod huH t
  have happly : windowCompression ha hlambda u hS (causalPacketMod u H t)
      = ((Real.exp (u * lambda) : ℝ) : ℂ) •
          additiveTranslationUnitary u (causalPacketMod u H t)
        + windowCutoff hS (superluminalDefect ha hlambda u H t) := by
    have hsplit : superluminalHalfWave ha hlambda u (causalPacketMod u H t)
        = ((Real.exp (u * lambda) : ℝ) : ℂ) •
            additiveTranslationUnitary u (causalPacketMod u H t)
          + superluminalDefect ha hlambda u H t := by
      rw [superluminalDefect]
      abel
    rw [windowCompression, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      windowCutoff_causalPacketMod hS hin t, hsplit, map_add, map_smul,
      windowCutoff_translated hS hout t]
  have htr : ‖((Real.exp (u * lambda) : ℝ) : ℂ) •
      additiveTranslationUnitary u (causalPacketMod u H t)‖ = Real.exp (u * lambda) := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _),
      (additiveTranslationUnitary u).norm_map, hnorm1, mul_one]
  have hdef : ‖windowCutoff hS (superluminalDefect ha hlambda u H t)‖
      ≤ ‖superluminalDefect ha hlambda u H t‖ := by
    calc ‖windowCutoff hS (superluminalDefect ha hlambda u H t)‖
        ≤ ‖windowCutoff hS‖ * ‖superluminalDefect ha hlambda u H t‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖superluminalDefect ha hlambda u H t‖ :=
          mul_le_mul_of_nonneg_right (norm_windowCutoff_le hS) (norm_nonneg _)
      _ = ‖superluminalDefect ha hlambda u H t‖ := one_mul _
  have hlow : Real.exp (u * lambda) - ‖superluminalDefect ha hlambda u H t‖
      ≤ ‖windowCompression ha hlambda u hS (causalPacketMod u H t)‖ := by
    set A := ((Real.exp (u * lambda) : ℝ) : ℂ) •
      additiveTranslationUnitary u (causalPacketMod u H t) with hA
    set B := windowCutoff hS (superluminalDefect ha hlambda u H t) with hB
    have htri : ‖A‖ ≤ ‖A + B‖ + ‖B‖ := by
      have hstep := norm_sub_le (A + B) B
      rwa [add_sub_cancel_right] at hstep
    rw [happly]
    linarith [htri, htr, hdef]
  have hop : ‖windowCompression ha hlambda u hS (causalPacketMod u H t)‖
      ≤ ‖windowCompression ha hlambda u hS‖ := by
    have hle := ContinuousLinearMap.le_opNorm (windowCompression ha hlambda u hS)
      (causalPacketMod u H t)
    rwa [hnorm1, mul_one] at hle
  linarith

/-! ## The two causal cores -/

/-- The compression to the causal interval `(0, H)`. -/
def causalCompression {a lambda : ℝ} (ha : lambda < a) (hlambda : 0 < lambda) (u H : ℝ) :
    Lp (α := ℝ) ℂ 2 →L[ℂ] Lp (α := ℝ) ℂ 2 :=
  windowCompression ha hlambda u (measurableSet_Ioo (a := (0 : ℝ)) (b := H))

/-- **(24.45)** For every window strictly wider than the propagation distance, the compressed
gauged massive half-wave retains the exact radiation norm `e^{λu}`. -/
theorem norm_causalCompression_eq {a lambda : ℝ} (ha : lambda < a) (hlambda : 0 < lambda)
    {u H : ℝ} (hu : 0 ≤ u) (huH : u < H) :
    ‖causalCompression ha hlambda u H‖ = Real.exp (u * lambda) := by
  have hin : Set.Ioo u H ⊆ Set.Ioo (0 : ℝ) H := by
    intro x hx
    rw [Set.mem_Ioo] at hx ⊢
    exact ⟨lt_of_le_of_lt hu hx.1, hx.2⟩
  have hout : Set.Ioo (0 : ℝ) (H - u) ⊆ Set.Ioo (0 : ℝ) H := by
    intro x hx
    rw [Set.mem_Ioo] at hx ⊢
    exact ⟨hx.1, by linarith [hx.2]⟩
  refine le_antisymm ?_ (le_norm_windowCompression ha hlambda huH _ hin hout)
  have habs : |u| = u := abs_of_nonneg hu
  have hle := norm_windowCompression_le ha hlambda u (measurableSet_Ioo (a := (0 : ℝ)) (b := H))
  rwa [habs] at hle

/-- The compression to the causal half line. -/
def causalHalfLineCompression {a lambda : ℝ} (ha : lambda < a) (hlambda : 0 < lambda) (u : ℝ) :
    Lp (α := ℝ) ℂ 2 →L[ℂ] Lp (α := ℝ) ℂ 2 :=
  windowCompression ha hlambda u (measurableSet_Ioi (a := (0 : ℝ)))

/-- **(24.47)** The causal half-line projection retains the exact radiation norm as well: half-line
support is not corona polarization. -/
theorem norm_causalHalfLineCompression_eq {a lambda : ℝ} (ha : lambda < a) (hlambda : 0 < lambda)
    {u : ℝ} (hu : 0 ≤ u) :
    ‖causalHalfLineCompression ha hlambda u‖ = Real.exp (u * lambda) := by
  have huH : u < u + 1 := by linarith
  have hin : Set.Ioo u (u + 1) ⊆ Set.Ioi (0 : ℝ) := by
    intro x hx
    rw [Set.mem_Ioo] at hx
    exact Set.mem_Ioi.2 (lt_of_le_of_lt hu hx.1)
  have hout : Set.Ioo (0 : ℝ) (u + 1 - u) ⊆ Set.Ioi (0 : ℝ) := by
    intro x hx
    rw [Set.mem_Ioo] at hx
    exact Set.mem_Ioi.2 hx.1
  refine le_antisymm ?_
    (le_norm_windowCompression ha hlambda huH (measurableSet_Ioi (a := (0 : ℝ))) hin hout)
  have habs : |u| = u := abs_of_nonneg hu
  have hle := norm_windowCompression_le ha hlambda u (measurableSet_Ioi (a := (0 : ℝ)))
  rwa [habs] at hle

/-! ## Both exact cores are superluminal -/

/-- **(24.52)** The elementary outgoing cone strictly outruns the light cone. -/
theorem one_lt_outgoingConeSlope {d : ℝ} (hd : 1 / 2 < d) : 1 < d / (d - 1 / 2) := by
  have hpos : 0 < d - 1 / 2 := by linarith
  rw [lt_div_iff₀ hpos]
  linarith

/-- **(24.52)** The sharp Bessel aperture strictly outruns the light cone. -/
theorem one_lt_besselBalanceSlope {a : ℝ} (ha : 1 / 2 < a) :
    1 < a / Real.sqrt (a ^ 2 - 1 / 4) := by
  have hapos : 0 < a := by linarith
  have hrad : 0 < a ^ 2 - 1 / 4 := by nlinarith
  have hsq : 0 < Real.sqrt (a ^ 2 - 1 / 4) := Real.sqrt_pos.2 hrad
  have hlt : Real.sqrt (a ^ 2 - 1 / 4) < a := by
    have hle : Real.sqrt (a ^ 2 - 1 / 4) < Real.sqrt (a ^ 2) := by
      refine Real.sqrt_lt_sqrt hrad.le ?_
      linarith
    rwa [Real.sqrt_sq hapos.le] at hle
  rw [lt_div_iff₀ hsq]
  linarith

end

end RHTower
