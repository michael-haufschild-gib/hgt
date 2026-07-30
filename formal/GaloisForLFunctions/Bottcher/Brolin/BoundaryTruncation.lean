/-
# Böttcher tower — Brolin: boundary truncation estimates

This module is part of the split Brolin/Riesz-measure interface. Import
`GaloisForLFunctions.Bottcher.Brolin` for the full public surface.
-/
import GaloisForLFunctions.Bottcher.Brolin.GapAMuCore

open Filter Topology MeasureTheory CompactlySupported Laplacian
open scoped Laplacian

namespace Bottcher

local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- Disconnected boundary truncation inequality for the constructed limiting
measure.  At points of `K_c`, every positive truncation of the singular
logarithmic kernel has nonpositive limiting integral.  This is the
finite-to-limit half of the remaining monotone singular-kernel passage. -/
theorem integral_truncatedLogKernel_limitingBrolinMeasure_nonpos_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hz : z ∈ filledJulia c)
    {δ : ℝ} (hδ : 0 < δ) :
    ∫ w, truncatedLogKernel z δ w ∂limitingBrolinMeasure c ≤ 0 := by
  have hleft :=
    truncatedLogKernel_preBrolinMeasure_subseq_integral_tendsto_limiting
      c z hδ
  have hneg :=
    neg_logPotential_preBrolinMeasure_limitSubseq_tendsto_zero_filledJulia_of_disconnected
      hc hz
  have hright :
      Tendsto
        (fun k =>
          logPotential (preBrolinMeasure c (brolinLimitSubsequence c k)) z)
        atTop (𝓝 0) := by
    simpa using hneg.neg
  have hdiff := hleft.sub hright
  have hle :
      ∀ᶠ k in atTop,
        ∫ w, truncatedLogKernel z δ w
            ∂preBrolinMeasure c (brolinLimitSubsequence c k) -
          logPotential (preBrolinMeasure c (brolinLimitSubsequence c k)) z ≤ 0 := by
    filter_upwards [eventually_ge_atTop 0] with k _hk
    have hnotAtom :
        (quadratic c)^[brolinLimitSubsequence c k] z ≠ 0 :=
      iterate_ne_zero_of_mem_filledJulia_of_disconnected hc hz
        (brolinLimitSubsequence c k)
    have hineq :=
      integral_truncatedLogKernel_preBrolinMeasure_le_logPotential_of_iterate_ne_zero
        (c := c) (z := z) (δ := δ)
        (n := brolinLimitSubsequence c k) hδ hnotAtom
    linarith
  have hlim := le_of_tendsto hdiff hle
  simpa using hlim

theorem integral_truncatedLogKernel_brolinMu_nonpos_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hz : z ∈ filledJulia c)
    {δ : ℝ} (hδ : 0 < δ) :
    ∫ w, truncatedLogKernel z δ w ∂brolinMu c ≤ 0 := by
  simpa [brolinMu] using
    integral_truncatedLogKernel_limitingBrolinMeasure_nonpos_of_mem_filledJulia_of_disconnected
      hc hz hδ

theorem integral_truncatedLogKernel_brolinMuRieszMeasure_nonpos_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hz : z ∈ filledJulia c)
    {δ : ℝ} (hδ : 0 < δ) :
    ∫ w, truncatedLogKernel z δ w ∂brolinMuRieszMeasure c ≤ 0 := by
  rw [brolinMuRieszMeasure_eq_brolinMu]
  exact integral_truncatedLogKernel_brolinMu_nonpos_of_mem_filledJulia_of_disconnected
    hc hz hδ

theorem integral_truncatedLogKernel_brolinMuRieszMeasure_escapeDisk_lower_bound
    (c : ℂ) {z : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hz : z ∈ escapeDisk c) :
    - Real.log (max δ (2 * max 2 ‖c‖)) ≤
      ∫ w, truncatedLogKernel z δ w ∂brolinMuRieszMeasure c := by
  rw [brolinMuRieszMeasure_eq_brolinMu]
  simpa [brolinMu] using
    integral_truncatedLogKernel_limitingBrolinMeasure_escapeDisk_lower_bound
      c hδ hz

/-- On `K_c` in the disconnected case, every positive truncation of the
constructed Riesz-measure potential is trapped between the fixed escape-disk
diameter lower bound and zero. -/
theorem integral_truncatedLogKernel_brolinMuRieszMeasure_bounds_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hz : z ∈ filledJulia c)
    {δ : ℝ} (hδ : 0 < δ) :
    - Real.log (max δ (2 * max 2 ‖c‖)) ≤
        ∫ w, truncatedLogKernel z δ w ∂brolinMuRieszMeasure c ∧
      ∫ w, truncatedLogKernel z δ w ∂brolinMuRieszMeasure c ≤ 0 := by
  exact ⟨
    integral_truncatedLogKernel_brolinMuRieszMeasure_escapeDisk_lower_bound
      c hδ (mem_escapeDisk_of_mem_filledJulia hz),
    integral_truncatedLogKernel_brolinMuRieszMeasure_nonpos_of_mem_filledJulia_of_disconnected
      hc hz hδ⟩

/-- The shifted limiting measure satisfies the same disconnected boundary
truncation inequality.  This is the shifted version of the singular-kernel
pressure estimate and is proved from the shifted finite subsequence. -/
theorem integral_truncatedLogKernel_shiftedLimitingBrolinMeasure_nonpos_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hz : z ∈ filledJulia c)
    {δ : ℝ} (hδ : 0 < δ) :
    ∫ w, truncatedLogKernel z δ w ∂shiftedLimitingBrolinMeasure c ≤ 0 := by
  have hleft :=
    truncatedLogKernel_preBrolinMeasure_shiftedSubseq_integral_tendsto_shiftedLimiting
      c z hδ
  have hneg :
      Tendsto
        (fun k =>
          - logPotential (preBrolinMeasure c (shiftedBrolinIndex c k)) z)
        atTop (𝓝 0) :=
    (neg_logPotential_preBrolinMeasure_tendsto_zero_filledJulia_of_disconnected
      hc hz).comp (shiftedBrolinIndex_tendsto_atTop c)
  have hright :
      Tendsto
        (fun k =>
          logPotential (preBrolinMeasure c (shiftedBrolinIndex c k)) z)
        atTop (𝓝 0) := by
    simpa using hneg.neg
  have hdiff := hleft.sub hright
  have hle :
      ∀ᶠ k in atTop,
        ∫ w, truncatedLogKernel z δ w
            ∂preBrolinMeasure c (shiftedBrolinIndex c k) -
          logPotential (preBrolinMeasure c (shiftedBrolinIndex c k)) z ≤ 0 := by
    filter_upwards [eventually_ge_atTop 0] with k _hk
    have hnotAtom :
        (quadratic c)^[shiftedBrolinIndex c k] z ≠ 0 :=
      iterate_ne_zero_of_mem_filledJulia_of_disconnected hc hz
        (shiftedBrolinIndex c k)
    have hineq :=
      integral_truncatedLogKernel_preBrolinMeasure_le_logPotential_of_iterate_ne_zero
        (c := c) (z := z) (δ := δ)
        (n := shiftedBrolinIndex c k) hδ hnotAtom
    linarith
  have hlim := le_of_tendsto hdiff hle
  simpa using hlim

/-- Generic compact-carrier lower bound for truncated logarithmic kernels on
the fixed escape disk. -/
theorem integral_truncatedLogKernel_escapeDisk_lower_bound_of_probability
    (c : ℂ) {z : ℂ} {δ : ℝ} (hδ : 0 < δ) (hz : z ∈ escapeDisk c)
    (μK : Measure (escapeDisk c)) [IsProbabilityMeasure μK] :
    - Real.log (max δ (2 * max 2 ‖c‖)) ≤
      ∫ w : escapeDisk c, truncatedLogKernel z δ (w : ℂ) ∂μK := by
  let A : ℝ := - Real.log (max δ (2 * max 2 ‖c‖))
  have hconst : Integrable (fun _ : escapeDisk c => A) μK :=
    integrable_const A
  have hfun :
      Integrable (fun w : escapeDisk c => truncatedLogKernel z δ (w : ℂ)) μK := by
    simpa [truncatedLogKernelOnEscapeDisk] using!
      (truncatedLogKernelOnEscapeDisk c z δ hδ).integrable μK
  have hmono :
      (fun _ : escapeDisk c => A) ≤
        (fun w : escapeDisk c => truncatedLogKernel z δ (w : ℂ)) := by
    intro w
    exact truncatedLogKernel_escapeDisk_lower_bound hδ hz w.2
  have hle := integral_mono hconst hfun hmono
  simpa [A] using hle

/-- Shifted limiting truncated-kernel integrals have the same fixed lower
bound on the escape disk. -/
theorem integral_truncatedLogKernel_shiftedLimitingBrolinMeasure_escapeDisk_lower_bound
    (c : ℂ) {z : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hz : z ∈ escapeDisk c) :
    - Real.log (max δ (2 * max 2 ‖c‖)) ≤
      ∫ w, truncatedLogKernel z δ w ∂shiftedLimitingBrolinMeasure c := by
  rw [integral_truncatedLogKernel_shiftedLimitingBrolinMeasure_eq_integral_escapeDisk
    c z hδ]
  exact integral_truncatedLogKernel_escapeDisk_lower_bound_of_probability
    c hδ hz (shiftedBrolinLimitOnEscapeDisk c : Measure (escapeDisk c))

/-- Shifted boundary truncations are bounded between the escape-disk diameter
lower bound and zero on `K_c` for disconnected parameters. -/
theorem integral_truncatedLogKernel_shiftedLimitingBrolinMeasure_bounds_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hz : z ∈ filledJulia c)
    {δ : ℝ} (hδ : 0 < δ) :
    - Real.log (max δ (2 * max 2 ‖c‖)) ≤
        ∫ w, truncatedLogKernel z δ w ∂shiftedLimitingBrolinMeasure c ∧
      ∫ w, truncatedLogKernel z δ w ∂shiftedLimitingBrolinMeasure c ≤ 0 := by
  exact ⟨
    integral_truncatedLogKernel_shiftedLimitingBrolinMeasure_escapeDisk_lower_bound
      c hδ (mem_escapeDisk_of_mem_filledJulia hz),
    integral_truncatedLogKernel_shiftedLimitingBrolinMeasure_nonpos_of_mem_filledJulia_of_disconnected
      hc hz hδ⟩

/-- Generic escape-disk atomlessness criterion from the boundary truncation
pressure estimate.  This is used for shifted compactness limits without
duplicating the full Brolin atom-pressure proof. -/
theorem escapeDisk_singleton_eq_zero_of_truncatedLogKernel_nonpos
    (c : ℂ) {z : ℂ} (hzK : z ∈ filledJulia c)
    (μK : Measure (escapeDisk c)) [IsProbabilityMeasure μK]
    (hnonpos : ∀ {δ : ℝ}, 0 < δ → δ ≤ 1 →
      ∫ w : escapeDisk c, truncatedLogKernel z δ (w : ℂ) ∂μK ≤ 0) :
    let hz : z ∈ escapeDisk c := mem_escapeDisk_of_mem_filledJulia hzK
    let zz : escapeDisk c := ⟨z, hz⟩
    μK {zz} = 0 := by
  intro hz zz
  by_contra hne
  have hmTop : μK {zz} ≠ ⊤ := measure_ne_top μK {zz}
  let m : ℝ := (μK {zz}).toReal
  have hmpos : 0 < m := ENNReal.toReal_pos hne hmTop
  let C : ℝ := 2 * max 2 ‖c‖
  have hCgt : 1 < C := by
    dsimp [C]
    have hR : (2 : ℝ) ≤ max 2 ‖c‖ := le_max_left _ _
    nlinarith
  have hlogCpos : 0 < Real.log C := Real.log_pos hCgt
  let δ : ℝ := Real.exp (-(Real.log C / m + Real.log C + 1))
  have hδpos : 0 < δ := Real.exp_pos _
  have hδle : δ ≤ 1 := by
    dsimp [δ]
    rw [Real.exp_le_one_iff]
    have hdiv_nonneg : 0 ≤ Real.log C / m :=
      div_nonneg hlogCpos.le hmpos.le
    nlinarith
  let A : ℝ := - Real.log δ
  let B : ℝ := - Real.log C
  let S : Set (escapeDisk c) := {zz}
  have hS : MeasurableSet S := measurableSet_singleton zz
  let atomIndicator : escapeDisk c → ℝ := S.indicator (fun _ => (1 : ℝ))
  have hconst : Integrable (fun _ : escapeDisk c => B) μK :=
    integrable_const B
  have hind : Integrable atomIndicator μK := by
    dsimp [atomIndicator]
    exact (integrable_const (α := escapeDisk c) (μ := μK) (1 : ℝ)).indicator hS
  have hscaled : Integrable (fun w : escapeDisk c => (A - B) * atomIndicator w) μK :=
    hind.const_mul (A - B)
  have hlowerInt :
      Integrable (fun w : escapeDisk c => B + (A - B) * atomIndicator w) μK :=
    hconst.add hscaled
  have htruncInt :
      Integrable (fun w : escapeDisk c => truncatedLogKernel z δ (w : ℂ)) μK := by
    simpa [truncatedLogKernelOnEscapeDisk] using!
      (truncatedLogKernelOnEscapeDisk c z δ hδpos).integrable μK
  have hmono :
      (fun w : escapeDisk c => B + (A - B) * atomIndicator w) ≤
        (fun w : escapeDisk c => truncatedLogKernel z δ (w : ℂ)) := by
    intro w
    simpa [hz, zz, C, A, B, S, atomIndicator] using
      truncatedLogKernel_escapeDisk_atom_lower_bound c hz hδpos hδle w
  have hle := integral_mono hlowerInt htruncInt hmono
  have hlowerIntegral :
      ∫ w : escapeDisk c, B + (A - B) * atomIndicator w ∂μK =
        B + (A - B) * (μK {zz}).toReal := by
    rw [integral_add hconst hscaled]
    rw [integral_const, integral_const_mul]
    have hindint :
        ∫ w : escapeDisk c, atomIndicator w ∂μK =
          (μK {zz}).toReal := by
      rw [show atomIndicator = S.indicator (fun _ => (1 : ℝ)) from rfl]
      rw [integral_indicator_const (1 : ℝ) hS]
      simp [S, measureReal_def]
    rw [hindint]
    simp [measureReal_def]
  have hpress :
      B + (A - B) * (μK {zz}).toReal ≤ 0 :=
    le_trans (by simpa [hlowerIntegral] using hle) (hnonpos hδpos hδle)
  have hden :
      - Real.log δ + Real.log C =
        Real.log C / m + 2 * Real.log C + 1 := by
    dsimp [δ]
    rw [Real.log_exp]
    ring
  have hmass' :
      m ≤ Real.log C / (Real.log C / m + 2 * Real.log C + 1) := by
    have hDpos : 0 < - Real.log δ + Real.log C := by
      have hlogδnonpos : Real.log δ ≤ 0 := Real.log_nonpos hδpos.le hδle
      nlinarith
    rw [← hden, le_div_iff₀ hDpos]
    have hpress' :
        - Real.log C + (- Real.log δ + Real.log C) * m ≤ 0 := by
      simpa [A, B, C, m, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hpress
    nlinarith
  have hdenpos : 0 < Real.log C / m + 2 * Real.log C + 1 := by
    have hdivpos : 0 < Real.log C / m := div_pos hlogCpos hmpos
    nlinarith
  have hlt : Real.log C / (Real.log C / m + 2 * Real.log C + 1) < m := by
    rw [div_lt_iff₀ hdenpos]
    have hmul :
        m * (Real.log C / m + 2 * Real.log C + 1) =
          Real.log C + m * (2 * Real.log C + 1) := by
      field_simp [ne_of_gt hmpos]
      ring
    rw [hmul]
    have htail : 0 < m * (2 * Real.log C + 1) :=
      mul_pos hmpos (by nlinarith)
    nlinarith
  exact (not_lt_of_ge hmass') hlt

/-- Generic boundary ball-pressure estimate on the compact escape-disk carrier.
The same truncation inequality that kills atoms also controls the measure of a
small Euclidean ball around a filled-Julia point. -/
theorem escapeDisk_ball_pressure_of_truncatedLogKernel_nonpos
    (c : ℂ) {z : ℂ} (hzK : z ∈ filledJulia c)
    {δ : ℝ} (hδ : 0 < δ) (hδle : δ ≤ 1)
    (μK : Measure (escapeDisk c)) [IsProbabilityMeasure μK]
    (hnonpos :
      ∫ w : escapeDisk c, truncatedLogKernel z δ (w : ℂ) ∂μK ≤ 0) :
    let S : Set (escapeDisk c) := {w | ‖z - (w : ℂ)‖ < δ}
    let C : ℝ := 2 * max 2 ‖c‖
    let A : ℝ := - Real.log δ
    let B : ℝ := - Real.log C
    B + (A - B) * (μK S).toReal ≤ 0 := by
  intro S C A B
  have hz : z ∈ escapeDisk c := mem_escapeDisk_of_mem_filledJulia hzK
  have hCge : 1 ≤ C := by
    dsimp [C]
    have hR : (2 : ℝ) ≤ max 2 ‖c‖ := le_max_left _ _
    nlinarith
  have hδC : δ ≤ C := le_trans hδle hCge
  have hmaxC : max δ C = C := max_eq_right hδC
  have hSopen : IsOpen S := by
    dsimp [S]
    exact isOpen_lt
      ((continuous_const.sub continuous_subtype_val).norm)
      continuous_const
  have hS : MeasurableSet S := hSopen.measurableSet
  let ballIndicator : escapeDisk c → ℝ := S.indicator (fun _ => (1 : ℝ))
  have hconst : Integrable (fun _ : escapeDisk c => B) μK :=
    integrable_const B
  have hind : Integrable ballIndicator μK := by
    dsimp [ballIndicator]
    exact (integrable_const (α := escapeDisk c) (μ := μK) (1 : ℝ)).indicator hS
  have hscaled : Integrable (fun w : escapeDisk c => (A - B) * ballIndicator w) μK :=
    hind.const_mul (A - B)
  have hlowerInt :
      Integrable (fun w : escapeDisk c => B + (A - B) * ballIndicator w) μK :=
    hconst.add hscaled
  have htruncInt :
      Integrable (fun w : escapeDisk c => truncatedLogKernel z δ (w : ℂ)) μK := by
    simpa [truncatedLogKernelOnEscapeDisk] using!
      (truncatedLogKernelOnEscapeDisk c z δ hδ).integrable μK
  have hmono :
      (fun w : escapeDisk c => B + (A - B) * ballIndicator w) ≤
        (fun w : escapeDisk c => truncatedLogKernel z δ (w : ℂ)) := by
    intro w
    by_cases hw : w ∈ S
    · have hdist_le : ‖z - (w : ℂ)‖ ≤ δ := le_of_lt hw
      have hmax : max δ ‖z - (w : ℂ)‖ = δ := max_eq_left hdist_le
      apply le_of_eq
      calc
        B + (A - B) * ballIndicator w = A := by
          simp [ballIndicator, Set.indicator_of_mem hw]
        _ = truncatedLogKernel z δ (w : ℂ) := by
          simp [truncatedLogKernel, A, hmax]
    · have hlower :=
        truncatedLogKernel_escapeDisk_lower_bound
          (c := c) (z := z) (w := (w : ℂ)) hδ hz w.2
      rw [hmaxC] at hlower
      calc
        B + (A - B) * ballIndicator w = B := by
          simp [ballIndicator, Set.indicator_of_notMem hw]
        _ ≤ truncatedLogKernel z δ (w : ℂ) := by
          simpa [B, C] using hlower
  have hle := integral_mono hlowerInt htruncInt hmono
  have hlowerIntegral :
      ∫ w : escapeDisk c, B + (A - B) * ballIndicator w ∂μK =
        B + (A - B) * (μK S).toReal := by
    rw [integral_add hconst hscaled]
    rw [integral_const, integral_const_mul]
    have hindint :
        ∫ w : escapeDisk c, ballIndicator w ∂μK =
          (μK S).toReal := by
      rw [show ballIndicator = S.indicator (fun _ => (1 : ℝ)) from rfl]
      rw [integral_indicator_const (1 : ℝ) hS]
      simp [S, measureReal_def]
    rw [hindint]
    simp [measureReal_def]
  exact le_trans (by simpa [hlowerIntegral] using hle) hnonpos

/-- Generic explicit small-ball mass bound extracted from the boundary
truncation pressure estimate on the compact escape-disk carrier. -/
theorem escapeDisk_ball_mass_le_of_truncatedLogKernel_nonpos
    (c : ℂ) {z : ℂ} (hzK : z ∈ filledJulia c)
    {δ : ℝ} (hδ : 0 < δ) (hδle : δ ≤ 1)
    (μK : Measure (escapeDisk c)) [IsProbabilityMeasure μK]
    (hnonpos :
      ∫ w : escapeDisk c, truncatedLogKernel z δ (w : ℂ) ∂μK ≤ 0) :
    let S : Set (escapeDisk c) := {w | ‖z - (w : ℂ)‖ < δ}
    let C : ℝ := 2 * max 2 ‖c‖
    (μK S).toReal ≤
      Real.log C / (- Real.log δ + Real.log C) := by
  intro S C
  have hpress :=
    escapeDisk_ball_pressure_of_truncatedLogKernel_nonpos
      (c := c) (z := z) hzK hδ hδle μK hnonpos
  dsimp at hpress
  have hCgt : 1 < C := by
    dsimp [C]
    have hR : (2 : ℝ) ≤ max 2 ‖c‖ := le_max_left _ _
    nlinarith
  have hlogCpos : 0 < Real.log C := Real.log_pos hCgt
  have hlogδnonpos : Real.log δ ≤ 0 := Real.log_nonpos hδ.le hδle
  have hDpos : 0 < - Real.log δ + Real.log C := by
    nlinarith
  rw [le_div_iff₀ hDpos]
  nlinarith

/-- Shifted compact-carrier small-ball mass bound near any filled-Julia point.
This is the shifted analogue of the unshifted boundary ball-pressure estimate. -/
theorem shiftedBrolinLimitOnEscapeDisk_ball_mass_le_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c)
    {δ : ℝ} (hδ : 0 < δ) (hδle : δ ≤ 1) :
    let μK : Measure (escapeDisk c) :=
      (shiftedBrolinLimitOnEscapeDisk c : Measure (escapeDisk c))
    let S : Set (escapeDisk c) := {w | ‖z - (w : ℂ)‖ < δ}
    let C : ℝ := 2 * max 2 ‖c‖
    (μK S).toReal ≤
      Real.log C / (- Real.log δ + Real.log C) := by
  intro μK S C
  haveI : IsProbabilityMeasure μK := by
    dsimp [μK]
    infer_instance
  have hnonpos :
      ∫ w : escapeDisk c, truncatedLogKernel z δ (w : ℂ) ∂μK ≤ 0 := by
    have hplane :=
      integral_truncatedLogKernel_shiftedLimitingBrolinMeasure_nonpos_of_mem_filledJulia_of_disconnected
        (c := c) (z := z) hc hzK hδ
    rw [integral_truncatedLogKernel_shiftedLimitingBrolinMeasure_eq_integral_escapeDisk
      c z hδ] at hplane
    simpa [μK] using hplane
  have hmass :=
    escapeDisk_ball_mass_le_of_truncatedLogKernel_nonpos
      (c := c) (z := z) hzK hδ hδle μK hnonpos
  dsimp at hmass
  simpa [S, C] using hmass

theorem shiftedLimitingBrolinMeasure_ball_mass_le_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c)
    {δ : ℝ} (hδ : 0 < δ) (hδle : δ ≤ 1) :
    let S : Set ℂ := {w | ‖z - w‖ < δ}
    let C : ℝ := 2 * max 2 ‖c‖
    (shiftedLimitingBrolinMeasure c S).toReal ≤
      Real.log C / (- Real.log δ + Real.log C) := by
  intro S C
  have hS : MeasurableSet S := by
    dsimp [S]
    exact (isOpen_lt ((continuous_const.sub continuous_id).norm) continuous_const).measurableSet
  have hcarrier :=
    shiftedBrolinLimitOnEscapeDisk_ball_mass_le_of_mem_filledJulia_of_disconnected
      (c := c) (z := z) hc hzK hδ hδle
  dsimp at hcarrier
  rw [shiftedLimitingBrolinMeasure, Measure.map_apply measurable_subtype_coe hS]
  simpa [S, C] using hcarrier

/-- Shifted small-ball mass bound at the antipodal singularity `w = -z`.  This
is the estimate needed for the second term `logKernel z (-w)` in the quadratic
boundary kernel split. -/
theorem shiftedLimitingBrolinMeasure_antipodal_ball_mass_le_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c)
    {δ : ℝ} (hδ : 0 < δ) (hδle : δ ≤ 1) :
    let S : Set ℂ := {w | ‖z + w‖ < δ}
    let C : ℝ := 2 * max 2 ‖c‖
    (shiftedLimitingBrolinMeasure c S).toReal ≤
      Real.log C / (- Real.log δ + Real.log C) := by
  intro S C
  have hnegK : -z ∈ filledJulia c := (mem_filledJulia_neg_iff c z).2 hzK
  have hmass :=
    shiftedLimitingBrolinMeasure_ball_mass_le_of_mem_filledJulia_of_disconnected
      (c := c) (z := -z) hc hnegK hδ hδle
  dsimp at hmass
  have hS :
      ({w : ℂ | ‖-z - w‖ < δ}) = S := by
    ext w
    have hnorm : ‖-z - w‖ = ‖z + w‖ := by
      rw [show -z - w = -(z + w) by ring, norm_neg]
    simp [S, hnorm]
  simpa [S, C, hS] using hmass

theorem shiftedBrolinLimitOnEscapeDisk_singleton_eq_zero_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c) :
    let hz : z ∈ escapeDisk c := mem_escapeDisk_of_mem_filledJulia hzK
    let zz : escapeDisk c := ⟨z, hz⟩
    (shiftedBrolinLimitOnEscapeDisk c : Measure (escapeDisk c)) {zz} = 0 := by
  intro hz zz
  have hgeneric :=
    escapeDisk_singleton_eq_zero_of_truncatedLogKernel_nonpos
    (c := c) (z := z) hzK
    (shiftedBrolinLimitOnEscapeDisk c : Measure (escapeDisk c))
    (by
      intro δ hδ _hδle
      have hplane :=
        integral_truncatedLogKernel_shiftedLimitingBrolinMeasure_nonpos_of_mem_filledJulia_of_disconnected
          (c := c) (z := z) hc hzK hδ
      rw [integral_truncatedLogKernel_shiftedLimitingBrolinMeasure_eq_integral_escapeDisk
        c z hδ] at hplane
      simpa using hplane)
  simpa [hz, zz] using hgeneric

theorem shiftedLimitingBrolinMeasure_singleton_eq_zero_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c) :
    shiftedLimitingBrolinMeasure c {z} = 0 := by
  have hz : z ∈ escapeDisk c := mem_escapeDisk_of_mem_filledJulia hzK
  let zz : escapeDisk c := ⟨z, hz⟩
  rw [shiftedLimitingBrolinMeasure, Measure.map_apply measurable_subtype_coe
    (measurableSet_singleton z)]
  have hpre :
      ((fun w : escapeDisk c => (w : ℂ)) ⁻¹' ({z} : Set ℂ)) =
        ({zz} : Set (escapeDisk c)) := by
    ext w
    constructor
    · intro hw
      exact Subtype.ext hw
    · intro hw
      rw [hw]
      rfl
  rw [hpre]
  exact shiftedBrolinLimitOnEscapeDisk_singleton_eq_zero_of_mem_filledJulia_of_disconnected
    hc hzK

/-- For the shifted limiting measure, positive truncations at a boundary point
are a.e. below the true logarithmic kernel. -/
theorem ae_truncatedLogKernel_le_logKernel_shiftedLimitingBrolinMeasure_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᵐ w ∂shiftedLimitingBrolinMeasure c,
      truncatedLogKernel z δ w ≤ logKernel z w := by
  have hzero :
      shiftedLimitingBrolinMeasure c (({z} : Set ℂ)ᶜ)ᶜ = 0 := by
    simpa using
      shiftedLimitingBrolinMeasure_singleton_eq_zero_of_mem_filledJulia_of_disconnected
        hc hzK
  have hne_ae : ∀ᵐ w ∂shiftedLimitingBrolinMeasure c, w ∈ ({z} : Set ℂ)ᶜ :=
    (mem_ae_iff).2 hzero
  filter_upwards [hne_ae] with w hw
  exact truncatedLogKernel_le_logKernel_of_ne hδ (fun hzw => hw hzw.symm)

/-- Finite-integral tail inequality for the shifted boundary kernel.  Once the
true boundary kernel is integrable, every small positive truncation integrates
below the actual shifted logarithmic potential; the remaining value passage is
therefore exactly a singular-tail control problem. -/
theorem integral_truncatedLogKernel_shiftedLimitingBrolinMeasure_le_logPotential_of_integrable
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c)
    {δ : ℝ} (hδ : 0 < δ) (hδle : δ ≤ 1)
    (hint :
      Integrable (fun w => logKernel z w)
        (shiftedLimitingBrolinMeasure c)) :
    ∫ w, truncatedLogKernel z δ w ∂shiftedLimitingBrolinMeasure c ≤
      logPotential (shiftedLimitingBrolinMeasure c) z := by
  let ν : Measure ℂ := shiftedLimitingBrolinMeasure c
  have hzero :
      ν (({z} : Set ℂ)ᶜ)ᶜ = 0 := by
    dsimp [ν]
    simpa using
      shiftedLimitingBrolinMeasure_singleton_eq_zero_of_mem_filledJulia_of_disconnected
        (c := c) (z := z) hc hzK
  have hne_ae : ∀ᵐ w ∂ν, w ∈ ({z} : Set ℂ)ᶜ :=
    (mem_ae_iff).2 hzero
  have htruncInt :
      Integrable (fun w => truncatedLogKernel z δ w) ν := by
    have hnorm :
        ∀ᵐ w ∂ν, ‖truncatedLogKernel z δ w‖ ≤ ‖logKernel z w‖ := by
      filter_upwards [hne_ae] with w hw
      exact norm_truncatedLogKernel_le_norm_logKernel_of_ne_of_le_one
        hδ hδle (fun hzw => hw hzw.symm)
    exact hint.mono
      ((continuous_truncatedLogKernel (z := z) hδ).aestronglyMeasurable)
      (by simpa [ν] using hnorm)
  have hmono :
      (fun w => truncatedLogKernel z δ w) ≤ᵐ[ν]
        fun w => logKernel z w := by
    dsimp [ν]
    exact
      ae_truncatedLogKernel_le_logKernel_shiftedLimitingBrolinMeasure_of_mem_filledJulia_of_disconnected
        (c := c) (z := z) hc hzK hδ
  have hle := integral_mono_ae htruncInt (by simpa [ν] using hint) hmono
  simpa [ν, logPotential] using hle

/-- For a finite shifted boundary kernel, the standard shrinking truncations
converge to the actual shifted logarithmic potential.  This names the
dominated-convergence singular-kernel passage used by the hDisc boundary
problem. -/
theorem integral_truncatedLogKernel_shiftedLimitingBrolinMeasure_inv_nat_tendsto_logPotential_of_integrable
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c)
    (hint :
      Integrable (fun w => logKernel z w)
        (shiftedLimitingBrolinMeasure c)) :
    Tendsto
      (fun n : ℕ =>
        ∫ w, truncatedLogKernel z (((n + 1 : ℕ) : ℝ)⁻¹) w
          ∂shiftedLimitingBrolinMeasure c)
      atTop (𝓝 (logPotential (shiftedLimitingBrolinMeasure c) z)) := by
  have hzero :
      shiftedLimitingBrolinMeasure c (({z} : Set ℂ)ᶜ)ᶜ = 0 := by
    simpa using
      shiftedLimitingBrolinMeasure_singleton_eq_zero_of_mem_filledJulia_of_disconnected
        (c := c) (z := z) hc hzK
  have hne_ae :
      ∀ᵐ w ∂shiftedLimitingBrolinMeasure c, w ∈ ({z} : Set ℂ)ᶜ :=
    (mem_ae_iff).2 hzero
  unfold logPotential
  refine tendsto_integral_of_dominated_convergence
    (fun w => ‖logKernel z w‖) ?_ hint.norm ?_ ?_
  · intro n
    exact (continuous_truncatedLogKernel
      (z := z) (δ := (((n + 1 : ℕ) : ℝ)⁻¹))
      (by positivity)).aestronglyMeasurable
  · intro n
    have hδle : (((n + 1 : ℕ) : ℝ)⁻¹) ≤ 1 := by
      have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      exact inv_le_one_of_one_le₀ hn
    filter_upwards [hne_ae] with w hw
    exact norm_truncatedLogKernel_le_norm_logKernel_of_ne_of_le_one
      (by positivity) hδle (fun hzw => hw hzw.symm)
  · filter_upwards [hne_ae] with w hw
    exact truncatedLogKernel_inv_nat_succ_tendsto_logKernel_of_ne
      (fun hzw => hw hzw.symm)

/-- For the shifted limiting measure, positive truncations at the antipodal
boundary singularity are a.e. below the true antipodal logarithmic kernel. -/
theorem ae_truncatedLogKernel_neg_right_le_logKernel_neg_right_shiftedLimitingBrolinMeasure_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᵐ w ∂shiftedLimitingBrolinMeasure c,
      truncatedLogKernel z δ (-w) ≤ logKernel z (-w) := by
  have hnegK : -z ∈ filledJulia c := (mem_filledJulia_neg_iff c z).2 hzK
  have hzero :
      shiftedLimitingBrolinMeasure c (({-z} : Set ℂ)ᶜ)ᶜ = 0 := by
    simpa using
      shiftedLimitingBrolinMeasure_singleton_eq_zero_of_mem_filledJulia_of_disconnected
        (c := c) (z := -z) hc hnegK
  have hne_ae : ∀ᵐ w ∂shiftedLimitingBrolinMeasure c, w ∈ ({-z} : Set ℂ)ᶜ :=
    (mem_ae_iff).2 hzero
  filter_upwards [hne_ae] with w hw
  exact truncatedLogKernel_le_logKernel_of_ne hδ (by
    intro hzw
    have hw_eq : w = -z := by
      rw [hzw, neg_neg]
    exact hw hw_eq)

/-- Under the shifted limiting measure, the quadratic pullback of the
logarithmic kernel splits almost everywhere into the two antipodal kernels. -/
theorem ae_logKernel_quadratic_eq_add_shiftedLimitingBrolinMeasure_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c) :
    ∀ᵐ w ∂shiftedLimitingBrolinMeasure c,
      logKernel (quadratic c z) (quadratic c w) =
        logKernel z w + logKernel z (-w) := by
  have hzero_z :
      shiftedLimitingBrolinMeasure c (({z} : Set ℂ)ᶜ)ᶜ = 0 := by
    simpa using
      shiftedLimitingBrolinMeasure_singleton_eq_zero_of_mem_filledJulia_of_disconnected
        hc hzK
  have hne_z : ∀ᵐ w ∂shiftedLimitingBrolinMeasure c, w ∈ ({z} : Set ℂ)ᶜ :=
    (mem_ae_iff).2 hzero_z
  have hnegK : -z ∈ filledJulia c := (mem_filledJulia_neg_iff c z).2 hzK
  have hzero_neg :
      shiftedLimitingBrolinMeasure c (({-z} : Set ℂ)ᶜ)ᶜ = 0 := by
    simpa using
      shiftedLimitingBrolinMeasure_singleton_eq_zero_of_mem_filledJulia_of_disconnected
        hc hnegK
  have hne_neg : ∀ᵐ w ∂shiftedLimitingBrolinMeasure c, w ∈ ({-z} : Set ℂ)ᶜ :=
    (mem_ae_iff).2 hzero_neg
  filter_upwards [hne_z, hne_neg] with w hwz hwneg
  exact logKernel_quadratic_eq_add
    (c := c) (z := z) (w := w)
    (fun hzw => hwz hzw.symm)
    (fun hznw => by
      have hw_eq : w = -z := by
        rw [hznw, neg_neg]
      exact hwneg hw_eq)

/-- Antipodal symmetry of the shifted limit transfers logarithmic-kernel
integrability from a boundary point to its antipodal kernel. -/
theorem integrable_logKernel_neg_right_shiftedLimitingBrolinMeasure
    {c z : ℂ}
    (hzint :
      Integrable (fun w => logKernel z w) (shiftedLimitingBrolinMeasure c)) :
    Integrable (fun w => logKernel z (-w)) (shiftedLimitingBrolinMeasure c) := by
  let ν : Measure ℂ := shiftedLimitingBrolinMeasure c
  have hmap : Measure.map Neg.neg ν = ν := by
    simpa [ν] using map_shiftedLimitingBrolinMeasure_neg c
  have hzmap : Integrable (fun w => logKernel z w) (Measure.map Neg.neg ν) := by
    rw [hmap]
    exact hzint
  simpa [ν] using!
    (integrable_map_measure
      (logKernel_aestronglyMeasurable z (Measure.map Neg.neg ν))
      continuous_neg.measurable.aemeasurable).1 hzmap

/-- Antipodal symmetry of the shifted limit makes the antipodal kernel integral
equal to the original kernel integral. -/
theorem integral_logKernel_neg_right_shiftedLimitingBrolinMeasure_eq
    (c z : ℂ) :
    ∫ w, logKernel z (-w) ∂shiftedLimitingBrolinMeasure c =
      ∫ w, logKernel z w ∂shiftedLimitingBrolinMeasure c := by
  let ν : Measure ℂ := shiftedLimitingBrolinMeasure c
  calc
    ∫ w, logKernel z (-w) ∂shiftedLimitingBrolinMeasure c
        = ∫ w, logKernel z (-w) ∂ν := by rfl
    _ = ∫ w, logKernel z w ∂Measure.map Neg.neg ν := by
          rw [integral_map]
          · exact continuous_neg.measurable.aemeasurable
          · exact logKernel_aestronglyMeasurable z (Measure.map Neg.neg ν)
    _ = ∫ w, logKernel z w ∂shiftedLimitingBrolinMeasure c := by
          rw [show ν = shiftedLimitingBrolinMeasure c from rfl,
            map_shiftedLimitingBrolinMeasure_neg c]

/-- The shifted limiting potential is even under `z ↦ -z`. -/
theorem logPotential_shiftedLimitingBrolinMeasure_neg_eq
    (c z : ℂ) :
    logPotential (shiftedLimitingBrolinMeasure c) (-z) =
      logPotential (shiftedLimitingBrolinMeasure c) z := by
  calc
    logPotential (shiftedLimitingBrolinMeasure c) (-z)
        = ∫ w, logKernel z (-w) ∂shiftedLimitingBrolinMeasure c := by
          unfold logPotential
          refine integral_congr_ae ?_
          exact Filter.Eventually.of_forall
            (fun w => (logKernel_neg_right z w).symm)
    _ = logPotential (shiftedLimitingBrolinMeasure c) z := by
          rw [integral_logKernel_neg_right_shiftedLimitingBrolinMeasure_eq]
          rfl

/-- The quadratic-composed kernel is integrable against the shifted limiting
measure as soon as the two antipodal boundary kernels are. -/
theorem integrable_logKernel_quadratic_comp_shiftedLimitingBrolinMeasure_of_antipodal
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c)
    (hzint :
      Integrable (fun w => logKernel z w) (shiftedLimitingBrolinMeasure c))
    (hnegRightInt :
      Integrable (fun w => logKernel z (-w)) (shiftedLimitingBrolinMeasure c)) :
    Integrable
      (fun w => logKernel (quadratic c z) (quadratic c w))
      (shiftedLimitingBrolinMeasure c) := by
  refine (hzint.add hnegRightInt).congr ?_
  filter_upwards
    [ae_logKernel_quadratic_eq_add_shiftedLimitingBrolinMeasure_of_mem_filledJulia_of_disconnected
      hc hzK] with w hsplit
  exact hsplit.symm

/-- The quadratic-composed kernel is integrable against the shifted limiting
measure as soon as the original boundary kernel is; antipodal integrability is
supplied by shifted antipodal symmetry. -/
theorem integrable_logKernel_quadratic_comp_shiftedLimitingBrolinMeasure
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c)
    (hzint :
      Integrable (fun w => logKernel z w) (shiftedLimitingBrolinMeasure c)) :
    Integrable
      (fun w => logKernel (quadratic c z) (quadratic c w))
      (shiftedLimitingBrolinMeasure c) :=
  integrable_logKernel_quadratic_comp_shiftedLimitingBrolinMeasure_of_antipodal
    (c := c) (z := z) hc hzK hzint
    (integrable_logKernel_neg_right_shiftedLimitingBrolinMeasure hzint)

/-- The target-side logarithmic kernel at `f_c z` is integrable against
`μ_c` whenever the two shifted antipodal boundary kernels at `z` are
integrable.  This removes the separate `μ_c` integrability premise from the
quadratic boundary potential identity. -/
theorem integrable_logKernel_gapAMu_quadratic_of_shifted_antipodal
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c)
    (hzint :
      Integrable (fun w => logKernel z w) (shiftedLimitingBrolinMeasure c))
    (hnegRightInt :
      Integrable (fun w => logKernel z (-w)) (shiftedLimitingBrolinMeasure c)) :
    Integrable (fun y => logKernel (quadratic c z) y) (gapAMu c) := by
  have hcomp :
      Integrable
        (fun w => logKernel (quadratic c z) (quadratic c w))
        (shiftedLimitingBrolinMeasure c) :=
    integrable_logKernel_quadratic_comp_shiftedLimitingBrolinMeasure_of_antipodal
      (c := c) (z := z) hc hzK hzint hnegRightInt
  rw [← map_shiftedLimitingBrolinMeasure_quadratic_eq_gapAMu c]
  exact (integrable_map_measure
    (logKernel_aestronglyMeasurable (quadratic c z)
      (Measure.map (quadratic c) (shiftedLimitingBrolinMeasure c)))
    (continuous_quadratic c).measurable.aemeasurable).2 hcomp

/-- The target-side logarithmic kernel at `f_c z` is integrable against `μ_c`
as soon as the original shifted boundary kernel at `z` is integrable. -/
theorem integrable_logKernel_gapAMu_quadratic_of_shifted
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c)
    (hzint :
      Integrable (fun w => logKernel z w) (shiftedLimitingBrolinMeasure c)) :
    Integrable (fun y => logKernel (quadratic c z) y) (gapAMu c) :=
  integrable_logKernel_gapAMu_quadratic_of_shifted_antipodal
    (c := c) (z := z) hc hzK hzint
    (integrable_logKernel_neg_right_shiftedLimitingBrolinMeasure hzint)

/-- The shifted limiting measure is carried by the filled Julia set, in the
`∀ᵐ` form used by pointwise lower-bound arguments. -/
theorem ae_mem_filledJulia_shiftedLimitingBrolinMeasure (c : ℂ) :
    ∀ᵐ w ∂shiftedLimitingBrolinMeasure c, w ∈ filledJulia c := by
  exact (mem_ae_iff).2 (shiftedLimitingBrolinMeasure_filledJulia_compl c)

/-- If the split antipodal logarithmic kernel is integrable against the shifted
limit, then the original branch is integrable.  The point is that both branches
have a uniform escape-disk lower bound on the support, so after adding the
diameter constant they are nonnegative and integrability of the sum separates. -/
theorem integrable_logKernel_shiftedLimitingBrolinMeasure_of_integrable_add_neg_right
    {c z : ℂ} (hzK : z ∈ filledJulia c)
    (hadd :
      Integrable
        (fun w => logKernel z w + logKernel z (-w))
        (shiftedLimitingBrolinMeasure c)) :
    Integrable
      (fun w => logKernel z w)
      (shiftedLimitingBrolinMeasure c) := by
  let ν : Measure ℂ := shiftedLimitingBrolinMeasure c
  let D : ℝ := Real.log (2 * max 2 ‖c‖)
  haveI : IsProbabilityMeasure ν := by
    dsimp [ν]
    exact instIsProbabilityMeasure_shiftedLimitingBrolinMeasure c
  have hzEsc : z ∈ escapeDisk c := mem_escapeDisk_of_mem_filledJulia hzK
  have hsupport : ∀ᵐ w ∂ν, w ∈ filledJulia c := by
    dsimp [ν]
    exact ae_mem_filledJulia_shiftedLimitingBrolinMeasure c
  have hf_nonneg :
      0 ≤ᵐ[ν] fun w => logKernel z w + D := by
    filter_upwards [hsupport] with w hwK
    have hwEsc : w ∈ escapeDisk c := mem_escapeDisk_of_mem_filledJulia hwK
    have hfloor : -D ≤ logKernel z w := by
      dsimp [D]
      exact logKernel_escapeDisk_lower_bound hzEsc hwEsc
    have hnonneg : (0 : ℝ) ≤ logKernel z w + D := by linarith
    simpa using hnonneg
  have hg_nonneg :
      0 ≤ᵐ[ν] fun w => logKernel z (-w) + D := by
    filter_upwards [hsupport] with w hwK
    have hnegK : -w ∈ filledJulia c := (mem_filledJulia_neg_iff c w).2 hwK
    have hnegEsc : -w ∈ escapeDisk c := mem_escapeDisk_of_mem_filledJulia hnegK
    have hfloor : -D ≤ logKernel z (-w) := by
      dsimp [D]
      exact logKernel_escapeDisk_lower_bound hzEsc hnegEsc
    have hnonneg : (0 : ℝ) ≤ logKernel z (-w) + D := by linarith
    simpa using hnonneg
  have hshifted_sum :
      Integrable
        (fun w => (logKernel z w + logKernel z (-w)) + 2 * D)
        ν := by
    have hconst : Integrable (fun _ : ℂ => 2 * D) ν := integrable_const _
    have haddν :
        Integrable (fun w => logKernel z w + logKernel z (-w)) ν := by
      simpa [ν] using hadd
    simpa [Pi.add_apply] using! haddν.add hconst
  have hbranch_sum :
      Integrable
        ((fun w => logKernel z w + D) +
          (fun w => logKernel z (-w) + D))
        ν := by
    refine hshifted_sum.congr ?_
    filter_upwards with w
    simp only [Pi.add_apply]
    ring
  have hf_meas :
      AEStronglyMeasurable (fun w => logKernel z w + D) ν :=
    (logKernel_aestronglyMeasurable z ν).add aestronglyMeasurable_const
  have hf_shift :
      Integrable (fun w => logKernel z w + D) ν :=
    integrable_left_of_integrable_add_of_nonneg
      (μ := ν) hf_meas hf_nonneg hg_nonneg hbranch_sum
  have hplain :
      Integrable (fun w => logKernel z w) ν := by
    exact (integrable_add_const_iff.mp hf_shift)
  dsimp [ν] at hplain
  exact hplain

/-- Converse integrability transfer for the quadratic GAP-A pushforward:
target-side integrability at `f_c z` forces integrability of the shifted branch
at `z`. -/
theorem integrable_logKernel_shiftedLimitingBrolinMeasure_of_gapAMu_quadratic
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c)
    (hμint :
      Integrable (fun y => logKernel (quadratic c z) y) (gapAMu c)) :
    Integrable
      (fun w => logKernel z w)
      (shiftedLimitingBrolinMeasure c) := by
  let ν : Measure ℂ := shiftedLimitingBrolinMeasure c
  have hmapint :
      Integrable (fun y => logKernel (quadratic c z) y)
        (Measure.map (quadratic c) ν) := by
    dsimp [ν]
    rw [map_shiftedLimitingBrolinMeasure_quadratic_eq_gapAMu]
    exact hμint
  have hcomp :
      Integrable
        (fun w => logKernel (quadratic c z) (quadratic c w))
        ν := by
    exact
      (integrable_map_measure
        (logKernel_aestronglyMeasurable (quadratic c z)
          (Measure.map (quadratic c) ν))
        (continuous_quadratic c).measurable.aemeasurable).1 hmapint
  have hsum :
      Integrable
        (fun w => logKernel z w + logKernel z (-w))
        ν := by
    refine hcomp.congr ?_
    dsimp [ν]
    exact ae_logKernel_quadratic_eq_add_shiftedLimitingBrolinMeasure_of_mem_filledJulia_of_disconnected
      (c := c) (z := z) hc hzK
  dsimp [ν] at hsum ⊢
  exact integrable_logKernel_shiftedLimitingBrolinMeasure_of_integrable_add_neg_right
    (c := c) (z := z) hzK hsum

/-- Shifted boundary-kernel core for hDisc: the shifted compactness limit is a
probability on `K_c`, has the exterior Green potential, pushes forward to
`μ_c`, has no boundary atoms, satisfies the shifted truncation pressure
estimate, and obeys the quadratic kernel splitting almost everywhere. -/
theorem shiftedLimitingBrolinMeasure_hDiscBoundaryKernelCore
    {c : ℂ} (hc : Disconnected c) :
    IsProbOn (shiftedLimitingBrolinMeasure c) (filledJulia c) ∧
      (∀ z : ℂ, z ∉ filledJulia c →
        greenFunctionDyn c z =
          - logPotential (shiftedLimitingBrolinMeasure c) z) ∧
      (∀ φ : C_c(ℂ, ℝ),
        ∫ z, φ (quadratic c z) ∂shiftedLimitingBrolinMeasure c =
          ∫ z, φ z ∂gapAMu c) ∧
      (∀ z : ℂ, ∀ {δ : ℝ}, 0 < δ →
        ∫ w, truncatedLogKernel z δ (quadratic c w)
            ∂shiftedLimitingBrolinMeasure c =
          ∫ w, truncatedLogKernel z δ w ∂gapAMu c) ∧
      (∀ z : ℂ, z ∈ filledJulia c →
        shiftedLimitingBrolinMeasure c {z} = 0) ∧
      (∀ z : ℂ, z ∈ filledJulia c → ∀ {δ : ℝ}, 0 < δ →
        ∫ w, truncatedLogKernel z δ w ∂shiftedLimitingBrolinMeasure c ≤ 0) ∧
      (∀ z : ℂ, z ∈ filledJulia c →
        Integrable (fun w => logKernel z w) (shiftedLimitingBrolinMeasure c) →
        Integrable (fun w => logKernel z (-w)) (shiftedLimitingBrolinMeasure c) →
        Integrable
          (fun w => logKernel (quadratic c z) (quadratic c w))
          (shiftedLimitingBrolinMeasure c)) ∧
      (∀ z : ℂ, z ∈ filledJulia c →
        Integrable (fun w => logKernel z w) (shiftedLimitingBrolinMeasure c) →
        Integrable (fun w => logKernel z (-w)) (shiftedLimitingBrolinMeasure c) →
        Integrable (fun y => logKernel (quadratic c z) y) (gapAMu c)) ∧
      ∀ z : ℂ, z ∈ filledJulia c →
        ∀ᵐ w ∂shiftedLimitingBrolinMeasure c,
          logKernel (quadratic c z) (quadratic c w) =
            logKernel z w + logKernel z (-w) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact shiftedLimitingBrolinMeasure_isProbOn_filledJulia c
  · intro z hz
    exact green_eq_neg_logPotential_shiftedLimitingBrolinMeasure_on_basin hz
  · intro φ
    exact shiftedLimitingBrolinMeasure_quadratic_test_integral_eq_gapAMu c φ
  · intro z δ hδ
    exact shiftedLimitingBrolinMeasure_truncatedLogKernel_comp_quadratic_integral_eq_gapAMu
      c z hδ
  · intro z hz
    exact shiftedLimitingBrolinMeasure_singleton_eq_zero_of_mem_filledJulia_of_disconnected
      hc hz
  · intro z hz δ hδ
    exact integral_truncatedLogKernel_shiftedLimitingBrolinMeasure_nonpos_of_mem_filledJulia_of_disconnected
      hc hz hδ
  · intro z hz hzint hnegRightInt
    exact
      integrable_logKernel_quadratic_comp_shiftedLimitingBrolinMeasure_of_antipodal
        hc hz hzint hnegRightInt
  · intro z hz hzint hnegRightInt
    exact
      integrable_logKernel_gapAMu_quadratic_of_shifted_antipodal
        hc hz hzint hnegRightInt
  · intro z hz
    exact ae_logKernel_quadratic_eq_add_shiftedLimitingBrolinMeasure_of_mem_filledJulia_of_disconnected
      hc hz

/-- Integral form of the shifted quadratic kernel split, under the precise
integrability assumptions for the two antipodal boundary kernels. -/
theorem integral_logKernel_quadratic_comp_shiftedLimitingBrolinMeasure_eq_add
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c)
    (hzint :
      Integrable (fun w => logKernel z w) (shiftedLimitingBrolinMeasure c))
    (hnegint :
      Integrable (fun w => logKernel z (-w)) (shiftedLimitingBrolinMeasure c)) :
    ∫ w, logKernel (quadratic c z) (quadratic c w)
        ∂shiftedLimitingBrolinMeasure c =
      ∫ w, logKernel z w ∂shiftedLimitingBrolinMeasure c +
        ∫ w, logKernel z (-w) ∂shiftedLimitingBrolinMeasure c := by
  calc
    ∫ w, logKernel (quadratic c z) (quadratic c w)
        ∂shiftedLimitingBrolinMeasure c
        = ∫ w, logKernel z w + logKernel z (-w)
            ∂shiftedLimitingBrolinMeasure c := by
          exact integral_congr_ae
            (ae_logKernel_quadratic_eq_add_shiftedLimitingBrolinMeasure_of_mem_filledJulia_of_disconnected
              hc hzK)
    _ = ∫ w, logKernel z w ∂shiftedLimitingBrolinMeasure c +
          ∫ w, logKernel z (-w) ∂shiftedLimitingBrolinMeasure c := by
        rw [integral_add hzint hnegint]

/-- Antipodal symmetry collapses the shifted quadratic kernel split to twice
the original shifted kernel integral. -/
theorem integral_logKernel_quadratic_comp_shiftedLimitingBrolinMeasure_eq_two
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c)
    (hzint :
      Integrable (fun w => logKernel z w) (shiftedLimitingBrolinMeasure c)) :
    ∫ w, logKernel (quadratic c z) (quadratic c w)
        ∂shiftedLimitingBrolinMeasure c =
      2 * ∫ w, logKernel z w ∂shiftedLimitingBrolinMeasure c := by
  have hnegint :
      Integrable (fun w => logKernel z (-w)) (shiftedLimitingBrolinMeasure c) :=
    integrable_logKernel_neg_right_shiftedLimitingBrolinMeasure hzint
  calc
    ∫ w, logKernel (quadratic c z) (quadratic c w)
        ∂shiftedLimitingBrolinMeasure c
        = ∫ w, logKernel z w ∂shiftedLimitingBrolinMeasure c +
            ∫ w, logKernel z (-w) ∂shiftedLimitingBrolinMeasure c :=
          integral_logKernel_quadratic_comp_shiftedLimitingBrolinMeasure_eq_add
            hc hzK hzint hnegint
    _ = ∫ w, logKernel z w ∂shiftedLimitingBrolinMeasure c +
          ∫ w, logKernel z w ∂shiftedLimitingBrolinMeasure c := by
        rw [integral_logKernel_neg_right_shiftedLimitingBrolinMeasure_eq]
    _ = 2 * ∫ w, logKernel z w ∂shiftedLimitingBrolinMeasure c := by
        ring

/-- Integral form of `logKernel_neg_right`. -/
theorem integral_logKernel_neg_right_eq_logPotential_neg
    (μ : Measure ℂ) (z : ℂ) :
    ∫ w, logKernel z (-w) ∂μ = logPotential μ (-z) := by
  unfold logPotential
  refine integral_congr_ae ?_
  exact Filter.Eventually.of_forall (fun w => logKernel_neg_right z w)

/-- Potential form of the shifted quadratic kernel split: under the exact
integrability assumptions for the two shifted boundary kernels, the quadratic
pullback integral is the sum of the shifted potentials at `z` and `-z`. -/
theorem integral_logKernel_quadratic_comp_shiftedLimitingBrolinMeasure_eq_potential_add
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c)
    (hzint :
      Integrable (fun w => logKernel z w) (shiftedLimitingBrolinMeasure c))
    (hnegRightInt :
      Integrable (fun w => logKernel z (-w)) (shiftedLimitingBrolinMeasure c)) :
    ∫ w, logKernel (quadratic c z) (quadratic c w)
        ∂shiftedLimitingBrolinMeasure c =
      logPotential (shiftedLimitingBrolinMeasure c) z +
        logPotential (shiftedLimitingBrolinMeasure c) (-z) := by
  rw [integral_logKernel_quadratic_comp_shiftedLimitingBrolinMeasure_eq_add
    (c := c) (z := z) hc hzK hzint hnegRightInt]
  rw [integral_logKernel_neg_right_eq_logPotential_neg]
  rfl

/-- Potential form of the shifted quadratic kernel split after antipodal
symmetry: the quadratic pullback integral is `2 U_ν(z)`. -/
theorem integral_logKernel_quadratic_comp_shiftedLimitingBrolinMeasure_eq_two_potential
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c)
    (hzint :
      Integrable (fun w => logKernel z w) (shiftedLimitingBrolinMeasure c)) :
    ∫ w, logKernel (quadratic c z) (quadratic c w)
        ∂shiftedLimitingBrolinMeasure c =
      2 * logPotential (shiftedLimitingBrolinMeasure c) z := by
  rw [integral_logKernel_quadratic_comp_shiftedLimitingBrolinMeasure_eq_two
    hc hzK hzint]
  rfl

/-- Boundary singular-kernel passage for the shifted limiting measure,
upper-potential side. -/
theorem logPotential_shiftedLimitingBrolinMeasure_nonpos_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c) :
    logPotential (shiftedLimitingBrolinMeasure c) z ≤ 0 := by
  by_cases hint : Integrable (fun w => logKernel z w) (shiftedLimitingBrolinMeasure c)
  · have hzero :
        shiftedLimitingBrolinMeasure c (({z} : Set ℂ)ᶜ)ᶜ = 0 := by
      simpa using
        shiftedLimitingBrolinMeasure_singleton_eq_zero_of_mem_filledJulia_of_disconnected
          hc hzK
    have hne_ae : ∀ᵐ w ∂shiftedLimitingBrolinMeasure c, w ∈ ({z} : Set ℂ)ᶜ :=
      (mem_ae_iff).2 hzero
    have hlim :
        Tendsto
          (fun n : ℕ =>
            ∫ w, truncatedLogKernel z (((n + 1 : ℕ) : ℝ)⁻¹) w
              ∂shiftedLimitingBrolinMeasure c)
          atTop (𝓝 (logPotential (shiftedLimitingBrolinMeasure c) z)) := by
      unfold logPotential
      refine tendsto_integral_of_dominated_convergence
        (fun w => ‖logKernel z w‖) ?_ hint.norm ?_ ?_
      · intro n
        exact (continuous_truncatedLogKernel
          (z := z) (δ := (((n + 1 : ℕ) : ℝ)⁻¹))
          (by positivity)).aestronglyMeasurable
      · intro n
        have hδle : (((n + 1 : ℕ) : ℝ)⁻¹) ≤ 1 := by
          have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
            exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
          exact inv_le_one_of_one_le₀ hn
        filter_upwards [hne_ae] with w hw
        exact norm_truncatedLogKernel_le_norm_logKernel_of_ne_of_le_one
          (by positivity) hδle (fun hzw => hw hzw.symm)
      · filter_upwards [hne_ae] with w hw
        exact truncatedLogKernel_inv_nat_succ_tendsto_logKernel_of_ne
          (fun hzw => hw hzw.symm)
    have hnonpos :
        ∀ n : ℕ,
          ∫ w, truncatedLogKernel z (((n + 1 : ℕ) : ℝ)⁻¹) w
              ∂shiftedLimitingBrolinMeasure c ≤ 0 := by
      intro n
      exact
        integral_truncatedLogKernel_shiftedLimitingBrolinMeasure_nonpos_of_mem_filledJulia_of_disconnected
          hc hzK (by positivity)
    exact le_of_tendsto hlim (Filter.Eventually.of_forall hnonpos)
  · have hzero : logPotential (shiftedLimitingBrolinMeasure c) z = 0 := by
      unfold logPotential
      exact integral_undef hint
    rw [hzero]

/-- Boundary singular-kernel passage for the shifted limiting measure,
lower-potential side. -/
theorem logPotential_shiftedLimitingBrolinMeasure_lower_bound_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c) :
    - Real.log (2 * max 2 ‖c‖) ≤
      logPotential (shiftedLimitingBrolinMeasure c) z := by
  let C : ℝ := 2 * max 2 ‖c‖
  have hCge : 1 ≤ C := by
    dsimp [C]
    have hR : (2 : ℝ) ≤ max 2 ‖c‖ := le_max_left _ _
    nlinarith
  have hlogCnonneg : 0 ≤ Real.log C := Real.log_nonneg hCge
  by_cases hint : Integrable (fun w => logKernel z w) (shiftedLimitingBrolinMeasure c)
  · have hzero :
        shiftedLimitingBrolinMeasure c (({z} : Set ℂ)ᶜ)ᶜ = 0 := by
      simpa using
        shiftedLimitingBrolinMeasure_singleton_eq_zero_of_mem_filledJulia_of_disconnected
          hc hzK
    have hne_ae : ∀ᵐ w ∂shiftedLimitingBrolinMeasure c, w ∈ ({z} : Set ℂ)ᶜ :=
      (mem_ae_iff).2 hzero
    have hlim :
        Tendsto
          (fun n : ℕ =>
            ∫ w, truncatedLogKernel z (((n + 1 : ℕ) : ℝ)⁻¹) w
              ∂shiftedLimitingBrolinMeasure c)
          atTop (𝓝 (logPotential (shiftedLimitingBrolinMeasure c) z)) := by
      unfold logPotential
      refine tendsto_integral_of_dominated_convergence
        (fun w => ‖logKernel z w‖) ?_ hint.norm ?_ ?_
      · intro n
        exact (continuous_truncatedLogKernel
          (z := z) (δ := (((n + 1 : ℕ) : ℝ)⁻¹))
          (by positivity)).aestronglyMeasurable
      · intro n
        have hδle : (((n + 1 : ℕ) : ℝ)⁻¹) ≤ 1 := by
          have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
            exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
          exact inv_le_one_of_one_le₀ hn
        filter_upwards [hne_ae] with w hw
        exact norm_truncatedLogKernel_le_norm_logKernel_of_ne_of_le_one
          (by positivity) hδle (fun hzw => hw hzw.symm)
      · filter_upwards [hne_ae] with w hw
        exact truncatedLogKernel_inv_nat_succ_tendsto_logKernel_of_ne
          (fun hzw => hw hzw.symm)
    have hlower :
        ∀ n : ℕ,
          - Real.log C ≤
            ∫ w, truncatedLogKernel z (((n + 1 : ℕ) : ℝ)⁻¹) w
              ∂shiftedLimitingBrolinMeasure c := by
      intro n
      have hδ : 0 < (((n + 1 : ℕ) : ℝ)⁻¹) := by positivity
      have hδleC : (((n + 1 : ℕ) : ℝ)⁻¹) ≤ C := by
        have hδle1 : (((n + 1 : ℕ) : ℝ)⁻¹) ≤ 1 := by
          have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
            exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
          exact inv_le_one_of_one_le₀ hn
        exact le_trans hδle1 hCge
      have hbounds :=
        integral_truncatedLogKernel_shiftedLimitingBrolinMeasure_bounds_of_mem_filledJulia_of_disconnected
          (c := c) (z := z) hc hzK hδ
      have hbounds' := hbounds.1
      rwa [show max (((n + 1 : ℕ) : ℝ)⁻¹) C = C from max_eq_right hδleC] at hbounds'
    exact ge_of_tendsto hlim (Filter.Eventually.of_forall hlower)
  · have hzero : logPotential (shiftedLimitingBrolinMeasure c) z = 0 := by
      unfold logPotential
      exact integral_undef hint
    rw [hzero]
    exact neg_nonpos.mpr hlogCnonneg

/-- Boundary potential bounds for the shifted limiting measure. -/
theorem logPotential_shiftedLimitingBrolinMeasure_bounds_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c) :
    - Real.log (2 * max 2 ‖c‖) ≤
        logPotential (shiftedLimitingBrolinMeasure c) z ∧
      logPotential (shiftedLimitingBrolinMeasure c) z ≤ 0 := by
  exact ⟨
    logPotential_shiftedLimitingBrolinMeasure_lower_bound_of_mem_filledJulia_of_disconnected
      (c := c) (z := z) hc hzK,
    logPotential_shiftedLimitingBrolinMeasure_nonpos_of_mem_filledJulia_of_disconnected
      (c := c) (z := z) hc hzK⟩

/-- Shifted hDisc boundary-potential core: the shifted limiting measure has
the exterior potential identity, the quadratic pushforward bridge to `μ_c`,
no atoms on `K_c`, the shifted truncation pressure, the true boundary
potential bounds, and the quadratic kernel split almost everywhere. -/
theorem shiftedLimitingBrolinMeasure_hDiscBoundaryPotentialCore
    {c : ℂ} (hc : Disconnected c) :
    IsProbOn (shiftedLimitingBrolinMeasure c) (filledJulia c) ∧
      (∀ z : ℂ, z ∉ filledJulia c →
        greenFunctionDyn c z =
          - logPotential (shiftedLimitingBrolinMeasure c) z) ∧
      (∀ φ : C_c(ℂ, ℝ),
        ∫ z, φ (quadratic c z) ∂shiftedLimitingBrolinMeasure c =
          ∫ z, φ z ∂gapAMu c) ∧
      (∀ z : ℂ, ∀ {δ : ℝ}, 0 < δ →
        ∫ w, truncatedLogKernel z δ (quadratic c w)
            ∂shiftedLimitingBrolinMeasure c =
          ∫ w, truncatedLogKernel z δ w ∂gapAMu c) ∧
      (∀ z : ℂ, z ∈ filledJulia c →
        shiftedLimitingBrolinMeasure c {z} = 0) ∧
      (∀ z : ℂ, z ∈ filledJulia c → ∀ {δ : ℝ}, 0 < δ →
        - Real.log (max δ (2 * max 2 ‖c‖)) ≤
            ∫ w, truncatedLogKernel z δ w ∂shiftedLimitingBrolinMeasure c ∧
          ∫ w, truncatedLogKernel z δ w ∂shiftedLimitingBrolinMeasure c ≤ 0) ∧
      (∀ z : ℂ, z ∈ filledJulia c →
        - Real.log (2 * max 2 ‖c‖) ≤
            logPotential (shiftedLimitingBrolinMeasure c) z ∧
          logPotential (shiftedLimitingBrolinMeasure c) z ≤ 0) ∧
      (∀ z : ℂ, z ∈ filledJulia c →
        Integrable (fun w => logKernel z w) (shiftedLimitingBrolinMeasure c) →
        Integrable (fun w => logKernel z (-w)) (shiftedLimitingBrolinMeasure c) →
        Integrable
          (fun w => logKernel (quadratic c z) (quadratic c w))
          (shiftedLimitingBrolinMeasure c)) ∧
      (∀ z : ℂ, z ∈ filledJulia c →
        Integrable (fun w => logKernel z w) (shiftedLimitingBrolinMeasure c) →
        Integrable (fun w => logKernel z (-w)) (shiftedLimitingBrolinMeasure c) →
        Integrable (fun y => logKernel (quadratic c z) y) (gapAMu c)) ∧
      ∀ z : ℂ, z ∈ filledJulia c →
        ∀ᵐ w ∂shiftedLimitingBrolinMeasure c,
          logKernel (quadratic c z) (quadratic c w) =
            logKernel z w + logKernel z (-w) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact shiftedLimitingBrolinMeasure_isProbOn_filledJulia c
  · intro z hz
    exact green_eq_neg_logPotential_shiftedLimitingBrolinMeasure_on_basin hz
  · intro φ
    exact shiftedLimitingBrolinMeasure_quadratic_test_integral_eq_gapAMu c φ
  · intro z δ hδ
    exact shiftedLimitingBrolinMeasure_truncatedLogKernel_comp_quadratic_integral_eq_gapAMu
      c z hδ
  · intro z hz
    exact shiftedLimitingBrolinMeasure_singleton_eq_zero_of_mem_filledJulia_of_disconnected
      hc hz
  · intro z hz δ hδ
    exact integral_truncatedLogKernel_shiftedLimitingBrolinMeasure_bounds_of_mem_filledJulia_of_disconnected
      hc hz hδ
  · intro z hz
    exact logPotential_shiftedLimitingBrolinMeasure_bounds_of_mem_filledJulia_of_disconnected
      hc hz
  · intro z hz hzint hnegRightInt
    exact
      integrable_logKernel_quadratic_comp_shiftedLimitingBrolinMeasure_of_antipodal
        hc hz hzint hnegRightInt
  · intro z hz hzint hnegRightInt
    exact
      integrable_logKernel_gapAMu_quadratic_of_shifted_antipodal
        hc hz hzint hnegRightInt
  · intro z hz
    exact ae_logKernel_quadratic_eq_add_shiftedLimitingBrolinMeasure_of_mem_filledJulia_of_disconnected
      hc hz

end Bottcher
