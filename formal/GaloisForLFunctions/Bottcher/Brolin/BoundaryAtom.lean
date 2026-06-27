/-
# Böttcher tower — Brolin: boundary atom and mass estimates

This module is part of the split Brolin/Riesz-measure interface. Import
`GaloisForLFunctions.Bottcher.Brolin` for the full public surface.
-/
import GaloisForLFunctions.Bottcher.Brolin.BoundaryTruncation

open Filter Topology MeasureTheory CompactlySupported Laplacian
open scoped Laplacian

namespace Bottcher

local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- Boundary atom-pressure estimate on the compact carrier.  If the limiting
measure put mass at a filled-Julia point, the boundary truncation inequality
would force the displayed singleton-mass bound for every `0 < δ ≤ 1`. -/
theorem brolinLimitOnEscapeDisk_atom_pressure_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c)
    {δ : ℝ} (hδ : 0 < δ) (hδle : δ ≤ 1) :
    let hz : z ∈ escapeDisk c := mem_escapeDisk_of_mem_filledJulia hzK
    let zz : escapeDisk c := ⟨z, hz⟩
    let μK : Measure (escapeDisk c) :=
      (brolinLimitOnEscapeDisk c : Measure (escapeDisk c))
    let C : ℝ := 2 * max 2 ‖c‖
    let A : ℝ := - Real.log δ
    let B : ℝ := - Real.log C
    B + (A - B) * (μK {zz}).toReal ≤ 0 := by
  intro hz zz μK C A B
  haveI : IsProbabilityMeasure μK := by
    dsimp [μK]
    infer_instance
  have hnonpos :
      ∫ w : escapeDisk c, truncatedLogKernel z δ (w : ℂ) ∂μK ≤ 0 := by
    have hplane :=
      integral_truncatedLogKernel_limitingBrolinMeasure_nonpos_of_mem_filledJulia_of_disconnected
        hc hzK hδ
    rw [integral_truncatedLogKernel_limitingBrolinMeasure_eq_integral_escapeDisk
      c z hδ] at hplane
    simpa [μK] using hplane
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
    simpa [truncatedLogKernelOnEscapeDisk, μK] using
      (truncatedLogKernelOnEscapeDisk c z δ hδ).integrable μK
  have hmono :
      (fun w : escapeDisk c => B + (A - B) * atomIndicator w) ≤
        (fun w : escapeDisk c => truncatedLogKernel z δ (w : ℂ)) := by
    intro w
    simpa [hz, zz, C, A, B, S, atomIndicator] using
      truncatedLogKernel_escapeDisk_atom_lower_bound c hz hδ hδle w
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
  exact le_trans (by simpa [hlowerIntegral] using hle) hnonpos

/-- Explicit singleton-mass bound obtained from boundary atom pressure.  As
`δ ↓ 0`, the right side tends to zero; the follow-up atomlessness step is
therefore reduced to a one-variable real squeeze. -/
theorem brolinLimitOnEscapeDisk_atom_mass_le_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c)
    {δ : ℝ} (hδ : 0 < δ) (hδle : δ ≤ 1) :
    let hz : z ∈ escapeDisk c := mem_escapeDisk_of_mem_filledJulia hzK
    let zz : escapeDisk c := ⟨z, hz⟩
    let μK : Measure (escapeDisk c) :=
      (brolinLimitOnEscapeDisk c : Measure (escapeDisk c))
    let C : ℝ := 2 * max 2 ‖c‖
    (μK {zz}).toReal ≤
      Real.log C / (- Real.log δ + Real.log C) := by
  intro hz zz μK C
  have hpress :=
    brolinLimitOnEscapeDisk_atom_pressure_of_mem_filledJulia_of_disconnected
      (c := c) (z := z) hc hzK hδ hδle
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

/-- Boundary ball-pressure estimate on the compact carrier.  The same
truncation inequality that kills atoms also controls the limiting mass in
every sufficiently small Euclidean ball around a filled-Julia point. -/
theorem brolinLimitOnEscapeDisk_ball_pressure_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c)
    {δ : ℝ} (hδ : 0 < δ) (hδle : δ ≤ 1) :
    let μK : Measure (escapeDisk c) :=
      (brolinLimitOnEscapeDisk c : Measure (escapeDisk c))
    let S : Set (escapeDisk c) := {w | ‖z - (w : ℂ)‖ < δ}
    let C : ℝ := 2 * max 2 ‖c‖
    let A : ℝ := - Real.log δ
    let B : ℝ := - Real.log C
    B + (A - B) * (μK S).toReal ≤ 0 := by
  intro μK S C A B
  have hz : z ∈ escapeDisk c := mem_escapeDisk_of_mem_filledJulia hzK
  haveI : IsProbabilityMeasure μK := by
    dsimp [μK]
    infer_instance
  have hCge : 1 ≤ C := by
    dsimp [C]
    have hR : (2 : ℝ) ≤ max 2 ‖c‖ := le_max_left _ _
    nlinarith
  have hδC : δ ≤ C := le_trans hδle hCge
  have hmaxC : max δ C = C := max_eq_right hδC
  have hnonpos :
      ∫ w : escapeDisk c, truncatedLogKernel z δ (w : ℂ) ∂μK ≤ 0 := by
    have hplane :=
      integral_truncatedLogKernel_limitingBrolinMeasure_nonpos_of_mem_filledJulia_of_disconnected
        hc hzK hδ
    rw [integral_truncatedLogKernel_limitingBrolinMeasure_eq_integral_escapeDisk
      c z hδ] at hplane
    simpa [μK] using hplane
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
    simpa [truncatedLogKernelOnEscapeDisk, μK] using
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

/-- Explicit small-ball mass bound near any filled-Julia point.  As `δ ↓ 0`,
the right side tends to zero; this is the uniform-integrability pressure
needed for the remaining boundary singular-potential lower semicontinuity. -/
theorem brolinLimitOnEscapeDisk_ball_mass_le_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c)
    {δ : ℝ} (hδ : 0 < δ) (hδle : δ ≤ 1) :
    let μK : Measure (escapeDisk c) :=
      (brolinLimitOnEscapeDisk c : Measure (escapeDisk c))
    let S : Set (escapeDisk c) := {w | ‖z - (w : ℂ)‖ < δ}
    let C : ℝ := 2 * max 2 ‖c‖
    (μK S).toReal ≤
      Real.log C / (- Real.log δ + Real.log C) := by
  intro μK S C
  have hpress :=
    brolinLimitOnEscapeDisk_ball_pressure_of_mem_filledJulia_of_disconnected
      (c := c) (z := z) hc hzK hδ hδle
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

theorem limitingBrolinMeasure_ball_mass_le_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c)
    {δ : ℝ} (hδ : 0 < δ) (hδle : δ ≤ 1) :
    let S : Set ℂ := {w | ‖z - w‖ < δ}
    let C : ℝ := 2 * max 2 ‖c‖
    (limitingBrolinMeasure c S).toReal ≤
      Real.log C / (- Real.log δ + Real.log C) := by
  intro S C
  have hS : MeasurableSet S := by
    dsimp [S]
    exact (isOpen_lt ((continuous_const.sub continuous_id).norm) continuous_const).measurableSet
  have hcarrier :=
    brolinLimitOnEscapeDisk_ball_mass_le_of_mem_filledJulia_of_disconnected
      (c := c) (z := z) hc hzK hδ hδle
  dsimp at hcarrier
  rw [limitingBrolinMeasure, Measure.map_apply measurable_subtype_coe hS]
  simpa [S, C] using hcarrier

theorem gapAMu_ball_mass_le_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c)
    {δ : ℝ} (hδ : 0 < δ) (hδle : δ ≤ 1) :
    let S : Set ℂ := {w | ‖z - w‖ < δ}
    let C : ℝ := 2 * max 2 ‖c‖
    (gapAMu c S).toReal ≤
      Real.log C / (- Real.log δ + Real.log C) := by
  intro S C
  rw [gapAMu_eq_brolinMu, brolinMu]
  exact limitingBrolinMeasure_ball_mass_le_of_mem_filledJulia_of_disconnected
    (c := c) (z := z) hc hzK hδ hδle

/-- Closed-ball version of the compact-carrier pressure estimate.  This is
the portmanteau-ready form: weak limits control closed sets from above. -/
theorem brolinLimitOnEscapeDisk_closedBall_pressure_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c)
    {δ : ℝ} (hδ : 0 < δ) (hδle : δ ≤ 1) :
    let μK : Measure (escapeDisk c) :=
      (brolinLimitOnEscapeDisk c : Measure (escapeDisk c))
    let S : Set (escapeDisk c) := {w | ‖z - (w : ℂ)‖ ≤ δ}
    let C : ℝ := 2 * max 2 ‖c‖
    let A : ℝ := - Real.log δ
    let B : ℝ := - Real.log C
    B + (A - B) * (μK S).toReal ≤ 0 := by
  intro μK S C A B
  have hz : z ∈ escapeDisk c := mem_escapeDisk_of_mem_filledJulia hzK
  haveI : IsProbabilityMeasure μK := by
    dsimp [μK]
    infer_instance
  have hCge : 1 ≤ C := by
    dsimp [C]
    have hR : (2 : ℝ) ≤ max 2 ‖c‖ := le_max_left _ _
    nlinarith
  have hδC : δ ≤ C := le_trans hδle hCge
  have hmaxC : max δ C = C := max_eq_right hδC
  have hnonpos :
      ∫ w : escapeDisk c, truncatedLogKernel z δ (w : ℂ) ∂μK ≤ 0 := by
    have hplane :=
      integral_truncatedLogKernel_limitingBrolinMeasure_nonpos_of_mem_filledJulia_of_disconnected
        hc hzK hδ
    rw [integral_truncatedLogKernel_limitingBrolinMeasure_eq_integral_escapeDisk
      c z hδ] at hplane
    simpa [μK] using hplane
  have hSclosed : IsClosed S := by
    dsimp [S]
    exact isClosed_le
      ((continuous_const.sub continuous_subtype_val).norm)
      continuous_const
  have hS : MeasurableSet S := hSclosed.measurableSet
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
    simpa [truncatedLogKernelOnEscapeDisk, μK] using
      (truncatedLogKernelOnEscapeDisk c z δ hδ).integrable μK
  have hmono :
      (fun w : escapeDisk c => B + (A - B) * ballIndicator w) ≤
        (fun w : escapeDisk c => truncatedLogKernel z δ (w : ℂ)) := by
    intro w
    by_cases hw : w ∈ S
    · have hdist_le : ‖z - (w : ℂ)‖ ≤ δ := by
        simpa [S] using hw
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

/-- Explicit closed-small-ball mass bound on the compact carrier. -/
theorem brolinLimitOnEscapeDisk_closedBall_mass_le_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c)
    {δ : ℝ} (hδ : 0 < δ) (hδle : δ ≤ 1) :
    let μK : Measure (escapeDisk c) :=
      (brolinLimitOnEscapeDisk c : Measure (escapeDisk c))
    let S : Set (escapeDisk c) := {w | ‖z - (w : ℂ)‖ ≤ δ}
    let C : ℝ := 2 * max 2 ‖c‖
    (μK S).toReal ≤
      Real.log C / (- Real.log δ + Real.log C) := by
  intro μK S C
  have hpress :=
    brolinLimitOnEscapeDisk_closedBall_pressure_of_mem_filledJulia_of_disconnected
      (c := c) (z := z) hc hzK hδ hδle
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

theorem limitingBrolinMeasure_closedBall_mass_le_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c)
    {δ : ℝ} (hδ : 0 < δ) (hδle : δ ≤ 1) :
    let S : Set ℂ := {w | ‖z - w‖ ≤ δ}
    let C : ℝ := 2 * max 2 ‖c‖
    (limitingBrolinMeasure c S).toReal ≤
      Real.log C / (- Real.log δ + Real.log C) := by
  intro S C
  have hS : MeasurableSet S := by
    dsimp [S]
    exact (isClosed_le
      ((continuous_const.sub continuous_id).norm)
      continuous_const).measurableSet
  have hcarrier :=
    brolinLimitOnEscapeDisk_closedBall_mass_le_of_mem_filledJulia_of_disconnected
      (c := c) (z := z) hc hzK hδ hδle
  dsimp at hcarrier
  rw [limitingBrolinMeasure, Measure.map_apply measurable_subtype_coe hS]
  simpa [S, C] using hcarrier

theorem gapAMu_closedBall_mass_le_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c)
    {δ : ℝ} (hδ : 0 < δ) (hδle : δ ≤ 1) :
    let S : Set ℂ := {w | ‖z - w‖ ≤ δ}
    let C : ℝ := 2 * max 2 ‖c‖
    (gapAMu c S).toReal ≤
      Real.log C / (- Real.log δ + Real.log C) := by
  intro S C
  rw [gapAMu_eq_brolinMu, brolinMu]
  exact limitingBrolinMeasure_closedBall_mass_le_of_mem_filledJulia_of_disconnected
    (c := c) (z := z) hc hzK hδ hδle

/-- Portmanteau transfer of the closed-ball logarithmic pressure bound to the
finite compact-carrier measures along the chosen Brolin subsequence. -/
theorem eventually_preBrolinMeasureOnEscapeDisk_subseq_closedBall_toReal_le_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c)
    {δ η : ℝ} (hδ : 0 < δ) (hδle : δ ≤ 1) (hη : 0 < η) :
    let S : Set (escapeDisk c) := {w | ‖z - (w : ℂ)‖ ≤ δ}
    let C : ℝ := 2 * max 2 ‖c‖
    ∀ᶠ k in atTop,
      (preBrolinMeasureOnEscapeDisk c (brolinLimitSubsequence c k) S).toReal ≤
        Real.log C / (- Real.log δ + Real.log C) + η := by
  intro S C
  let B : ℝ := Real.log C / (- Real.log δ + Real.log C)
  have hCgt : 1 < C := by
    dsimp [C]
    have hR : (2 : ℝ) ≤ max 2 ‖c‖ := le_max_left _ _
    nlinarith
  have hlogCpos : 0 < Real.log C := Real.log_pos hCgt
  have hlogδnonpos : Real.log δ ≤ 0 := Real.log_nonpos hδ.le hδle
  have hDpos : 0 < - Real.log δ + Real.log C := by
    nlinarith
  have hBnonneg : 0 ≤ B := by
    dsimp [B]
    exact div_nonneg hlogCpos.le hDpos.le
  have hBηpos : 0 < B + η := add_pos_of_nonneg_of_pos hBnonneg hη
  have hSclosed : IsClosed S := by
    dsimp [S]
    exact isClosed_le
      ((continuous_const.sub continuous_subtype_val).norm)
      continuous_const
  have hlimsup :
      atTop.limsup
          (fun k =>
            (preBrolinProbabilityOnEscapeDisk c (brolinLimitSubsequence c k) :
              Measure (escapeDisk c)) S) ≤
        (brolinLimitOnEscapeDisk c : Measure (escapeDisk c)) S :=
    ProbabilityMeasure.limsup_measure_closed_le_of_tendsto
      (preBrolinProbabilityOnEscapeDisk_subseq_tendsto c) hSclosed
  have hlimitMass :=
    brolinLimitOnEscapeDisk_closedBall_mass_le_of_mem_filledJulia_of_disconnected
      (c := c) (z := z) hc hzK hδ hδle
  dsimp [B] at hlimitMass
  have hlimit_ne_top :
      (brolinLimitOnEscapeDisk c : Measure (escapeDisk c)) S ≠ ⊤ :=
    measure_ne_top (brolinLimitOnEscapeDisk c : Measure (escapeDisk c)) S
  have hlimit_le_ofReal :
      (brolinLimitOnEscapeDisk c : Measure (escapeDisk c)) S ≤ ENNReal.ofReal B :=
    (ENNReal.le_ofReal_iff_toReal_le hlimit_ne_top hBnonneg).2 (by
      simpa [S, C, B] using hlimitMass)
  have hlimsup_le_ofReal :
      atTop.limsup
          (fun k =>
            (preBrolinProbabilityOnEscapeDisk c (brolinLimitSubsequence c k) :
              Measure (escapeDisk c)) S) ≤ ENNReal.ofReal B :=
    hlimsup.trans hlimit_le_ofReal
  have hgap :
      ENNReal.ofReal B < ENNReal.ofReal (B + η) := by
    rw [ENNReal.ofReal_lt_ofReal_iff hBηpos]
    exact lt_add_of_pos_right B hη
  have hevent :
      ∀ᶠ k in atTop,
        (preBrolinProbabilityOnEscapeDisk c (brolinLimitSubsequence c k) :
          Measure (escapeDisk c)) S < ENNReal.ofReal (B + η) :=
    eventually_lt_of_limsup_lt (lt_of_le_of_lt hlimsup_le_ofReal hgap)
  filter_upwards [hevent] with k hk
  exact ENNReal.toReal_le_of_le_ofReal hBηpos.le (by
    exact le_of_lt (by simpa [preBrolinProbabilityOnEscapeDisk] using hk))

/-- Plane version of the finite closed-ball mass estimate obtained from the
compact-carrier portmanteau transfer. -/
theorem eventually_preBrolinMeasure_subseq_closedBall_toReal_le_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c)
    {δ η : ℝ} (hδ : 0 < δ) (hδle : δ ≤ 1) (hη : 0 < η) :
    let S : Set ℂ := {w | ‖z - w‖ ≤ δ}
    let C : ℝ := 2 * max 2 ‖c‖
    ∀ᶠ k in atTop,
      (preBrolinMeasure c (brolinLimitSubsequence c k) S).toReal ≤
        Real.log C / (- Real.log δ + Real.log C) + η := by
  intro S C
  let SK : Set (escapeDisk c) := {w | ‖z - (w : ℂ)‖ ≤ δ}
  have hS : MeasurableSet S := by
    dsimp [S]
    exact (isClosed_le
      ((continuous_const.sub continuous_id).norm)
      continuous_const).measurableSet
  have hpreimage :
      ((fun w : escapeDisk c => (w : ℂ)) ⁻¹' S) = SK := by
    ext w
    simp [S, SK]
  have hcarrier :=
    eventually_preBrolinMeasureOnEscapeDisk_subseq_closedBall_toReal_le_of_mem_filledJulia_of_disconnected
      (c := c) (z := z) hc hzK hδ hδle hη
  dsimp at hcarrier
  filter_upwards [hcarrier] with k hk
  have hmap := congrArg (fun μ : Measure ℂ => μ S)
    (map_preBrolinMeasureOnEscapeDisk_subtype_coe c (brolinLimitSubsequence c k))
  change (Measure.map (fun w : escapeDisk c => (w : ℂ))
      (preBrolinMeasureOnEscapeDisk c (brolinLimitSubsequence c k))) S =
        preBrolinMeasure c (brolinLimitSubsequence c k) S at hmap
  rw [Measure.map_apply measurable_subtype_coe hS, hpreimage] at hmap
  rw [← hmap]
  simpa [SK, C] using hk

/-- Open-ball finite mass estimate, obtained by monotonicity from the closed
ball estimate.  This is the form used by the singular-tail bounds. -/
theorem eventually_preBrolinMeasure_subseq_ball_toReal_le_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c)
    {δ η : ℝ} (hδ : 0 < δ) (hδle : δ ≤ 1) (hη : 0 < η) :
    let S : Set ℂ := {w | ‖z - w‖ < δ}
    let C : ℝ := 2 * max 2 ‖c‖
    ∀ᶠ k in atTop,
      (preBrolinMeasure c (brolinLimitSubsequence c k) S).toReal ≤
        Real.log C / (- Real.log δ + Real.log C) + η := by
  intro S C
  let T : Set ℂ := {w | ‖z - w‖ ≤ δ}
  have hclosed :=
    eventually_preBrolinMeasure_subseq_closedBall_toReal_le_of_mem_filledJulia_of_disconnected
      (c := c) (z := z) hc hzK hδ hδle hη
  dsimp at hclosed
  filter_upwards [hclosed] with k hk
  have hsubset : S ⊆ T := by
    intro w hw
    exact le_of_lt (by simpa [S] using hw)
  have hmono :
      preBrolinMeasure c (brolinLimitSubsequence c k) S ≤
        preBrolinMeasure c (brolinLimitSubsequence c k) T :=
    measure_mono hsubset
  have hT_ne_top :
      preBrolinMeasure c (brolinLimitSubsequence c k) T ≠ ⊤ :=
    measure_ne_top (preBrolinMeasure c (brolinLimitSubsequence c k)) T
  exact (ENNReal.toReal_mono hT_ne_top hmono).trans (by simpa [T, C] using hk)

/-- The compact-carrier limiting Brolin measure has no atom at any filled-Julia
point in the disconnected case.  This is extracted directly from the
truncation-pressure bound by sending the truncation radius to zero. -/
theorem brolinLimitOnEscapeDisk_singleton_eq_zero_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c) :
    let hz : z ∈ escapeDisk c := mem_escapeDisk_of_mem_filledJulia hzK
    let zz : escapeDisk c := ⟨z, hz⟩
    (brolinLimitOnEscapeDisk c : Measure (escapeDisk c)) {zz} = 0 := by
  intro hz zz
  let μK : Measure (escapeDisk c) := (brolinLimitOnEscapeDisk c : Measure (escapeDisk c))
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
  have hmass :=
    brolinLimitOnEscapeDisk_atom_mass_le_of_mem_filledJulia_of_disconnected
      (c := c) (z := z) hc hzK hδpos hδle
  dsimp at hmass
  have hden :
      - Real.log δ + Real.log C =
        Real.log C / m + 2 * Real.log C + 1 := by
    dsimp [δ]
    rw [Real.log_exp]
    ring
  rw [hden] at hmass
  have hmass' :
      m ≤ Real.log C / (Real.log C / m + 2 * Real.log C + 1) := by
    simpa [hz, zz, μK, C, m] using hmass
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

theorem limitingBrolinMeasure_singleton_eq_zero_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c) :
    limitingBrolinMeasure c {z} = 0 := by
  have hz : z ∈ escapeDisk c := mem_escapeDisk_of_mem_filledJulia hzK
  let zz : escapeDisk c := ⟨z, hz⟩
  rw [limitingBrolinMeasure, Measure.map_apply measurable_subtype_coe
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
  exact brolinLimitOnEscapeDisk_singleton_eq_zero_of_mem_filledJulia_of_disconnected
    hc hzK

theorem brolinMu_singleton_eq_zero_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c) :
    brolinMu c {z} = 0 := by
  simpa [brolinMu] using
    limitingBrolinMeasure_singleton_eq_zero_of_mem_filledJulia_of_disconnected
      hc hzK

theorem brolinMuRieszMeasure_singleton_eq_zero_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c) :
    brolinMuRieszMeasure c {z} = 0 := by
  rw [brolinMuRieszMeasure_eq_brolinMu]
  exact brolinMu_singleton_eq_zero_of_mem_filledJulia_of_disconnected hc hzK

theorem gapAMu_singleton_eq_zero_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c) :
    gapAMu c {z} = 0 := by
  rw [gapAMu_eq_brolinMuRieszMeasure]
  exact brolinMuRieszMeasure_singleton_eq_zero_of_mem_filledJulia_of_disconnected
    hc hzK

theorem ae_truncatedLogKernel_le_logKernel_brolinMuRieszMeasure_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᵐ w ∂brolinMuRieszMeasure c,
      truncatedLogKernel z δ w ≤ logKernel z w := by
  have hzero :
      brolinMuRieszMeasure c (({z} : Set ℂ)ᶜ)ᶜ = 0 := by
    simpa using
      brolinMuRieszMeasure_singleton_eq_zero_of_mem_filledJulia_of_disconnected
        hc hzK
  have hne_ae : ∀ᵐ w ∂brolinMuRieszMeasure c, w ∈ ({z} : Set ℂ)ᶜ :=
    (mem_ae_iff).2 hzero
  filter_upwards [hne_ae] with w hw
  exact truncatedLogKernel_le_logKernel_of_ne hδ (fun hzw => hw hzw.symm)

theorem ae_truncatedLogKernel_le_logKernel_gapAMu_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᵐ w ∂gapAMu c, truncatedLogKernel z δ w ≤ logKernel z w := by
  rw [gapAMu_eq_brolinMuRieszMeasure]
  exact ae_truncatedLogKernel_le_logKernel_brolinMuRieszMeasure_of_mem_filledJulia_of_disconnected
    hc hzK hδ

/-- Finite-integral tail inequality for the canonical GAP-A boundary kernel.
When the true kernel is integrable at a boundary point, small truncations
integrate below the actual GAP-A logarithmic potential. -/
theorem integral_truncatedLogKernel_gapAMu_le_logPotential_of_integrable
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c)
    {δ : ℝ} (hδ : 0 < δ) (hδle : δ ≤ 1)
    (hint : Integrable (fun w => logKernel z w) (gapAMu c)) :
    ∫ w, truncatedLogKernel z δ w ∂gapAMu c ≤
      logPotential (gapAMu c) z := by
  have hzero :
      gapAMu c (({z} : Set ℂ)ᶜ)ᶜ = 0 := by
    simpa using
      gapAMu_singleton_eq_zero_of_mem_filledJulia_of_disconnected
        (c := c) (z := z) hc hzK
  have hne_ae : ∀ᵐ w ∂gapAMu c, w ∈ ({z} : Set ℂ)ᶜ :=
    (mem_ae_iff).2 hzero
  have htruncInt :
      Integrable (fun w => truncatedLogKernel z δ w) (gapAMu c) := by
    have hnorm :
        ∀ᵐ w ∂gapAMu c, ‖truncatedLogKernel z δ w‖ ≤ ‖logKernel z w‖ := by
      filter_upwards [hne_ae] with w hw
      exact norm_truncatedLogKernel_le_norm_logKernel_of_ne_of_le_one
        hδ hδle (fun hzw => hw hzw.symm)
    exact hint.mono
      ((continuous_truncatedLogKernel (z := z) hδ).aestronglyMeasurable)
      hnorm
  have hmono :
      (fun w => truncatedLogKernel z δ w) ≤ᵐ[gapAMu c]
        fun w => logKernel z w :=
    ae_truncatedLogKernel_le_logKernel_gapAMu_of_mem_filledJulia_of_disconnected
      (c := c) (z := z) hc hzK hδ
  have hle := integral_mono_ae htruncInt hint hmono
  simpa [logPotential] using hle

/-- For a finite canonical GAP-A boundary kernel, the standard shrinking
truncations converge to the actual GAP-A logarithmic potential. -/
theorem integral_truncatedLogKernel_gapAMu_inv_nat_tendsto_logPotential_of_integrable
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c)
    (hint : Integrable (fun w => logKernel z w) (gapAMu c)) :
    Tendsto
      (fun n : ℕ =>
        ∫ w, truncatedLogKernel z (((n + 1 : ℕ) : ℝ)⁻¹) w ∂gapAMu c)
      atTop (𝓝 (logPotential (gapAMu c) z)) := by
  have hzero :
      gapAMu c (({z} : Set ℂ)ᶜ)ᶜ = 0 := by
    simpa using
      gapAMu_singleton_eq_zero_of_mem_filledJulia_of_disconnected
        (c := c) (z := z) hc hzK
  have hne_ae : ∀ᵐ w ∂gapAMu c, w ∈ ({z} : Set ℂ)ᶜ :=
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

/-- Passing the shifted truncated pushforward identity to the true logarithmic
kernel at a boundary point.  The domination on the shifted side is supplied by
the antipodal kernel split. -/
theorem logPotential_gapAMu_quadratic_eq_integral_logKernel_quadratic_comp_shiftedLimitingBrolinMeasure
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c)
    (hμint :
      Integrable (fun y => logKernel (quadratic c z) y) (gapAMu c))
    (hzint :
      Integrable (fun w => logKernel z w) (shiftedLimitingBrolinMeasure c))
    (hnegRightInt :
      Integrable (fun w => logKernel z (-w)) (shiftedLimitingBrolinMeasure c)) :
    logPotential (gapAMu c) (quadratic c z) =
      ∫ w, logKernel (quadratic c z) (quadratic c w)
        ∂shiftedLimitingBrolinMeasure c := by
  let ν : Measure ℂ := shiftedLimitingBrolinMeasure c
  let μ : Measure ℂ := gapAMu c
  have hfzK : quadratic c z ∈ filledJulia c :=
    (mem_filledJulia_iff_quadratic_mem c z).mp hzK
  have hμzero :
      μ (({quadratic c z} : Set ℂ)ᶜ)ᶜ = 0 := by
    dsimp [μ]
    simpa using
      gapAMu_singleton_eq_zero_of_mem_filledJulia_of_disconnected
        (c := c) (z := quadratic c z) hc hfzK
  have hμne_ae : ∀ᵐ y ∂μ, y ∈ ({quadratic c z} : Set ℂ)ᶜ :=
    (mem_ae_iff).2 hμzero
  have hνzero_z :
      ν (({z} : Set ℂ)ᶜ)ᶜ = 0 := by
    dsimp [ν]
    simpa using
      shiftedLimitingBrolinMeasure_singleton_eq_zero_of_mem_filledJulia_of_disconnected
        (c := c) (z := z) hc hzK
  have hνne_z : ∀ᵐ w ∂ν, w ∈ ({z} : Set ℂ)ᶜ :=
    (mem_ae_iff).2 hνzero_z
  have hnegK : -z ∈ filledJulia c := (mem_filledJulia_neg_iff c z).2 hzK
  have hνzero_neg :
      ν (({-z} : Set ℂ)ᶜ)ᶜ = 0 := by
    dsimp [ν]
    simpa using
      shiftedLimitingBrolinMeasure_singleton_eq_zero_of_mem_filledJulia_of_disconnected
        (c := c) (z := -z) hc hnegK
  have hνne_neg : ∀ᵐ w ∂ν, w ∈ ({-z} : Set ℂ)ᶜ :=
    (mem_ae_iff).2 hνzero_neg
  have hright :
      Tendsto
        (fun n : ℕ =>
          ∫ y, truncatedLogKernel (quadratic c z)
              (((n + 1 : ℕ) : ℝ)⁻¹) y ∂μ)
        atTop (𝓝 (logPotential μ (quadratic c z))) := by
    unfold logPotential
    refine tendsto_integral_of_dominated_convergence
      (fun y => ‖logKernel (quadratic c z) y‖) ?_ hμint.norm ?_ ?_
    · intro n
      exact (continuous_truncatedLogKernel
        (z := quadratic c z) (δ := (((n + 1 : ℕ) : ℝ)⁻¹))
        (by positivity)).aestronglyMeasurable
    · intro n
      have hδle : (((n + 1 : ℕ) : ℝ)⁻¹) ≤ 1 := by
        have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
          exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
        exact inv_le_one_of_one_le₀ hn
      filter_upwards [hμne_ae] with y hy
      exact norm_truncatedLogKernel_le_norm_logKernel_of_ne_of_le_one
        (by positivity) hδle (fun hzy => hy hzy.symm)
    · filter_upwards [hμne_ae] with y hy
      exact truncatedLogKernel_inv_nat_succ_tendsto_logKernel_of_ne
        (fun hzy => hy hzy.symm)
  have hleft :
      Tendsto
        (fun n : ℕ =>
          ∫ w, truncatedLogKernel (quadratic c z)
              (((n + 1 : ℕ) : ℝ)⁻¹) (quadratic c w) ∂ν)
        atTop
        (𝓝 (∫ w, logKernel (quadratic c z) (quadratic c w) ∂ν)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun w => ‖logKernel z w‖ + ‖logKernel z (-w)‖) ?_
      (hzint.norm.add hnegRightInt.norm) ?_ ?_
    · intro n
      exact ((continuous_truncatedLogKernel
        (z := quadratic c z) (δ := (((n + 1 : ℕ) : ℝ)⁻¹))
        (by positivity)).comp (continuous_quadratic c)).aestronglyMeasurable
    · intro n
      have hδle : (((n + 1 : ℕ) : ℝ)⁻¹) ≤ 1 := by
        have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
          exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
        exact inv_le_one_of_one_le₀ hn
      filter_upwards [hνne_z, hνne_neg] with w hwz hwneg
      have hzw : z ≠ w := fun h => hwz h.symm
      have hznw : z ≠ -w := by
        intro h
        have hw_eq : w = -z := by
          rw [h, neg_neg]
        exact hwneg hw_eq
      have hquad_ne : quadratic c z ≠ quadratic c w := by
        intro hquad
        rcases (quadratic_eq_quadratic_iff c z w).mp hquad with h | h
        · exact hzw h
        · exact hznw h
      have hdom :=
        norm_truncatedLogKernel_le_norm_logKernel_of_ne_of_le_one
          (by positivity) hδle hquad_ne
      have hsplit := logKernel_quadratic_eq_add
        (c := c) (z := z) (w := w) hzw hznw
      rw [hsplit] at hdom
      exact le_trans hdom (norm_add_le (logKernel z w) (logKernel z (-w)))
    · filter_upwards [hνne_z, hνne_neg] with w hwz hwneg
      have hzw : z ≠ w := fun h => hwz h.symm
      have hznw : z ≠ -w := by
        intro h
        have hw_eq : w = -z := by
          rw [h, neg_neg]
        exact hwneg hw_eq
      have hquad_ne : quadratic c z ≠ quadratic c w := by
        intro hquad
        rcases (quadratic_eq_quadratic_iff c z w).mp hquad with h | h
        · exact hzw h
        · exact hznw h
      exact truncatedLogKernel_inv_nat_succ_tendsto_logKernel_of_ne hquad_ne
  have hright_on_left :
      Tendsto
        (fun n : ℕ =>
          ∫ w, truncatedLogKernel (quadratic c z)
              (((n + 1 : ℕ) : ℝ)⁻¹) (quadratic c w) ∂ν)
        atTop (𝓝 (logPotential μ (quadratic c z))) := by
    refine hright.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with n _hn
    dsimp [μ, ν]
    exact
      (shiftedLimitingBrolinMeasure_truncatedLogKernel_comp_quadratic_integral_eq_gapAMu
        c (quadratic c z) (by positivity)).symm
  have huniq := tendsto_nhds_unique hleft hright_on_left
  dsimp [μ, ν] at huniq
  exact huniq.symm

/-- Potential form of the true shifted pushforward identity at the boundary:
`U_{μ_c}(f_c z)` is the sum of the shifted limiting potentials at `z` and
`-z`, under the exact integrability assumptions for the three kernels. -/
theorem logPotential_gapAMu_quadratic_eq_shiftedPotential_add
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c)
    (hμint :
      Integrable (fun y => logKernel (quadratic c z) y) (gapAMu c))
    (hzint :
      Integrable (fun w => logKernel z w) (shiftedLimitingBrolinMeasure c))
    (hnegRightInt :
      Integrable (fun w => logKernel z (-w)) (shiftedLimitingBrolinMeasure c)) :
    logPotential (gapAMu c) (quadratic c z) =
      logPotential (shiftedLimitingBrolinMeasure c) z +
        logPotential (shiftedLimitingBrolinMeasure c) (-z) := by
  rw [
    logPotential_gapAMu_quadratic_eq_integral_logKernel_quadratic_comp_shiftedLimitingBrolinMeasure
      (c := c) (z := z) hc hzK hμint hzint hnegRightInt]
  exact integral_logKernel_quadratic_comp_shiftedLimitingBrolinMeasure_eq_potential_add
    (c := c) (z := z) hc hzK hzint hnegRightInt

/-- Potential form of the true shifted pushforward identity with the
`μ_c`-side integrability discharged from the shifted antipodal kernels. -/
theorem logPotential_gapAMu_quadratic_eq_shiftedPotential_add_of_shifted_antipodal_integrable
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c)
    (hzint :
      Integrable (fun w => logKernel z w) (shiftedLimitingBrolinMeasure c))
    (hnegRightInt :
      Integrable (fun w => logKernel z (-w)) (shiftedLimitingBrolinMeasure c)) :
    logPotential (gapAMu c) (quadratic c z) =
      logPotential (shiftedLimitingBrolinMeasure c) z +
        logPotential (shiftedLimitingBrolinMeasure c) (-z) := by
  exact logPotential_gapAMu_quadratic_eq_shiftedPotential_add
    (c := c) (z := z) hc hzK
    (integrable_logKernel_gapAMu_quadratic_of_shifted_antipodal
      (c := c) (z := z) hc hzK hzint hnegRightInt)
    hzint hnegRightInt

/-- Antipodal symmetry collapses the GAP-A boundary pushforward identity to
`U_{μ_c}(f_c z) = 2 U_ν(z)` for the shifted limiting measure `ν`. -/
theorem logPotential_gapAMu_quadratic_eq_two_shiftedPotential
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c)
    (hzint :
      Integrable (fun w => logKernel z w) (shiftedLimitingBrolinMeasure c)) :
    logPotential (gapAMu c) (quadratic c z) =
      2 * logPotential (shiftedLimitingBrolinMeasure c) z := by
  have hnegRightInt :
      Integrable (fun w => logKernel z (-w)) (shiftedLimitingBrolinMeasure c) :=
    integrable_logKernel_neg_right_shiftedLimitingBrolinMeasure hzint
  calc
    logPotential (gapAMu c) (quadratic c z)
        = logPotential (shiftedLimitingBrolinMeasure c) z +
            logPotential (shiftedLimitingBrolinMeasure c) (-z) :=
          logPotential_gapAMu_quadratic_eq_shiftedPotential_add_of_shifted_antipodal_integrable
            (c := c) (z := z) hc hzK hzint hnegRightInt
    _ = logPotential (shiftedLimitingBrolinMeasure c) z +
          logPotential (shiftedLimitingBrolinMeasure c) z := by
        rw [logPotential_shiftedLimitingBrolinMeasure_neg_eq]
    _ = 2 * logPotential (shiftedLimitingBrolinMeasure c) z := by
        ring

/-- Signed form of the collapsed GAP-A boundary pushforward identity. -/
theorem neg_logPotential_gapAMu_quadratic_eq_two_neg_shiftedPotential
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c)
    (hzint :
      Integrable (fun w => logKernel z w) (shiftedLimitingBrolinMeasure c)) :
    - logPotential (gapAMu c) (quadratic c z) =
      2 * (- logPotential (shiftedLimitingBrolinMeasure c) z) := by
  have h :=
    logPotential_gapAMu_quadratic_eq_two_shiftedPotential
      (c := c) (z := z) hc hzK hzint
  linarith

/-- Unconditional collapsed GAP-A boundary pushforward identity.  If the
shifted branch is integrable this is the proved dominated-convergence identity;
if it is not, reverse integrability transfer forces the GAP-A target kernel to
be nonintegrable too, so both Bochner integrals reduce to `0` by the project's
`logPotential` convention. -/
theorem logPotential_gapAMu_quadratic_eq_two_shiftedPotential_unconditional
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c) :
    logPotential (gapAMu c) (quadratic c z) =
      2 * logPotential (shiftedLimitingBrolinMeasure c) z := by
  by_cases hzint :
      Integrable (fun w => logKernel z w) (shiftedLimitingBrolinMeasure c)
  · exact logPotential_gapAMu_quadratic_eq_two_shiftedPotential
      (c := c) (z := z) hc hzK hzint
  · have hμnot :
        ¬ Integrable
          (fun y => logKernel (quadratic c z) y) (gapAMu c) := by
      intro hμint
      exact hzint
        (integrable_logKernel_shiftedLimitingBrolinMeasure_of_gapAMu_quadratic
          (c := c) (z := z) hc hzK hμint)
    have hleft :
        logPotential (gapAMu c) (quadratic c z) = 0 := by
      unfold logPotential
      exact integral_undef hμnot
    have hright :
        logPotential (shiftedLimitingBrolinMeasure c) z = 0 := by
      unfold logPotential
      exact integral_undef hzint
    calc
      logPotential (gapAMu c) (quadratic c z) = 0 := hleft
      _ = 2 * logPotential (shiftedLimitingBrolinMeasure c) z := by
            rw [hright, mul_zero]

/-- Signed unconditional form of the collapsed GAP-A boundary pushforward
identity. -/
theorem neg_logPotential_gapAMu_quadratic_eq_two_neg_shiftedPotential_unconditional
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c) :
    - logPotential (gapAMu c) (quadratic c z) =
      2 * (- logPotential (shiftedLimitingBrolinMeasure c) z) := by
  have h :=
    logPotential_gapAMu_quadratic_eq_two_shiftedPotential_unconditional
      (c := c) (z := z) hc hzK
  linarith

/-- Boundary singular-kernel passage, upper-potential side.  At a filled-Julia
point for disconnected `c`, the actual logarithmic potential of the
constructed GAP-A measure is nonpositive.  The proof uses the no-atom result to
dominate the standard `1/(n+1)` truncations by the true kernel, then passes the
nonpositive truncation integrals to the Bochner integral. -/
theorem logPotential_gapAMu_nonpos_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c) :
    logPotential (gapAMu c) z ≤ 0 := by
  by_cases hint : Integrable (fun w => logKernel z w) (gapAMu c)
  · have hzero :
        gapAMu c (({z} : Set ℂ)ᶜ)ᶜ = 0 := by
      simpa using
        gapAMu_singleton_eq_zero_of_mem_filledJulia_of_disconnected hc hzK
    have hne_ae : ∀ᵐ w ∂gapAMu c, w ∈ ({z} : Set ℂ)ᶜ :=
      (mem_ae_iff).2 hzero
    have hlim :
        Tendsto
          (fun n : ℕ =>
            ∫ w, truncatedLogKernel z (((n + 1 : ℕ) : ℝ)⁻¹) w ∂gapAMu c)
          atTop (𝓝 (logPotential (gapAMu c) z)) := by
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
          ∫ w, truncatedLogKernel z (((n + 1 : ℕ) : ℝ)⁻¹) w ∂gapAMu c ≤ 0 := by
      intro n
      have hδ : 0 < (((n + 1 : ℕ) : ℝ)⁻¹) := by positivity
      rw [gapAMu_eq_brolinMuRieszMeasure]
      exact
        integral_truncatedLogKernel_brolinMuRieszMeasure_nonpos_of_mem_filledJulia_of_disconnected
          hc hzK hδ
    exact le_of_tendsto hlim (Filter.Eventually.of_forall hnonpos)
  · have hzero : logPotential (gapAMu c) z = 0 := by
      unfold logPotential
      exact integral_undef hint
    rw [hzero]

/-- Boundary singular-kernel passage, lower-potential side.  On `K_c` in the
disconnected case, the actual GAP-A logarithmic potential is bounded below by
the fixed escape-disk diameter bound.  This is the boundedness input for the
later scaling contradiction: a negative boundary value cannot double forever
along a compact orbit. -/
theorem logPotential_gapAMu_lower_bound_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c) :
    - Real.log (2 * max 2 ‖c‖) ≤ logPotential (gapAMu c) z := by
  let C : ℝ := 2 * max 2 ‖c‖
  have hCge : 1 ≤ C := by
    dsimp [C]
    have hR : (2 : ℝ) ≤ max 2 ‖c‖ := le_max_left _ _
    nlinarith
  have hlogCnonneg : 0 ≤ Real.log C := Real.log_nonneg hCge
  by_cases hint : Integrable (fun w => logKernel z w) (gapAMu c)
  · have hzero :
        gapAMu c (({z} : Set ℂ)ᶜ)ᶜ = 0 := by
      simpa using
        gapAMu_singleton_eq_zero_of_mem_filledJulia_of_disconnected hc hzK
    have hne_ae : ∀ᵐ w ∂gapAMu c, w ∈ ({z} : Set ℂ)ᶜ :=
      (mem_ae_iff).2 hzero
    have hlim :
        Tendsto
          (fun n : ℕ =>
            ∫ w, truncatedLogKernel z (((n + 1 : ℕ) : ℝ)⁻¹) w ∂gapAMu c)
          atTop (𝓝 (logPotential (gapAMu c) z)) := by
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
            ∫ w, truncatedLogKernel z (((n + 1 : ℕ) : ℝ)⁻¹) w ∂gapAMu c := by
      intro n
      have hδ : 0 < (((n + 1 : ℕ) : ℝ)⁻¹) := by positivity
      have hδleC : (((n + 1 : ℕ) : ℝ)⁻¹) ≤ C := by
        have hδle1 : (((n + 1 : ℕ) : ℝ)⁻¹) ≤ 1 := by
          have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
            exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
          exact inv_le_one_of_one_le₀ hn
        exact le_trans hδle1 hCge
      have hbounds :
          - Real.log (max (((n + 1 : ℕ) : ℝ)⁻¹) C) ≤
            ∫ w, truncatedLogKernel z (((n + 1 : ℕ) : ℝ)⁻¹) w
              ∂gapAMu c ∧
          ∫ w, truncatedLogKernel z (((n + 1 : ℕ) : ℝ)⁻¹) w
              ∂gapAMu c ≤ 0 := by
        rw [gapAMu_eq_brolinMuRieszMeasure]
        simpa [C] using
          integral_truncatedLogKernel_brolinMuRieszMeasure_bounds_of_mem_filledJulia_of_disconnected
            (c := c) (z := z) hc hzK hδ
      have hbounds' := hbounds.1
      rwa [max_eq_right hδleC] at hbounds'
    exact ge_of_tendsto hlim (Filter.Eventually.of_forall hlower)
  · have hzero : logPotential (gapAMu c) z = 0 := by
      unfold logPotential
      exact integral_undef hint
    rw [hzero]
    exact neg_nonpos.mpr hlogCnonneg

theorem neg_logPotential_gapAMu_nonneg_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c) :
    0 ≤ - logPotential (gapAMu c) z := by
  have h :=
    logPotential_gapAMu_nonpos_of_mem_filledJulia_of_disconnected
      (c := c) (z := z) hc hzK
  linarith

theorem neg_logPotential_gapAMu_upper_bound_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (_hc : Disconnected c) (hzK : z ∈ filledJulia c) :
    - logPotential (gapAMu c) z ≤ Real.log (2 * max 2 ‖c‖) := by
  exact neg_logPotential_gapAMu_upper_bound_of_mem_filledJulia
    (c := c) (z := z) hzK

theorem logPotential_gapAMu_bounds_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c) :
    - Real.log (2 * max 2 ‖c‖) ≤ logPotential (gapAMu c) z ∧
      logPotential (gapAMu c) z ≤ 0 := by
  exact ⟨
    logPotential_gapAMu_lower_bound_of_mem_filledJulia_of_disconnected
      (c := c) (z := z) hc hzK,
    logPotential_gapAMu_nonpos_of_mem_filledJulia_of_disconnected
      (c := c) (z := z) hc hzK⟩

theorem neg_logPotential_gapAMu_bounds_of_mem_filledJulia_of_disconnected
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c) :
    0 ≤ - logPotential (gapAMu c) z ∧
      - logPotential (gapAMu c) z ≤ Real.log (2 * max 2 ‖c‖) := by
  exact ⟨
    neg_logPotential_gapAMu_nonneg_of_mem_filledJulia_of_disconnected
      (c := c) (z := z) hc hzK,
    neg_logPotential_gapAMu_upper_bound_of_mem_filledJulia_of_disconnected
      (c := c) (z := z) hc hzK⟩

theorem gapAMu_hDiscBoundaryPotentialBoundsCore {c : ℂ} (hc : Disconnected c) :
    gapAMu c = brolinMu c ∧
      IsProbOn (gapAMu c) (filledJulia c) ∧
      HasSubseqLogPotentialLimit c (gapAMu c) ∧
      (∀ z : ℂ, z ∉ filledJulia c →
        greenFunctionDyn c z = - logPotential (gapAMu c) z) ∧
      ∀ z : ℂ, z ∈ filledJulia c →
        0 ≤ - logPotential (gapAMu c) z ∧
          - logPotential (gapAMu c) z ≤ Real.log (2 * max 2 ‖c‖) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact gapAMu_eq_brolinMu c
  · exact gapAMu_isProbOn_filledJulia c
  · exact gapAMu_hasSubseqLogPotentialLimit c
  · intro z hz
    exact green_eq_neg_logPotential_gapAMu_on_basin hz
  · intro z hz
    exact neg_logPotential_gapAMu_bounds_of_mem_filledJulia_of_disconnected
      (c := c) (z := z) hc hz

/-- In the disconnected case, after the checked singular-kernel passage above,
the full GAP-A potential representation is equivalent to the remaining
opposite boundary inequality `-U^{μ_c} ≤ 0` on `K_c`. -/
theorem gapAMu_hasGreenPotentialRepresentation_iff_boundary_nonpos_of_disconnected
    {c : ℂ} (hc : Disconnected c) :
    HasGreenPotentialRepresentation c (gapAMu c) ↔
      ∀ z : ℂ, z ∈ filledJulia c → - logPotential (gapAMu c) z ≤ 0 := by
  rw [gapAMu_hasGreenPotentialRepresentation_iff_boundary_zero]
  constructor
  · intro h z hz
    rw [h z hz]
  · intro h z hz
    exact le_antisymm (h z hz)
      (neg_logPotential_gapAMu_nonneg_of_mem_filledJulia_of_disconnected
        (c := c) (z := z) hc hz)

/-- At a point where the canonical GAP-A boundary kernel is not integrable,
the real-valued `logPotential` convention makes the boundary value vanish. -/
theorem gapAMu_boundary_zero_of_not_integrable
    {c z : ℂ}
    (hnot : ¬ Integrable (fun w => logKernel z w) (gapAMu c)) :
    - logPotential (gapAMu c) z = 0 := by
  have hzero : logPotential (gapAMu c) z = 0 := by
    unfold logPotential
    exact integral_undef hnot
  rw [hzero, neg_zero]

/-- Exact finite-kernel form of the GAP-A boundary problem for the canonical
measure `μ_c`.  Nonintegrable boundary kernels are already zero by convention;
therefore the full Green-potential representation is equivalent to proving
`U_{μ_c}(z) ≥ 0` only at boundary points where the true kernel is integrable. -/
theorem gapAMu_hasGreenPotentialRepresentation_iff_boundary_integrable_nonnegative
    {c : ℂ} (hc : Disconnected c) :
    HasGreenPotentialRepresentation c (gapAMu c) ↔
      ∀ z : ℂ, z ∈ filledJulia c →
        Integrable (fun w => logKernel z w) (gapAMu c) →
        0 ≤ logPotential (gapAMu c) z := by
  rw [gapAMu_hasGreenPotentialRepresentation_iff_boundary_zero]
  constructor
  · intro hzero z hzK _hint
    have hz0 := hzero z hzK
    have hUzero : logPotential (gapAMu c) z = 0 := by
      linarith
    rw [hUzero]
  · intro hnonneg z hzK
    by_cases hint : Integrable (fun w => logKernel z w) (gapAMu c)
    · have hle : logPotential (gapAMu c) z ≤ 0 :=
        logPotential_gapAMu_nonpos_of_mem_filledJulia_of_disconnected
          (c := c) (z := z) hc hzK
      have hge : 0 ≤ logPotential (gapAMu c) z :=
        hnonneg z hzK hint
      have hzero : logPotential (gapAMu c) z = 0 :=
        le_antisymm hle hge
      rw [hzero, neg_zero]
    · exact gapAMu_boundary_zero_of_not_integrable hint

/-- For the canonical GAP-A measure, the finite-kernel boundary nonnegativity
target is exactly the zero-limit of the standard shrinking truncation
integrals. -/
theorem gapAMu_boundary_integrable_nonnegative_iff_truncation_zero
    {c : ℂ} (hc : Disconnected c) :
    (∀ z : ℂ, z ∈ filledJulia c →
        Integrable (fun w => logKernel z w) (gapAMu c) →
        0 ≤ logPotential (gapAMu c) z) ↔
      ∀ z : ℂ, z ∈ filledJulia c →
        Integrable (fun w => logKernel z w) (gapAMu c) →
        Tendsto
          (fun n : ℕ =>
            ∫ w, truncatedLogKernel z (((n + 1 : ℕ) : ℝ)⁻¹) w ∂gapAMu c)
          atTop (𝓝 0) := by
  constructor
  · intro hnonneg z hzK hint
    have hlim :=
      integral_truncatedLogKernel_gapAMu_inv_nat_tendsto_logPotential_of_integrable
        (c := c) (z := z) hc hzK hint
    have hle : logPotential (gapAMu c) z ≤ 0 :=
      logPotential_gapAMu_nonpos_of_mem_filledJulia_of_disconnected
        (c := c) (z := z) hc hzK
    have hge : 0 ≤ logPotential (gapAMu c) z := hnonneg z hzK hint
    have hzero : logPotential (gapAMu c) z = 0 := le_antisymm hle hge
    simpa [hzero] using hlim
  · intro hzero z hzK hint
    have hlim :=
      integral_truncatedLogKernel_gapAMu_inv_nat_tendsto_logPotential_of_integrable
        (c := c) (z := z) hc hzK hint
    have h0eq :
        (0 : ℝ) = logPotential (gapAMu c) z :=
      tendsto_nhds_unique (hzero z hzK hint) hlim
    rw [← h0eq]

/-- Equivalent shrinking-truncation form of the canonical GAP-A hDisc target.
After nonintegrable boundary kernels are discharged by convention, hDisc is
equivalent to proving that every finite boundary kernel has zero truncation
limit. -/
theorem gapAMu_hasGreenPotentialRepresentation_iff_boundary_truncation_zero
    {c : ℂ} (hc : Disconnected c) :
    HasGreenPotentialRepresentation c (gapAMu c) ↔
      ∀ z : ℂ, z ∈ filledJulia c →
        Integrable (fun w => logKernel z w) (gapAMu c) →
        Tendsto
          (fun n : ℕ =>
            ∫ w, truncatedLogKernel z (((n + 1 : ℕ) : ℝ)⁻¹) w ∂gapAMu c)
          atTop (𝓝 0) := by
  rw [gapAMu_hasGreenPotentialRepresentation_iff_boundary_integrable_nonnegative hc,
    gapAMu_boundary_integrable_nonnegative_iff_truncation_zero hc]

end Bottcher
