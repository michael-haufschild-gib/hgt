import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheCompleteWeilMatrixDecomposesAtEveryOverlap
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheCompletedShellEnergyIsAPositiveFourierIntegral
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheMixedRobinExpansionSurvivesActualOverlap

/-!
# Near atoms pair through the logarithm of the width

Two atoms of a profile `φ` at width `w` and log-distance `0 ≤ s ≤ 2w` lie in one common window of
width `w + s ≤ 3w`. The mixed Robin expansion on that window gives

`Arch(n, j)/(w∫φ²) = log(1/w) · G(s/w)/∫φ² + O_φ(1)`,

uniformly in `n, j` and `0 < w ≤ 1/3` (`exists_abs_atomArchPair_near_sub_le`). Here
`G(t) = ∫ φ(u) φ(u+t) du`. The bounded remainder collects `2θ′(0) + 2c_∞`, the loss `log(1+s/w)`
of the larger window, and the mixed shape term, which is at most twice the single-atom shape term
`w(β(φ) + ∫φ² · log 3)`.
-/

noncomputable section

open MeasureTheory Set Filter Topology Finset
open scoped Real

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open ArithmeticElectrostatics SpacingScaleHarmonicAnalysis ArithmeticLorentzianGeometry
  CriticalArithmeticCorrelationTheory CompletedShell
open _root_.RHTower (archLevyDensity gammaHardyPhaseRate levyEnergy)

variable {φ : ℝ → ℝ}

/-- The shape term scales with the width on every window: `β(φ(·/w), wR) = w β(φ, R)`. -/
theorem bumpRobin_atomDilate_window {w : ℝ} (hw : 0 < w) {R : ℝ} (hR : 0 ≤ R) :
    bumpRobin (atomDilate φ w) (w * R) = w * bumpRobin φ R := by
  set h : ℝ → ℝ := fun t => (∫ v, (φ v - φ (v + t)) ^ 2) / (2 * t)
  have hpt : ∀ y ∈ Ioc (0 : ℝ) (w * R),
      (∫ u, (atomDilate φ w u - atomDilate φ w (u + y)) ^ 2) / (2 * y) = h (y / w) := by
    intro y hy
    rw [integral_sub_shift_atomDilate hw]
    simp only [h]
    have hy0 : y ≠ 0 := ne_of_gt hy.1
    field_simp
  unfold bumpRobin
  rw [setIntegral_congr_fun measurableSet_Ioc hpt,
    ← intervalIntegral.integral_of_le (mul_nonneg hw.le hR),
    intervalIntegral.integral_comp_div (fun t => h t) hw.ne', zero_div,
    mul_div_cancel_left₀ R hw.ne', intervalIntegral.integral_of_le hR, smul_eq_mul]

section Profile

variable (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u : ℝ, u ∉ Set.Icc (0 : ℝ) 1 → φ u = 0)
include hφ hsupp

/-- On a window `R ≥ 1` the shape term is `β(φ) + ∫φ² · log R`. -/
theorem bumpRobin_window_eq {R : ℝ} (hR : 1 ≤ R) :
    bumpRobin φ R = bumpRobin φ 1 + (∫ u, φ u ^ 2) * Real.log R := by
  have hH := continuous_shellRegular hφ hsupp
  have hpt : ∀ y ∈ Ioc (0 : ℝ) R, (∫ u, (φ u - φ (u + y)) ^ 2) / (2 * y) = shellRegular φ y := by
    intro y hy
    have hy0 : y ≠ 0 := ne_of_gt hy.1
    rw [RHTower.ArchimedeanAnomaly.integral_sub_shift_sq (hasCompactSupport_profile hsupp)
      hφ.continuous y, shellRegular, if_neg hy0]
    field_simp
  have htail : ∫ y in (1 : ℝ)..R, shellRegular φ y = (∫ u, φ u ^ 2) * Real.log R := by
    have hinv : ∫ y in (1 : ℝ)..R, shellRegular φ y = ∫ y in (1 : ℝ)..R, (∫ u, φ u ^ 2) * y⁻¹ := by
      refine intervalIntegral.integral_congr fun y hy => ?_
      rw [uIcc_of_le hR] at hy
      have hy0 : y ≠ 0 := by linarith [hy.1]
      simp only [shellRegular, if_neg hy0, shellAutocorr_eq_zero_of_one_le hφ hsupp hy.1,
        shellAutocorr_zero, sub_zero, div_eq_mul_inv]
    rw [hinv, intervalIntegral.integral_const_mul, integral_inv_of_pos one_pos (by linarith),
      div_one]
  have hBR : bumpRobin φ R = ∫ y in (0 : ℝ)..R, shellRegular φ y := by
    rw [intervalIntegral.integral_of_le (by linarith : (0 : ℝ) ≤ R), bumpRobin]
    exact setIntegral_congr_fun measurableSet_Ioc hpt
  rw [hBR, ← intervalIntegral.integral_add_adjacent_intervals
      (hH.intervalIntegrable 0 1) (hH.intervalIntegrable 1 R), htail,
    bumpRobin_eq_integral_shellRegular hφ hsupp]

omit hφ hsupp in
/-- The autocorrelation of a dilated profile: `∫ φ_w(u) φ_w(u − s) du = w G(s/w)`. -/
theorem integral_atomDilate_mul_shift {w : ℝ} (hw0 : 0 < w) (s : ℝ) :
    (∫ u, atomDilate φ w u * atomDilate φ w (u - s)) = w * shellAutocorr φ (s / w) := by
  have h1 : (∫ u, atomDilate φ w u * atomDilate φ w (u - s)) = bumpCorr (atomDilate φ w) (-s) := by
    rw [bumpCorr]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [sub_eq_add_neg]
  have h2 : bumpCorr (atomDilate φ w) s = w * bumpCorr φ (s / w) := by
    have h := MeasureTheory.Measure.integral_comp_div (fun u => φ u * φ (u + s / w)) w
    simp only [smul_eq_mul, abs_of_pos hw0] at h
    simp only [bumpCorr]
    rw [← h]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [atomDilate, add_div]
  rw [h1, bumpCorr_neg, h2]
  rfl

omit hφ hsupp in
/-- The archimedean pairing of two atoms only reads their log-distance. -/
theorem atomArchPair_eq_translate (g : ℝ → ℝ) (n j : ℕ) :
    atomArchPair g n j =
      2 * gammaHardyPhaseRate 0 * (∫ u, g u * g (u - (Real.log j - Real.log n))) +
        ∫ y in Ioi 0, levyMixed g (fun u => g (u - (Real.log j - Real.log n))) y := by
  have hmass : (∫ u, atom g n u * atom g j u) = ∫ u, g u * g (u - (Real.log j - Real.log n)) := by
    rw [← integral_sub_right_eq_self (fun u => g u * g (u - (Real.log j - Real.log n)))
      (Real.log n)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [atom]
    ring_nf
  have hlevy : (∫ y in Ioi 0, levyMixed (atom g n) (atom g j) y) =
      ∫ y in Ioi 0, levyMixed g (fun u => g (u - (Real.log j - Real.log n))) y := by
    refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
    unfold levyMixed atom
    congr 1
    rw [← integral_sub_right_eq_self
      (fun u => (g u - g (u + y)) * (g (u - (Real.log j - Real.log n)) -
        g (u + y - (Real.log j - Real.log n)))) (Real.log n)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    ring_nf
  rw [atomArchPair, hmass, hlevy]

/-- The single-atom shape term on a window of at most three widths. -/
theorem bumpRobin_atomDilate_le_three {w W : ℝ} (hw0 : 0 < w) (hwW : w ≤ W) (hW3 : W ≤ 3 * w) :
    bumpRobin (atomDilate φ w) W ≤ w * (bumpRobin φ 1 + (∫ u, φ u ^ 2) * Real.log 3) := by
  have hR : 1 ≤ W / w := by rw [le_div_iff₀ hw0]; linarith
  have hR3 : W / w ≤ 3 := by rw [div_le_iff₀ hw0]; linarith
  have h := bumpRobin_atomDilate_window (φ := φ) hw0 (by positivity : (0 : ℝ) ≤ W / w)
  rw [mul_div_cancel₀ W hw0.ne', bumpRobin_window_eq hφ hsupp hR] at h
  rw [h]
  refine mul_le_mul_of_nonneg_left ?_ hw0.le
  have hM0 : 0 ≤ ∫ u, φ u ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have := Real.log_le_log (by linarith) hR3
  nlinarith

/-- The shape integrand of a dilated atom is integrable on every window. -/
theorem integrableOn_shape_atomDilate {w W : ℝ} (hw0 : 0 < w) :
    IntegrableOn (fun y => (∫ u, (atomDilate φ w u - atomDilate φ w (u + y)) ^ 2) / (2 * y))
      (Ioc 0 W) := by
  have hpt : ∀ y ∈ Ioc (0 : ℝ) W, (∫ u, (atomDilate φ w u - atomDilate φ w (u + y)) ^ 2) /
      (2 * y) = shellRegular φ (y / w) := by
    intro y hy
    have hy0 : y ≠ 0 := ne_of_gt hy.1
    rw [integral_sub_shift_atomDilate hw0, RHTower.ArchimedeanAnomaly.integral_sub_shift_sq
      (hasCompactSupport_profile hsupp) hφ.continuous (y / w), shellRegular,
      if_neg (div_ne_zero hy0 hw0.ne')]
    field_simp
  refine IntegrableOn.congr_fun ?_ (fun y hy => (hpt y hy).symm) measurableSet_Ioc
  exact ((continuous_shellRegular hφ hsupp).comp
    (continuous_id.div_const w)).integrableOn_Icc.mono_set Ioc_subset_Icc_self

/-- A sum of a unit multiple of an atom and a translate has at most four times its shape term. -/
theorem bumpRobin_unit_add_translate_le {w W : ℝ} (hw0 : 0 < w) (s : ℝ) {a : ℝ}
    (ha : a ^ 2 = 1) :
    bumpRobin (fun u => a * atomDilate φ w u + atomDilate φ w (u - s)) W ≤
      4 * bumpRobin (atomDilate φ w) W := by
  obtain ⟨hg, -, hgc⟩ := atomDilate_facts hφ hsupp hw0
  set g := atomDilate φ w with hgdef
  have hint := integrableOn_shape_atomDilate hφ hsupp (W := W) hw0
  unfold bumpRobin
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_mono_of_nonneg ?_ (hint.const_mul 4) ?_
  · refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun y hy => ?_)
    exact div_nonneg (integral_nonneg fun _ => sq_nonneg _) (by linarith [hy.1])
  · refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun y hy => ?_)
    have hy2 : 0 < 2 * y := by linarith [hy.1]
    beta_reduce
    rw [mul_div_assoc', div_le_div_iff_of_pos_right hy2]
    have hgi : Integrable fun u => (g u - g (u + y)) ^ 2 :=
      RHTower.WeilMarkovPole.integrable_sub_shift_sq hg.continuous hgc y
    have hdi : Integrable fun u => (g (u - s) - g (u + y - s)) ^ 2 := by
      have := hgi.comp_sub_right s
      refine this.congr (Filter.Eventually.of_forall fun u => ?_)
      simp only
      ring_nf
    have hdeq : (∫ u, (g (u - s) - g (u + y - s)) ^ 2) = ∫ u, (g u - g (u + y)) ^ 2 := by
      rw [← integral_sub_right_eq_self (fun u => (g u - g (u + y)) ^ 2) s]
      refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
      simp only
      ring_nf
    have hle : ∀ u, (a * g u + g (u - s) - (a * g (u + y) + g (u + y - s))) ^ 2 ≤
        2 * (g u - g (u + y)) ^ 2 + 2 * (g (u - s) - g (u + y - s)) ^ 2 := by
      intro u
      have e : a * g u + g (u - s) - (a * g (u + y) + g (u + y - s)) =
          a * (g u - g (u + y)) + (g (u - s) - g (u + y - s)) := by ring
      rw [e]
      nlinarith [sq_nonneg (a * (g u - g (u + y)) - (g (u - s) - g (u + y - s))),
        sq_nonneg (g u - g (u + y))]
    have hle' : ∀ u, (a * g u + g (u - s) - (a * g (u + y) + g (u + y - s))) ^ 2 =
        (a * g u + g (u - s) - (a * g (u + y) + g (u + y - s))) ^ 2 := fun _ => rfl
    calc (∫ u, (a * g u + g (u - s) - (a * g (u + y) + g (u + y - s))) ^ 2)
        ≤ ∫ u, (2 * (g u - g (u + y)) ^ 2 + 2 * (g (u - s) - g (u + y - s)) ^ 2) :=
          MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun _ => sq_nonneg _)
            ((hgi.const_mul 2).add (hdi.const_mul 2)) (Filter.Eventually.of_forall hle)
      _ = 4 * ∫ u, (g u - g (u + y)) ^ 2 := by
          rw [integral_add (hgi.const_mul 2) (hdi.const_mul 2), MeasureTheory.integral_const_mul,
            MeasureTheory.integral_const_mul, hdeq]
          ring

/-- The mixed shape term of an atom and a translate within three widths. -/
theorem abs_mixedBumpRobin_translate_le {w W : ℝ} (hw0 : 0 < w) (hwW : w ≤ W) (hW3 : W ≤ 3 * w)
    (s : ℝ) :
    |mixedBumpRobin (atomDilate φ w) (fun u => atomDilate φ w (u - s)) W| ≤
      2 * (w * (bumpRobin φ 1 + (∫ u, φ u ^ 2) * Real.log 3)) := by
  have hsingle := bumpRobin_atomDilate_le_three hφ hsupp hw0 hwW hW3
  have hplus := bumpRobin_unit_add_translate_le hφ hsupp (W := W) hw0 s (a := 1) (by norm_num)
  have hminus := bumpRobin_unit_add_translate_le hφ hsupp (W := W) hw0 s (a := -1) (by norm_num)
  simp only [one_mul, neg_one_mul] at hplus hminus
  have hp0 : 0 ≤ bumpRobin (fun u => atomDilate φ w u + atomDilate φ w (u - s)) W :=
    setIntegral_nonneg measurableSet_Ioc fun y hy =>
      div_nonneg (integral_nonneg fun _ => sq_nonneg _) (by linarith [hy.1])
  have hm0 : 0 ≤ bumpRobin (fun u => -atomDilate φ w u + atomDilate φ w (u - s)) W :=
    setIntegral_nonneg measurableSet_Ioc fun y hy =>
      div_nonneg (integral_nonneg fun _ => sq_nonneg _) (by linarith [hy.1])
  rw [mixedBumpRobin, abs_le]
  constructor <;> linarith

variable (hM : 0 < ∫ u, φ u ^ 2)
include hM

/-- The remainder bound of the near pairing at one ordered pair. -/
theorem abs_atomArchPair_near_ordered_le {w : ℝ} (hw0 : 0 < w) (hw1 : w ≤ 1 / 3) {n j : ℕ}
    (hs0 : 0 ≤ Real.log j - Real.log n) (hs2 : Real.log j - Real.log n ≤ 2 * w) :
    |atomArchPair (atomDilate φ w) n j - Real.log (1 / w) *
        (w * shellAutocorr φ ((Real.log j - Real.log n) / w))| ≤
      (w * ∫ u, φ u ^ 2) * ((|2 * gammaHardyPhaseRate 0| + |archRobinConstant| + Real.log 3) +
        2 * (bumpRobin φ 1 / (∫ u, φ u ^ 2) + Real.log 3) + Real.exp (1 / 2)) := by
  set M := ∫ u, φ u ^ 2 with hMdef
  set s := Real.log j - Real.log n with hs
  obtain ⟨hg, hgsupp, -⟩ := atomDilate_facts hφ hsupp hw0
  set g := atomDilate φ w with hgdef
  set d : ℝ → ℝ := fun u => g (u - s) with hd
  set W := w + s with hW
  have hW0 : 0 < W := by linarith
  have hW1 : W ≤ 1 := by linarith
  have hwM : 0 < w * M := mul_pos hw0 hM
  have hdsupp : ∀ u, u ∉ Set.Icc 0 W → d u = 0 := fun u hu =>
    hgsupp _ fun h => hu ⟨by linarith [h.1], by linarith [h.2]⟩
  have hgsuppW : ∀ u, u ∉ Set.Icc 0 W → g u = 0 := fun u hu =>
    hgsupp _ fun h => hu ⟨h.1, by linarith [h.2]⟩
  have hdC : ContDiff ℝ 2 d := hg.comp (contDiff_id.sub contDiff_const)
  have hrobin := abs_mixed_levy_sub_robin_le hg hgsuppW hdC hdsupp hW0 hW1
  have hgM : (∫ u, g u ^ 2) = w * M := integral_atomDilate_sq hw0
  have hdM : (∫ u, d u ^ 2) = w * M := by
    rw [← hgM]; exact integral_sub_right_eq_self (fun u => g u ^ 2) s
  have hfd : (∫ u, g u * d u) = w * shellAutocorr φ (s / w) :=
    integral_atomDilate_mul_shift hw0 s
  have hmixed := abs_mixedBumpRobin_translate_le hφ hsupp hw0 (by linarith : w ≤ W)
    (by linarith : W ≤ 3 * w) s
  have hG : |shellAutocorr φ (s / w)| ≤ M :=
    abs_bumpCorr_le hφ.continuous (hasCompactSupport_profile hsupp) (s / w)
  have hR0 : 0 ≤ Real.log (W / w) := Real.log_nonneg (by rw [le_div_iff₀ hw0]; linarith)
  have hR3 : Real.log (W / w) ≤ Real.log 3 :=
    Real.log_le_log (by positivity) (by rw [div_le_iff₀ hw0]; linarith)
  have hWlog : Real.log (1 / W) = Real.log (1 / w) - Real.log (W / w) := by
    rw [one_div, one_div, Real.log_inv, Real.log_inv, Real.log_div hW0.ne' hw0.ne']
    ring
  set E := (∫ y in Ioi 0, levyMixed g d y) -
    ((Real.log (1 / W) + archRobinConstant) * (∫ u, g u * d u) + mixedBumpRobin g d W) with hE
  have hEb : |E| ≤ Real.exp (1 / 2) * (w * M) := by
    have h := hrobin
    rw [hgM, hdM] at h
    have hW' : W * (w * M + w * M) ≤ 2 * (w * M) := by nlinarith
    have hex := Real.exp_pos (1 / 2)
    calc |E| ≤ Real.exp (1 / 2) / 4 * W * (w * M + w * M) := h
      _ = Real.exp (1 / 2) / 4 * (W * (w * M + w * M)) := by ring
      _ ≤ Real.exp (1 / 2) / 4 * (2 * (w * M)) := mul_le_mul_of_nonneg_left hW' (by positivity)
      _ ≤ Real.exp (1 / 2) * (w * M) := by nlinarith
  have hpair : atomArchPair g n j = 2 * gammaHardyPhaseRate 0 * (∫ u, g u * d u) +
      ∫ y in Ioi 0, levyMixed g d y := by
    rw [atomArchPair_eq_translate g n j]
  have hexpand : atomArchPair g n j - Real.log (1 / w) * (w * shellAutocorr φ (s / w)) =
      (w * shellAutocorr φ (s / w)) * (2 * gammaHardyPhaseRate 0 + archRobinConstant -
        Real.log (W / w)) + mixedBumpRobin g d W + E := by
    rw [hpair, hE, hfd, hWlog]
    ring
  have hc : |2 * gammaHardyPhaseRate 0 + archRobinConstant - Real.log (W / w)| ≤
      |2 * gammaHardyPhaseRate 0| + |archRobinConstant| + Real.log 3 := by
    rw [abs_le]
    constructor <;> linarith [le_abs_self (2 * gammaHardyPhaseRate 0),
      neg_abs_le (2 * gammaHardyPhaseRate 0), le_abs_self archRobinConstant,
      neg_abs_le archRobinConstant]
  have h1 : |w * shellAutocorr φ (s / w) * (2 * gammaHardyPhaseRate 0 + archRobinConstant -
      Real.log (W / w))| ≤ (w * M) * (|2 * gammaHardyPhaseRate 0| + |archRobinConstant| +
        Real.log 3) := by
    rw [abs_mul, abs_mul, abs_of_pos hw0, mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul hG hc (abs_nonneg _) hM.le) hw0.le
  have h2 : 2 * (w * (bumpRobin φ 1 + M * Real.log 3)) =
      (w * M) * (2 * (bumpRobin φ 1 / M + Real.log 3)) := by
    field_simp
  rw [hexpand]
  calc _ ≤ |w * shellAutocorr φ (s / w) * (2 * gammaHardyPhaseRate 0 + archRobinConstant -
        Real.log (W / w))| + |mixedBumpRobin g d W| + |E| := abs_add_three _ _ _
    _ ≤ (w * M) * (|2 * gammaHardyPhaseRate 0| + |archRobinConstant| + Real.log 3) +
        (w * M) * (2 * (bumpRobin φ 1 / M + Real.log 3)) + Real.exp (1 / 2) * (w * M) := by
        rw [← h2]; linarith
    _ = _ := by ring

/-- **Near atoms pair through `log(1/w)`.** -/
theorem exists_abs_atomArchPair_near_sub_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ w : ℝ, 0 < w → w ≤ 1 / 3 → ∀ n j : ℕ,
      |Real.log j - Real.log n| ≤ 2 * w →
        |atomArchPair (atomDilate φ w) n j / (∫ u, atomDilate φ w u ^ 2) -
          Real.log (1 / w) * shellAutocorr φ (|Real.log j - Real.log n| / w) /
            (∫ u, φ u ^ 2)| ≤ K := by
  set M := ∫ u, φ u ^ 2 with hMdef
  have hβ0 : 0 ≤ bumpRobin φ 1 := setIntegral_nonneg measurableSet_Ioc fun y hy =>
    div_nonneg (integral_nonneg fun _ => sq_nonneg _) (by linarith [hy.1])
  have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  refine ⟨(|2 * gammaHardyPhaseRate 0| + |archRobinConstant| + Real.log 3) +
    2 * (bumpRobin φ 1 / M + Real.log 3) + Real.exp (1 / 2), by positivity, ?_⟩
  intro w hw0 hw1 n j hs
  have hwM : 0 < w * M := mul_pos hw0 hM
  have hgM : (∫ u, atomDilate φ w u ^ 2) = w * M := integral_atomDilate_sq hw0
  have hdiv : ∀ A t : ℝ, A / (∫ u, atomDilate φ w u ^ 2) - Real.log (1 / w) * t / M =
      (A - Real.log (1 / w) * (w * t)) / (w * M) := fun A t => by
    rw [hgM]; field_simp
  rcases le_total 0 (Real.log j - Real.log n) with h | h
  · rw [abs_of_nonneg h] at hs ⊢
    rw [hdiv, abs_div, abs_of_pos hwM, div_le_iff₀ hwM, mul_comm _ (w * M)]
    exact abs_atomArchPair_near_ordered_le hφ hsupp hM hw0 hw1 h hs
  · rw [abs_of_nonpos h] at hs ⊢
    rw [atomArchPair_comm, show -(Real.log j - Real.log n) = Real.log n - Real.log j by ring,
      hdiv, abs_div, abs_of_pos hwM, div_le_iff₀ hwM, mul_comm _ (w * M)]
    exact abs_atomArchPair_near_ordered_le hφ hsupp hM hw0 hw1 (by linarith) (by linarith)

end Profile

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
