import GaloisForLFunctions.RHTower.WeilWorkDeficitMassBounds
import GaloisForLFunctions.RHTower.WeilWorkDeficitPoissonLeakage
import GaloisForLFunctions.RHTower.WeilFullConeAtomExtraction

/-!
# Integrating finite-height Poisson leakage against both actual measures

Endpoint neighborhoods, the remaining bounded interval, and the integrable Cauchy tail
give finite-height bounds for the canonical Weil measure and the full actual zero divisor.
-/

open Set Filter MeasureTheory
open scoped Topology

noncomputable section

namespace RHTower.WeilSpectral

private theorem measurableSet_deficitFar (T : ℝ) : MeasurableSet {r : ℝ | 2 * T < |r|} :=
  isOpen_lt continuous_const continuous_abs |>.measurableSet

/-- The inverse-square mass outside the distant height window. -/
private def measureCauchyTail (μ : Measure ℝ) (T : ℝ) : ℝ :=
  ∫ r in {r : ℝ | 2 * T < |r|}, 1 / (1 + r ^ 2) ∂μ

private theorem tendsto_measureCauchyTail (μ : Measure ℝ)
    (hi : Integrable (fun r : ℝ => 1 / (1 + r ^ 2)) μ) :
    Tendsto (measureCauchyTail μ) atTop (𝓝 0) := by
  have hlim : Tendsto
      (fun T : ℝ => ∫ r, {r : ℝ | 2 * T < |r|}.indicator
        (fun r => 1 / (1 + r ^ 2)) r ∂μ) atTop
      (𝓝 (∫ _r : ℝ, (0 : ℝ) ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun r : ℝ => 1 / (1 + r ^ 2))
    · exact Eventually.of_forall fun T =>
        (hi.indicator (measurableSet_deficitFar T)).aestronglyMeasurable
    · refine Eventually.of_forall fun T => Eventually.of_forall fun r => ?_
      by_cases hr : 2 * T < |r|
      · rw [indicator_of_mem (show r ∈ {r : ℝ | 2 * T < |r|} from hr),
          Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      · rw [indicator_of_notMem (show r ∉ {r : ℝ | 2 * T < |r|} from hr), norm_zero]
        positivity
    · exact hi
    · refine Eventually.of_forall fun r => tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop (|r| + 1)] with T hT
      symm
      apply indicator_of_notMem
      change ¬ 2 * T < |r|
      linarith [abs_nonneg r]
  change Tendsto (fun T : ℝ =>
    ∫ r in {r : ℝ | 2 * T < |r|}, 1 / (1 + r ^ 2) ∂μ) atTop (𝓝 0)
  simpa only [integral_indicator (measurableSet_deficitFar _), integral_zero] using hlim

private def leakageMajorant (T H r : ℝ) : ℝ :=
  (Icc (-H) H).indicator (fun _ => Real.pi) r +
  (Icc (T - H) (T + H)).indicator (fun _ => Real.pi) r +
  (Icc (-2 * T) (2 * T)).indicator (fun _ => 3 / H) r +
  {r : ℝ | 2 * T < |r|}.indicator (fun r => 12 * T / (1 + r ^ 2)) r

private theorem deficitPoissonLeakage_le_majorant {T H : ℝ} (hT : 1 ≤ T) (hH : 0 < H)
    (r : ℝ) : deficitPoissonLeakage T r ≤ leakageMajorant T H r := by
  have h1 : 0 ≤ (Icc (-H) H).indicator (fun _ => Real.pi) r :=
    indicator_nonneg (fun _ _ => Real.pi_pos.le) r
  have h2 : 0 ≤ (Icc (T - H) (T + H)).indicator (fun _ => Real.pi) r :=
    indicator_nonneg (fun _ _ => Real.pi_pos.le) r
  have h3 : 0 ≤ (Icc (-2 * T) (2 * T)).indicator (fun _ => 3 / H) r :=
    indicator_nonneg (fun _ _ => by positivity) r
  have h4 : 0 ≤ {r : ℝ | 2 * T < |r|}.indicator
      (fun r => 12 * T / (1 + r ^ 2)) r :=
    indicator_nonneg (fun _ _ => by positivity) r
  unfold leakageMajorant
  by_cases hnear0 : r ∈ Icc (-H) H
  · rw [indicator_of_mem hnear0]
    linarith [deficitPoissonLeakage_le_pi (by linarith : 0 ≤ T) r]
  by_cases hnearT : r ∈ Icc (T - H) (T + H)
  · rw [indicator_of_mem hnearT]
    linarith [deficitPoissonLeakage_le_pi (by linarith : 0 ≤ T) r]
  by_cases hbulk : r ∈ Icc (-2 * T) (2 * T)
  · have hr : H ≤ |r| := by
      by_contra h
      have := abs_lt.mp (lt_of_not_ge h)
      exact hnear0 ⟨this.1.le, this.2.le⟩
    have hTr : H ≤ |T - r| := by
      by_contra h
      have := abs_lt.mp (lt_of_not_ge h)
      exact hnearT ⟨by linarith [this.2], by linarith [this.1]⟩
    rw [indicator_of_mem hbulk]
    linarith [deficitPoissonLeakage_le_endpoint (by linarith : 0 ≤ T) hH hr hTr]
  · have hfar : 2 * T < |r| := by
      by_contra h
      have := abs_le.mp (le_of_not_gt h)
      exact hbulk ⟨by linarith [this.1], this.2⟩
    rw [indicator_of_mem (show r ∈ {r : ℝ | 2 * T < |r|} from hfar)]
    linarith [deficitPoissonLeakage_le_far hT hfar]

private theorem integrable_leakageMajorant (μ : Measure ℝ)
    (hfin : ∀ a b : ℝ, μ (Icc a b) ≠ ⊤)
    (hiC : Integrable (fun r : ℝ => 1 / (1 + r ^ 2)) μ)
    (T H : ℝ) : Integrable (leakageMajorant T H) μ := by
  have hc (a b c : ℝ) : Integrable ((Icc a b).indicator (fun _ => c)) μ :=
    (integrableOn_const (hfin a b)).integrable_indicator measurableSet_Icc
  have hi : Integrable (fun r : ℝ => 12 * T / (1 + r ^ 2)) μ := by
    simpa [div_eq_mul_inv] using hiC.const_mul (12 * T)
  exact (((hc (-H) H Real.pi).add (hc (T - H) (T + H) Real.pi)).add
    (hc (-2 * T) (2 * T) (3 / H))).add (hi.indicator (measurableSet_deficitFar T))

private theorem integrable_measureLeakage (μ : Measure ℝ)
    (hfin : ∀ a b : ℝ, μ (Icc a b) ≠ ⊤)
    (hiC : Integrable (fun r : ℝ => 1 / (1 + r ^ 2)) μ)
    {T : ℝ} (hT : 1 ≤ T) : Integrable (deficitPoissonLeakage T) μ := by
  refine (integrable_leakageMajorant μ hfin hiC T 1).mono'
    (measurable_deficitPoissonLeakage T).aestronglyMeasurable
    (Eventually.of_forall fun r => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (deficitPoissonLeakage_nonneg T r)]
  exact deficitPoissonLeakage_le_majorant hT zero_lt_one r

/-- A finite-height bound retaining every endpoint atom and all diffuse mass. -/
private theorem integral_measureLeakage_le (μ : Measure ℝ)
    (hfin : ∀ a b : ℝ, μ (Icc a b) ≠ ⊤)
    (hiC : Integrable (fun r : ℝ => 1 / (1 + r ^ 2)) μ)
    {T H : ℝ} (hT : 1 ≤ T) (hH : 0 < H) :
    ∫ r, deficitPoissonLeakage T r ∂μ ≤
      Real.pi * μ.real (Icc (-H) H) +
      Real.pi * μ.real (Icc (T - H) (T + H)) +
      (3 / H) * μ.real (Icc (-2 * T) (2 * T)) +
      12 * T * measureCauchyTail μ T := by
  have hc (a b c : ℝ) : Integrable ((Icc a b).indicator (fun _ => c)) μ :=
    (integrableOn_const (hfin a b)).integrable_indicator measurableSet_Icc
  have hi : Integrable (fun r : ℝ => 12 * T / (1 + r ^ 2)) μ := by
    simpa [div_eq_mul_inv] using hiC.const_mul (12 * T)
  have h := integral_mono (integrable_measureLeakage μ hfin hiC hT)
    (integrable_leakageMajorant μ hfin hiC T H) (deficitPoissonLeakage_le_majorant hT hH)
  have h12 : Integrable (fun r =>
      (Icc (-H) H).indicator (fun _ => Real.pi) r +
      (Icc (T - H) (T + H)).indicator (fun _ => Real.pi) r) μ :=
    (hc (-H) H Real.pi).add (hc (T - H) (T + H) Real.pi)
  have h123 : Integrable (fun r =>
      (Icc (-H) H).indicator (fun _ => Real.pi) r +
      (Icc (T - H) (T + H)).indicator (fun _ => Real.pi) r +
      (Icc (-2 * T) (2 * T)).indicator (fun _ => 3 / H) r) μ :=
    h12.add (hc (-2 * T) (2 * T) (3 / H))
  unfold leakageMajorant at h
  rw [integral_add h123 (hi.indicator (measurableSet_deficitFar T)),
    integral_add h12 (hc (-2 * T) (2 * T) (3 / H)),
    integral_add (hc (-H) H Real.pi) (hc (T - H) (T + H) Real.pi),
    integral_indicator_const Real.pi measurableSet_Icc,
    integral_indicator_const Real.pi measurableSet_Icc,
    integral_indicator_const (3 / H) measurableSet_Icc,
    integral_indicator (measurableSet_deficitFar T)] at h
  simp only [smul_eq_mul] at h
  have heq : (∫ r in {r : ℝ | 2 * T < |r|}, 12 * T / (1 + r ^ 2)
      ∂μ) = 12 * T * measureCauchyTail μ T := by
    simp only [measureCauchyTail, div_eq_mul_inv, one_mul, integral_const_mul]
  rw [heq] at h
  simpa only [mul_comm] using h

private theorem normalized_leakage_bound (μ : Measure ℝ)
    (hfin : ∀ a b : ℝ, μ (Icc a b) ≠ ⊤)
    (hiC : Integrable (fun r : ℝ => 1 / (1 + r ^ 2)) μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hmass : ∀ a b : ℝ, a ≤ b → μ (Icc a b) ≤
      ENNReal.ofReal (C * (b - a + 1) * Real.log (max |a| |b| + 3)))
    {T : ℝ} (hT : 1 ≤ T) :
    (∫ r, deficitPoissonLeakage T r ∂μ) / T ≤
      (6 * Real.pi + 15) * C * ((Real.log T + Real.log 5) / Real.sqrt T) +
      12 * measureCauchyTail μ T := by
  have hT0 : 0 < T := by linarith
  set H := Real.sqrt T
  have hH : 0 < H := Real.sqrt_pos.mpr hT0
  have hH1 : 1 ≤ H := by simpa [H] using Real.sqrt_le_sqrt hT
  have hHT : H ≤ T := by nlinarith [Real.sq_sqrt hT0.le]
  have hsq : H * H = T := Real.mul_self_sqrt hT0.le
  set L := Real.log T + Real.log 5
  have hL : 0 ≤ L := add_nonneg (Real.log_nonneg hT) (Real.log_nonneg (by norm_num))
  have hinterval (a b K : ℝ) (hab : a ≤ b) (hlen : b - a + 1 ≤ K)
      (hloc : max |a| |b| ≤ 2 * T) :
      μ.real (Icc a b) ≤ C * K * L := by
    have hw : 0 ≤ b - a + 1 := by linarith
    have hK : 0 ≤ K := hw.trans hlen
    have hlog : 0 ≤ Real.log (max |a| |b| + 3) :=
      Real.log_nonneg (by linarith [abs_nonneg a, le_max_left |a| |b|])
    have hm := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hmass a b hab)
    rw [ENNReal.toReal_ofReal (mul_nonneg (mul_nonneg hC hw) hlog)] at hm
    refine hm.trans ?_
    have hlog' : Real.log (max |a| |b| + 3) ≤ L := by
      calc
        Real.log (max |a| |b| + 3) ≤ Real.log (5 * T) :=
          Real.log_le_log (by positivity) (by linarith)
        _ = L := by rw [Real.log_mul (by norm_num) hT0.ne']; dsimp [L]; ring
    exact mul_le_mul (mul_le_mul_of_nonneg_left hlen hC) hlog' hlog (mul_nonneg hC hK)
  have hm0 : μ.real (Icc (-H) H) ≤ C * (3 * H) * L := by
    apply hinterval _ _ _ (by linarith) (by linarith)
    simpa [abs_of_pos hH] using (show H ≤ 2 * T by linarith)
  have hmT : μ.real (Icc (T - H) (T + H)) ≤ C * (3 * H) * L := by
    apply hinterval _ _ _ (by linarith) (by linarith)
    rw [abs_of_nonneg (sub_nonneg.mpr hHT), abs_of_nonneg (by linarith : 0 ≤ T + H)]
    exact max_le (by linarith) (by linarith)
  have hmB : μ.real (Icc (-2 * T) (2 * T)) ≤ C * (5 * T) * L := by
    apply hinterval _ _ _ (by linarith) (by linarith)
    rw [abs_of_nonpos (by linarith : -2 * T ≤ 0), abs_of_pos (by positivity : 0 < 2 * T)]
    simp
  have hbase := integral_measureLeakage_le μ hfin hiC hT hH
  have hbound : (∫ r, deficitPoissonLeakage T r ∂μ) ≤
      Real.pi * (C * (3 * H) * L) + Real.pi * (C * (3 * H) * L) +
      (3 / H) * (C * (5 * T) * L) + 12 * T * measureCauchyTail μ T :=
    hbase.trans (add_le_add (add_le_add
      (add_le_add (mul_le_mul_of_nonneg_left hm0 Real.pi_pos.le)
        (mul_le_mul_of_nonneg_left hmT Real.pi_pos.le))
      (mul_le_mul_of_nonneg_left hmB (show 0 ≤ 3 / H by positivity))) le_rfl)
  apply (div_le_div_of_nonneg_right hbound hT0.le).trans
  apply le_of_eq
  change (_ / T) = (6 * Real.pi + 15) * C * (L / H) + 12 * measureCauchyTail μ T
  rw [← hsq]
  field_simp [hH.ne']
  ring

/-- The full Poisson endpoint leakage is negligible on the required linear height scale. -/
private theorem tendsto_integral_measureLeakage_div (μ : Measure ℝ)
    (hfin : ∀ a b : ℝ, μ (Icc a b) ≠ ⊤)
    (hiC : Integrable (fun r : ℝ => 1 / (1 + r ^ 2)) μ)
    (hmassExists : ∃ C : ℝ, 0 ≤ C ∧ ∀ a b : ℝ, a ≤ b →
      μ (Icc a b) ≤ ENNReal.ofReal (C * (b - a + 1) * Real.log (max |a| |b| + 3))) :
    Tendsto (fun T : ℝ => (∫ r, deficitPoissonLeakage T r ∂μ) / T)
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hmass⟩ := hmassExists
  have hlog : Tendsto (fun T : ℝ => Real.log T / Real.sqrt T) atTop (𝓝 0) := by
    have h := ((Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      Real.tendsto_sqrt_atTop).const_mul 2
    rw [mul_zero] at h
    refine h.congr' ((eventually_gt_atTop 0).mono fun T hT => ?_)
    simp only [Function.comp, pow_one, one_mul, add_zero]
    rw [Real.log_sqrt hT.le]
    ring
  have hc : Tendsto (fun T : ℝ => Real.log 5 / Real.sqrt T) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop
  have hnear : Tendsto (fun T : ℝ =>
      (6 * Real.pi + 15) * C * ((Real.log T + Real.log 5) / Real.sqrt T)) atTop (𝓝 0) := by
    simpa only [← add_div, add_zero, mul_zero] using
      (hlog.add hc).const_mul ((6 * Real.pi + 15) * C)
  have hu : Tendsto (fun T : ℝ =>
      (6 * Real.pi + 15) * C * ((Real.log T + Real.log 5) / Real.sqrt T) +
      12 * measureCauchyTail μ T) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using hnear.add ((tendsto_measureCauchyTail μ hiC).const_mul 12)
  apply squeeze_zero' _ _ hu
  · filter_upwards [eventually_ge_atTop 1] with T hT
    exact div_nonneg (integral_nonneg (deficitPoissonLeakage_nonneg T)) (by linarith)
  · filter_upwards [eventually_ge_atTop 1] with T hT
    exact normalized_leakage_bound μ hfin hiC hC hmass hT

/-- The canonical inverse-square mass outside the distant height window. -/
def deficitCauchyTail {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (T : ℝ) : ℝ :=
  measureCauchyTail (boundaryMeasure hW) T

theorem tendsto_deficitCauchyTail {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    Tendsto (deficitCauchyTail hW) atTop (𝓝 0) :=
  tendsto_measureCauchyTail (boundaryMeasure hW) (by simpa using integrable_inv_one_add_sq_sub hW 0)

theorem integrable_deficitPoissonLeakage {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {T : ℝ} (hT : 1 ≤ T) : Integrable (deficitPoissonLeakage T) (boundaryMeasure hW) :=
  integrable_measureLeakage (boundaryMeasure hW) (boundaryMeasure_Icc_ne_top hW)
    (by simpa using integrable_inv_one_add_sq_sub hW 0) hT

/-- A finite-height bound retaining every endpoint atom and all diffuse mass. -/
theorem integral_deficitPoissonLeakage_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {T H : ℝ} (hT : 1 ≤ T) (hH : 0 < H) :
    ∫ r, deficitPoissonLeakage T r ∂boundaryMeasure hW ≤
      Real.pi * (boundaryMeasure hW).real (Icc (-H) H) +
      Real.pi * (boundaryMeasure hW).real (Icc (T - H) (T + H)) +
      (3 / H) * (boundaryMeasure hW).real (Icc (-2 * T) (2 * T)) +
      12 * T * deficitCauchyTail hW T :=
  integral_measureLeakage_le (boundaryMeasure hW) (boundaryMeasure_Icc_ne_top hW)
    (by simpa using integrable_inv_one_add_sq_sub hW 0) hT hH

/-- The canonical Poisson endpoint leakage is negligible on the linear height scale. -/
theorem tendsto_integral_deficitPoissonLeakage_div {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    Tendsto (fun T : ℝ => (∫ r, deficitPoissonLeakage T r ∂boundaryMeasure hW) / T)
      atTop (𝓝 0) :=
  tendsto_integral_measureLeakage_div (boundaryMeasure hW) (boundaryMeasure_Icc_ne_top hW)
    (by simpa using integrable_inv_one_add_sq_sub hW 0) (exists_boundaryMeasure_Icc_le_length_log hW)

/-- The same leakage kernel is integrable against all actual zero ordinates. -/
theorem integrable_deficitOrdinatePoissonLeakage {T : ℝ} (hT : 1 ≤ T) :
    Integrable (deficitPoissonLeakage T) deficitOrdinateMeasure :=
  integrable_measureLeakage deficitOrdinateMeasure deficitOrdinateMeasure_Icc_ne_top
    integrable_deficitOrdinateCauchyWeight hT

/-- Actual zero-copy endpoint leakage is negligible, without any support assumption. -/
theorem tendsto_integral_deficitOrdinatePoissonLeakage_div :
    Tendsto (fun T : ℝ => (∫ r, deficitPoissonLeakage T r ∂deficitOrdinateMeasure) / T)
      atTop (𝓝 0) :=
  tendsto_integral_measureLeakage_div deficitOrdinateMeasure deficitOrdinateMeasure_Icc_ne_top
    integrable_deficitOrdinateCauchyWeight exists_deficitOrdinateMeasure_Icc_le_length_log

end RHTower.WeilSpectral

end
