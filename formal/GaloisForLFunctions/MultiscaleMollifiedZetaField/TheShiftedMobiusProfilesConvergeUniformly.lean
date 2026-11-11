import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheMobiusKernelConvergesInMean

/-!
# Uniform Möbius transforms of shifted smooth profiles

Multiplication by the reciprocal-logarithmic power becomes multiplication
of the test by an exponential. The bounded smoothed-kernel estimate gives
a common bound down to the cutoff endpoint and uniform convergence away
from it. The limiting transform is `P′−vP`.
-/

open ArithmeticFunction Filter MeasureTheory Set Topology
open scoped ArithmeticFunction.Moebius

noncomputable section

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

/-- A smooth profile with a reciprocal-logarithmic power shift. -/
def normalizedShiftedMobiusProfile (P : ℝ → ℝ) (L u v : ℝ) : ℝ :=
  L * (∑ n ∈ Finset.Icc 1 ⌊Real.exp (L * u)⌋₊,
    ((moebius n : ℤ) : ℝ) / (n : ℝ) * Real.exp (v * Real.log n / L) *
      P (u - Real.log n / L))

/-- The power shift is an exponential change of the smooth logarithmic test. -/
theorem normalizedShiftedMobiusProfile_eq_test (P : ℝ → ℝ) (L u v : ℝ) :
    normalizedShiftedMobiusProfile P L u v = Real.exp (v * u) *
      scaledMobiusLogTest (fun x => P x * Real.exp (-v * x)) L u := by
  unfold normalizedShiftedMobiusProfile scaledMobiusLogTest
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have he : Real.exp (v * u) * Real.exp (-v * (u - Real.log n / L)) =
      Real.exp (v * Real.log n / L) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [← he]
  ring

/-- Shifted profiles are bounded and converge uniformly on every compact shift interval. -/
theorem normalizedShiftedMobiusProfile_compact_uniform
    {P P₁ P₂ : ℝ → ℝ} (hP : ∀ x, HasDerivAt P (P₁ x) x)
    (hP₁ : ∀ x, HasDerivAt P₁ (P₂ x) x) (hc₂ : Continuous P₂) (hP0 : P 0 = 0)
    {V : ℝ} (hV : 0 ≤ V) :
    (∃ B : ℝ, 0 ≤ B ∧ ∀ L : ℝ, 0 < L → ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (-V) V,
      |normalizedShiftedMobiusProfile P L u v| ≤ B) ∧
    (∀ δ ε : ℝ, 0 < δ → 0 < ε → ∀ᶠ L : ℝ in atTop, ∀ u ∈ Icc δ 1, ∀ v ∈ Icc (-V) V,
      |normalizedShiftedMobiusProfile P L u v - (P₁ u - v * P u)| < ε) := by
  let f (v x : ℝ) := P x * Real.exp (-v * x)
  let f₁ (v x : ℝ) := (P₁ x - v * P x) * Real.exp (-v * x)
  let f₂ (v x : ℝ) := (P₂ x - 2 * v * P₁ x + v ^ 2 * P x) * Real.exp (-v * x)
  have he (v x : ℝ) : HasDerivAt (fun x => Real.exp (-v * x)) (-v * Real.exp (-v * x)) x := by
    exact ((Real.hasDerivAt_exp _).comp x ((hasDerivAt_id x).const_mul (-v))).congr_deriv (by simp only [id_eq]; ring)
  have hf (v x : ℝ) : HasDerivAt (f v) (f₁ v x) x := by
    apply ((hP x).mul (he v x)).congr_deriv
    dsimp only [f₁]
    ring
  have hf₁ (v x : ℝ) : HasDerivAt (f₁ v) (f₂ v x) x := by
    apply (((hP₁ x).sub ((hP x).const_mul v)).mul (he v x)).congr_deriv
    dsimp only [f₂, Pi.sub_apply]
    ring
  have hcP : Continuous P := continuous_iff_continuousAt.mpr (fun x => (hP x).continuousAt)
  have hcP₁ : Continuous P₁ := continuous_iff_continuousAt.mpr (fun x => (hP₁ x).continuousAt)
  have hcf₂ : Continuous (fun q : ℝ × ℝ => f₂ q.1 q.2) := by dsimp only [f₂]; fun_prop
  have hcf₂v (v : ℝ) : Continuous (f₂ v) := by dsimp only [f₂]; fun_prop
  have hcg : Continuous (fun q : ℝ × ℝ => P₁ q.2 - q.1 * P q.2) := by fun_prop
  have hcompact : IsCompact ((Icc (-V) V) ×ˢ (Icc (0 : ℝ) 1)) := isCompact_Icc.prod isCompact_Icc
  have hmem : ((0, 0) : ℝ × ℝ) ∈ (Icc (-V) V) ×ˢ (Icc (0 : ℝ) 1) :=
    ⟨⟨neg_nonpos.mpr hV, hV⟩, ⟨le_rfl, zero_le_one⟩⟩
  obtain ⟨M, hM⟩ := hcompact.exists_bound_of_continuousOn hcf₂.continuousOn
  obtain ⟨B₀, hB₀⟩ := hcompact.exists_bound_of_continuousOn hcg.continuousOn
  have hM0 : 0 ≤ M := (norm_nonneg (f₂ 0 0)).trans (hM (0, 0) hmem)
  have hB₀0 : 0 ≤ B₀ := (norm_nonneg (P₁ 0 - 0 * P 0)).trans (hB₀ (0, 0) hmem)
  let A := Real.exp V * |P₁ 0|
  let B := Real.exp V * M
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hexp {u v : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (-V) V) :
      Real.exp (v * u) ≤ Real.exp V := by
    apply Real.exp_le_exp.mpr
    exact (mul_le_mul_of_nonneg_right hv.2 hu.1).trans
      ((mul_le_mul_of_nonneg_left hu.2 hV).trans_eq (mul_one _))
  have hvalue (v u : ℝ) : Real.exp (v * u) * f₁ v u = P₁ u - v * P u := by
    have he' : Real.exp (v * u) * Real.exp (-v * u) = 1 := by
      rw [← Real.exp_add, show v * u + -v * u = 0 by ring, Real.exp_zero]
    dsimp only [f₁]
    calc
      _ = (P₁ u - v * P u) * (Real.exp (v * u) * Real.exp (-v * u)) := by ring
      _ = _ := by rw [he', mul_one]
  have herr {L u v : ℝ} (hL : 0 < L) (hu : u ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (-V) V) :
      |normalizedShiftedMobiusProfile P L u v - (P₁ u - v * P u)| ≤
        A * |smoothedMobiusKernel (L * u) - 1| + B * smoothedMobiusKernelMeanError L := by
    have hf0 : f v 0 = 0 := by simp [f, hP0]
    have hh := scaledMobiusLogTest_error_bound (hf v) (hf₁ v) (hcf₂v v) hf0 M
      (fun x hx => hM (v, x) ⟨hv, hx⟩) hL hu
    have hzero : f₁ v 0 = P₁ 0 := by simp [f₁, hP0]
    rw [hzero] at hh
    rw [normalizedShiftedMobiusProfile_eq_test, ← hvalue v u, ← mul_sub,
      abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp V * |scaledMobiusLogTest (f v) L u - f₁ v u| :=
        mul_le_mul_of_nonneg_right (hexp hu hv) (abs_nonneg _)
      _ ≤ Real.exp V * (|P₁ 0| * |smoothedMobiusKernel (L * u) - 1| + M * smoothedMobiusKernelMeanError L) :=
        mul_le_mul_of_nonneg_left hh (Real.exp_nonneg _)
      _ = _ := by dsimp only [A, B]; ring
  constructor
  · obtain ⟨D, hD, hkernel⟩ := smoothedMobiusKernel_bounded_and_tendsto.1
    refine ⟨B₀ + (A + B) * (D + 1), by positivity, ?_⟩
    intro L hL u hu v hv
    have hF {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
        |smoothedMobiusKernel (L * x) - 1| ≤ D + 1 := by
      have hh : |smoothedMobiusKernel (L * x)| + |(1 : ℝ)| ≤ D + 1 := by
        simpa only [abs_one] using add_le_add (hkernel _ (mul_nonneg hL.le hx.1)) (le_refl (1 : ℝ))
      exact (abs_sub _ _).trans hh
    have hE : smoothedMobiusKernelMeanError L ≤ D + 1 := by
      have hc := ((continuousOn_dilatedSmoothedMobiusKernel hL.le).sub
        (continuous_const : Continuous (fun _ : ℝ => (1 : ℝ))).continuousOn).abs
      have hh := intervalIntegral.integral_mono_on zero_le_one
        (hc.intervalIntegrable_of_Icc zero_le_one)
        (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => D + 1) volume 0 1)
        (fun x hx => hF hx)
      simpa only [Pi.sub_apply, intervalIntegral.integral_const, sub_zero, one_smul,
        smoothedMobiusKernelMeanError] using hh
    calc
      _ = |(normalizedShiftedMobiusProfile P L u v - (P₁ u - v * P u)) + (P₁ u - v * P u)| := by rw [sub_add_cancel]
      _ ≤ |normalizedShiftedMobiusProfile P L u v - (P₁ u - v * P u)| + |P₁ u - v * P u| := abs_add_le _ _
      _ ≤ (A * |smoothedMobiusKernel (L * u) - 1| + B * smoothedMobiusKernelMeanError L) + B₀ :=
        add_le_add (herr hL hu hv) (by simpa only [Real.norm_eq_abs] using hB₀ (v, u) ⟨hv, hu⟩)
      _ ≤ (A * (D + 1) + B * (D + 1)) + B₀ :=
        add_le_add (add_le_add (mul_le_mul_of_nonneg_left (hF hu) hA)
          (mul_le_mul_of_nonneg_left hE hB)) le_rfl
      _ = _ := by ring
  · intro δ ε hδ hε
    let η := ε / (2 * (A + 1))
    have hη : 0 < η := by dsimp only [η]; positivity
    have htail : ∀ᶠ y : ℝ in atTop, |smoothedMobiusKernel y - 1| < η := by
      simpa only [Metric.mem_ball, Real.dist_eq] using
        smoothedMobiusKernel_bounded_and_tendsto.2.eventually (Metric.ball_mem_nhds 1 hη)
    obtain ⟨K, hK⟩ := eventually_atTop.mp htail
    have hmean : ∀ᶠ L : ℝ in atTop, B * smoothedMobiusKernelMeanError L < ε / 2 :=
      (tendsto_smoothedMobiusKernelMeanError.const_mul B).eventually_lt_const
        (by simpa only [mul_zero] using half_pos hε)
    filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_ge_atTop (K / δ), hmean] with L hL hLK hLM
    intro u hu v hv
    have hKu : K ≤ L * u := ((div_le_iff₀ hδ).mp hLK).trans
      (mul_le_mul_of_nonneg_left hu.1 hL.le)
    have hfirst : A * |smoothedMobiusKernel (L * u) - 1| ≤ ε / 2 := by
      calc
        _ ≤ A * η := mul_le_mul_of_nonneg_left (hK (L * u) hKu).le hA
        _ ≤ (A + 1) * η := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hη.le
        _ = ε / 2 := by dsimp only [η]; field_simp [show A + 1 ≠ 0 by positivity]
    have hh := herr hL ⟨hδ.le.trans hu.1, hu.2⟩ hv
    linarith only [hh, hfirst, hLM]

/-- Fixed-shift form of the compact uniform profile limit. -/
theorem normalizedShiftedMobiusProfile_bounded_and_converges
    {P P₁ P₂ : ℝ → ℝ} (hP : ∀ x, HasDerivAt P (P₁ x) x)
    (hP₁ : ∀ x, HasDerivAt P₁ (P₂ x) x) (hc₂ : Continuous P₂) (hP0 : P 0 = 0) (v : ℝ) :
    (∃ B : ℝ, 0 ≤ B ∧ ∀ L : ℝ, 0 < L → ∀ u ∈ Icc (0 : ℝ) 1,
      |normalizedShiftedMobiusProfile P L u v| ≤ B) ∧
    (∀ δ ε : ℝ, 0 < δ → 0 < ε → ∀ᶠ L : ℝ in atTop, ∀ u ∈ Icc δ 1,
      |normalizedShiftedMobiusProfile P L u v - (P₁ u - v * P u)| < ε) := by
  have hh := normalizedShiftedMobiusProfile_compact_uniform hP hP₁ hc₂ hP0 (abs_nonneg v)
  have hv : v ∈ Icc (-|v|) |v| := ⟨neg_abs_le v, le_abs_self v⟩
  constructor
  · obtain ⟨B, hB, hb⟩ := hh.1
    exact ⟨B, hB, fun L hL u hu => hb L hL u hu v hv⟩
  · intro δ ε hδ hε
    filter_upwards [hh.2 δ ε hδ hε] with L hL
    exact fun u hu => hL u hu v hv

end GaloisForLFunctions.MultiscaleMollifiedZetaField
