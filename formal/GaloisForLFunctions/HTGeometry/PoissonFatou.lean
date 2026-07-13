import Mathlib.Analysis.Complex.Poisson
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Fatou's theorem: a.e. boundary limits of Poisson integrals

The Poisson integral of an `L¹` function on the circle converges almost everywhere to the function
as the radius tends to `1`.  This is the analytic crux of the Szegő outer function's boundary
identity `|D|² = w` (and hence of the upper bound half of the first Szegő limit theorem).  mathlib
supplies the Poisson kernel with its pointwise bounds and normalization (via the Poisson
representation of continuous functions) and the Lebesgue differentiation theorem; this module builds
the a.e. boundary convergence on top of them.

This file develops the angular Poisson kernel `P_r(t) = (1-r²)/(1 - 2r cos t + r²)` and its
elementary estimates.
-/

namespace GaloisForLFunctions.HTGeometry

open Real MeasureTheory Complex intervalIntegral Metric Filter Topology
open scoped Real

/-- The angular Poisson kernel `P_r(t) = (1-r²)/(1 - 2r cos t + r²)`. -/
noncomputable def poissonKer (r t : ℝ) : ℝ := (1 - r ^ 2) / (1 - 2 * r * Real.cos t + r ^ 2)

/-- The Poisson kernel denominator is strictly positive for `|r| < 1`. -/
theorem poissonKer_denom_pos {r : ℝ} (hr : |r| < 1) (t : ℝ) :
    0 < 1 - 2 * r * Real.cos t + r ^ 2 := by
  have hrc : r * Real.cos t ≤ |r| := by
    calc r * Real.cos t ≤ |r * Real.cos t| := le_abs_self _
      _ = |r| * |Real.cos t| := abs_mul r _
      _ ≤ |r| * 1 := by
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg r); exact Real.abs_cos_le_one t
      _ = |r| := mul_one _
  have hrr : r ^ 2 = |r| ^ 2 := (sq_abs r).symm
  have hp : 0 < 1 - |r| := by linarith
  nlinarith [hrc, hrr, mul_pos hp hp]

/-- The Poisson kernel is nonnegative for `0 ≤ r < 1`. -/
theorem poissonKer_nonneg {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (t : ℝ) :
    0 ≤ poissonKer r t := by
  rw [poissonKer]
  apply div_nonneg
  · nlinarith
  · exact (poissonKer_denom_pos (by rw [abs_of_nonneg hr0]; exact hr1) t).le

/-- The Poisson kernel denominator equals `‖e^{it} - r‖²`. -/
theorem poissonKer_denom_eq (r t : ℝ) :
    1 - 2 * r * Real.cos t + r ^ 2 = ‖Complex.exp (t * Complex.I) - (r : ℂ)‖ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, Complex.ofReal_re, Complex.ofReal_im]
  nlinarith [Real.sin_sq_add_cos_sq t]

/-- Uniform upper bound: `P_r(t) ≤ (1+r)/(1-r)`, attained at `t = 0`. -/
theorem poissonKer_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (t : ℝ) :
    poissonKer r t ≤ (1 + r) / (1 - r) := by
  rw [poissonKer]
  have hden : 0 < 1 - 2 * r * Real.cos t + r ^ 2 :=
    poissonKer_denom_pos (by rw [abs_of_nonneg hr0]; exact hr1) t
  have hden' : (1 - r) ^ 2 ≤ 1 - 2 * r * Real.cos t + r ^ 2 := by
    nlinarith [mul_nonneg hr0 (sub_nonneg.mpr (Real.cos_le_one t))]
  rw [div_le_div_iff₀ hden (by linarith : (0:ℝ) < 1 - r)]
  nlinarith [mul_le_mul_of_nonneg_left hden' (show (0:ℝ) ≤ 1 + r by linarith)]

/-- The angular Poisson kernel is mathlib's geometric Poisson kernel at a real disk point. -/
theorem poissonKer_eq_poissonKernel {r : ℝ} (hr0 : 0 ≤ r) (t : ℝ) :
    poissonKer r t = poissonKernel 0 (r : ℂ) (Complex.exp (t * Complex.I)) := by
  rw [poissonKernel_def, poissonKer, poissonKer_denom_eq r t]
  simp only [sub_zero, Complex.norm_exp_ofReal_mul_I]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
  ring_nf

/-- **Normalization of the Poisson kernel**: `∫₀²π P_r(t) dt = 2π`.  Obtained from mathlib's Poisson
representation applied to the constant function `1`. -/
theorem poissonKer_integral {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∫ t in (0:ℝ)..(2 * π), poissonKer r t = 2 * π := by
  have hw : (r : ℂ) ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1
  have hf : DiffContOnCl ℂ (fun _ : ℂ => (1 : ℂ)) (ball 0 1) :=
    (differentiable_const (1 : ℂ)).differentiableOn.diffContOnCl
  have hrep := hf.circleAverage_poissonKernel_smul hw
  have hfun : (poissonKernel 0 (r : ℂ) • (fun _ : ℂ => (1 : ℂ)))
      = fun z => ((poissonKernel 0 (r : ℂ) z : ℝ) : ℂ) := by
    funext z; rw [Pi.smul_apply', Complex.real_smul, mul_one]
  rw [hfun, Real.circleAverage] at hrep
  have hcm : ∀ θ : ℝ, poissonKernel 0 (r : ℂ) (circleMap 0 1 θ) = poissonKer r θ := by
    intro θ
    rw [poissonKer_eq_poissonKernel hr0]
    congr 1
    simp [circleMap]
  simp_rw [hcm] at hrep
  rw [intervalIntegral.integral_ofReal] at hrep
  have hr : (2 * π)⁻¹ * (∫ θ in (0:ℝ)..(2 * π), poissonKer r θ) = 1 := by
    have := hrep
    rw [Complex.real_smul, ← Complex.ofReal_mul] at this
    exact_mod_cast this
  have hpi : (2 * π) ≠ 0 := by positivity
  field_simp at hr
  linarith [hr]

/-- `1 - cos t ≥ 2t²/π²` on `[0, π]` (from Jordan's inequality). -/
theorem one_sub_cos_ge {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ π) :
    2 * t ^ 2 / π ^ 2 ≤ 1 - Real.cos t := by
  have hpi : 0 < π := Real.pi_pos
  have hhalf : 1 - Real.cos t = 2 * Real.sin (t / 2) ^ 2 := by
    have hc : Real.cos t = 2 * Real.cos (t / 2) ^ 2 - 1 := by
      have := Real.cos_two_mul (t / 2); rwa [show 2 * (t / 2) = t by ring] at this
    nlinarith [Real.sin_sq_add_cos_sq (t / 2)]
  have hjordan : 2 / π * (t / 2) ≤ Real.sin (t / 2) := Real.mul_le_sin (by linarith) (by linarith)
  have hlow : t / π ≤ Real.sin (t / 2) := by
    have heq : (2:ℝ) / π * (t / 2) = t / π := by ring
    linarith [heq ▸ hjordan]
  have htpi : 0 ≤ t / π := by positivity
  rw [hhalf]
  have hsq : (t / π) ^ 2 ≤ Real.sin (t / 2) ^ 2 := pow_le_pow_left₀ htpi hlow 2
  have hconv : 2 * (t / π) ^ 2 = 2 * t ^ 2 / π ^ 2 := by field_simp
  nlinarith [hsq, hconv]

/-- Lower bound on the denominator away from `0`: `denom ≥ 4r t²/π²` on `[0, π]`. -/
theorem poissonKer_denom_ge {r : ℝ} (hr0 : 0 < r) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ π) :
    4 * r * t ^ 2 / π ^ 2 ≤ 1 - 2 * r * Real.cos t + r ^ 2 := by
  have hc := one_sub_cos_ge h0 h1
  have key : 4 * r * t ^ 2 / π ^ 2 ≤ 2 * r * (1 - Real.cos t) := by
    rw [show 4 * r * t ^ 2 / π ^ 2 = 2 * r * (2 * t ^ 2 / π ^ 2) by ring]
    exact mul_le_mul_of_nonneg_left hc (by linarith)
  nlinarith [key, sq_nonneg (1 - r)]

/-- Decay bound: `P_r(t) ≤ (1-r²)π²/(4r t²)` on `(0, π]`, giving mass concentration at `0`. -/
theorem poissonKer_le_decay {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) {t : ℝ} (h0 : 0 < t) (h1 : t ≤ π) :
    poissonKer r t ≤ (1 - r ^ 2) * π ^ 2 / (4 * r * t ^ 2) := by
  rw [poissonKer]
  have hden := poissonKer_denom_ge hr0 h0.le h1
  have hdenpos : 0 < 1 - 2 * r * Real.cos t + r ^ 2 :=
    poissonKer_denom_pos (by rw [abs_of_nonneg hr0.le]; exact hr1) t
  have hnn : 0 ≤ 1 - r ^ 2 := by nlinarith
  have hpi : 0 < π := Real.pi_pos
  rw [div_le_div_iff₀ hdenpos (by positivity)]
  have hpe : 4 * r * t ^ 2 ≤ π ^ 2 * (1 - 2 * r * Real.cos t + r ^ 2) := by
    have := (div_le_iff₀ (by positivity : (0:ℝ) < π ^ 2)).mp hden
    linarith [this]
  nlinarith [mul_le_mul_of_nonneg_left hpe hnn]

/-- The Poisson kernel `t ↦ P_r(t)` is continuous for `|r| < 1`. -/
theorem poissonKer_continuous {r : ℝ} (hr : |r| < 1) : Continuous (poissonKer r) := by
  apply Continuous.div continuous_const
  · fun_prop
  · intro t; exact (poissonKer_denom_pos hr t).ne'

/-- **Mass concentration**: away from `0`, the Poisson integral tends to `0` as `r → 1⁻`.  Together
with nonnegativity and the normalization `∫ P_r = 2π`, this is the approximate-identity property of
the Poisson kernel that drives a.e. boundary convergence. -/
theorem poissonKer_concentration {δ : ℝ} (hδ0 : 0 < δ) (hδπ : δ ≤ π) :
    Tendsto (fun r : ℝ => ∫ t in δ..π, poissonKer r t) (𝓝[<] 1) (𝓝 0) := by
  have hπ : 0 < π := Real.pi_pos
  set C := π ^ 2 * (π - δ) / (2 * δ ^ 2) with hC
  have hupper : Tendsto (fun r : ℝ => C * (1 - r ^ 2)) (𝓝[<] 1) (𝓝 0) := by
    rw [show (0:ℝ) = C * 0 by ring]
    apply Tendsto.const_mul
    have h : Tendsto (fun r : ℝ => 1 - r ^ 2) (𝓝 1) (𝓝 0) := by
      have hc : Tendsto (fun r : ℝ => 1 - r ^ 2) (𝓝 1) (𝓝 (1 - 1 ^ 2)) :=
        (by fun_prop : Continuous (fun r : ℝ => 1 - r ^ 2)).tendsto 1
      simpa using hc
    exact h.mono_left nhdsWithin_le_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper ?_ ?_
  · filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (show (1/2:ℝ) < 1 by norm_num)),
      self_mem_nhdsWithin] with r hr hr1
    have hr0 : (0:ℝ) < r := by simp only [Set.mem_Ioi] at hr; linarith
    have hr1' : r < 1 := by simpa using hr1
    exact intervalIntegral.integral_nonneg hδπ (fun t _ => poissonKer_nonneg hr0.le hr1' t)
  · filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (show (1/2:ℝ) < 1 by norm_num)),
      self_mem_nhdsWithin] with r hr hr1
    simp only [Set.mem_Ioi] at hr
    have hr0 : (0:ℝ) < r := by linarith
    have hr1' : r < 1 := by simpa using hr1
    have habs : |r| < 1 := by rw [abs_of_nonneg hr0.le]; exact hr1'
    have hcont : Continuous (poissonKer r) := poissonKer_continuous habs
    calc ∫ t in δ..π, poissonKer r t
        ≤ ∫ _t in δ..π, (1 - r ^ 2) * π ^ 2 / (4 * r * δ ^ 2) := by
          apply intervalIntegral.integral_mono_on hδπ (hcont.intervalIntegrable δ π)
            intervalIntegrable_const
          intro t ht
          have ht0 : 0 < t := by linarith [ht.1]
          calc poissonKer r t ≤ (1 - r ^ 2) * π ^ 2 / (4 * r * t ^ 2) :=
                poissonKer_le_decay hr0 hr1' ht0 ht.2
            _ ≤ (1 - r ^ 2) * π ^ 2 / (4 * r * δ ^ 2) := by
                have hnn : 0 ≤ (1 - r ^ 2) * π ^ 2 := by
                  have : (0:ℝ) < 1 - r ^ 2 := by
                    nlinarith [mul_pos (show (0:ℝ) < 1 - r by linarith)
                      (show (0:ℝ) < 1 + r by linarith)]
                  positivity
                gcongr
                exact ht.1
      _ = (1 - r ^ 2) * (π ^ 2 * (π - δ) / (4 * r * δ ^ 2)) := by
          rw [intervalIntegral.integral_const, smul_eq_mul]; ring
      _ ≤ C * (1 - r ^ 2) := by
          have hX : π ^ 2 * (π - δ) / (4 * r * δ ^ 2) ≤ C := by
            rw [hC]; gcongr; nlinarith [pow_pos hδ0 2]
          nlinarith [mul_le_mul_of_nonneg_left hX (show (0:ℝ) ≤ 1 - r ^ 2 by nlinarith)]

/-- The Poisson kernel is even in `t`. -/
theorem poissonKer_even (r t : ℝ) : poissonKer r (-t) = poissonKer r t := by
  simp [poissonKer, Real.cos_neg]

/-- The Poisson kernel is `2π`-periodic in `t`. -/
theorem poissonKer_periodic (r : ℝ) : Function.Periodic (poissonKer r) (2 * π) := by
  intro t; simp [poissonKer, Real.cos_add, Real.cos_two_pi, Real.sin_two_pi]

/-- `∫_{δ}^{π} P_r = ∫_{-π}^{-δ} P_r` by evenness. -/
theorem poissonKer_integral_neg (r δ : ℝ) :
    ∫ t in δ..π, poissonKer r t = ∫ t in (-π)..(-δ), poissonKer r t := by
  have h1 : ∫ t in δ..π, poissonKer r t = ∫ t in δ..π, poissonKer r (-t) :=
    intervalIntegral.integral_congr (fun t _ => (poissonKer_even r t).symm)
  rw [h1, intervalIntegral.integral_comp_neg (fun t => poissonKer r t)]

/-- **Normalization on the symmetric interval**: `∫_{-π}^{π} P_r = 2π`. -/
theorem poissonKer_integral_symm {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∫ t in (-π)..π, poissonKer r t = 2 * π := by
  have h := (poissonKer_periodic r).intervalIntegral_add_eq (-π) 0
  rw [show (-π) + 2 * π = π by ring, show (0:ℝ) + 2 * π = 2 * π by ring] at h
  rw [h]; exact poissonKer_integral hr0 hr1

/-- **Concentration on the symmetric interval**: `∫_{-π}^{-δ} P_r + ∫_{δ}^{π} P_r → 0` as `r → 1⁻`. -/
theorem poissonKer_concentration_symm {δ : ℝ} (hδ0 : 0 < δ) (hδπ : δ ≤ π) :
    Tendsto (fun r : ℝ => (∫ t in (-π)..(-δ), poissonKer r t) + ∫ t in δ..π, poissonKer r t)
      (𝓝[<] 1) (𝓝 0) := by
  have key : Tendsto
      (fun r : ℝ => (∫ t in δ..π, poissonKer r t) + ∫ t in δ..π, poissonKer r t) (𝓝[<] 1) (𝓝 0) := by
    rw [show (0:ℝ) = 0 + 0 by ring]
    exact (poissonKer_concentration hδ0 hδπ).add (poissonKer_concentration hδ0 hδπ)
  refine key.congr (fun r => ?_)
  rw [poissonKer_integral_neg r δ]

theorem poissonKer_split_bound {f : ℝ → ℝ} (hf : Continuous f) {r ε δ M : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hδ0 : 0 < δ) (hδπ : δ ≤ π) (hε : 0 < ε) (hM0 : 0 ≤ M)
    (hsmall : ∀ t ∈ Set.Icc (-δ) δ, |f t - f 0| ≤ ε / 2)
    (hbig : ∀ t ∈ Set.Icc (-π) π, |f t - f 0| ≤ M) :
    |∫ t in (-π)..π, poissonKer r t * (f t - f 0)|
      ≤ ε / 2 * (2 * π) + M * ((∫ t in (-π)..(-δ), poissonKer r t) + ∫ t in δ..π, poissonKer r t) := by
  have habs : |r| < 1 := by rw [abs_of_nonneg hr0]; exact hr1
  have hcont : Continuous (poissonKer r) := poissonKer_continuous habs
  have hg : Continuous (fun t => poissonKer r t * (f t - f 0)) := hcont.mul (hf.sub continuous_const)
  have hnn : ∀ t, 0 ≤ poissonKer r t := fun t => poissonKer_nonneg hr0 hr1 t
  have hπ : 0 < π := Real.pi_pos
  set A := ∫ t in (-π)..(-δ), poissonKer r t * (f t - f 0)
  set B := ∫ t in (-δ)..δ, poissonKer r t * (f t - f 0)
  set Cc := ∫ t in δ..π, poissonKer r t * (f t - f 0)
  have hsplit : (∫ t in (-π)..π, poissonKer r t * (f t - f 0)) = A + (B + Cc) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (a := -π) (b := -δ) (c := π)
      (hg.intervalIntegrable _ _) (hg.intervalIntegrable _ _),
      ← intervalIntegral.integral_add_adjacent_intervals (a := -δ) (b := δ) (c := π)
        (hg.intervalIntegrable _ _) (hg.intervalIntegrable _ _)]
  have hmid : |B| ≤ ε / 2 * (2 * π) := by
    have hb1 : |B| ≤ ∫ t in (-δ)..δ, ε / 2 * poissonKer r t := by
      apply le_trans (intervalIntegral.abs_integral_le_integral_abs (by linarith))
      apply intervalIntegral.integral_mono_on (by linarith)
        (hg.abs.intervalIntegrable _ _) ((continuous_const.mul hcont).intervalIntegrable _ _)
      intro t ht
      rw [abs_mul, abs_of_nonneg (hnn t), mul_comm]
      exact mul_le_mul_of_nonneg_right (hsmall t (Set.mem_Icc.mpr ⟨ht.1, ht.2⟩)) (hnn t)
    rw [intervalIntegral.integral_const_mul] at hb1
    refine hb1.trans ?_
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    rw [← poissonKer_integral_symm hr0 hr1,
      ← intervalIntegral.integral_add_adjacent_intervals (a := -π) (b := -δ) (c := π)
        (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _),
      ← intervalIntegral.integral_add_adjacent_intervals (a := -δ) (b := δ) (c := π)
        (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
    have hL : 0 ≤ ∫ t in (-π)..(-δ), poissonKer r t :=
      intervalIntegral.integral_nonneg (by linarith) (fun t _ => hnn t)
    have hR : 0 ≤ ∫ t in δ..π, poissonKer r t :=
      intervalIntegral.integral_nonneg hδπ (fun t _ => hnn t)
    linarith
  have hLc : |A| ≤ M * ∫ t in (-π)..(-δ), poissonKer r t := by
    have : |A| ≤ ∫ t in (-π)..(-δ), M * poissonKer r t := by
      apply le_trans (intervalIntegral.abs_integral_le_integral_abs (by linarith))
      apply intervalIntegral.integral_mono_on (by linarith)
        (hg.abs.intervalIntegrable _ _) ((continuous_const.mul hcont).intervalIntegrable _ _)
      intro t ht
      rw [abs_mul, abs_of_nonneg (hnn t), mul_comm]
      exact mul_le_mul_of_nonneg_right (hbig t (Set.mem_Icc.mpr ⟨ht.1, by linarith [ht.2]⟩)) (hnn t)
    rwa [intervalIntegral.integral_const_mul] at this
  have hRc : |Cc| ≤ M * ∫ t in δ..π, poissonKer r t := by
    have : |Cc| ≤ ∫ t in δ..π, M * poissonKer r t := by
      apply le_trans (intervalIntegral.abs_integral_le_integral_abs hδπ)
      apply intervalIntegral.integral_mono_on hδπ
        (hg.abs.intervalIntegrable _ _) ((continuous_const.mul hcont).intervalIntegrable _ _)
      intro t ht
      rw [abs_mul, abs_of_nonneg (hnn t), mul_comm]
      exact mul_le_mul_of_nonneg_right (hbig t (Set.mem_Icc.mpr ⟨by linarith [ht.1], ht.2⟩)) (hnn t)
    rwa [intervalIntegral.integral_const_mul] at this
  rw [hsplit, mul_add]
  calc |A + (B + Cc)| ≤ |A| + |B + Cc| := abs_add_le A (B + Cc)
    _ ≤ |A| + (|B| + |Cc|) := by linarith [abs_add_le B Cc]
    _ ≤ _ := by linarith [hmid, hLc, hRc]

/-- **Poisson approximate-identity convergence at a continuity point.**  For `f` continuous, the
Poisson average `(2π)⁻¹∫_{-π}^{π} P_r(t) f(t) dt` converges to `f(0)` as `r → 1⁻`. -/
theorem tendsto_poissonKerAvg_of_continuous {f : ℝ → ℝ} (hf : Continuous f) :
    Tendsto (fun r : ℝ => (2 * π)⁻¹ * ∫ t in (-π)..π, poissonKer r t * f t) (𝓝[<] 1)
      (𝓝 (f 0)) := by
  have hπ : 0 < π := Real.pi_pos
  obtain ⟨M, hM0, hM⟩ : ∃ M, 0 ≤ M ∧ ∀ t ∈ Set.Icc (-π) π, |f t - f 0| ≤ M := by
    obtain ⟨t0, -, ht0⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr (by linarith))
      (by fun_prop : ContinuousOn (fun t : ℝ => |f t - f 0|) (Set.Icc (-π) π))
    exact ⟨|f t0 - f 0|, abs_nonneg _, fun t ht => isMaxOn_iff.mp ht0 t ht⟩
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨δ0, hδ00, hδc⟩ := Metric.continuousAt_iff.mp hf.continuousAt (ε / 2) (by linarith)
  set δ : ℝ := min (δ0 / 2) π with hδdef
  have hδ0 : 0 < δ := lt_min (by linarith) hπ
  have hδπ : δ ≤ π := min_le_right _ _
  have hsmall : ∀ t ∈ Set.Icc (-δ) δ, |f t - f 0| ≤ ε / 2 := by
    intro t ht
    rw [Set.mem_Icc] at ht
    have hlt : dist t 0 < δ0 := by
      rw [Real.dist_eq, sub_zero, abs_lt]
      constructor
      · have : -δ ≤ t := ht.1
        have : δ ≤ δ0 / 2 := min_le_left _ _
        linarith [ht.1, min_le_left (δ0/2) π]
      · linarith [ht.2, min_le_left (δ0/2) π]
    have := hδc hlt
    rw [Real.dist_eq] at this
    linarith [this]
  have hconc := poissonKer_concentration_symm hδ0 hδπ
  rw [Metric.tendsto_nhdsWithin_nhds] at hconc
  obtain ⟨η, hη0, hη⟩ := hconc (π * ε / (M + 1)) (by positivity)
  refine ⟨min η (1 / 2), lt_min hη0 (by norm_num), fun r hrmem hrdist => ?_⟩
  rw [Set.mem_Iio] at hrmem
  have h12 : |r - 1| < 1 / 2 := by
    rw [Real.dist_eq] at hrdist; exact lt_of_lt_of_le hrdist (min_le_right _ _)
  rw [abs_lt] at h12
  have hr0 : (0 : ℝ) ≤ r := by linarith [h12.1]
  -- avg - f 0 rewritten
  have habs : |r| < 1 := by rw [abs_of_nonneg hr0]; exact hrmem
  have hcont : Continuous (poissonKer r) := poissonKer_continuous habs
  have hf0 : (2 * π)⁻¹ * ∫ t in (-π)..π, poissonKer r t * f 0 = f 0 := by
    rw [intervalIntegral.integral_mul_const, poissonKer_integral_symm hr0 hrmem]
    field_simp
  have hdiff : (2 * π)⁻¹ * (∫ t in (-π)..π, poissonKer r t * f t) - f 0
      = (2 * π)⁻¹ * ∫ t in (-π)..π, poissonKer r t * (f t - f 0) := by
    have hI1 : IntervalIntegrable (fun t => poissonKer r t * f t) volume (-π) π :=
      (hcont.mul hf).intervalIntegrable _ _
    have hI2 : IntervalIntegrable (fun t => poissonKer r t * f 0) volume (-π) π :=
      (hcont.mul (continuous_const : Continuous fun _ : ℝ => f 0)).intervalIntegrable _ _
    have hint : (∫ t in (-π)..π, poissonKer r t * (f t - f 0))
        = (∫ t in (-π)..π, poissonKer r t * f t) - ∫ t in (-π)..π, poissonKer r t * f 0 := by
      rw [← intervalIntegral.integral_sub hI1 hI2]
      exact intervalIntegral.integral_congr (fun t _ => by ring)
    rw [hint, mul_sub]; linarith [hf0]
  rw [Real.dist_eq, hdiff, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (2 * π)⁻¹)]
  have hbnd := poissonKer_split_bound hf hr0 hrmem hδ0 hδπ hε hM0 hsmall hM
  have hcpos : (∫ t in (-π)..(-δ), poissonKer r t) + ∫ t in δ..π, poissonKer r t < π * ε / (M + 1) := by
    have hd := hη (Set.mem_Iio.mpr hrmem) (lt_of_lt_of_le hrdist (min_le_left _ _))
    rw [Real.dist_eq, sub_zero] at hd
    exact lt_of_le_of_lt (le_abs_self _) hd
  have hcnn : 0 ≤ (∫ t in (-π)..(-δ), poissonKer r t) + ∫ t in δ..π, poissonKer r t := by
    have h1 : (0:ℝ) ≤ ∫ t in (-π)..(-δ), poissonKer r t :=
      intervalIntegral.integral_nonneg (by linarith) (fun t _ => poissonKer_nonneg hr0 hrmem t)
    have h2 : (0:ℝ) ≤ ∫ t in δ..π, poissonKer r t :=
      intervalIntegral.integral_nonneg hδπ (fun t _ => poissonKer_nonneg hr0 hrmem t)
    linarith
  calc (2 * π)⁻¹ * |∫ t in (-π)..π, poissonKer r t * (f t - f 0)|
      ≤ (2 * π)⁻¹ * (ε / 2 * (2 * π) + M *
          ((∫ t in (-π)..(-δ), poissonKer r t) + ∫ t in δ..π, poissonKer r t)) :=
        mul_le_mul_of_nonneg_left hbnd (by positivity)
    _ < ε := by
        have hMc : M * ((∫ t in (-π)..(-δ), poissonKer r t) + ∫ t in δ..π, poissonKer r t) < π * ε := by
          calc M * _ ≤ M * (π * ε / (M + 1)) := mul_le_mul_of_nonneg_left hcpos.le hM0
            _ < π * ε := by
                rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
                nlinarith [hπ, hε]
        have he1 : (2 * π)⁻¹ * (ε / 2 * (2 * π)) = ε / 2 := by field_simp
        have he2 : (2 * π)⁻¹ * (π * ε) = ε / 2 := by field_simp
        rw [mul_add, he1]
        have : (2 * π)⁻¹ * (M * _) < (2 * π)⁻¹ * (π * ε) :=
          mul_lt_mul_of_pos_left hMc (by positivity)
        rw [he2] at this
        linarith

/-- The Poisson kernel is antitone (decreasing) in `t` on `[0, π]` for `0 ≤ r < 1`.  This is the
monotonicity that lets the Lebesgue-point average estimate control the boundary limit. -/
theorem poissonKer_antitoneOn {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    AntitoneOn (poissonKer r) (Set.Icc 0 π) := by
  have habs : |r| < 1 := by rw [abs_of_nonneg hr0]; exact hr1
  intro a ha b hb hab
  rw [Set.mem_Icc] at ha hb
  rw [poissonKer, poissonKer]
  have hda : 0 < 1 - 2 * r * Real.cos a + r ^ 2 := poissonKer_denom_pos habs a
  have hdb : 0 < 1 - 2 * r * Real.cos b + r ^ 2 := poissonKer_denom_pos habs b
  have hcos : Real.cos b ≤ Real.cos a := by
    rcases eq_or_lt_of_le hab with h | h
    · rw [h]
    · exact le_of_lt (Real.cos_lt_cos_of_nonneg_of_le_pi ha.1 hb.2 h)
  have hden : 1 - 2 * r * Real.cos a + r ^ 2 ≤ 1 - 2 * r * Real.cos b + r ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hcos (by linarith : (0:ℝ) ≤ 2 * r)]
  have hnum : 0 ≤ 1 - r ^ 2 := by nlinarith
  rw [div_le_div_iff₀ hdb hda]
  nlinarith [mul_le_mul_of_nonneg_left hden hnum]

/-- The `t`-derivative of the Poisson kernel: `P_r'(t) = -2r(1-r²)sin t / (1-2r cos t+r²)²`.  It is
`≤ 0` on `[0,π]` (whence the monotonicity), and drives the decreasing-kernel integral estimate used
in the Lebesgue-point boundary limit. -/
theorem hasDerivAt_poissonKer {r : ℝ} (hr : |r| < 1) (t : ℝ) :
    HasDerivAt (poissonKer r)
      (-(2 * r * (1 - r ^ 2) * Real.sin t) / (1 - 2 * r * Real.cos t + r ^ 2) ^ 2) t := by
  have hden0 : (1 - 2 * r * Real.cos t + r ^ 2) ≠ 0 := (poissonKer_denom_pos hr t).ne'
  have hden : HasDerivAt (fun t => 1 - 2 * r * Real.cos t + r ^ 2) (2 * r * Real.sin t) t := by
    have hc : HasDerivAt Real.cos (-Real.sin t) t := Real.hasDerivAt_cos t
    have hd0 := ((hasDerivAt_const t (1:ℝ)).sub (hc.const_mul (2 * r))).add_const (r ^ 2)
    convert hd0 using 1; ring
  have hq := (hasDerivAt_const t (1 - r ^ 2)).div hden hden0
  show HasDerivAt (fun t => (1 - r ^ 2) / (1 - 2 * r * Real.cos t + r ^ 2)) _ t
  convert hq using 1
  field_simp
  ring

end GaloisForLFunctions.HTGeometry
