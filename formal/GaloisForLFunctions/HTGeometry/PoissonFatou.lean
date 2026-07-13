import Mathlib.Analysis.Complex.Poisson
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

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

/-- Triangle Fubini: for `φ` continuous and `h` interval-integrable on `[0,b]`,
`∫₀ᵇ (∫ₜᵇ φ) · h(t) dt = ∫₀ᵇ φ(s) · (∫₀ˢ h) ds`. The swap of the order of integration
over the triangle `{(t,s) : t ≤ s}`. -/
theorem triangle_fubini {φ h : ℝ → ℝ} {b : ℝ} (hb : 0 ≤ b)
    (hφ : Continuous φ) (hh : IntervalIntegrable h volume 0 b) :
    (∫ t in (0:ℝ)..b, (∫ s in t..b, φ s) * h t)
      = ∫ s in (0:ℝ)..b, φ s * (∫ t in (0:ℝ)..s, h t) := by
  set μ : Measure ℝ := volume.restrict (Set.Ioc (0:ℝ) b) with hμdef
  have hφμ : Integrable φ μ := hφ.integrableOn_Ioc
  have hhμ : Integrable h μ := hh.1
  have hprod : Integrable (fun p : ℝ × ℝ => h p.1 * φ p.2) (μ.prod μ) := hhμ.mul_prod hφμ
  set F : ℝ → ℝ → ℝ := fun t s => if t ≤ s then h t * φ s else 0 with hFdef
  have hFae : (Function.uncurry F)
      = fun p : ℝ × ℝ => (({p : ℝ × ℝ | p.1 ≤ p.2}).indicator (fun p => h p.1 * φ p.2)) p := by
    funext p; rw [Set.indicator_apply]; simp [hFdef, Function.uncurry, Set.mem_setOf_eq]
  have hFint : Integrable (Function.uncurry F) (μ.prod μ) := by
    rw [hFae]
    refine hprod.indicator ?_
    exact measurableSet_le measurable_fst measurable_snd
  have hswap := integral_integral_swap (f := F) hFint
  have hLeq : (∫ t in (0:ℝ)..b, (∫ s in t..b, φ s) * h t) = ∫ t, (∫ s, F t s ∂μ) ∂μ := by
    rw [intervalIntegral.integral_of_le hb]
    refine setIntegral_congr_ae measurableSet_Ioc (Filter.Eventually.of_forall ?_)
    intro t ht
    rw [Set.mem_Ioc] at ht
    have hind : (fun s => F t s)
        = (Set.Ici t).indicator (fun s => h t * φ s) := by
      funext s; rw [Set.indicator_apply]; by_cases hs : t ≤ s <;> simp [hFdef, hs, Set.mem_Ici]
    have hset : Set.Ioc (0:ℝ) b ∩ Set.Ici t = Set.Icc t b := by
      ext s; simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ici, Set.mem_Icc]
      constructor
      · rintro ⟨⟨_, hsb⟩, hts⟩; exact ⟨hts, hsb⟩
      · rintro ⟨hts, hsb⟩; exact ⟨⟨lt_of_lt_of_le ht.1 hts, hsb⟩, hts⟩
    symm
    calc (∫ s, F t s ∂μ)
        = ∫ s in Set.Ioc (0:ℝ) b, (Set.Ici t).indicator (fun s => h t * φ s) s ∂volume := by
          rw [hμdef]; rw [hind]
      _ = ∫ s in Set.Ioc (0:ℝ) b ∩ Set.Ici t, h t * φ s ∂volume :=
          setIntegral_indicator measurableSet_Ici
      _ = ∫ s in Set.Icc t b, h t * φ s ∂volume := by rw [hset]
      _ = ∫ s in Set.Ioc t b, h t * φ s ∂volume := integral_Icc_eq_integral_Ioc
      _ = h t * ∫ s in Set.Ioc t b, φ s ∂volume := integral_const_mul _ _
      _ = h t * ∫ s in t..b, φ s := by rw [intervalIntegral.integral_of_le ht.2]
      _ = (∫ s in t..b, φ s) * h t := mul_comm _ _
  have hReq : (∫ s in (0:ℝ)..b, φ s * (∫ t in (0:ℝ)..s, h t)) = ∫ s, (∫ t, F t s ∂μ) ∂μ := by
    rw [intervalIntegral.integral_of_le hb]
    refine setIntegral_congr_ae measurableSet_Ioc (Filter.Eventually.of_forall ?_)
    intro s hs
    rw [Set.mem_Ioc] at hs
    have hind : (fun t => F t s)
        = (Set.Iic s).indicator (fun t => h t * φ s) := by
      funext t; rw [Set.indicator_apply]; by_cases ht : t ≤ s <;> simp [hFdef, ht, Set.mem_Iic]
    have hset : Set.Ioc (0:ℝ) b ∩ Set.Iic s = Set.Ioc (0:ℝ) s := by
      ext t; simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Iic]
      constructor
      · rintro ⟨⟨h0, _⟩, hts⟩; exact ⟨h0, hts⟩
      · rintro ⟨h0, hts⟩; exact ⟨⟨h0, le_trans hts hs.2⟩, hts⟩
    symm
    calc (∫ t, F t s ∂μ)
        = ∫ t in Set.Ioc (0:ℝ) b, (Set.Iic s).indicator (fun t => h t * φ s) t ∂volume := by
          rw [hμdef]; rw [hind]
      _ = ∫ t in Set.Ioc (0:ℝ) b ∩ Set.Iic s, h t * φ s ∂volume :=
          setIntegral_indicator measurableSet_Iic
      _ = ∫ t in Set.Ioc (0:ℝ) s, h t * φ s ∂volume := by rw [hset]
      _ = (∫ t in Set.Ioc (0:ℝ) s, h t ∂volume) * φ s := integral_mul_const _ _
      _ = (∫ t in (0:ℝ)..s, h t) * φ s := by rw [intervalIntegral.integral_of_le hs.1.le]
      _ = φ s * (∫ t in (0:ℝ)..s, h t) := mul_comm _ _
  rw [hLeq, hReq]; exact hswap

/-- Decreasing-kernel bound: if `k` is `C¹` and antitone with `k(b) ≥ 0`, `h ≥ 0` with
primitive `∫₀ˢ h ≤ A·s`, then `∫₀ᵇ k·h ≤ A·∫₀ᵇ k`. The kernel form of the maximal-function
domination for an approximate identity with decreasing majorant. -/
theorem decreasing_kernel_bound {k k' h : ℝ → ℝ} {b A : ℝ} (hb : 0 ≤ b)
    (hkd : ∀ t, HasDerivAt k (k' t) t)
    (hk'c : Continuous k')
    (hk'np : ∀ t ∈ Set.Icc 0 b, k' t ≤ 0)
    (hkbnn : 0 ≤ k b)
    (hh : IntervalIntegrable h volume 0 b)
    (hHle : ∀ s ∈ Set.Icc 0 b, (∫ t in (0:ℝ)..s, h t) ≤ A * s) :
    (∫ t in (0:ℝ)..b, k t * h t) ≤ A * ∫ t in (0:ℝ)..b, k t := by
  have hkc : Continuous k := continuous_iff_continuousAt.mpr (fun t => (hkd t).continuousAt)
  set H : ℝ → ℝ := fun s => ∫ t in (0:ℝ)..s, h t with hHdef
  have huIcc : Set.uIcc (0:ℝ) b = Set.Icc 0 b := Set.uIcc_of_le hb
  have hHcont : ContinuousOn H (Set.Icc 0 b) := by
    have hInt : IntegrableOn h (Set.uIcc 0 b) volume := by
      rw [huIcc]; exact (hh.1).congr_set_ae Ioc_ae_eq_Icc.symm
    have hc := continuousOn_primitive_interval (f := h) (a := 0) (b := b) (μ := volume) hInt
    rwa [huIcc] at hc
  have hfub : (∫ t in (0:ℝ)..b, (∫ s in t..b, k' s) * h t) = ∫ s in (0:ℝ)..b, k' s * H s :=
    triangle_fubini hb hk'c hh
  have hpt : ∀ t, k t * h t = k b * h t - (∫ s in t..b, k' s) * h t := by
    intro t
    have he : (∫ s in t..b, k' s) = k b - k t :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hkd x) (hk'c.intervalIntegrable t b)
    rw [he]; ring
  have hI1 : IntervalIntegrable (fun t => k b * h t) volume 0 b := hh.const_mul (k b)
  have hI2 : IntervalIntegrable (fun t => (∫ s in t..b, k' s) * h t) volume 0 b := by
    apply hh.continuousOn_mul
    apply ContinuousOn.congr ((continuous_const.sub hkc).continuousOn)
    intro t _
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hkd x) (hk'c.intervalIntegrable t b)
  have hsplit : (∫ t in (0:ℝ)..b, k t * h t)
      = (∫ t in (0:ℝ)..b, k b * h t) - ∫ t in (0:ℝ)..b, (∫ s in t..b, k' s) * h t := by
    rw [← intervalIntegral.integral_sub hI1 hI2]
    exact intervalIntegral.integral_congr (fun t _ => hpt t)
  have hconst : (∫ t in (0:ℝ)..b, k b * h t) = k b * H b := intervalIntegral.integral_const_mul _ _
  have hkey : (∫ t in (0:ℝ)..b, k t * h t) = k b * H b - ∫ s in (0:ℝ)..b, k' s * H s := by
    rw [hsplit, hconst, hfub]
  have hIBP : (∫ s in (0:ℝ)..b, k' s * s) = k b * b - ∫ s in (0:ℝ)..b, k s := by
    have hmain := intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (u := k) (v := fun s => s) (u' := k') (v' := fun _ => (1:ℝ))
      (fun x _ => hkd x) (fun x _ => hasDerivAt_id x) (hk'c.intervalIntegrable 0 b)
      (_root_.intervalIntegrable_const)
    simp only [mul_one, mul_zero, sub_zero] at hmain
    linarith [hmain]
  have hIk'H : IntervalIntegrable (fun s => k' s * H s) volume 0 b := by
    apply ContinuousOn.intervalIntegrable
    rw [huIcc]; exact hk'c.continuousOn.mul hHcont
  have hIk's : IntervalIntegrable (fun s => k' s * (A * s)) volume 0 b :=
    (hk'c.mul (continuous_const.mul continuous_id)).intervalIntegrable 0 b
  have hmono : (∫ s in (0:ℝ)..b, k' s * (A * s)) ≤ ∫ s in (0:ℝ)..b, k' s * H s :=
    intervalIntegral.integral_mono_on hb hIk's hIk'H
      (fun s hs => mul_le_mul_of_nonpos_left (hHle s hs) (hk'np s hs))
  have hApull : (∫ s in (0:ℝ)..b, k' s * (A * s)) = A * ∫ s in (0:ℝ)..b, k' s * s := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr (fun s _ => by ring)
  have hHb : H b ≤ A * b := hHle b ⟨hb, le_refl b⟩
  have hlow : A * (k b * b - ∫ s in (0:ℝ)..b, k s) ≤ ∫ s in (0:ℝ)..b, k' s * H s := by
    calc A * (k b * b - ∫ s in (0:ℝ)..b, k s)
        = A * ∫ s in (0:ℝ)..b, k' s * s := by rw [hIBP]
      _ = ∫ s in (0:ℝ)..b, k' s * (A * s) := hApull.symm
      _ ≤ ∫ s in (0:ℝ)..b, k' s * H s := hmono
  have hup : k b * H b ≤ A * (k b * b) := by
    calc k b * H b ≤ k b * (A * b) := mul_le_mul_of_nonneg_left hHb hkbnn
      _ = A * (k b * b) := by ring
  rw [hkey]
  calc k b * H b - ∫ s in (0:ℝ)..b, k' s * H s
      ≤ A * (k b * b) - A * (k b * b - ∫ s in (0:ℝ)..b, k s) := sub_le_sub hup hlow
    _ = A * ∫ s in (0:ℝ)..b, k s := by ring

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
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hδ0 : 0 < δ) (hδπ : δ ≤ π) (hε : 0 < ε) (_hM0 : 0 ≤ M)
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

/-- The `t`-derivative kernel of `poissonKer`. -/
noncomputable def poissonKerDeriv (r t : ℝ) : ℝ :=
  -(2 * r * (1 - r ^ 2) * Real.sin t) / (1 - 2 * r * Real.cos t + r ^ 2) ^ 2

theorem hasDerivAt_poissonKer' {r : ℝ} (hr : |r| < 1) (t : ℝ) :
    HasDerivAt (poissonKer r) (poissonKerDeriv r t) t := hasDerivAt_poissonKer hr t

/-- The derivative kernel is continuous for `|r| < 1`. -/
theorem poissonKerDeriv_continuous {r : ℝ} (hr : |r| < 1) : Continuous (poissonKerDeriv r) := by
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro t; exact pow_ne_zero 2 (poissonKer_denom_pos hr t).ne'

/-- The Poisson kernel is decreasing on `[0, π]`: its derivative is `≤ 0` there. -/
theorem poissonKerDeriv_nonpos {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) {t : ℝ}
    (h0 : 0 ≤ t) (h1 : t ≤ π) : poissonKerDeriv r t ≤ 0 := by
  have habs : |r| < 1 := by rw [abs_of_nonneg hr0]; exact hr1
  rw [poissonKerDeriv]
  apply div_nonpos_of_nonpos_of_nonneg
  · have hsin : 0 ≤ Real.sin t := Real.sin_nonneg_of_nonneg_of_le_pi h0 h1
    have hr2 : 0 ≤ 1 - r ^ 2 := by nlinarith [abs_nonneg r, sq_abs r]
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 2 * r) hr2) hsin]
  · positivity

/-- The Poisson kernel at a fixed positive angle tends to `0` as `r → 1⁻`. -/
theorem tendsto_poissonKer_point {δ : ℝ} (hδ0 : 0 < δ) (hδπ : δ ≤ π) :
    Tendsto (fun r => poissonKer r δ) (𝓝[<] 1) (𝓝 0) := by
  have hpos : (0:ℝ) < 1 - 2 * 1 * Real.cos δ + 1 ^ 2 := by
    have h := one_sub_cos_ge (le_of_lt hδ0) hδπ
    have h2 : (0:ℝ) < 2 * δ ^ 2 / π ^ 2 := by positivity
    nlinarith [h, h2]
  have hnum : Tendsto (fun r : ℝ => 1 - r ^ 2) (𝓝[<] 1) (𝓝 0) := by
    have hc : Tendsto (fun r : ℝ => 1 - r ^ 2) (𝓝 1) (𝓝 (1 - 1 ^ 2)) :=
      (by fun_prop : Continuous fun r : ℝ => 1 - r ^ 2).tendsto 1
    simp only [one_pow, sub_self] at hc
    exact hc.mono_left nhdsWithin_le_nhds
  have hden : Tendsto (fun r : ℝ => 1 - 2 * r * Real.cos δ + r ^ 2) (𝓝[<] 1)
      (𝓝 (1 - 2 * 1 * Real.cos δ + 1 ^ 2)) :=
    ((by fun_prop : Continuous fun r : ℝ => 1 - 2 * r * Real.cos δ + r ^ 2).tendsto 1).mono_left
      nhdsWithin_le_nhds
  have hdiv := hnum.div hden hpos.ne'
  simp only [zero_div] at hdiv
  exact hdiv

/-- Half-interval normalization: `∫₀^π P_r = π`. -/
theorem poissonKer_integral_half {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∫ t in (0:ℝ)..π, poissonKer r t = π := by
  have habs : |r| < 1 := by rw [abs_of_nonneg hr0]; exact hr1
  have hcont : Continuous (poissonKer r) := poissonKer_continuous habs
  have hhalf : (∫ t in (0:ℝ)..π, poissonKer r t) = ∫ t in (-π)..(0:ℝ), poissonKer r t := by
    have h := poissonKer_integral_neg r 0; rwa [neg_zero] at h
  have hsplit : (∫ t in (-π)..π, poissonKer r t)
      = (∫ t in (-π)..(0:ℝ), poissonKer r t) + ∫ t in (0:ℝ)..π, poissonKer r t :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)).symm
  have hsymm := poissonKer_integral_symm hr0 hr1
  linarith [hhalf, hsplit, hsymm]

/-- Evenness fold: `∫_{-π}^π P_r·w = ∫₀^π P_r·(w(t) + w(-t))`. -/
theorem poissonKer_fold {r : ℝ} (hr : |r| < 1) {w : ℝ → ℝ}
    (hw : IntervalIntegrable w volume (-π) π) :
    (∫ t in (-π)..π, poissonKer r t * w t)
      = ∫ t in (0:ℝ)..π, poissonKer r t * (w t + w (-t)) := by
  have hcont : Continuous (poissonKer r) := poissonKer_continuous hr
  have hπ : (0:ℝ) ≤ π := le_of_lt Real.pi_pos
  have hmemn : (-π:ℝ) ∈ Set.uIcc (-π) π := Set.left_mem_uIcc
  have hmemp : (π:ℝ) ∈ Set.uIcc (-π) π := Set.right_mem_uIcc
  have hmem0 : (0:ℝ) ∈ Set.uIcc (-π) π := by
    rw [Set.uIcc_of_le (by linarith)]; exact ⟨by linarith, by linarith⟩
  have hwL : IntervalIntegrable w volume (-π) 0 := hw.mono_set (Set.uIcc_subset_uIcc hmemn hmem0)
  have hwR : IntervalIntegrable w volume 0 π := hw.mono_set (Set.uIcc_subset_uIcc hmem0 hmemp)
  have hwNeg : IntervalIntegrable (fun t => w (-t)) volume 0 π := by
    have h := (IntervalIntegrable.iff_comp_neg).1 hwL; simpa using h.symm
  have hpw : IntervalIntegrable (fun t => poissonKer r t * w t) volume (-π) 0 :=
    hwL.continuousOn_mul hcont.continuousOn
  have hpwR : IntervalIntegrable (fun t => poissonKer r t * w t) volume 0 π :=
    hwR.continuousOn_mul hcont.continuousOn
  have hpwNeg : IntervalIntegrable (fun t => poissonKer r t * w (-t)) volume 0 π :=
    hwNeg.continuousOn_mul hcont.continuousOn
  have hsplit : (∫ t in (-π)..π, poissonKer r t * w t)
      = (∫ t in (-π)..(0:ℝ), poissonKer r t * w t) + ∫ t in (0:ℝ)..π, poissonKer r t * w t :=
    (intervalIntegral.integral_add_adjacent_intervals hpw hpwR).symm
  have hneg : (∫ t in (-π)..(0:ℝ), poissonKer r t * w t)
      = ∫ t in (0:ℝ)..π, poissonKer r t * w (-t) := by
    have h := intervalIntegral.integral_comp_neg (a := 0) (b := π)
      (fun t => poissonKer r t * w t)
    rw [neg_zero] at h
    rw [← h]
    exact intervalIntegral.integral_congr (fun t _ => by rw [poissonKer_even])
  rw [hsplit, hneg, ← intervalIntegral.integral_add hpwNeg hpwR]
  exact intervalIntegral.integral_congr (fun t _ => by ring)

/-- Per-`r` bound for the Poisson convolution error, split into a near part controlled by the
local `L¹` mean `A` and a far part controlled by `P_r(δ) → 0`. -/
theorem poissonConv_pointwise_bound {φ : ℝ → ℝ}
    (hφ : IntervalIntegrable φ volume (-π) π)
    {r δ A : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (hδ0 : 0 < δ) (hδπ : δ ≤ π) (hA0 : 0 ≤ A)
    (hHle : ∀ s ∈ Set.Icc 0 δ, (∫ t in (0:ℝ)..s, |φ t - φ 0| + |φ (-t) - φ 0|) ≤ A * s) :
    |(2 * π)⁻¹ * (∫ t in (-π)..π, poissonKer r t * φ t) - φ 0|
      ≤ (2 * π)⁻¹ * (A * π + poissonKer r δ *
          (∫ t in (0:ℝ)..π, |φ t - φ 0| + |φ (-t) - φ 0|)) := by
  have habs : |r| < 1 := by rw [abs_of_nonneg hr0]; exact hr1
  have hcont : Continuous (poissonKer r) := poissonKer_continuous habs
  have hnn : ∀ t, 0 ≤ poissonKer r t := fun t => poissonKer_nonneg hr0 hr1 t
  have hπ : (0:ℝ) < π := Real.pi_pos
  have h2π : (0:ℝ) < 2 * π := by linarith
  have hc0 : IntervalIntegrable (fun _ : ℝ => φ 0) volume (-π) π := _root_.intervalIntegrable_const
  set w : ℝ → ℝ := fun t => |φ t - φ 0| with hwdef
  set h : ℝ → ℝ := fun t => w t + w (-t) with hhdef
  have hwnn : ∀ t, 0 ≤ w t := fun t => abs_nonneg _
  have hhnn : ∀ t, 0 ≤ h t := fun t => by rw [hhdef]; exact add_nonneg (hwnn t) (hwnn _)
  -- integrability of w and h
  have hwI : IntervalIntegrable w volume (-π) π := (hφ.sub hc0).abs
  have hφneg : IntervalIntegrable (fun t => φ (-t)) volume (-π) π := by
    have h := (IntervalIntegrable.iff_comp_neg (f := φ) (a := -π) (b := π)).1 hφ
    simpa using h.symm
  have hwnegI : IntervalIntegrable (fun t => w (-t)) volume (-π) π := by
    have : IntervalIntegrable (fun t => |φ (-t) - φ 0|) volume (-π) π := (hφneg.sub hc0).abs
    simpa [hwdef] using this
  have hhI : IntervalIntegrable h volume (-π) π := hwI.add hwnegI
  have hmem0π : (0:ℝ) ∈ Set.uIcc (-π) π := by rw [Set.uIcc_of_le (by linarith)]; exact ⟨by linarith, by linarith⟩
  have hhI0π : IntervalIntegrable h volume 0 π :=
    hhI.mono_set (Set.uIcc_subset_uIcc hmem0π Set.right_mem_uIcc)
  have hmem0δ : (0:ℝ) ∈ Set.uIcc 0 π := by rw [Set.uIcc_of_le (by linarith)]; exact ⟨le_refl 0, by linarith⟩
  have hmemδπ : δ ∈ Set.uIcc 0 π := by rw [Set.uIcc_of_le (by linarith)]; exact ⟨hδ0.le, hδπ⟩
  have hhI0δ : IntervalIntegrable h volume 0 δ :=
    hhI0π.mono_set (Set.uIcc_subset_uIcc hmem0δ hmemδπ)
  have hhIδπ : IntervalIntegrable h volume δ π :=
    hhI0π.mono_set (Set.uIcc_subset_uIcc hmemδπ Set.right_mem_uIcc)
  -- normalization: (2π)⁻¹∫P_r·φ - φ0 = (2π)⁻¹∫P_r(φ-φ0)
  have hPφ : IntervalIntegrable (fun t => poissonKer r t * φ t) volume (-π) π :=
    hφ.continuousOn_mul hcont.continuousOn
  have hPφ0 : IntervalIntegrable (fun t => poissonKer r t * φ 0) volume (-π) π :=
    (hcont.mul continuous_const).intervalIntegrable _ _
  have hPsub : IntervalIntegrable (fun t => poissonKer r t * (φ t - φ 0)) volume (-π) π :=
    (hφ.sub hc0).continuousOn_mul hcont.continuousOn
  have hnorm : (∫ t in (-π)..π, poissonKer r t * φ t)
      = (∫ t in (-π)..π, poissonKer r t * (φ t - φ 0)) + φ 0 * (2 * π) := by
    have hsplit : (∫ t in (-π)..π, poissonKer r t * φ t)
        = (∫ t in (-π)..π, poissonKer r t * (φ t - φ 0)) + ∫ t in (-π)..π, poissonKer r t * φ 0 := by
      rw [← intervalIntegral.integral_add hPsub hPφ0]
      exact intervalIntegral.integral_congr (fun t _ => by ring)
    rw [hsplit]
    congr 1
    rw [intervalIntegral.integral_mul_const, poissonKer_integral_symm hr0 hr1]; ring
  have hAvg : (2 * π)⁻¹ * (∫ t in (-π)..π, poissonKer r t * φ t) - φ 0
      = (2 * π)⁻¹ * ∫ t in (-π)..π, poissonKer r t * (φ t - φ 0) := by
    rw [hnorm]; field_simp; ring
  -- abs + fold: |(2π)⁻¹∫P_r(φ-φ0)| ≤ (2π)⁻¹∫₀^π P_r·h
  have hfoldabs : |∫ t in (-π)..π, poissonKer r t * (φ t - φ 0)| ≤ ∫ t in (0:ℝ)..π, poissonKer r t * h t := by
    have hstep1 : |∫ t in (-π)..π, poissonKer r t * (φ t - φ 0)|
        ≤ ∫ t in (-π)..π, poissonKer r t * w t := by
      refine (intervalIntegral.abs_integral_le_integral_abs (by linarith)).trans ?_
      apply intervalIntegral.integral_mono_on (by linarith) hPsub.abs
        (hwI.continuousOn_mul hcont.continuousOn)
      intro t _
      rw [abs_mul, abs_of_nonneg (hnn t)]
    have hfold : (∫ t in (-π)..π, poissonKer r t * w t) = ∫ t in (0:ℝ)..π, poissonKer r t * h t :=
      poissonKer_fold habs hwI
    rw [hfold] at hstep1; exact hstep1
  -- near part: decreasing kernel bound
  have hnear : (∫ t in (0:ℝ)..δ, poissonKer r t * h t) ≤ A * π := by
    have hdkb := decreasing_kernel_bound (k := poissonKer r) (k' := poissonKerDeriv r) (h := h)
      (b := δ) (A := A) hδ0.le (fun t => hasDerivAt_poissonKer' habs t)
      (poissonKerDeriv_continuous habs)
      (fun t ht => poissonKerDeriv_nonpos hr0 hr1 ht.1 (ht.2.trans hδπ))
      (poissonKer_nonneg hr0 hr1 δ) hhI0δ hHle
    refine hdkb.trans ?_
    have hle : (∫ t in (0:ℝ)..δ, poissonKer r t) ≤ π := by
      rw [← poissonKer_integral_half hr0 hr1]
      have hadd : (∫ t in (0:ℝ)..π, poissonKer r t)
          = (∫ t in (0:ℝ)..δ, poissonKer r t) + ∫ t in δ..π, poissonKer r t :=
        (intervalIntegral.integral_add_adjacent_intervals
          (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)).symm
      have hδπnn : 0 ≤ ∫ t in δ..π, poissonKer r t :=
        intervalIntegral.integral_nonneg hδπ (fun t _ => hnn t)
      linarith
    exact mul_le_mul_of_nonneg_left hle hA0
  -- far part
  have hfar : (∫ t in δ..π, poissonKer r t * h t) ≤ poissonKer r δ * ∫ t in (0:ℝ)..π, h t := by
    have hmono : (∫ t in δ..π, poissonKer r t * h t) ≤ ∫ t in δ..π, poissonKer r δ * h t := by
      apply intervalIntegral.integral_mono_on hδπ
        (hhIδπ.continuousOn_mul hcont.continuousOn)
        (hhIδπ.const_mul (poissonKer r δ))
      intro t ht
      apply mul_le_mul_of_nonneg_right _ (hhnn t)
      exact poissonKer_antitoneOn hr0 hr1 (Set.mem_Icc.mpr ⟨hδ0.le, hδπ⟩)
        (Set.mem_Icc.mpr ⟨by linarith [ht.1], ht.2⟩) ht.1
    rw [intervalIntegral.integral_const_mul] at hmono
    refine hmono.trans ?_
    apply mul_le_mul_of_nonneg_left _ (hnn δ)
    have hadd : (∫ t in (0:ℝ)..π, h t) = (∫ t in (0:ℝ)..δ, h t) + ∫ t in δ..π, h t :=
      (intervalIntegral.integral_add_adjacent_intervals hhI0δ hhIδπ).symm
    have h0δ : 0 ≤ ∫ t in (0:ℝ)..δ, h t := intervalIntegral.integral_nonneg hδ0.le (fun t _ => hhnn t)
    linarith
  -- combine near + far into a bound on ∫₀^π P_r·h
  have hπsum : (∫ t in (0:ℝ)..π, poissonKer r t * h t)
      ≤ A * π + poissonKer r δ * ∫ t in (0:ℝ)..π, h t := by
    have hPh0δ : IntervalIntegrable (fun t => poissonKer r t * h t) volume 0 δ :=
      hhI0δ.continuousOn_mul hcont.continuousOn
    have hPhδπ : IntervalIntegrable (fun t => poissonKer r t * h t) volume δ π :=
      hhIδπ.continuousOn_mul hcont.continuousOn
    have hadd : (∫ t in (0:ℝ)..π, poissonKer r t * h t)
        = (∫ t in (0:ℝ)..δ, poissonKer r t * h t) + ∫ t in δ..π, poissonKer r t * h t :=
      (intervalIntegral.integral_add_adjacent_intervals hPh0δ hPhδπ).symm
    rw [hadd]; linarith [hnear, hfar]
  -- ∫₀^π h equals the explicit integrand in the statement
  have hheq : (∫ t in (0:ℝ)..π, h t) = ∫ t in (0:ℝ)..π, |φ t - φ 0| + |φ (-t) - φ 0| :=
    intervalIntegral.integral_congr (fun t _ => by simp only [hhdef, hwdef])
  -- assemble
  calc |(2 * π)⁻¹ * (∫ t in (-π)..π, poissonKer r t * φ t) - φ 0|
      = |(2 * π)⁻¹ * ∫ t in (-π)..π, poissonKer r t * (φ t - φ 0)| := by rw [hAvg]
    _ = (2 * π)⁻¹ * |∫ t in (-π)..π, poissonKer r t * (φ t - φ 0)| := by
        rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (2 * π)⁻¹)]
    _ ≤ (2 * π)⁻¹ * ∫ t in (0:ℝ)..π, poissonKer r t * h t :=
        mul_le_mul_of_nonneg_left hfoldabs (by positivity)
    _ ≤ (2 * π)⁻¹ * (A * π + poissonKer r δ * ∫ t in (0:ℝ)..π, h t) :=
        mul_le_mul_of_nonneg_left hπsum (by positivity)
    _ = (2 * π)⁻¹ * (A * π + poissonKer r δ *
          ∫ t in (0:ℝ)..π, |φ t - φ 0| + |φ (-t) - φ 0|) := by rw [hheq]

/-- **Poisson convergence at a symmetric Lebesgue point.**  If the symmetrized local mean
`s⁻¹∫₀ˢ(|φ(t)-φ(0)| + |φ(-t)-φ(0)|) → 0` as `s → 0⁺`, then the Poisson average converges to
`φ(0)` as `r → 1⁻`. -/
theorem tendsto_poissonConv_of_symmLebesgue {φ : ℝ → ℝ}
    (hφ : IntervalIntegrable φ volume (-π) π)
    (hleb : Tendsto (fun s => (∫ t in (0:ℝ)..s, |φ t - φ 0| + |φ (-t) - φ 0|) / s)
      (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun r => (2 * π)⁻¹ * ∫ t in (-π)..π, poissonKer r t * φ t) (𝓝[<] 1) (𝓝 (φ 0)) := by
  have hπ : (0:ℝ) < π := Real.pi_pos
  set Ih : ℝ := ∫ t in (0:ℝ)..π, |φ t - φ 0| + |φ (-t) - φ 0| with hIhdef
  have hIhnn : 0 ≤ Ih := by
    rw [hIhdef]
    exact intervalIntegral.integral_nonneg hπ.le (fun t _ => add_nonneg (abs_nonneg _) (abs_nonneg _))
  set c : ℝ := (2 * π)⁻¹ * Ih with hcdef
  have hcnn : 0 ≤ c := by rw [hcdef]; positivity
  rw [← tendsto_sub_nhds_zero_iff]
  refine NormedAddGroup.tendsto_nhds_zero.2 (fun ε hε => ?_)
  -- extract δ from the Lebesgue condition
  obtain ⟨δ', hδ'0, hδ'⟩ := Metric.tendsto_nhdsWithin_nhds.1 hleb ε hε
  set δ : ℝ := min (δ' / 2) π with hδdef
  have hδ0 : 0 < δ := lt_min (by linarith) hπ
  have hδπ : δ ≤ π := min_le_right _ _
  have hδδ' : δ < δ' := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hHle : ∀ s ∈ Set.Icc 0 δ,
      (∫ t in (0:ℝ)..s, |φ t - φ 0| + |φ (-t) - φ 0|) ≤ ε * s := by
    intro s hs
    rcases eq_or_lt_of_le hs.1 with hs0 | hs0
    · simp [← hs0]
    · have hsd : dist s 0 < δ' := by rw [Real.dist_eq, sub_zero, abs_of_pos hs0]; linarith [hs.2]
      have hlt := hδ' (Set.mem_Ioi.mpr hs0) hsd
      rw [Real.dist_eq, sub_zero] at hlt
      have hΨnn : 0 ≤ ∫ t in (0:ℝ)..s, |φ t - φ 0| + |φ (-t) - φ 0| :=
        intervalIntegral.integral_nonneg hs.1 (fun t _ => add_nonneg (abs_nonneg _) (abs_nonneg _))
      rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ (∫ t in (0:ℝ)..s, |φ t - φ 0| + |φ (-t) - φ 0|) / s)]
        at hlt
      rw [div_lt_iff₀ hs0] at hlt
      linarith [hlt]
  -- eventual conditions on r
  have h0r : ∀ᶠ r in 𝓝[<] (1:ℝ), (0:ℝ) ≤ r :=
    ((isOpen_Ioi.eventually_mem (by norm_num : (0:ℝ) < 1)).filter_mono nhdsWithin_le_nhds).mono
      (fun r hr => hr.le)
  have h1r : ∀ᶠ r in 𝓝[<] (1:ℝ), r < 1 :=
    eventually_of_mem self_mem_nhdsWithin (fun r hr => Set.mem_Iio.1 hr)
  have htail : ∀ᶠ r in 𝓝[<] (1:ℝ), c * poissonKer r δ < ε / 2 := by
    have htend : Tendsto (fun r => c * poissonKer r δ) (𝓝[<] 1) (𝓝 0) := by
      have := (tendsto_poissonKer_point hδ0 hδπ).const_mul c
      simpa using this
    exact (htend.eventually (isOpen_Iio.eventually_mem (Set.mem_Iio.2 (half_pos hε)))).mono
      (fun r hr => Set.mem_Iio.1 hr)
  filter_upwards [h0r, h1r, htail] with r hr0 hr1 htl
  have hbound := poissonConv_pointwise_bound hφ hr0 hr1 hδ0 hδπ hε.le hHle
  rw [← hIhdef] at hbound
  rw [Real.norm_eq_abs]
  have harith : (2 * π)⁻¹ * (ε * π + poissonKer r δ * Ih) = ε / 2 + c * poissonKer r δ := by
    rw [hcdef]; field_simp
  calc |(2 * π)⁻¹ * (∫ t in (-π)..π, poissonKer r t * φ t) - φ 0|
      ≤ (2 * π)⁻¹ * (ε * π + poissonKer r δ * Ih) := hbound
    _ = ε / 2 + c * poissonKer r δ := harith
    _ < ε := by linarith [htl]

/-- Symmetric interval fold (no kernel): `∫_{-s}^s H = ∫₀^s (H(t) + H(-t))`. -/
theorem interval_fold {H : ℝ → ℝ} {s : ℝ} (hs : 0 ≤ s)
    (hH : IntervalIntegrable H volume (-s) s) :
    (∫ t in (-s)..s, H t) = ∫ t in (0:ℝ)..s, (H t + H (-t)) := by
  have hmemn : (-s:ℝ) ∈ Set.uIcc (-s) s := Set.left_mem_uIcc
  have hmemp : (s:ℝ) ∈ Set.uIcc (-s) s := Set.right_mem_uIcc
  have hmem0 : (0:ℝ) ∈ Set.uIcc (-s) s := by
    rw [Set.uIcc_of_le (by linarith)]; exact ⟨by linarith, by linarith⟩
  have hHL : IntervalIntegrable H volume (-s) 0 := hH.mono_set (Set.uIcc_subset_uIcc hmemn hmem0)
  have hHR : IntervalIntegrable H volume 0 s := hH.mono_set (Set.uIcc_subset_uIcc hmem0 hmemp)
  have hHNeg : IntervalIntegrable (fun t => H (-t)) volume 0 s := by
    have h := (IntervalIntegrable.iff_comp_neg).1 hHL; simpa using h.symm
  have hsplit : (∫ t in (-s)..s, H t)
      = (∫ t in (-s)..(0:ℝ), H t) + ∫ t in (0:ℝ)..s, H t :=
    (intervalIntegral.integral_add_adjacent_intervals hHL hHR).symm
  have hneg : (∫ t in (-s)..(0:ℝ), H t) = ∫ t in (0:ℝ)..s, H (-t) := by
    have h := intervalIntegral.integral_comp_neg (a := 0) (b := s) H
    rw [neg_zero] at h; rw [← h]
  rw [hsplit, hneg, ← intervalIntegral.integral_add hHNeg hHR]
  exact intervalIntegral.integral_congr (fun t _ => by ring)

/-- **A.e. Fatou for the Poisson integral.**  For `g` locally integrable, the Poisson integral
`(2π)⁻¹∫_{-π}^{π} P_r(t) g(θ+t) dt` converges to `g(θ)` for almost every `θ` as `r → 1⁻`. -/
theorem tendsto_poissonConv_ae {g : ℝ → ℝ} (hg : LocallyIntegrable g volume) :
    ∀ᵐ θ, Tendsto (fun r => (2 * π)⁻¹ * ∫ t in (-π)..π, poissonKer r t * g (θ + t))
      (𝓝[<] 1) (𝓝 (g θ)) := by
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub (volume : Measure ℝ) hg 1]
    with θ hθ
  set φ : ℝ → ℝ := fun t => g (θ + t) with hφdef
  have hφ0 : φ 0 = g θ := by simp [hφdef]
  have hφI : IntervalIntegrable φ volume (-π) π := by
    have hg' : IntervalIntegrable g volume (θ + -π) (θ + π) :=
      (hg.integrableOn_isCompact isCompact_uIcc).intervalIntegrable
    have h := hg'.comp_add_left θ; simpa [hφdef] using h
  -- Lebesgue-average condition at θ
  have havg : Tendsto (fun r : ℝ => ⨍ y in closedBall θ r, ‖g y - g θ‖ ∂volume) (𝓝[>] 0) (𝓝 0) := by
    refine hθ (fun _ => θ) id tendsto_id ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact mem_closedBall_self (by rw [one_mul]; exact (Set.mem_Ioi.1 hr).le)
  -- convert ⨍ to the symmetric local mean
  have hleb : Tendsto (fun s => (∫ t in (0:ℝ)..s, |φ t - φ 0| + |φ (-t) - φ 0|) / s)
      (𝓝[>] 0) (𝓝 0) := by
    have h2 : Tendsto (fun s => (2:ℝ) * ⨍ y in closedBall θ s, ‖g y - g θ‖ ∂volume)
        (𝓝[>] 0) (𝓝 0) := by simpa using havg.const_mul 2
    refine h2.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs0 : (0:ℝ) < s := hs
    have hvol : volume.real (closedBall θ s) = 2 * s := by
      rw [Measure.real, Real.volume_closedBall, ENNReal.toReal_ofReal (by positivity)]
    have hint : (∫ y in closedBall θ s, ‖g y - g θ‖ ∂volume)
        = ∫ t in (0:ℝ)..s, |φ t - φ 0| + |φ (-t) - φ 0| := by
      simp_rw [Real.norm_eq_abs]
      rw [Real.closedBall_eq_Icc, integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by linarith : θ - s ≤ θ + s),
        show (θ - s) = θ + (-s) by ring,
        ← intervalIntegral.integral_comp_add_left (fun y => |g y - g θ|) θ]
      have hHI : IntervalIntegrable (fun t => |g (θ + t) - g θ|) volume (-s) s := by
        have hg' : IntervalIntegrable g volume (θ + -s) (θ + s) :=
          (hg.integrableOn_isCompact isCompact_uIcc).intervalIntegrable
        have h := ((hg'.comp_add_left θ).sub (_root_.intervalIntegrable_const (c := g θ))).abs
        simpa using h
      rw [interval_fold hs0.le hHI]
      refine intervalIntegral.integral_congr (fun t _ => ?_)
      simp only [hφdef, add_zero]
    have hsne : s ≠ 0 := hs0.ne'
    rw [setAverage_eq, hvol, hint, smul_eq_mul]
    field_simp
  have hres := tendsto_poissonConv_of_symmLebesgue hφI hleb
  rw [hφ0] at hres
  exact hres

end GaloisForLFunctions.HTGeometry
