import Mathlib
import Zeta23.Defs

/-!
# A smooth compactly supported bump with an explicit Fourier bound

The uniform probability density `U_w` on `[−w, w]` has Fourier transform
`∫ U_w(x) e^{izx} dx = (e^{izw} − e^{−izw})/(2izw)`, hence `‖Û_w(z)‖ ≤ cosh(w·Im z)/(w‖z‖)`.
Convolution multiplies Fourier transforms, so the `(n+1)`-fold convolution power `U_w^{⋆(n+1)}`
has `‖·‖ ≤ (cosh(w·Im z)/(w‖z‖))^{n+1}`.  Convolving once more with a normalized smooth bump of
radius `r` gives a `C^∞` probability density `φ` supported in `[−(r + (n+1)w), r + (n+1)w]` with

  `‖φ̂(z)‖ ≤ e^{r|Im z|} · (cosh(w·Im z)/(w‖z‖))^{n+1}`.

The Fourier transform used is Zeta23's `paperFT k z = ∫ k(u) e^{izu} du`, so that the results feed
the unconditional Weil explicit formula `Zeta23.WeilEF.EF_lit_zeta` directly.
-/

open MeasureTheory Complex Set
open scoped Convolution

namespace RHTower.WeilDeletion

noncomputable section

/-! ## Integrability of a compactly supported function against a complex exponential -/

theorem norm_exp_I_mul_le {z : ℂ} {x R : ℝ} (hx : |x| ≤ R) :
    ‖Complex.exp (I * z * x)‖ ≤ Real.exp (R * |z.im|) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have hre : (I * z * (x : ℂ)).re = -(z.im * x) := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hre]
  calc -(z.im * x) ≤ |z.im * x| := neg_le_abs _
    _ = |z.im| * |x| := abs_mul _ _
    _ ≤ |z.im| * R := by gcongr
    _ = R * |z.im| := by ring

theorem integrable_ofReal_mul_exp {f : ℝ → ℝ} (hf : Integrable f) (hfc : HasCompactSupport f)
    (z : ℂ) : Integrable (fun x : ℝ => (f x : ℂ) * Complex.exp (I * z * x)) := by
  obtain ⟨R, hR⟩ := hfc.isCompact.isBounded.subset_closedBall 0
  refine Integrable.mono' (hf.norm.const_mul (Real.exp (R * |z.im|))) ?_ ?_
  · exact (Complex.continuous_ofReal.comp_aestronglyMeasurable hf.aestronglyMeasurable).mul
      (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun x => ?_
    rw [norm_mul, Complex.norm_real]
    by_cases hx : x ∈ Function.support f
    · have hxR : |x| ≤ R := by
        have := hR (subset_tsupport f hx)
        rwa [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
      calc ‖f x‖ * ‖Complex.exp (I * z * x)‖ ≤ ‖f x‖ * Real.exp (R * |z.im|) := by
            gcongr; exact norm_exp_I_mul_le hxR
        _ = Real.exp (R * |z.im|) * ‖f x‖ := by ring
    · rw [Function.notMem_support.mp hx]
      simp

/-! ## The Fourier transform of a convolution -/

theorem paperFT_conv {f g : ℝ → ℝ} (hf : Integrable f) (hg : Integrable g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) (z : ℂ) :
    Zeta23.paperFT (fun x => ((f ⋆ g) x : ℂ)) z =
      Zeta23.paperFT (fun x => (f x : ℂ)) z * Zeta23.paperFT (fun x => (g x : ℂ)) z := by
  set F : ℝ → ℂ := fun x => (f x : ℂ) * Complex.exp (I * z * x) with hF
  set G : ℝ → ℂ := fun x => (g x : ℂ) * Complex.exp (I * z * x) with hG
  have hFi : Integrable F := integrable_ofReal_mul_exp hf hfc z
  have hGi : Integrable G := integrable_ofReal_mul_exp hg hgc z
  -- the convolution of the twisted functions is the twisted convolution
  have hconv : ∀ x : ℝ, (F ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] G) x =
      ((f ⋆ g) x : ℂ) * Complex.exp (I * z * x) := by
    intro x
    rw [convolution_def, convolution_def]
    simp only [ContinuousLinearMap.mul_apply', ContinuousLinearMap.lsmul_apply, smul_eq_mul, hF, hG]
    have hpt : ∀ t : ℝ, (f t : ℂ) * Complex.exp (I * z * t) *
        ((g (x - t) : ℂ) * Complex.exp (I * z * ((x - t : ℝ) : ℂ))) =
        Complex.exp (I * z * x) * ((f t * g (x - t) : ℝ) : ℂ) := by
      intro t
      have e : Complex.exp (I * z * t) * Complex.exp (I * z * ((x : ℂ) - t)) =
          Complex.exp (I * z * x) := by
        rw [← Complex.exp_add]
        congr 1
        ring
      push_cast
      linear_combination ((f t : ℂ) * (g (x - t) : ℂ)) * e
    simp_rw [hpt]
    rw [integral_const_mul, integral_complex_ofReal]
    ring
  unfold Zeta23.paperFT
  have hint : ∫ x : ℝ, ((f ⋆ g) x : ℂ) * Complex.exp (I * z * x) =
      ∫ x : ℝ, (F ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] G) x := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    rw [hconv]
  rw [hint, integral_convolution]
  · simp only [ContinuousLinearMap.mul_apply']
    rfl
  · exact hFi
  · exact hGi

/-! ## The uniform density and its convolution powers -/

/-- The uniform probability density on `[−w, w]`. -/
def unif (w : ℝ) : ℝ → ℝ := (Icc (-w) w).indicator (fun _ => 1 / (2 * w))

theorem unif_nonneg {w : ℝ} (hw : 0 < w) (x : ℝ) : 0 ≤ unif w x := by
  unfold unif
  apply Set.indicator_nonneg
  intro _ _
  positivity

theorem support_unif_subset (w : ℝ) : Function.support (unif w) ⊆ Icc (-w) w :=
  Set.support_indicator_subset

theorem hasCompactSupport_unif (w : ℝ) : HasCompactSupport (unif w) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc (support_unif_subset w)

theorem integrable_unif (w : ℝ) : Integrable (unif w) := by
  unfold unif
  exact (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc

theorem integral_unif {w : ℝ} (hw : 0 < w) : ∫ x, unif w x = 1 := by
  unfold unif
  rw [integral_indicator measurableSet_Icc, setIntegral_const, measureReal_def, Real.volume_Icc,
    ENNReal.toReal_ofReal (by linarith), smul_eq_mul]
  field_simp
  try norm_num

/-- The Fourier transform of the uniform density. -/
theorem paperFT_unif {w : ℝ} (hw : 0 < w) {z : ℂ} (hz : z ≠ 0) :
    Zeta23.paperFT (fun x => (unif w x : ℂ)) z =
      (Complex.exp (I * z * w) - Complex.exp (-(I * z * w))) / (2 * I * z * w) := by
  unfold Zeta23.paperFT
  have hind : (fun x : ℝ => (unif w x : ℂ) * Complex.exp (I * z * x)) =
      (Icc (-w) w).indicator (fun x : ℝ => ((1 / (2 * w) : ℝ) : ℂ) * Complex.exp (I * z * x)) := by
    funext x
    unfold unif
    by_cases hx : x ∈ Icc (-w) w
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
      simp
  rw [hind, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_const_mul]
  have hc : I * z ≠ 0 := mul_ne_zero I_ne_zero hz
  have := integral_exp_mul_complex (a := -w) (b := w) hc
  rw [this]
  have hw' : (w : ℂ) ≠ 0 := by exact_mod_cast hw.ne'
  push_cast
  field_simp
  try ring

theorem norm_paperFT_unif_le {w : ℝ} (hw : 0 < w) {z : ℂ} (hz : z ≠ 0) :
    ‖Zeta23.paperFT (fun x => (unif w x : ℂ)) z‖ ≤ Real.cosh (w * z.im) / (w * ‖z‖) := by
  rw [paperFT_unif hw hz, norm_div]
  have hden : ‖(2 : ℂ) * I * z * w‖ = 2 * w * ‖z‖ := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hw]
    simp
    ring
  rw [hden]
  have hnum : ‖Complex.exp (I * z * w) - Complex.exp (-(I * z * w))‖ ≤ 2 * Real.cosh (w * z.im) := by
    calc ‖Complex.exp (I * z * w) - Complex.exp (-(I * z * w))‖
        ≤ ‖Complex.exp (I * z * w)‖ + ‖Complex.exp (-(I * z * w))‖ := norm_sub_le _ _
      _ = Real.exp (-(w * z.im)) + Real.exp (w * z.im) := by
          rw [Complex.norm_exp, Complex.norm_exp]
          congr 2
          · simp [Complex.mul_re, Complex.mul_im]; ring
          · simp [Complex.mul_re, Complex.mul_im]; ring
      _ = 2 * Real.cosh (w * z.im) := by rw [Real.cosh_eq]; ring
  have hpos : 0 < 2 * w * ‖z‖ := by
    have := norm_pos_iff.mpr hz
    positivity
  calc ‖Complex.exp (I * z * w) - Complex.exp (-(I * z * w))‖ / (2 * w * ‖z‖)
      ≤ 2 * Real.cosh (w * z.im) / (2 * w * ‖z‖) := by gcongr
    _ = Real.cosh (w * z.im) / (w * ‖z‖) := by
        field_simp
        try ring

/-- The `(n+1)`-fold convolution power of the uniform density. -/
def upow (w : ℝ) : ℕ → ℝ → ℝ
  | 0 => unif w
  | n + 1 => unif w ⋆ upow w n

theorem integrable_upow (w : ℝ) (n : ℕ) : Integrable (upow w n) := by
  induction n with
  | zero => exact integrable_unif w
  | succ n ih => exact (integrable_unif w).integrable_convolution _ ih

theorem hasCompactSupport_upow (w : ℝ) (n : ℕ) : HasCompactSupport (upow w n) := by
  induction n with
  | zero => exact hasCompactSupport_unif w
  | succ n ih => exact (hasCompactSupport_unif w).convolution _ ih

theorem support_upow_subset {w : ℝ} (hw : 0 < w) (n : ℕ) :
    Function.support (upow w n) ⊆ Icc (-((n + 1) * w)) ((n + 1) * w) := by
  induction n with
  | zero =>
      simp only [upow]
      simpa using support_unif_subset w
  | succ n ih =>
      refine (support_convolution_subset _).trans ?_
      refine (Set.add_subset_add (support_unif_subset w) ih).trans ?_
      rw [Set.Icc_add_Icc (by linarith) (neg_le_self (by positivity))]
      push_cast
      apply Set.Icc_subset_Icc <;> linarith

theorem upow_nonneg {w : ℝ} (hw : 0 < w) (n : ℕ) (x : ℝ) : 0 ≤ upow w n x := by
  induction n generalizing x with
  | zero => exact unif_nonneg hw x
  | succ n ih =>
      show 0 ≤ (unif w ⋆ upow w n) x
      rw [convolution_def]
      refine integral_nonneg fun t => ?_
      simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
      exact mul_nonneg (unif_nonneg hw t) (ih _)

theorem integral_upow {w : ℝ} (hw : 0 < w) (n : ℕ) : ∫ x, upow w n x = 1 := by
  induction n with
  | zero => exact integral_unif hw
  | succ n ih =>
      show ∫ x, (unif w ⋆ upow w n) x = 1
      rw [integral_convolution _ (integrable_unif w) (integrable_upow w n)]
      simp [integral_unif hw, ih]

theorem paperFT_upow (w : ℝ) (n : ℕ) (z : ℂ) :
    Zeta23.paperFT (fun x => (upow w n x : ℂ)) z =
      Zeta23.paperFT (fun x => (unif w x : ℂ)) z ^ (n + 1) := by
  induction n with
  | zero => simp [upow]
  | succ n ih =>
      show Zeta23.paperFT (fun x => ((unif w ⋆ upow w n) x : ℂ)) z = _
      rw [paperFT_conv (integrable_unif w) (integrable_upow w n) (hasCompactSupport_unif w)
        (hasCompactSupport_upow w n), ih]
      ring

theorem norm_paperFT_upow_le {w : ℝ} (hw : 0 < w) (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    ‖Zeta23.paperFT (fun x => (upow w n x : ℂ)) z‖ ≤
      (Real.cosh (w * z.im) / (w * ‖z‖)) ^ (n + 1) := by
  rw [paperFT_upow, norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_paperFT_unif_le hw hz) _

/-! ## The smoothed bump -/

/-- A normalized smooth bump of radius `r` centred at `0`. -/
def smoothBump (r : ℝ) (hr : 0 < r) : ℝ → ℝ :=
  (⟨r / 2, r, by positivity, by linarith⟩ : ContDiffBump (0 : ℝ)).normed volume

theorem smoothBump_contDiff {r : ℝ} (hr : 0 < r) : ContDiff ℝ 2 (smoothBump r hr) :=
  ContDiffBump.contDiff_normed _ (n := 2)

theorem smoothBump_hasCompactSupport {r : ℝ} (hr : 0 < r) : HasCompactSupport (smoothBump r hr) :=
  ContDiffBump.hasCompactSupport_normed _

theorem smoothBump_nonneg {r : ℝ} (hr : 0 < r) (x : ℝ) : 0 ≤ smoothBump r hr x :=
  ContDiffBump.nonneg_normed _ x

theorem integral_smoothBump {r : ℝ} (hr : 0 < r) : ∫ x, smoothBump r hr x = 1 :=
  ContDiffBump.integral_normed _

theorem support_smoothBump_subset {r : ℝ} (hr : 0 < r) :
    Function.support (smoothBump r hr) ⊆ Icc (-r) r := by
  unfold smoothBump
  rw [ContDiffBump.support_normed_eq]
  intro x hx
  rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hx
  exact ⟨by linarith [abs_le.mp hx.le], by linarith [abs_le.mp hx.le]⟩

theorem integrable_smoothBump {r : ℝ} (hr : 0 < r) : Integrable (smoothBump r hr) :=
  (smoothBump_contDiff hr).continuous.integrable_of_hasCompactSupport
    (smoothBump_hasCompactSupport hr)

theorem norm_paperFT_smoothBump_le {r : ℝ} (hr : 0 < r) (z : ℂ) :
    ‖Zeta23.paperFT (fun x => (smoothBump r hr x : ℂ)) z‖ ≤ Real.exp (r * |z.im|) := by
  unfold Zeta23.paperFT
  have hbound : ∀ x : ℝ, ‖(smoothBump r hr x : ℂ) * Complex.exp (I * z * x)‖ ≤
      Real.exp (r * |z.im|) * smoothBump r hr x := by
    intro x
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (smoothBump_nonneg hr x)]
    by_cases hx : x ∈ Function.support (smoothBump r hr)
    · have hxr : |x| ≤ r := by
        have := support_smoothBump_subset hr hx
        rw [abs_le]; exact ⟨by linarith [this.1], this.2⟩
      calc smoothBump r hr x * ‖Complex.exp (I * z * x)‖
          ≤ smoothBump r hr x * Real.exp (r * |z.im|) := by
            gcongr
            · exact smoothBump_nonneg hr x
            · exact norm_exp_I_mul_le hxr
        _ = _ := by ring
    · rw [Function.notMem_support.mp hx]
      simp
  calc ‖∫ x : ℝ, (smoothBump r hr x : ℂ) * Complex.exp (I * z * x)‖
      ≤ ∫ x : ℝ, Real.exp (r * |z.im|) * smoothBump r hr x :=
        norm_integral_le_of_norm_le ((integrable_smoothBump hr).const_mul _)
          (Filter.Eventually.of_forall hbound)
    _ = Real.exp (r * |z.im|) := by
        rw [integral_const_mul, integral_smoothBump hr, mul_one]

/-- The smoothed bump: a smooth bump of radius `r` convolved with the `(n+1)`-fold power of the
uniform density of half-width `w`. -/
def phi (r : ℝ) (hr : 0 < r) (w : ℝ) (n : ℕ) : ℝ → ℝ :=
  smoothBump r hr ⋆ upow w n

theorem phi_contDiff {r : ℝ} (hr : 0 < r) (w : ℝ) (n : ℕ) : ContDiff ℝ 2 (phi r hr w n) :=
  HasCompactSupport.contDiff_convolution_left _ (smoothBump_hasCompactSupport hr)
    (smoothBump_contDiff hr) (integrable_upow w n).locallyIntegrable

theorem phi_hasCompactSupport {r : ℝ} (hr : 0 < r) (w : ℝ) (n : ℕ) :
    HasCompactSupport (phi r hr w n) :=
  (smoothBump_hasCompactSupport hr).convolution _ (hasCompactSupport_upow w n)

theorem integrable_phi {r : ℝ} (hr : 0 < r) (w : ℝ) (n : ℕ) : Integrable (phi r hr w n) :=
  (integrable_smoothBump hr).integrable_convolution _ (integrable_upow w n)

theorem support_phi_subset {r : ℝ} (hr : 0 < r) {w : ℝ} (hw : 0 < w) (n : ℕ) :
    Function.support (phi r hr w n) ⊆ Icc (-(r + (n + 1) * w)) (r + (n + 1) * w) := by
  unfold phi
  refine (support_convolution_subset _).trans ?_
  refine (Set.add_subset_add (support_smoothBump_subset hr) (support_upow_subset hw n)).trans ?_
  rw [Set.Icc_add_Icc (by linarith) (neg_le_self (by positivity))]
  apply Set.Icc_subset_Icc <;> linarith

theorem phi_nonneg {r : ℝ} (hr : 0 < r) {w : ℝ} (hw : 0 < w) (n : ℕ) (x : ℝ) :
    0 ≤ phi r hr w n x := by
  unfold phi
  rw [convolution_def]
  refine integral_nonneg fun t => ?_
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  exact mul_nonneg (smoothBump_nonneg hr t) (upow_nonneg hw n _)

theorem integral_phi {r : ℝ} (hr : 0 < r) {w : ℝ} (hw : 0 < w) (n : ℕ) :
    ∫ x, phi r hr w n x = 1 := by
  unfold phi
  rw [integral_convolution _ (integrable_smoothBump hr) (integrable_upow w n)]
  simp [integral_smoothBump hr, integral_upow hw n]

theorem paperFT_phi {r : ℝ} (hr : 0 < r) (w : ℝ) (n : ℕ) (z : ℂ) :
    Zeta23.paperFT (fun x => (phi r hr w n x : ℂ)) z =
      Zeta23.paperFT (fun x => (smoothBump r hr x : ℂ)) z *
        Zeta23.paperFT (fun x => (unif w x : ℂ)) z ^ (n + 1) := by
  unfold phi
  rw [paperFT_conv (integrable_smoothBump hr) (integrable_upow w n)
    (smoothBump_hasCompactSupport hr) (hasCompactSupport_upow w n), paperFT_upow]

/-- **The Fourier bound for the smoothed bump.** -/
theorem norm_paperFT_phi_le {r : ℝ} (hr : 0 < r) {w : ℝ} (hw : 0 < w) (n : ℕ) {z : ℂ}
    (hz : z ≠ 0) :
    ‖Zeta23.paperFT (fun x => (phi r hr w n x : ℂ)) z‖ ≤
      Real.exp (r * |z.im|) * (Real.cosh (w * z.im) / (w * ‖z‖)) ^ (n + 1) := by
  rw [paperFT_phi, norm_mul, norm_pow]
  gcongr
  · exact norm_paperFT_smoothBump_le hr z
  · exact norm_paperFT_unif_le hw hz

/-! ## A lower bound for the `L²` norm -/

/-- A nonnegative function of integral one supported in an interval of length `2s` has
`∫ φ² ≥ 1/(2s)`. -/
theorem integral_sq_ge_of_support {φ : ℝ → ℝ} {s : ℝ} (hs : 0 < s) (hφ : ∀ x, 0 ≤ φ x)
    (hsupp : Function.support φ ⊆ Icc (-s) s) (hint : Integrable φ) (hone : ∫ x, φ x = 1)
    (hsq : Integrable (fun x => φ x ^ 2)) :
    1 / (2 * s) ≤ ∫ x, φ x ^ 2 := by
  -- Cauchy–Schwarz: `1 = ∫ φ·1_{[-s,s]} ≤ (∫ φ²)^{1/2} (2s)^{1/2}`
  have hind : ∀ x, φ x = φ x * (Icc (-s) s).indicator (fun _ => (1 : ℝ)) x := by
    intro x
    by_cases hx : x ∈ Icc (-s) s
    · rw [Set.indicator_of_mem hx, mul_one]
    · rw [Set.indicator_of_notMem hx, mul_zero]
      by_contra h
      exact hx (hsupp h)
  have hmem2 : MemLp φ (ENNReal.ofReal 2) volume := by
    rw [ENNReal.ofReal_ofNat]
    exact (memLp_two_iff_integrable_sq hint.aestronglyMeasurable).mpr hsq
  have hmemI : MemLp ((Icc (-s) s).indicator (fun _ => (1 : ℝ))) (ENNReal.ofReal 2) volume := by
    rw [ENNReal.ofReal_ofNat]
    refine (memLp_two_iff_integrable_sq ?_).mpr ?_
    · exact (measurable_const.indicator measurableSet_Icc).aestronglyMeasurable
    · have : (fun x => (Icc (-s) s).indicator (fun _ => (1 : ℝ)) x ^ 2) =
          (Icc (-s) s).indicator (fun _ => (1 : ℝ)) := by
        funext x
        by_cases hx : x ∈ Icc (-s) s
        · simp [Set.indicator_of_mem hx]
        · simp [Set.indicator_of_notMem hx]
      rw [this]
      exact (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume) (p := 2) (q := 2)
    Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall hφ)
    (Filter.Eventually.of_forall fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) x)
    hmem2 hmemI
  have hlhs : ∫ x, φ x * (Icc (-s) s).indicator (fun _ => (1 : ℝ)) x = 1 := by
    calc ∫ x, φ x * (Icc (-s) s).indicator (fun _ => (1 : ℝ)) x = ∫ x, φ x :=
          integral_congr_ae (Filter.Eventually.of_forall fun x => (hind x).symm)
      _ = 1 := hone
  have hIsq : ∫ x, (Icc (-s) s).indicator (fun _ => (1 : ℝ)) x ^ (2 : ℝ) = 2 * s := by
    have : (fun x => (Icc (-s) s).indicator (fun _ => (1 : ℝ)) x ^ (2 : ℝ)) =
        (Icc (-s) s).indicator (fun _ => (1 : ℝ)) := by
      funext x
      by_cases hx : x ∈ Icc (-s) s
      · simp [Set.indicator_of_mem hx]
      · simp [Set.indicator_of_notMem hx]
    rw [this, integral_indicator measurableSet_Icc, setIntegral_const, measureReal_def,
      Real.volume_Icc, ENNReal.toReal_ofReal (by linarith), smul_eq_mul]
    ring
  have hφsq : ∫ x, φ x ^ (2 : ℝ) = ∫ x, φ x ^ 2 := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show φ x ^ (2 : ℝ) = φ x ^ 2
    exact Real.rpow_two _
  rw [hlhs, hIsq, hφsq] at hholder
  have hA : 0 ≤ ∫ x, φ x ^ 2 := integral_nonneg fun x => sq_nonneg _
  -- `1 ≤ A^{1/2} (2s)^{1/2}` gives `1 ≤ A·2s`
  have hsq' : (1 : ℝ) ≤ (∫ x, φ x ^ 2) * (2 * s) := by
    have h := hholder
    have hprod : (∫ x, φ x ^ 2) ^ (1 / (2 : ℝ)) * (2 * s) ^ (1 / (2 : ℝ)) =
        ((∫ x, φ x ^ 2) * (2 * s)) ^ (1 / (2 : ℝ)) := by
      rw [Real.mul_rpow hA (by linarith)]
    rw [hprod] at h
    have h2 : (1 : ℝ) ^ (2 : ℝ) ≤ (((∫ x, φ x ^ 2) * (2 * s)) ^ (1 / (2 : ℝ))) ^ (2 : ℝ) :=
      Real.rpow_le_rpow (by norm_num) h (by norm_num)
    rw [← Real.rpow_mul (by positivity), Real.one_rpow] at h2
    norm_num at h2
    exact h2
  rw [div_le_iff₀ (by positivity)]
  linarith

end

end RHTower.WeilDeletion
