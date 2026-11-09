import GaloisForLFunctions.EulerFETransportTheory.TheNormalizedHeightReflection
import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheMissingInputOfTransport
import GaloisForLFunctions.RHTower.SmoothAFEZetaChiPowerBound
import GaloisForLFunctions.RHTower.Sieve.ZeroFreeCombination

/-!
# Bounded escaping translates stay right of the critical line

Boundedness at reflected points and decay of the functional-equation factor
force a zero limit on any reflected disc crossing the critical line. Vitali
propagates that limit through a connected domain. If the domain meets the Euler
half-plane, its uniform positive lower bound gives a contradiction. No alignment
of prime phases is required. In particular, whole-quadrant boundedness is
impossible. The conductor-normalized reflection law remains valid.
-/

open Complex ComplexConjugate Filter Topology Metric Set
open RHTower
open GaloisForLFunctions.ArithmeticAuxiliaryDynamics

noncomputable section

namespace GaloisForLFunctions.EulerFETransportTheory

/-- Bounded reflected translates force decay on the right of the critical line. -/
private theorem tendsto_zeta_translate_zero_of_bounded
    {τ : ℕ → ℝ} (hτ : Tendsto τ atTop atTop)
    {s : ℂ} (hs0 : 1 / 2 < s.re) (hs1 : s.re < 1)
    (hbd : ∃ C : ℝ, ∀ j, ‖riemannZeta (heightReflection s + (τ j : ℂ) * I)‖ ≤ C) :
    Tendsto (fun j => riemannZeta (s + (τ j : ℂ) * I)) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := hbd
  have hbound : ∀ j, ‖conj (riemannZeta (heightReflection s + (τ j : ℂ) * I))‖ ≤ C := by
    intro j
    rw [norm_conj]
    exact hC j
  let A := Real.exp ((s.re - 1 / 2) * (Real.log Real.pi + Real.log 2 + 2))
  have hy : Tendsto (fun j => τ j + s.im) atTop atTop :=
    tendsto_atTop.2 fun b => (hτ.eventually_ge_atTop (b - s.im)).mono
      fun j hj => by linarith
  have hlim : Tendsto (fun j => A * (τ j + s.im) ^ (-(s.re - 1 / 2)) * C)
      atTop (𝓝 0) := by
    simpa using (((tendsto_rpow_neg_atTop (by linarith : 0 < s.re - 1 / 2)).comp hy).const_mul A).mul_const C
  apply squeeze_zero_norm' _ hlim
  filter_upwards [hy.eventually_ge_atTop 256] with j hj
  rw [zeta_height_reflection (by linarith) hs1, norm_mul]
  have heq : s + (τ j : ℂ) * I = (s.re : ℂ) + ((τ j + s.im : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [add_comm]
  have hchi := norm_zetaChi_le_right_line_rpow hs0.le hs1 hj
  rw [← heq] at hchi
  exact mul_le_mul hchi (hbound j) (norm_nonneg _) (by dsimp [A]; positivity)

private theorem exists_positive_vertical_lower_bound {σ : ℝ} (hσ : 1 < σ) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, c ≤ ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ := by
  let B := 1 + 1 / (σ - 1)
  refine ⟨Real.exp ((-22 - 3 * Real.log B - Real.log B) / 4), Real.exp_pos _, ?_⟩
  intro t
  apply Sieve.exp_le_norm_riemannZeta_shift hσ
  simpa [B] using
    Sieve.norm_riemannZeta_le (s := (σ : ℂ) + (2 * t : ℂ) * I) (by simpa using hσ)

private theorem re_gt_half_of_translatesBoundedOn_nonneg
    {τ : ℕ → ℝ} (hτ : Tendsto τ atTop atTop) (hτ0 : ∀ j, 0 ≤ τ j)
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUim : ∀ z ∈ U, 0 < z.im) {s₀ : ℂ} (hs₀ : s₀ ∈ U) (hs₀1 : 1 < s₀.re)
    (hbd : TranslatesBoundedOn τ U) {z : ℂ} (hz : z ∈ U) : 1 / 2 < z.re := by
  by_contra hcon
  have hzre : z.re ≤ 1 / 2 := not_lt.mp hcon
  obtain ⟨w, hwU, hwre⟩ := hUc.intermediate_value hz hs₀ continuous_re.continuousOn
    (⟨hzre, by linarith⟩ : (1 / 2 : ℝ) ∈ Icc z.re s₀.re)
  obtain ⟨ε₀, hε₀, hball⟩ := Metric.isOpen_iff.mp hUo w hwU
  let ε : ℝ := min ε₀ (1 / 2)
  have hε0 : 0 < ε := lt_min hε₀ (by norm_num)
  have hεU : ball w ε ⊆ U := (ball_subset_ball (min_le_left _ _)).trans hball
  have hεhalf : ε ≤ 1 / 2 := min_le_right _ _
  let Y : Set ℂ := ball w ε ∩ {x : ℂ | 1 / 2 < x.re}
  let c : ℂ := w + ((ε / 2 : ℝ) : ℂ)
  have hcre : c.re = 1 / 2 + ε / 2 := by simp [c, hwre]
  have hcball : c ∈ ball w ε := by
    rw [mem_ball, dist_eq_norm]
    dsimp [c]
    rw [add_sub_cancel_left, norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith
  have hcY : c ∈ Y := ⟨hcball, by change 1 / 2 < c.re; rw [hcre]; linarith⟩
  have hcU : c ∈ U := hεU hcball
  have hY : IsOpen Y := isOpen_ball.inter (isOpen_lt continuous_const continuous_re)
  have hYU : Y ⊆ U := fun _ hx => hεU hx.1
  have hconv : ∀ x ∈ Y, Tendsto (fun j => riemannZeta (x + (τ j : ℂ) * I))
      atTop (𝓝 0) := by
    intro x hx
    have hxn : ‖x - w‖ < ε := by simpa only [mem_ball, dist_eq_norm] using hx.1
    have hx1 : x.re < 1 := by
      have hr := (abs_lt.mp ((Complex.abs_re_le_norm (x - w)).trans_lt hxn)).2
      rw [sub_re, hwre] at hr
      linarith
    have hRball : heightReflection x ∈ ball w ε := by
      have heq : heightReflection x - w = -conj (x - w) := by
        apply Complex.ext
        · simp only [heightReflection, sub_re, one_re, conj_re, neg_re, hwre]
          ring
        · simp only [heightReflection, sub_im, one_im, conj_im, neg_im]
          ring
      rwa [mem_ball, dist_eq_norm, heq, norm_neg, norm_conj]
    obtain ⟨r, hr, -, C, hC⟩ := hbd _ (hεU hRball)
    exact tendsto_zeta_translate_zero_of_bounded hτ hx.2 hx1
      ⟨C, fun j => hC j _ (mem_ball_self hr)⟩
  have hdiff : ∀ j, DifferentiableOn ℂ
      (fun x => riemannZeta (x + (τ j : ℂ) * I)) U := by
    intro j x hx
    apply DifferentiableAt.differentiableWithinAt
    refine (differentiableAt_riemannZeta ?_).comp x (differentiableAt_id.add_const _)
    intro heq
    have hi := congrArg Complex.im heq
    simp at hi
    have hxpos := hUim x hx
    have hj := hτ0 j
    linarith
  have hacc : ∃ᶠ x in 𝓝[≠] c, x ∈ Y :=
    (eventually_nhdsWithin_of_eventually_nhds (hY.mem_nhds hcY)).frequently
  obtain ⟨G, hGdiff, hG⟩ := HTGeometry.vitali_tendstoLocallyUniformlyOn_of_isPreconnected
    hUc hdiff hbd hcU hacc (fun x hx => ⟨0, hconv x hx⟩)
  have hzero : EqOn G 0 U := by
    apply (hGdiff.analyticOnNhd hUo).eqOn_zero_of_preconnected_of_eventuallyEq_zero hUc hcU
    filter_upwards [hY.mem_nhds hcY] with x hx
    exact tendsto_nhds_unique (hG.tendsto_at (hYU hx)) (hconv x hx)
  have hlim := (hG.tendsto_at hs₀).norm
  rw [hzero hs₀, Pi.zero_apply, norm_zero] at hlim
  obtain ⟨a, ha, hlower⟩ := exists_positive_vertical_lower_bound hs₀1
  obtain ⟨j, hj⟩ := (hlim.eventually (gt_mem_nhds ha)).exists
  have heq : s₀ + (τ j : ℂ) * I = (s₀.re : ℂ) + ((s₀.im + τ j : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp
  rw [heq] at hj
  exact (not_lt_of_ge (hlower _)) hj

/-- Every connected open boundedness domain in the upper half-plane that meets
the Euler half-plane lies strictly right of the critical line. The shifts need
only escape; no prime-phase return or target profile is assumed. -/
theorem re_gt_half_of_translatesBoundedOn
    {τ : ℕ → ℝ} (hτ : Tendsto τ atTop atTop)
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUim : ∀ z ∈ U, 0 < z.im) {s₀ : ℂ} (hs₀ : s₀ ∈ U) (hs₀1 : 1 < s₀.re)
    (hbd : TranslatesBoundedOn τ U) {z : ℂ} (hz : z ∈ U) : 1 / 2 < z.re := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hτ.eventually_ge_atTop 0)
  have hbd' : TranslatesBoundedOn (fun j => τ (j + N)) U := by
    intro x hx
    obtain ⟨r, hr, hsub, C, hC⟩ := hbd x hx
    exact ⟨r, hr, hsub, C, fun j w hw => hC (j + N) w hw⟩
  exact re_gt_half_of_translatesBoundedOn_nonneg (hτ.comp (tendsto_add_atTop_nat N))
    (fun j => hN _ (by change N ≤ j + N; omega)) hUo hUc hUim hs₀ hs₀1 hbd' hz

/-- No sequence escaping to positive infinity has locally bounded zeta translates
on the whole upper quadrant. No recurrence hypothesis is needed. -/
theorem not_translatesLocallyBounded_of_tendsto_atTop
    {τ : ℕ → ℝ} (hτ : Tendsto τ atTop atTop) : ¬TranslatesLocallyBounded τ := by
  intro hbd
  have h := re_gt_half_of_translatesBoundedOn hτ isOpen_upperQuadrant
    isPreconnected_upperQuadrant (fun _ hx => hx.2)
    (s₀ := 2 + I) (by constructor <;> norm_num) (by norm_num)
    hbd (z := 1 / 4 + I) (by constructor <;> norm_num)
  norm_num at h

end GaloisForLFunctions.EulerFETransportTheory

#print axioms GaloisForLFunctions.EulerFETransportTheory.not_translatesLocallyBounded_of_tendsto_atTop
#print axioms GaloisForLFunctions.EulerFETransportTheory.re_gt_half_of_translatesBoundedOn
