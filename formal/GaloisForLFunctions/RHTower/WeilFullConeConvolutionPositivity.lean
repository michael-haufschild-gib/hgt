import GaloisForLFunctions.RHTower.WeilFullConeDyadicRigidity

/-!
# Weil positivity for convolution tests `g ⋆ Φχ_L`

Let `lam` be full-cone Weil-positive and `v(n) = (Λ(n) − lam(n))/√n` (`normDeficit`), and let
`K` be the autocorrelation of Riemann's kernel `Φ`. Write
`riemannPairForm K g y = ∫∫ g(v) conj g(w) K(y + w − v) dv dw`.

**Theorem** (`normDeficit_pairing_nonneg`). For every continuous compactly supported `g` and
bounded `v`: `Re Σ_n v(n)(riemannPairForm K g (log n) + riemannPairForm K g (−log n)) ≥ 0`.

**Proof.**
- The test `g ⋆ Φχ_L` (`convRiemannTest`) is `C²` and compactly supported.
- Its autocorrelation is `riemannPairForm K_L g` (`weilTest_convRiemannTest`).
- Its transform factors as `paperFT g · paperFT(Φχ_L)`, so its zero side is at most
  `(∫|g|e^{|x|/2})²` times the near-radical energy of `Φχ_L`, which tends to `0`.
- Weil positivity then gives the inequality up to that error. Letting `L → ∞`,
  `K_L → K` pointwise (`tendsto_truncatedRiemannAutocorr_atTop`), under a uniform bound
  `K_L(y) ≤ Ce^{−2|y|}`.

**Extension** (`normDeficit_pairing_nonneg_of_decay`). The same holds for continuous `g` with
`‖g(x)‖ ≤ D(1 + |x|)^{−(k+2)}`, provided `Σ |v(n)|(1 + |log n|)^{−k} < ∞`. The proof truncates
with `linearCutoff` and bounds the pairings through `(1+|y|) ≤ (1+|v|)(1+|w|)(1+|y+w−v|)`.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate Convolution FourierTransform
open Zeta23

namespace RHTower

noncomputable section

/-! ## Convolution tests `g ⋆ Φχ_L` -/

/-- The convolution test `(g ⋆ Φχ_L)(x) = ∫ g(t) Φχ_L(x − t) dt`. -/
def convRiemannTest (L : ℝ) (g : ℝ → ℂ) : ℝ → ℂ :=
  g ⋆[ContinuousLinearMap.mul ℝ ℂ] truncatedRiemannKernel L

theorem convRiemannTest_apply (L : ℝ) (g : ℝ → ℂ) (x : ℝ) :
    convRiemannTest L g x = ∫ t, g t * truncatedRiemannKernel L (x - t) := by
  rw [convRiemannTest, convolution_def]; rfl

theorem contDiff_convRiemannTest (L : ℝ) {g : ℝ → ℂ} (hg : Continuous g) :
    ContDiff ℝ 2 (convRiemannTest L g) :=
  (hasCompactSupport_truncatedRiemannKernel L).contDiff_convolution_right
    (ContinuousLinearMap.mul ℝ ℂ) hg.locallyIntegrable
    (contDiff_nearRadicalTest L (fun _ : Fin 1 => (1 : ℂ)))

theorem hasCompactSupport_convRiemannTest (L : ℝ) {g : ℝ → ℂ} (hgc : HasCompactSupport g) :
    HasCompactSupport (convRiemannTest L g) :=
  hgc.convolution _ (hasCompactSupport_truncatedRiemannKernel L)

theorem exists_radius_vanishing_complex {g : ℝ → ℂ} (hgc : HasCompactSupport g) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ x, R < |x| → g x = 0 := by
  obtain ⟨R, hR⟩ := hgc.isCompact.isBounded.subset_closedBall 0
  refine ⟨|R|, abs_nonneg _, fun x hx => ?_⟩
  by_contra hne
  have hmem := hR (subset_tsupport g hne)
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at hmem
  linarith [le_abs_self R]

/-- A continuous function on the plane vanishing off a box is integrable. -/
theorem integrable_prod_of_vanish {F : ℝ × ℝ → ℂ} (hF : Continuous F) {A B : ℝ}
    (hAB : ∀ p : ℝ × ℝ, F p ≠ 0 → |p.1| ≤ A ∧ |p.2| ≤ B) :
    Integrable F (volume.prod volume) := by
  have hc : HasCompactSupport F := by
    refine HasCompactSupport.intro ((isCompact_Icc (a := -A) (b := A)).prod
      (isCompact_Icc (a := -B) (b := B))) fun p hp => ?_
    by_contra hne
    obtain ⟨h1, h2⟩ := hAB p hne
    exact hp ⟨⟨by linarith [neg_abs_le p.1], by linarith [le_abs_self p.1]⟩,
      ⟨by linarith [neg_abs_le p.2], by linarith [le_abs_self p.2]⟩⟩
  exact hF.integrable_of_hasCompactSupport hc

/-- The transform of a convolution test factors. -/
theorem paperFT_convRiemannTest (L : ℝ) {g : ℝ → ℂ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (z : ℂ) :
    paperFT (convRiemannTest L g) z = paperFT g z * paperFT (truncatedRiemannKernel L) z := by
  obtain ⟨R, hR0, hR⟩ := exists_radius_vanishing_complex hgc
  have hΦ := continuous_truncatedRiemannKernel L
  unfold paperFT
  have e1 : (fun x : ℝ => convRiemannTest L g x * Complex.exp (I * z * (x : ℂ))) =
      fun x : ℝ => ∫ t, g t * truncatedRiemannKernel L (x - t) * Complex.exp (I * z * (x : ℂ)) := by
    funext x; rw [convRiemannTest_apply, ← integral_mul_const]
  rw [e1, integral_integral_swap]
  · rw [← integral_mul_const]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    have e2 : (fun x : ℝ => g t * truncatedRiemannKernel L (x - t) * Complex.exp (I * z * (x : ℂ))) =
        fun x : ℝ => (g t * Complex.exp (I * z * (t : ℂ))) *
          (fun u : ℝ => truncatedRiemannKernel L u * Complex.exp (I * z * (u : ℂ))) (x - t) := by
      funext x
      have ex : Complex.exp (I * z * (x : ℂ)) =
          Complex.exp (I * z * (t : ℂ)) * Complex.exp (I * z * ((x - t : ℝ) : ℂ)) := by
        rw [← Complex.exp_add]; congr 1; push_cast; ring
      rw [ex]; ring
    beta_reduce
    rw [e2, integral_const_mul, integral_sub_right_eq_self
      (fun u : ℝ => truncatedRiemannKernel L u * Complex.exp (I * z * (u : ℂ))) t]
  · refine integrable_prod_of_vanish (A := R + |L|) (B := R) ?_ fun p hp => ?_
    · exact ((hg.comp continuous_snd).mul (hΦ.comp (continuous_fst.sub continuous_snd))).mul
        (Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
          continuous_fst)))
    · change g p.2 * truncatedRiemannKernel L (p.1 - p.2) * Complex.exp (I * z * (p.1 : ℂ)) ≠ 0 at hp
      have hgt : g p.2 ≠ 0 := fun h => hp (by rw [h]; ring)
      have hΦt : truncatedRiemannKernel L (p.1 - p.2) ≠ 0 := fun h => hp (by rw [h]; ring)
      have h1 : |p.2| ≤ R := by by_contra h; exact hgt (hR _ (lt_of_not_ge h))
      have h2 : |p.1 - p.2| ≤ L := by
        by_contra h; exact hΦt (truncatedRiemannKernel_eq_zero (lt_of_not_ge h))
      refine ⟨?_, h1⟩
      calc |p.1| = |(p.1 - p.2) + p.2| := by ring_nf
        _ ≤ |p.1 - p.2| + |p.2| := abs_add_le _ _
        _ ≤ R + |L| := by linarith [le_abs_self L]


theorem continuous_convRiemannTest (L : ℝ) {g : ℝ → ℂ} (hg : Continuous g) :
    Continuous (convRiemannTest L g) :=
  (contDiff_convRiemannTest L hg).continuous

/-- The double pairing `∫∫ g(v) conj g(w) κ(y + w − v) dv dw`. -/
def riemannPairForm (κ : ℝ → ℝ) (g : ℝ → ℂ) (y : ℝ) : ℂ :=
  ∫ v, ∫ w, g v * conj (g w) * (κ (y + w - v) : ℂ)

theorem truncatedRiemannKernel_conj (L u : ℝ) :
    conj (truncatedRiemannKernel L u) = truncatedRiemannKernel L u := by
  rw [truncatedRiemannKernel_eq, Complex.conj_ofReal]

theorem integral_truncatedRiemannKernel_shift_mul (L v a : ℝ) :
    ∫ t, truncatedRiemannKernel L (t - v) * truncatedRiemannKernel L (t - a) =
      (truncatedRiemannAutocorr L (a - v) : ℂ) := by
  unfold truncatedRiemannAutocorr
  rw [← integral_complex_ofReal]
  have h := integral_sub_right_eq_self (μ := volume)
    (fun s : ℝ => ((truncatedRiemannKernelReal L s * truncatedRiemannKernelReal L (s - (a - v)) : ℝ)
      : ℂ)) v
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [truncatedRiemannKernel_eq]
  rw [show t - v - (a - v) = t - a by ring]
  push_cast; ring

/-- **The autocorrelation of a convolution test.** -/
theorem weilTest_convRiemannTest (L : ℝ) {g : ℝ → ℂ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (y : ℝ) :
    EF.weilTest (convRiemannTest L g) (convRiemannTest L g) y =
      riemannPairForm (truncatedRiemannAutocorr L) g y := by
  obtain ⟨R, hR0, hR⟩ := exists_radius_vanishing_complex hgc
  have hΦ := continuous_truncatedRiemannKernel L
  have hf := continuous_convRiemannTest L hg
  set f := convRiemannTest L g with hfdef
  unfold EF.weilTest EF.tilde
  rw [convolution_def]
  have e1 : ∀ t : ℝ, (ContinuousLinearMap.mul ℝ ℂ) (f t) (conj (f (-(y - t)))) =
      ∫ v, g v * truncatedRiemannKernel L (t - v) * conj (f (t - y)) := by
    intro t
    rw [ContinuousLinearMap.mul_apply', show -(y - t) = t - y by ring, hfdef,
      convRiemannTest_apply, ← integral_mul_const]
  simp_rw [e1]
  rw [integral_integral_swap]
  · unfold riemannPairForm
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    have e2 : ∀ t : ℝ, g v * truncatedRiemannKernel L (t - v) * conj (f (t - y)) =
        g v * ∫ w, conj (g w) * (truncatedRiemannKernel L (t - v) *
          truncatedRiemannKernel L (t - (y + w))) := by
      intro t
      rw [hfdef, convRiemannTest_apply, ← integral_conj, mul_assoc, ← integral_const_mul]
      congr 1
      refine integral_congr_ae (Eventually.of_forall fun w => ?_)
      beta_reduce
      rw [map_mul, truncatedRiemannKernel_conj, show t - y - w = t - (y + w) by ring]
      ring
    simp_rw [e2]
    rw [integral_const_mul, integral_integral_swap, ← integral_const_mul]
    · refine integral_congr_ae (Eventually.of_forall fun w => ?_)
      beta_reduce
      rw [integral_const_mul, integral_truncatedRiemannKernel_shift_mul]
      ring
    · refine integrable_prod_of_vanish (A := |v| + |L|) (B := R) ?_ fun p hp => ?_
      · exact (hg.comp continuous_snd).star.mul ((hΦ.comp (continuous_fst.sub continuous_const)).mul
          (hΦ.comp (continuous_fst.sub (continuous_const.add continuous_snd))))
      · change conj (g p.2) * (truncatedRiemannKernel L (p.1 - v) *
          truncatedRiemannKernel L (p.1 - (y + p.2))) ≠ 0 at hp
        have hgt : g p.2 ≠ 0 := fun h => hp (by rw [h, map_zero]; ring)
        have hΦt : truncatedRiemannKernel L (p.1 - v) ≠ 0 := fun h => hp (by rw [h]; ring)
        have h1 : |p.2| ≤ R := by by_contra h; exact hgt (hR _ (lt_of_not_ge h))
        have h2 : |p.1 - v| ≤ L := by
          by_contra h; exact hΦt (truncatedRiemannKernel_eq_zero (lt_of_not_ge h))
        refine ⟨?_, h1⟩
        calc |p.1| = |(p.1 - v) + v| := by ring_nf
          _ ≤ |p.1 - v| + |v| := abs_add_le _ _
          _ ≤ |v| + |L| := by linarith [le_abs_self L]
  · refine integrable_prod_of_vanish (A := R + |L|) (B := R) ?_ fun p hp => ?_
    · exact ((hg.comp continuous_snd).mul (hΦ.comp (continuous_fst.sub continuous_snd))).mul
        (hf.comp (continuous_fst.sub continuous_const)).star
    · change g p.2 * truncatedRiemannKernel L (p.1 - p.2) * conj (f (p.1 - y)) ≠ 0 at hp
      have hgt : g p.2 ≠ 0 := fun h => hp (by rw [h]; ring)
      have hΦt : truncatedRiemannKernel L (p.1 - p.2) ≠ 0 := fun h => hp (by rw [h]; ring)
      have h1 : |p.2| ≤ R := by by_contra h; exact hgt (hR _ (lt_of_not_ge h))
      have h2 : |p.1 - p.2| ≤ L := by
        by_contra h; exact hΦt (truncatedRiemannKernel_eq_zero (lt_of_not_ge h))
      refine ⟨?_, h1⟩
      calc |p.1| = |(p.1 - p.2) + p.2| := by ring_nf
        _ ≤ |p.1 - p.2| + |p.2| := abs_add_le _ _
        _ ≤ R + |L| := by linarith [le_abs_self L]


/-! ## The kernel autocorrelations: continuity, decay, convergence -/

theorem exists_riemannKernelReal_le_exp :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, riemannKernelReal x ≤ C * Real.exp (-(4 * |x|)) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_riemannPhiKernel_le_exp (B := 4) (by norm_num)
  refine ⟨C, hC0, fun x => ?_⟩
  have h := hC x
  rwa [riemannPhiKernel_eq_ofReal, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (riemannKernelReal_pos x)] at h

theorem integrable_exp_neg_four_abs : Integrable (fun x : ℝ => Real.exp (-(4 * |x|))) := by
  refine integrable_exp_neg_abs.mono' (by fun_prop) (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr (by nlinarith [abs_nonneg x])

theorem riemannAutocorr_continuous : Continuous riemannAutocorr := by
  obtain ⟨C, hC0, hC⟩ := exists_riemannKernelReal_le_exp
  unfold riemannAutocorr
  refine continuous_of_dominated (bound := fun t => C * Real.exp (-(4 * |t|)) * C)
    (fun y => (continuous_riemannKernelReal.mul (continuous_riemannKernelReal.comp
      (continuous_id.sub continuous_const))).aestronglyMeasurable)
    (fun y => Eventually.of_forall fun t => ?_) ((integrable_exp_neg_four_abs.const_mul C).mul_const C)
    (Eventually.of_forall fun t => continuous_const.mul (continuous_riemannKernelReal.comp
      (continuous_const.sub continuous_id)))
  have h1 := hC t
  have h2 : riemannKernelReal (t - y) ≤ C := (hC _).trans (by
    have := Real.exp_le_one_iff.mpr (by nlinarith [abs_nonneg (t - y)] : -(4 * |t - y|) ≤ 0)
    nlinarith)
  rw [Real.norm_eq_abs, abs_of_pos (mul_pos (riemannKernelReal_pos _) (riemannKernelReal_pos _))]
  exact mul_le_mul h1 h2 (riemannKernelReal_pos _).le (by positivity)

theorem truncatedRiemannAutocorr_continuous (L : ℝ) : Continuous (truncatedRiemannAutocorr L) := by
  obtain ⟨C, hC0, hC⟩ := exists_riemannKernelReal_le_exp
  unfold truncatedRiemannAutocorr
  have hc := continuous_truncatedRiemannKernelReal L
  refine continuous_of_dominated (bound := fun t => C * Real.exp (-(4 * |t|)) * C)
    (fun y => (hc.mul (hc.comp (continuous_id.sub continuous_const))).aestronglyMeasurable)
    (fun y => Eventually.of_forall fun t => ?_) ((integrable_exp_neg_four_abs.const_mul C).mul_const C)
    (Eventually.of_forall fun t => continuous_const.mul (hc.comp (continuous_const.sub continuous_id)))
  have h1 := (truncatedRiemannKernelReal_le L t).trans (hC t)
  have h2 : truncatedRiemannKernelReal L (t - y) ≤ C := (truncatedRiemannKernelReal_le L _).trans
    ((hC _).trans (by
      have := Real.exp_le_one_iff.mpr (by nlinarith [abs_nonneg (t - y)] : -(4 * |t - y|) ≤ 0)
      nlinarith))
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (truncatedRiemannKernelReal_nonneg _ _)
    (truncatedRiemannKernelReal_nonneg _ _))]
  exact mul_le_mul h1 h2 (truncatedRiemannKernelReal_nonneg _ _) (by positivity)

/-- `K_L → K` pointwise. -/
theorem tendsto_truncatedRiemannAutocorr_atTop (y : ℝ) :
    Tendsto (fun L => truncatedRiemannAutocorr L y) atTop (𝓝 (riemannAutocorr y)) := by
  obtain ⟨C, hC0, hC⟩ := exists_riemannKernelReal_le_exp
  unfold truncatedRiemannAutocorr riemannAutocorr
  refine tendsto_integral_filter_of_dominated_convergence
    (fun t => C * Real.exp (-(4 * |t|)) * C)
    (Eventually.of_forall fun L => ((continuous_truncatedRiemannKernelReal L).mul
      ((continuous_truncatedRiemannKernelReal L).comp (continuous_id.sub continuous_const))
      ).aestronglyMeasurable)
    (Eventually.of_forall fun L => Eventually.of_forall fun t => ?_)
    ((integrable_exp_neg_four_abs.const_mul C).mul_const C)
    (Eventually.of_forall fun t => ?_)
  · have h1 := (truncatedRiemannKernelReal_le L t).trans (hC t)
    have h2 : truncatedRiemannKernelReal L (t - y) ≤ C := (truncatedRiemannKernelReal_le L _).trans
      ((hC _).trans (by
        have := Real.exp_le_one_iff.mpr (by nlinarith [abs_nonneg (t - y)] : -(4 * |t - y|) ≤ 0)
        nlinarith))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (truncatedRiemannKernelReal_nonneg _ _)
      (truncatedRiemannKernelReal_nonneg _ _))]
    exact mul_le_mul h1 h2 (truncatedRiemannKernelReal_nonneg _ _) (by positivity)
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop (|t| + |t - y| + 1)] with L hL
    unfold truncatedRiemannKernelReal
    rw [bulkCutoff_eq_one (by linarith [abs_nonneg (t - y)]),
      bulkCutoff_eq_one (by linarith [abs_nonneg t]), mul_one, mul_one]

/-- Double-exponential-type decay of `K`, in the crude form `K(y) ≤ C e^{−2|y|}`. -/
theorem exists_riemannAutocorr_le_exp :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y, riemannAutocorr y ≤ C * Real.exp (-(2 * |y|)) := by
  obtain ⟨C, hC0, hC⟩ := exists_truncatedRiemannAutocorr_le
  exact ⟨C, hC0, fun y => le_of_tendsto (tendsto_truncatedRiemannAutocorr_atTop y)
    (Eventually.of_forall fun L => hC L y)⟩

/-! ## The zero side of a convolution test -/

theorem norm_paperFT_le_of_abs_im_le {g : ℝ → ℂ} (hg : Continuous g) (hgc : HasCompactSupport g)
    {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    ‖paperFT g z‖ ≤ ∫ u, ‖g u‖ * Real.exp (1 / 2 * |u|) := by
  unfold paperFT
  refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun _ => norm_nonneg _) ?_ (Eventually.of_forall fun u => ?_))
  · exact (hg.norm.mul (Real.continuous_exp.comp (continuous_const.mul continuous_abs))
      ).integrable_of_hasCompactSupport hgc.norm.mul_right
  · simp only
    rw [norm_mul, Complex.norm_exp]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
    have hre : (I * z * (u : ℂ)).re = -(z.im * u) := by simp [Complex.mul_re]
    rw [hre]
    have h2 : |z.im * u| ≤ 1 / 2 * |u| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right hz (abs_nonneg u)
    linarith [neg_abs_le (z.im * u)]

/-- The zero side of a convolution test is controlled by the near-radical energy. -/
theorem norm_W_convRiemannTest_le (L : ℝ) {g : ℝ → ℂ} (hg : Continuous g)
    (hgc : HasCompactSupport g) {Λ : ℝ} (hΛ : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ Λ) :
    ‖zetaZeroConfig.W (convRiemannTest L g) (convRiemannTest L g)‖ ≤
      (∫ u, ‖g u‖ * Real.exp (1 / 2 * |u|)) ^ 2 *
        ((5 / 4) * zetaInvSqSum * truncatedRiemannTailEnergy L ^ 2) := by
  set M := ∫ u, ‖g u‖ * Real.exp (1 / 2 * |u|) with hM
  have hM0 : 0 ≤ M := integral_nonneg fun _ => by positivity
  have hE0 := truncatedRiemannTailEnergy_nonneg L
  have h := norm_W_le_of_zero_bound (f := convRiemannTest L g)
    (E := M * truncatedRiemannTailEnergy L) (by positivity) (fun ρ => ?_)
  · calc _ ≤ (5 / 4) * zetaInvSqSum * (M * truncatedRiemannTailEnergy L) ^ 2 := h
      _ = _ := by ring
  have hmem := ρ.2
  have hstrip' : 0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1 := by
    have h : IsNontrivialZero (ρ : ℂ) := hmem
    exact ⟨h.2.1, h.2.2⟩
  have hIm : |(gammaOf (ρ : ℂ)).im| ≤ 1 / 2 := (WeilEF.abs_gammaOf_im_lt hstrip').le
  have hIm' : |((starRingEnd ℂ) (gammaOf (ρ : ℂ))).im| ≤ 1 / 2 := by
    rw [Complex.conj_im, abs_neg]; exact hIm
  obtain ⟨hv1, hv2⟩ := truncatedRiemannKernel_zero_bound L hΛ ρ
  constructor
  · rw [paperFT_convRiemannTest L hg hgc, norm_mul]
    have hm := norm_paperFT_le_of_abs_im_le hg hgc hIm
    calc (1 + |(ρ : ℂ).im|) * (‖paperFT g (gammaOf ρ)‖ *
          ‖paperFT (truncatedRiemannKernel L) (gammaOf ρ)‖)
        = ‖paperFT g (gammaOf ρ)‖ *
          ((1 + |(ρ : ℂ).im|) * ‖paperFT (truncatedRiemannKernel L) (gammaOf ρ)‖) := by ring
      _ ≤ M * truncatedRiemannTailEnergy L := mul_le_mul hm hv1 (by positivity) hM0
  · rw [paperFT_convRiemannTest L hg hgc, norm_mul]
    have hm := norm_paperFT_le_of_abs_im_le hg hgc hIm'
    calc (1 + |(ρ : ℂ).im|) * (‖paperFT g ((starRingEnd ℂ) (gammaOf ρ))‖ *
          ‖paperFT (truncatedRiemannKernel L) ((starRingEnd ℂ) (gammaOf ρ))‖)
        = ‖paperFT g ((starRingEnd ℂ) (gammaOf ρ))‖ *
          ((1 + |(ρ : ℂ).im|) *
            ‖paperFT (truncatedRiemannKernel L) ((starRingEnd ℂ) (gammaOf ρ))‖) := by ring
      _ ≤ M * truncatedRiemannTailEnergy L := mul_le_mul hm hv2 (by positivity) hM0


/-! ## Positivity of the deviation pairing -/

/-- Weil positivity for the convolution test at a fixed truncation. -/
theorem normDeficit_pairing_ge_of_truncation {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (L : ℝ)
    {g : ℝ → ℂ} (hg : Continuous g) (hgc : HasCompactSupport g) {Λ : ℝ}
    (hΛ : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ Λ) :
    -((∫ u, ‖g u‖ * Real.exp (1 / 2 * |u|)) ^ 2 *
        ((5 / 4) * zetaInvSqSum * truncatedRiemannTailEnergy L ^ 2)) ≤
      (∑' n : ℕ, ((normDeficit lam n : ℝ) : ℂ) *
        (riemannPairForm (truncatedRiemannAutocorr L) g (Real.log n) +
          riemannPairForm (truncatedRiemannAutocorr L) g (-Real.log n))).re := by
  set f := convRiemannTest L g with hfdef
  have hfd := contDiff_convRiemannTest L hg
  have hfc := hasCompactSupport_convRiemannTest L hgc
  set k := EF.weilTest f f with hk
  have hkc : HasCompactSupport k := EF.weilTest_hasCompactSupport hfc hfc
  have hpos := hW f hfd hfc
  rw [← hk, weilFullFunctional_eq_sub lam hkc, ← weilFullFunctional_vonMangoldt, hk,
    ← zeta_W_eq_weilFullFunctional hfd hfc, ← hk] at hpos
  have hkp : ∀ y, k y = riemannPairForm (truncatedRiemannAutocorr L) g y := fun y => by
    rw [hk, hfdef, weilTest_convRiemannTest L hg hgc]
  have hterm : ∀ n : ℕ, ((if 2 ≤ n then (lam n - ArithmeticFunction.vonMangoldt n) / Real.sqrt n
      else 0 : ℝ) : ℂ) * (k (Real.log n) + k (-Real.log n)) =
      -(((normDeficit lam n : ℝ) : ℂ) * (riemannPairForm (truncatedRiemannAutocorr L) g (Real.log n) +
        riemannPairForm (truncatedRiemannAutocorr L) g (-Real.log n))) := by
    intro n
    rw [hkp, hkp]
    unfold normDeficit
    split_ifs
    · push_cast; ring
    · push_cast; ring
  simp_rw [hterm] at hpos
  rw [tsum_neg, sub_neg_eq_add, Complex.add_re] at hpos
  have hW' := norm_W_convRiemannTest_le L hg hgc hΛ
  have := Complex.re_le_norm (zetaZeroConfig.W f f)
  have h2 : -(zetaZeroConfig.W f f).re ≤ ‖zetaZeroConfig.W f f‖ := by
    have := Complex.abs_re_le_norm (zetaZeroConfig.W f f)
    linarith [neg_abs_le (zetaZeroConfig.W f f).re]
  linarith

/-- A pointwise bound for the double pairing of a compactly supported `g`. -/
theorem norm_riemannPairForm_le {κ : ℝ → ℝ} {C : ℝ} (hC0 : 0 ≤ C)
    (hκ : ∀ y, |κ y| ≤ C * Real.exp (-(2 * |y|))) {g : ℝ → ℂ} (hg : Continuous g)
    (hgc : HasCompactSupport g) {R : ℝ} (hR : ∀ x, R < |x| → g x = 0) (y : ℝ) :
    ‖riemannPairForm κ g y‖ ≤
      C * Real.exp (4 * R) * Real.exp (-(2 * |y|)) * (∫ u, ‖g u‖) ^ 2 := by
  set c := C * Real.exp (4 * R) * Real.exp (-(2 * |y|)) with hc
  have hc0 : 0 ≤ c := by positivity
  have hgi : Integrable fun u => ‖g u‖ := (hg.norm.integrable_of_hasCompactSupport hgc.norm)
  have hpt : ∀ v w, ‖g v * conj (g w) * (κ (y + w - v) : ℂ)‖ ≤ ‖g v‖ * ‖g w‖ * c := by
    intro v w
    rw [norm_mul, norm_mul, RCLike.norm_conj, Complex.norm_real, Real.norm_eq_abs]
    by_cases hv : g v = 0
    · rw [hv, norm_zero]; simp
    by_cases hw : g w = 0
    · rw [hw, norm_zero]; simp
    have hv' : |v| ≤ R := by by_contra h; exact hv (hR _ (lt_of_not_ge h))
    have hw' : |w| ≤ R := by by_contra h; exact hw (hR _ (lt_of_not_ge h))
    refine mul_le_mul_of_nonneg_left ((hκ _).trans ?_) (by positivity)
    rw [hc, mul_assoc, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC0
    have : |y| ≤ |y + w - v| + |w| + |v| := by
      calc |y| = |(y + w - v) - w + v| := by ring_nf
        _ ≤ |(y + w - v) - w| + |v| := abs_add_le _ _
        _ ≤ |y + w - v| + |w| + |v| := by linarith [abs_sub (y + w - v) w]
    linarith
  unfold riemannPairForm
  calc ‖∫ v, ∫ w, g v * conj (g w) * (κ (y + w - v) : ℂ)‖
      ≤ ∫ v, ‖∫ w, g v * conj (g w) * (κ (y + w - v) : ℂ)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ v, ‖g v‖ * (c * ∫ u, ‖g u‖) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
          (hgi.mul_const _) (Eventually.of_forall fun v => ?_)
        calc ‖∫ w, g v * conj (g w) * (κ (y + w - v) : ℂ)‖
            ≤ ∫ w, ‖g v * conj (g w) * (κ (y + w - v) : ℂ)‖ := norm_integral_le_integral_norm _
          _ ≤ ∫ w, ‖g v‖ * ‖g w‖ * c := integral_mono_of_nonneg
              (Eventually.of_forall fun _ => norm_nonneg _)
              ((hgi.const_mul ‖g v‖).mul_const c) (Eventually.of_forall fun w => hpt v w)
          _ = ‖g v‖ * (c * ∫ u, ‖g u‖) := by
              rw [integral_mul_const, integral_const_mul]; ring
    _ = c * (∫ u, ‖g u‖) ^ 2 := by rw [integral_mul_const]; ring


/-- `riemannPairForm K_L g y → riemannPairForm K g y`. -/
theorem tendsto_riemannPairForm_truncated {g : ℝ → ℂ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (y : ℝ) :
    Tendsto (fun L => riemannPairForm (truncatedRiemannAutocorr L) g y) atTop
      (𝓝 (riemannPairForm riemannAutocorr g y)) := by
  obtain ⟨C, hC0, hC⟩ := exists_truncatedRiemannAutocorr_le
  have hKb : ∀ L z, ‖((truncatedRiemannAutocorr L z : ℝ) : ℂ)‖ ≤ C := by
    intro L z
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (truncatedRiemannAutocorr_nonneg L z)]
    refine (hC L z).trans ?_
    have := Real.exp_le_one_iff.mpr (by nlinarith [abs_nonneg z] : -(2 * |z|) ≤ 0)
    nlinarith
  have hgi : Integrable fun u => ‖g u‖ := (hg.norm.integrable_of_hasCompactSupport hgc.norm)
  unfold riemannPairForm
  refine tendsto_integral_filter_of_dominated_convergence (fun v => ‖g v‖ * (C * ∫ u, ‖g u‖))
    (Eventually.of_forall fun L => ?_) (Eventually.of_forall fun L => Eventually.of_forall
      fun v => ?_) (hgi.mul_const _) (Eventually.of_forall fun v => ?_)
  · refine (StronglyMeasurable.integral_prod_right (f := fun v w =>
      g v * conj (g w) * ((truncatedRiemannAutocorr L (y + w - v) : ℝ) : ℂ)) ?_).aestronglyMeasurable
    refine Continuous.stronglyMeasurable ?_
    exact ((hg.comp continuous_fst).mul (hg.comp continuous_snd).star).mul
      (Complex.continuous_ofReal.comp ((truncatedRiemannAutocorr_continuous L).comp
        ((continuous_const.add continuous_snd).sub continuous_fst)))
  · calc ‖∫ w, g v * conj (g w) * ((truncatedRiemannAutocorr L (y + w - v) : ℝ) : ℂ)‖
        ≤ ∫ w, ‖g v‖ * ‖g w‖ * C := by
          refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
            (Eventually.of_forall fun _ => norm_nonneg _) ((hgi.const_mul _).mul_const _)
            (Eventually.of_forall fun w => ?_))
          simp only
          rw [norm_mul, norm_mul, RCLike.norm_conj]
          exact mul_le_mul_of_nonneg_left (hKb _ _) (by positivity)
      _ = ‖g v‖ * (C * ∫ u, ‖g u‖) := by rw [integral_mul_const, integral_const_mul]; ring
  · refine tendsto_integral_filter_of_dominated_convergence (fun w => ‖g v‖ * ‖g w‖ * C)
      (Eventually.of_forall fun L => ?_) (Eventually.of_forall fun L => Eventually.of_forall
        fun w => ?_) ((hgi.const_mul _).mul_const _) (Eventually.of_forall fun w => ?_)
    · exact (continuous_const.mul (hg.star)).mul (Complex.continuous_ofReal.comp
        ((truncatedRiemannAutocorr_continuous L).comp ((continuous_const.add continuous_id).sub
          continuous_const))) |>.aestronglyMeasurable
    · rw [norm_mul, norm_mul, RCLike.norm_conj]
      exact mul_le_mul_of_nonneg_left (hKb _ _) (by positivity)
    · exact tendsto_const_nhds.mul ((Complex.continuous_ofReal.tendsto _).comp
        (tendsto_truncatedRiemannAutocorr_atTop (y + w - v)))

theorem summable_four_div_succ_sq : Summable fun n : ℕ => (4 : ℝ) / ((n : ℝ) + 1) ^ 2 := by
  have h := (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
  have h2 := (summable_nat_add_iff 1).mpr h
  refine (h2.mul_left 4).congr fun n => ?_
  push_cast; ring

theorem exp_neg_two_abs_log_le (n : ℕ) :
    Real.exp (-(2 * |Real.log n|)) ≤ 4 / ((n : ℝ) + 1) ^ 2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · norm_num
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hl : 0 ≤ Real.log n := Real.log_nonneg hn1
    have h1 : 0 < (n : ℝ) := by linarith
    rw [abs_of_nonneg hl, show -(2 * Real.log n) = Real.log (((n : ℝ) * n)⁻¹) by
      rw [Real.log_inv, Real.log_mul h1.ne' h1.ne']; ring, Real.exp_log (by positivity)]
    rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith

/-- **Near-null positivity for compactly supported convolution tests.** -/
theorem normDeficit_pairing_nonneg {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {A : ℝ}
    (hA : ∀ n, |normDeficit lam n| ≤ A) {g : ℝ → ℂ} (hg : Continuous g)
    (hgc : HasCompactSupport g) :
    0 ≤ (∑' n : ℕ, ((normDeficit lam n : ℝ) : ℂ) *
      (riemannPairForm riemannAutocorr g (Real.log n) + riemannPairForm riemannAutocorr g (-Real.log n))).re := by
  obtain ⟨Λ, -, hΛ⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
  obtain ⟨R, hR0, hR⟩ := exists_radius_vanishing_complex hgc
  obtain ⟨C, hC0, hC⟩ := exists_truncatedRiemannAutocorr_le
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0)
  set B := C * Real.exp (4 * R) * (∫ u, ‖g u‖) ^ 2 with hB
  have hB0 : 0 ≤ B := by positivity
  have hκ : ∀ L z, |truncatedRiemannAutocorr L z| ≤ C * Real.exp (-(2 * |z|)) := fun L z => by
    rw [abs_of_nonneg (truncatedRiemannAutocorr_nonneg L z)]; exact hC L z
  have hbd : ∀ L (n : ℕ), ‖((normDeficit lam n : ℝ) : ℂ) *
      (riemannPairForm (truncatedRiemannAutocorr L) g (Real.log n) +
        riemannPairForm (truncatedRiemannAutocorr L) g (-Real.log n))‖ ≤
      A * (2 * B * (4 / ((n : ℝ) + 1) ^ 2)) := by
    intro L n
    have h1 := norm_riemannPairForm_le hC0 (hκ L) hg hgc hR (Real.log n)
    have h2 := norm_riemannPairForm_le hC0 (hκ L) hg hgc hR (-Real.log n)
    rw [abs_neg] at h2
    have he := exp_neg_two_abs_log_le n
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    refine mul_le_mul (hA n) ((norm_add_le _ _).trans ?_) (norm_nonneg _) hA0
    have : C * Real.exp (4 * R) * Real.exp (-(2 * |Real.log n|)) * (∫ u, ‖g u‖) ^ 2 =
        B * Real.exp (-(2 * |Real.log n|)) := by rw [hB]; ring
    rw [this] at h1 h2
    nlinarith [mul_le_mul_of_nonneg_left he hB0]
  have hlim : Tendsto (fun L => ∑' n : ℕ, ((normDeficit lam n : ℝ) : ℂ) *
      (riemannPairForm (truncatedRiemannAutocorr L) g (Real.log n) +
        riemannPairForm (truncatedRiemannAutocorr L) g (-Real.log n))) atTop
      (𝓝 (∑' n : ℕ, ((normDeficit lam n : ℝ) : ℂ) *
        (riemannPairForm riemannAutocorr g (Real.log n) + riemannPairForm riemannAutocorr g (-Real.log n)))) :=
    tendsto_tsum_of_dominated_convergence ((summable_four_div_succ_sq.mul_left (2 * B)).mul_left A)
      (fun n => tendsto_const_nhds.mul ((tendsto_riemannPairForm_truncated hg hgc _).add
        (tendsto_riemannPairForm_truncated hg hgc _)))
      (Eventually.of_forall fun L n => hbd L n)
  have hre := (Complex.continuous_re.tendsto _).comp hlim
  set M2 := (∫ u, ‖g u‖ * Real.exp (1 / 2 * |u|)) ^ 2 with hM2
  have hM0 : 0 ≤ M2 := sq_nonneg _
  have key : ∀ ε > 0, -(M2 * ε) ≤ (∑' n : ℕ, ((normDeficit lam n : ℝ) : ℂ) *
      (riemannPairForm riemannAutocorr g (Real.log n) + riemannPairForm riemannAutocorr g (-Real.log n))).re := by
    intro ε hε
    obtain ⟨L₀, hL₀⟩ := exists_nearRadicalEnergy_le hε
    refine ge_of_tendsto hre ?_
    filter_upwards [eventually_ge_atTop L₀] with L hL
    have h1 := normDeficit_pairing_ge_of_truncation hW L hg hgc hΛ
    have h2 := mul_le_mul_of_nonneg_left (hL₀ L hL) hM0
    simp only [Function.comp]
    rw [← hM2] at h1
    linarith
  by_contra hneg
  push Not at hneg
  set x := (∑' n : ℕ, ((normDeficit lam n : ℝ) : ℂ) *
      (riemannPairForm riemannAutocorr g (Real.log n) + riemannPairForm riemannAutocorr g (-Real.log n))).re
  have hε : 0 < -x / (2 * (M2 + 1)) := div_pos (by linarith) (by positivity)
  have h := key _ hε
  have e : M2 * (-x / (2 * (M2 + 1))) = -x * (M2 / (2 * (M2 + 1))) := by ring
  have hq : M2 / (2 * (M2 + 1)) < 1 := by
    rw [div_lt_one (by positivity)]; linarith
  rw [e] at h
  nlinarith


/-! ## Extension to rapidly decaying tests -/

theorem integrable_inv_one_add_abs_sq : Integrable fun x : ℝ => ((1 + |x|) ^ 2)⁻¹ := by
  have h := integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by simp)
  refine h.congr (Eventually.of_forall fun x => ?_)
  simp only [Real.norm_eq_abs]
  rw [Real.rpow_neg (by positivity), show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- `(1 + |y|) ≤ (1 + |v|)(1 + |w|)(1 + |y + w − v|)`. -/
theorem one_add_abs_le_mul_three (y v w : ℝ) :
    1 + |y| ≤ (1 + |v|) * (1 + |w|) * (1 + |y + w - v|) := by
  have h : |y| ≤ |y + w - v| + |w| + |v| := by
    calc |y| = |(y + w - v) - w + v| := by ring_nf
      _ ≤ |(y + w - v) - w| + |v| := abs_add_le _ _
      _ ≤ |y + w - v| + |w| + |v| := by linarith [abs_sub (y + w - v) w]
  have h1 := abs_nonneg v; have h2 := abs_nonneg w; have h3 := abs_nonneg (y + w - v)
  nlinarith [mul_nonneg h1 h2, mul_nonneg (mul_nonneg h1 h2) h3, mul_nonneg h1 h3, mul_nonneg h2 h3]

/-- `K(z)(1 + |z|)^k` is bounded. -/
theorem exists_riemannAutocorr_mul_pow_le (k : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z, riemannAutocorr z * (1 + |z|) ^ k ≤ B := by
  obtain ⟨C, hC0, hC⟩ := exists_riemannAutocorr_le_exp
  refine ⟨C * k.factorial * Real.exp 1, by positivity, fun z => ?_⟩
  have hK0 : 0 ≤ riemannAutocorr z := riemannAutocorr_nonneg z
  have hp : (1 + |z|) ^ k ≤ k.factorial * Real.exp (1 + |z|) := by
    have := Real.pow_div_factorial_le_exp (1 + |z|) (by positivity) k
    rw [div_le_iff₀ (by positivity)] at this; linarith
  calc riemannAutocorr z * (1 + |z|) ^ k ≤ C * Real.exp (-(2 * |z|)) *
        (k.factorial * Real.exp (1 + |z|)) :=
        mul_le_mul (hC z) hp (by positivity) (by positivity)
    _ = C * k.factorial * Real.exp 1 * Real.exp (-|z|) := by
        rw [show C * Real.exp (-(2 * |z|)) * (k.factorial * Real.exp (1 + |z|)) =
          C * k.factorial * (Real.exp (-(2 * |z|)) * Real.exp (1 + |z|)) by ring, ← Real.exp_add,
          show -(2 * |z|) + (1 + |z|) = 1 + -|z| by ring, Real.exp_add]; ring
    _ ≤ C * k.factorial * Real.exp 1 * 1 := by
        gcongr; exact Real.exp_le_one_iff.mpr (by linarith [abs_nonneg z])
    _ = _ := mul_one _

/-- The decay of the pairing of a rapidly decaying test. -/
theorem norm_riemannPairForm_le_of_decay {k : ℕ} {B : ℝ} (hB : ∀ z, riemannAutocorr z * (1 + |z|) ^ k ≤ B)
    {h : ℝ → ℂ} {D : ℝ} (hD : ∀ x, ‖h x‖ ≤ D * ((1 + |x|) ^ (k + 2))⁻¹)
    (y : ℝ) :
    ‖riemannPairForm riemannAutocorr h y‖ ≤
      D ^ 2 * B * (∫ x : ℝ, ((1 + |x|) ^ 2)⁻¹) ^ 2 * ((1 + |y|) ^ k)⁻¹ := by
  have hD0 : 0 ≤ D := by
    have := (norm_nonneg _).trans (hD 0); simp at this; exact this
  have hI := integrable_inv_one_add_abs_sq
  set I := ∫ x : ℝ, ((1 + |x|) ^ 2)⁻¹ with hIdef
  have hyk : 0 < (1 + |y|) ^ k := by positivity
  have hpt : ∀ v w, ‖h v * conj (h w) * ((riemannAutocorr (y + w - v) : ℝ) : ℂ)‖ ≤
      (D * ((1 + |v|) ^ 2)⁻¹) * (D * ((1 + |w|) ^ 2)⁻¹) * (B * ((1 + |y|) ^ k)⁻¹) := by
    intro v w
    rw [norm_mul, norm_mul, RCLike.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (riemannAutocorr_nonneg _)]
    set z := y + w - v
    have hv := hD v; have hw := hD w
    have hK := hB z
    have hK0 := riemannAutocorr_nonneg z
    have hmul := one_add_abs_le_mul_three y v w
    have hmk : (1 + |y|) ^ k ≤ (1 + |v|) ^ k * (1 + |w|) ^ k * (1 + |z|) ^ k := by
      rw [← mul_pow, ← mul_pow]; exact pow_le_pow_left₀ (by positivity) hmul k
    -- ‖h v‖ ‖h w‖ K(z) ≤ D(1+|v|)^{-(k+2)} D (1+|w|)^{-(k+2)} K(z)
    have hvk : 0 < (1 + |v|) := by positivity
    have hwk : 0 < (1 + |w|) := by positivity
    have hzk : 0 < (1 + |z|) := by positivity
    have e1 : D * ((1 + |v|) ^ (k + 2))⁻¹ = D * ((1 + |v|) ^ 2)⁻¹ * ((1 + |v|) ^ k)⁻¹ := by
      rw [pow_add, mul_inv]; ring
    have e2 : D * ((1 + |w|) ^ (k + 2))⁻¹ = D * ((1 + |w|) ^ 2)⁻¹ * ((1 + |w|) ^ k)⁻¹ := by
      rw [pow_add, mul_inv]; ring
    rw [e1] at hv; rw [e2] at hw
    have hKz : riemannAutocorr z ≤ B * ((1 + |z|) ^ k)⁻¹ := by
      rw [le_mul_inv_iff₀ (by positivity)]; exact hK
    calc ‖h v‖ * ‖h w‖ * riemannAutocorr z
        ≤ (D * ((1 + |v|) ^ 2)⁻¹ * ((1 + |v|) ^ k)⁻¹) * (D * ((1 + |w|) ^ 2)⁻¹ *
            ((1 + |w|) ^ k)⁻¹) * (B * ((1 + |z|) ^ k)⁻¹) := by
          gcongr
      _ = (D * ((1 + |v|) ^ 2)⁻¹) * (D * ((1 + |w|) ^ 2)⁻¹) *
            (B * ((1 + |v|) ^ k * (1 + |w|) ^ k * (1 + |z|) ^ k)⁻¹) := by
          rw [mul_inv, mul_inv]; ring
      _ ≤ _ := by
          gcongr
          · have : 0 ≤ B := le_trans (mul_nonneg hK0 (by positivity)) hK
            exact this
  unfold riemannPairForm
  have hIv : Integrable fun v : ℝ => D * ((1 + |v|) ^ 2)⁻¹ := hI.const_mul D
  calc ‖∫ v, ∫ w, h v * conj (h w) * ((riemannAutocorr (y + w - v) : ℝ) : ℂ)‖
      ≤ ∫ v, (D * ((1 + |v|) ^ 2)⁻¹) * ((D * I) * (B * ((1 + |y|) ^ k)⁻¹)) := by
        refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
          (Eventually.of_forall fun _ => norm_nonneg _) (hIv.mul_const _)
          (Eventually.of_forall fun v => ?_))
        refine (norm_integral_le_integral_norm _).trans ?_
        calc ∫ w, ‖h v * conj (h w) * ((riemannAutocorr (y + w - v) : ℝ) : ℂ)‖
            ≤ ∫ w, (D * ((1 + |v|) ^ 2)⁻¹) * (D * ((1 + |w|) ^ 2)⁻¹) *
                (B * ((1 + |y|) ^ k)⁻¹) :=
              integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
                (((hI.const_mul D).const_mul _).mul_const _) (Eventually.of_forall fun w => hpt v w)
          _ = _ := by rw [integral_mul_const, integral_const_mul, integral_const_mul]; ring
    _ = D ^ 2 * B * I ^ 2 * ((1 + |y|) ^ k)⁻¹ := by
        rw [integral_mul_const, integral_const_mul]; ring


/-- The piecewise-linear cutoff `max 0 (min 1 (M + 1 − |x|))`. -/
def linearCutoff (M x : ℝ) : ℝ := max 0 (min 1 (M + 1 - |x|))

theorem continuous_linearCutoff (M : ℝ) : Continuous (linearCutoff M) := by
  unfold linearCutoff; fun_prop

theorem linearCutoff_nonneg (M x : ℝ) : 0 ≤ linearCutoff M x := le_max_left _ _

theorem linearCutoff_le_one (M x : ℝ) : linearCutoff M x ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem linearCutoff_eq_one {M x : ℝ} (h : |x| ≤ M) : linearCutoff M x = 1 := by
  unfold linearCutoff; rw [min_eq_left (by linarith), max_eq_right zero_le_one]

theorem linearCutoff_eq_zero {M x : ℝ} (h : M + 1 ≤ |x|) : linearCutoff M x = 0 := by
  unfold linearCutoff; rw [max_eq_left (min_le_of_right_le (by linarith))]

/-- The truncation `χ_M g`. -/
def cutoffTest (M : ℝ) (g : ℝ → ℂ) (x : ℝ) : ℂ := (linearCutoff M x : ℂ) * g x

theorem continuous_cutoffTest (M : ℝ) {g : ℝ → ℂ} (hg : Continuous g) :
    Continuous (cutoffTest M g) :=
  (Complex.continuous_ofReal.comp (continuous_linearCutoff M)).mul hg

theorem hasCompactSupport_cutoffTest (M : ℝ) (g : ℝ → ℂ) :
    HasCompactSupport (cutoffTest M g) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -(|M| + 1)) (b := |M| + 1)) fun x hx => ?_
  have hx' : |M| + 1 < |x| := by
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
    rcases hx with h | h
    · rw [abs_of_neg (show x < 0 by linarith [abs_nonneg M])]; linarith
    · rw [abs_of_pos (show 0 < x by linarith [abs_nonneg M])]; linarith
  unfold cutoffTest
  rw [linearCutoff_eq_zero (by linarith [le_abs_self M]), Complex.ofReal_zero, zero_mul]

theorem norm_cutoffTest_le (M : ℝ) (g : ℝ → ℂ) (x : ℝ) : ‖cutoffTest M g x‖ ≤ ‖g x‖ := by
  unfold cutoffTest
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (linearCutoff_nonneg M x)]
  exact mul_le_of_le_one_left (norm_nonneg _) (linearCutoff_le_one M x)

theorem tendsto_cutoffTest (g : ℝ → ℂ) (x : ℝ) :
    Tendsto (fun M => cutoffTest M g x) atTop (𝓝 (g x)) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop |x|] with M hM
  unfold cutoffTest; rw [linearCutoff_eq_one hM, Complex.ofReal_one, one_mul]

/-- `riemannPairForm K (χ_M g) y → riemannPairForm K g y`. -/
theorem tendsto_riemannPairForm_cutoff {g : ℝ → ℂ} (hg : Continuous g) (hgi : Integrable fun x => ‖g x‖)
    (y : ℝ) :
    Tendsto (fun M => riemannPairForm riemannAutocorr (cutoffTest M g) y) atTop
      (𝓝 (riemannPairForm riemannAutocorr g y)) := by
  obtain ⟨C, hC0, hC⟩ := exists_riemannAutocorr_le_exp
  have hKb : ∀ z, ‖((riemannAutocorr z : ℝ) : ℂ)‖ ≤ C := by
    intro z
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (riemannAutocorr_nonneg z)]
    refine (hC z).trans ?_
    have := Real.exp_le_one_iff.mpr (by nlinarith [abs_nonneg z] : -(2 * |z|) ≤ 0)
    nlinarith
  have hKc := riemannAutocorr_continuous
  unfold riemannPairForm
  refine tendsto_integral_filter_of_dominated_convergence (fun v => ‖g v‖ * (C * ∫ u, ‖g u‖))
    (Eventually.of_forall fun M => ?_) (Eventually.of_forall fun M => Eventually.of_forall
      fun v => ?_) (hgi.mul_const _) (Eventually.of_forall fun v => ?_)
  · have hgM := continuous_cutoffTest M hg
    refine (StronglyMeasurable.integral_prod_right (f := fun v w =>
      cutoffTest M g v * conj (cutoffTest M g w) * ((riemannAutocorr (y + w - v) : ℝ) : ℂ))
      ?_).aestronglyMeasurable
    refine Continuous.stronglyMeasurable ?_
    exact ((hgM.comp continuous_fst).mul (hgM.comp continuous_snd).star).mul
      (Complex.continuous_ofReal.comp (hKc.comp
        ((continuous_const.add continuous_snd).sub continuous_fst)))
  · calc ‖∫ w, cutoffTest M g v * conj (cutoffTest M g w) * ((riemannAutocorr (y + w - v) : ℝ) : ℂ)‖
        ≤ ∫ w, ‖g v‖ * ‖g w‖ * C := by
          refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
            (Eventually.of_forall fun _ => norm_nonneg _) ((hgi.const_mul _).mul_const _)
            (Eventually.of_forall fun w => ?_))
          simp only
          rw [norm_mul, norm_mul, RCLike.norm_conj]
          exact mul_le_mul (mul_le_mul (norm_cutoffTest_le M g v) (norm_cutoffTest_le M g w)
            (norm_nonneg _) (norm_nonneg _)) (hKb _) (norm_nonneg _) (by positivity)
      _ = ‖g v‖ * (C * ∫ u, ‖g u‖) := by rw [integral_mul_const, integral_const_mul]; ring
  · refine tendsto_integral_filter_of_dominated_convergence (fun w => ‖g v‖ * ‖g w‖ * C)
      (Eventually.of_forall fun M => ?_) (Eventually.of_forall fun M => Eventually.of_forall
        fun w => ?_) ((hgi.const_mul _).mul_const _) (Eventually.of_forall fun w => ?_)
    · exact (continuous_const.mul ((continuous_cutoffTest M hg).star)).mul
        (Complex.continuous_ofReal.comp (hKc.comp ((continuous_const.add continuous_id).sub
          continuous_const))) |>.aestronglyMeasurable
    · rw [norm_mul, norm_mul, RCLike.norm_conj]
      exact mul_le_mul (mul_le_mul (norm_cutoffTest_le M g v) (norm_cutoffTest_le M g w)
        (norm_nonneg _) (norm_nonneg _)) (hKb _) (norm_nonneg _) (by positivity)
    · exact ((tendsto_cutoffTest g v).mul ((continuous_star.tendsto _).comp
        (tendsto_cutoffTest g w))).mul tendsto_const_nhds

/-- **Near-null positivity for rapidly decaying tests.** If the deviation is bounded and
`Σ |v(n)| (1 + |log n|)^{−k} < ∞`, then the pairing with `K ⋆ (g ⋆ g̃)` is nonnegative for every
continuous `g` with `‖g(x)‖ ≤ D(1 + |x|)^{−(k+2)}`. -/
theorem normDeficit_pairing_nonneg_of_decay {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {A : ℝ}
    (hA : ∀ n, |normDeficit lam n| ≤ A) {k : ℕ}
    (hZ : Summable fun n : ℕ => |normDeficit lam n| * ((1 + |Real.log n|) ^ k)⁻¹)
    {g : ℝ → ℂ} (hg : Continuous g) {D : ℝ} (hD : ∀ x, ‖g x‖ ≤ D * ((1 + |x|) ^ (k + 2))⁻¹) :
    0 ≤ (∑' n : ℕ, ((normDeficit lam n : ℝ) : ℂ) *
      (riemannPairForm riemannAutocorr g (Real.log n) + riemannPairForm riemannAutocorr g (-Real.log n))).re := by
  obtain ⟨B, hB0, hB⟩ := exists_riemannAutocorr_mul_pow_le k
  have hD0 : 0 ≤ D := by
    have := (norm_nonneg _).trans (hD 0); simp at this; exact this
  have hgi : Integrable fun x => ‖g x‖ := by
    refine (integrable_inv_one_add_abs_sq.const_mul D).mono' hg.norm.aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    refine (hD x).trans (mul_le_mul_of_nonneg_left ?_ hD0)
    have h1 : (1 : ℝ) ≤ 1 + |x| := by linarith [abs_nonneg x]
    exact inv_anti₀ (by positivity) (pow_le_pow_right₀ h1 (by omega))
  set c := D ^ 2 * B * (∫ x : ℝ, ((1 + |x|) ^ 2)⁻¹) ^ 2 with hc
  have hc0 : 0 ≤ c := by
    have : 0 ≤ ∫ x : ℝ, ((1 + |x|) ^ 2)⁻¹ := integral_nonneg fun _ => by positivity
    positivity
  have hDM : ∀ M x, ‖cutoffTest M g x‖ ≤ D * ((1 + |x|) ^ (k + 2))⁻¹ := fun M x =>
    (norm_cutoffTest_le M g x).trans (hD x)
  have hbd : ∀ M (n : ℕ), ‖((normDeficit lam n : ℝ) : ℂ) *
      (riemannPairForm riemannAutocorr (cutoffTest M g) (Real.log n) +
        riemannPairForm riemannAutocorr (cutoffTest M g) (-Real.log n))‖ ≤
      2 * c * (|normDeficit lam n| * ((1 + |Real.log n|) ^ k)⁻¹) := by
    intro M n
    have h1 := norm_riemannPairForm_le_of_decay hB (hDM M) (Real.log n)
    have h2 := norm_riemannPairForm_le_of_decay hB (hDM M) (-Real.log n)
    rw [abs_neg] at h2
    rw [← hc] at h1 h2
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h3 := norm_add_le (riemannPairForm riemannAutocorr (cutoffTest M g) (Real.log n))
      (riemannPairForm riemannAutocorr (cutoffTest M g) (-Real.log n))
    have ha := abs_nonneg (normDeficit lam n)
    calc |normDeficit lam n| * ‖riemannPairForm riemannAutocorr (cutoffTest M g) (Real.log n) +
          riemannPairForm riemannAutocorr (cutoffTest M g) (-Real.log n)‖
        ≤ |normDeficit lam n| * (2 * (c * ((1 + |Real.log n|) ^ k)⁻¹)) :=
          mul_le_mul_of_nonneg_left (by linarith) ha
      _ = _ := by ring
  have hlim := tendsto_tsum_of_dominated_convergence (hZ.mul_left (2 * c))
    (fun n => tendsto_const_nhds.mul ((tendsto_riemannPairForm_cutoff hg hgi _).add
      (tendsto_riemannPairForm_cutoff hg hgi _)))
    (Eventually.of_forall fun M n => hbd M n)
  refine ge_of_tendsto ((Complex.continuous_re.tendsto _).comp hlim)
    (Eventually.of_forall fun M => ?_)
  exact normDeficit_pairing_nonneg hW hA (continuous_cutoffTest M hg)
    (hasCompactSupport_cutoffTest M g)

end

end RHTower
