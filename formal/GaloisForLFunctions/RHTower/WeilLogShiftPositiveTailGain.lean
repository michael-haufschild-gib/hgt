import GaloisForLFunctions.RHTower.WeilLogShiftTailComparison

/-!
# Uniform tail gain for every positive inward shift

The smooth transition stays uniformly positive a fixed distance inside its
support. A central interval scaled to the shift therefore removes the former
restriction that the shift be at least four.
-/

open MeasureTheory Filter Topology Set Real

noncomputable section

namespace RHTower

/-- A fixed interior margin gives a quantitative cutoff lower bound, including
inside the transition region. -/
theorem bulkCutoff_ge_transition_sq {L u d : ℝ} (hu : |u| ≤ L - d) :
    smoothTransition d ^ 2 ≤ bulkCutoff L u := by
  have hleft : d ≤ L - u := by linarith only [hu, le_abs_self u]
  have hright : d ≤ L + u := by linarith only [hu, neg_le_abs u]
  simpa only [pow_two, bulkCutoff] using
    mul_le_mul (smoothTransition.monotone hleft) (smoothTransition.monotone hright)
      (smoothTransition.nonneg d) (smoothTransition.nonneg (L - u))

/-- A central interval with arbitrary positive radius survives any equally
large interior margin; no flat cutoff plateau is needed. -/
theorem truncatedRiemannAutocorr_central_lower_of_margin {L z d : ℝ}
    (hd : 0 < d) (hz : 0 ≤ z) (hL : z / 2 + 2 * d ≤ L) :
    (2 * d * ((2 * π ^ 2) * smoothTransition d ^ 2) ^ 2) *
      exp (-(2 * π * exp (z + 2 * d))) ≤ truncatedRiemannAutocorr L z := by
  let q := (2 * π ^ 2) * smoothTransition d ^ 2
  have hfactor (u : ℝ) (hu : |u| ≤ z / 2 + d) :
      q * exp (-(π * exp (2 * |u|))) ≤ truncatedRiemannKernelReal L u := by
    have hcut := bulkCutoff_ge_transition_sq (L := L) (d := d)
      (show |u| ≤ L - d by linarith only [hu, hL])
    have h := mul_le_mul (ExposingRayTail.phi_lower u) hcut
      (sq_nonneg _) (riemannKernelReal_pos u).le
    change _ ≤ riemannKernelReal u * bulkCutoff L u at h
    change _ ≤ riemannKernelReal u * bulkCutoff L u
    calc q * exp (-(π * exp (2 * |u|))) =
        (2 * π ^ 2 * exp (-(π * exp (2 * |u|)))) * smoothTransition d ^ 2 := by
          dsimp only [q]
          ring
      _ ≤ _ := h
  have hpoint : ∀ t ∈ Ioc (z / 2 - d) (z / 2 + d),
      q ^ 2 * exp (-(2 * π * exp (z + 2 * d))) ≤
        truncatedRiemannKernelReal L t * truncatedRiemannKernelReal L (t - z) := by
    intro t ht
    have ht1 : |t| ≤ z / 2 + d := by
      rw [abs_le]
      constructor <;> linarith only [ht.1, ht.2, hz]
    have ht2 : |t - z| ≤ z / 2 + d := by
      rw [abs_le]
      constructor <;> linarith only [ht.1, ht.2, hz]
    have h1 := exp_le_exp.mpr (show 2 * |t| ≤ z + 2 * d by linarith only [ht1])
    have h2 := exp_le_exp.mpr (show 2 * |t - z| ≤ z + 2 * d by linarith only [ht2])
    have hs : π * (exp (2 * |t|) + exp (2 * |t - z|)) ≤
        2 * π * exp (z + 2 * d) := by
      have h := mul_le_mul_of_nonneg_left (add_le_add h1 h2) pi_pos.le
      nlinarith only [h]
    have heq (U V : ℝ) : (q * exp U) * (q * exp V) = q ^ 2 * exp (U + V) := by
      rw [exp_add]
      ring
    have hprod : q ^ 2 * exp (-(2 * π * exp (z + 2 * d))) ≤
        (q * exp (-(π * exp (2 * |t|)))) * (q * exp (-(π * exp (2 * |t - z|)))) := by
      rw [heq]
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      apply exp_le_exp.mpr
      linarith only [hs]
    exact hprod.trans (mul_le_mul (hfactor t ht1) (hfactor (t - z) ht2)
      (by dsimp only [q]; positivity) (truncatedRiemannKernelReal_nonneg L t))
  have hi := setIntegral_mono_on (integrableOn_const (by simp))
    (integrable_truncatedRiemannKernel_prod L z).integrableOn measurableSet_Ioc hpoint
  have hconst : (∫ t in Ioc (z / 2 - d) (z / 2 + d),
      q ^ 2 * exp (-(2 * π * exp (z + 2 * d)))) =
      (2 * d * q ^ 2) * exp (-(2 * π * exp (z + 2 * d))) := by
    rw [setIntegral_const, Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
    simp only [smul_eq_mul]
    ring
  rw [hconst] at hi
  exact hi.trans (setIntegral_le_integral (integrable_truncatedRiemannKernel_prod L z)
    (Eventually.of_forall fun t => mul_nonneg (truncatedRiemannKernelReal_nonneg L t)
      (truncatedRiemannKernelReal_nonneg L (t - z))))

/-- Every strictly positive inward shift gives any prescribed tail gain,
uniformly over all real cutoffs. -/
theorem exists_truncatedRiemannAutocorr_tail_shift_gain_of_pos {c : ℝ}
    (hc : 0 < c) (A : ℝ) :
    ∃ Y : ℝ, ∀ y : ℝ, Y ≤ y → ∀ L : ℝ,
      A * truncatedRiemannAutocorr L y ≤ truncatedRiemannAutocorr L (y - c) := by
  let d := c / 4
  let B := 2 * π * exp (-c / 2)
  let a := π * (1 + exp (-c / 2)) / 2
  let g := 2 * a - B
  have he : exp (-c / 2) < 1 := exp_lt_one_iff.mpr (by linarith only [hc])
  have ha0 : 0 < a := by dsimp only [a]; positivity
  have haπ : a < π := by
    have h := mul_lt_mul_of_pos_left he pi_pos
    dsimp only [a]
    nlinarith only [h]
  have hg : 0 < g := by
    have h := mul_lt_mul_of_pos_left he pi_pos
    dsimp only [g, a, B]
    nlinarith only [h]
  obtain ⟨C, hC0, hC⟩ := ExposingRayTail.autocorr_upper ha0 haπ
  let D := 2 * d * ((2 * π ^ 2) * smoothTransition d ^ 2) ^ 2
  have hd : 0 < d := by dsimp only [d]; positivity
  have hD : 0 < D := by
    have hs := smoothTransition.pos_of_pos hd
    dsimp only [D]
    positivity
  have hE : Tendsto (fun y : ℝ => exp (-(g * exp y))) atTop (𝓝 0) := by
    simpa only [pow_zero, one_mul, Function.comp_def] using
      (tendsto_pow_mul_exp_neg_atTop_nhds_zero 0).comp
        (tendsto_exp_atTop.const_mul_atTop hg)
  have hlim := hE.const_mul (|A| * C)
  rw [mul_zero] at hlim
  obtain ⟨Y, hY⟩ := eventually_atTop.mp ((tendsto_order.mp hlim).2 D hD)
  refine ⟨max c Y, fun y hy L => ?_⟩
  have hyc : c ≤ y := (le_max_left _ _).trans hy
  have hy0 : 0 ≤ y := hc.le.trans hyc
  by_cases hz : 2 * L ≤ y
  · rw [truncatedRiemannAutocorr_eq_zero (by rwa [abs_of_nonneg hy0]), mul_zero]
    exact truncatedRiemannAutocorr_nonneg _ _
  have hcentral := truncatedRiemannAutocorr_central_lower_of_margin
    (L := L) (z := y - c) hd (by linarith only [hyc])
    (by dsimp only [d]; linarith only [hz])
  have hscale : 2 * π * exp (y - c + 2 * d) = B * exp y := by
    rw [show y - c + 2 * d = y + (-c / 2) by dsimp only [d]; ring, exp_add]
    dsimp only [B]
    ring
  rw [hscale] at hcentral
  let E := exp (-(g * exp y))
  let F := exp (-(B * exp y))
  have hfull : riemannAutocorr y ≤ C * (E * F) := by
    have h := hC y
    change riemannAutocorr y ≤ _ at h
    rw [abs_of_nonneg hy0] at h
    have heq : exp (-(2 * a * exp y)) = E * F := by
      dsimp only [E, F]
      rw [← exp_add]
      congr 1
      dsimp only [g]
      ring
    rwa [heq] at h
  have hsmall : |A| * C * E < D := hY y ((le_max_right _ _).trans hy)
  calc A * truncatedRiemannAutocorr L y ≤ |A| * truncatedRiemannAutocorr L y :=
      mul_le_mul_of_nonneg_right (le_abs_self A) (truncatedRiemannAutocorr_nonneg _ _)
    _ ≤ |A| * riemannAutocorr y :=
      mul_le_mul_of_nonneg_left (truncatedRiemannAutocorr_le_riemannAutocorr L y) (abs_nonneg A)
    _ ≤ |A| * (C * (E * F)) := mul_le_mul_of_nonneg_left hfull (abs_nonneg A)
    _ = (|A| * C * E) * F := by ring
    _ ≤ D * F := mul_le_mul_of_nonneg_right hsmall.le (exp_pos _).le
    _ ≤ truncatedRiemannAutocorr L (y - c) := hcentral

end RHTower
