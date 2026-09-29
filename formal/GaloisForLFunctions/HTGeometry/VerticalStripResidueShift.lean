import GaloisForLFunctions.PNTPlus.ResidueCalcOnRectangles
import GaloisForLFunctions.HTGeometry.VerticalStripContourShift
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Shifting a vertical contour past a simple pole

Let `F` be holomorphic at every point of the closed strip `a ≤ Re s ≤ b` except one interior point
`p`, with `(s - p) F(s) → A` as `s → p`, and `‖F(s)‖ ≤ C (1 + (Im s)²)⁻¹` for `|Im s| ≥ T₀` in the
strip.  Then `∫ F(b + it) dt - ∫ F(a + it) dt = 2π A` (`integral_line_sub_integral_line_eq`).

Proof: the residue theorem on the rectangles `[a, b] × [-T, T]` (the pole is removable after
subtracting `A/(s - p)`), then `T → ∞`: the horizontal sides vanish by the decay and the vertical
sides converge to the line integrals.
-/

open Complex Set Filter Topology MeasureTheory Asymptotics

namespace GaloisForLFunctions.HTGeometry

/-- A function continuous along a vertical line and bounded by `C (1+t²)⁻¹` for `|t| ≥ T₀` is
integrable along the line. -/
theorem integrable_line_of_bound {F : ℂ → ℂ} {x T₀ C : ℝ}
    (hF : ∀ t : ℝ, ContinuousAt F (x + t * I))
    (hb : ∀ t : ℝ, T₀ ≤ |t| → ‖F (x + t * I)‖ ≤ C * (1 + t ^ 2)⁻¹) :
    Integrable fun t : ℝ => F (x + t * I) := by
  have hc : Continuous fun t : ℝ => F (x + t * I) :=
    continuous_iff_continuousAt.2 fun t =>
      (hF t).comp (f := fun t : ℝ => (x : ℂ) + t * I) (by fun_prop)
  have h1 : IntegrableOn (fun t : ℝ => F (x + t * I)) (Icc (-T₀) T₀) :=
    hc.continuousOn.integrableOn_compact isCompact_Icc
  have h2 : IntegrableOn (fun t : ℝ => F (x + t * I)) (Icc (-T₀) T₀)ᶜ := by
    refine Integrable.mono' (integrable_inv_one_add_sq.const_mul C).integrableOn
      hc.aestronglyMeasurable.restrict ?_
    refine (ae_restrict_iff' measurableSet_Icc.compl).2 (Eventually.of_forall fun t ht => ?_)
    refine hb t ?_
    rcases not_and_or.1 ht with h | h
    · rw [not_le] at h; exact (by linarith : T₀ ≤ -t).trans (neg_le_abs t)
    · rw [not_le] at h; exact h.le.trans (le_abs_self t)
  have := h1.union h2
  rwa [union_compl_self, integrableOn_univ] at this

/-- Subtracting the polar part leaves a bounded function near a simple pole. -/
theorem isBigO_sub_polar_of_tendsto {F : ℂ → ℂ} {p A : ℂ} {U : Set ℂ} (hU : U ∈ 𝓝 p)
    (hF : ∀ s ∈ U, s ≠ p → DifferentiableAt ℂ F s)
    (hres : Tendsto (fun s => (s - p) * F s) (𝓝[≠] p) (𝓝 A)) :
    (F - fun s => A / (s - p)) =O[𝓝[≠] p] (1 : ℂ → ℂ) := by
  set G : ℂ → ℂ := Function.update (fun s => (s - p) * F s) p A
  have hGU : DifferentiableOn ℂ G U := by
    refine (Complex.differentiableOn_compl_singleton_and_continuousAt_iff hU).1 ⟨fun s hs => ?_, ?_⟩
    · have hsp : s ≠ p := hs.2
      have hd : DifferentiableAt ℂ (fun s => (s - p) * F s) s :=
        (differentiableAt_id.sub_const p).mul (hF s hs.1 hsp)
      refine (hd.congr_of_eventuallyEq ?_).differentiableWithinAt
      filter_upwards [isOpen_compl_singleton.mem_nhds hsp] with u hu
      exact Function.update_of_ne hu _ _
    · exact continuousAt_update_same.2 hres
  have hGp : DifferentiableAt ℂ G p := hGU.differentiableAt hU
  obtain ⟨c, hc⟩ := hGp.isBigO_sub.bound
  refine IsBigO.of_bound c ?_
  filter_upwards [nhdsWithin_le_nhds hc, self_mem_nhdsWithin] with s hs hsp
  have hsp' : s - p ≠ 0 := sub_ne_zero.2 hsp
  have hGs : G s = (s - p) * F s := Function.update_of_ne hsp _ _
  have hGp' : G p = A := Function.update_self _ _ _
  rw [hGs, hGp'] at hs
  have he : (F - fun s => A / (s - p)) s = ((s - p) * F s - A) / (s - p) := by
    simp only [Pi.sub_apply]
    field_simp
  rw [he, norm_div, Pi.one_apply, norm_one, mul_one, div_le_iff₀ (norm_pos_iff.2 hsp')]
  exact hs

/-- **Contour shift past a simple pole.** -/
theorem integral_line_sub_integral_line_eq {F : ℂ → ℂ} {a b : ℝ} {p A : ℂ} (hap : a < p.re)
    (hpb : p.re < b) (hF : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → s ≠ p → DifferentiableAt ℂ F s)
    (hres : Tendsto (fun s => (s - p) * F s) (𝓝[≠] p) (𝓝 A)) {T₀ C : ℝ}
    (hb : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → T₀ ≤ |s.im| → ‖F s‖ ≤ C * (1 + s.im ^ 2)⁻¹) :
    (∫ t : ℝ, F (b + t * I)) - ∫ t : ℝ, F (a + t * I) = 2 * Real.pi * A := by
  have hab : a ≤ b := (hap.trans hpb).le
  have hline : ∀ x : ℝ, a ≤ x → x ≤ b → x ≠ p.re → Integrable fun t : ℝ => F (x + t * I) := by
    intro x hax hxb hxp
    refine integrable_line_of_bound (T₀ := T₀) (C := C) (fun t => ?_) (fun t ht => ?_)
    · refine (hF _ (by simpa using hax) (by simpa using hxb) fun h => hxp ?_).continuousAt
      rw [← h]; simp
    · simpa using hb (x + t * I) (by simpa using hax) (by simpa using hxb) (by simpa using ht)
  have hIa := hline a le_rfl hab hap.ne
  have hIb := hline b hab le_rfl hpb.ne'
  -- the rectangle identity for large `T`
  have hrect : ∀ᶠ T : ℝ in atTop,
      ((∫ x : ℝ in a..b, F (x + ((-T : ℝ) : ℂ) * I)) - (∫ x : ℝ in a..b, F (x + (T : ℂ) * I)) +
        I • (∫ y : ℝ in (-T)..T, F (b + y * I))) - I • (∫ y : ℝ in (-T)..T, F (a + y * I)) =
        2 * Real.pi * I * A := by
    filter_upwards [eventually_gt_atTop |p.im|] with T hT
    have hT0 : 0 ≤ T := (abs_nonneg _).trans hT.le
    set z : ℂ := (a : ℂ) + ((-T : ℝ) : ℂ) * I
    set w : ℂ := (b : ℂ) + (T : ℂ) * I
    have hzre : z.re = a := by simp [z]
    have hzim : z.im = -T := by simp [z]
    have hwre : w.re = b := by simp [w]
    have hwim : w.im = T := by simp [w]
    have hpin : Rectangle z w ∈ 𝓝 p := by
      rw [rectangle_mem_nhds_iff, hzre, hzim, hwre, hwim, uIoo_of_le hab,
        uIoo_of_le (by linarith)]
      exact ⟨⟨hap, hpb⟩, ⟨by linarith [neg_abs_le p.im], by linarith [le_abs_self p.im]⟩⟩
    have hsub : ∀ s ∈ Rectangle z w, a ≤ s.re ∧ s.re ≤ b := by
      intro s hs
      rw [Rectangle, mem_reProdIm, hzre, hwre, uIcc_of_le hab] at hs
      exact hs.1
    have hholo : HolomorphicOn F (Rectangle z w \ {p}) := fun s hs =>
      (hF s (hsub s hs.1).1 (hsub s hs.1).2 hs.2).differentiableWithinAt
    have hnear := isBigO_sub_polar_of_tendsto hpin (fun s hs hsp => hF s (hsub s hs).1 (hsub s hs).2 hsp)
      hres
    have hres' := ResidueTheoremOnRectangleWithSimplePole' (by rw [hzre, hwre]; exact hab)
      (by rw [hzim, hwim]; linarith) hpin hholo hnear
    rw [RectangleIntegral', RectangleIntegral, HIntegral, HIntegral, VIntegral, VIntegral,
      hzre, hzim, hwre, hwim] at hres'
    have h2πI : (2 * Real.pi * I : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, I_ne_zero]
    rw [smul_eq_mul, one_div, inv_mul_eq_iff_eq_mul₀ h2πI] at hres'
    rw [hres']
  -- limits of the four sides
  have hdec : Tendsto (fun T : ℝ => C * (1 + T ^ 2)⁻¹) atTop (𝓝 0) := by
    have : Tendsto (fun T : ℝ => 1 + T ^ 2) atTop atTop :=
      tendsto_atTop_add_const_left _ _ (tendsto_pow_atTop two_ne_zero)
    simpa using this.inv_tendsto_atTop.const_mul C
  have hbot : Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, F (x + ((-T : ℝ) : ℂ) * I)) atTop (𝓝 0) := by
    refine tendsto_intervalIntegral_of_tendsto_bound (hgt := fun T => -T) ?_ hdec
    filter_upwards [eventually_ge_atTop T₀] with T hT u hu
    rw [uIoc_of_le hab] at hu
    have h := hb ((u : ℂ) + ((-T : ℝ) : ℂ) * I) (by simpa using hu.1.le) (by simpa using hu.2)
      (by rw [show ((u : ℂ) + ((-T : ℝ) : ℂ) * I).im = -T by simp, abs_neg]
          exact hT.trans (le_abs_self T))
    simpa using h
  have htop : Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, F (x + (T : ℂ) * I)) atTop (𝓝 0) := by
    refine tendsto_intervalIntegral_of_tendsto_bound (hgt := fun T => T) ?_ hdec
    filter_upwards [eventually_ge_atTop T₀] with T hT u hu
    rw [uIoc_of_le hab] at hu
    have h := hb (u + (T : ℂ) * I) (by simpa using hu.1.le) (by simpa using hu.2)
      (by simpa using hT.trans (le_abs_self T))
    simpa using h
  have hlimb := intervalIntegral_tendsto_integral hIb tendsto_neg_atTop_atBot tendsto_id
  have hlima := intervalIntegral_tendsto_integral hIa tendsto_neg_atTop_atBot tendsto_id
  have hcomb := ((hbot.sub htop).add (hlimb.const_smul I)).sub (hlima.const_smul I)
  have heq := tendsto_nhds_unique hcomb (tendsto_const_nhds.congr' (hrect.mono fun T hT => hT.symm))
  have hI : I * ((∫ t : ℝ, F (b + t * I)) - ∫ t : ℝ, F (a + t * I)) = I * (2 * Real.pi * A) := by
    rw [mul_sub]
    simp only [smul_eq_mul, sub_zero, zero_add] at heq
    linear_combination heq
  exact mul_left_cancel₀ I_ne_zero hI

end GaloisForLFunctions.HTGeometry
