import GaloisForLFunctions.RHTower.MellinLineMass
import GaloisForLFunctions.RHTower.MellinHeadHardyEquiv
import GaloisForLFunctions.RHTower.HeadTailVector
import GaloisForLFunctions.RHTower.BurnolReflectionStability
import GaloisForLFunctions.RHTower.MellinContinuationOrder

/-!
# A vector of `L_a` has its continued Mellin transform in the head Hardy class

Right of the critical line the continued Mellin transform of a vector of `L_a` *is* the explicit
head/tail expression `d·a^{1-s}/(1-s) + ∫_a^∞ t^{-s} v(t) dt`, so Proposition 4.1 puts it in
`L̂_a = s/(s-1)·A^s H²`.  Its reflection `χ(s)·M(v)(1-s)` is the continued Mellin transform of
`F₊v`, hence in the same class.  This is the "forward" half of Proposition 4.1, in the form the
division theorem needs.

## Main results

* `extendedMellinContinuation_eq_headTailMellin`
* `isMellinHeadHardy_extendedMellinContinuation`
* `chi_mul_extendedMellinContinuation_one_sub`
* `extendedMellinContinuation_headTailVector`
-/

namespace RHTower

open MeasureTheory Set Complex Filter Topology

open GaloisForLFunctions.HTGeometry

noncomputable section

variable {a : ℝ} {v : SoninL2} {c d : ℂ}

/-- Right of the critical line the continued transform is the explicit head/tail expression. -/
theorem extendedMellinContinuation_eq_headTailMellin (ha : 0 < a) (hev : v ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary v : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (v : ℝ → ℂ) t = d)
    {s : ℂ} (hs : 1 / 2 < s.re) (hs1 : s ≠ 1) :
    extendedMellinContinuation a c d v s = headTailMellin a d ((v : ℝ → ℂ)) s := by
  have hs0 : s ≠ 0 := by
    intro h; rw [h] at hs; simp at hs; linarith
  rw [extendedMellinContinuation_eq_right a c d v (le_of_lt hs) hs0 hs1, extendedMellinRight,
    extendedTailMellin_eq ha hc hs, headTailMellin]
  ring

/-- **The continued Mellin transform of a vector of `L_a` lies in `L̂_a`.** -/
theorem isMellinHeadHardy_extendedMellinContinuation (ha : 0 < a) (hev : v ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary v : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (v : ℝ → ℂ) t = d) :
    IsMellinHeadHardy a (extendedMellinContinuation a c d v) := by
  refine (isMellinHeadHardy_iff ha _).2 ⟨d, (v : ℝ → ℂ), (Lp.memLp v).restrict (Ioi a), ?_⟩
  intro s hs hs1
  exact extendedMellinContinuation_eq_headTailMellin ha hev hc hd hs hs1

/-- **The reflected transform.**  `χ(s)·M(v)(1-s)` is the continued Mellin transform of `F₊v`, on
the whole strip `1/2 < Re s < 1` — the real points included. -/
theorem chi_mul_extendedMellinContinuation_one_sub (ha : 0 < a) (hev : v ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary v : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (v : ℝ → ℂ) t = d)
    {s : ℂ} (hs1 : 0 < s.re) (hs2 : s.re < 1) :
    burnolChiFactor s * extendedMellinContinuation a c d v (1 - s)
      = extendedMellinContinuation a d c (fourierUnitary v) s := by
  have hev' : fourierUnitary v ∈ evenSubspace := fourierUnitary_mem_evenSubspace hev
  have hff : fourierUnitary (fourierUnitary v) = v :=
    fourierUnitary_fourierUnitary_of_mem_evenSubspace hev
  have hoff : ∀ w : ℂ, w.im ≠ 0 →
      burnolChiFactor w * extendedMellinContinuation a c d v (1 - w)
        = extendedMellinContinuation a d c (fourierUnitary v) w := fun w hw =>
    (extendedMellinContinuation_reflect_of_im_ne ha hev hc hd hw).symm
  by_cases him : s.im ≠ 0
  · exact hoff s him
  · push Not at him
    -- approach the real point from above
    set u : ℕ → ℂ := fun n => s + (((1 : ℝ) / (n + 1) : ℝ) : ℂ) * I with hu
    have hure : ∀ n, (u n).re = s.re := by
      intro n
      rw [hu]
      simp
    have huim : ∀ n : ℕ, (u n).im ≠ 0 := by
      intro n
      have hval : (u n).im = 1 / ((n : ℝ) + 1) := by
        simp only [hu, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im, him]
        ring
      rw [hval]
      positivity
    have hulim : Tendsto u atTop (𝓝 s) := by
      have h1 : Tendsto (fun n : ℕ => (((1 : ℝ) / ((n : ℝ) + 1) : ℝ) : ℂ) * I) atTop
          (𝓝 ((0 : ℂ) * I)) :=
        (((Complex.continuous_ofReal.tendsto 0).comp
          tendsto_one_div_add_atTop_nhds_zero_nat)).mul tendsto_const_nhds
      have h2 := tendsto_const_nhds (x := s) (f := atTop (α := ℕ)) |>.add h1
      simpa [hu] using h2
    have hs0 : s ≠ 0 := by
      intro h; rw [h] at hs1; simp at hs1
    have hsne1 : s ≠ 1 := by
      intro h; rw [h] at hs2; simp at hs2
    have hL : ContinuousAt
        (fun w : ℂ => burnolChiFactor w * extendedMellinContinuation a c d v (1 - w)) s := by
      have h1 : ContinuousAt burnolChiFactor s :=
        (differentiableAt_burnolChiFactor hs2).continuousAt
      have honesub0 : (1 : ℂ) - s ≠ 0 := sub_ne_zero.2 (Ne.symm hsne1)
      have honesub1 : (1 : ℂ) - s ≠ 1 := by
        intro h
        exact hs0 (by linear_combination -h)
      have h2 : ContinuousAt (fun w : ℂ => extendedMellinContinuation a c d v (1 - w)) s := by
        have ha2 := (analyticAt_extendedMellinContinuation_of_ne ha hev hc hd
          honesub0 honesub1).continuousAt
        have hsub : ContinuousAt (fun w : ℂ => (1 : ℂ) - w) s := by fun_prop
        exact ha2.comp hsub
      exact h1.mul h2
    have hR : ContinuousAt (extendedMellinContinuation a d c (fourierUnitary v)) s := by
      have hcc : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ centralInterval a →
          ((fourierUnitary (fourierUnitary v) : SoninL2) : ℝ → ℂ) x = d := by
        rw [hff]; exact hd
      exact (analyticAt_extendedMellinContinuation_of_ne ha hev' hcc hc hs0 hsne1).continuousAt
    have hLlim := hL.tendsto.comp hulim
    have hRlim := hR.tendsto.comp hulim
    have hLlim' : Tendsto (fun n : ℕ =>
        extendedMellinContinuation a d c (fourierUnitary v) (u n)) atTop
        (𝓝 (burnolChiFactor s * extendedMellinContinuation a c d v (1 - s))) :=
      hLlim.congr (fun n => hoff (u n) (huim n))
    exact tendsto_nhds_unique hLlim' hRlim

/-- The continued transform of the head/tail vector. -/
theorem extendedMellinContinuation_headTailVector (ha : 0 < a) (c₁ : ℂ) {g₁ : ℝ → ℂ}
    (hg₁ : MemLp g₁ 2 (volume.restrict (Ioi a))) {c₂ : ℂ}
    (hband : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ centralInterval a →
      ((fourierUnitary (headTailVector ha c₁ hg₁) : SoninL2) : ℝ → ℂ) x = c₂)
    {s : ℂ} (hs : 1 / 2 < s.re) (hs1 : s ≠ 1) :
    extendedMellinContinuation a c₂ c₁ (headTailVector ha c₁ hg₁) s
      = headTailMellin a c₁ g₁ s := by
  have hev : headTailVector ha c₁ hg₁ ∈ evenSubspace :=
    headTailVector_mem_evenSubspace ha c₁ hg₁
  have hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a →
      ((headTailVector ha c₁ hg₁ : SoninL2) : ℝ → ℂ) t = c₁ :=
    headTailVector_ae_band ha c₁ hg₁
  rw [extendedMellinContinuation_eq_headTailMellin ha hev hband hd hs hs1, headTailMellin,
    headTailMellin]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [headTailVector_ae_tail ha c₁ hg₁] with t ht
  rw [ht]

end

end RHTower
