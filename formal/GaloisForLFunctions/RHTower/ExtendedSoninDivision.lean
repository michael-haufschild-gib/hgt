import GaloisForLFunctions.RHTower.SoninHardyRepresentative
import GaloisForLFunctions.RHTower.SoninFromHardyData

/-!
# Burnol's Proposition 4.3 for `L_a`, at every point of the open critical strip

If the continued Mellin transform of a vector of `L_a` vanishes at a point `ρ` of the open critical
strip, then the quotient by `(s - ρ)` is again the continued Mellin transform of a vector of `L_a`.

The corpus already owned this for `1/2 < Re ρ < 1` (`BurnolSoninDividedShift`).  Here it is proved
for *every* strip point — the critical line included, which is the case that matters for the zeros
of `ζ` — by dividing the *canonical* Hardy representative of `SoninHardyRepresentative` on both
sides of the functional equation and feeding the result to the two-sided converse of
Proposition 4.1.

## Main results

* `exists_divided_extendedSonin`
-/

namespace RHTower

open MeasureTheory Set Complex Filter Topology

open GaloisForLFunctions.HTGeometry

noncomputable section

theorem headTailMellin_neg (a : ℝ) (c : ℂ) (g : ℝ → ℂ) (s : ℂ) :
    headTailMellin a (-c) (fun t : ℝ => -g t) s = -headTailMellin a c g s := by
  rw [headTailMellin, headTailMellin]
  have hint : (∫ t in Ioi a, ((t : ℝ) : ℂ) ^ (-s) * -g t)
      = -∫ t in Ioi a, ((t : ℝ) : ℂ) ^ (-s) * g t := by
    rw [← MeasureTheory.integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    ring
  rw [hint]
  ring

/-- **Proposition 4.3 for `L_a`, at every point of the open critical strip.** -/
theorem exists_divided_extendedSonin {a : ℝ} (ha : 0 < a) {v : SoninL2} {c d : ℂ}
    (hev : v ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary v : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (v : ℝ → ℂ) t = d)
    {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (hvan : extendedMellinContinuation a c d v ρ = 0) :
    ∃ (w : SoninL2) (c' d' : ℂ), w ∈ evenSubspace ∧ w ∈ centralSoninExtendedCarrier a ∧
      (∀ᵐ x ∂(volume : Measure ℝ), x ∈ centralInterval a →
        ((fourierUnitary w : SoninL2) : ℝ → ℂ) x = c') ∧
      (∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (w : ℝ → ℂ) t = d') ∧
      ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 →
        extendedMellinContinuation a c' d' w s * (s - ρ)
          = extendedMellinContinuation a c d v s := by
  classical
  set F : ℂ → ℂ := extendedMellinContinuation a c d v with hF
  set Fr : ℂ → ℂ := extendedMellinContinuation a d c (fourierUnitary v) with hFr
  have hev' : fourierUnitary v ∈ evenSubspace := fourierUnitary_mem_evenSubspace hev
  have hff : fourierUnitary (fourierUnitary v) = v :=
    fourierUnitary_fourierUnitary_of_mem_evenSubspace hev
  have hc' : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ centralInterval a →
      ((fourierUnitary (fourierUnitary v) : SoninL2) : ℝ → ℂ) x = d := by
    rw [hff]; exact hd
  have hρ0 : ρ ≠ 0 := by intro h; rw [h] at h0; norm_num at h0
  have hρ1 : ρ ≠ 1 := by intro h; rw [h] at h1; norm_num at h1
  have hmre : ((1 : ℂ) - ρ).re = 1 - ρ.re := by rw [Complex.sub_re]; simp
  have hm0 : 0 < ((1 : ℂ) - ρ).re := by rw [hmre]; linarith
  have hm1 : ((1 : ℂ) - ρ).re < 1 := by rw [hmre]; linarith
  have hFmero : ∀ s : ℂ, MeromorphicAt F s := meromorphicAt_extendedMellinContinuation ha hev hc hd
  have hFrmero : ∀ s : ℂ, MeromorphicAt Fr s :=
    meromorphicAt_extendedMellinContinuation ha hev' hc' hc
  have hFana : ∀ s : ℂ, s ≠ 0 → s ≠ 1 → AnalyticAt ℂ F s := fun s hs0 hs1 =>
    analyticAt_extendedMellinContinuation_of_ne ha hev hc hd hs0 hs1
  have hFrana : ∀ s : ℂ, s ≠ 0 → s ≠ 1 → AnalyticAt ℂ Fr s := fun s hs0 hs1 =>
    analyticAt_extendedMellinContinuation_of_ne ha hev' hc' hc hs0 hs1
  -- the reflected transform vanishes at the mirror point
  have hrefl : ∀ s : ℂ, 0 < s.re → s.re < 1 → burnolChiFactor s * F (1 - s) = Fr s := fun s hs0 hs1 =>
    chi_mul_extendedMellinContinuation_one_sub ha hev hc hd hs0 hs1
  have hFrvan : Fr ((1 : ℂ) - ρ) = 0 := by
    have h := hrefl ((1 : ℂ) - ρ) hm0 hm1
    rw [show (1 : ℂ) - ((1 : ℂ) - ρ) = ρ from by ring, hvan, mul_zero] at h
    exact h.symm
  -- the two divided transforms
  set Q : ℂ → ℂ := divShiftNF F ρ with hQ
  set Qr : ℂ → ℂ := divShiftNF Fr ((1 : ℂ) - ρ) with hQr
  have hQhardy : IsMellinHeadHardy a Q := isMellinHeadHardy_divShiftNF ha hev hc hd h0 h1 hvan
  have hQrhardy : IsMellinHeadHardy a Qr :=
    isMellinHeadHardy_divShiftNF ha hev' hc' hc hm0 hm1 hFrvan
  obtain ⟨c₁, g₁, hg₁, heq₁'⟩ := (isMellinHeadHardy_iff ha Q).1 hQhardy
  obtain ⟨c₀, g₀, hg₀, heq₀⟩ := (isMellinHeadHardy_iff ha Qr).1 hQrhardy
  have heq₁ : ∀ z : ℂ, 1 / 2 < z.re → z.re < 1 → Q z = headTailMellin a c₁ g₁ z := by
    intro z hz1 hz2
    refine heq₁' z hz1 ?_
    intro h; rw [h] at hz2; simp at hz2
  -- the reflected description
  have hQana : ∀ z : ℂ, 0 < z.re → z.re < 1 → AnalyticAt ℂ Q z := by
    intro z hz0 hz1
    have hz0' : z ≠ 0 := by intro h; rw [h] at hz0; simp at hz0
    have hz1' : z ≠ 1 := by intro h; rw [h] at hz1; simp at hz1
    exact analyticAt_divShiftNF hFmero (hFana z hz0' hz1') (hFana ρ hρ0 hρ1) hvan
  have hQrana : ∀ z : ℂ, 0 < z.re → z.re < 1 → AnalyticAt ℂ Qr z := by
    intro z hz0 hz1
    have hz0' : z ≠ 0 := by intro h; rw [h] at hz0; simp at hz0
    have hz1' : z ≠ 1 := by intro h; rw [h] at hz1; simp at hz1
    refine analyticAt_divShiftNF hFrmero (hFrana z hz0' hz1') (hFrana _ ?_ ?_) hFrvan
    · intro h; rw [h] at hm0; norm_num at hm0
    · intro h; rw [h] at hm1; norm_num at hm1
  have hoff : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 → s ≠ (1 : ℂ) - ρ →
      burnolChiFactor s * Q (1 - s) = -Qr s := by
    intro s hs1 hs2 hsm
    have hs0 : 0 < s.re := by linarith
    have hsub0 : (1 : ℂ) - s ≠ 0 := by
      intro h
      have : s = 1 := by linear_combination -h
      rw [this] at hs2; norm_num at hs2
    have hsub1 : (1 : ℂ) - s ≠ 1 := by
      intro h
      have : s = 0 := by linear_combination -h
      rw [this] at hs1; norm_num at hs1
    have hsubρ : (1 : ℂ) - s ≠ ρ := by
      intro h
      exact hsm (by linear_combination -h)
    have hs0' : s ≠ 0 := by intro h; rw [h] at hs1; norm_num at hs1
    have hs1' : s ≠ 1 := by intro h; rw [h] at hs2; norm_num at hs2
    rw [hQ, divShiftNF_eq hFmero (hFana _ hsub0 hsub1) hsubρ, hQr,
      divShiftNF_eq hFrmero (hFrana _ hs0' hs1') hsm]
    have hden : ((1 : ℂ) - s) - ρ = -(s - ((1 : ℂ) - ρ)) := by ring
    rw [hden]
    have hne : s - ((1 : ℂ) - ρ) ≠ 0 := sub_ne_zero.2 hsm
    rw [← hrefl s hs0 hs2]
    field_simp
  have heq₂ : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 →
      burnolChiFactor s * Q (1 - s)
        = headTailMellin a (-c₀) (fun t : ℝ => -g₀ t) s := by
    intro s hs1 hs2
    have hbase : ∀ z : ℂ, 1 / 2 < z.re → z.re < 1 →
        -Qr z = headTailMellin a (-c₀) (fun t : ℝ => -g₀ t) z := by
      intro z hz1 hz2
      have hz1' : z ≠ 1 := by intro h; rw [h] at hz2; simp at hz2
      rw [headTailMellin_neg, ← heq₀ z hz1 hz1']
    by_cases hsm : s = (1 : ℂ) - ρ
    · -- fill the puncture
      have hcontL : ContinuousAt (fun z : ℂ => burnolChiFactor z * Q (1 - z)) s := by
        have hchi : ContinuousAt burnolChiFactor s :=
          (differentiableAt_burnolChiFactor hs2).continuousAt
        have hsub : ContinuousAt (fun z : ℂ => (1 : ℂ) - z) s := by fun_prop
        have hsub0 : 0 < ((1 : ℂ) - s).re := by
          rw [Complex.sub_re]; simp; linarith
        have hsub1 : ((1 : ℂ) - s).re < 1 := by
          rw [Complex.sub_re]; simp; linarith
        have hq : ContinuousAt (fun z : ℂ => Q (1 - z)) s :=
          ContinuousAt.comp (g := Q) (f := fun z : ℂ => (1 : ℂ) - z) (x := s)
            (hQana _ hsub0 hsub1).continuousAt hsub
        exact hchi.mul hq
      have hs1' : s ≠ 1 := by intro h; rw [h] at hs2; norm_num at hs2
      have hcontR : ContinuousAt
          (fun z : ℂ => headTailMellin a (-c₀) (fun t : ℝ => -g₀ t) z) s :=
        (differentiableAt_headTailMellin ha (-c₀) (hg₀.neg) hs1 hs1').continuousAt
      have hstrip : IsOpen {z : ℂ | 1 / 2 < z.re ∧ z.re < 1} :=
        (isOpen_lt continuous_const Complex.continuous_re).inter
          (isOpen_lt Complex.continuous_re continuous_const)
      refine eq_of_eventuallyEq_punctured (ρ := s)
        (F := fun z : ℂ => burnolChiFactor z * Q (1 - z))
        (H := fun z : ℂ => headTailMellin a (-c₀) (fun t : ℝ => -g₀ t) z) hcontL hcontR ?_
      filter_upwards [self_mem_nhdsWithin,
        eventually_nhdsWithin_of_eventually_nhds (hstrip.mem_nhds ⟨hs1, hs2⟩)] with z hz hz'
      rw [hoff z hz'.1 hz'.2 (by rw [← hsm]; exact hz), hbase z hz'.1 hz'.2]
    · rw [hoff s hs1 hs2 hsm, hbase s hs1 hs2]
  -- build the vector
  have hQcont : ContinuousOn Q {z : ℂ | 0 < z.re ∧ z.re < 1} := fun z hz =>
    ((hQana z hz.1 hz.2).continuousAt).continuousWithinAt
  obtain ⟨hmem, hband⟩ :=
    headTailVector_mem_centralSoninExtendedCarrier ha hQcont hg₁ heq₁ (hg₀.neg) heq₂
  set w : SoninL2 := headTailVector ha c₁ hg₁ with hw
  refine ⟨w, -c₀, c₁, headTailVector_mem_evenSubspace ha c₁ hg₁, hmem, hband,
    headTailVector_ae_band ha c₁ hg₁, ?_⟩
  intro s hs1 hs2
  have hs1' : s ≠ 1 := by intro h; rw [h] at hs2; norm_num at hs2
  rw [extendedMellinContinuation_headTailVector ha c₁ hg₁ hband hs1 hs1', ← heq₁ s hs1 hs2]
  by_cases hsρ : s = ρ
  · subst hsρ
    rw [sub_self, mul_zero, hvan]
  · have hs0' : s ≠ 0 := by intro h; rw [h] at hs1; norm_num at hs1
    rw [hQ, divShiftNF_eq hFmero (hFana s hs0' hs1') hsρ, div_mul_cancel₀]
    exact sub_ne_zero.2 hsρ

end

end RHTower
