import GaloisForLFunctions.RHTower.HeadTailVector
import GaloisForLFunctions.RHTower.MellinTwoSidedGlue
import GaloisForLFunctions.RHTower.SoninExtendedFunctionalEquation
import GaloisForLFunctions.RHTower.SoninExtendedDilation
import GaloisForLFunctions.RHTower.SoninEntireMellin
import GaloisForLFunctions.RHTower.SoninMixedPhysicalBlockNonvanishing
import GaloisForLFunctions.RHTower.SoninBandLimitedShellVanishing

/-!
# Burnol's Proposition 4.1, two-sided converse

A function `F` on the strip which is the Mellin transform of a head/tail pair `(c₁, g₁)` **and**
whose reflection `χ(s)F(1-s)` is the Mellin transform of a head/tail pair `(c₂, g₂)` is the
continued Mellin transform of an actual vector of Burnol's extended Sonine space `L_a`.

The head/tail pair produces the even vector `v` of `HeadTailVector`; the functional equation of
`SoninExtendedFunctionalEquation` — whose only hypotheses are evenness and *one* constant head —
identifies `χ(s)F(1-s)` with the continued full Mellin transform of `F₊v` left of the critical line,
while the second Hardy hypothesis describes it right of the line.  `MellinTwoSidedGlue` then forces
`F₊v` to be constant on the aperture head, which is exactly the missing Sonine condition.

## Main results

* `headTailVector_mem_centralSoninExtendedCarrier`
-/

namespace RHTower

open MeasureTheory Set Complex Filter Topology

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Proposition 4.1, two-sided converse.**  The head/tail vector lies in `L_a`, and the aperture
constant of its cosine transform is the head constant of the reflected transform. -/
theorem headTailVector_mem_centralSoninExtendedCarrier {a : ℝ} (ha : 0 < a)
    {F : ℂ → ℂ} (hFcont : ContinuousOn F {z : ℂ | 0 < z.re ∧ z.re < 1})
    {c₁ : ℂ} {g₁ : ℝ → ℂ} (hg₁ : MemLp g₁ 2 (volume.restrict (Ioi a)))
    (hF₁ : ∀ z : ℂ, 1 / 2 < z.re → z.re < 1 → F z = headTailMellin a c₁ g₁ z)
    {c₂ : ℂ} {g₂ : ℝ → ℂ} (hg₂ : MemLp g₂ 2 (volume.restrict (Ioi a)))
    (hF₂ : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 →
      burnolChiFactor s * F (1 - s) = headTailMellin a c₂ g₂ s) :
    headTailVector ha c₁ hg₁ ∈ centralSoninExtendedCarrier a ∧
      (∀ᵐ x ∂(volume : Measure ℝ), x ∈ centralInterval a →
        ((fourierUnitary (headTailVector ha c₁ hg₁) : SoninL2) : ℝ → ℂ) x = c₂) := by
  classical
  set v : SoninL2 := headTailVector ha c₁ hg₁ with hvdef
  have hev : v ∈ evenSubspace := headTailVector_mem_evenSubspace ha c₁ hg₁
  have hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (v : ℝ → ℂ) t = c₁ :=
    headTailVector_ae_band ha c₁ hg₁
  set u : SoninL2 := fourierUnitary v with hudef
  have huev : u ∈ evenSubspace := fourierUnitary_mem_evenSubspace hev
  have huu : fourierUnitary u = v := fourierUnitary_fourierUnitary_of_mem_evenSubspace hev
  have hc : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ centralInterval a →
      ((fourierUnitary u : SoninL2) : ℝ → ℂ) x = c₁ := by
    rw [huu]
    exact hd
  -- the reflected transform on the left of the critical line
  have hFE : ∀ s : ℂ, 0 < s.re → s.re < 1 / 2 →
      extendedFullMellin a c₁ u s = burnolChiFactor s * F (1 - s) := by
    intro s hs0 hs
    have h := extendedFullMellin_functional_equation ha huev hc hs0 hs
    rw [huu] at h
    have hz1 : 1 / 2 < ((1 : ℂ) - s).re := by
      rw [Complex.sub_re]
      simp only [Complex.one_re]
      linarith
    have hz2 : ((1 : ℂ) - s).re < 1 := by
      rw [Complex.sub_re]
      simp only [Complex.one_re]
      linarith
    rw [h, soninMellinIntegral_headTailVector ha c₁ hg₁ hz1 hz2, ← hF₁ _ hz1 hz2]
  -- the glue function
  set Ψ : ℂ → ℂ := fun s : ℂ => burnolChiFactor s * F (1 - s) - extendedTailMellin a c₁ u s
    with hΨdef
  have hleft : ∀ s : ℂ, 0 < s.re → s.re < 1 / 2 →
      Ψ s = ∫ t in Ioo (0 : ℝ) a, ((t : ℝ) : ℂ) ^ (-s) * (u : ℝ → ℂ) t := by
    intro s hs0 hs
    rw [hΨdef]
    simp only
    rw [← hFE s hs0 hs, extendedFullMellin]
    ring
  have hright : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 →
      Ψ s = c₂ * ((a : ℝ) : ℂ) ^ ((1 : ℂ) - s) / (1 - s)
        + ∫ t in Ioi a, ((t : ℝ) : ℂ) ^ (-s) * (g₂ t - (u : ℝ → ℂ) t) := by
    intro s hs1 hs2
    have htail : extendedTailMellin a c₁ u s
        = ∫ t in Ioi a, ((t : ℝ) : ℂ) ^ (-s) * (u : ℝ → ℂ) t := extendedTailMellin_eq ha hc hs1
    have hint1 : IntegrableOn (fun t : ℝ => ((t : ℝ) : ℂ) ^ (-s) * g₂ t) (Ioi a) volume :=
      (memLp_two_cpow_Ioi ha hs1).integrable_mul hg₂
    have hint2 : IntegrableOn (fun t : ℝ => ((t : ℝ) : ℂ) ^ (-s) * (u : ℝ → ℂ) t)
        (Ioi a) volume := integrableOn_cpow_mul_Ioi ha u hs1
    have hsub : (∫ t in Ioi a, ((t : ℝ) : ℂ) ^ (-s) * (g₂ t - (u : ℝ → ℂ) t))
        = (∫ t in Ioi a, ((t : ℝ) : ℂ) ^ (-s) * g₂ t)
          - ∫ t in Ioi a, ((t : ℝ) : ℂ) ^ (-s) * (u : ℝ → ℂ) t := by
      rw [← MeasureTheory.integral_sub hint1 hint2]
      refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
      ring
    rw [hΨdef]
    simp only
    rw [hF₂ s hs1 hs2, htail, hsub, headTailMellin]
    ring
  -- continuity of the glue
  have hΨcont : ContinuousOn Ψ {s : ℂ | 0 < s.re ∧ s.re < 1} := by
    have h1 : ContinuousOn (fun s : ℂ => burnolChiFactor s) {s : ℂ | 0 < s.re ∧ s.re < 1} := by
      intro s hs
      exact ((differentiableAt_burnolChiFactor hs.2).continuousAt).continuousWithinAt
    have hrefl : Set.MapsTo (fun s : ℂ => (1 : ℂ) - s) {s : ℂ | 0 < s.re ∧ s.re < 1}
        {z : ℂ | 0 < z.re ∧ z.re < 1} := by
      intro s hs
      have h1 : 0 < s.re := hs.1
      have h2 : s.re < 1 := hs.2
      refine ⟨?_, ?_⟩ <;> (rw [Set.mem_setOf_eq] at *; rw [Complex.sub_re]; simp; linarith)
    have h2 : ContinuousOn (fun s : ℂ => F ((1 : ℂ) - s)) {s : ℂ | 0 < s.re ∧ s.re < 1} :=
      hFcont.comp (by fun_prop) hrefl
    have h3 : ContinuousOn (extendedTailMellin a c₁ u) {s : ℂ | 0 < s.re ∧ s.re < 1} := by
      refine ContinuousOn.mono ?_ (fun s hs => hs.1)
      exact (differentiableOn_extendedTailMellin ha hc).continuousOn
    exact (h1.mul h2).sub h3
  -- the gluing theorem
  have hu0 : MemLp ((u : ℝ → ℂ)) 2 (volume.restrict (Ioo (0 : ℝ) a)) :=
    (Lp.memLp u).restrict (Ioo (0 : ℝ) a)
  have hgu : MemLp (fun t : ℝ => g₂ t - (u : ℝ → ℂ) t) 2 (volume.restrict (Ioi a)) :=
    hg₂.sub ((Lp.memLp u).restrict (Ioi a))
  obtain ⟨hhead, _htail⟩ := ae_eq_of_two_sided_mellin ha hu0 hgu hΨcont hleft hright
  -- from the positive head to the whole band
  have huneg : ∀ᵐ x ∂(volume : Measure ℝ), (u : ℝ → ℂ) (-x) = (u : ℝ → ℂ) x := by
    have hrefl : ((l2Reflection u : SoninL2) : ℝ → ℂ)
        =ᵐ[volume] fun x => (u : ℝ → ℂ) (-x) :=
      MeasureTheory.Lp.coeFn_compMeasurePreserving u
        (Measure.measurePreserving_neg (volume : Measure ℝ))
    have heq : l2Reflection u = u := (mem_evenSubspace_iff u).1 huev
    filter_upwards [hrefl] with x hx
    rw [← hx, heq]
  have hheadAll : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Ioo (0 : ℝ) a → (u : ℝ → ℂ) x = c₂ := by
    rw [← ae_restrict_iff' measurableSet_Ioo]
    exact hhead
  have hheadNeg : ∀ᵐ x ∂(volume : Measure ℝ), -x ∈ Ioo (0 : ℝ) a → (u : ℝ → ℂ) (-x) = c₂ :=
    ((Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving).ae hheadAll
  have hband : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ centralInterval a → (u : ℝ → ℂ) x = c₂ := by
    have hzero : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 0 := by
      rw [ae_iff]
      simp
    have hpm : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ a ∧ x ≠ -a := by
      have h1 : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ a := by
        rw [ae_iff]
        simp
      have h2 : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ -a := by
        rw [ae_iff]
        simp
      filter_upwards [h1, h2] with x hx1 hx2
      exact ⟨hx1, hx2⟩
    filter_upwards [hheadAll, hheadNeg, huneg, hzero, hpm] with x hx1 hx2 hx3 hx4 hx5 hmem
    rcases hmem with ⟨hm1, hm2⟩
    rcases lt_or_gt_of_ne hx4 with hneg | hpos
    · have : -x ∈ Ioo (0 : ℝ) a := ⟨by linarith, by
        rcases lt_or_eq_of_le hm1 with h | h
        · linarith
        · exact absurd h.symm hx5.2⟩
      rw [← hx3]
      exact hx2 this
    · have : x ∈ Ioo (0 : ℝ) a := ⟨hpos, lt_of_le_of_ne hm2 hx5.1⟩
      exact hx1 this
  refine ⟨?_, hband⟩
  rw [mem_centralSoninExtendedCarrier_iff]
  exact ⟨⟨c₁, hd⟩, ⟨c₂, hband⟩⟩

end

end RHTower
