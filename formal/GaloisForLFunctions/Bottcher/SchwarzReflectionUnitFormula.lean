/-
# The Schwarz reflection formula across the unit circle (from boundary values)

The constructive half of the reflection route.  `differentiableAt_of_off_modulus_arc`
(`SchwarzReflectionModulusArc.lean`) proves that a function already *glued* across a modulus-one arc
is holomorphic; it does not build the glued function.  This file builds it in the unit-circle model:
given `F` holomorphic on the outer side `{1 < ‖w‖}` of a ball around a circle point `w₀`, continuous
up to the circle, nonzero on the closed outer side, and of modulus one *on* the circle, the
reflection

  `reflectUnit F w = if 1 ≤ ‖w‖ then F w else (conj (F (1 / conj w)))⁻¹`

is analytic at `w₀`.  The inner piece is `(conj ∘ F ∘ conj)(1/w)⁻¹`, holomorphic by
`differentiableAt_conj_conj_iff`; on the circle `1 / conj w = w` and `|F| = 1` force it to agree with
`F`, so the glued function is continuous across; `differentiableAt_of_off_modulus_arc` (with `g = id`)
then makes it holomorphic at `w₀`.

This is a classical, mathlib-absent theorem.  In the q62 application it supplies the reflected
extension `f` of the exterior Böttcher branch across a smooth Julia arc (after transport through the
local biholomorphism `φ` that carries the arc to the unit circle), reducing `ArcReflectionData`
(`Q62ReflectionBridge.lean`) to the pure boundary regularity of `β` at the piece — the reflection
formula content is now discharged here.  The `F ≠ 0` hypothesis holds automatically for
`F = β ∘ γ`: the Böttcher coordinate is nonzero on the basin.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).
-/
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import GaloisForLFunctions.Bottcher.SchwarzReflectionModulusArc

open Complex Set Filter Topology

namespace Bottcher

/-- The reflection of `F` across the unit circle: `F` on the closed outer side `{1 ≤ ‖w‖}`, and the
Schwarz-reflected value `(conj (F (1 / conj w)))⁻¹` strictly inside. -/
noncomputable def reflectUnit (F : ℂ → ℂ) (w : ℂ) : ℂ :=
  if 1 ≤ ‖w‖ then F w else (starRingEnd ℂ (F (1 / starRingEnd ℂ w)))⁻¹

/-- The reflected inner value as a standalone function (defined everywhere, meaningful on `‖w‖ ≤ 1`,
where the reflected point `1 / conj w` lands on the outer side). -/
noncomputable def reflInner (F : ℂ → ℂ) (w : ℂ) : ℂ :=
  (starRingEnd ℂ (F (1 / starRingEnd ℂ w)))⁻¹

/-- On the unit circle the reflection map `w ↦ 1 / conj w` is the identity (`w · conj w = ‖w‖² = 1`). -/
theorem inv_conj_of_unit {w : ℂ} (hw : ‖w‖ = 1) : 1 / (starRingEnd ℂ) w = w := by
  have hw0 : w ≠ 0 := by rw [← norm_ne_zero_iff, hw]; norm_num
  have hcw : (starRingEnd ℂ) w ≠ 0 := by simpa using hw0
  have hns : w * (starRingEnd ℂ) w = 1 := by
    rw [Complex.mul_conj]; rw [Complex.normSq_eq_norm_sq, hw]; norm_num
  rw [div_eq_iff hcw]; exact hns.symm

/-- Norm of the reflection map: `‖1 / conj z‖ = 1 / ‖z‖`. -/
theorem norm_invConj (z : ℂ) : ‖1 / (starRingEnd ℂ) z‖ = 1 / ‖z‖ := by
  rw [norm_div, norm_one, RCLike.norm_conj]

/-- On the circle, the reflected inner value agrees with `F`: `1 / conj w = w` and `|F w| = 1` give
`(conj (F w))⁻¹ = F w`.  This is what makes the glued reflection continuous across the arc. -/
theorem reflInner_eq_of_unit {F : ℂ → ℂ} {w : ℂ} (hw : ‖w‖ = 1) (hF : ‖F w‖ = 1) :
    reflInner F w = F w := by
  rw [reflInner, inv_conj_of_unit hw]
  have hFw0 : F w ≠ 0 := by rw [← norm_ne_zero_iff, hF]; norm_num
  have hns : F w * (starRingEnd ℂ) (F w) = 1 := by
    rw [Complex.mul_conj]; rw [Complex.normSq_eq_norm_sq, hF]; norm_num
  have hcF : (starRingEnd ℂ) (F w) ≠ 0 := by simpa using hFw0
  rw [inv_eq_one_div, div_eq_iff hcF]; exact hns.symm

/-- The reflected inner value as `(conj ∘ F ∘ conj)(1/w)⁻¹` (using `1 / conj w = conj (1/w)`). -/
theorem reflInner_eq_comp (F : ℂ → ℂ) (w : ℂ) :
    reflInner F w = ((starRingEnd ℂ ∘ F ∘ starRingEnd ℂ) (1 / w))⁻¹ := by
  rw [reflInner]
  congr 2
  simp only [Function.comp_apply]
  rw [map_div₀, map_one]

/-- **Inner holomorphy.**  Where `‖w‖ < 1` (so the reflected point `1 / conj w` is outer), `reflInner F`
is holomorphic: it is `(conj ∘ F ∘ conj)(1/w)⁻¹`, and `conj ∘ F ∘ conj` is holomorphic exactly where
`F` is (`differentiableAt_conj_conj_iff`), composed with the holomorphic `w ↦ 1/w` and inverted at a
nonzero value. -/
theorem reflInner_differentiableAt {F : ℂ → ℂ} {w : ℂ} (hw0 : w ≠ 0)
    (hFdiff : DifferentiableAt ℂ F (1 / (starRingEnd ℂ) w))
    (hFne : F (1 / (starRingEnd ℂ) w) ≠ 0) :
    DifferentiableAt ℂ (reflInner F) w := by
  set G : ℂ → ℂ := starRingEnd ℂ ∘ F ∘ starRingEnd ℂ with hG
  have hGdiff : DifferentiableAt ℂ G (1 / w) := by
    rw [hG, differentiableAt_conj_conj_iff]
    have : (starRingEnd ℂ) (1 / w) = 1 / (starRingEnd ℂ) w := by rw [map_div₀, map_one]
    rw [this]; exact hFdiff
  have hinvw : DifferentiableAt ℂ (fun z : ℂ => 1 / z) w := by
    simp only [one_div]; exact (differentiableAt_inv hw0)
  have hcomp : DifferentiableAt ℂ (fun z => G (1 / z)) w := hGdiff.comp w hinvw
  have hGne : G (1 / w) ≠ 0 := by
    rw [hG]; simp only [Function.comp_apply]
    rw [show (starRingEnd ℂ) (1 / w) = 1 / (starRingEnd ℂ) w from by rw [map_div₀, map_one]]
    simpa using hFne
  have hres : DifferentiableAt ℂ (fun z => (G (1 / z))⁻¹) w := hcomp.inv hGne
  have heq : reflInner F = fun z => (G (1 / z))⁻¹ := by
    funext z; rw [reflInner_eq_comp]
  rw [heq]; exact hres

/-- The reflection map `w ↦ 1 / conj w` is continuous at a nonzero point. -/
theorem continuousAt_invConj {w : ℂ} (hw0 : w ≠ 0) :
    ContinuousAt (fun z => 1 / (starRingEnd ℂ) z) w := by
  have hcw : (starRingEnd ℂ) w ≠ 0 := by simpa using hw0
  fun_prop (disch := assumption)

/-- **Inner-side continuity at an arc point.**  At a circle point `w₁` (`‖w₁‖ = 1`, `F w₁ ≠ 0`,
`F` continuous within the outer side), `reflInner F` is continuous within `{‖w‖ ≤ 1}`: the reflection
`w ↦ 1 / conj w` maps `{‖w‖ ≤ 1}` (near `w₁`) into the outer side `{1 ≤ ‖w‖}`, so it composes with the
outer continuity of `F`, then `conj` and inversion (`F w₁ ≠ 0`). -/
theorem reflInner_continuousWithinAt {F : ℂ → ℂ} {w₁ : ℂ}
    (hw₁ : ‖w₁‖ = 1) (hFne : F w₁ ≠ 0)
    (hFcont : ContinuousWithinAt F {v | 1 ≤ ‖v‖} w₁) :
    ContinuousWithinAt (reflInner F) {w | ‖w‖ ≤ 1} w₁ := by
  set ι : ℂ → ℂ := fun z => 1 / (starRingEnd ℂ) z with hιdef
  have hw₁0 : w₁ ≠ 0 := by rw [← norm_ne_zero_iff, hw₁]; norm_num
  have hιw₁ : ι w₁ = w₁ := inv_conj_of_unit hw₁
  set s₀ : Set ℂ := {w | ‖w‖ ≤ 1} ∩ Metric.ball w₁ (1/2) with hs₀
  have hball_nhds : Metric.ball w₁ (1/2) ∈ 𝓝 w₁ := Metric.ball_mem_nhds w₁ (by norm_num)
  have hne0 : ∀ w ∈ s₀, w ≠ 0 := by
    intro w hw
    have hd : ‖w - w₁‖ < 1/2 := by
      have := hw.2; rw [Metric.mem_ball, Complex.dist_eq] at this; exact this
    have hlt : 1/2 < ‖w‖ := by
      have h1 : ‖w₁‖ - ‖w‖ ≤ ‖w₁ - w‖ := norm_sub_norm_le _ _
      rw [norm_sub_rev] at h1; rw [hw₁] at h1; linarith
    rw [← norm_ne_zero_iff]; linarith
  have hιcont : ContinuousWithinAt ι s₀ w₁ :=
    (continuousAt_invConj hw₁0).continuousWithinAt
  have hmaps : Set.MapsTo ι s₀ {v | 1 ≤ ‖v‖} := by
    intro w hw
    have hw0 := hne0 w hw
    have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    have hle1 : ‖w‖ ≤ 1 := hw.1
    have hcw : (starRingEnd ℂ) w ≠ 0 := by simpa using hw0
    simp only [mem_setOf_eq, hιdef, one_div, norm_inv, RCLike.norm_conj]
    exact (one_le_inv₀ hwpos).mpr hle1
  have hFcompose : ContinuousWithinAt (fun w => F (ι w)) s₀ w₁ := by
    have hFc' : ContinuousWithinAt F {v | 1 ≤ ‖v‖} (ι w₁) := by rw [hιw₁]; exact hFcont
    exact hFc'.comp hιcont hmaps
  have hconj : ContinuousWithinAt (fun w => (starRingEnd ℂ) (F (ι w))) s₀ w₁ :=
    Complex.continuous_conj.continuousWithinAt.comp hFcompose (Set.mapsTo_univ _ _)
  have hFιne : (starRingEnd ℂ) (F (ι w₁)) ≠ 0 := by rw [hιw₁]; simpa using hFne
  have hinv : ContinuousWithinAt (fun w => ((starRingEnd ℂ) (F (ι w)))⁻¹) s₀ w₁ :=
    hconj.inv₀ hFιne
  have heq : (fun w => ((starRingEnd ℂ) (F (ι w)))⁻¹) = reflInner F := by
    funext w; rw [reflInner, hιdef]
  rw [heq, hs₀] at hinv
  exact (continuousWithinAt_inter hball_nhds).mp hinv

/-- **Schwarz reflection across the unit circle (from boundary values).**  If `F` is holomorphic on
the outer side `{1 < ‖w‖}` of a ball around a unit-circle point `w₀`, continuous up to the circle,
nonzero on the closed outer side, and has modulus one on the circle, then its reflection
`reflectUnit F` — equal to `F` on `{1 ≤ ‖w‖}` and to the Schwarz-reflected value inside — is analytic
at `w₀`.  Since `reflectUnit F = F` on the outer side, this analytically continues `F` across the
circle.  Mathlib-absent classical reflection principle. -/
theorem schwarzReflect_unit_circle {F : ℂ → ℂ} {w₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hw₀ : ‖w₀‖ = 1)
    (hFcont : ContinuousOn F ({v | 1 ≤ ‖v‖} ∩ Metric.ball w₀ r))
    (hFhol : DifferentiableOn ℂ F ({v | 1 < ‖v‖} ∩ Metric.ball w₀ r))
    (hFne : ∀ v ∈ {v : ℂ | 1 ≤ ‖v‖} ∩ Metric.ball w₀ r, F v ≠ 0)
    (hFmod : ∀ v ∈ {v : ℂ | ‖v‖ = 1} ∩ Metric.ball w₀ r, ‖F v‖ = 1) :
    AnalyticAt ℂ (reflectUnit F) w₀ := by
  classical
  have hw₀0 : w₀ ≠ 0 := by rw [← norm_ne_zero_iff, hw₀]; norm_num
  have hOuterOpen : IsOpen {w : ℂ | 1 < ‖w‖} := isOpen_lt continuous_const continuous_norm
  have hInnerOpen : IsOpen {w : ℂ | ‖w‖ < 1} := isOpen_lt continuous_norm continuous_const
  have hOInter : IsOpen ({w : ℂ | 1 < ‖w‖} ∩ Metric.ball w₀ r) := hOuterOpen.inter Metric.isOpen_ball
  -- δ: `ball w₀ δ` maps under the reflection into `ball w₀ r`, with `δ ≤ r`, `δ ≤ 1/2`
  have hpre : ∀ᶠ z in 𝓝 w₀, (1 / (starRingEnd ℂ) z) ∈ Metric.ball w₀ r := by
    have hmem : Metric.ball w₀ r ∈ 𝓝 (1 / (starRingEnd ℂ) w₀) := by
      rw [inv_conj_of_unit hw₀]; exact Metric.ball_mem_nhds w₀ hr
    exact (continuousAt_invConj hw₀0).preimage_mem_nhds hmem
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := Metric.eventually_nhds_iff.mp hpre
  set δ : ℝ := min δ₀ (min r (1/2)) with hδdef
  have hδpos : 0 < δ := lt_min hδ₀pos (lt_min hr (by norm_num))
  have hδr : δ ≤ r := le_trans (min_le_right _ _) (min_le_left _ _)
  have hδhalf : δ ≤ 1/2 := le_trans (min_le_right _ _) (min_le_right _ _)
  have hzball_r : ∀ z ∈ Metric.ball w₀ δ, z ∈ Metric.ball w₀ r :=
    fun z hz => Metric.ball_subset_ball hδr hz
  have hzne0 : ∀ z ∈ Metric.ball w₀ δ, z ≠ 0 := by
    intro z hz
    have hd : ‖z - w₀‖ < δ := by rw [Metric.mem_ball, Complex.dist_eq] at hz; exact hz
    have hgt : 1 - δ < ‖z‖ := by
      have h1 : ‖w₀‖ - ‖z‖ ≤ ‖w₀ - z‖ := norm_sub_norm_le _ _
      rw [norm_sub_rev] at h1; rw [hw₀] at h1; linarith
    rw [← norm_ne_zero_iff]; nlinarith [hδhalf]
  have hι_in : ∀ z ∈ Metric.ball w₀ δ, (1 / (starRingEnd ℂ) z) ∈ Metric.ball w₀ r :=
    fun z hz => hδ₀ (Metric.ball_subset_ball (min_le_left _ _) hz)
  -- off-arc holomorphy on `ball w₀ δ`
  have hoff : ∀ z ∈ Metric.ball w₀ δ, ‖z‖ ≠ 1 → DifferentiableAt ℂ (reflectUnit F) z := by
    intro z hzδ hznorm
    rcases lt_or_gt_of_ne hznorm with hlt | hgt
    · -- `‖z‖ < 1`: `reflectUnit F = reflInner F`, holomorphic by `reflInner_differentiableAt`
      have hz0 : z ≠ 0 := hzne0 z hzδ
      have hιnorm : 1 < ‖1 / (starRingEnd ℂ) z‖ := by
        rw [norm_invConj z, lt_div_iff₀ (norm_pos_iff.mpr hz0)]; simpa using hlt
      have hιin : (1 / (starRingEnd ℂ) z) ∈ {v : ℂ | 1 < ‖v‖} ∩ Metric.ball w₀ r :=
        ⟨hιnorm, hι_in z hzδ⟩
      have hFdiff : DifferentiableAt ℂ F (1 / (starRingEnd ℂ) z) :=
        hFhol.differentiableAt (hOInter.mem_nhds hιin)
      have hmem1 : (1 / (starRingEnd ℂ) z) ∈ {v : ℂ | 1 ≤ ‖v‖} := le_of_lt hιnorm
      have hFne' : F (1 / (starRingEnd ℂ) z) ≠ 0 :=
        hFne (1 / (starRingEnd ℂ) z) ⟨hmem1, hι_in z hzδ⟩
      have hrefl : DifferentiableAt ℂ (reflInner F) z := reflInner_differentiableAt hz0 hFdiff hFne'
      have heq : reflectUnit F =ᶠ[𝓝 z] reflInner F := by
        filter_upwards [hInnerOpen.mem_nhds hlt] with y hy
        have hy' : ‖y‖ < 1 := hy
        simp only [reflectUnit, reflInner, if_neg (not_le.mpr hy')]
      exact (heq.differentiableAt_iff).mpr hrefl
    · -- `‖z‖ > 1`: `reflectUnit F = F`, holomorphic by `hFhol`
      have hzin : z ∈ {v : ℂ | 1 < ‖v‖} ∩ Metric.ball w₀ r := ⟨hgt, hzball_r z hzδ⟩
      have hFdiff : DifferentiableAt ℂ F z := hFhol.differentiableAt (hOInter.mem_nhds hzin)
      have heq : reflectUnit F =ᶠ[𝓝 z] F := by
        filter_upwards [hOuterOpen.mem_nhds hgt] with y hy
        have hy' : 1 < ‖y‖ := hy
        rw [reflectUnit, if_pos (le_of_lt hy')]
      exact (heq.differentiableAt_iff).mpr hFdiff
  -- continuity on `ball w₀ δ`
  have hcont : ∀ z ∈ Metric.ball w₀ δ, ContinuousAt (reflectUnit F) z := by
    intro z hzδ
    rcases lt_trichotomy ‖z‖ 1 with hlt | heq1 | hgt
    · exact (hoff z hzδ (ne_of_lt hlt)).continuousAt
    · -- `‖z‖ = 1`: glue the two one-sided continuities over the covering `{1≤‖·‖} ∪ {‖·‖≤1}`
      have hzr : z ∈ Metric.ball w₀ r := hzball_r z hzδ
      have hballnhds : Metric.ball w₀ r ∈ 𝓝 z := Metric.isOpen_ball.mem_nhds hzr
      have hFcont_z : ContinuousWithinAt F {v | 1 ≤ ‖v‖} z := by
        have hin : z ∈ {v : ℂ | 1 ≤ ‖v‖} ∩ Metric.ball w₀ r := ⟨le_of_eq heq1.symm, hzr⟩
        exact (continuousWithinAt_inter hballnhds).mp (hFcont z hin)
      have hFne_z : F z ≠ 0 := hFne z ⟨le_of_eq heq1.symm, hzr⟩
      have hcover : (Set.univ : Set ℂ) = {w | 1 ≤ ‖w‖} ∪ {w | ‖w‖ ≤ 1} := by
        ext w; simp only [mem_univ, mem_union, mem_setOf_eq, true_iff]; exact le_total 1 ‖w‖
      have hval : reflectUnit F z = F z := by rw [reflectUnit, if_pos (le_of_eq heq1.symm)]
      have hcOuter : ContinuousWithinAt (reflectUnit F) {w | 1 ≤ ‖w‖} z := by
        refine hFcont_z.congr (fun y hy => ?_) hval
        have hy' : 1 ≤ ‖y‖ := hy
        rw [reflectUnit, if_pos hy']
      have hinnerBig : ContinuousWithinAt (reflInner F) {w | ‖w‖ ≤ 1} z :=
        reflInner_continuousWithinAt heq1 hFne_z hFcont_z
      have hinnerSmall : ContinuousWithinAt (reflInner F) ({w | ‖w‖ ≤ 1} ∩ Metric.ball w₀ r) z :=
        hinnerBig.mono inter_subset_left
      have hagree : ∀ y ∈ ({w : ℂ | ‖w‖ ≤ 1} ∩ Metric.ball w₀ r),
          reflectUnit F y = reflInner F y := by
        intro y hy
        have hy1 : ‖y‖ ≤ 1 := hy.1
        rcases lt_or_eq_of_le hy1 with hlt | heqy
        · simp only [reflectUnit, reflInner, if_neg (not_le.mpr hlt)]
        · rw [reflectUnit, if_pos heqy.ge]
          exact (reflInner_eq_of_unit heqy (hFmod y ⟨heqy, hy.2⟩)).symm
      have hzInner : reflectUnit F z = reflInner F z := by
        rw [hval]; exact (reflInner_eq_of_unit heq1 (hFmod z ⟨heq1, hzr⟩)).symm
      have hcInnerSmall : ContinuousWithinAt (reflectUnit F) ({w | ‖w‖ ≤ 1} ∩ Metric.ball w₀ r) z :=
        hinnerSmall.congr hagree hzInner
      have hcInner : ContinuousWithinAt (reflectUnit F) {w | ‖w‖ ≤ 1} z :=
        (continuousWithinAt_inter hballnhds).mp hcInnerSmall
      rw [← continuousWithinAt_univ, hcover, continuousWithinAt_union]
      exact ⟨hcOuter, hcInner⟩
    · exact (hoff z hzδ (ne_of_gt hgt)).continuousAt
  -- reflect across the modulus-one arc `{‖id z‖ = 1}` with `g = id`
  refine differentiableAt_of_off_modulus_arc (g := fun z => z) analyticAt_id ?_ ?_ ?_ ?_
  · simp
  · exact hw₀
  · filter_upwards [Metric.ball_mem_nhds w₀ hδpos] with z hz using hcont z hz
  · filter_upwards [Metric.ball_mem_nhds w₀ hδpos] with z hz hznorm using hoff z hz hznorm

end Bottcher
