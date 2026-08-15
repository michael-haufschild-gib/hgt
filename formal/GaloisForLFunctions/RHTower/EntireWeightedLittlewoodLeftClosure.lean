import GaloisForLFunctions.RHTower.VerticalLogNormIntegralContinuity

/-!
# Weighted Littlewood identity with zeros on the left boundary

The classical fixed-contour theorem excludes zeros on all four boundary edges. For the first
horizontal zero moment this is stronger than necessary: a zero on the left edge has weight zero.
This module proves exact closure under such zeros. It moves the left edge rightward, uses finiteness
of the compact zero packet to stabilize the positive-width zeros, and passes to the original edge
through continuity of vertical logarithmic norm integrals. No boundary value of `logDeriv` is
required on the possibly singular left edge.
-/

open Complex MeasureTheory Set Filter intervalIntegral Topology
open scoped Interval

namespace RHTower

noncomputable section

theorem continuousOn_weighted_left_endpoint_integral
    {q : ℝ → ℝ} {c d : ℝ} (hq : ContinuousOn q (uIcc c d)) :
    ContinuousOn (fun a : ℝ => ∫ x in a..d, (x - a) * q x) (uIcc c d) := by
  have hqInt : IntervalIntegrable q volume c d := hq.intervalIntegrable
  have hxq : ContinuousOn (fun x : ℝ => x * q x) (uIcc c d) :=
    continuousOn_id.mul hq
  have hxqInt : IntervalIntegrable (fun x : ℝ => x * q x) volume c d :=
    hxq.intervalIntegrable
  have hprimq : ContinuousOn (fun a : ℝ => ∫ x in a..d, q x) (uIcc c d) :=
    continuousOn_primitive_interval_left (hq.integrableOn_compact isCompact_uIcc)
  have hprimxq : ContinuousOn (fun a : ℝ => ∫ x in a..d, x * q x) (uIcc c d) :=
    continuousOn_primitive_interval_left (hxq.integrableOn_compact isCompact_uIcc)
  have hdecomp : Set.EqOn (fun a : ℝ => ∫ x in a..d, (x - a) * q x)
      (fun a => (∫ x in a..d, x * q x) - a * ∫ x in a..d, q x) (uIcc c d) := by
    intro a ha
    change (∫ x in a..d, (x - a) * q x) =
      (∫ x in a..d, x * q x) - a * ∫ x in a..d, q x
    rw [show (fun x : ℝ => (x - a) * q x) =
        (fun x => x * q x - a * q x) by funext x; ring,
      intervalIntegral.integral_sub]
    · rw [intervalIntegral.integral_const_mul]
    · exact hxqInt.mono_set (uIcc_subset_uIcc_right ha)
    · exact (hqInt.const_mul a).mono_set (uIcc_subset_uIcc_right ha)
  refine (hprimxq.sub (continuousOn_id.mul hprimq)).congr ?_
  intro a ha
  simpa only [Pi.sub_apply, Pi.mul_apply, id_eq] using hdecomp ha

/-- Boundary expression in the weighted Littlewood identity, viewed as a function of its left
edge. -/
def weightedLittlewoodBoundary (f : ℂ → ℂ) (a d T₁ T₂ : ℝ) : ℝ :=
  (∫ t in T₁..T₂, Real.log ‖f ((a : ℂ) + t * I)‖)
    - (∫ t in T₁..T₂, Real.log ‖f ((d : ℂ) + t * I)‖)
    + (d - a) * (∫ t in T₁..T₂, (logDeriv f ((d : ℂ) + t * I)).re)
    + (∫ x in a..d, (x - a) * (logDeriv f ((x : ℂ) + T₁ * I)).im)
    - ∫ x in a..d, (x - a) * (logDeriv f ((x : ℂ) + T₂ * I)).im

theorem continuousWithinAt_weightedLittlewoodBoundary_left
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ)
    (hne : ∃ z : ℂ, f z ≠ 0) {c d T₁ T₂ : ℝ} (hcd : c < d)
    (hbot : ∀ x ∈ uIcc c d, f ((x : ℂ) + T₁ * I) ≠ 0)
    (htop : ∀ x ∈ uIcc c d, f ((x : ℂ) + T₂ * I) ≠ 0) :
    ContinuousWithinAt (fun a => weightedLittlewoodBoundary f a d T₁ T₂) (Icc c d) c := by
  have hqbot : ContinuousOn
      (fun x : ℝ => (logDeriv f ((x : ℂ) + T₁ * I)).im) (uIcc c d) := by
    intro x hx
    have hA : AnalyticAt ℂ (logDeriv f) ((x : ℂ) + T₁ * I) := by
      rw [show logDeriv f = fun z => deriv f z / f z from rfl]
      exact (hf _ (Set.mem_univ _)).deriv.div (hf _ (Set.mem_univ _)) (hbot x hx)
    have hc := ContinuousAt.comp (f := fun y : ℝ => (y : ℂ) + T₁ * I)
      hA.continuousAt (by fun_prop : ContinuousAt (fun y : ℝ => (y : ℂ) + T₁ * I) x)
    exact (Complex.continuous_im.continuousAt.comp hc).continuousWithinAt
  have hqtop : ContinuousOn
      (fun x : ℝ => (logDeriv f ((x : ℂ) + T₂ * I)).im) (uIcc c d) := by
    intro x hx
    have hA : AnalyticAt ℂ (logDeriv f) ((x : ℂ) + T₂ * I) := by
      rw [show logDeriv f = fun z => deriv f z / f z from rfl]
      exact (hf _ (Set.mem_univ _)).deriv.div (hf _ (Set.mem_univ _)) (htop x hx)
    have hc := ContinuousAt.comp (f := fun y : ℝ => (y : ℂ) + T₂ * I)
      hA.continuousAt (by fun_prop : ContinuousAt (fun y : ℝ => (y : ℂ) + T₂ * I) x)
    exact (Complex.continuous_im.continuousAt.comp hc).continuousWithinAt
  have hbotW := continuousOn_weighted_left_endpoint_integral hqbot
  have htopW := continuousOn_weighted_left_endpoint_integral hqtop
  rw [uIcc_of_le hcd.le] at hbotW htopW
  have hslice : ContinuousWithinAt (fun a : ℝ =>
      ∫ t in T₁..T₂, Real.log ‖f ((a : ℂ) + t * I)‖) (Icc c d) c :=
    (continuousAt_verticalIntegral_log_norm_of_entire hf hne T₁ T₂ c).continuousWithinAt
  have hrightLog : ContinuousWithinAt (fun _ : ℝ =>
      ∫ t in T₁..T₂, Real.log ‖f ((d : ℂ) + t * I)‖) (Icc c d) c :=
    continuousWithinAt_const
  have hrightDeriv : ContinuousWithinAt (fun _ : ℝ =>
      ∫ t in T₁..T₂, (logDeriv f ((d : ℂ) + t * I)).re) (Icc c d) c :=
    continuousWithinAt_const
  have hdminus : ContinuousWithinAt (fun a : ℝ => d - a) (Icc c d) c := by fun_prop
  have hcombined : ContinuousWithinAt (fun a : ℝ =>
      (∫ t in T₁..T₂, Real.log ‖f ((a : ℂ) + t * I)‖)
        - (∫ t in T₁..T₂, Real.log ‖f ((d : ℂ) + t * I)‖)
        + (d - a) * (∫ t in T₁..T₂, (logDeriv f ((d : ℂ) + t * I)).re)
        + (∫ x in a..d, (x - a) * (logDeriv f ((x : ℂ) + T₁ * I)).im)
        - ∫ x in a..d, (x - a) * (logDeriv f ((x : ℂ) + T₂ * I)).im)
      (Icc c d) c := ((((hslice.sub hrightLog).add
    (hdminus.mul hrightDeriv)).add
      (hbotW c (Set.mem_Icc.mpr ⟨le_rfl, hcd.le⟩))).sub
        (htopW c (Set.mem_Icc.mpr ⟨le_rfl, hcd.le⟩)))
  simpa only [weightedLittlewoodBoundary] using hcombined

theorem eventually_left_edge_lt_iff_lt_of_finset
    {Z : Finset ℂ} {c d : ℝ} (hleft : ∀ w ∈ Z, c ≤ w.re) :
    ∀ᶠ a in 𝓝[Ioc c d] c, ∀ w ∈ Z, (a < w.re ↔ c < w.re) := by
  apply (eventually_all_finset Z).2
  intro w hw
  rcases (hleft w hw).eq_or_lt with hEq | hlt
  · rw [← hEq]
    filter_upwards [self_mem_nhdsWithin] with a ha
    exact ⟨fun h => ((not_lt_of_ge ha.1.le) h).elim,
      fun h => ((lt_irrefl c) h).elim⟩
  · filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hlt)] with a ha
    exact ⟨fun _ => hlt, fun _ => ha⟩

/-- Weighted Littlewood identity with no nonvanishing assumption on the left edge. Zeros on that
edge have zero horizontal weight, and are recovered by a right-hand limiting contour. -/
theorem exists_entire_weighted_littlewood_rectangle_allow_left_zeros
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ)
    (hne : ∃ z : ℂ, f z ≠ 0)
    {c d T₁ T₂ : ℝ} (hcd : c < d) (hT : T₁ < T₂)
    (hbot : ∀ x ∈ uIcc c d, f ((x : ℂ) + T₁ * I) ≠ 0)
    (htop : ∀ x ∈ uIcc c d, f ((x : ℂ) + T₂ * I) ≠ 0)
    (hright : ∀ t ∈ uIcc T₁ T₂, f ((d : ℂ) + t * I) ≠ 0) :
    ∃ Z : Finset ℂ,
      (∀ z : ℂ, z ∈ Z ↔
        z ∈ (uIcc c d ×ℂ uIcc T₁ T₂) ∧ f z = 0) ∧
      2 * Real.pi *
          (∑ w ∈ Z, ((analyticOrderAt f w).toNat : ℝ) * (w.re - c)) =
        weightedLittlewoodBoundary f c d T₁ T₂ := by
  classical
  let z₁ : ℂ := (c : ℂ) + T₁ * I
  let z₂ : ℂ := (d : ℂ) + T₂ * I
  let hfinite : {z ∈ (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) |
      f z = 0}.Finite := entire_zeros_closedRectangle_finite hf hne z₁ z₂
  let Z : Finset ℂ := hfinite.toFinset
  have hmem (z : ℂ) : z ∈ Z ↔
      z ∈ (uIcc c d ×ℂ uIcc T₁ T₂) ∧ f z = 0 := by
    change z ∈ hfinite.toFinset ↔ _
    rw [Set.Finite.mem_toFinset, Set.mem_sep_iff]
    simp [z₁, z₂]
  let Zplus : Finset ℂ := Z.filter (fun w => c < w.re)
  have hleftbound : ∀ w ∈ Z, c ≤ w.re := by
    intro w hw
    have hwK := (hmem w).mp hw |>.1
    have hwre := Complex.mem_reProdIm.mp hwK |>.1
    rw [uIcc_of_le hcd.le] at hwre
    exact hwre.1
  have hstable : ∀ᶠ a in 𝓝[Ioc c d] c,
      ∀ w ∈ Z, (a < w.re ↔ c < w.re) :=
    eventually_left_edge_lt_iff_lt_of_finset hleftbound
  let Fmass : ℝ → ℝ := fun a => 2 * Real.pi *
    ∑ w ∈ Zplus, ((analyticOrderAt f w).toNat : ℝ) * (w.re - a)
  have hFmass : Continuous Fmass := by
    dsimp only [Fmass]
    exact continuous_const.mul (continuous_finsetSum Zplus fun w _ => by fun_prop)
  have hboundary := continuousWithinAt_weightedLittlewoodBoundary_left hf hne hcd hbot htop
  have heq : Fmass =ᶠ[𝓝[Ioc c d] c]
      (fun a => weightedLittlewoodBoundary f a d T₁ T₂) := by
    filter_upwards [self_mem_nhdsWithin, hstable,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hcd)] with a ha haStable hacd
    have hbot' : ∀ x ∈ uIcc a d, f ((x : ℂ) + T₁ * I) ≠ 0 := by
      intro x hx
      apply hbot x
      rw [uIcc_of_le hacd.le] at hx
      rw [uIcc_of_le hcd.le]
      exact ⟨ha.1.le.trans hx.1, hx.2⟩
    have htop' : ∀ x ∈ uIcc a d, f ((x : ℂ) + T₂ * I) ≠ 0 := by
      intro x hx
      apply htop x
      rw [uIcc_of_le hacd.le] at hx
      rw [uIcc_of_le hcd.le]
      exact ⟨ha.1.le.trans hx.1, hx.2⟩
    have hleft' : ∀ t ∈ uIcc T₁ T₂, f ((a : ℂ) + t * I) ≠ 0 := by
      intro t ht hzero
      let w : ℂ := (a : ℂ) + t * I
      have hwK : w ∈ (uIcc c d ×ℂ uIcc T₁ T₂) := by
        apply Complex.mem_reProdIm.mpr
        constructor
        · rw [uIcc_of_le hcd.le]
          simpa [w] using (show c ≤ a ∧ a ≤ d from ⟨ha.1.le, hacd.le⟩)
        · simpa [w] using ht
      have hwZ : w ∈ Z := (hmem w).mpr ⟨hwK, hzero⟩
      have hcwr : c < w.re := by simpa [w] using ha.1
      have hcontra : a < a := by
        simpa [w] using (haStable w hwZ).mpr hcwr
      exact (lt_irrefl a) hcontra
    obtain ⟨Z', hZ'mem, hident⟩ :=
      exists_entire_weighted_littlewood_rectangle hf hne hacd hT hbot' htop' hright hleft'
    have hZZ : Z' = Zplus := by
      ext w
      rw [hZ'mem w, Finset.mem_filter, hmem w]
      constructor
      · intro hw
        obtain ⟨hwK', hwzero⟩ := hw
        obtain ⟨hwre', hwim'⟩ := Complex.mem_reProdIm.mp hwK'
        rw [uIcc_of_le hacd.le] at hwre'
        have hwK : w ∈ (uIcc c d ×ℂ uIcc T₁ T₂) := by
          apply Complex.mem_reProdIm.mpr
          constructor
          · rw [uIcc_of_le hcd.le]
            exact ⟨ha.1.le.trans hwre'.1, hwre'.2⟩
          · exact hwim'
        have hwZ : w ∈ Z := (hmem w).mpr ⟨hwK, hwzero⟩
        have haw : a < w.re := by
          apply lt_of_le_of_ne hwre'.1
          intro haweq
          have hedge : (a : ℂ) + w.im * I = w := by
            apply Complex.ext <;> simp [haweq]
          have hz : f ((a : ℂ) + w.im * I) = 0 := by
            rw [hedge]
            exact hwzero
          exact hleft' w.im hwim' hz
        exact ⟨⟨hwK, hwzero⟩, (haStable w hwZ).mp haw⟩
      · intro hw
        obtain ⟨⟨hwK, hwzero⟩, hcwr⟩ := hw
        obtain ⟨hwre, hwim⟩ := Complex.mem_reProdIm.mp hwK
        rw [uIcc_of_le hcd.le] at hwre
        have haw : a < w.re := (haStable w ((hmem w).mpr ⟨hwK, hwzero⟩)).mpr hcwr
        constructor
        · apply Complex.mem_reProdIm.mpr
          constructor
          · rw [uIcc_of_le hacd.le]
            exact ⟨haw.le, hwre.2⟩
          · exact hwim
        · exact hwzero
    rw [hZZ] at hident
    simpa only [Fmass, weightedLittlewoodBoundary] using hident
  have hFmassWithin : ContinuousWithinAt Fmass (Ioc c d) c :=
    hFmass.continuousAt.continuousWithinAt
  have hboundaryWithin : ContinuousWithinAt
      (fun a => weightedLittlewoodBoundary f a d T₁ T₂) (Ioc c d) c :=
    hboundary.mono Ioc_subset_Icc_self
  haveI : NeBot (𝓝[Ioc c d] c) := left_nhdsWithin_Ioc_neBot hcd
  have hvalue : Fmass c = weightedLittlewoodBoundary f c d T₁ T₂ := by
    exact tendsto_nhds_unique hFmassWithin
      (Tendsto.congr' heq.symm hboundaryWithin)
  have hmass :
      (∑ w ∈ Zplus, ((analyticOrderAt f w).toNat : ℝ) * (w.re - c)) =
      ∑ w ∈ Z, ((analyticOrderAt f w).toNat : ℝ) * (w.re - c) := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro w hwZ hwNot
    have hnot : ¬ c < w.re := by
      intro hlt
      exact hwNot (by simp [hwZ, hlt])
    have heqre : w.re = c := le_antisymm (le_of_not_gt hnot) (hleftbound w hwZ)
    simp [heqre]
  refine ⟨Z, hmem, ?_⟩
  dsimp only [Fmass] at hvalue
  rw [← hmass]
  exact hvalue

theorem exists_entire_weighted_littlewood_rectangle_left_boundary_zeros
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ)
    (hne : ∃ z : ℂ, f z ≠ 0)
    {c d T₁ T₂ : ℝ} (hcd : c < d) (hT : T₁ < T₂)
    (hbot : ∀ x ∈ uIcc c d, f ((x : ℂ) + T₁ * I) ≠ 0)
    (htop : ∀ x ∈ uIcc c d, f ((x : ℂ) + T₂ * I) ≠ 0)
    (hright : ∀ t ∈ uIcc T₁ T₂, f ((d : ℂ) + t * I) ≠ 0) :
    ∃ Z : Finset ℂ,
      (∀ z : ℂ, z ∈ Z ↔
        z ∈ (uIcc c d ×ℂ uIcc T₁ T₂) ∧ f z = 0) ∧
      2 * Real.pi *
          (∑ w ∈ Z, ((analyticOrderAt f w).toNat : ℝ) * (w.re - c)) =
        (∫ t in T₁..T₂, Real.log ‖f ((c : ℂ) + t * I)‖)
          - (∫ t in T₁..T₂, Real.log ‖f ((d : ℂ) + t * I)‖)
          + (d - c) *
            (∫ t in T₁..T₂, (logDeriv f ((d : ℂ) + t * I)).re)
          + (∫ x in c..d,
            (x - c) * (logDeriv f ((x : ℂ) + T₁ * I)).im)
          - ∫ x in c..d,
            (x - c) * (logDeriv f ((x : ℂ) + T₂ * I)).im := by
  obtain ⟨Z, hZ, hident⟩ :=
    exists_entire_weighted_littlewood_rectangle_allow_left_zeros
      hf hne hcd hT hbot htop hright
  exact ⟨Z, hZ, by simpa only [weightedLittlewoodBoundary] using hident⟩

end

end RHTower

