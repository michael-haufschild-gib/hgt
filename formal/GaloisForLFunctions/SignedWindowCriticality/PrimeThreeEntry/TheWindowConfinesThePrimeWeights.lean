import GaloisForLFunctions.SignedWindowCriticality.BelowLogFour.RetainedVarianceAndHalfWindowBandBelowLogFour

/-!
# The window confines the prime weights

Below `log 4` the window `[−c, c]` reads the arithmetic through the weight pair `(w₂, w₃)` of the
half-window band, and `belowLogFourBandWeights c` is the convex set of admissible pairs. As soon as a
prime acts, the window bounds its weight from both sides: a bump centred at the midpoint
`−½ log n` of the collar sliver of `n` is symmetric under the reflection `u ↦ −log n − u`, so its
reflection term `(f⋆f)(−log n) = ∫ f²` is positive, while for `2c < log 4` its reflection at the
other prime misses its support. The band on this one test pins `w_n` between
`(𝓗₀(f) ∓ W(f))/(f⋆f)(−log n)`:

* `exists_bounds_snd_of_lt` (`½ log 3 < c < log 2`): `w₃` lies in a bounded interval;
* `exists_bounds_fst_of_lt` (`½ log 2 < c < log 2`): `w₂` lies in a bounded interval;
* `isCompact_belowLogFourBandWeights` (`½ log 3 < c < log 2`): the admissible set is compact.

Before the entry of `3` (`2c ≤ log 3`) the set is a cylinder in `w₃`
(`PrimeThreeEntry.mem_oddBandWeights_iff_of_le`), and just after it the `w₃`-range is wide
(`PrimeThreeEntry.mem_bandWeights_of_margin_log`); from then on it is a compact interval.
-/

open MeasureTheory Set Filter
open scoped Real

noncomputable section

namespace GaloisForLFunctions.SignedWindowCriticality.PrimeThreeEntry

open GaloisForLFunctions.SignedWindowCriticality
open GaloisForLFunctions.SignedWindowCriticality.BelowLogFour
open GaloisForLFunctions.SpacingScaleHarmonicAnalysis
open _root_.RHTower

/-- The bump of radius `r` centred at `m`. -/
def sliverBump (m r : ℝ) (u : ℝ) : ℝ := centreBump ((u - m) / r)

theorem contDiff_sliverBump (m r : ℝ) : ContDiff ℝ 2 (sliverBump m r) :=
  contDiff_centreBump.comp ((contDiff_id.sub contDiff_const).div_const r)

theorem sliverBump_eq_zero {m r u : ℝ} (hr : 0 < r) (hu : r ≤ |u - m|) : sliverBump m r u = 0 := by
  apply centreBump_eq_zero
  rw [abs_div, abs_of_pos hr, one_le_div hr]; exact hu

/-- The bump is symmetric about its centre: `f(2m − u) = f(u)`. -/
theorem sliverBump_reflect (m r u : ℝ) : sliverBump m r (2 * m - u) = sliverBump m r u := by
  unfold sliverBump
  rw [show (2 * m - u - m) / r = -((u - m) / r) by ring, centreBump_neg]

/-- The reflection term of the bump at its own centre is its mass: `(f⋆f)(2m) = ∫ f² > 0`. -/
theorem selfConv_sliverBump_pos {m r : ℝ} (hr : 0 < r) :
    0 < selfConv (sliverBump m r) (2 * m) := by
  have he : selfConv (sliverBump m r) (2 * m) = ∫ u, sliverBump m r u ^ 2 := by
    unfold selfConv
    exact integral_congr_ae (Eventually.of_forall fun u => by
      show sliverBump m r u * sliverBump m r (2 * m - u) = sliverBump m r u ^ 2
      rw [sliverBump_reflect, sq])
  rw [he]
  have hc : Continuous fun u => sliverBump m r u ^ 2 := (contDiff_sliverBump m r).continuous.pow 2
  have hcs : HasCompactSupport fun u => sliverBump m r u ^ 2 :=
    HasCompactSupport.intro (isCompact_Icc (a := m - r) (b := m + r)) fun u hu => by
      have : r ≤ |u - m| := by
        simp only [mem_Icc, not_and_or, not_le] at hu
        rcases hu with h | h
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith
      rw [sliverBump_eq_zero hr this]; norm_num
  have hpos : 0 < sliverBump m r m ^ 2 := by
    unfold sliverBump; rw [sub_self, zero_div, centreBump_eq_one (by norm_num)]; norm_num
  exact hc.integral_pos_of_hasCompactSupport_nonneg_nonzero hcs (fun u => sq_nonneg _) hpos.ne'

/-- Two bumps whose supports are farther apart than `2r` do not meet:
`(f⋆f)(s) = 0` when `|s − 2m| ≥ 2r`. -/
theorem selfConv_sliverBump_eq_zero {m r s : ℝ} (hr : 0 < r) (hs : 2 * r ≤ |s - 2 * m|) :
    selfConv (sliverBump m r) s = 0 := by
  unfold selfConv
  refine integral_eq_zero_of_ae (Eventually.of_forall fun u => ?_)
  simp only [Pi.zero_apply]
  by_cases hu : r ≤ |u - m|
  · rw [sliverBump_eq_zero hr hu, zero_mul]
  · have : r ≤ |s - u - m| := by
      have h1 : |s - 2 * m| ≤ |s - u - m| + |u - m| := by
        rw [show s - 2 * m = (s - u - m) + (u - m) by ring]
        exact abs_add _ _
      linarith [not_le.mp hu]
    rw [sliverBump_eq_zero hr this, mul_zero]

/-- The band on one test `f` with `(f⋆f)(−log 2) = 0` and `(f⋆f)(−log 3) > 0` pins `w₃`. -/
private lemma snd_bounds_of_test {c : ℝ} {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (h0 : ∀ u, 0 < u → f u = 0) (hfc : ∀ u, u < -c → f u = 0)
    (h2 : selfConv f (-Real.log 2) = 0) (h3 : 0 < selfConv f (-Real.log 3))
    {w : ℝ × ℝ} (hw : w ∈ belowLogFourBandWeights c) :
    (collarHankel 0 f - weilQuad f) / selfConv f (-Real.log 3) ≤ w.2 ∧
      w.2 ≤ (collarHankel 0 f + weilQuad f) / selfConv f (-Real.log 3) := by
  have hb := abs_le.mp (hw f hf h0 hfc)
  rw [h2, mul_zero, sub_zero] at hb
  constructor
  · rw [div_le_iff₀ h3]; linarith [hb.2]
  · rw [le_div_iff₀ h3]; linarith [hb.1]

private lemma fst_bounds_of_test {c : ℝ} {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (h0 : ∀ u, 0 < u → f u = 0) (hfc : ∀ u, u < -c → f u = 0)
    (h3 : selfConv f (-Real.log 3) = 0) (h2 : 0 < selfConv f (-Real.log 2))
    {w : ℝ × ℝ} (hw : w ∈ belowLogFourBandWeights c) :
    (collarHankel 0 f - weilQuad f) / selfConv f (-Real.log 2) ≤ w.1 ∧
      w.1 ≤ (collarHankel 0 f + weilQuad f) / selfConv f (-Real.log 2) := by
  have hb := abs_le.mp (hw f hf h0 hfc)
  rw [h3, mul_zero, sub_zero] at hb
  constructor
  · rw [div_le_iff₀ h2]; linarith [hb.2]
  · rw [le_div_iff₀ h2]; linarith [hb.1]

/-- Support of a centred bump inside `[−c, 0]`. -/
private lemma sliverBump_supp {c m r : ℝ} (hr : 0 < r) (hl : -c ≤ m - r) (hr0 : m + r ≤ 0) :
    (∀ u, 0 < u → sliverBump m r u = 0) ∧ (∀ u, u < -c → sliverBump m r u = 0) :=
  ⟨fun u hu => sliverBump_eq_zero hr (by rw [abs_of_pos (by linarith)]; linarith),
    fun u hu => sliverBump_eq_zero hr (by rw [abs_of_neg (by linarith)]; linarith)⟩

/-- **Once the prime `3` acts, the window bounds `w₃`.** For `½ log 3 < c < log 2` there are
`L ≤ U` with `L ≤ w₃ ≤ U` for every admissible pair. -/
theorem exists_bounds_snd_of_lt {c : ℝ} (hc3 : Real.log 3 < 2 * c) (hc : c < Real.log 2) :
    ∃ L U : ℝ, ∀ w ∈ belowLogFourBandWeights c, L ≤ w.2 ∧ w.2 ≤ U := by
  have hl2 := Real.log_two_gt_d9
  have hl3 := Real.log_three_lt_d9
  have hl3' := Real.log_three_gt_d9
  set m : ℝ := -(Real.log 3 / 2)
  set r : ℝ := (2 * c - Real.log 3) / 4
  have hr : 0 < r := by simp only [r]; linarith
  have hsupp := sliverBump_supp (c := c) (m := m) hr (by simp only [m, r]; linarith)
    (by simp only [m, r]; linarith)
  have h3 : 0 < selfConv (sliverBump m r) (-Real.log 3) := by
    have := selfConv_sliverBump_pos (m := m) hr
    rwa [show 2 * m = -Real.log 3 by simp only [m]; ring] at this
  have h2 : selfConv (sliverBump m r) (-Real.log 2) = 0 :=
    selfConv_sliverBump_eq_zero hr (by
      simp only [m, r]
      rw [abs_of_pos (by linarith)]; linarith)
  exact ⟨_, _, fun w hw => snd_bounds_of_test (contDiff_sliverBump m r) hsupp.1 hsupp.2 h2 h3 hw⟩

/-- **Once the prime `2` acts, the window bounds `w₂`.** For `½ log 2 < c < log 2`. -/
theorem exists_bounds_fst_of_lt {c : ℝ} (hc2 : Real.log 2 < 2 * c) (hc : c < Real.log 2) :
    ∃ L U : ℝ, ∀ w ∈ belowLogFourBandWeights c, L ≤ w.1 ∧ w.1 ≤ U := by
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hl3 := Real.log_three_gt_d9
  set m : ℝ := -(Real.log 2 / 2)
  set r : ℝ := min ((2 * c - Real.log 2) / 4) (1 / 20)
  have hr : 0 < r := lt_min (by linarith) (by norm_num)
  have hr1 : r ≤ (2 * c - Real.log 2) / 4 := min_le_left _ _
  have hr2 : r ≤ 1 / 20 := min_le_right _ _
  have hsupp := sliverBump_supp (c := c) (m := m) hr (by simp only [m]; linarith)
    (by simp only [m]; linarith)
  have h2 : 0 < selfConv (sliverBump m r) (-Real.log 2) := by
    have := selfConv_sliverBump_pos (m := m) hr
    rwa [show 2 * m = -Real.log 2 by simp only [m]; ring] at this
  have h3 : selfConv (sliverBump m r) (-Real.log 3) = 0 :=
    selfConv_sliverBump_eq_zero hr (by
      simp only [m]
      rw [abs_of_neg (by linarith)]; linarith)
  exact ⟨_, _, fun w hw => fst_bounds_of_test (contDiff_sliverBump m r) hsupp.1 hsupp.2 h3 h2 hw⟩

theorem isClosed_belowLogFourBandWeights (c : ℝ) : IsClosed (belowLogFourBandWeights c) := by
  have : belowLogFourBandWeights c = ⋂ f ∈ {f : ℝ → ℝ | ContDiff ℝ 2 f ∧ (∀ u, 0 < u → f u = 0) ∧
      (∀ u, u < -c → f u = 0)}, {w : ℝ × ℝ | |collarHankel 0 f - w.1 * selfConv f (-Real.log 2) -
        w.2 * selfConv f (-Real.log 3)| ≤ weilQuad f} := by
    ext w
    simp only [belowLogFourBandWeights, mem_setOf_eq, mem_iInter]
    exact ⟨fun h f hf => h f hf.1 hf.2.1 hf.2.2, fun h f hf h0 hfc => h f ⟨hf, h0, hfc⟩⟩
  rw [this]
  refine isClosed_biInter fun f _ => isClosed_le ?_ continuous_const
  fun_prop

/-- **Once the prime `3` acts, the admissible set is compact.** For `½ log 3 < c < log 2`,
`belowLogFourBandWeights c` is a compact convex subset of `ℝ²`. -/
theorem isCompact_belowLogFourBandWeights {c : ℝ} (hc3 : Real.log 3 < 2 * c)
    (hc : c < Real.log 2) :
    IsCompact (belowLogFourBandWeights c) ∧ Convex ℝ (belowLogFourBandWeights c) := by
  have hc2 : Real.log 2 < 2 * c := by
    have := Real.log_lt_log (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) < 3)
    linarith
  obtain ⟨L₂, U₂, h₂⟩ := exists_bounds_fst_of_lt hc2 hc
  obtain ⟨L₃, U₃, h₃⟩ := exists_bounds_snd_of_lt hc3 hc
  have hsub : belowLogFourBandWeights c ⊆ Icc L₂ U₂ ×ˢ Icc L₃ U₃ := fun w hw =>
    ⟨⟨(h₂ w hw).1, (h₂ w hw).2⟩, ⟨(h₃ w hw).1, (h₃ w hw).2⟩⟩
  have hbd : Bornology.IsBounded (belowLogFourBandWeights c) :=
    ((Metric.isBounded_Icc L₂ U₂).prod (Metric.isBounded_Icc L₃ U₃)).subset hsub
  exact ⟨Metric.isCompact_of_isClosed_isBounded (isClosed_belowLogFourBandWeights c) hbd,
    convex_belowLogFourBandWeights c⟩

end GaloisForLFunctions.SignedWindowCriticality.PrimeThreeEntry

end
