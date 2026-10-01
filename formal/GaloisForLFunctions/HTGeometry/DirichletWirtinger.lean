import GaloisForLFunctions.HTGeometry.CirclePoincareWirtinger

/-!
# Wirtinger's inequality with Dirichlet boundary conditions

If `f(a) = f(b) = 0` and `f` is `C¹` on `[a, b]`, then
`∫_a^b |f|² ≤ ((b - a)/π)² ∫_a^b |f'|²`, with the sharp constant (equality for `sin(π(x-a)/(b-a))`).

The proof reflects `f` oddly about `b` to a function on `[a, 2b - a]` that is periodic, has mean
zero and a continuous derivative, and applies the periodic Wirtinger inequality on the doubled
interval.
-/

open MeasureTheory intervalIntegral Set Complex Real

namespace GaloisForLFunctions.HTGeometry

/-- Sharp Wirtinger inequality for functions vanishing at both endpoints. -/
theorem dirichlet_wirtinger_intervalIntegral {a b : ℝ} (hab : a < b) {f f' : ℝ → ℂ}
    (hf : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x) (hf'c : ContinuousOn f' (Icc a b))
    (ha : f a = 0) (hb : f b = 0) :
    ∫ x in a..b, ‖f x‖ ^ 2 ≤ ((b - a) / π) ^ 2 * ∫ x in a..b, ‖f' x‖ ^ 2 := by
  set c : ℝ := 2 * b - a with hc
  have hbc : b < c := by rw [hc]; linarith
  have hac : a < c := by linarith
  set g : ℝ → ℂ := fun x => if x ≤ b then f x else -f (2 * b - x) with hg
  set r : ℝ → ℝ := fun x => b - |x - b| with hr
  set g' : ℝ → ℂ := fun x => f' (r x) with hg'
  have hrmem : ∀ x ∈ uIcc a c, r x ∈ Icc a b := by
    intro x hx
    rw [uIcc_of_le hac.le] at hx
    simp only [hr, mem_Icc]
    constructor
    · rcases le_or_gt x b with h | h
      · rw [abs_of_nonpos (by linarith)]; linarith [hx.1]
      · rw [abs_of_pos (by linarith)]; linarith [hx.2]
    · linarith [abs_nonneg (x - b)]
  -- derivative of the odd reflection
  have hderR : ∀ x ∈ Icc b c, HasDerivAt (fun y => -f (2 * b - y)) (f' (2 * b - x)) x := by
    intro x hx
    have hmem : 2 * b - x ∈ Icc a b := ⟨by rw [hc] at hx; linarith [hx.2], by linarith [hx.1]⟩
    have h1 := (hf _ hmem).scomp x ((hasDerivAt_id x).const_sub (2 * b))
    convert h1.neg using 1 <;> first | (ext y; simp) | simp
  have hgd : ∀ x ∈ uIcc a c, HasDerivAt g (g' x) x := by
    intro x hx
    rw [uIcc_of_le hac.le] at hx
    rcases lt_trichotomy x b with h | h | h
    · have hrx : r x = x := by simp only [hr]; rw [abs_of_neg (by linarith)]; ring
      rw [show g' x = f' x by simp only [hg', hrx]]
      refine (hf x ⟨hx.1, h.le⟩).congr_of_eventuallyEq ?_
      filter_upwards [Iio_mem_nhds h] with y hy
      simp only [hg, if_pos (mem_Iio.mp hy).le]
    · have hrx : r x = x := by simp only [hr, h, sub_self, abs_zero, sub_zero]
      rw [show g' x = f' x by simp only [hg', hrx], h]
      have hL : HasDerivWithinAt g (f' b) (Iic b) b := by
        refine ((hf b ⟨hab.le, le_rfl⟩).hasDerivWithinAt).congr (fun y hy => ?_) ?_
        · simp only [hg, if_pos (mem_Iic.mp hy)]
        · simp only [hg, if_pos le_rfl]
      have hR : HasDerivWithinAt g (f' b) (Ici b) b := by
        have h0 := (hderR b ⟨le_rfl, hbc.le⟩).hasDerivWithinAt (s := Ici b)
        rw [show 2 * b - b = b by ring] at h0
        refine h0.congr (fun y hy => ?_) ?_
        · rcases eq_or_lt_of_le (mem_Ici.mp hy) with h' | h'
          · rw [← h']; simp only [hg, if_pos le_rfl, show 2 * b - b = b by ring, hb, neg_zero]
          · simp only [hg, if_neg (not_le.mpr h')]
        · simp only [hg, if_pos le_rfl, show 2 * b - b = b by ring, hb, neg_zero]
      have := hL.union hR
      rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this
    · have hrx : r x = 2 * b - x := by simp only [hr]; rw [abs_of_pos (by linarith)]; ring
      rw [show g' x = f' (2 * b - x) by simp only [hg', hrx]]
      refine (hderR x ⟨h.le, hx.2⟩).congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds h] with y hy
      simp only [hg, if_neg (not_le.mpr (mem_Ioi.mp hy))]
  have hg'c : ContinuousOn g' (uIcc a c) :=
    hf'c.comp (by fun_prop) (fun x hx => hrmem x hx)
  have hper : g c = g a := by
    have hca0 : 2 * b - c = a := by rw [hc]; ring
    simp only [hg, if_neg (not_le.mpr hbc), if_pos hab.le, hca0, ha, neg_zero]
  have W := wirtinger_intervalIntegral hac hgd hg'c hper
  have hgc : ContinuousOn g (uIcc a c) := fun x hx => (hgd x hx).continuousAt.continuousWithinAt
  have hsub1 : uIcc a b ⊆ uIcc a c := by
    rw [uIcc_of_le hab.le, uIcc_of_le hac.le]; exact Icc_subset_Icc le_rfl hbc.le
  have hsub2 : uIcc b c ⊆ uIcc a c := by
    rw [uIcc_of_le hbc.le, uIcc_of_le hac.le]; exact Icc_subset_Icc hab.le le_rfl
  have iG : IntervalIntegrable (fun x => ‖g x‖ ^ 2) volume a c :=
    (hgc.norm.pow 2).intervalIntegrable
  have iG' : IntervalIntegrable (fun x => ‖g' x‖ ^ 2) volume a c :=
    (hg'c.norm.pow 2).intervalIntegrable
  have iG1 : IntervalIntegrable g volume a c := hgc.intervalIntegrable
  have hca : 2 * b - c = a := by rw [hc]; ring
  have hbb : 2 * b - b = b := by ring
  have left : ∀ x ∈ uIcc a b, x ≤ b := fun x hx => by
    rw [uIcc_of_le hab.le] at hx; exact hx.2
  have right : ∀ x ∈ uIcc b c, b ≤ x := fun x hx => by
    rw [uIcc_of_le hbc.le] at hx; exact hx.1
  have rL : ∀ x ∈ uIcc a b, r x = x := fun x hx => by
    simp only [hr]; rw [abs_of_nonpos (by linarith [left x hx])]; ring
  have rR : ∀ x ∈ uIcc b c, r x = 2 * b - x := fun x hx => by
    simp only [hr]; rw [abs_of_nonneg (by linarith [right x hx])]; ring
  have gR : ∀ x ∈ uIcc b c, g x = -f (2 * b - x) := fun x hx => by
    rcases eq_or_lt_of_le (right x hx) with h' | h'
    · rw [← h']; simp only [hg, if_pos le_rfl, hbb, hb, neg_zero]
    · simp only [hg, if_neg (not_le.mpr h')]
  have I1 : ∫ x in a..c, ‖g x‖ ^ 2 = 2 * ∫ x in a..b, ‖f x‖ ^ 2 := by
    rw [← integral_add_adjacent_intervals (iG.mono_set hsub1) (iG.mono_set hsub2),
      integral_congr (a := a) (b := b) (g := fun x => ‖f x‖ ^ 2) (fun x hx => by simp only [hg, if_pos (left x hx)]),
      integral_congr (a := b) (b := c) (g := fun x => ‖f (2 * b - x)‖ ^ 2)
        (fun x hx => by simp only [gR x hx, norm_neg]),
      integral_comp_sub_left (fun y => ‖f y‖ ^ 2), hca, hbb]
    ring
  have I2 : ∫ x in a..c, ‖g' x‖ ^ 2 = 2 * ∫ x in a..b, ‖f' x‖ ^ 2 := by
    rw [← integral_add_adjacent_intervals (iG'.mono_set hsub1) (iG'.mono_set hsub2),
      integral_congr (a := a) (b := b) (g := fun x => ‖f' x‖ ^ 2) (fun x hx => by simp only [hg', rL x hx]),
      integral_congr (a := b) (b := c) (g := fun x => ‖f' (2 * b - x)‖ ^ 2) (fun x hx => by simp only [hg', rR x hx]),
      integral_comp_sub_left (fun y => ‖f' y‖ ^ 2), hca, hbb]
    ring
  have I3 : ∫ x in a..c, g x = 0 := by
    rw [← integral_add_adjacent_intervals (iG1.mono_set hsub1) (iG1.mono_set hsub2),
      integral_congr (a := a) (b := b) (g := f) (fun x hx => by simp only [hg, if_pos (left x hx)]),
      integral_congr (a := b) (b := c) (g := fun x => -f (2 * b - x)) (fun x hx => gR x hx), intervalIntegral.integral_neg,
      integral_comp_sub_left f, hca, hbb]
    ring
  rw [I1, I2, I3, smul_zero, norm_zero, show c - a = 2 * (b - a) by rw [hc]; ring] at W
  have hL : 0 < b - a := by linarith
  have key : (∫ x in a..b, ‖f x‖ ^ 2) / (b - a)
      ≤ ((b - a) / π) ^ 2 * (∫ x in a..b, ‖f' x‖ ^ 2) / (b - a) := by
    have hpi : π ≠ 0 := Real.pi_ne_zero
    convert W using 1
    · field_simp
      try ring
    · field_simp
      try ring
  exact (div_le_div_iff_of_pos_right hL).mp key

end GaloisForLFunctions.HTGeometry
