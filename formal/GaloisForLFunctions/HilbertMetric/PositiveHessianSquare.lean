import GaloisForLFunctions.HilbertMetric.ThreePointCorrelationLocal

/-!
# A positive-Hessian entrance lemma for a quadrant

This module packages the two-variable calculus step used at a doubly coalesced correlation
corner.  If a `C²` scalar has zero value and gradient at the corner and all three coordinate
Hessian entries are strictly positive there, then it is strictly positive on a small open square
in the positive quadrant.  The deliberately stronger entrywise condition avoids any division by
an aspect ratio and is exactly what the three-point determinant supplies.
-/

open Set Filter Topology

namespace HilbertMetric

/-- A positive first jet on an interval makes a differentiable function strictly larger than its
value at the left endpoint. -/
theorem lt_right_of_firstJet_posOn
    {F F' : ℝ → ℝ}
    (hF : ∀ x, HasDerivAt F (F' x) x)
    {ε : ℝ} (hε : 0 < ε)
    (hfirst : ∀ x ∈ interior (Icc (0 : ℝ) ε), 0 < F' x) :
    ∀ x, 0 < x → x < ε → F 0 < F x := by
  have hFcont : Continuous F :=
    continuous_iff_continuousAt.mpr fun x => (hF x).continuousAt
  have hFstrict : StrictMonoOn F (Icc (0 : ℝ) ε) :=
    strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc 0 ε) hFcont.continuousOn
      (fun x _ => (hF x).hasDerivWithinAt) hfirst
  intro x hx0 hxε
  exact hFstrict ⟨le_rfl, hε.le⟩ ⟨hx0.le, hxε.le⟩ hx0

/-- Entrywise positivity of the coordinate Hessian at a zero critical corner opens a strict
positive square in the positive quadrant. -/
theorem exists_pos_square_of_coordinateHessian_pos
    {F Fx Fy Fxx Fxy Fyy : ℝ → ℝ → ℝ}
    (hFx : ∀ x y, HasDerivAt (fun z => F z y) (Fx x y) x)
    (hFy : ∀ x y, HasDerivAt (fun z => F x z) (Fy x y) y)
    (hFxx : ∀ x y, HasDerivAt (fun z => Fx z y) (Fxx x y) x)
    (hFxy : ∀ x y, HasDerivAt (fun z => Fy z y) (Fxy x y) x)
    (hFyy : ∀ x y, HasDerivAt (fun z => Fy x z) (Fyy x y) y)
    (hFxxcont : Continuous (fun p : ℝ × ℝ => Fxx p.1 p.2))
    (hFxycont : Continuous (fun p : ℝ × ℝ => Fxy p.1 p.2))
    (hFyycont : Continuous (fun p : ℝ × ℝ => Fyy p.1 p.2))
    (hFzero : F 0 0 = 0) (hFxzero : Fx 0 0 = 0) (hFyzero : Fy 0 0 = 0)
    (hFxxpos : 0 < Fxx 0 0) (hFxypos : 0 < Fxy 0 0) (hFyypos : 0 < Fyy 0 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x y : ℝ, 0 < x → x < δ → 0 < y → y < δ →
      0 < F x y := by
  let H : ℝ × ℝ → ℝ := fun p => min (Fxx p.1 p.2) (min (Fxy p.1 p.2) (Fyy p.1 p.2))
  have hHcont : Continuous H := hFxxcont.min (hFxycont.min hFyycont)
  have hHpos : 0 < H (0, 0) := by
    exact lt_min hFxxpos (lt_min hFxypos hFyypos)
  have hopen : IsOpen {p : ℝ × ℝ | 0 < H p} :=
    isOpen_lt continuous_const hHcont
  have hnhds : {p : ℝ × ℝ | 0 < H p} ∈ 𝓝 (0, 0) := hopen.mem_nhds hHpos
  rcases Metric.mem_nhds_iff.mp hnhds with ⟨r, hr, hball⟩
  let δ := r / 2
  have hδ : 0 < δ := div_pos hr (by norm_num)
  have hentries : ∀ x y : ℝ, 0 ≤ x → x < δ → 0 ≤ y → y < δ →
      0 < Fxx x y ∧ 0 < Fxy x y ∧ 0 < Fyy x y := by
    intro x y hx0 hxδ hy0 hyδ
    have hp : (x, y) ∈ Metric.ball ((0, 0) : ℝ × ℝ) r := by
      rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
      constructor
      · rw [Real.dist_eq, sub_zero, abs_of_nonneg hx0]
        exact lt_trans hxδ (by dsimp [δ]; linarith)
      · rw [Real.dist_eq, sub_zero, abs_of_nonneg hy0]
        exact lt_trans hyδ (by dsimp [δ]; linarith)
    have hmin := hball hp
    exact ⟨(lt_min_iff.mp hmin).1,
      (lt_min_iff.mp (lt_min_iff.mp hmin).2).1,
      (lt_min_iff.mp (lt_min_iff.mp hmin).2).2⟩
  refine ⟨δ, hδ, ?_⟩
  intro x y hx hxδ hy hyδ
  have hFxaxis : 0 < F x 0 := by
    exact pos_right_of_secondJet_posOn
      (fun z => hFx z 0) (fun z => hFxx z 0) hFzero hFxzero hδ
      (fun z hz => by
        have hz' : 0 < z ∧ z < δ := by
          simpa [interior_Icc, hδ.ne'] using hz
        exact (hentries z 0 hz'.1.le hz'.2 le_rfl hδ).1) x hx hxδ
  have hFyaxis : 0 < Fy x 0 := by
    have hlt := lt_right_of_firstJet_posOn
      (fun z => hFxy z 0) hδ (fun z hz => by
        have hz' : 0 < z ∧ z < δ := by
          simpa [interior_Icc, hδ.ne'] using hz
        exact (hentries z 0 hz'.1.le hz'.2 le_rfl hδ).2.1) x hx hxδ
    simpa [hFyzero] using hlt
  have hFypos : ∀ z ∈ interior (Icc (0 : ℝ) δ), 0 < Fy x z := by
    intro z hz
    have hz' : 0 < z ∧ z < δ := by
      simpa [interior_Icc, hδ.ne'] using hz
    have hlt := lt_right_of_firstJet_posOn
      (fun w => hFyy x w) hδ (fun w hw => by
        have hw' : 0 < w ∧ w < δ := by
          simpa [interior_Icc, hδ.ne'] using hw
        exact (hentries x w hx.le hxδ hw'.1.le hw'.2).2.2) z hz'.1 hz'.2
    exact lt_trans hFyaxis hlt
  have hlt := lt_right_of_firstJet_posOn (fun z => hFy x z) hδ hFypos y hy hyδ
  exact lt_trans hFxaxis hlt

end HilbertMetric
