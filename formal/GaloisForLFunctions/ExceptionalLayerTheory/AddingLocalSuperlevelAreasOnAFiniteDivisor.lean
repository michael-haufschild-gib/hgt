import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Real

/-!
# Local superlevel areas add over a finite set of singularities

On a closed observation disk a function continuous away from finitely
many interior points is bounded above off small neighborhoods of those
points. Once the level exceeds that bound the whole superlevel set is
a disjoint union. Any common normalization of the local areas then
gives the sum of their limiting coefficients.
-/

noncomputable section
open Complex Filter MeasureTheory Metric Set Topology
namespace GaloisForLFunctions.ExceptionalLayerTheory

private theorem separated (t : Finset ℂ) :
    ∃ d : ℝ, 0<d ∧ ∀ x ∈ t, ∀ y ∈ t, x≠y → d≤dist x y := by
  classical
  let P := (t.product t).filter (fun p => p.1≠p.2)
  let D := insert (1:ℝ) (P.image fun p => dist p.1 p.2)
  have hn : D.Nonempty := ⟨1,Finset.mem_insert_self ..⟩
  refine ⟨D.min' hn,?_,?_⟩
  · obtain h | h := Finset.mem_insert.mp (D.min'_mem hn)
    · rw [h]; exact one_pos
    · obtain ⟨p,hp,he⟩ := Finset.mem_image.mp h
      exact he ▸ dist_pos.mpr (Finset.mem_filter.mp hp).2
  · intro x hx y hy hxy
    exact D.min'_le _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr
      ⟨(x,y),Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx,hy⟩,hxy⟩,rfl⟩))

/-- Finite gluing of local area laws, allowing arbitrary values of the
reading at its singular points and arbitrary real normalizations. -/
theorem sum_local_superlevel_areas (f A : ℂ → ℝ) (scale : ℝ → ℝ) (c : ℂ) (R : ℝ)
    (t : Finset ℂ) (ht : ∀ x ∈ t, x∈ball c R)
    (hreg : ∀ x ∈ closedBall c R, x∉t → ContinuousAt f x)
    (hl : ∀ x : ℂ, ∃ r : ℝ, 0 < r ∧ ∀ s : ℝ, 0<s → s ≤ r →
      Tendsto (fun u : ℝ => scale u*volume.real {z | z∈ball x s ∧ u < f z})
        atTop (𝓝 (A x))) :
    Tendsto (fun u : ℝ => scale u*volume.real {z | z∈ball c R ∧ u < f z}) atTop
      (𝓝 (∑ x ∈ t, A x)) := by
  classical
  choose r hr hlocal using hl
  obtain ⟨d,hd,hsep⟩ := separated t
  let s (x : ℂ) := min (d/3) (min (r x) (R-dist x c))
  have hs (x : ℂ) (hx : x∈t) : 0<s x :=
    lt_min (by positivity) (lt_min (hr x) (sub_pos.mpr (mem_ball.mp (ht x hx))))
  have hinside (x : ℂ) : ball x (s x) ⊆ ball c R := by
    intro z hz
    have hh := (mem_ball.mp hz).trans_le ((min_le_right ..).trans (min_le_right ..) : s x≤R-dist x c)
    apply (dist_triangle z x c).trans_lt
    linarith only [hh]
  have hballs : (↑t : Set ℂ).PairwiseDisjoint (fun x => ball x (s x)) := by
    intro x hx y hy hne
    apply Set.disjoint_left.mpr
    intro z hzx hzy
    have h₁ := (mem_ball.mp hzx).trans_le (min_le_left .. : s x≤d/3)
    have h₂ := (mem_ball.mp hzy).trans_le (min_le_left .. : s y≤d/3)
    rw [dist_comm z x] at h₁
    linarith only [h₁,h₂,dist_triangle x z y,hsep x hx y hy hne,hd]
  let U := ⋃ x ∈ t, ball x (s x)
  have hU : IsOpen U := isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_ball
  let K := closedBall c R \ U
  have hK : IsCompact K := (isCompact_closedBall c R).diff hU
  have hc : ContinuousOn f K := by
    intro z hz
    apply (hreg z hz.1 ?_).continuousWithinAt
    intro hzt
    exact hz.2 (mem_iUnion.mpr ⟨z,mem_iUnion.mpr ⟨hzt,mem_ball_self (hs z hzt)⟩⟩)
  obtain ⟨B,hB⟩ := hK.bddAbove_image hc
  let M := ∑ x ∈ t, |f x|
  have hM {x : ℂ} (hx : x∈t) : f x≤M := (le_abs_self _).trans
    (Finset.single_le_sum (fun y _ => abs_nonneg (f y)) hx)
  have hsum := tendsto_finsetSum t (fun x hx =>
    hlocal x (s x) (hs x hx) ((min_le_right ..).trans (min_le_left ..)))
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop B,eventually_gt_atTop M] with u hu huM
  let V (x : ℂ) := {z | z∈ball x (s x) ∧ u < f z}
  have he : {z | z∈ball c R ∧ u < f z} = ⋃ x ∈ t, V x := by
    ext z
    constructor
    · rintro ⟨hz,hread⟩
      have hin : z∈U := by
        by_contra hout
        have hh := hB (mem_image_of_mem _ (show z∈K from ⟨ball_subset_closedBall hz,hout⟩))
        exact hu.not_ge (hread.le.trans hh)
      obtain ⟨x,hx⟩ := mem_iUnion.mp hin
      obtain ⟨hxt,hzx⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨x,mem_iUnion.mpr ⟨hxt,hzx,hread⟩⟩
    · intro hz
      obtain ⟨x,hx⟩ := mem_iUnion.mp hz
      obtain ⟨_,hV⟩ := mem_iUnion.mp hx
      exact ⟨hinside x hV.1,hV.2⟩
  have hdV : (↑t : Set ℂ).PairwiseDisjoint V := fun _ hx _ hy hn =>
    (hballs hx hy hn).mono (fun _ h => h.1) (fun _ h => h.1)
  have hop (x : ℂ) : IsOpen (V x) := by
    apply isOpen_iff_mem_nhds.mpr
    rintro z ⟨hz,hread⟩
    have hn : z∉t := fun hzt => huM.not_ge (hread.le.trans (hM hzt))
    exact inter_mem (isOpen_ball.mem_nhds hz)
      ((hreg z (ball_subset_closedBall (hinside x hz)) hn).eventually_const_lt hread)
  have hfV (x : ℂ) : volume (V x)≠⊤ :=
    ne_top_of_le_ne_top (measure_ball_lt_top (μ:=volume) (x:=x) (r:=s x)).ne
      (measure_mono fun _ h => h.1)
  rw [he,measureReal_biUnion_finset hdV (fun x _ => (hop x).measurableSet) (fun x _ => hfV x),
    Finset.mul_sum]

#print axioms sum_local_superlevel_areas
end GaloisForLFunctions.ExceptionalLayerTheory
