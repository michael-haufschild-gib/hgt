import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.DrawConstraints

/-! # A common Hamiltonian for every dilation on a chosen partition -/

open MeasureTheory Finset Set Real
namespace GaloisForLFunctions.HTGeometry.BlockDilations.AdaptiveCuts
noncomputable section
variable {n : ℕ}

/-- Expand the cut bonds once, then expand the selected packet interiors. -/
theorem expand_disjoint {ι : Type*} [DecidableEq ι] (C S : Finset ι) (h : Disjoint S C)
    (d : ℝ) (z : ι→ℝ) :
    expand (C∪S) d z=expand S d (expand C d z) := by
  funext i
  by_cases hs : i∈S
  · have hc : i∉C := fun hi => disjoint_left.mp h hs hi
    simp [expand,hs,hc]
  · simp only [expand,mem_union,hs,or_false,if_false]

/-- Bounds on the physical draw include a uniform cap on the chosen
seams and a second cap on all coefficients incident on them. -/
def cutBounds (C : Finset (PathLabel n)) (F E w R : ℝ) : Set (PathLabel n→ℝ) :=
  drawBounds ∅ F E 0 ∩ {z | ∀ i∈C, |z i|≤w} ∩ {z | ∀ i, |z i|≤R}

theorem measurable_cutBounds (C : Finset (PathLabel n)) (F E w R : ℝ) :
    MeasurableSet (cutBounds C F E w R) := by
  have hmeas (A : Finset (PathLabel n)) (v : ℝ) : MeasurableSet {z : PathLabel n→ℝ | ∀ i∈A, |z i|≤v} := by
    have he : {z : PathLabel n→ℝ | ∀ i∈A, |z i|≤v} =
        ⋂ i : ↥A, {z : PathLabel n→ℝ | |z i|≤v} := by ext z; simp
    rw [he]
    exact MeasurableSet.iInter fun i => measurableSet_le (measurable_pi_apply i.val).abs measurable_const
  apply ((measurable_drawBounds ..).inter (hmeas C w)).inter
  simpa using hmeas univ R

/-- Removing a packet dilation keeps both coefficient caps and the
energy bound. Only the lower bound on longitudinal mass loses a factor. -/
theorem cutBounds_precursor (S C : Finset (PathLabel n)) {d : ℝ} (hd : 1≤d)
    (F E w R : ℝ) (z : PathLabel n→ℝ) (hz : expand S d z∈cutBounds C F E w R) :
    z∈cutBounds C (F/d) E w R := by
  have hc (i : PathLabel n) : |z i|≤|expand S d z i| := by
    by_cases hi : i∈S
    · simpa only [expand,if_pos hi,abs_mul,abs_of_nonneg (zero_le_one.trans hd)] using
        le_mul_of_one_le_left (abs_nonneg (z i)) hd
    · rw [show expand S d z i=z i from if_neg hi]
  exact ⟨⟨drawBounds_precursor S ∅ hd F E 0 z hz.1.1,fun i hi => (hc i).trans (hz.1.2 i hi)⟩,
    fun i => (hc i).trans (hz.2 i)⟩

#print axioms expand_disjoint
#print axioms cutBounds_precursor
end
end GaloisForLFunctions.HTGeometry.BlockDilations.AdaptiveCuts
