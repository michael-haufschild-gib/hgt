import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.ReImTopology

/-!
# The maximum modulus principle on a rectangle

An entire function is bounded on a closed rectangle by its bound on the four edges.  This is the
tool that converts Burnol's height-selected estimates (`1/ζ` polynomially bounded on the selected
horizontal lines, the transform bounded on the two vertical lines) into polynomial growth on the
whole strip — the elementary substitute for Krein's theorem in Proposition 6.1 at aperture one.

## Main results

* `norm_le_of_mem_rectangle`
-/

open Complex Set Topology

namespace GaloisForLFunctions.HTGeometry

theorem norm_le_of_mem_rectangle {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {A B T C : ℝ} (hAB : A < B) (hT : 0 < T)
    (hedge : ∀ z : ℂ, A ≤ z.re → z.re ≤ B → -T ≤ z.im → z.im ≤ T →
      (z.re = A ∨ z.re = B ∨ z.im = -T ∨ z.im = T) → ‖f z‖ ≤ C)
    {z : ℂ} (h1 : A ≤ z.re) (h2 : z.re ≤ B) (h3 : -T ≤ z.im) (h4 : z.im ≤ T) :
    ‖f z‖ ≤ C := by
  have hTT : (-T : ℝ) < T := by linarith
  set U : Set ℂ := Set.Ioo A B ×ℂ Set.Ioo (-T) T with hU
  have hclosure : closure U = Set.Icc A B ×ℂ Set.Icc (-T) T := by
    rw [hU, Complex.closure_reProdIm, closure_Ioo hAB.ne, closure_Ioo hTT.ne]
  have hbdd : Bornology.IsBounded U := by
    refine Bornology.IsBounded.subset (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := |A| + |B| + T)) ?_
    intro w hw
    rw [hU, Complex.mem_reProdIm] at hw
    obtain ⟨hw1, hw2⟩ := hw
    rw [Metric.mem_closedBall, dist_zero_right]
    have hre : |w.re| ≤ |A| + |B| := by
      rcases le_or_gt w.re 0 with hle | hgt
      · rw [abs_of_nonpos hle]
        have := hw1.1
        have h := abs_nonneg B
        have hA : -|A| ≤ A := neg_abs_le A
        linarith
      · rw [abs_of_pos hgt]
        have := hw1.2
        have h := abs_nonneg A
        have hB : B ≤ |B| := le_abs_self B
        linarith
    have him : |w.im| ≤ T := by
      rw [abs_le]
      exact ⟨hw2.1.le, hw2.2.le⟩
    have := Complex.norm_le_abs_re_add_abs_im w
    linarith
  have hdc : DiffContOnCl ℂ f U := hf.diffContOnCl
  refine Complex.norm_le_of_forall_mem_frontier_norm_le hbdd hdc ?_ ?_
  · intro w hw
    rw [hU, Complex.frontier_reProdIm, closure_Ioo hAB.ne, frontier_Ioo hAB,
      closure_Ioo hTT.ne, frontier_Ioo hTT] at hw
    rcases hw with hw | hw
    · rw [Complex.mem_reProdIm] at hw
      obtain ⟨hre, him⟩ := hw
      have hre' := hre
      rw [Set.mem_Icc] at hre'
      rcases him with him | him
      · refine hedge w hre'.1 hre'.2 (le_of_eq him.symm) ?_ (Or.inr (Or.inr (Or.inl him)))
        rw [him]
        linarith
      · have him' : w.im = T := him
        refine hedge w hre'.1 hre'.2 ?_ (le_of_eq him') (Or.inr (Or.inr (Or.inr him')))
        rw [him']
        linarith
    · rw [Complex.mem_reProdIm] at hw
      obtain ⟨hre, him⟩ := hw
      have him' := him
      rw [Set.mem_Icc] at him'
      rcases hre with hre | hre
      · refine hedge w (le_of_eq hre.symm) ?_ him'.1 him'.2 (Or.inl hre)
        rw [hre]
        linarith
      · have hre' : w.re = B := hre
        refine hedge w ?_ (le_of_eq hre') him'.1 him'.2 (Or.inr (Or.inl hre'))
        rw [hre']
        linarith
  · rw [hclosure, Complex.mem_reProdIm, Set.mem_Icc, Set.mem_Icc]
    exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩

end GaloisForLFunctions.HTGeometry
