import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.EmptyVisitFlux.FaceGeometry

/-! # Positive residence following a regular inward contact -/

open Finset Set
namespace GaloisForLFunctions.HTGeometry.AdaptiveSampling.ContactRecurrence.ClosingGap.Residence
open EmptyVisitFlux
noncomputable section

theorem inward_window {I : Type*} [Fintype I] {w : I → ℝ} {r v : ℝ} {i j : I}
    (hr : 0<r) (hf : inwardFace w r v i j) :
    ∃ h>0, ∀ u∈Icc (0:ℝ) h, flow w (v+u)∈enclosingUnitArc r := by
  classical
  letI : Nonempty I := ⟨i⟩
  have local_window (k : I) (hk : k≠i) : ∃ d>0, ∀ u∈Icc (0:ℝ) d,
      flow w (v+u) k-flow w (v+u) i∈forwardUnitArc r := by
    have he (u : ℝ) : flow w (v+u) k-flow w (v+u) i=
        flow w v k-flow w v i+((u*(w k-w i):ℝ):UnitAddCircle) := by
      simp only [flow,←AddCircle.coe_sub,←AddCircle.coe_add]
      congr 1
      ring
    by_cases hkj : k=j
    · subst k
      have hg := sub_pos.mpr hf.1
      refine ⟨r/(w i-w j),div_pos hr hg,fun u hu => ?_⟩
      rw [he,hf.2.1]
      have hu' := (le_div_iff₀ hg).mp hu.2
      have hneg := mul_nonpos_of_nonneg_of_nonpos hu.1 (sub_nonpos.mpr hf.1.le)
      exact ⟨r+u*(w j-w i),⟨by linarith only [hu'],by linarith only [hneg]⟩,AddCircle.coe_add ..⟩
    · obtain ⟨y,hy,hyc⟩ := hf.2.2 k hk hkj
      let m := min y (r-y)
      have hm : 0<m := lt_min hy.1 (sub_pos.mpr hy.2)
      let B := |w k-w i|+1
      have hB : 0<B := by dsimp only [B]; positivity
      refine ⟨m/B,div_pos hm hB,fun u hu => ?_⟩
      have bound : |u*(w k-w i)|≤m := by
        rw [abs_mul,abs_of_nonneg hu.1]
        exact (mul_le_mul_of_nonneg_left (by dsimp [B]; linarith : |w k-w i|≤B) hu.1).trans
          ((le_div_iff₀ hB).mp hu.2)
      rw [he,←hyc]
      refine ⟨y+u*(w k-w i),⟨?_,?_⟩,AddCircle.coe_add ..⟩
      · linarith only [(abs_le.mp bound).1,show m≤y from min_le_left ..]
      · linarith only [(abs_le.mp bound).2,show m≤r-y from min_le_right ..]
  have each (k : I) : ∃ d>0, ∀ u∈Icc (0:ℝ) d, k≠i →
      flow w (v+u) k-flow w (v+u) i∈forwardUnitArc r := by
    by_cases he : k=i
    · exact ⟨1,one_pos,fun _ _ hn => (hn he).elim⟩
    · obtain ⟨d,hd,hu⟩ := local_window k he
      exact ⟨d,hd,fun u h _ => hu u h⟩
  choose d hd hu using each
  refine ⟨univ.inf' univ_nonempty d,(lt_inf'_iff ..).mpr fun k _ => hd k,fun u h => mem_iUnion.mpr ⟨i,?_⟩⟩
  exact fun k => hu k u ⟨h.1,h.2.trans (inf'_le d (mem_univ k))⟩

#print axioms inward_window
end
end GaloisForLFunctions.HTGeometry.AdaptiveSampling.ContactRecurrence.ClosingGap.Residence
