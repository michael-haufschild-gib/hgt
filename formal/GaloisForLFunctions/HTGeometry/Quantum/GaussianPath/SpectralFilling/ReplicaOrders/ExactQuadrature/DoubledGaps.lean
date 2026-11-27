import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.ReplicaOrders.ExactQuadrature.GapClock
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.ReplicaOrders.ExactQuadrature.HarmonicSpan

/-! # Separation of the entire half-period clock at doubled order -/
open Finset Real
namespace GaloisForLFunctions.HTGeometry.SpectralFilling.ExactQuadrature
noncomputable section
variable {I : Type*}

private theorem oriented_gap (S : Finset I) (E : I → ℝ) {u : ℝ} (hu : u∈gaps S E) :
    ∃ i∈S, ∃ j∈S, u=E i-E j ∧ 0<u := by
  obtain ⟨hne,hi⟩ := mem_erase.mp hu
  obtain ⟨⟨i,j⟩,hm,he⟩ := mem_image.mp hi
  obtain ⟨hi,hj⟩ := mem_product.mp hm
  change |E i-E j|=u at he
  have hpos := lt_of_le_of_ne ((abs_nonneg _).trans_eq he) (Ne.symm hne)
  rcases le_total (E j) (E i) with h|h
  · exact ⟨i,hi,j,hj,he.symm.trans (abs_of_nonneg (sub_nonneg.mpr h)),hpos⟩
  · exact ⟨j,hj,i,hi,(he.symm.trans (abs_of_nonpos (sub_nonpos.mpr h))).trans (neg_sub ..),hpos⟩

/-- Two different positive detunings differ by a difference of two
pair sums. A gap bound for unequal pair sums therefore controls the
whole clock even in the presence of repeated frequencies. -/
theorem doubled_gap_span (S : Finset I) (E : I → ℝ) {γ : ℝ} (hγ : 0<γ)
    (hgap : ∀ i∈S, ∀ j∈S, ∀ k∈S, ∀ l∈S, E i+E j≠E k+E l →
      γ≤|(E i+E j)-(E k+E l)|) :
    ∑ w∈gaps S E, π/w ≤ (π/γ)*(1+log (gaps S E).card) := by
  apply logarithmic_span _ hγ
  · intro u hu
    obtain ⟨i,hi,j,hj,hu,hp⟩ := oriented_gap S E hu
    have h : (E i+E j)-(E j+E j)=u := by rw [hu]; ring
    have hn : E i+E j≠E j+E j := sub_ne_zero.mp (h.trans_ne hp.ne')
    simpa only [h,abs_of_pos hp] using hgap i hi j hj j hj j hj hn
  · intro u hu v hv huv
    obtain ⟨i,hi,j,hj,hu,_⟩ := oriented_gap S E hu
    obtain ⟨k,hk,l,hl,hv,_⟩ := oriented_gap S E hv
    have h : (E i+E l)-(E j+E k)=u-v := by rw [hu,hv]; ring
    have hn : E i+E l≠E j+E k := sub_ne_zero.mp (h.trans_ne (sub_ne_zero.mpr huv))
    simpa only [h] using hgap i hi l hl j hj k hk hn

#print axioms doubled_gap_span
end
end GaloisForLFunctions.HTGeometry.SpectralFilling.ExactQuadrature
