import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.FluxOccupation.PathGaps

/-! # Mean pair gap and mean absolute energy -/
open Real
namespace GaloisForLFunctions.HTGeometry.SpectralGapMass
open EmptyVisitFlux
noncomputable section

/-- The mean absolute difference of two independent centered energies is
between the first absolute moment and twice that moment. -/
theorem pair_absolute_bounds {I : Type*} [Fintype I] (E : I → ℝ) (h : ∑ i, E i=0) :
    let D := (Fintype.card I:ℝ)
    D*(∑ i, |E i|) ≤ 4*π*pairTurnRate E ∧ 4*π*pairTurnRate E ≤ 2*D*(∑ i, |E i|) := by
  intro D
  let S := ∑ i, ∑ j, max 0 (E i-E j)
  have hr : 4*π*pairTurnRate E=2*S := by
    rw [pairTurnRate,←Finset.sum_div,Fintype.sum_prod_type]
    dsimp only [S]
    field_simp
    ring
  have he : (∑ i, ∑ j, |E i-E j|)=2*S := by
    have point (u v : ℝ) : |u-v|=max 0 (u-v)+max 0 (v-u) := by
      rcases le_total u v with h|h
      · rw [abs_of_nonpos (sub_nonpos.mpr h),max_eq_left (sub_nonpos.mpr h),max_eq_right (sub_nonneg.mpr h),zero_add,neg_sub]
      · rw [abs_of_nonneg (sub_nonneg.mpr h),max_eq_right (sub_nonneg.mpr h),max_eq_left (sub_nonpos.mpr h),add_zero]
    simp_rw [point,Finset.sum_add_distrib]
    have hf : (∑ i, ∑ j, max 0 (E j-E i))=S := Finset.sum_comm
    rw [hf,two_mul]
  rw [hr,←he]
  constructor
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hi : (∑ j, (E i-E j))=D*E i := by
      simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,h,sub_zero,D]
    rw [←abs_of_nonneg (show 0≤D by dsimp only [D]; positivity),←abs_mul,←hi]
    exact Finset.abs_sum_le_sum_abs _ _
  · calc
      _ ≤ ∑ i, ∑ j, (|E i|+|E j|) := Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => abs_sub _ _
      _ = _ := by
        simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,←Finset.mul_sum,D]
        ring

end
end GaloisForLFunctions.HTGeometry.SpectralGapMass
