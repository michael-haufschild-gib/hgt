import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.ReplicaOrders.ExactQuadrature.HalfPeriods

/-! # The record distinguishing every pair of distinct energies -/
open Finset
namespace GaloisForLFunctions.HTGeometry.SpectralFilling.ExactQuadrature
noncomputable section
variable {I : Type*}

/-- Only distinct positive gaps contribute half-periods to the clock. -/
def gaps (S : Finset I) (E : I → ℝ) : Finset ℝ :=
  ((S ×ˢ S).image (fun x => |E x.1-E x.2|)).erase 0

theorem gap_phase (S : Finset I) (E : I → ℝ) {i j : I} (hi : i∈S) (hj : j∈S) (a : ℝ) :
    average (gaps S E).toList (wave (E i-E j)) a=if E i=E j then 1 else 0 := by
  by_cases h : E i=E j
  · rw [h,sub_self,if_pos rfl,show wave 0=(fun _ => 1) by funext t; simp [wave],average_const]
  · rw [if_neg h]
    have hz := sub_ne_zero.mpr h
    apply annihilate _ hz
    refine ⟨|E i-E j|,?_,(abs_abs _).symm⟩
    rw [mem_toList,gaps,mem_erase]
    exact ⟨abs_ne_zero.mpr hz,mem_image.mpr ⟨(i,j),mem_product.mpr ⟨hi,hj⟩,rfl⟩⟩

#print axioms gap_phase
end
end GaloisForLFunctions.HTGeometry.SpectralFilling.ExactQuadrature
