import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.PairedFields.EnergySpread

/-! # Energy dispersion in a single ranked row of a spectral overlap matrix -/

open Finset
namespace GaloisForLFunctions.HTGeometry.Dephasing.PairedFields.SpectralEdge
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Loss in the top partial sum after taking spectral expectations in another frame. -/
def cutDeficit (p : I → I → ℝ) (v : I → ℝ) (S : Finset I) : ℝ :=
  ∑ i ∈ S, v i - ∑ j ∈ S, rowMean p v j

private theorem centered_cut (p : I → I → ℝ) (hr : ∀ j, ∑ i, p j i=1)
    (v : I → ℝ) (S : Finset I) (z : ℝ) :
    cutDeficit p v S = ∑ i, ((if i∈S then 1 else 0) - ∑ k ∈ S, p k i)*(v i-z) := by
  have hm (k : I) : ∑ i, p k i*(v i-z)=rowMean p v k-z := by
    simp only [mul_sub,sum_sub_distrib,←sum_mul,hr,one_mul,rowMean]
  have hind : ∑ i, (if i∈S then (1:ℝ) else 0)*(v i-z)=∑ i ∈ S, (v i-z) := by
    simp only [ite_mul,one_mul,zero_mul,sum_ite_mem,univ_inter]
  simp only [sub_mul,sum_sub_distrib,hind,sum_mul]
  rw [sum_comm (s:=univ) (t:=S)]
  simp only [hm,sum_sub_distrib,cutDeficit]
  abel

/-- The two cuts on either side of row j pay its mean absolute energy
displacement from the jth eigenvalue, including at repeated eigenvalues. -/
theorem row_gap_le_adjacent_cuts {p : I → I → ℝ} (hn : ∀ k i, 0≤p k i)
    (hr : ∀ k, ∑ i, p k i=1) (hc : ∀ i, ∑ k, p k i=1)
    (v : I → ℝ) (S : Finset I) (j : I) (hj : j∉S)
    (hhigh : ∀ i∈S, v j≤v i) (hlow : ∀ i∉S, v i≤v j) :
    rowMean p (fun i => |v i-v j|) j ≤ cutDeficit p v S+cutDeficit p v (insert j S) := by
  rw [centered_cut p hr v S (v j),centered_cut p hr v (insert j S) (v j),←sum_add_distrib]
  apply sum_le_sum
  intro i _
  change p j i*|v i-v j| ≤ _
  have h₀ : 0 ≤ ∑ k ∈ S, p k i := sum_nonneg fun k _ => hn k i
  have h₁ : p j i+∑ k ∈ S, p k i ≤ 1 := by
    rw [←sum_insert (f:=fun k => p k i) hj,←hc i]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun k _ _ => hn k i)
  rw [sum_insert hj]
  by_cases hi : i∈S
  · have hi' := mem_insert_of_mem (b:=j) hi
    rw [if_pos hi,if_pos hi',abs_of_nonneg (sub_nonneg.mpr (hhigh i hi)),←add_mul]
    exact mul_le_mul_of_nonneg_right (by linarith only [h₁]) (sub_nonneg.mpr (hhigh i hi))
  · by_cases he : i=j
    · subst i
      simp only [sub_self,abs_zero,mul_zero,add_zero,le_refl]
    · have hi' : i∉insert j S := by simpa only [mem_insert,not_or] using And.intro he hi
      have hv := sub_nonpos.mpr (hlow i hi)
      rw [if_neg hi,if_neg hi',abs_of_nonpos hv,mul_neg,←neg_mul,←add_mul]
      exact mul_le_mul_of_nonpos_right (by linarith only [h₀]) hv

#print axioms row_gap_le_adjacent_cuts
end
end GaloisForLFunctions.HTGeometry.Dephasing.PairedFields.SpectralEdge
