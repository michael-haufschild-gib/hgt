import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.IncidentPauliTerms
import GaloisForLFunctions.HTGeometry.PauliOperatorNormSandwich
import GaloisForLFunctions.HTGeometry.PauliTwoLocalLabels

/-! # Energy variance of a sum of arbitrary local path terms -/
open Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.ProductInputs
noncomputable section

/-- Each off-diagonal entry sees at most the 21 path terms incident on
any differing bit. Summing their squares costs no Hilbert-space dimension. -/
theorem local_column_variance {n : ℕ} (u : PathShell n)
    (P : PathLabel n→Matrix (Fin (n+2)→Bool) (Fin (n+2)→Bool) ℂ)
    (hP : ∀ l, ‖P l‖=1)
    (hoff : ∀ l v, ¬pathIncident v l → ∀ y x : Fin (n+2)→Bool, y v≠x v → P l y x=0)
    (H : Matrix (Fin (n+2)→Bool) _ ℂ) (hH : H=∑ l, (u l:ℂ) • P l) (x : Fin (n+2)→Bool) :
    (∑ y ∈ Finset.univ.erase x, ‖H y x‖^2) ≤ 21*‖u‖^2 := by
  classical
  let a (y : Fin (n+2)→Bool) (l : PathLabel n) := (u l:ℂ)*P l y x
  have hrow (y : Fin (n+2)→Bool) (hy : y≠x) :
      ‖H y x‖^2 ≤ 21*∑ l : PathLabel n, ‖a y l‖^2 := by
    obtain ⟨v,hv⟩ := Function.ne_iff.mp hy
    let F := pathIncidentLabels v
    have hzero (l : PathLabel n) (hl : l∉F) : a y l=0 := by
      have hi : ¬pathIncident v l := fun h => hl (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
      have hp : P l y x=0 := hoff l v hi y x hv
      simp only [a,hp,mul_zero]
    have he : H y x=∑ l∈F, a y l := by
      rw [hH,Matrix.sum_apply]
      exact (Finset.sum_subset (Finset.subset_univ F) (fun l _ hl => hzero l hl)).symm
    rw [he]
    calc
      _ ≤ (∑ l∈F, ‖a y l‖)^2 := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ ≤ (F.card:ℝ)*∑ l∈F, ‖a y l‖^2 := sq_sum_le_card_mul_sum_sq
      _ ≤ _ := mul_le_mul (by exact_mod_cast pathIncidentLabels_card v)
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ F) (fun _ _ _ => sq_nonneg _))
        (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by norm_num)
  have hcol (l : PathLabel n) :
      (∑ y ∈ Finset.univ.erase x, ‖a y l‖^2) ≤ (u l)^2 := by
    have hn : ‖P l‖=1 := hP l
    have hle := (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.erase_subset x (Finset.univ : Finset (Fin (n+2)→Bool)))
      (fun y _ _ => sq_nonneg ‖P l y x‖)).trans (sum_normSq_column_le_opNorm_sq (P l) x)
    rw [hn,one_pow] at hle
    simp only [a,norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs,←Finset.mul_sum]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hle (sq_nonneg (u l))
  calc
    _ ≤ ∑ y ∈ Finset.univ.erase x, 21*∑ l : PathLabel n, ‖a y l‖^2 :=
      Finset.sum_le_sum fun y hy => hrow y (Finset.ne_of_mem_erase hy)
    _ = 21*∑ l : PathLabel n, ∑ y ∈ Finset.univ.erase x, ‖a y l‖^2 := by
      rw [← Finset.mul_sum,Finset.sum_comm]
    _ ≤ 21*∑ l : PathLabel n, (u l)^2 := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum fun l _ => hcol l) (by norm_num)
    _ = _ := by simp only [EuclideanSpace.norm_sq_eq,Real.norm_eq_abs,sq_abs]

end
end GaloisForLFunctions.HTGeometry.SpanningDensity.ProductInputs
