import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.FreeAxis.GaussianAction
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.FreeAxis.CentralCones
import GaloisForLFunctions.HTGeometry.PathShellPatchTransport

/-! # Positive laboratory coordinates throughout the octant of spin frames -/
open Matrix Finset Set
namespace GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut.FreeAxis
noncomputable section

private theorem positive_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hι : Fintype.card ι ≤ 9) (c x : ι→ℝ) (j : ι)
    (hc : ∀ i, |c i| ≤ 1) (hx : ∀ i, |x i| ≤ 3)
    (hj : 1/9 ≤ c j) (hy : 1/2 ≤ x j) (ho : ∀ i, i≠j → |x i|≤1/20000) :
    (∑ i, c i*x i) ∈ Icc (1/20:ℝ) 4 := by
  have hlo (i : ι) : (if i=j then (1/18:ℝ) else 0)-1/20000 ≤ c i*x i := by
    by_cases hi : i=j
    · subst i
      rw [if_pos rfl]
      have hh := mul_le_mul hj hy (by norm_num) ((by norm_num : (0:ℝ)≤1/9).trans hj)
      linarith only [hh]
    · rw [if_neg hi,zero_sub]
      have hh := mul_le_mul (hc i) (ho i hi) (abs_nonneg _) zero_le_one
      rw [←abs_mul,one_mul] at hh
      exact (abs_le.mp hh).1
  have hu (i : ι) : c i*x i ≤ (if i=j then (3:ℝ) else 0)+1/20000 := by
    apply (le_abs_self _).trans
    rw [abs_mul]
    by_cases hi : i=j
    · rw [if_pos hi]
      exact ((mul_le_mul (hc i) (hx i) (abs_nonneg _) zero_le_one).trans_eq
        (one_mul _)).trans (le_add_of_nonneg_right (by norm_num))
    · rw [if_neg hi,zero_add]
      exact (mul_le_mul (hc i) (ho i hi) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hcard : (Fintype.card ι:ℝ) ≤ 9 := by exact_mod_cast hι
  have h₁ := sum_le_sum (s:=univ) (fun i _ => hlo i)
  have h₂ := sum_le_sum (s:=univ) (fun i _ => hu i)
  simp [sum_sub_distrib,sum_add_distrib,nsmul_eq_mul] at h₁ h₂
  exact ⟨by linarith only [h₁,hcard],by linarith only [h₂,hcard]⟩

/-- All rotated laboratory entries, with their signs, lie in [1/20,4].
At most eight small transverse terms accompany the longitudinal term. -/
theorem octant_coordinates {n : ℕ} (F : SpinFrame) (hF : ∀ i : Fin 3, 1/3 ≤ F.R i 2)
    (x : PathLabel n→ℝ) (hx : ∀ l, |x l|≤3) (hd : ∀ l, IsDiagLabel l → 1/2<x l)
    (ho : ∀ l, ¬IsDiagLabel l → |x l|≤1/20000) (l : PathLabel n) :
    rotateLabels F.R n x l ∈ Icc (1/20:ℝ) 4 := by
  rcases l with ⟨s,a⟩|⟨e,a,b⟩
  · exact positive_sum (by simp) (F.R a) (fun j => x (.inl (s,j))) 2 (F.entry_le a)
      (fun j => hx (.inl (s,j))) ((by norm_num : (1/9:ℝ)≤1/3).trans (hF a))
      (hd (.inl (s,2)) rfl).le (fun j h => ho (.inl (s,j)) h)
  · let c := fun j : Fin 3×Fin 3 => F.R a j.1*F.R b j.2
    have hc (j : Fin 3×Fin 3) : |c j| ≤ 1 := by
      dsimp only [c]; rw [abs_mul]
      exact mul_le_one₀ (F.entry_le _ _) (abs_nonneg _) (F.entry_le _ _)
    have hj : 1/9 ≤ c (2,2) :=
      (by norm_num : (1/9:ℝ)=(1/3)*(1/3)).le.trans
        (mul_le_mul (hF a) (hF b) (by norm_num) ((by norm_num : (0:ℝ)≤1/3).trans (hF a)))
    have h := positive_sum (by simp) c (fun j => x (.inr (e,j))) (2,2) hc
      (fun j => hx (.inr (e,j))) hj (hd (.inr (e,2,2)) rfl).le (fun j h => ho (.inr (e,j)) h)
    simpa only [Fintype.sum_prod_type,c,rotateLabels] using h

#print axioms octant_coordinates
end
end GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut.FreeAxis
