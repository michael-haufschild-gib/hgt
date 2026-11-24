import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.EnergyMesh.SpectralEdges
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.EnergyMesh.DisjointLevels

/-! # Filling the energy interval by moving a cut -/

open Finset Set Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.FirstAscent.EnergyMesh
noncomputable section

private theorem near_range {m : ℕ→ℝ} {N : ℕ} {y r : ℝ} (hr : 0 ≤ r) (h₀ : y ≤ m 0)
    (hN : m N ≤ y) (hstep : ∀ j<N, m j-m (j+1) ≤ 2*r) :
    ∃ j ≤ N, |m j-y| ≤ r := by
  induction N with
  | zero => exact ⟨0,le_rfl,by rw [le_antisymm hN h₀,sub_self,abs_zero]; exact hr⟩
  | succ N ih =>
    by_cases h : m N ≤ y
    · obtain ⟨j,hj,hd⟩ := ih h (fun j hj => hstep j (Nat.lt_succ_of_lt hj))
      exact ⟨j,hj.step,hd⟩
    · have hs := hstep N (Nat.lt_succ_self N)
      by_cases hn : m N-y ≤ r
      · exact ⟨N,Nat.le_succ N,by rwa [abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge h))]⟩
      · exact ⟨N+1,le_rfl,by rw [abs_of_nonpos (sub_nonpos.mpr hN)]; linarith only [hs,lt_of_not_ge hn]⟩

private abbrev QReg (N : ℕ) := EnergyOperator (Fin N → Bool)

/-- Follow the lowest left-packet energy plus the highest right-packet
energy from the top of the spectrum to the bottom. Half a step and one
cut perturbation suffice to reach a level near any prescribed energy. -/
theorem moving_cut_cover {N K : ℕ} (H : QReg N) (A B : ℕ→QReg N)
    (L R : ℕ→Finset (Fin N)) {r d : ℝ} (hr : 0 ≤ r)
    (hstart : upper H ≤ lower (A 0)+upper (B 0))
    (hfinish : lower (A K)+upper (B K) ≤ lower H)
    (hcut : ∀ j ≤ K, ‖(A j+B j).val-H.val‖ ≤ d)
    (hs : ∀ j ≤ K, Disjoint (L j) (R j) ∧ IsSiteSupported (L j) (A j).val ∧ IsSiteSupported (R j) (B j).val)
    (hstep : ∀ j<K, ‖(A j).val-(A (j+1)).val‖+‖(B j).val-(B (j+1)).val‖ ≤ 2*r)
    {y : ℝ} (hy : y ∈ Icc (lower H) (upper H)) :
    ∃ i, |H.2.isHermitian.eigenvalues i-y| ≤ r+d := by
  let m (j : ℕ) := lower (A j)+upper (B j)
  obtain ⟨j,hj,hd⟩ := near_range (m:=m) hr (hy.2.trans hstart) (hfinish.trans hy.1) (fun j hj => by
    have h₁ := (abs_le.mp (lower_stability (A j) (A (j+1)))).2
    have h₂ := (abs_le.mp (upper_stability (B j) (B (j+1)))).2
    dsimp only [m]
    linarith only [h₁,h₂,hstep j hj])
  obtain ⟨a,_,ha⟩ := exists_mem_eq_inf' univ_nonempty (A j).2.isHermitian.eigenvalues
  obtain ⟨b,_,hb⟩ := exists_mem_eq_sup' univ_nonempty (B j).2.isHermitian.eigenvalues
  obtain ⟨hs',hA,hB⟩ := hs j hj
  obtain ⟨k,hk⟩ := disjoint_sum_level hs' hA hB (A j).2.isHermitian (B j).2.isHermitian a b
  have hlevel : (A j+B j).2.isHermitian.eigenvalues k=m j := by
    dsimp only [m,lower,upper]
    rw [ha,hb]
    exact hk
  obtain ⟨i,hi⟩ := matching (A j+B j) H k
  rw [hlevel,abs_sub_comm] at hi
  exact ⟨i,(abs_sub_le _ (m j) _).trans (by linarith only [hi,hd,hcut j hj])⟩

#print axioms moving_cut_cover
end
end GaloisForLFunctions.HTGeometry.FirstAscent.EnergyMesh
