import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.SpectatorCost.PathLayers
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SpectralApproximation.PhaseTail
import GaloisForLFunctions.HTGeometry.MatrixRankSubadditive

/-! # Exponentially small spectral rank outside an extensive energy window -/
open Matrix Finset
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralGapMass.SpectatorCost
noncomputable section

/-- Delete the central part of a Hermitian spectrum. The retained
matrix has rank bounded by the two-sided eigenvalue count. -/
theorem hermitian_tail {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    {H : Matrix I I ℂ} (h : H.IsHermitian) {r : ℝ} (hr : 0 ≤ r) :
    ∃ B : Matrix I I ℂ, ‖H-B‖ ≤ r ∧
      B.rank ≤ (univ.filter fun j => r < |h.eigenvalues j|).card := by
  let V := h.eigenvectorUnitary
  let E (j : I) : ℂ := h.eigenvalues j
  have he : diagonal (fun j => 1-E j) = (1:Matrix I I ℂ)-diagonal E := by
    simpa only [Matrix.diagonal_one] using (Matrix.diagonal_sub (fun _ : I => (1:ℂ)) E).symm
  have hv : V.val*star V.val=1 := V.property.2
  have hH : V.val*diagonal E*star V.val=H := (isHermitian_eq_conj_diagonal h).symm
  obtain ⟨B,hB,hc⟩ := SpectralApproximation.truncate_displacement V (fun j => 1-E j) hr
  rw [he,mul_sub,sub_mul,mul_one,hv,hH,sub_sub_cancel] at hB
  exact ⟨B,hB,by simpa only [sub_sub_cancel,E,Complex.norm_real,Real.norm_eq_abs] using hc⟩

/-- Truncate each disjoint layer at r. Their central parts have total
operator norm at most 21r, and ranks add across the remaining parts. -/
theorem path_generator_tail {n : ℕ} (u : PathShell n) {B r : ℝ}
    (hB : 0 < B) (hmass : ‖u‖^2 ≤ B) (hr : 0 ≤ r) :
    ∃ G : Matrix (Fin (n+2) → Bool) (Fin (n+2) → Bool) ℂ,
      ‖pathHamiltonian u-G‖ ≤ 21*r ∧
      (G.rank:ℝ) ≤ 42*(2:ℝ)^(n+2)*Real.exp (-(r^2)/(2*B)) := by
  classical
  choose G hG hc using fun a : Layer => hermitian_tail (hermitian_layer u a) hr
  have hcard : Fintype.card Layer=21 := by simp [Layer,Fintype.card_sum,Fintype.card_prod]
  refine ⟨∑ a, G a,?_,?_⟩
  · rw [←sum_layer u,←Finset.sum_sub_distrib]
    apply (norm_sum_le ..).trans
    apply (sum_le_sum fun a _ => hG a).trans_eq
    simp only [sum_const,card_univ,hcard,nsmul_eq_mul,Nat.cast_ofNat]
  · have hrc : ((∑ a, G a).rank:ℝ) ≤ ∑ a, ((G a).rank:ℝ) := by
      exact_mod_cast rank_sum_le univ G
    apply hrc.trans
    apply (sum_le_sum fun a _ => (Nat.cast_le.mpr (hc a)).trans (layer_energy_count u a hB hmass hr)).trans_eq
    simp only [sum_const,card_univ,hcard,nsmul_eq_mul,Nat.cast_ofNat]
    ring

#print axioms path_generator_tail
end
end GaloisForLFunctions.HTGeometry.SpectralGapMass.SpectatorCost
