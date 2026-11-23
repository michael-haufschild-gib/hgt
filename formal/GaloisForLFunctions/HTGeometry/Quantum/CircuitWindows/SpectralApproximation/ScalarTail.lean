import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SpectralApproximation.SpectatorRank
import GaloisForLFunctions.HTGeometry.Quantum.PhysicalCircuitDeletionBound
import GaloisForLFunctions.HTGeometry.SiteFactorLiftedSpectrum
import GaloisForLFunctions.HTGeometry.SiteSupportedReindex
import GaloisForLFunctions.HTGeometry.PathHamiltonianSiteRestriction

/-! # Spectral tails obstruct cheap circuits in every basis -/
open Matrix
open scoped Matrix.Norms.L2Operator Kronecker
namespace GaloisForLFunctions.HTGeometry.SpectralApproximation
noncomputable section

private abbrev Reg (N : ℕ) := Matrix (Fin N → Bool) (Fin N → Bool) ℂ

/-- Every accurate low-rank approximation of the difference between a
supported operator and identity has rank at least the spectator dimension. -/
theorem supported_scalar_rank {N : ℕ} {S : Finset (Fin N)} {A : Reg N}
    (hA : IsSiteSupported S A) (B : Reg N) (h : ‖(1-A)-B‖ < ‖1-A‖) :
    2^(N-S.card) ≤ B.rank := by
  classical
  let e := configurationSplitEquiv (fun _ : Fin N => Bool) S
  let Φ := Matrix.reindexAlgEquiv ℂ ℂ e
  obtain ⟨L,hL⟩ := exists_liftLocalMatrix_of_isSiteSupported hA
  have hsplit : Φ (1-A) = (1-L) ⊗ₖ 1 := by
    rw [hL]
    change Matrix.reindex (configurationSplitEquiv (fun _ : Fin N => Bool) S)
      (configurationSplitEquiv (fun _ : Fin N => Bool) S) (1-liftLocalMatrix S L) = _
    simpa only [map_one] using reindex_scalarSub_liftLocalMatrix S L (1:ℂ)
  have hh : ‖(1-L) ⊗ₖ 1 - Φ B‖ < ‖1-L‖ := by
    rw [←l2_opNorm_kronecker_one (n:=OutsideConfiguration (fun _ : Fin N => Bool) S) (1-L),
      ←hsplit,←map_sub]
    simpa only [Φ,l2_opNorm_reindexAlgEquiv_eq] using h
  have hdim := spectator_rank (1-L) (Φ B) hh
  change Fintype.card (OutsideConfiguration (fun _ : Fin N => Bool) S) ≤ (Matrix.reindex e e B).rank at hdim
  simpa [OutsideConfiguration,Fintype.card_subtype_compl,Matrix.rank_reindex] using hdim

/-- If the displacement from identity is larger than the tail error plus
twice the circuit error, the tail rank bounds the spectator dimension
of every fitting circuit, even after an arbitrary free change of basis. -/
theorem conjugate_scalar_tail {N : ℕ} (U B : Reg N) (W : unitaryGroup (Fin N → Bool) ℂ)
    {ε ρ : ℝ} (hB : ‖(1-U)-B‖ ≤ ρ) (hU : 2*ε+ρ < ‖1-U‖) {s : ℕ}
    (hfit : HasProjectiveCircuitApproximation N ε s (W.val*U*star W.val)) :
    2^(N-2*s) ≤ B.rank := by
  obtain ⟨z,_,C,hC,hfit⟩ := hfit
  let V := W.val*U*star W.val
  let R := W.val*B*star W.val
  let Q := z • C.eval.val
  have hW : W.val * star W.val = 1 := W.property.2
  have shift : 1-V = W.val*(1-U)*star W.val := by simp only [mul_sub,sub_mul,mul_one,hW,V]
  have hnorm : ‖1-V‖ = ‖1-U‖ := by rw [shift,l2_opNorm_unitary_conj_eq W.property]
  have herr : ‖(1-V)-R‖ ≤ ρ := by
    rw [shift,show W.val*(1-U)*star W.val-R=W.val*((1-U)-B)*star W.val by
      simp only [R,mul_sub,sub_mul],l2_opNorm_unitary_conj_eq W.property]
    exact hB
  have he : ‖(1-Q)-(1-V)‖ ≤ ε := by
    rw [show (1-Q)-(1-V)=V-Q by abel]
    exact hfit
  have tri := norm_sub_le_norm_sub_add_norm_sub (1-Q) (1-V) R
  have low := norm_sub_le_norm_sub_add_norm_sub (1-V) (1-Q) 0
  rw [sub_zero,sub_zero,norm_sub_rev (1-V) (1-Q),hnorm] at low
  have hsmall : ‖(1-Q)-R‖ < ‖1-Q‖ := by linarith only [tri,low,he,herr,hU]
  have hr := supported_scalar_rank (IsSiteSupported.complex_smul z C.isSiteSupported_touchedSites) R hsmall
  have hsites := C.card_touchedSites_le
  exact (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : N-2*s ≤ N-C.touchedSites.card)).trans
    (hr.trans ((Matrix.rank_mul_le_left ..).trans (Matrix.rank_mul_le_right ..)))

#print axioms conjugate_scalar_tail
end
end GaloisForLFunctions.HTGeometry.SpectralApproximation
