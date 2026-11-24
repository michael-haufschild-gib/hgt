import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Rank.NecessaryOrder.MultisetCount
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Rank.NecessaryOrder.BinomialBound

/-! # How many independently varied couplings a linear-order energy test needs -/

open Matrix
namespace GaloisForLFunctions.HTGeometry.SpectralJets.NecessaryOrder
noncomputable section

/-- For a 2ᴺ-level simple spectrum, any analytic parametrization giving a full
projective derivative basis through order 12N needs more than N/9 parameters.
The parameters may vary several physical couplings together. -/
theorem necessary_control_count {n m a L : ℕ} (hn : 53≤n)
    {P : Fin a → Matrix (Fin (2^(n+1))) (Fin (2^(n+1))) ℂ}
    (hP : ∀ i, (P i).IsHermitian)
    (φ : (Fin m→ℝ)→(Fin a→ℝ)) (x : Fin m→ℝ) (hφ : AnalyticAt ℝ φ x)
    (hs : Function.Injective (isHermitian_spectralEnsembleMatrix hP (φ x)).eigenvalues)
    (k : Fin (2^(n+1))) (w : Fin (2^(n+1))→List (Fin m))
    (hw : ∀ i, (w i).length≤L) (hL : L≤12*(n+1))
    (hd : (of fun i j => if i=k then (1:ℝ) else
      realMixed (w i) (fun y => sortedEnsembleSpectrum hP (φ y) j) x).det≠0) : n+1<9*m := by
  have h := ambient_order_bound k w hw _ x (fun j => (analyticAt_sortedEnsembleSpectrum hP hs j).comp hφ) hd
  by_contra! hm
  have hb := choose_le_half_dimension hn hL hm
  have hsym : (m+L).choose L=(L+m).choose m := by
    rw [←Nat.choose_symm (Nat.le_add_left L m),Nat.add_sub_cancel_right,Nat.add_comm m L]
  rw [hsym,pow_succ] at h
  have ht : 1<(2:ℕ)^n := one_lt_pow₀ (by decide) (by omega)
  omega

#print axioms necessary_control_count
end
end GaloisForLFunctions.HTGeometry.SpectralJets.NecessaryOrder
