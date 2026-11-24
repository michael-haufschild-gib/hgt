import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Rank.NecessaryOrder.MultisetCount
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Rank.NecessaryOrder.BinomialBound
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.DirectedBond.Gaussian.SortedRank

/-! # The least full projective spectral order grows linearly on the Gaussian chain -/
open Matrix MeasureTheory Filter
namespace GaloisForLFunctions.HTGeometry.SpectralJets.NecessaryOrder
open SpinExtension.DirectedBond
noncomputable section

/-- One constant row and ordinary real energy derivatives in arbitrary physical
Pauli coefficients form a full minor through order L. -/
def HasFullOrder (N : ℕ) (x : Coordinates N→ℝ) (L : ℕ) : Prop :=
  ∃ (k : Fin (2^N)) (w : Fin (2^N)→List (Coordinates N)), (∀ i, (w i).length≤L) ∧
    (of fun i j => if i=k then (1:ℝ) else
      realMixed (w i) (fun y => sortedEnsembleSpectrum (chainPauliFin_isHermitian N) y j) x).det≠0

private theorem coordinate_count (k : ℕ) : Fintype.card (ChainLabel (k+3))≤12*(k+3) := by
  have h := Fintype.card_congr (pathCoeffEquiv (k+1))
  simp only [PathLabel,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin] at h
  calc Fintype.card (ChainLabel (k+3)) = (k+3)*3+(k+2)*(3*3) := h
       _ ≤ _ := by omega

/-- At every simple physical spectrum on at least 54 spins, any complete
derivative basis, even using all 12N−9 coefficients, needs order above N/9. -/
theorem necessary_order_at_simple (k : ℕ) (hk : 51≤k) (x : Coordinates (k+3)→ℝ)
    (hs : x∈simpleEnsembleLocus (chainPauliFin_isHermitian (k+3))) (L : ℕ)
    (hL : HasFullOrder (k+3) x L) : k+3<9*L := by
  obtain ⟨i,w,hw,hd⟩ := hL
  have h := ambient_order_bound i w hw _ x (analyticAt_sortedEnsembleSpectrum _ hs) hd
  by_contra! hsmall
  have hb := choose_le_half_dimension (n:=k+2) (by omega) (coordinate_count k) hsmall
  have htwo : 1<(2:ℕ)^(k+2) := one_lt_pow₀ (by decide) (by omega)
  rw [show (2:ℕ)^(k+3)=2^(k+2)*2 from pow_succ ..] at h
  omega

/-- On one full-measure event, every prefix has a least full order. It lies
between N/9 and 2N−1 on every prefix with N≥54. -/
theorem gaussian_least_order :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ,
      let N := k+3
      let x := fun i => pathPauliDisorderShell ω (k+1) (pathCoeffEquiv (k+1) i)
      ∃ L, HasFullOrder N x L ∧ (∀ r, HasFullOrder N x r → L≤r) ∧
        L≤2*(k+2)+1 ∧ (51≤k → N<9*L) := by
  classical
  obtain ⟨i,v,_,hl,hr⟩ := gaussian_sorted_full_projective_rank
  filter_upwards [hr,gaussian_path_all_prefixes_maximally_projective] with ω hdet hgen
  intro k N x
  have hu : HasFullOrder N x (2*(k+2)+1) :=
    ⟨i k,fun a => (v k a).map (fieldIndex (k+2)),fun a => by simpa only [List.length_map] using hl k a,hdet k⟩
  have hex : ∃ r, HasFullOrder N x r := ⟨_,hu⟩
  refine ⟨Nat.find hex,Nat.find_spec hex,fun _ => Nat.find_min' hex,Nat.find_min' hex hu,fun hk => ?_⟩
  let u := pathPauliDisorderShell ω (k+1)
  let q := qubitConfigFin (k+3)
  let hH := (isSelfAdjoint_pathHamiltonian u).isHermitian
  have hp : ∃ h : (reindex q q (pathHamiltonian u)).IsHermitian, MaximallyProjectiveEnergy h.eigenvalues :=
    ⟨hH.reindex q,Matrix.IsHermitian.maximallyProjective_reindexAlgEquiv q hH (hgen k)⟩
  rw [reindex_pathHamiltonian] at hp
  exact necessary_order_at_simple k hk x hp.choose_spec.injective _ (Nat.find_spec hex)

#print axioms necessary_order_at_simple
#print axioms gaussian_least_order
end
end GaloisForLFunctions.HTGeometry.SpectralJets.NecessaryOrder
