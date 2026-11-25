import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.AntipodalHorizons.PhysicalScales
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.FirstWaitLaw

/-! # Identifying the intrinsic spectral clock with the sorted extremal levels -/

open Matrix Finset Set MeasureTheory
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.WindingConfidence
open PrescribedTimes AntipodalHorizons
noncomputable section

/-- The sorted physical endpoints give the native spectral diameter for
every coupling vector, including degenerate spectra. Hence all the
corresponding full-width winding dates are Borel functions. -/
theorem intrinsic_sorted_width (k : ℕ) (x : PrefixIndex (k+1)→ℝ) :
    let E := sortedEnsembleSpectrum (chainPauliFin_isHermitian (k+3)) x
    circuitHamiltonianSpectralWidth (prefixGenerator (k+1) x)=E (topLevel k)-E 0 := by
  intro E
  let n := k+1
  let u : PathShell n := WithLp.toLp 2 (fun l => x ((pathCoeffEquiv n).symm l))
  let H := (isSelfAdjoint_pathHamiltonian u).isHermitian
  let G := isHermitian_spectralEnsembleMatrix (chainPauliFin_isHermitian (k+3)) x
  have hgen : numberedGenerator n x=pathHamiltonian u := by
    simpa only [u,WithLp.ofLp_toLp,Equiv.symm_apply_apply] using numberedGenerator_shell u
  have hOp : prefixGenerator n x=⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩ := Subtype.ext hgen
  rw [hOp]
  let e := qubitConfigFin (k+3)
  have hg := range_eigenvalues_reindex e H
  have hmat : Matrix.reindex e e (pathHamiltonian u)=spectralEnsembleMatrix (chainPauliFin (k+3)) x := by
    simpa only [u,WithLp.ofLp_toLp,Equiv.symm_apply_apply] using reindex_pathHamiltonian u
  have he := isHermitian_eigenvalues_congr (isHermitian_reindex e H) G hmat
  rw [he] at hg
  have hr : Set.range E=Set.range H.eigenvalues := by
    change Set.range (G.eigenvalues ∘ Tuple.sort G.eigenvalues)=_
    rw [Set.range_comp,(Tuple.sort G.eigenvalues).surjective.range_eq,Set.image_univ]
    exact hg
  have hends (j : Fin (k+3)→Bool) : E 0≤H.eigenvalues j ∧ H.eigenvalues j≤E (topLevel k) := by
    have hmem : H.eigenvalues j∈Set.range E := by rw [hr]; exact Set.mem_range_self j
    obtain ⟨i,hi⟩ := hmem
    rw [←hi]
    refine ⟨monotone_sortedTuple _ (Fin.zero_le i),monotone_sortedTuple _ ?_⟩
    change i.val≤2^(k+3)-1
    have := i.isLt
    omega
  have hatt (i : Level k) : E i∈Set.range H.eigenvalues := by rw [←hr]; exact Set.mem_range_self i
  obtain ⟨a,ha⟩ := hatt (topLevel k)
  obtain ⟨b,hb⟩ := hatt 0
  change Finset.univ.sup' Finset.univ_nonempty H.eigenvalues -
    Finset.univ.inf' Finset.univ_nonempty H.eigenvalues=_
  congr 1
  · refine le_antisymm ?_ (ha ▸ le_sup' H.eigenvalues (Finset.mem_univ a))
    apply sup'_le
    exact fun j _ => (hends j).2
  · refine le_antisymm (hb ▸ inf'_le H.eigenvalues (Finset.mem_univ b)) ?_
    apply le_inf'
    exact fun j _ => (hends j).1

theorem continuous_prefix_width (k : ℕ) :
    Continuous (fun x : PrefixIndex (k+1)→ℝ => circuitHamiltonianSpectralWidth (prefixGenerator (k+1) x)) := by
  simp_rw [intrinsic_sorted_width]
  have hE := continuous_sortedEnsembleSpectrum (chainPauliFin_isHermitian (k+3))
  exact ((continuous_apply (topLevel k)).comp hE).sub ((continuous_apply 0).comp hE)

#print axioms intrinsic_sorted_width
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.WindingConfidence
