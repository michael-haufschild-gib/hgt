import GaloisForLFunctions.HTGeometry.SpectralActionNonconstancy
import GaloisForLFunctions.HTGeometry.PathChainLabelIdentification
import GaloisForLFunctions.HTGeometry.DisjointPacketSpectrum
import GaloisForLFunctions.HTGeometry.PauliEnsembleSimpleSpectrum

/-! # Sorted physical block energies and their Gaussian coordinates -/
open Set Matrix MeasureTheory
namespace GaloisForLFunctions.HTGeometry.WeakBonds.NearDiagonal.BlockMergers
noncomputable section

/-- The full spectrum in increasing order, including every multiplicity. -/
def energies (n : ℕ) (x : PathLabel n→ℝ) : Fin (2^(n+2))→ℝ :=
  sortedEnsembleSpectrum (chainPauliFin_isHermitian (n+2)) (fun i => x (pathCoeffEquiv n i))

theorem measurable_energies (n : ℕ) (i : Fin (2^(n+2))) : Measurable fun x => energies n x i :=
  ((continuous_apply i).comp ((continuous_sortedEnsembleSpectrum _).comp
    (continuous_pi fun j => continuous_apply (pathCoeffEquiv n j)))).measurable

theorem energies_scale {n : ℕ} (c : ℝ) (hc : 0<c) (x : PathLabel n→ℝ) (i : Fin (2^(n+2))) :
    energies n (c • x) i=c*energies n x i :=
  congrFun (sortedEnsembleSpectrum_smul (chainPauliFin_isHermitian (n+2)) hc
    (fun j => x (pathCoeffEquiv n j))) i

theorem energies_range {n : ℕ} (x : PathLabel n→ℝ) :
    range (energies n x)=range (isSelfAdjoint_pathHamiltonian (WithLp.toLp 2 x : PathShell n)).isHermitian.eigenvalues := by
  let u : PathShell n := WithLp.toLp 2 x
  let θ := fun i => x (pathCoeffEquiv n i)
  let H := (isSelfAdjoint_pathHamiltonian u).isHermitian
  let G := isHermitian_spectralEnsembleMatrix (chainPauliFin_isHermitian (n+2)) θ
  let e := qubitConfigFin (n+2)
  have hr := range_eigenvalues_reindex e H
  have he := isHermitian_eigenvalues_congr (isHermitian_reindex e H) G (reindex_pathHamiltonian u)
  rw [he] at hr
  apply Eq.trans _ hr
  change range (sortedTuple G.eigenvalues)=range G.eigenvalues
  ext t
  constructor
  · rintro ⟨i,rfl⟩
    exact ⟨Tuple.sort G.eigenvalues i,rfl⟩
  · rintro ⟨i,rfl⟩
    exact ⟨(Tuple.sort G.eigenvalues).symm i,sortedTuple_symm_apply _ _⟩

/-- Gap lower bounds transfer between two enumerations of equal size.
A positive common spacing rules out a repeated level in either array. -/
theorem transfer_spacing {I J : Type*} [Fintype I] [Fintype J] (e : I ≃ J)
    {a : I→ℝ} {b : J→ℝ} (he : range a⊆range b) {g : ℝ} (hg : 0<g)
    (ha : ∀ i j, i≠j → g≤|a i-a j|) : ∀ i j, i≠j → g≤|b i-b j| := by
  have h (i : I) : ∃ j, b j=a i := he (mem_range_self i)
  choose f hf using h
  have hi : Function.Injective f := by
    intro i j h
    by_contra hij
    have h' := ha i j hij
    rw [←hf i,←hf j,h,sub_self,abs_zero] at h'
    exact hg.not_ge h'
  have hs := hi.surjective_of_finite e
  intro i j hij
  obtain ⟨s,rfl⟩ := hs i
  obtain ⟨t,rfl⟩ := hs j
  rw [hf,hf]
  exact ha _ _ (fun h => hij (congrArg f h))

#print axioms energies_range
#print axioms transfer_spacing
end
end GaloisForLFunctions.HTGeometry.WeakBonds.NearDiagonal.BlockMergers
