import GaloisForLFunctions.HTGeometry.Thermofield.ReturnLawResolution
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Finite tests of thermofield return-law stability

The balanced integer relation lattice of a finite spectrum is finitely
generated. A single replica moment at or above the heights of its generators
tests preservation of the full stationary return law.
-/

open Filter Set Topology _root_.HTGeometry

namespace GaloisForLFunctions.HTGeometry.Thermofield

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

omit [DecidableEq α] [Nonempty α] in
/-- A finite list of integral relations tests preservation of every coarse relation. -/
theorem exists_gibbsReturnRelationTests (E : α → ℝ) :
    ∃ S : Finset (α → ℤ), (∀ k ∈ S, k ∈ projectiveSpectralRelationLattice E) ∧
      ∀ F : α → ℝ, (projectiveSpectralRelationLattice E ≤ projectiveSpectralRelationLattice F) ↔
        ∀ k ∈ S, finiteTorusCharacterDetuning k F = 0 := by
  classical
  let L := projectiveSpectralRelationLattice E
  obtain ⟨S, hS⟩ := IsNoetherian.noetherian L.toIntSubmodule
  have hmem (k : α → ℤ) (hk : k ∈ S) : k ∈ L := by
    change k ∈ L.toIntSubmodule
    rw [← hS]
    exact Submodule.subset_span hk
  refine ⟨S, hmem, fun F => ⟨?_, ?_⟩⟩
  · intro h k hk
    exact ((mem_projectiveSpectralRelationLattice_iff F k).mp (h (hmem k hk))).2
  · intro h
    change L.toIntSubmodule ≤ (projectiveSpectralRelationLattice F).toIntSubmodule
    rw [← hS]
    apply Submodule.span_le.mpr
    intro k hk
    exact (mem_projectiveSpectralRelationLattice_iff F k).mpr
      ⟨((mem_projectiveSpectralRelationLattice_iff E k).mp (hmem k hk)).1, h k hk⟩

/-- At any order above a spectrum-dependent cutoff, equality of that single
moment is equivalent to preservation of the entire return law. -/
theorem exists_gibbsReturnLaw_moment_cutoff (E : α → ℝ) :
    ∃ N : ℕ, ∀ (β : ℝ) (F : α → ℝ) (n : ℕ), N ≤ n →
      (returnFidelityMoment (gibbsResolvedReturnLaw β E F) n =
        returnFidelityMoment (gibbsUnresolvedReturnLaw β E) n ↔
        gibbsResolvedReturnLaw β E F = gibbsUnresolvedReturnLaw β E) := by
  classical
  obtain ⟨S, hmem, htests⟩ := exists_gibbsReturnRelationTests E
  refine ⟨S.sup spectralCharacterPositiveMass, fun β F n hn => ⟨?_, ?_⟩⟩
  · intro heq
    apply (gibbsResolvedReturnLaw_eq_iff_relationLattice_le β E F).mpr
    apply (htests F).mpr
    intro k hk
    by_contra hdet
    have hkF : k ∉ projectiveSpectralRelationLattice F :=
      fun h => hdet ((mem_projectiveSpectralRelationLattice_iff F k).mp h).2
    have hheight : spectralCharacterPositiveMass k ≤ n :=
      (Finset.le_sup (f := spectralCharacterPositiveMass) hk).trans hn
    have hlt := (returnFidelityMoment_resolved_lt_iff β E F n).mpr ⟨k, hmem k hk, hkF, hheight⟩
    rw [heq] at hlt
    exact lt_irrefl _ hlt
  · intro heq
    rw [heq]

/-- One sufficiently high stationary moment tests continuity of the full
law at zero splitting. The order is independent of temperature and fine spectrum. -/
theorem exists_gibbsAffineReturnLaw_continuity_cutoff (E : α → ℝ) :
    ∃ N : ℕ, ∀ (β : ℝ) (F : α → ℝ) (n : ℕ), N ≤ n →
      (ContinuousAt (fun s => returnFidelityMoment (gibbsUnresolvedReturnLaw β (affineSpectrum E F s)) n)
          (0 : ℝ) ↔
        ContinuousAt (fun s => gibbsUnresolvedReturnLaw β (affineSpectrum E F s)) (0 : ℝ)) := by
  obtain ⟨N, hN⟩ := exists_gibbsReturnLaw_moment_cutoff E
  refine ⟨N, fun β F n hn => ?_⟩
  rw [gibbsAffineReturnMoment_continuousAt_iff, hN β F n hn,
    gibbsResolvedReturnLaw_eq_iff_relationLattice_le, gibbsAffineReturnLaw_continuousAt_iff]

#print axioms exists_gibbsReturnRelationTests
#print axioms exists_gibbsReturnLaw_moment_cutoff
#print axioms exists_gibbsAffineReturnLaw_continuity_cutoff

end

end GaloisForLFunctions.HTGeometry.Thermofield
