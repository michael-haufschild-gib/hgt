import GaloisForLFunctions.HTGeometry.TwoLocalIntegerWitness
import GaloisForLFunctions.HTGeometry.SpectralRelationSpaceGalois

/-!
# The explicit integer two-local witness has a rationally rigid spectrum

The integer traceless two-local witness has symmetric Galois group, so every permutation of its
eigenvalues is realized by a field automorphism, and the only rational relation among them is the
trace relation.  This is the spectral rigidity that the transcendence and phase-filling arguments
consume.

## Main results

* `trace_map_int` — the trace of a coefficient-mapped matrix.
* `exists_integer_twoLocal_rigid_spectrum` — **an explicit traceless integer two-local Hamiltonian
  whose eigenvalues admit no rational relation other than the trace relation.**
-/

open Polynomial Matrix
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

namespace TwoLocalWitness

noncomputable section

variable {m : ℕ}

theorem trace_map_int {R S : Type*} [CommRing R] [CommRing S] {n : Type*} [Fintype n]
    (f : R →+* S) (M : Matrix n n R) : (M.map f).trace = f M.trace := by
  rw [Matrix.trace, Matrix.trace, map_sum]
  rfl

/-- **The explicit integer two-local witness has a rationally rigid spectrum.** -/
theorem exists_integer_twoLocal_rigid_spectrum {g : MvPolynomial (Fin (m + 1)) ℚ} (hg : g ≠ 0) :
    ∃ (u : Fin (m + 1) → ℚ) (N : ℕ)
      (Hz : Matrix (Fin (m + 1) → Bool) (Fin (m + 1) → Bool) ℤ),
      MvPolynomial.eval u g ≠ 0 ∧ 0 < N ∧
      Hz.map (Int.castRingHom ℚ)
        = (N : ℚ) • twoLocalHam (witnessConstant m) 0 witnessCoupling u ∧
      Hz.trace = 0 ∧
      Nat.card (Hz.charpoly.map (Int.castRingHom ℚ)).Gal = (2 ^ (m + 1)).factorial ∧
      ∃ γ : Fin (2 ^ (m + 1)) → (Hz.charpoly.map (Int.castRingHom ℚ)).SplittingField,
        Function.Injective γ ∧
        (Hz.charpoly.map (Int.castRingHom ℚ)).map
            (algebraMap ℚ (Hz.charpoly.map (Int.castRingHom ℚ)).SplittingField)
          = ∏ j, (X - C (γ j)) ∧
        LinearMap.ker (ratRelationForm γ)
          = PermSubspace.constLine (K := ℚ) (ι := Fin (2 ^ (m + 1))) := by
  classical
  obtain ⟨u, N, Hz, hu, hN, hA, hgal, hirr, -⟩ :=
    exists_integer_twoLocal_symmetric_gal (witnessConstant m) hg
  have hcardcube : Fintype.card (Fin (m + 1) → Bool) = 2 ^ (m + 1) := by simp
  have htraceQ : (Hz.map (Int.castRingHom ℚ)).trace = 0 := by
    rw [hA, Matrix.trace_smul, twoLocalHam, trace_transverseFamilyHam]
    have hsw := sum_witnessDiagonal m
    rw [witnessDiagonal] at hsw
    rw [hsw, smul_zero]
  have htrace : Hz.trace = 0 := by
    have hcast := trace_map_int (Int.castRingHom ℚ) Hz
    rw [htraceQ] at hcast
    have hcast' : ((Hz.trace : ℤ) : ℚ) = 0 := hcast.symm
    exact_mod_cast hcast'
  have hmonic : (Hz.charpoly.map (Int.castRingHom ℚ)).Monic := (Hz.charpoly_monic).map _
  have hdeg : (Hz.charpoly.map (Int.castRingHom ℚ)).natDegree = 2 ^ (m + 1) := by
    rw [(Hz.charpoly_monic).natDegree_map, Matrix.charpoly_natDegree_eq_dim, hcardcube]
  have hD1 : 1 < 2 ^ (m + 1) := Nat.one_lt_two_pow (by omega)
  have hcoeffZ : Hz.charpoly.coeff (2 ^ (m + 1) - 1) = 0 := by
    have htr := Matrix.trace_eq_neg_charpoly_coeff Hz
    rw [hcardcube, htrace] at htr
    linarith
  have hcoeffQ : (Hz.charpoly.map (Int.castRingHom ℚ)).coeff (2 ^ (m + 1) - 1) = 0 := by
    rw [Polynomial.coeff_map, hcoeffZ, map_zero]
  obtain ⟨γ, hγinj, hγ, hker⟩ :=
    exists_rigid_root_family hmonic hirr hdeg hD1 hcoeffQ hgal
  exact ⟨u, N, Hz, hu, hN, hA, htrace, hgal, γ, hγinj, hγ, hker⟩

end

end TwoLocalWitness

end GaloisForLFunctions.HTGeometry
