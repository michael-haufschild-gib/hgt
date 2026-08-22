import GaloisForLFunctions.HTGeometry.TwoLocalWitness
import GaloisForLFunctions.HTGeometry.CharpolyScaleGalois

/-!
# An integer two-local witness with symmetric Galois group

Clearing the denominators of the couplings replaces the rational witness by an integral multiple of
itself.  Scaling does not move the Galois group of the characteristic polynomial, so the integer
Hamiltonian obtained this way still has the full symmetric Galois group — and its characteristic
polynomial has integer coefficients, which is what the arithmetic spectral-action bound consumes.

## Main results

* `exists_common_denominator` — a common denominator for a finite family of rationals.
* `exists_integral_scaling` — the scaling that makes the witness integral.
* `exists_integer_twoLocal_symmetric_gal` — **an integer two-local Hamiltonian whose characteristic
  polynomial has integer coefficients, the full symmetric Galois group, and makes every nonzero
  rational vector cyclic.**
-/

open Polynomial Matrix
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

namespace TwoLocalWitness

noncomputable section

variable {m : ℕ}

theorem exists_common_denominator {ι : Type*} [Fintype ι] (u : ι → ℚ) :
    ∃ N : ℕ, 0 < N ∧ ∀ i, ∃ z : ℤ, (N : ℚ) * u i = (z : ℚ) := by
  classical
  refine ⟨∏ i, (u i).den, Finset.prod_pos fun i _ => (u i).pos, fun i => ?_⟩
  obtain ⟨k, hk⟩ : (u i).den ∣ ∏ j, (u j).den := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  refine ⟨k * (u i).num, ?_⟩
  rw [hk]
  push_cast
  rw [mul_comm ((u i).den : ℚ) (k : ℚ), mul_assoc, mul_comm ((u i).den : ℚ) (u i),
    Rat.mul_den_eq_num]

theorem exists_integral_scaling (c : ℚ) (u : Fin (m + 1) → ℚ) :
    ∃ N : ℕ, 0 < N ∧ ∀ x y : Fin (m + 1) → Bool, ∃ z : ℤ,
      ((N : ℚ) • twoLocalHam c 0 witnessCoupling u) x y = (z : ℚ) := by
  classical
  obtain ⟨N₀, hN₀, hu₀⟩ := exists_common_denominator u
  obtain ⟨zc, hzc⟩ : ∃ z : ℤ, ((c.den : ℚ)) * c = (z : ℚ) :=
    ⟨c.num, by rw [mul_comm]; exact Rat.mul_den_eq_num c⟩
  refine ⟨N₀ * c.den, Nat.mul_pos hN₀ c.pos, fun x y => ?_⟩
  have hu : ∀ i, ∃ z : ℤ, ((N₀ * c.den : ℕ) : ℚ) * u i = (z : ℚ) := by
    intro i
    obtain ⟨z, hz⟩ := hu₀ i
    refine ⟨c.den * z, ?_⟩
    push_cast
    rw [mul_comm (N₀ : ℚ) ((c.den : ℚ)), mul_assoc, hz]
  have hc : ∃ z : ℤ, ((N₀ * c.den : ℕ) : ℚ) * c = (z : ℚ) := by
    refine ⟨N₀ * zc, ?_⟩
    push_cast
    rw [mul_assoc, hzc]
  set N : ℕ := N₀ * c.den with hNdef
  rw [Matrix.smul_apply, smul_eq_mul, twoLocalHam, transverseFamilyHam]
  by_cases hxy : x = y
  · rw [if_pos hxy]
    obtain ⟨zc', hzc'⟩ := hc
    refine ⟨zc' + N * (occZ x) ^ 2, ?_⟩
    have hd : twoLocalDiagonal c 0 witnessCoupling x = c + ((occZ x : ℤ) : ℚ) ^ 2 := by
      have := witnessDiagonal_eq c x
      rw [witnessDiagonal] at this
      rw [this]
    rw [hd, mul_add, hzc']
    push_cast
    ring
  · rw [if_neg hxy, Finset.mul_sum]
    choose z hz using hu
    refine ⟨∑ i, (if y = boolToggle x i then z i else 0), ?_⟩
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : y = boolToggle x i
    · rw [if_pos hi, if_pos hi, hz i]
    · rw [if_neg hi, if_neg hi, mul_zero]

/-- **An integer two-local Hamiltonian with the full symmetric Galois group.** -/
theorem exists_integer_twoLocal_symmetric_gal (c : ℚ) {g : MvPolynomial (Fin (m + 1)) ℚ}
    (hg : g ≠ 0) :
    ∃ (u : Fin (m + 1) → ℚ) (N : ℕ)
      (Hz : Matrix (Fin (m + 1) → Bool) (Fin (m + 1) → Bool) ℤ),
      MvPolynomial.eval u g ≠ 0 ∧ 0 < N ∧
      Hz.map (Int.castRingHom ℚ) = (N : ℚ) • twoLocalHam c 0 witnessCoupling u ∧
      Nat.card ((Hz.charpoly.map (Int.castRingHom ℚ))).Gal = (2 ^ (m + 1)).factorial ∧
      Irreducible (Hz.charpoly.map (Int.castRingHom ℚ)) ∧
      ∀ v : (Fin (m + 1) → Bool) → ℚ, v ≠ 0 →
        LinearIndependent ℚ (fun k : Fin (Fintype.card (Fin (m + 1) → Bool)) =>
          (Hz.map (Int.castRingHom ℚ)) ^ (k : ℕ) *ᵥ v) := by
  classical
  obtain ⟨u, hu, hgal⟩ := exists_twoLocal_symmetric_gal c hg
  obtain ⟨N, hN, hint⟩ := exists_integral_scaling c u
  choose zz hzz using hint
  have hA : (Matrix.of zz).map (Int.castRingHom ℚ)
      = (N : ℚ) • twoLocalHam c 0 witnessCoupling u := by
    ext x y
    rw [Matrix.map_apply]
    exact (hzz x y).symm
  have hNQ : ((N : ℚ)) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  have hcharmap : (Matrix.of zz).charpoly.map (Int.castRingHom ℚ)
      = ((N : ℚ) • twoLocalHam c 0 witnessCoupling u).charpoly := by
    rw [← Matrix.charpoly_map, ← hA]
  have hgal' : Nat.card ((Matrix.of zz).charpoly.map (Int.castRingHom ℚ)).Gal
      = (2 ^ (m + 1)).factorial := by
    rw [hcharmap, card_gal_charpoly_smul hNQ]
    exact hgal
  have hdegcard : (((Matrix.of zz).charpoly.map (Int.castRingHom ℚ))).natDegree
      = 2 ^ (m + 1) := by
    rw [hcharmap, Matrix.charpoly_natDegree_eq_dim]
    simp
  have hirr : Irreducible ((Matrix.of zz).charpoly.map (Int.castRingHom ℚ)) := by
    refine irreducible_of_card_gal_eq_factorial ?_ ?_ ?_
    · rw [hcharmap]
      exact (Matrix.charpoly_monic _).ne_zero
    · rw [hdegcard]
      exact Nat.one_le_two_pow
    · rw [hgal', hdegcard]
  have hirr' : Irreducible (((Matrix.of zz).map (Int.castRingHom ℚ)).charpoly) := by
    rw [Matrix.charpoly_map (Matrix.of zz) (Int.castRingHom ℚ)]
    exact hirr
  exact ⟨u, N, Matrix.of zz, hu, hN, hA, hgal', hirr,
    fun v hv => linearIndependent_krylov_of_irreducible _ hirr' hv⟩

end

end TwoLocalWitness

end GaloisForLFunctions.HTGeometry
