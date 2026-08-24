import GaloisForLFunctions.HTGeometry.RationalDiagonalDerivation
import GaloisForLFunctions.HTGeometry.RationalTorusInvariantFamilyRank
import GaloisForLFunctions.HTGeometry.ActiveLatticeCompressionClassification
import GaloisForLFunctions.HTGeometry.ScalarDifferentialOrderUpperBound
import GaloisForLFunctions.HTGeometry.UnitCharacterStabilizerRank

/-!
# Algebraic dependence of rational diagonal jets

All diagonal derivatives of a rational torus observable retain its scaling
symmetries.  A finite packet through active-lattice rank therefore lies in a
common state field of at most that transcendence degree, forcing a nonzero
polynomial relation among the first `rank + 1` symbolic jets.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Set

noncomputable section

variable {r : ℕ}

/-- Every iterate of a fixed rational function remains fixed because scaling
commutes with the diagonal derivation. -/
theorem rationalTorusScaleEquiv_iterate_rationalDiagonalDerivation_fixed
    (omega : Fin r → ℝ) (u : Fin r → ℂˣ)
    (z : FractionRing (MvPolynomial (Fin r) ℂ))
    (hfix : rationalTorusScaleEquiv u z = z) (n : ℕ) :
    rationalTorusScaleEquiv u
        ((rationalDiagonalDerivation omega)^[n] z) =
      (rationalDiagonalDerivation omega)^[n] z := by
  induction n generalizing z with
  | zero => simpa using hfix
  | succ n hn =>
      rw [Function.iterate_succ_apply]
      apply hn
      rw [rationalTorusScaleEquiv_rationalDiagonalDerivation, hfix]

set_option maxHeartbeats 100000 in
/-- The first `active-rank + 1` symbolic derivatives of a rational observable
fixed by its active-character stabilizer satisfy a nonzero polynomial relation. -/
theorem exists_rationalDiagonalIterate_relation_of_activeSupport_fix
    (omega : Fin r → ℝ) (F : (Fin r → ℂ) → ℂ)
    (z : FractionRing (MvPolynomial (Fin r) ℂ))
    (hfix : ∀ u ∈ unitCharacterStabilizer (activeSupport F),
      rationalTorusScaleEquiv u z = z) :
    ∃ H : MvPolynomial (Fin (activeLatticeNatRank F + 1)) ℂ,
      H ≠ 0 ∧ MvPolynomial.aeval
        (fun j : Fin (activeLatticeNatRank F + 1) =>
          (rationalDiagonalDerivation omega)^[(j : ℕ)] z) H = 0 := by
  classical
  let y₀ : Fin (activeLatticeNatRank F + 1) →
      FractionRing (MvPolynomial (Fin r) ℂ) := fun j =>
    (rationalDiagonalDerivation omega)^[(j : ℕ)] z
  have hy₀fix : ∀ j u, u ∈ unitCharacterStabilizer (activeSupport F) →
      rationalTorusScaleEquiv u (y₀ j) = y₀ j := by
    intro j u hu
    exact rationalTorusScaleEquiv_iterate_rationalDiagonalDerivation_fixed
      omega u z (hfix u hu) (j : ℕ)
  obtain ⟨K, hKtr, hKmem⟩ :=
    exists_rationalInvariant_family_stateField_rank_le
      (S := unitCharacterStabilizer (activeSupport F))
      (A := activeSupport F)
      (rank_scaleAnnihilator_unitCharacterStabilizer_le (activeSupport F))
      y₀ hy₀fix
  change Algebra.trdeg ℂ K ≤ Module.rank ℤ (activeLattice F) at hKtr
  rw [← natCast_activeLatticeNatRank F] at hKtr
  let y : Fin (activeLatticeNatRank F + 1) → K :=
    fun j => ⟨y₀ j, hKmem j⟩
  have hdep : ¬ AlgebraicIndependent ℂ y :=
    not_algebraicIndependent_of_trdeg_le hKtr y
  rw [algebraicIndependent_iff_injective_aeval] at hdep
  obtain ⟨H₁, H₂, hEq, hne⟩ := Function.not_injective_iff.mp hdep
  refine ⟨H₁ - H₂, sub_ne_zero.mpr hne, ?_⟩
  have hy : MvPolynomial.aeval y (H₁ - H₂) = 0 := by
    rw [map_sub, hEq, sub_self]
  have hcomp := MvPolynomial.comp_aeval_apply y K.val (H₁ - H₂)
  rw [hy, map_zero] at hcomp
  simpa [y, y₀] using hcomp.symm

end

end GaloisForLFunctions.HTGeometry
