import GaloisForLFunctions.HTGeometry.MilnorTameResidueQuotient

/-!
# Hasse classification for realized finite-support Milnor residues

Global Milnor classes have equal finite-support residue profiles exactly when they differ by the
everywhere-unramified tame kernel.  Every profile in the realized range has a representative unique
modulo that kernel.  No simultaneous approximation theorem outside the realized range is asserted.
-/

namespace GaloisForLFunctions.HTGeometry

section TotalResidue

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-- Equality of all finite-place Milnor residues is congruence modulo the tame kernel. -/
theorem milnorTameResidue_congr_hasse_iff (n : ℕ) (x y : MilnorKDeg K n) :
    x - y ∈ milnorTameKernel R K n ↔
      milnorTotalResidue (R := R) K n x = milnorTotalResidue (R := R) K n y := by
  rw [← milnorTotalResidue_mem_ker_iff (R := R) K n]
  change milnorTotalResidue (R := R) K n (x - y) = 0 ↔ _
  rw [map_sub, sub_eq_zero]

/-- Every globally realized finite-support residue profile has a global Milnor representative,
unique modulo the tame kernel. -/
theorem milnorTameResidue_exists_unique_mod_tameKernel
    (n : ℕ) (z : (milnorTotalResidue (R := R) K n).range) :
    ∃ x : MilnorKDeg K n, milnorTotalResidue (R := R) K n x = z.1 ∧
      ∀ y : MilnorKDeg K n, milnorTotalResidue (R := R) K n y = z.1 ↔
        y - x ∈ milnorTameKernel R K n := by
  obtain ⟨x, hx⟩ := z.2
  refine ⟨x, hx, fun y => ?_⟩
  rw [← hx]
  exact (milnorTameResidue_congr_hasse_iff (R := R) K n y x).symm

end TotalResidue
end GaloisForLFunctions.HTGeometry
