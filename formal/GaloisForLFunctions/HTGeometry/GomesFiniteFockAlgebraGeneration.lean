import GaloisForLFunctions.HTGeometry.GomesFiniteFockTaylorArc

/-!
# Exact generation and self-commutant of the finite Fock symmetry algebra

The actual finite clock alone generates its full matrix commutant as a complex
algebra. This commutative algebra is its own matrix commutant and bicommutant,
so no additional matrices appear at the bicommutant step in this finite model.
-/

noncomputable section
open Matrix Polynomial
open scoped BigOperators
namespace GaloisForLFunctions.HTGeometry.GammaFactorialFock

/-- The actual finite clock belongs to its full symmetry algebra. -/
theorem gomesFiniteFockCommutant_clock_mem (N : ℕ) :
    fockShiftMatrix N ∈ gomesFiniteFockCommutant N :=
  (gomesFiniteFockCommutant_mem_iff _ _).mpr (Commute.refl _)

/-- The single actual clock generates its entire symmetry algebra using finite algebra operations. -/
theorem gomesFiniteFockCommutant_eq_adjoin (N : ℕ) :
    gomesFiniteFockCommutant N = Algebra.adjoin ℂ {fockShiftMatrix N} := by
  apply le_antisymm
  · intro M hM
    obtain ⟨c, hc, _⟩ := (gomesFiniteFock_commute_iff_unique_clock_polynomial N M).mp
      ((gomesFiniteFockCommutant_mem_iff _ _).mp hM)
    rw [← hc]
    apply Subalgebra.sum_mem
    intro k _
    apply Subalgebra.smul_mem
    apply Subalgebra.pow_mem
    exact Algebra.subset_adjoin (Set.mem_singleton _)
  · apply Algebra.adjoin_le
    intro M hM
    rcases hM with rfl
    exact gomesFiniteFockCommutant_clock_mem N

/-- The full symmetry algebra is its own commutant inside the actual matrix algebra. -/
theorem gomesFiniteFockCommutant_centralizer (N : ℕ) :
    Subalgebra.centralizer ℂ (gomesFiniteFockCommutant N : Set (Matrix (Fin N) (Fin N) ℂ)) =
      gomesFiniteFockCommutant N := by
  ext M
  constructor
  · intro h
    apply (gomesFiniteFockCommutant_mem_iff _ _).mpr
    exact ((Subalgebra.mem_centralizer_iff ℂ).mp h _
      (gomesFiniteFockCommutant_clock_mem N)).symm
  · intro h
    apply (Subalgebra.mem_centralizer_iff ℂ).mpr
    intro E hE
    exact (gomesFiniteFockCommutant_commute N ⟨E, hE⟩ ⟨M, h⟩).eq

/-- Taking the bicommutant preserves exactly the same finite clock algebra. -/
theorem gomesFiniteFockCommutant_bicommutant (N : ℕ) :
    Subalgebra.centralizer ℂ
      (Subalgebra.centralizer ℂ (gomesFiniteFockCommutant N : Set (Matrix (Fin N) (Fin N) ℂ)) :
        Set (Matrix (Fin N) (Fin N) ℂ)) = gomesFiniteFockCommutant N := by
  rw [gomesFiniteFockCommutant_centralizer, gomesFiniteFockCommutant_centralizer]

end GaloisForLFunctions.HTGeometry.GammaFactorialFock
