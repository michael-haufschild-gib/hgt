import GaloisForLFunctions.HTGeometry.GomesFiniteFockFormalSubstitution
import Mathlib.RingTheory.Adjoin.Polynomial.Basic

/-!
# Recovering the actual clock from any invertible formal coordinate

Mathlib's two-sided formal compositional inverse becomes an exact finite
polynomial inverse after evaluation. Every based formal coordinate with an
invertible linear term therefore generates the same actual finite clock algebra
and has exactly the same full matrix commutant.
-/

noncomputable section
open Matrix Polynomial
namespace GaloisForLFunctions.HTGeometry.GammaFactorialFock

/-- A formal change of clock has zero constant coefficient and invertible linear coefficient. -/
abbrev GomesInvertibleFormalCoordinate :=
  {G : PowerSeries ℂ // PowerSeries.constantCoeff G = 0 ∧ IsUnit (PowerSeries.coeff 1 G)}

/-- Every invertible formal coordinate belongs to the based augmentation ideal. -/
def gomesInvertibleFormalCoordinate_based (G : GomesInvertibleFormalCoordinate) : GomesBasedFormalSeries :=
  ⟨G.val, RingHom.mem_ker.mpr G.property.1⟩

/-- The exact finite inverse is the truncated existing compositional inverse. -/
def gomesFiniteFockCoordinateRecoveryPolynomial (N : ℕ) (G : GomesInvertibleFormalCoordinate) : ℂ[X] :=
  PowerSeries.trunc N (G.val.substInvOfIsUnit G.property.2)

/-- A finite polynomial in the changed clock recovers the literal original derivative clock. -/
theorem gomesFiniteFockCoordinateRecoveryPolynomial_eval (N : ℕ) (G : GomesInvertibleFormalCoordinate) :
    Polynomial.aeval (gomesFiniteFockFormalHom N G.val) (gomesFiniteFockCoordinateRecoveryPolynomial N G) =
      fockShiftMatrix N := by
  rw [gomesFiniteFockCoordinateRecoveryPolynomial]
  change Polynomial.aeval (gomesFiniteFockFormalHom N (gomesInvertibleFormalCoordinate_based G).val) _ = _
  rw [← gomesFiniteFockFormalHom_subst]
  change gomesFiniteFockFormalHom N ((G.val.substInvOfIsUnit G.property.2).subst G.val) = _
  rw [PowerSeries.subst_substInvOfIsUnit_left G.val G.property.1 G.property.2,
    gomesFiniteFockFormalHom_X]

/-- Every invertible formal coordinate generates exactly the original finite clock symmetry algebra. -/
theorem gomesFiniteFockCoordinate_adjoin (N : ℕ) (G : GomesInvertibleFormalCoordinate) :
    gomesFiniteFockCommutant N = Algebra.adjoin ℂ {gomesFiniteFockFormalHom N G.val} := by
  apply le_antisymm
  · rw [gomesFiniteFockCommutant_eq_adjoin]
    apply Algebra.adjoin_singleton_le
    rw [← gomesFiniteFockCoordinateRecoveryPolynomial_eval N G]
    exact Polynomial.aeval_mem_adjoin_singleton _ _
  · exact Algebra.adjoin_singleton_le (gomesFiniteFockFormalHom_mem N G.val)

/-- One changed clock has exactly the same matrix symmetries as the original actual clock. -/
theorem gomesFiniteFockCoordinate_commute_iff (N : ℕ) (G : GomesInvertibleFormalCoordinate)
    (M : Matrix (Fin N) (Fin N) ℂ) :
    Commute M (gomesFiniteFockFormalHom N G.val) ↔ Commute M (fockShiftMatrix N) := by
  constructor
  · intro h
    have hd : fockShiftMatrix N ∈ Algebra.adjoin ℂ {gomesFiniteFockFormalHom N G.val} := by
      rw [← gomesFiniteFockCoordinate_adjoin]
      exact gomesFiniteFockCommutant_clock_mem N
    exact Algebra.commute_of_mem_adjoin_singleton_of_commute hd h
  · intro h
    have hg := gomesFiniteFockFormalHom_mem N G.val
    rw [gomesFiniteFockCommutant_eq_adjoin] at hg
    exact Algebra.commute_of_mem_adjoin_singleton_of_commute hg h

/-- Full commutant equality is invariant under every invertible formal change of the finite clock. -/
theorem gomesFiniteFockCoordinate_centralizer (N : ℕ) (G : GomesInvertibleFormalCoordinate) :
    Subalgebra.centralizer ℂ {gomesFiniteFockFormalHom N G.val} = gomesFiniteFockCommutant N := by
  ext M
  rw [gomesFiniteFockCommutant_mem_iff]
  simp only [Subalgebra.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
  exact eq_comm.trans (gomesFiniteFockCoordinate_commute_iff N G M)

end GaloisForLFunctions.HTGeometry.GammaFactorialFock
