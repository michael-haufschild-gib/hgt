import GaloisForLFunctions.HTGeometry.CountableDifferentialPattern
import Mathlib.Data.Set.Countable

/-!
# The countable rational-lattice shift palette

The facet-sewn construction uses shifts in

`Q(i) + ∑_v Z ω_v`.

Representations in this form need not be unique, so the correct palette is the range subtype in
`C`, not the raw coefficient code.  Its inclusion into `C` is automatically injective and the
range is countable.  The countable differential-pattern theorem therefore supplies one bounded
prime-log gauge free of every encoded polynomial-coefficient differential relation on this exact
palette.
-/

namespace GaloisForLFunctions.HTGeometry

variable {V : Type*} [Fintype V]

/-- Evaluation of a Gaussian-rational plus finite integral lattice shift. -/
noncomputable def rationalLatticeShiftMap (omega : V → ℝ) :
    ((ℚ × ℚ) × (V → ℤ)) → ℂ :=
  fun code ↦
    (code.1.1 : ℂ) + (code.1.2 : ℂ) * Complex.I +
      ∑ v, (code.2 v : ℂ) * (omega v : ℂ)

/-- The actual shift set `Q(i) + ∑_v Z ω_v`, with duplicate representations identified. -/
noncomputable def rationalLatticeShiftSet (omega : V → ℝ) : Set ℂ :=
  Set.range (rationalLatticeShiftMap omega)

theorem rationalLatticeShiftSet_countable (omega : V → ℝ) :
    (rationalLatticeShiftSet omega).Countable := by
  exact Set.countable_range _

noncomputable instance (omega : V → ℝ) :
    Countable (rationalLatticeShiftSet omega) :=
  (rationalLatticeShiftSet_countable omega).to_subtype

/-- Polynomial differential freeness on the exact facet-sewn rational-lattice shift palette is a
dense residual bounded-gauge condition. -/
theorem rationalLatticeShift_polynomialDifferentialFree_dense_residual
    (omega : V → ℝ) :
    Dense {u : PrimeLogBoundedGauge |
      CountableShiftPolynomialDifferentialFree
        ((↑) : rationalLatticeShiftSet omega → ℂ) u} ∧
    {u : PrimeLogBoundedGauge |
      CountableShiftPolynomialDifferentialFree
        ((↑) : rationalLatticeShiftSet omega → ℂ) u} ∈
      residual PrimeLogBoundedGauge := by
  exact countableShiftPolynomialDifferentialFree_dense_residual
    ((↑) : rationalLatticeShiftSet omega → ℂ) Subtype.val_injective

/-- There exists one bounded prime-log gauge polynomial-differentially free on every finite packet
from `Q(i) + ∑_v Z ω_v`. -/
theorem exists_rationalLatticeShift_polynomialDifferentialFree
    (omega : V → ℝ) :
    ∃ u : PrimeLogBoundedGauge,
      CountableShiftPolynomialDifferentialFree
        ((↑) : rationalLatticeShiftSet omega → ℂ) u := by
  exact exists_countableShiftPolynomialDifferentialFree
    ((↑) : rationalLatticeShiftSet omega → ℂ) Subtype.val_injective

end GaloisForLFunctions.HTGeometry
