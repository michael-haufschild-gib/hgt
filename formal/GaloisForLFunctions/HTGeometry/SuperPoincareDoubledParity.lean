import GaloisForLFunctions.HTGeometry.DoubledParityClock
import GaloisForLFunctions.HTGeometry.SuperPoincareAlgebra

/-!
# Canonical doubled-parity Super-Poincare representation

Every Hilbert carrier has a canonical unit-momentum `N = 2` representation on its direct square.
The two supercharges are the identity swap clock and the opposite-sign sector observable.  This is
the hypothesis-free core of the corpus doubled-parity construction.
-/

open scoped InnerProductSpace

noncomputable section

namespace HTGeometry

variable {K E : Type*} [RCLike K]
  [NormedAddCommGroup E] [InnerProductSpace K E]

/-- Canonical Pauli-X/Pauli-Z action on a Hilbert direct square. -/
def canonicalDoubledParityD1N2 :
    SuperPoincare.D1N2
      (WithLp 2 (E × E) →L[K] WithLp 2 (E × E)) where
  supercharge0 := doubledParityClock 1
  supercharge1 := doubledOddObservable 1
  momentum := 1
  supercharge0_sq := by
    simpa only [pow_two] using doubledParityClock_sq (1 : E →L[K] E) (by simp)
  supercharge1_sq := by
    ext x
    apply (WithLp.equiv 2 (E × E)).injective
    apply Prod.ext
    · simp [mul_apply_eq_comp]
    · simp [mul_apply_eq_comp]
  mixed_anticommutator := by
    ext x
    apply (WithLp.equiv 2 (E × E)).injective
    apply Prod.ext
    · simp [mul_apply_eq_comp]
    · simp [mul_apply_eq_comp]

end HTGeometry
