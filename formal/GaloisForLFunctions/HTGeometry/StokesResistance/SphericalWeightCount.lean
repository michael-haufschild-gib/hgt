import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Spherical Stokes-response parameter counts

Moreau's Appendix A counts spherical invariants by Schur multiplicities. For `SO(3)`, each interior
angular-momentum type occurs three times, while the two tail types occur twice and once. A symmetric
form on a multiplicity-`m` isotypic block has `choose (m+1) 2` parameters.

For `O(3)`, inversion parity splits every interior multiplicity `3` as `2+1`, and the multiplicity-2
tail as `1+1`; cross-parity forms disappear. With paper order shifted to `k=n+3`, the resulting raw
counts are `6n+4` and `4n+3`, equivalent to `6k-14` and `4k-9`.
-/

namespace GaloisForLFunctions.HTGeometry.StokesResistance

/-- Symmetric-form parameter count on a multiplicity space of dimension `m`. -/
def symmetricMultiplicityParameterCount (m : ℕ) : ℕ := Nat.choose (m + 1) 2

/-- `SO(3)` count from `n` interior multiplicity-three blocks and tail multiplicities `2,1`. -/
def specialOrthogonalRawParameterCount (n : ℕ) : ℕ :=
  n * symmetricMultiplicityParameterCount 3 +
    symmetricMultiplicityParameterCount 2 + symmetricMultiplicityParameterCount 1

/-- Moreau's spherical formula `d_raw(SO(3))=6k-14`, shifted to `k=n+3`. -/
theorem specialOrthogonalRawParameterCount_eq (n : ℕ) :
    specialOrthogonalRawParameterCount n = 6 * n + 4 := by
  norm_num [specialOrthogonalRawParameterCount, symmetricMultiplicityParameterCount,
    Nat.choose]
  ring

/-- `O(3)` count after splitting each repeated type by inversion parity. -/
def orthogonalRawParameterCount (n : ℕ) : ℕ :=
  n * (symmetricMultiplicityParameterCount 2 + symmetricMultiplicityParameterCount 1) +
    3 * symmetricMultiplicityParameterCount 1

/-- Moreau's spherical formula `d_raw(O(3))=4k-9`, shifted to `k=n+3`. -/
theorem orthogonalRawParameterCount_eq (n : ℕ) :
    orthogonalRawParameterCount n = 4 * n + 3 := by
  norm_num [orthogonalRawParameterCount, symmetricMultiplicityParameterCount, Nat.choose]
  ring

/-- Inversion parity removes exactly `2n+1` raw spherical coefficients. -/
theorem specialOrthogonal_sub_orthogonal_parameterCount (n : ℕ) :
    orthogonalRawParameterCount n + (2 * n + 1) = specialOrthogonalRawParameterCount n := by
  rw [specialOrthogonalRawParameterCount_eq, orthogonalRawParameterCount_eq]
  omega

end GaloisForLFunctions.HTGeometry.StokesResistance
