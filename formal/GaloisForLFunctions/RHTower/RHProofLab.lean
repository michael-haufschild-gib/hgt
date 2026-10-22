/-
RH proof lab: finite algebraic mechanisms

This aggregator bundles two self-contained finite modules. `EulerProductArithmetic` proves that a
finite product of local factors `∏_{i ∈ S} (1 + a_i)` over a commutative semiring expands as the sum
of the squarefree monomials `∏_{i ∈ T} a_i` over all subsets `T ⊆ S`, and that disjoint blocks
multiply independently. `PositivitySelector` proves that a weighted sum of squared defects with
strictly positive weights vanishes exactly when every defect vanishes; specialized to the
critical-line defect `Re z - 1/2` of a finite family of complex points, the energy is zero exactly
when all points lie on `Re z = 1/2` (zero off-line count), and the mirror `z ↦ 1 - conj z` leaves
the energy invariant, so mirror symmetry alone does not force it to vanish.

No statement here concerns zeros of an actual L-function; all results are unconditional finite
identities, the positivity selector assuming only strictly positive weights.
-/

import GaloisForLFunctions.RHProofLab.EulerProductArithmetic
import GaloisForLFunctions.RHProofLab.PositivitySelector
