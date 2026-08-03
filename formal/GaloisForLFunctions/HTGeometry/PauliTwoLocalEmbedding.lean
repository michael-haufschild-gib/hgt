import GaloisForLFunctions.HTGeometry.PauliTwoLocalLabels
import GaloisForLFunctions.HTGeometry.TwoLocalRealSliceGenericity

/-!
# The occupation form of a two-local Hamiltonian in Pauli coordinates

Occupation numbers and Pauli signs are affinely related, `occ = (1 - Z)/2`, so a Hamiltonian written
with one- and two-body occupation couplings and single-qubit flips is a combination of the identity,
the `Z` strings, the `Z Z` strings and the `X` strings.  Collecting the coefficients is a finite
rearrangement: the `i = j` interaction terms feed the identity and `Z_i` coefficients because
`occ^2 = occ`, and the two orientations of a pair feed the same `Z_i Z_j` label.

This dictionary embeds the two-local coefficients of the hypercube family into the coefficients of
any Pauli ensemble containing the strings of weight at most two.
-/

open scoped BigOperators Matrix.Norms.Elementwise

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {n : ℕ}

end

end GaloisForLFunctions.HTGeometry
