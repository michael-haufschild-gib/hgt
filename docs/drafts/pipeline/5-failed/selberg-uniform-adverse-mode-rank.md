# No width-independent adverse-mode count at fixed height

- **ID:** SELBERG-UNIFORM-ADVERSE-MODE-RANK
- **Stage:** 5-failed, the fixed-height uniform-count strengthening only.
- **Parent:** [Constructive Selberg loop](../1-in-progress/selberg-quarter-conjecturing-loop.md), cycle 15.

## Tested strengthening and exact failure

After reducing the critical cusp seam cost to finitely many integer modes, one might hope that the number of adverse channels is bounded independently of congruence period at a fixed cutoff height.

The exact count is `2*(ceil(exp(tau)*w/(2*pi*Y))-1)`. `integer_width_cutoff_unbounded` proves that at every fixed `Y>0` and every natural bound `m`, there is a positive integer period whose adverse cutoff exceeds `m`. Thus no uniform count of this kind exists for the permitted integer-frequency seam coefficients.

This concerns the set of permitted frequencies and their coefficients. It does not assert that an actual Maass form has nonzero trace in every adverse channel, or construct a negative core-plus-cusp energy. It does not retire a width-scaled cutoff or a growing-block arithmetic estimate.

## Strongest positive survivor after second pass

The positive survivor is an exact scaling law, complete signed interval classification, and an exact finite-packet square-plus-positive-boundary-minus-cost identity. At every fixed height, every even adverse-block size occurs for an explicit positive width; the block is empty exactly when the first frequency reaches the Bessel transition. The adverse cost is strictly positive precisely on traces meeting its finite support nontrivially.

**New insight:** moving the seam to height proportional to width can keep this count controlled, but a fixed height cannot. The core obligation therefore changes with the chosen cutoff; a finite boundary reduction cannot be treated as a uniform spectral estimate.

**Paper status:** complete. **Lean status:** complete in `SelbergBesselAdverseModes`, including the signed count, exact cost decomposition, finite-packet integral identity, and unboundedness along integer periods. [Positive survivor and audit](../3-formalized/selberg-exact-adverse-cusp-modes.md).

## Live successor

Determine the sharp trace-constrained cusp energy before coupling it to a core response. The completed square supplies a lower bound; a compact approximation to the actual Bessel profile must establish whether this bound is attained as an infimum. No such approximation theorem is assumed here.
