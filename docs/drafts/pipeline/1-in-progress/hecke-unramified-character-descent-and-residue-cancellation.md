# Unramified descent and completed Hecke residue cancellation

- **ID:** hecke-unramified-character-descent-and-residue-cancellation
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** [Hecke programme](hecke-l-functions-and-class-field-theory-2026-10-28.md)
- **Statement:** Cancel both raw completed-theta residues for nontrivial characters and construct the Gamma-completed continuation with its removable values.

## Finalized

Actual descent to the ordinary class group, nontriviality of the descended
character, and ordinary-class orthogonality are formalized in
`UnramifiedHeckeCharactersDescendToIdealClasses`. See
[the descent proof](../3-formalized/hecke-unramified-character-descent.md).

The ordinary global continuation is entire for every nontrivial character
and has the exact positive simple pole at one for the trivial character.
See [global continuation](../3-formalized/hecke-global-continuation-from-ordinary-classes.md).

`HeckeCompletedThetaResiduesCancel` now cancels both raw completed
numerators before reciprocal Gamma removal. The physical cancellation
uses the actual base ideal class and ordinary-class character sum. The
dual cancellation uses the proved ordinary residue and nonvanishing of
Gamma at one. Both main transitive axiom audits are standard only; final
direct source audit passes without warnings. See
[the completed residue proof](../3-formalized/hecke-completed-theta-residues-cancel.md).

## Remaining completion

`/tmp/HeckeGammaCompletedContinuationScratch.lean` contains the complete
unchecked divided-difference construction. Write the raw expression as
`R(s) - (2/n)P(s)/s + (2/n)Q(s)/(s-1)` when parity is zero.
Replacing the varying numerators by divided differences gives an entire
regular part plus the constant residues `-(2/n)P(0)` and `(2/n)Q(1)`.
The proved cancellations make the completion entire for nontrivial
characters, including zero and one. Nonzero parity has no zero modes.

The draft proves agreement with the actual theta expression away from
zero and one, Gamma times the ideal series on `Re(s)>1`, meromorphy,
nontrivial-character entireness, and recovery of the ordinary entire
function by reciprocal Gamma through analytic uniqueness. The residue
module's olean is being built for this already written consumer.

Primitive scalar normalization, class recombination, and global
reflection remain on the [dual analytic card](hecke-dual-theta-unfolding-over-fractional-ideal-classes.md).
