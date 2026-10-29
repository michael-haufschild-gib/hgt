# Unramified character descent and completed-theta residue cancellation

- **ID:** hecke-unramified-character-descent-and-residue-cancellation
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** [Hecke programme](hecke-l-functions-and-class-field-theory-2026-10-28.md)
- **Statement:** A nontrivial Hecke character with trivial finite residue character and zero real parity cancels both polar coefficients of the globally recombined completed theta transform.

## Completed arithmetic and ordinary L-continuation

`UnramifiedHeckeCharactersDescendToIdealClasses.lean` proves actual descent
to the ordinary class group, nontriviality of the descended character,
and the vanishing ordinary-class character sum. Zero parity degree forces
all real sign characters to be trivial. Trivial finite weight forces the
finite residue character to be trivial. The proved ray-to-ordinary class
surjection then gives descent by its actual kernel description.
See [the finalized arithmetic proof](../3-formalized/hecke-unramified-character-descent.md).

`HeckeLFunctionsHaveGlobalContinuation.lean` now proves the entire ordinary
L-continuation for every nontrivial character and the exact trivial pole.
The remaining ordinary L-residue vanishes by comparison with the already
proved holomorphy at one. Both results pass final source audits and
standard-only transitive axiom audits. See
[global continuation](../3-formalized/hecke-global-continuation-from-ordinary-classes.md).

## Remaining stronger completed-theta statement

The Gamma-removed continuation does not itself identify the two raw
completed-theta polar sums. That stronger cancellation is useful for the
primitive completed functional equation and remains to be formalized.

For each ordinary class `c`, the actual base ideal `B_c` is prime to the
modulus and has class `c^-1`. If `phi` is the descended class character,
prove `heckeValue(B_c)=phi(c^-1)`. At zero, the inverse base weights are
therefore exactly `phi(c)`; their sum is zero. This cancels the physical
completed-theta pole before multiplication by reciprocal Gamma.

At one, the raw dual scalar contributes `N(B_c)^-1`, canceling the
base weight's `N(B_c)`. Its remaining class dependence is again `phi(c)`.
Alternatively, use the now-proved vanishing ordinary L-pole coefficient,
together with nonvanishing of the Gamma product at one, to obtain the
raw dual cancellation without repeating the norm normalization.

Entire divided differences can then fill both raw completed-theta poles.
For nontrivial finite weight or nonzero real parity, completed entireness
is already proved by the actual strong theta pair. This remaining card
concerns precisely the nontrivial unramified ordinary-class characters.

No normalized completed residue identity is assumed. Primitive Gauss
normalization, conductor scaling, and the arithmetic dual-character
identification remain independent functional-equation obligations.
