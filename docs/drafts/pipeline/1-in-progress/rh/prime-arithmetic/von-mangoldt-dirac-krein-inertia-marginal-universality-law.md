# Von Mangoldt Dirac--Krein inertia/marginal universality law

## Status

Formalized in Lean and wired into the RHTower umbrella. Kept in progress until global exhaustion
and final audit complete.

## Lean sources

- `GaloisForLFunctions.RHTower.VonMangoldtSuccessorDiracKreinEdge`
- `GaloisForLFunctions.RHTower.VonMangoldtSuccessorTransportInertia`
- `GaloisForLFunctions.RHTower.VonMangoldtBivariateMarginalTraceLock`

## Conjecture

The explicit finite source-edge Dirac--Krein Gram has the complete transport-mass signature:
positive, negative, and null indices are exactly the signs of the consolidated successor masses.
Every nonempty full-jet aperture has a negative direction, and negative index is unbounded over
apertures despite every individual lifted jet having a summable positive Hilbert majorant.

Moreover, consecutive source-edge Dirac--Krein jet sections cannot share any fixed finite source
marginal through ordinary bivariate coordinate partial traces.

## Corpus gap

The source-edge file identifies its Gram with the principal-relative matrix. Exact inertia and
trace-lock no-go are proved in separate terminal modules only for that matrix. Search found no
theorem returning those conclusions to the actual source-edge Dirac--Krein realization.

## Proof plan

1. Rewrite the full-jet Dirac--Krein Gram using its exact realization theorem.
2. Transfer all three exact signature formulas.
3. Transfer positivity and unboundedness of negative index.
4. Rewrite the two consecutive Dirac--Krein marginal hypotheses and apply the existing trace-lock
   no-go.

No numerical computation is used.

## Lean result

`formal/GaloisForLFunctions/RHTower/VonMangoldtDiracKreinInertiaMarginalUniversalityLaw.lean`
proves:

- exact `sigNeg`, `sigPos`, and radical dimension formulas for the source-edge Gram;
- `sigNeg_finiteVonMangoldtSuccessorDiracKreinGram_pos`;
- `sigNeg_finiteVonMangoldtSuccessorDiracKreinGram_unbounded`;
- `not_exists_two_bivariateMarginals_finiteVonMangoldtSuccessorDiracKrein`.

Exact check passed without warnings:

`lake env lean GaloisForLFunctions/RHTower/VonMangoldtDiracKreinInertiaMarginalUniversalityLaw.lean`

## Novelty status

Post-proof searches found general literature on Krein signatures, indefinite Hankel moment
matrices, and negative-square bounds, but no matching theorem for the von Mangoldt
successor-edge carrier, its transport masses, unbounded negative index, and consecutive marginal
obstruction. Novelty claim is restricted to this exact arithmetic source-edge package.
