# Library ticket: sigma divisor jet multiplicative kill

- **Target docs:** `docs/drafts/door/00-index.md`; likely `docs/drafts/door/bucket-the-seam-archimedean-obstruction.md`; possibly `docs/drafts/rh-monodromy-weight-mismatch/106-joint-reading-no-go.md`.
- **Source card:** `docs/drafts/pipeline/3-formalized/new/sigma-divisor-jet-multiplicative-kill.md`
- **Formal file:** `formal/GaloisForLFunctions/RHTower/SigmaDivisorJet.lean`

## Update Needed

Record the first attack on the doc-106 escape hatch:

1. The natural non-character, non-positivity local object is the divisor-tangent jet algebra `R[X]/(X^m)`.
2. A sigma direction that is locally multiplicative by the zeroed function, `(X^m u) h_p`, has zero class in this algebra.
3. Therefore the multiplicative prime-lane candidate does not produce a `{sigma_p}`-graded divisor refinement finer than multiplicity at one pinned annulus.
4. The open residue is now sharper: construct a non-multiplicative source map `sigma_p -> delta_p` with `delta_p mod X^m != 0`, before reading the zero divisor and without using a flow or positivity.

## Suggested Grade

THEOREM (Lean), negative route theorem. Door status: BRIDGE / seam-gap localization, not C5.
