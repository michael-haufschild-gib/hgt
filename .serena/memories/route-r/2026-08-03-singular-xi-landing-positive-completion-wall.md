# Route R frontier, 2026-08-03

Formal modules added and wired into `formal/GaloisForLFunctions/RHTower.lean`:

- `EulerPrimitiveJointDepthSingularXiLanding.lean`: exact literal joint-(prime,depth) Euler source/co-source, polar fill, Gamma connection, and unconditional regular-locus landing to the centered Xi relative resolvent trace.
- `VonMangoldtGammaJetPositiveCompletionNoGo.lean`: depth-one central Euler Gram atom at n=2 has norm square `1/(128*log 2*(log(2)^2-1/4)^2)>1/5`, while `normalizedPrimeArchMoment 0<29/625<1/5`. Any completion matching the arithmetic moment therefore has correction real part `<-96/625`; nonnegative diagonal/orthogonal positive Gamma completion is impossible.
- `EulerPrimitiveJointDepthBiorthogonalCommonTest.lean`: literal common-test source and balanced nonsummability boundary wall.

All three targeted Lake builds pass. Scratch `#print axioms` reports only `propext`, `Classical.choice`, `Quot.sound`. Authoritative `scripts/formal_tools.py lint` passes. No stale Lean processes from this work.

Updated Hellinger–Hodge–Green paper leaves same exact core: source-derived signed/off-diagonal transverse arithmetic annihilation before reflection-invariant coarsening. Existing source construction, continuation, Gamma sewing, and source-to-Xi landing do not prove this; it is equivalent to RH. Survivor must contain genuine divisor-coupled negative Schur/off-diagonal or singular indefinite coupling, with central negative budget below `-96/625`. Positive/direct-sum mechanisms are dead.

Research records:
- `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/route-r-depth-one-positive-completion-no-go.md`
- `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/route-r-primitive-joint-depth-biorthogonal-common-test.md`
- appended frontier sections in `docs/drafts/pipeline/1-in-progress/rh-current-frontier-map.md`.

Publication papers were read only, not edited.