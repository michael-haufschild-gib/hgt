# Source-odd quintic cross invariant

- **ID:** `source-odd-quintic-cross-invariant`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper + Lean) / BRIDGE / NOT NEW MATHEMATICS
- **Parent:** `source-odd-quintic-successor-modulus.md`
- **Statement:** Diagonal projective reparametrization of a source-odd quintic preserves the
  division-free cross product \(b'^2ac=b^2a'c'\); normalized triples with different squared
  middle coefficients are inequivalent.
- **Lean:** `formal/GaloisForLFunctions/HTGeometry/SourceOddQuinticSuccessorModulus.lean`

## Goal

Formalize the exact nonselection core exposed after source polarity uniquely selected the
quadratic paired orbit. Keep the theorem independent of division, algebraic closure, physical
interpretation, or computation.

## Gates

- [x] complete paper proof
- [x] unconditional Lean theorem `sourceOddQuinticReparam_cross_invariant`
- [x] equivalence-level theorem
  `sourceProjectivelyEquivalentOddQuintic_cross_invariant`
- [x] normalized nonselection theorem
  `normalizedSourceOddQuintic_not_projectivelyEquivalent_of_sq_ne`
- [x] direct `lake env lean` source check
- [x] final module build
- [x] axiom audit
- [ ] full complex orbit classification from the paper parent
- [ ] physical cross-law interference

## Formal theorem

For coefficients \(q=(a,b,c)\), define

\[
R_{\lambda,u,v}(q)
=
(\lambda a u^4v,\lambda b u^2v^3,\lambda c v^5).
\]

The Lean theorem proves over every commutative ring:

\[
R_{\lambda,u,v}(q)_b^2ac
=
b^2R_{\lambda,u,v}(q)_aR_{\lambda,u,v}(q)_c.
\]

No inverse or nonzero hypothesis is needed for this polynomial identity. Projective source
equivalence adds nonzero \(\lambda,u,v\) and inherits the identity.

For normalized triples \(q_b=(1,b,1)\), equivalence therefore implies

\[
d^2=b^2.
\]

Consequently \(d^2\ne b^2\) certifies inequivalent source-odd quintic successor orbits.

## Lean certificate

Module:

`GaloisForLFunctions.HTGeometry.SourceOddQuinticSuccessorModulus`.

Declarations:

- `SourceOddQuinticCoefficients`
- `sourceOddQuinticReparam`
- `sourceOddQuinticReparam_cross_invariant`
- `SourceProjectivelyEquivalentOddQuintic`
- `sourceProjectivelyEquivalentOddQuintic_cross_invariant`
- `normalizedSourceOddQuintic`
- `normalizedSourceOddQuintic_sq_eq_of_projectivelyEquivalent`
- `normalizedSourceOddQuintic_not_projectivelyEquivalent_of_sq_ne`

Verification:

```text
lake env lean GaloisForLFunctions/HTGeometry/SourceOddQuinticSuccessorModulus.lean
-- exit 0

lake build GaloisForLFunctions.HTGeometry.SourceOddQuinticSuccessorModulus
✔ [1825/1825] Built GaloisForLFunctions.HTGeometry.SourceOddQuinticSuccessorModulus
Build completed successfully (1825 jobs).
```

`#print axioms` for all four theorem declarations reports only `propext`.

Formal lint reaches this module through the `GaloisForLFunctions.HTGeometry` umbrella. The global
lint run continues to fail on the unrelated pre-existing unreachable module
`GaloisForLFunctions.HTGeometry.UniversalClockSamplingPhaseLaw`; it reports no error for this
module.

## Scientific boundary

This theorem proves inequivalent coefficient orbits, not:

- physical admissibility of a quintic successor tensor;
- survival after complete source consequence;
- coherent superposition or interference between orbits;
- probability, time, spacetime, gravity, or gauge force;
- novelty in invariant theory.

Its precise research use is negative and structural: source polarity and oddness do not
recursively guarantee a unique higher law. Any universal succession theory must either derive an
additional selector for the quintic invariant or explain how surviving invariant classes become
physical alternatives.

## Log

- 2026-07-30 — paper invariant reduced to a division-free commutative-ring identity.
- 2026-07-30 — direct source check and single final module build passed.
- 2026-07-30 — axiom audit reported only `propext`.
- 2026-07-30 — umbrella import added; global lint advanced past this module and stopped at an
  unrelated pre-existing unreachable module.
