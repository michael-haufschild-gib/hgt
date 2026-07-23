# Von Mangoldt bivariate marginal trace-lock no-go — formal certificate

- **ID:** `von-mangoldt-bivariate-marginal-trace-lock-no-go`
- **Stage:** 3 — formalized in Lean 4
- **Scientific status:** `[UNCONDITIONAL LEAN] [SOURCE-SPECIFIC CLASS NO-GO]`
  `[NOVELTY UNVERIFIED] [NOT RH]`
- **Paper proof:**
  `../2-fully-proven/new_scientific_knowledge/von-mangoldt-bivariate-marginal-trace-lock-no-go.md`

## Formal declarations

```text
HTGeometry.bivariateJetMarginal
HTGeometry.bivariateSourceMarginal
HTGeometry.trace_bivariateJetMarginal_eq_trace_bivariateSourceMarginal
RHTower.vonMangoldtAdditiveLogJetDifference_nonneg
RHTower.vonMangoldtAdditiveLogJetDifference_two_pos
RHTower.vonMangoldtSuccessorRelativeMomentTerm_nonneg
RHTower.vonMangoldtSuccessorRelativeMomentTerm_two_pos
RHTower.finiteVonMangoldtSuccessorRelativeMoment_pos
RHTower.trace_finiteVonMangoldtSuccessorPrincipalRelativeMatrix_succ
RHTower.trace_finiteVonMangoldtSuccessorPrincipalRelativeMatrix_strictMono
RHTower.not_exists_two_bivariateMarginals_finiteVonMangoldtSuccessor
RHTower.finiteGammaOddJacobiCoherentResidualMatrix
RHTower.not_exists_two_bivariateMarginals_finiteVonMangoldtSuccessor_gammaOddJacobi
```

## Source files

```text
formal/GaloisForLFunctions/HTGeometry/BivariateMarginalTraceLock.lean
formal/GaloisForLFunctions/RHTower/VonMangoldtBivariateMarginalTraceLock.lean
```

The generic theorem proves exact trace equality of both coordinate partial traces over every
additive commutative coefficient monoid. The source theorem proves strict `SR-40` trace growth and
excludes every fixed finite source marginal, then specializes directly to the actual `SR-38`
coherent odd Gamma--Jacobi kernel.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/BivariateMarginalTraceLock.lean
lake env lean GaloisForLFunctions/RHTower/VonMangoldtBivariateMarginalTraceLock.lean
lake build GaloisForLFunctions.RHTower.VonMangoldtBivariateMarginalTraceLock
```

Both direct Lean checks pass. Targeted cached build passes `8868/8868`. Repository formal lint
passes with large-file warnings only. Six capstone axiom surfaces use only `propext`,
`Classical.choice`, and `Quot.sound`; forbidden-declaration scan is clean. No stale Lean/lake
process remains.

## Exact scope

This closes ordinary coordinate partial trace as an `SR-41` completion class, independently of
Krein index and mixed coupling. It does not prove RH and does not exclude singular,
weighted/renormalized, non-trace-preserving cyclic readers. Such a reader must now expose the
strict jet-opening flux rather than hide it in a mixed block.
