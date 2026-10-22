# Prime-Arch cofinal irreducible negative-Hankel universality law

- **ID:** `prime-arch-cofinal-irreducible-negative-hankel-universality-law`
- **Law:** LAW510
- **Stage:** 1-in-progress
- **Type:** THEOREM (dependency-closed paper proof)
- **Register:** `[UNIVERSAL-LAW] [CORPUS-SYNTHESIS]`
- **Target:** `formal/GaloisForLFunctions/RHTower/PrimeArchCofinalIrreducibleNegativeHankelUniversalityLaw.lean`

## Theorem

If RH fails, then for every infinite prescribed set of polynomial degrees and every degree bound,
there exists above that bound a monic irreducible integer polynomial which:

- is Eisenstein at `2`;
- lies outside all three unconditional prime--Gamma positive coefficient families;
- has degree in the prescribed set;
- has strictly negative prime--Gamma source trace-Hankel value.

Thus non-RH negativity cannot be confined to reducible tests or finitely many exceptional
degrees; it recurs cofinally inside every infinite degree palette in one fixed Eisenstein chamber.

## Theorem-generated derivation

Whole-corpus leaf comparison exposed:

- `exists_combinedResidualTwoEisenstein_negativeTraceHankel_of_not_riemannHypothesis`;
- `irreducible_of_monic_primeArchTwoEisenstein`.

The first theorem produces a negative combined-residual monic `2`-Eisenstein test in every
infinite degree set.  The second proves irreducibility for every positive-degree member of that
chamber.  Corpus does not tail-restrict the degree palette, record cofinal recurrence, or attach
irreducibility to the non-RH witness.

## Dependency-closed paper proof

Fix infinite `D ⊆ ℕ` and a bound `N`.  Remove the finite initial segment `{d | d ≤ N}`.
The remaining tail `D \ Iic N` is still infinite.  Apply the existing non-RH witness theorem to
that tail.  Its polynomial `p` is monic, `2`-Eisenstein, combined-residual, has negative source
trace-Hankel value, and satisfies `deg p ∈ D \ Iic N`; hence `N < deg p`, in particular
`0 < deg p`.  The corpus Eisenstein theorem now proves `Irreducible p`.  No numerical computation
is used.

## Strict corpus delta

Existing source establishes one negative witness in each infinite palette.  New law proves the
negative irreducible witnesses are cofinal in every such palette, with all three structured
positive families simultaneously excluded.

## Lean result

`formal/GaloisForLFunctions/RHTower/PrimeArchCofinalIrreducibleNegativeHankelUniversalityLaw.lean`
proves:

- `exists_cofinal_irreducible_combinedResidualTwoEisenstein_negativeTraceHankel_of_not_rh`.

Direct exact check passed without warnings:

`lake env lean GaloisForLFunctions/RHTower/PrimeArchCofinalIrreducibleNegativeHankelUniversalityLaw.lean`

The module is imported by `GaloisForLFunctions/RHTower.lean`.

## Post-proof novelty audit

Performed only after dependency-closed Lean proof passed.  Targeted searches found classical
Eisenstein irreducibility, Hankel determinants of Eisenstein series, spectral and polynomial
criteria connected to RH, and RH results for unrelated Eisenstein-series integrals.  They did not
recover a prime--Gamma source trace-Hankel form whose non-RH negative witnesses are cofinal in
every infinite prescribed degree palette while simultaneously monic, irreducible,
`2`-Eisenstein, and outside three structured positive coefficient families.

Verdict: `[NOVELTY PLAUSIBLE — SEARCH NOT EXHAUSTIVE]`.  Novelty is claimed for this exact
cofinal negative-witness theorem, not for Eisenstein's irreducibility criterion.

## Gates

- [x] Whole-corpus theorem-leaf discovery
- [x] Prior corpus and failed-route audit
- [x] Dependency-closed paper proof
- [x] Lean formalization; direct `lake env lean`
- [x] Post-proof literature audit
- [ ] Axiom and umbrella audit
