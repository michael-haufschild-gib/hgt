# Quadratic principal-symbol locality universality law

## Status

Fully proven on paper; formalized in Lean 4; **verification gate passed**.

`lake build` succeeds on the module inside the `GaloisForLFunctions.HTGeometry` umbrella (which imports it), and `#print axioms` gives exactly `propext, Classical.choice, Quot.sound` for

```text
GaloisForLFunctions.HTGeometry.quadraticWidthPrincipalSymbolCompletion_membraneLocalityUniversality
GaloisForLFunctions.HTGeometry.quadraticWidthPrincipalSymbolCompletion_binaryLocal_membraneLowerBound
```


## Theorem-first source

- `quadraticWidthPrincipalSymbolCompletion_principalBracketPair_linearIndependent`: the
  quadratic-width universal completion realizes every unordered law-space two-plane as an
  independent principal bracket.
- `membranePairComplete_of_principalBracketPair_linearIndependent`: membrane locality plus
  independent brackets forces pair-complete support.
- `holographicLocality_choose_bound`: pair completeness and membrane valence `Δ` imply
  `choose n 2 ≤ #H * choose Δ 2`.

The universal completion and locality lower bound were terminal separately; no theorem applied
the lower bound to this concrete maximal principal symbol.

## Universal law

Every membrane-local support presentation of the quadratic-width universal principal-symbol
completion is pair-complete.  If each membrane sees at most `Δ` of the `n` law directions, then
`choose n 2 ≤ #H * choose Δ 2`.  Under binary locality, at least `choose n 2` distinct membrane
channels are unavoidable.

## Paper proof

The quadratic completion's principal brackets are linearly independent, hence each is nonzero.
Membrane locality says a bracket can be nonzero only if some membrane contains both directions,
so every two-element law subset is covered.  Double-count all covered pairs: each membrane of
valence at most `Δ` covers at most `choose Δ 2` pairs, whereas the law space contains
`choose n 2`.  For `Δ = 2`, each membrane covers at most one pair.

## Lean formalization

- Module: `GaloisForLFunctions.HTGeometry.QuadraticPrincipalSymbolLocalityUniversalityLaw`
- General theorem:
  `GaloisForLFunctions.HTGeometry.quadraticWidthPrincipalSymbolCompletion_membraneLocalityUniversality`
- Binary theorem:
  `GaloisForLFunctions.HTGeometry.quadraticWidthPrincipalSymbolCompletion_binaryLocal_membraneLowerBound`
- Exact check:
  `lake env lean GaloisForLFunctions/HTGeometry/QuadraticPrincipalSymbolLocalityUniversalityLaw.lean`
  passed on 2026-07-22.

## Novelty audit

Pending literature audit after theorem-generation phase. Corpus audit is negative.
