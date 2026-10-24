# CHMD reduced source compactness

- **ID:** chmd-reduced-source-compactness-2026-10-24
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Statement:** The source projection from the graph-orthogonal complement of the full signed radical into the theta–cosh mass space is compact.

## Exact target

```
IsCompactOperator (sourceMap.comp signedRadicalᗮ.subtypeL)
```

All spaces and maps are the literal CHMD objects. No hypothesis on Xi-zero
locations, multiplicities, a spectral gap, a frame bound, or tail tightness is
permitted. This is a conjecture, not an imported input to another proof.

## Why this question follows from the corpus

- `CHMDPrimitiveCuspEscape` refutes compactness before removing the critical
  band, even on the primitive sector. It does not assert that its escaping
  vectors retain mass after full signed-radical projection.
- `CHMDCriticalBandReduction` makes graph and source orthogonality compatible
  with critical projection; the radical has exactly twice its source norm
  squared as its graph norm squared.
- `CHMDMassSpectralAdmission` identifies the mass critical space with the
  full joint Xi/pole Fourier-sample kernel.
- `CHMDMassSamplingCompleteness.massSamplingSpan_closure` identifies its
  orthogonal complement with the closure of the actual Fourier-kernel span.
  This is density, not a uniform synthesis or tail estimate.
- `CHMDReducedSpectralCore` gives graph-norm spectral approximation within
  the reduced graph. Again, it does not give uniform tail control.
- The fixed-aperture quotient-landing theorem is formalized and audited in
  `CHMDFixedApertureQuotientLanding.lean`. It isolates compactness on each
  fixed source aperture and proves a lower quotient bound. Nothing in that
  argument makes its constants uniform as aperture grows.
- `CHMDNoWeylAboveThreshold` already excludes Weyl values above one half.
  Reproving that result would not resolve this stronger compactness claim.

## Consequence worth pursuing

If proved, the conjecture would make the arithmetic resolvent on the
mass-critical complement compact. There could then be only finitely many
eigenstates above one half. The established CHMD inertia dictionary would
give finiteness of the off-line zero set. This would close the finiteness
obstacle in the bound-state/abscissa branch of CHMD, but would not prove the
still-open `AsymptoticAbscissaLaw` or exclude the remaining finite set.

## Attempt to disprove before formalization

The decisive test is a graph-bounded sequence `p_n` in `signedRadicalᗮ`
whose source coordinates have no norm-convergent subsequence. Start with
the existing cusp escape, project it, and determine its reduced mass norm;
an unreduced norm-one sequence alone is not a counterexample. Also search
for Weyl sequences at nonzero spectral values below or at one half on the
reduced space.

An additional competing mechanism must be tested. The existing
`CHMDLevySymbolLowerBound.levySymbol_ge_log` proves unbounded logarithmic
high-frequency growth, while the physical theta multiplier becomes small
far in the cusp. A translated packet with a simultaneously increasing carrier
frequency might balance these effects and produce Weyl values strictly below
one half. Such packets would survive critical projection and refute the
compactness claim. This is not yet a counterexample: a full operator-defect
estimate, including the prime shifts and cutoff commutators, is missing.
Neither a Rayleigh quotient nor a symbol heuristic supplies that estimate.

If this mechanism can be proved, its positive content should be the exact
reduced essential-spectrum interval, not merely another compactness no-go.
Until then, the compactness conjecture remains unresolved and cannot be used.

## Open proof core

**[OPEN CORE]** Uniform mass-tail tightness for the reduced graph unit ball:
for every `epsilon > 0`, find a finite radius `R` such that every reduced
graph vector of norm at most one has source mass outside `[-R,R]` below
`epsilon`. The Fourier-kernel span gives individually rapidly decaying
generators, but arbitrary linear combinations may have severe cancellation
inside the aperture. No stable synthesis estimate has been proved.

No Lean module or source-sign theorem is claimed for this conjecture.
External search and novelty checks are excluded by the user.
