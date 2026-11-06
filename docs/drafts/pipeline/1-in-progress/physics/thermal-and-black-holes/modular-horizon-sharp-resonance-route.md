# Sharp resonance boundary of the modular horizon

- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Statement:** The normalized modular-horizon response is analytic above the sharp damping line exactly when RH holds. A source-derived bound must establish this analyticity independently of zero locations.

## Exact source

For radial decay `D`, the response is `S_D(ω) = XiC(z+i)/XiC(z)`,
`z = -2ω-2iD-i/2`. Its unnormalized version is the retarded transform of the
totient echo train in `TheEchoTrainOfTheCusp.lean`. Nontrivial zeros produce
frequencies `-γ/2-i(D+(1-β)/2)`.

## Mathematical obligations

1. Classify analyticity and poles at every frequency; retain every zero and multiplicity.
2. Show a concrete nonvanishing Gaussian probe preserves the pole obstruction.
3. Use functional-equation pairs to replace equal damping by a one-sided sharp lower bound.
4. Separate unconditional stability from the sharp bound; identify the exact positive invariant
   retained by reflected pairs.
5. Obtain the sharp bound from the totient echo source or geometric wave dynamics.

## Boundary conditions

The AdS realization uses the modular Eisenstein channel, or its deck-invariant lift to a smooth
congruence cover. A standard Dirichlet quantum Mixmaster billiard selects odd Maaß cusp forms and
excludes this channel. A cosmological realization needs a justified even boundary sector.

## Open core

No source-derived quarter-line estimate is known here. Positivity of the undamped echo train,
causality, and ordinary mode stability do not establish that estimate. Existing full-field packet
and contour work remains in `modular-horizon-full-field-ringdown.md`.

## Verification

Pending implementation and kernel dependency audit. No claim of an RH proof or novelty.
